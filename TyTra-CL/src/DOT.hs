{-# LANGUAGE OverloadedStrings #-}

module DOT where

import qualified AST
import qualified Cost
import           Data.Graph.Inductive
import           Data.Graph.Inductive.Dot
import           Inference
import qualified Transform
--import Data.Text.Lazy
import           Control.Monad            (forM, liftM)
import           Control.Monad.State
import           Text.Dot
import           Debug.Trace
import qualified Data.HashMap.Strict

type NodeManagement = State (Node, Data.HashMap.Strict.HashMap String Node)

genNodeId :: NodeManagement Node
genNodeId = do
    (n,x) <- get
    put ((n+1),x)
    return n


insDef :: String -> Node -> NodeManagement ()
insDef str gr = do
  (n,x) <- get
  put ((n), (Data.HashMap.Strict.insert str gr x))
  return ()

createNode :: String -> NodeManagement (LNode String)
createNode label = do
  iid <- genNodeId
  return (iid, label)

findOrCreate :: String ->  NodeManagement (LNode String)
findOrCreate label = do
   (n,mp) <- get
   case (Data.HashMap.Strict.lookup label mp) of
     Nothing -> do
        (nd, ln) <- createNode label
        insDef label nd
        return (nd, ln)
     Just y -> do
        return (y,label)


createEdge :: LNode String -> LNode String -> String -> (LEdge String)
createEdge (x,_) (y,_) label = (x,y,label)
-- mkGraph :: [LNode a] -> [LEdge b] -> gr a

maxNode :: Gr a b -> Node
maxNode gr = case nodeRange gr  of
              (_,max) -> max


actionToGr :: AST.Action -> NodeManagement GrNode

actionToGr (AST.MOpaque (AST.MkName name) extra _ _ _ ) = do
  nd <- createNode $ name
  extraGrphs <- mapM exprToGr extra
  let edgs = map (\(y,yty) -> createEdge y nd (show $ inferType yty))  $ zip (concatMap outNodes extraGrphs) extra
      in
        return $ foldGrKeepIO  ([nd], [nd], [nd], edgs) extraGrphs

actionToGr (AST.FOpaque _ (AST.MkName name) extra acc  _ _ _ ) = do
  nd <- createNode name
  extraGrphs <- mapM exprToGr $ acc:extra
  let edgs = map (\(y,yty) -> createEdge y nd (show $ inferType yty))  $ zip (concatMap outNodes extraGrphs) $ acc:extra
      in
        return $ foldGrKeepIO  ([nd], [nd], [nd], edgs) extraGrphs


actionToGr (AST.PNDMap fctrs action) = do
  nd <- createNode $ "map " ++ show fctrs
  (iOutNodes, iNodes, iInNodes, iEdges) <- actionToGr action
  let edgs = map (\y -> createEdge y nd "map")  iOutNodes
      in
        return ([nd], nd:iNodes, [nd], edgs++iEdges)


actionToGr (AST.PNDFold fctrs action) = do
  nd <- createNode $ "fold " ++ show fctrs
  (iOutNodes, iNodes, iInNodes, iEdges) <- actionToGr action
  let edgs = map (\y -> createEdge y nd "fold")  iOutNodes
      in
        return ([nd], nd:iNodes, [nd], edgs++iEdges)

actionToGr (AST.NDMap fctrs var action ) = do
  nd <- createNode $ "map " ++ show var ++ " " ++ show fctrs
  (iOutNodes, iNodes, iInNodes, iEdges) <- actionToGr action
  let edgs = map (\y -> createEdge y nd "map")  iOutNodes
      in
        return ([nd], nd:iNodes, [nd], edgs++iEdges)

actionToGr (AST.NDFold fctrs var action ) = do
  nd <- createNode $ "fold " ++ show var ++ " " ++ show fctrs
  (iOutNodes, iNodes, iInNodes, iEdges) <- actionToGr action
  let edgs = map (\y -> createEdge y nd "fold")  iOutNodes
      in
        return ([nd], nd:iNodes, [nd], edgs++iEdges)

actionToGr (AST.NDSplit fctrs) = do
  nd <- createNode $ "split " ++ show fctrs
  return ([nd],[nd],[nd],[])

actionToGr (AST.NDMerge fctrs) = do
  nd <- createNode $ "merge " ++ show fctrs
  return ([nd],[nd],[nd],[])

actionToGr (AST.NDDistr sfctrs mfctrs) = do
  nd <- createNode $ "distr " ++ show sfctrs ++ " " ++ show mfctrs
  return ([nd],[nd],[nd],[])

actionToGr (AST.NDZipT fctrs ) = do
  nd <- createNode $ "zip " ++ show fctrs
  return ([nd],[nd],[nd],[])

actionToGr (AST.NDUnzipT fctrs ) = do
  nd <- createNode $ "unzip " ++ show fctrs
  return ([nd],[nd],[nd],[])

actionToGr (AST.Compose actions) = do
    nd <- createNode $ "Compose "
    actionNodes <- mapM actionToGr actions
    return $ chainGr actionNodes nd

actionToGr (AST.Loop start stop step action) = do
  nd <- createNode $ "loop "
  actionNode <- actionToGr action
  return $ chainGr [actionNode] nd

actionToGr node@(AST.Let lhs rhs) = trace(show node) $ do
  (lOutNodes, lNodes, lInNodes, lEdges) <- exprToGr lhs
  (rOutNodes, rNodes, rInNodes, rEdges) <- exprToGr rhs
  let edgs = map (\y -> (map (\z -> createEdge y z (show $ inferType rhs)) lInNodes)) rOutNodes
      in
        return $ (lOutNodes, (lNodes ++ rNodes), rInNodes , lEdges ++ rEdges   )


actionToGr act = do
  nd <- findOrCreate "action"
  return $  ([nd],[nd],[nd],[])


chainGr   :: [GrNode] -> LNode String ->  GrNode
chainGr [] nd =  ([nd],[nd],[nd],[])
chainGr (x:xs) nd =
  do
    let (lOutNodes, lNodes, lInNodes, lEdges) = x
        (rOutNodes, rNodes, rInNodes, rEdges) = chainGr xs nd
        edgs =  map (\y -> (map (\z -> createEdge  z y "") lInNodes) ) rOutNodes
        in
          ([nd], [nd] ++ lNodes ++ rNodes , rInNodes,  (concat edgs) ++ lEdges ++ rEdges)


type GrNode = ([LNode String],[LNode String],[LNode String], [LEdge String])

addGrPart :: GrNode -> GrNode -> GrNode
addGrPart (lOutNodes, lNodes, lInNodes, lEdges)
          (rOutNodes, rNodes, rInNodes, rEdges)
          =
            (lOutNodes ++ rOutNodes, lNodes ++ rNodes, lInNodes ++ rInNodes, lEdges ++ rEdges)

foldGrKeepIO :: GrNode -> [GrNode] -> GrNode
foldGrKeepIO acc [] = acc
foldGrKeepIO acc (x:xs) =
  let (lOutNodes, lNodes, lInNodes, lEdges) = acc
      (rOutNodes, rNodes, rInNodes, rEdges) = x
      in
          (lOutNodes , lNodes ++ rNodes, lInNodes, lEdges ++ rEdges)

outNodes :: ([LNode String],[LNode String],[LNode String], [LEdge String]) -> [LNode String]
outNodes (lOutNodes, lNodes, lInNodes, lEdges) = lOutNodes

exprToGr :: AST.Expr -> NodeManagement ([LNode String],[LNode String],[LNode String], [LEdge String])

exprToGr (AST.Var (AST.MkName name) ty) = do
  nd <- findOrCreate $ name
  return ([nd], [nd] , [nd] , [])

exprToGr (AST.Res action input) =
  case action of
    (AST.Let lhs rhs) -> do
      (iOutNodes, iNodes, iInNodes, iEdges) <- exprToGr input
      (lOutNodes, lNodes, lInNodes, lEdges) <- exprToGr lhs
      (rOutNodes, rNodes, rInNodes, rEdges) <- exprToGr rhs

      let edgs = map (\y -> (map (\z -> createEdge y z (show $ inferType input)) lInNodes)) iOutNodes
          in
            return $ ( rOutNodes, iNodes ++ lNodes ++ rNodes, rInNodes , rEdges ++ lEdges ++ iEdges ++ concat edgs )
    _ -> do
      (iOutNodes, iNodes, iInNodes, iEdges) <- exprToGr input
      (actOutNodes, actNodes, actInNodes, actEdges) <- actionToGr action
      let edgs = map (\y -> (map (\z -> createEdge y z (show $ inferType input)) actInNodes)) iOutNodes
          in
            return $ ( actOutNodes, iNodes ++ actNodes, iInNodes , actEdges ++ iEdges ++ concat edgs )

exprToGr (AST.Tup exprs) = do
  grphs <- mapM exprToGr exprs
  let tupGr = foldl addGrPart ([],[],[],[])  grphs
      in
        trace(show tupGr) $
        return $ foldl addGrPart ([],[],[],[])  grphs



toGr :: AST.Assignment -> NodeManagement (Gr String String)
toGr (AST.Assign lhs rhs) = do
  (lOutNodes, lNodes, lInNodes, lEdges) <- exprToGr lhs
  (rOutNodes, rNodes, rInNodes, rEdges) <- exprToGr rhs
  let edgs = map (\y -> (map (\z -> createEdge y z (show $ inferType rhs)) lInNodes)) rOutNodes
      in
        return $ mkGraph (lNodes ++ rNodes) $ lEdges ++ rEdges ++ (concat edgs)





createDot :: AST.TyTraHLLProgram -> String ->  IO ()
createDot ast str =
  let
    graph = evalState (toGr ast) (0, Data.HashMap.Strict.empty)
    dot = showDot (fglToDot graph)
  in
    do
      writeFile str dot
      print $ show $ maxNode graph
