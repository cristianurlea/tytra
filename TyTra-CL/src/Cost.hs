module Cost where

import           AST
import           Data.Generics.Uniplate.Data
import           Inference
import qualified Debug.Trace(trace)

defaultRawCost = 1



computePrimCost :: PrimType -> RawCost
computePrimCost pty =
  case pty of
    Float -> defaultRawCost { size =  MkResourceUse { luts = 32, blockRams = 32, multipliers = 0 } }
    Double -> defaultRawCost { size =  MkResourceUse { luts = 64, blockRams = 64, multipliers = 0 }}
    Short -> defaultRawCost { size =  MkResourceUse { luts = 64, blockRams = 64, multipliers = 0 } }
    Char -> defaultRawCost { size =  MkResourceUse { luts = 8, blockRams = 8, multipliers = 0 } }
    Fix intg remain -> defaultRawCost { size =  MkResourceUse { luts = intg, blockRams = intg, multipliers = 0 }
                                                +  MkResourceUse { luts = remain, blockRams = remain, multipliers = 0 } }

computeTypeCost :: Type -> RawCost
computeTypeCost ty =
  case ty of
    Prim pty -> computePrimCost pty
    Vec innerty sz -> computeTypeCost innerty * fromInteger sz
    Tuple tys -> sum (map computeTypeCost tys)



appendCost :: RawCost -> RawCost -> RawCost
appendCost  MkRawCost { delay = d1, latency = l1, size = s1}
            MkRawCost { delay = d2, latency = l2, size = s2}
            =
              MkRawCost { delay = d1 + d2, latency = l1 + l2, size = s1}


maxLatencySumResource :: RawCost -> RawCost -> RawCost
maxLatencySumResource   MkRawCost { delay = d1, latency = l1, size = s1}
                        MkRawCost { delay = d2, latency = l2, size = s2}
                        =
                          MkRawCost { delay = max d1 d2 , latency =  max l1 l2, size = s1 + s2}

{-


  t0 + TD = one item of work

  RawCOst

-}




costlyMcCostFace :: Expr -> RawCost
costlyMcCostFace (Var _ ty) = computeTypeCost ty




finishAt :: RawCost -> Cycle
finishAt MkRawCost { delay = id1, latency = il1, size = is1} = il1 + id1


linearCost :: Integer -> RawCost -> RawCost -> RawCost
linearCost fctr actionCost inputCost =
  let
      MkRawCost { delay = ad, latency = al, size = as} = actionCost
      MkRawCost { delay = ind, latency = inl, size = ins} = inputCost
      finishInputTime = finishAt inputCost
      thisLatency = maximum [finishInputTime, al]
      in
        MkRawCost {delay = ad * fctr, latency = thisLatency, size = as + ins}


ndMapCost :: [(Integer, MVariant)] -> Integer -> MVariant -> RawCost -> RawCost -> RawCost
ndMapCost fctrs inputSize bvar actionCost inputCost =
  let
      MkRawCost { delay = ad, latency = al, size = as} = actionCost
      MkRawCost { delay = ind, latency = inl, size = ins} = inputCost
      finishInputTime = finishAt inputCost
      thisLatency = maximum [finishInputTime, al]
      in
        case (fctrs, bvar) of
          ([],Seq)  -> MkRawCost {delay = ad * inputSize, latency = thisLatency, size = as + ins}
          ([],Par)  -> MkRawCost {delay = ad , latency = thisLatency, size = (as * fromInteger inputSize) + ins}
          ([],Pipe)  -> MkRawCost {delay = inputSize, latency = thisLatency + (ad * inputSize), size = (as * fromInteger inputSize) + ins}
          ((x, tv):xs, bbvar) -> let thatCost = ndMapCost xs (inputSize `div` x) bbvar actionCost inputCost
                                     thisCost = ndMapCost [] x tv thatCost 0
                                     in
                                      -- Debug.Trace.trace (show thisCost ++ " * " ++ show thatCost ++ " s" ++ show inputSize) $
                                      thisCost


ndFoldCost :: [(Integer, FVariant)] -> Integer -> FVariant -> RawCost -> RawCost -> RawCost
ndFoldCost fctrs inputSize bvar actionCost inputCost =
  let
    MkRawCost { delay = ad, latency = al, size = as} = actionCost
    MkRawCost { delay = ind, latency = inl, size = ins} = inputCost
    finishInputTime = finishAt inputCost
    thisLatency = maximum [finishInputTime, al]
    in --Debug.Trace.trace (show actionCost ++ " " ++ show inputSize) $
      case (fctrs, bvar) of
      ([],FSeq)  -> MkRawCost {delay = ad * inputSize, latency = thisLatency, size = as + ins}
      ([],Tree)  -> MkRawCost {delay = ad , latency = thisLatency, size = (as * fromInteger inputSize) + ins}
      ([],FPipe)  -> MkRawCost {delay = inputSize, latency = thisLatency + (ad * inputSize), size = (as * fromInteger inputSize) + ins}
      ((x, tv):xs, bbvar) ->
        let thatCost = ndFoldCost xs (inputSize `div` x) bbvar actionCost inputCost
            thisCost = ndFoldCost [] x tv thatCost 0
            in
             --Debug.Trace.trace (show thisCost ++ " * " ++ show thatCost) $
             thisCost

computeExprCost :: Expr -> RawCost
computeExprCost expr =
  case expr of
    Var _ ty -> computeTypeCost ty

    Res act input ->
      let
        inputCost = computeExprCost input
        MkRawCost { delay = ind, latency = inl, size = ins} = inputCost

        outputCost = computeTypeCost (inferType expr)
        inputType = inferType input
        inputSize = sizeTy inputType
      in
        case act of
          MOpaque _ extra _ _ rc ->
            let extraCosts = map computeExprCost extra
                finishInputTime = finishAt inputCost
                finishExtraTimes = map finishAt extraCosts
                thisLatency = maximum $ finishInputTime:finishExtraTimes
                MkRawCost { delay = td, latency = tl, size = ts} = rc
                in
                  MkRawCost {delay = td, latency = tl + thisLatency, size = ts + ins}

          FOpaque assoc _ extra acc _ _ rc ->
            let extraCosts = map computeExprCost extra
                finishInputTime = finishAt inputCost
                finisAccTime = finishAt $ computeExprCost acc
                finishExtraTimes = map finishAt extraCosts
                thisLatency = maximum $ finishInputTime:finishExtraTimes
                MkRawCost { delay = td, latency = tl, size = ts} = rc
                in
                  MkRawCost {delay = td, latency = tl + thisLatency + finisAccTime, size = ts + ins}
          -- assume PNDMap equiv to fully seq map

          PNDMap fctrs innerAction ->
            case innerTy fctrs inputType of
              Nothing -> error "Type mismatch in PNDMap"
              Just ty -> linearCost inputSize ( computeExprCost (Res innerAction (Var (MkName "foo") ty)) ) inputCost

          PNDFold fctrs innerAction ->
            case innerTy fctrs inputType of
              Nothing -> error "Type mismatch in PNDFold"
              Just ty -> linearCost inputSize ( computeExprCost (Res innerAction (Var (MkName "foo") ty)) ) inputCost

          NDMap fctrs bvar innerAction ->
            case innerTy (map fst fctrs) inputType of
              Nothing -> error "Type mismatch in NDMap"
              Just ty -> ndMapCost fctrs inputSize bvar ( computeExprCost (Res innerAction (Var (MkName "foo") ty)) ) inputCost

          NDFold fctrs bvar innerAction ->
            case innerTy (map fst fctrs) inputType of
              Nothing -> error "Type mismatch in NDFold"
              Just ty -> if isAssoc innerAction
                 then ndFoldCost fctrs inputSize bvar ( computeExprCost (Res innerAction (Var (MkName "foo") ty)) ) inputCost
                 else linearCost inputSize ( computeExprCost (Res innerAction (Var (MkName "foo") ty)) ) inputCost

          NDSplit _ -> defaultRawCost + 2 + inputCost
          NDMerge _ -> defaultRawCost + inputCost
          NDDistr _ _ -> defaultRawCost + inputCost
          NDZipT _ -> computeTypeCost (inferType input) + inputCost
          NDUnzipT _ -> computeTypeCost (inferType input)+ inputCost
          Compose acts -> defaultRawCost -- $ (sum $ map computeActionCost acts) + inputCost
          Let lhs rhs -> computeExprCost rhs + inputCost
          Loop start stop step  act ->  computeExprCost (Res act (Var (MkName "foo") inputType))  * (fromInteger ( (stop - start) `div` step )) + inputCost


    Tup xs -> sum (map computeExprCost xs)





computeCost :: Assignment -> RawCost
computeCost (Assign lhs rhs) = computeExprCost rhs -- + computeExprCost lhs





{- Propagation Cost
   How many cycles does it take to buffer
-}
