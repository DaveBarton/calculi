{-# LANGUAGE Strict #-}

{- |  A 'UPoly' is a Univariate (single variable) Polynomial.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.UPoly (
    UPoly, RingTgtX(..), UPolyUniv,
    upDeg, upUniv,
    upShowPrec
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum

import Data.Bifunctor (bimap)


type UPoly c    = SparseSum c Integer
-- ^ normally we require (and assume) exponents >= 0

data RingTgtX c t       = RingTgtX (c -> t) t
-- ^ a ring homomorphism C -> T, and an element that commutes with image(C)

type UPolyUniv c        = UnivL Ring (RingTgtX c) (->) (UPoly c)
-- ^ a @Ring (UPoly c)@, @RingTgtX c (UPoly c)@, and a function for mapping to other 'Ring's
-- that have a @RingTgtX c@


upDeg           :: UPoly c -> Integer
upDeg           = sparseSum (-1) (\_ d _ -> d)

upUniv          :: forall c. Ring c -> UPolyUniv c
upUniv cR       = UnivL cxRing (RingTgtX cToCx x) cxUnivF
  where
    AbelianGroup _ cEq _ _ cIsZero cNeg     = cR.ag
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) _ssUnivF)   = ssAGUniv cR.ag compare
    x           = dcToSS 1 cR.one
    cToCx       = dcToSS 0
    cxFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. cR.rFlags
    nzds        = hasEIBit cR.rFlags NoZeroDivisors
    cxRing      = Ring ssAG cxFlags (if nzds then cxTimesNzds else ssTimes ssUniv cR (+))
                    (cToCx cR.one) (cToCx . cR.fromZ) cxDiv
    cxIsOne     = sparseSum False (\ ~c d ~t -> d == 0 && cEq c cR.one && null t)
        -- note wrong for 0 Ring, just cxIsOne => (== one)
    cxTimesNzds p q
        | cxIsOne p     = q     -- for efficiency
        | cxIsOne q     = p     -- for efficiency
        | otherwise     = ssTimesNzds ssUniv cR (+) p q
    minusTimesMonom p s d c     =   -- p - s*c*vars^d
        if cR.isZero c then p else
            ssAG.plus !$ p !$
                (if nzds then ssTimesNzdMonom else ssTimesMonom) cR (+) s d (cNeg c)
    {-# INLINE minusTimesMonom #-}
    
    ssLead'     = ssLead cIsZero
    cxDiv doFull p0 p1  = if cxIsOne p1 then (p0, ssZero) else  -- for efficiency
                            case pop p1 of
        Nothing                     -> (ssZero, p0)
        Just (SSTerm !c1 !d1, t1)   -> {-# SCC cxDiv' #-} cxDiv' p0
          where
            cxDiv' p    = case pop p of
                Nothing             -> (ssZero, p)
                Just (SSTerm c !d, t)
                    | d < d1        -> (ssZero, p)
                    | otherwise     ->
                        let qd  = d - d1
                            (qc, rc)    = cR.bDiv doFull c c1
                            -- want p = (c1*x^d1 + t1) * (qc*x^qd + q2) + (rc*x^d + r2):
                            ~p'     = minusTimesMonom t t1 qd qc
                            qr2     = if doFull.b || cIsZero rc then cxDiv' p' else (ssZero, p')
                        in  bimap (ssLead' qc qd) (ssLead' rc d) qr2
    cxUnivF     :: Ring t -> RingTgtX c t -> UPoly c -> t
    cxUnivF tR (RingTgtX cToT xT)   = sparseSum tR.zero (cxToT . cToT)  -- uses Horner's rule
      where
        (*~)        = tR.times
        -- cxToT t d p = t*xT^d + p(xT), d > degree(p)
        cxToT t d   = sparseSum (if d == 0 then t else t *~ expt1 (*~) xT d)
            (\c e -> cxToT (tR.plus (t *~ expt1 (*~) xT (d - e)) (cToT c)) e)
    -- @@ use _ssUnivF !?

-- @@ -> RMod, RAlg (if R comm.), R[X] * M[X] ?


upShowPrec      :: String -> ShowPrec c -> ShowPrec (UPoly c)
-- ^ varS prec > '^'
upShowPrec varS = ssShowPrec (varPowShowPrec varS)
