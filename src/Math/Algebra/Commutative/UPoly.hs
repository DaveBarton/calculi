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


type UPoly c    = SparseSum c Integer
-- ^ normally we require (and assume) exponents >= 0

data RingTgtX c t       = RingTgtX (c -> t) t
-- ^ a ring homomorphism C -> T, and an element that commutes with image(C)

type UPolyUniv c        = UnivL Ring (RingTgtX c) (->) (UPoly c)
-- ^ a @Ring (UPoly c)@, @RingTgtX c (UPoly c)@, and a function for mapping to other 'Ring's
-- that have a @RingTgtX c@


upDeg           :: UPoly c -> Integer
upDeg p         = if ssIsZero p then -1 else ssDegNZ p

upUniv          :: forall c. Ring c -> UPolyUniv c
upUniv cR       = UnivL cxRing (RingTgtX cToCx x) cxUnivF
  where
    AbelianGroup _ cEq _ _ cIsZero cNeg     = cR.ag
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) _ssUnivF)   = ssAGUniv cR.ag compare
    x           = dcToSS 1 cR.one
    cToCx       = dcToSS 0
    cxFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. cR.rFlags
    cxRing      = Ring ssAG cxFlags cxTimes (cToCx cR.one) (cToCx . cR.fromZ) cxDiv
    cxIsOne (SSNZ c 0 SSZero)   = cEq c cR.one
    cxIsOne _                   = False     -- note wrong for 0 Ring, just cxIsOne => (== one)
    cxTimesNzds p q
        | cxIsOne p     = q     -- for efficiency
        | cxIsOne q     = p     -- for efficiency
        | otherwise     = ssTimesNzds ssUniv cR (+) p q
    cxTimes
        | hasEIBit cR.rFlags NoZeroDivisors     = cxTimesNzds
        | otherwise                             = ssTimes ssUniv cR (+)
    upTimesMonom s d c
        | cR.isZero c                           = SSZero
        | hasEIBit cR.rFlags NoZeroDivisors     = ssTimesNzdMonom cR (+) s d c
        | otherwise                             = ssTimesMonom cR (+) s d c
    ssLead'     = ssLead cIsZero
    cxDiv _doFull p0 p1
        | cxIsOne p1  = (p0, SSZero)    -- for efficiency
        | ssIsZero p1       = (SSZero, p0)
    cxDiv  doFull p0 p1     = cxDiv' p0
      where
        d1  = ssDegNZ p1
        c1  = ssHeadCoef p1
        ~t1 = ssTail p1
        cxDiv' p    =
            if ssIsZero p || ssDegNZ p < d1 then (SSZero, p) else
            let d   = ssDegNZ p
                qd  = d - d1
                (qc, rc)    = cR.bDiv doFull (ssHeadCoef p) c1
                -- want p = (c1*x^d1 + t1) * (qc*x^qd + q2) + (rc*x^d + r2):
                ~p' = ssAG.plus !$ ssTail p !$ upTimesMonom t1 qd (cNeg qc)
                ~qr2    = if doFull.b || cIsZero rc then cxDiv' p' else (SSZero, p')
            in  (ssLead' qc qd (fst qr2), ssLead' rc d (snd qr2))
    cxUnivF     :: Ring t -> RingTgtX c t -> UPoly c -> t
    cxUnivF tR (RingTgtX cToT xT) p     = case p of     -- uses Horner's rule
        SSZero          -> tR.zero
        SSNZ c' d' r'   -> cxToT (cToT c') d' r'
          where
            (*~)                    = tR.times
            cxToT t 0 SSZero        = t
            cxToT t d SSZero        = t *~ expt1 (*~) xT d
            cxToT t d (SSNZ c e r)  = cxToT (tR.plus (t *~ expt1 (*~) xT (d - e)) (cToT c)) e r
    -- @@ use _ssUnivF !?

-- @@ -> RMod, RAlg (if R comm.), R[X] * M[X] ?


upShowPrec      :: String -> ShowPrec c -> ShowPrec (UPoly c)
-- ^ varS prec > '^'
upShowPrec varS = ssShowPrec (varPowShowPrec varS)
