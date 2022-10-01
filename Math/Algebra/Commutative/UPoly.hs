{-# LANGUAGE Strict #-}

{- |  A 'UPoly' is a Univariate (single variable) Polynomial.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.UPoly (
    UPoly, RingTgtX(..), UPolyUniv,
    upDeg, upTimesNZMonom, upTimesMonom, upRingUniv,
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

upTimesNZMonom  :: IRing c => UPoly c -> Integer -> c -> UPoly c
-- ^ the @c@ is nonzero
upTimesNZMonom  = ssTimesNZMonom (+)

upTimesMonom    :: IRing c => UPoly c -> Integer -> c -> UPoly c
upTimesMonom    = ssTimesMonom (+)

upRingUniv      :: forall c. IRing c => UPolyUniv c
upRingUniv      = UnivL cxRing (RingTgtX cToCx x) cxUnivF
  where
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) _ssUnivF)   = ssAGUniv compare
    ssTimesF    = ssTimes ssUniv (+)
    x           = dcToSS 1 one
    cToCx       = dcToSS 0
    cxFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. (iRFlags @c)
    cxRing      = Ring ssAG cxFlags cxTimes (cToCx one) (cToCx . fromZ) cxDiv2
    cxTimes p q
        | rIsOne cxRing p   = q     -- for efficiency
        | rIsOne cxRing q   = p     -- for efficiency
        | otherwise         = ssTimesF p q
    ssLead'     = ssLead (isZero @c)
    cxDiv2 _doFull p0 p1
        | rIsOne cxRing p1  = (p0, SSZero)  -- for efficiency
        | ssIsZero p1       = (SSZero, p0)
    cxDiv2 doFull p0 p1     = cxDiv2' p0
      where
        d1  = ssDegNZ p1
        c1  = ssHeadCoef p1
        ~t1 = ssTail p1
        cxDiv2' p   =
            if ssIsZero p || ssDegNZ p < d1 then (SSZero, p) else
            let d   = ssDegNZ p
                qd  = d - d1
                (qc, rc)    = bDiv2 doFull (ssHeadCoef p) c1
                -- want p = (c1*x^d1 + t1) * (qc*x^qd + q2) + (rc*x^d + r2):
                ~p' = agPlus ssAG !$ ssTail p !$ upTimesMonom t1 qd (neg qc)
                ~qr2    = if doFull || isZero rc then cxDiv2' p' else (SSZero, p')
            in  (ssLead' qc qd (fst qr2), ssLead' rc d (snd qr2))
    cxUnivF     :: Ring t -> RingTgtX c t -> UPoly c -> t
    cxUnivF tR (RingTgtX cToT xT) p     = case p of     -- uses Horner's rule
        SSZero          -> rZero tR
        (SSNZ c' d' r') -> cxToT (cToT c') d' r'
          where
            (*~)                    = rTimes tR
            cxToT t 0 SSZero        = t
            cxToT t d SSZero        = t *~ expt1 (*~) xT d
            cxToT t d (SSNZ c e r)  = cxToT (rPlus tR (t *~ expt1 (*~) xT (d - e)) (cToT c)) e r
    -- @@ use _ssUnivF !?

-- @@ -> RMod, RAlg (if R comm.), R[X] * M[X] ?


upShowPrec      :: String -> ShowPrec c -> ShowPrec (UPoly c)
-- ^ varS prec > '^'
upShowPrec varS = ssShowPrec dSP
  where
    dSP _prec d = case d of
        0   -> "1"
        1   -> varS
        _   -> varS ++ '^' : show d
