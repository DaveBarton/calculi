{-# LANGUAGE Strict #-}

{- |  A 'UPoly' is a Univariate (single variable) Polynomial.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.UPoly {- @@() -} where

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

upMonomTimes    :: Ring c -> c -> Integer -> UPoly c -> UPoly c
upMonomTimes cRing c d  = if cIs0 c then const SSZero else    -- for efficiency
    ssShiftMapC cIs0 (+ d) (rTimes cRing c)
  where cIs0    = rIsZero cRing

upRingUniv      :: Ring c -> UPolyUniv c
upRingUniv cRing        = UnivL cxRing (RingTgtX c2cx x) cxUnivF
  where
    Ring cAG _ cOne _ cDiv2 = cRing
    ssUniv@(UnivL ssAG (TgtArrsF dc2ss) _ssUnivF)   = ssAGUniv compare cAG
    ssTimesF    = ssTimes ssUniv (+) cRing
    x           = dc2ss 1 cOne
    c2cx        = dc2ss 0
    cxRing      = Ring ssAG cxTimes (c2cx cOne) (c2cx . rFromZ cRing) cxDiv2
    cxTimes p q
        | rOneQ cxRing p    = q     -- for efficiency
        | rOneQ cxRing q    = p     -- for efficiency
        | otherwise         = ssTimesF p q
    ssLead'     = ssLead (isZero cAG)
    cxDiv2 _doFull p0 p1
        | rOneQ cxRing p1   = (p0, SSZero)  -- for efficiency
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
                (qc, rc)    = cDiv2 doFull (ssHeadCoef p) c1
                -- want p = (qc*x^qd + q2) * (c1*x^d1 + t1) + (rc*x^d + r2):
                ~p' = agPlus ssAG !$ ssTail p !$ upMonomTimes cRing (agNeg cAG qc) qd t1
                ~qr2    = if doFull || isZero cAG rc then cxDiv2' p' else (SSZero, p')
            in  (ssLead' qc qd (fst qr2), ssLead' rc d (snd qr2))
    cxUnivF     :: Ring t -> RingTgtX c t -> UPoly c -> t
    cxUnivF tR (RingTgtX c2t xT) p  = case p of     -- uses Horner's rule
        SSZero          -> rZero tR
        (SSNZ c' d' r') -> cx2t (c2t c') d' r'
          where
            (*:)                    = rTimes tR
            cx2t t 0 SSZero         = t
            cx2t t d SSZero         = t *: expt1 (*:) xT d
            cx2t t d (SSNZ c e r)   = cx2t (rPlus tR (t *: expt1 (*:) xT (d - e)) (c2t c)) e r
    -- @@ use _ssUnivF !?

-- @@ -> RMod, RAlg (if R comm.), R[X] * M[X] ?


upShowPrec      :: String -> ShowPrec c -> ShowPrec (UPoly c)   -- ^ varS prec > '^'
upShowPrec varS = ssShowPrec dSP
  where
    dSP _prec d = case d of
        0   -> "1"
        1   -> varS
        _   -> varS ++ '^' : show d
