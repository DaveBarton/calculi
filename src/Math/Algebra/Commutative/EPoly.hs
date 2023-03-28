{-# LANGUAGE Strict #-}

{- |  An 'EPoly' is an \"Expanded\" or \"Exponent Vector\" Polynomial. That is, each term
    consists of a coefficient and an exponent vector ('ExponVec').
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.EPoly (
    ExponVec, eVecTotDeg, evMake, exponsL, evPlus, evMinusMay, evDividesF, evLCMF, gRevLex,
    EPoly, RingTgtXs(..), EPolyUniv,
    headTotDeg, epTimesNZMonom, epTimesMonom, epRingUniv, epGBPOps
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.GroebnerBasis (SPair(..), GBPolyOps(..))

import Data.Array.Base (numElements, unsafeAt)
import Data.Array.IArray (bounds, elems, listArray)
import Data.Array.Unboxed (UArray)
import Data.Bits (xor, unsafeShiftL, unsafeShiftR)
import Data.Maybe (fromJust)
import Data.Word (Word64)


zipWithExact    :: (a -> b -> c) -> [a] -> [b] -> [c]
-- ^ or use library @safe@
zipWithExact f xs ys    = assert (length xs == length ys) (zipWith f xs ys)


data Expons     = Expons1 Word64
                | Expons2 Word64 Word64
                | ExponsN (UArray Int Word)
    deriving Eq     -- e.g. for testing
-- In 'Expons1' and 'Expons2', the reversed exponents are stored in big-endian order.

instance Show Expons where  -- for debugging
    show (Expons1 w)        = show0x w
    show (Expons2 w v)      = show0x w ++ " " ++ show0x v
    show (ExponsN a)        = show (elems a)

data ExponVec   = ExponVec { totDeg :: Word, expons :: Expons }
    deriving (Eq, Show)     -- e.g. for testing & debugging
-- ^ the number of variables must be fixed;
-- if totDeg < 2^8 then we use Expons1 for nVars <= 8 or Expons2 for nVars <= 16,
-- else if totDeg < 2^16 then we use Expons1 for nVars <= 4 or Expons2 for nVars <= 8

eVecTotDeg      :: ExponVec -> Word
eVecTotDeg      = (.totDeg)

perWord64       :: Int -> Word -> Int
perWord64 nVars td
    | td < 256 && nVars > 4     = 8
    | td < 0x1_0000             = 4
    | otherwise                 = -1

evMake          :: [Word] -> ExponVec
-- ^ The exponents are listed in little-endian order.
evMake es       =
    let td          = sum es
        nVars       = length es
        perW        = perWord64 nVars td
        nBits       = if perW == 8 then 8 else 16
        packW []        = 0
        packW (e : t)   = packW t `unsafeShiftL` nBits + fromIntegral e
        exps
            | nVars <= perW     = Expons1 (packW es)
            | nVars <= 2*perW   = let (es1, es0)   = splitAt (nVars - perW) es
                                  in  Expons2 (packW es0) (packW es1)
            | otherwise         = ExponsN (listArray (0, nVars - 1) es)
    in  ExponVec td exps

exponsL         :: Int -> ExponVec -> [Word]
-- ^ The exponents are listed in little-endian order.
exponsL nVars (ExponVec td es)  = case es of
    Expons1 w       -> bytesL nVars w []
    Expons2 w0 w1   -> bytesL (nVars - perW) w1 (bytesL perW w0 [])
    ExponsN a       -> elems a
  where
    perW        = perWord64 nVars td
    nBits       = if perW == 8 then 8 else 16
    mask        = if perW == 8 then 0xFF else 0xFFFF
    bytesL          :: Int -> Word64 -> [Word] -> [Word]
    bytesL n w ~t   = if n == 0 then t else
        fromIntegral (w .&. mask) : bytesL (n - 1) (w `unsafeShiftR` nBits) t

evPlus          :: Int -> Op2 ExponVec
evPlus nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   = go es es'
  where
    td      = d + d'
    perW    = perWord64 nVars td
    go (Expons1 w)   (Expons1 w')     | nVars <= perW   =
        ExponVec td (Expons1 (w + w'))
    go (Expons2 w v) (Expons2 w' v')  | nVars <= 2*perW =
        ExponVec td (Expons2 (w + w') (v + v'))
    go _             _                                  =
        evMake (zipWithExact (+) (exponsL nVars ev) (exponsL nVars ev'))

evMinusMay      :: Int -> ExponVec -> ExponVec -> Maybe ExponVec
evMinusMay nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   =
    if not (evDividesF nVars ev' ev) then Nothing else Just (evMinus es es')
  where
    evMinus (Expons1 w)   (Expons1 w')                      =
        ExponVec (d - d') (Expons1 (w - w'))
    evMinus (Expons2 w v) (Expons2 w' v')   | nVars > perW  =
        ExponVec td (Expons2 (w - w') (v - v'))
      where
        td      = d - d'
        perW    = perWord64 nVars td
    evMinus _             _                                 =
        evMake (zipWithExact (-) (exponsL nVars ev) (exponsL nVars ev'))

evDividesF      :: Int -> ExponVec -> ExponVec -> Bool
-- ^ note args reversed from evMinusMay; really vars^ev1 `divides` vars^ev2
evDividesF nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   = d <= d' &&    -- for efficiency
    expsDivs es es'
  where
    expsDivs (Expons1 w)   (Expons1 w')     = bytesDivs w w'
    expsDivs (Expons2 w v) (Expons2 w' v')  = bytesDivs w w' && bytesDivs v v'
    expsDivs _             _                =
        and (zipWithExact (<=) (exponsL nVars ev) (exponsL nVars ev'))
    bytesDivs w w'      = w <= w' && (w' - w) .&. mask `xor` w .&. mask `xor` w' .&. mask == 0
      where     -- check if any bytes subtracted in (w' - w) cause borrowing from any mask bits
        perW        = perWord64 nVars d
        mask        = if perW == 8 then 0x0101_0101_0101_0100 else 0x0001_0001_0001_0000

evLCMF          :: Int -> Op2 ExponVec  -- really Least Common Multiple of vars^ev1 and vars^ev2
evLCMF nVars ev ev'     = evMake (zipWithExact max (exponsL nVars ev) (exponsL nVars ev'))

gRevLex         :: Cmp ExponVec
-- ^ The variables go from most main (variable 0) to least main, in little-endian order.
gRevLex (ExponVec d es) (ExponVec d' es')       =
    case compare d d' of
        EQ      -> cmpExps es es'
          where
            cmpExps (Expons1 w)   (Expons1 w')     = compare w' w
            cmpExps (Expons2 w v) (Expons2 w' v')  = case compare w' w of
                EQ      -> compare v' v
                other   -> other
            cmpExps (ExponsN a)   (ExponsN a')     =
                assert (bounds a == bounds a') (go (numElements a - 1))
              where
                go i    =
                    if i < 0 then EQ else
                    let c   = compare (unsafeAt a' i) (unsafeAt a i)
                    in  if c /= EQ then c else go (i - 1)
            cmpExps _             _                = undefined
        other   -> other


type EPoly c    = SparseSum c ExponVec
-- ^ evPlus must be order-preserving for the term order, and it must be a well ordering

data RingTgtXs c t      = RingTgtXs (c -> t) [t]
-- ^ a ring homomorphism C -> T, and a list of elements that commute with image(C)

type EPolyUniv c        = UnivL Ring (RingTgtXs c) (->) (EPoly c)
-- ^ a @Ring (EPoly c)@, @RingTgtXs c (EPoly c)@, and a function for mapping to other 'Ring's
-- that have a @RingTgtXs c@


headTotDeg      :: EPoly c -> Integer
headTotDeg p    = if ssIsZero p then -1 else fromIntegral (ssDegNZ p).totDeg

epTimesNZMonom  :: IRing c => Int -> EPoly c -> ExponVec -> c -> EPoly c
-- ^ the @c@ is nonzero
epTimesNZMonom nVars    = ssTimesNZMonom (evPlus nVars)

epTimesMonom    :: IRing c => Int -> EPoly c -> ExponVec -> c -> EPoly c
epTimesMonom nVars      = ssTimesMonom (evPlus nVars)
-- {-# SCC epTimesMonom #-}

epRingUniv      :: forall c. IRing c => Int -> Cmp ExponVec -> EPolyUniv c
epRingUniv nVars evCmp  = UnivL epRing (RingTgtXs cToEp xs) epUnivF
  where
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) ssUnivF)    = ssAGUniv iRing.ag evCmp
    ssTimesF    = ssTimes ssUniv (evPlus nVars)
    evZero      = evMake (replicate nVars 0)
    inds        = [0 .. nVars - 1]
    xs          = [dcToSS (evMake [if i == j then 1 else 0 | j <- inds]) iOne | i <- inds]
    cToEp       = dcToSS evZero
    epFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. (iRFlags @c)
    epRing      = Ring ssAG epFlags epTimes (cToEp iOne) (cToEp . iFromZ) epDiv
    epTimes p q
        | rIsOne epRing p   = q     -- for efficiency
        | rIsOne epRing q   = p     -- for efficiency
        | otherwise         = ssTimesF p q
    ssLead'     = ssLead (iIsZero @c)
    epDiv _doFull p0 p1
        | rIsOne epRing p1              = (p0, SSZero)  -- for efficiency
    epDiv _doFull p0 SSZero             = (SSZero, p0)
    epDiv  doFull p0 (SSNZ c1 ev1 ~t1)  = {-# SCC epDiv' #-} epDiv' p0
      where
        epDiv' p@SSZero                     = (SSZero, p)
        epDiv' p
            | evCmp (ssDegNZ p) ev1 == LT   = (SSZero, p)
        epDiv' p@(SSNZ c ev ~t)             =
            case evMinusMay nVars ev ev1 of
                Nothing     -> -- {-# SCC "sub-top-epDiv'" #-}
                    if not doFull then (SSZero, p) else
                    let (q2, r2) = epDiv' t
                    in (q2, SSNZ c ev r2)
                Just qd     -> -- {-# SCC "top-etc-epDiv'" #-}
                    let (qc, rc)    = iBDiv doFull c c1
                        -- want p = (c1*x^ev1 + t1) * (qc*x^qd + q2) + (rc*x^ev + r2):
                        ~p'         = {-# SCC "epDiv'-+-qM*" #-} agPlus ssAG !$ t
                                        !$ {-# SCC epTimesMonom #-}
                                           epTimesMonom nVars t1 qd (iNeg qc)
                        ~qr2    = if doFull || iIsZero rc then epDiv' p'
                                  else (SSZero, p')
                    in  (ssLead' qc qd (fst qr2), ssLead' rc ev (snd qr2))
    epUnivF     :: Ring t -> RingTgtXs c t -> EPoly c -> t
    epUnivF tR (RingTgtXs cToT xTs)     = ssUnivF tR.ag (TgtArrsF dcToT)
      where
        dcToT ev c  =
            foldr1 tR.times (cToT c : zipWithExact (rExpt tR) xTs (exponsL nVars ev))


epGBPOps        :: forall c. Cmp ExponVec -> Bool -> Ring c -> [String] -> ShowPrec c -> Bool ->
                    GBPolyOps ExponVec (SSTerm c ExponVec) (EPoly c)
{- ^ In @ep58GBPOps evCmp isGraded cR varSs cShowPrec useSugar@, @varSs@ lists more main
    variables first, and each @varS@ has precedence > '^'. -}
epGBPOps evCmp isGraded cR varSs cShowPrec useSugar     = GBPolyOps { numTerms = length, .. }
  where
    nVars               = length varSs
    evDivides           = evDividesF nVars
    evLCM               = evLCMF nVars
    evTotDeg            = (.totDeg)
    nEvGroups           = nVars
    evGroup             = exponsL nVars
    isRev               = nVars > 0 && evCmp (evMake es) (evMake (reverse es)) == GT
      where
        ~es         = 1 : replicate (nVars - 1) 0
    evShow ev           = concat (zipWith pow varSs es)
      where
        es          = (if isRev then id else reverse) (exponsL nVars ev)
        pow varS e  = case e of
            0   -> ""
            1   -> varS
            _   -> varS ++ '^' : show e
    UnivL pR (RingTgtXs _cToP _xs) _pUnivF  = withRing cR epRingUniv nVars evCmp
    leadEvNZ            = sparseSum undefined (\_ ev _ -> ev)
    monicize            = withRing cR ssMonicize
    extraSPairs _ _ _   = []
    sPoly f g (SPair { m })     = minus pR.ag (shift f) (shift g)
      where
        shift (SSNZ _ ev t) = ssShift (evPlus nVars (fromJust (evMinusMay nVars m ev))) t
        shift _             = undefined
    homogDeg0           = if isGraded then sparseSum 0 (\_ ev _ -> evTotDeg ev) else
        ssFoldr (\ _ ev n -> max ev.totDeg n) 0
    cons                = ssCons
    unconsNZ            = ssUnconsNZ
    pShow               = ssShowPrec (const evShow) cShowPrec 0
