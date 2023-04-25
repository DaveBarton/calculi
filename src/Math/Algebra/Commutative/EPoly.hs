{-# LANGUAGE Strict #-}

{- |  An 'EPoly' is an \"Expanded\" or \"Exponent Vector\" Polynomial. That is, each term
    consists of a coefficient and an exponent vector ('ExponVec').
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.EPoly (
    ExponVec, eVecTotDeg, evMake, exponsL, evPlus, evMinusMay, evDividesF, evLCMF, epEvCmpF,
    EPoly, RingTgtXs(..), EPolyUniv, EPolyOps(..),
    headTotDeg, epOps, EvVarSs(..), evVarSs, evShowPrecF, epGBPOps, epCountZeros
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.GroebnerBasis (SPair(..), GBPolyOps(..), StdEvCmp(..))

import Data.Bits (xor, unsafeShiftL, unsafeShiftR)
import Data.Maybe (fromJust)
import qualified Data.Vector.Unboxed as U
import Data.Word (Word64)

import Control.Parallel.Strategies (parMap, rseq)


zipWithExact    :: (a -> b -> c) -> [a] -> [b] -> [c]
-- ^ or use library @safe@
zipWithExact f xs ys    = assert (length xs == length ys) (zipWith f xs ys)


data Expons     = Expons1 Word64
                | Expons2 Word64 Word64
                | ExponsN (U.Vector Word)
    deriving Eq     -- e.g. for testing
-- The (possibly reversed) exponents are stored in big-endian order, for fast comparisons. That
-- is, the exponents are reversed (less main vars first) if isRev, e.g. GrRevLexCmp.

instance Show Expons where  -- e.g. for testing & debugging
    show (Expons1 w)        = show0x w
    show (Expons2 w v)      = show0x w ++ " " ++ show0x v
    show (ExponsN a)        = show (U.toList a)

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
-- ^ The exponents are listed in big-endian order.
evMake es       =
    let td          = sum es
        nVars       = length es
        perW        = perWord64 nVars td
        nBits       = if perW == 8 then 8 else 16
        packW       = foldl' (\w e -> w `unsafeShiftL` nBits + fromIntegral e) 0
        exps
            | nVars <= perW     = Expons1 (packW es)
            | nVars <= 2*perW   = let (es0, es1)   = splitAt perW es
                                  in  Expons2 (packW es0) (packW es1)
            | otherwise         = ExponsN (U.fromListN nVars es)
    in  ExponVec td exps

exponsL         :: Int -> ExponVec -> [Word]
-- ^ The exponents are listed in big-endian order.
exponsL nVars (ExponVec td es)  = case es of
    Expons1 w       -> bytesL nVars w []
    Expons2 w0 w1   -> bytesL perW w0 (bytesL (nVars - perW) w1 [])
    ExponsN a       -> U.toList a
  where
    perW        = perWord64 nVars td
    nBits       = if perW == 8 then 8 else 16
    mask        = if perW == 8 then 0xFF else 0xFFFF
    bytesL          :: Int -> Word64 -> [Word] -> [Word]
    bytesL n w ~t   = if n == 0 then t else
        bytesL (n - 1) (w `unsafeShiftR` nBits) (fromIntegral (w .&. mask) : t)

evPlus          :: Int -> Op2 ExponVec
evPlus nVars ev@(ExponVec d es) ev'@(ExponVec d' es')
    | perW == perWord64 nVars (min d d')    = ExponVec td (go es es')
    | otherwise                             = slow
  where
    td      = d + d'
    perW    = perWord64 nVars td
    go (Expons1 w)   (Expons1 w')       = Expons1 (w + w')
    go (Expons2 w v) (Expons2 w' v')    = Expons2 (w + w') (v + v')
    go (ExponsN a)   (ExponsN a')       = ExponsN (U.zipWith (+) a a')
    go _             _                  = undefined
    ~slow   = evMake (zipWithExact (+) (exponsL nVars ev) (exponsL nVars ev'))

evMinusMay      :: Int -> ExponVec -> ExponVec -> Maybe ExponVec
evMinusMay nVars ev ev'     | not (evDividesF nVars ev' ev)     = Nothing
evMinusMay nVars ev@(ExponVec d es) ev'@(ExponVec d' es')
    | perWord64 nVars d == perWord64 nVars (min d' td)  = Just (ExponVec td (go es es'))
    | otherwise                                         = Just slow
  where
    td      = d - d'
    go (Expons1 w)   (Expons1 w')       = Expons1 (w - w')
    go (Expons2 w v) (Expons2 w' v')    = Expons2 (w - w') (v - v')
    go (ExponsN a)   (ExponsN a')       = ExponsN (U.zipWith (-) a a')
    go _             _                  = undefined
    ~slow   = evMake (zipWithExact (-) (exponsL nVars ev) (exponsL nVars ev'))

evDividesF      :: Int -> ExponVec -> ExponVec -> Bool
-- ^ note args reversed from evMinusMay; really vars^ev1 `divides` vars^ev2
evDividesF _ (ExponVec d _) (ExponVec d' _)     | d > d'    = False     -- for efficiency
evDividesF nVars ev@(ExponVec d es) ev'@(ExponVec d' es')
    | perW == perWord64 nVars d'    = go es es'
    | otherwise                     = slow
  where
    perW    = perWord64 nVars d
    go (Expons1 w)   (Expons1 w')       = bytesDivs w w'
    go (Expons2 w v) (Expons2 w' v')    = bytesDivs w w' && bytesDivs v v'
    go (ExponsN a)   (ExponsN a')       = U.ifoldr (\i e ~b -> e <= a' U.! i && b) True a
    go _             _                  = undefined
    ~slow   = and (zipWithExact (<=) (exponsL nVars ev) (exponsL nVars ev'))
    bytesDivs w w'      = w <= w' && (w' - w) .&. mask `xor` w .&. mask `xor` w' .&. mask == 0
      where     -- check if any bytes subtracted in (w' - w) cause borrowing from any mask bits
        mask        = if perW == 8 then 0x0101_0101_0101_0100 else 0x0001_0001_0001_0000

evLCMF          :: Int -> Op2 ExponVec  -- really Least Common Multiple of vars^ev1 and vars^ev2
evLCMF nVars ev ev'     = evMake (zipWithExact max (exponsL nVars ev) (exponsL nVars ev'))

cmpExpsSameShape                                :: Cmp Expons
-- lexicographic comparison, assuming the same nVars and (perWord64 nVars td)
cmpExpsSameShape (Expons1 w)   (Expons1 w')     = compare w w'
cmpExpsSameShape (Expons2 w v) (Expons2 w' v')  = compare w w' <> compare v v'
cmpExpsSameShape (ExponsN a)   (ExponsN a')     = compare a a'
cmpExpsSameShape _             _                = undefined

evGrRevLexCmp   :: Cmp ExponVec
-- ^ The variables go from least main (variable 0) to most main, in big-endian order.
evGrRevLexCmp (ExponVec d es) (ExponVec d' es') = compare d d' <> cmpExpsSameShape es' es

evGrLexCmp      :: Cmp ExponVec
-- ^ The variables go from most main (variable 0) to least main, in big-endian order.
evGrLexCmp (ExponVec d es) (ExponVec d' es')    = compare d d' <> cmpExpsSameShape es es'

evLexCmpF       :: Int -> Cmp ExponVec
-- ^ The variables go from most main (variable 0) to least main, in big-endian order.
evLexCmpF nVars ev@(ExponVec d es) ev'@(ExponVec d' es')
    | perWord64 nVars d == perWord64 nVars d'   = cmpExpsSameShape es es'
    | otherwise                                 = compare (exponsL nVars ev) (exponsL nVars ev')

epEvCmpF            :: Int -> StdEvCmp -> Cmp ExponVec
epEvCmpF nVars      = \case
    LexCmp      -> evLexCmpF nVars
    GrLexCmp    -> evGrLexCmp
    GrRevLexCmp -> evGrRevLexCmp


type EPoly c    = SparseSum c ExponVec
-- ^ evPlus must be order-preserving for the term order, and it must be a well ordering

data RingTgtXs c t      = RingTgtXs (c -> t) [t]
-- ^ a ring homomorphism C -> T, and a list of elements that commute with image(C)

type EPolyUniv c        = UnivL Ring (RingTgtXs c) (->) (EPoly c)
-- ^ a @Ring (EPoly c)@, @RingTgtXs c (EPoly c)@, and a function for mapping to other 'Ring's
-- that have a @RingTgtXs c@

data EPolyOps c     = EPolyOps {
    nVars               :: Int,
    evCmp               :: Cmp ExponVec,
    epUniv              :: EPolyUniv c,     -- ^ The vars are in big-endian order. That is,
        -- the most main vars are first for LexCmp or GrLexCmp, and least main for GrRevLexCmp.
    ssOROps             :: SSOverRingOps c ExponVec,
    epTimesNZMonom      :: EPoly c -> ExponVec -> c -> EPoly c,     -- ^ the @c@ is nonzero
    epTimesMonom        :: EPoly c -> ExponVec -> c -> EPoly c
}


headTotDeg      :: EPoly c -> Integer
headTotDeg p    = if ssIsZero p then -1 else fromIntegral (ssDegNZ p).totDeg

epOps                   :: forall c. Ring c -> Int -> Cmp ExponVec -> EPolyOps c
epOps cR nVars evCmp    = EPolyOps { .. }
  where
    AbelianGroup _ _ _ _ cIsZero cNeg   = cR.ag
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) ssUnivF)    = ssAGUniv cR.ag evCmp
    ssOROps@(SSOverRingOps { .. })  = ssOverRingOps cR
    epTimesNZMonom  = ssTimesNZMonom (evPlus nVars)
    epTimesMonom    = ssTimesMonom (evPlus nVars)
    ssTimesF    = ssTimes ssUniv (evPlus nVars)
    evZero      = evMake (replicate nVars 0)
    inds        = [0 .. nVars - 1]
    xs          = [dcToSS (evMake [if i == j then 1 else 0 | j <- inds]) cR.one | i <- inds]
    cToEp       = dcToSS evZero
    epFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. cR.rFlags
    epRing      = Ring ssAG epFlags epTimes (cToEp cR.one) (cToEp . cR.fromZ) epDiv
    epUniv      = UnivL epRing (RingTgtXs cToEp xs) epUnivF
    epTimes p q
        | rIsOne epRing p   = q     -- for efficiency
        | rIsOne epRing q   = p     -- for efficiency
        | otherwise         = ssTimesF p q
    ssLead'     = ssLead cIsZero
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
                    let (qc, rc)    = cR.bDiv doFull c c1
                        -- want p = (c1*x^ev1 + t1) * (qc*x^qd + q2) + (rc*x^ev + r2):
                        ~p'         = {-# SCC "epDiv'-+-qM*" #-} ssAG.plus !$ t
                                        !$ {-# SCC epTimesMonom #-}
                                           epTimesMonom t1 qd (cNeg qc)
                        ~qr2    = if doFull || cIsZero rc then epDiv' p'
                                  else (SSZero, p')
                    in  (ssLead' qc qd (fst qr2), ssLead' rc ev (snd qr2))
    epUnivF     :: Ring t -> RingTgtXs c t -> EPoly c -> t
    epUnivF tR (RingTgtXs cToT xTs)     = ssUnivF tR.ag (TgtArrsF dcToT)
      where
        dcToT ev c  =
            foldr1 tR.times (cToT c : zipWithExact (rExpt tR) xTs (exponsL nVars ev))


data EvVarSs    = EvVarSs { descVarSs :: [String], nVars :: Int, isRev :: Bool }
-- ^ @descVarSs@ lists more main variables first, and each @varS@ has precedence > '^'.

evVarSs                     :: [String] -> Cmp ExponVec -> EvVarSs
evVarSs descVarSs evCmp     = EvVarSs { descVarSs, nVars, isRev }
  where
    nVars           = length descVarSs
    isRev           = nVars > 0 && evCmp (evMake es) (evMake (reverse es)) == LT
      where
        ~es     = 1 : replicate (nVars - 1) 0

evShowPrecF                 :: EvVarSs -> ShowPrec ExponVec
evShowPrecF (EvVarSs { descVarSs, nVars, isRev }) prec ev   =
    productSPrec powSP prec (zip descVarSs es)
  where
    es              = (if isRev then reverse else id) (exponsL nVars ev)
    powSP prec1 (varS, e)   = varPowShowPrec varS prec1 e

epGBPOps        :: forall c. Cmp ExponVec -> Bool -> Ring c -> [String] -> ShowPrec c -> Bool ->
                    GBPolyOps ExponVec (SSTerm c ExponVec) (EPoly c)
{- ^ In @ep58GBPOps evCmp isGraded cR descVarSs cShowPrec useSugar@, @descVarSs@ lists more main
    variables first, and each @varS@ has precedence > '^'. -}
epGBPOps evCmp isGraded cR descVarSs cShowPrec useSugar     =
    GBPolyOps { numTerms = length, .. }
  where
    evSs@(EvVarSs { nVars, isRev })     = evVarSs descVarSs evCmp
    evDivides           = evDividesF nVars
    evLCM               = evLCMF nVars
    evTotDeg            = (.totDeg)
    nEvGroups           = nVars
    evGroup             = exponsL nVars
    evShowPrec          = evShowPrecF evSs
    EPolyOps { epUniv, ssOROps }    = epOps cR nVars evCmp
    UnivL pR (RingTgtXs _cToP xs) _pUnivF   = epUniv
    descVarPs           = if isRev then reverse xs else xs
    leadEvNZ            = sparseSum undefined (\_ ev _ -> ev)
    SSOverRingOps { monicizeU }     = ssOROps
    extraSPairs _ _ _   = []
    sPoly f g (SPair { m })     = minus pR.ag (shift f) (shift g)
      where
        shift (SSNZ _ ev t) = ssShift (evPlus nVars (fromJust (evMinusMay nVars m ev))) t
        shift _             = undefined
    homogDeg0           = if isGraded then sparseSum 0 (\_ ev _ -> evTotDeg ev) else
        ssFoldr (\ _ ev n -> max ev.totDeg n) 0
    cons                = ssCons
    unconsNZ            = ssUnconsNZ
    pShow               = ssShowPrec evShowPrec cShowPrec 0

epCountZeros        :: Ring c -> [c] -> EPolyOps c -> [EPoly c] -> Int
-- ^ fastest if the first polynomials are short or have few zeros
epCountZeros cR cElts (EPolyOps { nVars, epUniv = UnivL _ _ epUnivF }) ps   = go [] nVars
  where
    evalAt cs   = epUnivF cR (RingTgtXs id cs)
    go cs 0     = if all (cR.isZero . evalAt cs) ps then 1 else 0
    go cs n     =
        sum $ (if n < minPar then map else parMap rseq) (\c -> go (c : cs) (n - 1)) cElts
    nCElts      = length cElts
    minPar      = if nCElts < 2 then maxBound else max (nVars + 1 - depth 1000) (depth 500)
    depth n     = floor (logBase @Double (fromIntegral nCElts) n)
