{-# LANGUAGE Strict #-}

{- |  An 'EPoly' is an \"Expanded\" or \"Exponent Vector\" Polynomial. That is, each term
    consists of a coefficient and an exponent vector ('ExponVec').
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.EPoly (
    ExponVec, evMake, exponsL, evPlus, evMinusMay, evDividesF, evLCMF, epEvCmpF,
    EPoly, RingTgtXs(..), EPolyUniv, EPolyOps(..),
    headTotDeg, epOps, EvVarSs(..), evVarSs, evShowPrecF,
    epGBPOps, epCountZeros
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.GroebnerBasis

import Control.Monad (replicateM)
import Data.Bifunctor (bimap)
import Data.Bits (complement, rotateL, unsafeShiftL, unsafeShiftR, xor)
import Data.List.Extra (chunksOf)
import Data.Maybe (fromJust)
import Data.Ord (clamp)
import qualified Data.Vector.Unboxed as U
import Data.Word (Word64)
import qualified StrictList2 as SL

import Control.Parallel.Cooperative

import qualified Debug.TimeStats as TS


zipWithExact    :: (a -> b -> c) -> [a] -> [b] -> [c]
-- ^ or use library @safe@
zipWithExact f xs ys    = assert (length xs == length ys) (zipWith f xs ys)


data Expons     = Expons1 Word64
                | Expons2 Word64 Word64
                | ExponsB Word64 (U.Vector Word64)
                | ExponsN (U.Vector Word)
    deriving Eq     -- e.g. for testing
-- The (possibly reversed) exponents are stored in big-endian order, for fast comparisons. That
-- is, the exponents are reversed (less main vars first) if isRev, e.g. GrRevLexCmp.

instance Show Expons where  -- e.g. for testing & debugging
    show (Expons1 w)        = show0x w
    show (Expons2 w v)      = show0x w ++ " " ++ show0x v
    show (ExponsB m ws)     = unwords (map show0x (m : U.toList ws))
    show (ExponsN a)        = show a

data ExponVec   = ExponVec { totDeg :: Word, expons :: Expons }
    deriving (Eq, Show)     -- e.g. for testing & debugging
-- ^ the number of variables must be fixed;
-- if totDeg < 2^8 then we use Expons1 for nVars <= 8 or Expons2 for nVars <= 16,
-- else if totDeg < 2^16 then we use Expons1 for nVars <= 4 or Expons2 for nVars <= 8,
-- else ExponsB (packed bytes or double-bytes) for totDeg < 2^8 or 2^16 and nVars larger

perWord64       :: Int -> Word -> Int
perWord64 nVars td
    | td < 256 && nVars > 4     = 8
    | td < 0x1_0000             = 4
    | otherwise                 = -1

exponsB                 :: Int -> Int -> U.Vector Word64 -> Expons
-- 0 < perW, 2*perW < nVars; computes a "divMask" of nonzero exponents
exponsB perW nBits ws   = ExponsB (U.foldl' (go perW) 0 ws) ws
  where
    mask            = if perW == 8 then 0xFF else 0xFFFF
    go n acc w      = if n == 0 then acc else
        go (n - 1) (acc `rotateL` 1 .|. (if w .&. mask /= 0 then 1 else 0))
            (w `unsafeShiftR` nBits)

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
            | perW > 0          = exponsB perW nBits (U.fromList (map packW (chunksOf perW es)))
            | otherwise         = ExponsN (U.fromListN nVars es)
    in  ExponVec td exps

exponsL         :: Int -> ExponVec -> [Word]
-- ^ The exponents are listed in big-endian order.
exponsL nVars (ExponVec td es)  = case es of
    Expons1 w       -> bytesL nVars w []
    Expons2 w0 w1   -> bytesL perW w0 (bytesL (nVars - perW) w1 [])
    ExponsB _ ws    -> goB nVars ws 0
    ExponsN a       -> U.toList a
  where
    perW        = perWord64 nVars td
    nBits       = if perW == 8 then 8 else 16
    mask        = if perW == 8 then 0xFF else 0xFFFF
    bytesL          :: Int -> Word64 -> [Word] -> [Word]
    bytesL n w ~t   = if n == 0 then t else
        bytesL (n - 1) (w `unsafeShiftR` nBits) (fromIntegral (w .&. mask) : t)
    goB n ws i
        | n <= perW     = bytesL n (ws U.! i) []
        | otherwise     = bytesL perW (ws U.! i) (goB (n - perW) ws (i + 1))

evPlus          :: Int -> Op2 ExponVec
evPlus nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   = go es es'
  where
    td      = d + d'
    perW    = perWord64 nVars td
    go (Expons1 w)    (Expons1 w')
        | nVars <= perW                 = ExponVec td (Expons1 (w + w'))
    go (Expons2 w v)  (Expons2 w' v')
        | nVars <= 2*perW               = ExponVec td (Expons2 (w + w') (v + v'))
    go (ExponsB m ws) (ExponsB m' ws')
        | td < 256 || d >= 256 && d' >= 256 && td < 0x1_0000
                                    = ExponVec td (ExponsB (m .|. m') (U.zipWith (+) ws ws'))
    go (ExponsN a)    (ExponsN a')      = ExponVec td (ExponsN (U.zipWith (+) a a'))
    go _              _                 =
        evMake (zipWithExact (+) (exponsL nVars ev) (exponsL nVars ev'))

evMinusMay      :: Int -> ExponVec -> ExponVec -> Maybe ExponVec
evMinusMay nVars ev ev'     | not (evDividesF nVars ev' ev)     = Nothing
evMinusMay nVars ev@(ExponVec d es) ev'@(ExponVec d' es')       = Just (evMinus es es')
  where
    td      = d - d'
    evMinus (Expons1 w)    (Expons1 w')     = ExponVec td (Expons1 (w - w'))
    evMinus (Expons2 w v)  (Expons2 w' v')
        | d < 256 || td >= 256              = ExponVec td (Expons2 (w - w') (v - v'))
    evMinus (ExponsB _ ws) (ExponsB _ ws')
        | d < 256 || td >= 256 && d' >= 256 =
            ExponVec td (exponsB perW nBits (U.zipWith (-) ws ws'))
      where
        ~perW       = perWord64 nVars td
        ~nBits      = if perW == 8 then 8 else 16
    evMinus (ExponsN a)    (ExponsN a')
        | td >= 0x1_0000                    = ExponVec td (ExponsN (U.zipWith (-) a a'))
    evMinus _              _                =
        evMake (zipWithExact (-) (exponsL nVars ev) (exponsL nVars ev'))

evDividesF      :: Int -> ExponVec -> ExponVec -> Bool
-- ^ note args reversed from evMinusMay; really vars^ev1 `divides` vars^ev2
evDividesF _ (ExponVec d _) (ExponVec d' _)     | d > d'    = False     -- for efficiency
evDividesF nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   = expsDivs es es'
  where
    expsDivs (Expons1 w)    (Expons1 w')    = bytesDivs w w'
    expsDivs (Expons2 w v)  (Expons2 w' v') = bytesDivs w w' && bytesDivs v v'
    expsDivs (ExponsB m ~a) (ExponsB m' ~a')
        | m .&. complement m' /= 0          = False
        | d' < 256 || d >= 256  = U.ifoldr (\i e ~b -> bytesDivs e (a' U.! i) && b) True a
    expsDivs (ExponsN a)    (ExponsN a')
                                = U.ifoldr (\i e ~b ->          e <= a' U.! i && b) True a
    expsDivs _              _               = TS.measurePure "evDividesF slow" $
        and (zipWithExact (<=) (exponsL nVars ev) (exponsL nVars ev'))
    perW        = perWord64 nVars d
    mask        = if perW == 8 then 0x0101_0101_0101_0100 else 0x0001_0001_0001_0000
    bytesDivs w w'      = w <= w' && (w' - w) .&. mask `xor` w .&. mask `xor` w' .&. mask == 0
        -- check if any bytes subtracted in (w' - w) cause borrowing from any mask bits
{-# INLINABLE evDividesF #-}

evLCMF          :: Int -> Op2 ExponVec  -- really Least Common Multiple of vars^ev1 and vars^ev2
evLCMF nVars ev@(ExponVec d es) ev'@(ExponVec d' es')   = goLCM es es'
  where
    perW        = perWord64 nVars d
    nBits       = if perW == 8 then 8 else 16
    mask        = if perW == 8 then 0xFF else 0xFFFF
    totDegPackedW   :: Word64 -> Word   -- assumes the input is packed
    totDegPackedW   = go 0
      where
        go t w          = if w == 0 then t else
            go (t + fromIntegral (w .&. mask)) (w `unsafeShiftR` nBits)
    maxPackedW      :: Word64 -> Word64 -> Word64   -- assumes perW == perW', perW > 0
    maxPackedW w w' = go 0 mask
      where
        go done m       = if m == 0 then done else
            go (done .|. max (w .&. m) (w' .&. m)) (m `unsafeShiftL` nBits)
    goLCM (Expons1 w)    (Expons1 w')
        | td <= fromIntegral mask           = ExponVec td (Expons1 w'')
      where
        w''         = maxPackedW w w'
        td          = totDegPackedW w''
    goLCM (Expons2 w v)  (Expons2 w' v')
        | td <= fromIntegral mask           = ExponVec td (Expons2 w'' v'')
      where
        w''         = maxPackedW w w'
        v''         = maxPackedW v v'
        td          = totDegPackedW w'' + totDegPackedW v''
    goLCM (ExponsB m ws) (ExponsB m' ws')
        | (d < 256) == (d' < 256) && td <= fromIntegral mask
                                            = ExponVec td (ExponsB (m .|. m') ws'')
      where
        ws''        = U.zipWith maxPackedW ws ws'
        td          = U.sum (U.map totDegPackedW ws'')  -- hopefully fuses, else U.ifoldl' !?
    goLCM (ExponsN a)    (ExponsN a')       = ExponVec (U.sum a'') (ExponsN a'')
      where
        a''         = U.zipWith max a a'
    goLCM _              _                  =
        evMake (zipWithExact max (exponsL nVars ev) (exponsL nVars ev'))

cmpExps                                     :: Ordering -> Cmp Expons
-- lexicographic comparison, assuming the same nVars
cmpExps ~_   (Expons1 w)    (Expons1 w')        = compare w w'
cmpExps ~_   (Expons2 w v)  (Expons2 w' v')     = compare w w' <> compare v v'
cmpExps ~_   (ExponsB _ ws) (ExponsB _ ws')     = compare ws ws'
cmpExps ~_   (ExponsN a)    (ExponsN a')        = compare a a'
cmpExps ~res _              _                   = res    -- different shapes

evGrRevLexCmp   :: Cmp ExponVec
-- ^ The variables go from least main (variable 0) to most main, in big-endian order.
evGrRevLexCmp (ExponVec d es) (ExponVec d' es') = compare d d' <> cmpExps undefined es' es

evGrLexCmp      :: Cmp ExponVec
-- ^ The variables go from most main (variable 0) to least main, in big-endian order.
evGrLexCmp (ExponVec d es) (ExponVec d' es')    = compare d d' <> cmpExps undefined es es'

evLexCmpF       :: Int -> Cmp ExponVec
-- ^ The variables go from most main (variable 0) to least main, in big-endian order.
evLexCmpF ~nVars ev@(ExponVec _ es) ev'@(ExponVec _ es')    =
    cmpExps (compare (exponsL nVars ev) (exponsL nVars ev')) es es'

epEvCmpF            :: Int -> StdEvCmp -> Cmp ExponVec
epEvCmpF ~nVars     = \case
    LexCmp      -> evLexCmpF nVars
    GrLexCmp    -> evGrLexCmp
    GrRevLexCmp -> evGrRevLexCmp
{-# INLINE epEvCmpF #-}


type EPoly c    = SparseSum c ExponVec
-- ^ evPlus must be order-preserving for the term order, and it must be a well ordering

instance GBEv ExponVec where
    evDivides       = evDividesF
    evLCM           = evLCMF
    evTotDeg        = (.totDeg)

instance GBPoly ExponVec (SSTerm c ExponVec) (EPoly c) where
    leadEvNZ        = sparseSum undefined (\_ ev _ -> ev)
    {-# INLINE leadEvNZ #-}

{-# SPECIALIZE gbiSmOps :: GBPolyOps ExponVec (EPoly c) ->
    SubmoduleOps (EPoly c) (EPoly c) (GroebnerIdeal (EPoly c)) #-}

data RingTgtXs c t      = RingTgtXs (c -> t) [t]
-- ^ a ring homomorphism C -> T, and a list of elements that commute with image(C)

type EPolyUniv c        = UnivL Ring (RingTgtXs c) (->) (EPoly c)
-- ^ a @Ring (EPoly c)@, @RingTgtXs c (EPoly c)@, and a function for mapping to other 'Ring's
-- that have a @RingTgtXs c@.  The vars are in big-endian order. That is, the most main vars are
-- first for LexCmp or GrLexCmp, and least main for GrRevLexCmp.

data EPolyOps c     = EPolyOps {
    nVars               :: Int,
    evCmp               :: Cmp ExponVec,
    epUniv              :: EPolyUniv c
}


headTotDeg      :: EPoly c -> Integer
headTotDeg      = sparseSum (-1) (\_ ev _ -> fromIntegral ev.totDeg)

epOps                   :: forall c. Ring c -> Int -> Cmp ExponVec -> EPolyOps c
epOps cR nVars evCmp    = EPolyOps { .. }
  where
    AbelianGroup _ cEq _ _ cIsZero cNeg     = cR.ag
    ssUniv@(UnivL ssAG (TgtArrsF dcToSS) ssUnivF)    = ssAGUniv cR.ag evCmp
    evZero      = evMake (replicate nVars 0)
    inds        = [0 .. nVars - 1]
    xs          = [dcToSS (evMake [if i == j then 1 else 0 | j <- inds]) cR.one | i <- inds]
    cToEp       = dcToSS evZero
    epFlags     = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors] .&. cR.rFlags
    nzds        = hasEIBit cR.rFlags NoZeroDivisors
    epRing      = Ring ssAG epFlags
                    (if nzds then epTimesNzds else ssTimes ssUniv cR (evPlus nVars))
                    (cToEp cR.one) (cToEp . cR.fromZ) epDiv
    epUniv      = UnivL epRing (RingTgtXs cToEp xs) epUnivF
    epIsOne     = sparseSum False (\ ~c ev ~t -> ev.totDeg == 0 && cEq c cR.one && null t)
        -- note wrong for 0 Ring, just cxIsOne => (== one)
    epTimesNzds p q
        | epIsOne p     = q     -- for efficiency
        | epIsOne q     = p     -- for efficiency
        | otherwise     = ssTimesNzds ssUniv cR (evPlus nVars) p q
    epTimesNzMonom  = if nzds then ssTimesNzdMonom else ssTimesMonom
    {- epTimesMonom s d c  =
        if cR.isZero c then ssZero else epTimesNzMonom cR (evPlus nVars) s d c -}
    minusTimesMonom p s d c     =   -- p - s*c*vars^d
        if cR.isZero c then p else
            ssAG.plus !$ p !$ epTimesNzMonom cR (evPlus nVars) s d (cNeg c)
    {-# INLINE minusTimesMonom #-}

    ssLead'     = ssLead cIsZero
    epDiv doFull p0 p1  = if epIsOne p1 then (p0, ssZero) else  -- for efficiency
                            case SL.uncons p1 of
        Nothing                     -> (ssZero, p0)
        Just (SSTerm !c1 !ev1, t1)  -> {-# SCC epDiv' #-} epDiv' p0
          where
            epDiv' p    = case SL.uncons p of
                Nothing                     -> (ssZero, p)
                Just (SSTerm c !ev, t)
                    | evCmp ev ev1 == LT    -> (ssZero, p)
                    | otherwise             -> case evMinusMay nVars ev ev1 of
                        Nothing     -> -- {-# SCC "sub-top-epDiv'" #-}
                            if not doFull.b then (ssZero, p) else
                            let (q2, r2) = epDiv' t
                            in  (q2, SSTerm c ev :! r2)
                        Just qd     -> -- {-# SCC "top-etc-epDiv'" #-}
                            let (qc, rc)    = cR.bDiv doFull c c1
                                -- want p = (c1*x^ev1 + t1) * (qc*x^qd + q2) + (rc*x^ev + r2):
                                ~p'     = {-# SCC "epDiv'-+-qM*" #-} minusTimesMonom t t1 qd qc
                                qr2     = if doFull.b || cIsZero rc then epDiv' p' else
                                            (ssZero, p')
                            in  bimap (ssLead' qc qd) (ssLead' rc ev) qr2
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

epGBPOps        :: forall c. Cmp ExponVec -> IsGraded -> Ring c -> [String] -> ShowPrec c ->
                    UseSugar -> GBPolyOps ExponVec (EPoly c)
{- ^ In @ep58GBPOps evCmp isGraded cR descVarSs cShowPrec useSugar@, @descVarSs@ lists more main
    variables first, and each @varS@ has precedence > '^'. -}
epGBPOps evCmp isGraded cR descVarSs cShowPrec useSugar     = GBPolyOps { .. }
  where
    evSs@(EvVarSs { nVars, isRev })     = evVarSs descVarSs evCmp
    nEvGroups           = nVars
    evGroup             = (if isRev then reverse else id) . exponsL nVars
    evShowPrec          = evShowPrecF evSs
    EPolyOps { epUniv } = epOps cR nVars evCmp
    UnivL pR (RingTgtXs _cToP xs) _pUnivF   = epUniv
    descVarPs           = if isRev then reverse xs else xs
    monicizeU           = ssMonicizeU cR
    extraSPairs _ _ _   = []
    sPoly f g (SPair { m })     = minus pR.ag (shift f) (shift g)
      where
        shift       = sparseSum undefined
            (\ _ ev t -> ssShift (evPlus nVars (fromJust (evMinusMay nVars m ev))) t)
    homogDeg0           = if isGraded.b then sparseSum 0 (\_ ev _ -> evTotDeg ev) else
        foldl' (\acc (SSTerm _ !ev) -> max acc ev.totDeg) 0
    pShow               = ssShowPrec evShowPrec cShowPrec 0

epCountZeros        :: Ring c -> [c] -> EPolyOps c -> [EPoly c] -> Int
-- ^ fastest if the first polynomials are short or have few zeros
epCountZeros cR cElts (EPolyOps { nVars, epUniv = UnivL _ _ epUnivF }) ps   =
    forkJoinPar (replicateM parDepth) sum (go (nVars - parDepth)) cElts
  where
    evalAt cs   = epUnivF cR (RingTgtXs id cs)
    go 0 cs     = if all (cR.isZero . evalAt cs) ps then 1 else 0
    go n cs     = sum [go (n - 1) (c : cs) | c <- cElts]
    nCElts      = length cElts
    parDepth    = if nCElts < 2 then 0 else nVars - clamp (1, nVars) (floorLogBase nCElts 500)
