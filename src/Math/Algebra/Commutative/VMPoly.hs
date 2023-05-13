{-# LANGUAGE DataKinds, Strict #-}

{- |  This module uses vector-backed multivariate polynomials from the @poly@ package.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.VMPoly (
    Proxy(Proxy), SomeNat(SomeNat), someNatVal,
    VMPolyEV(..), vmpEvExps, vmpEvFromExps, VMPolyModPwTerm, VMPolyModPw(..), vmpModPwGbpOps
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Commutative.GroebnerBasis

import Control.DeepSeq (NFData)
import Data.Coerce (coerce)
import Data.Data (Data, dataTypeOf, fromConstr, readConstr)
import Data.Maybe (fromJust, fromMaybe)
import Data.Mod.Word (Mod)
import Data.Poly.Multi (MultiPoly(..), VMultiPoly, monomial, scale, unMultiPoly)
import Data.Proxy (Proxy(Proxy))
import Data.Stack (RVector(..), pushRev, pop)
import Data.Tuple.Extra (first, second)
import Data.Typeable (Typeable, tyConName, typeRep, typeRepFingerprint, typeRepTyCon)
import GHC.TypeNats (KnownNat, Nat, SomeNat(SomeNat), natVal, someNatVal)
import qualified Data.Vector as PV
-- import qualified Data.Vector.Unboxed as PV
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Sized as EV
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL


typeEq          :: forall s t. (Typeable s, Typeable t) => Proxy s -> Proxy t -> Bool
typeEq p1 p2    = typeRepFingerprint (typeRep p1) == typeRepFingerprint (typeRep p2)

{-
typeToConstr0   :: forall proxy c t. (Typeable c, Data t) => proxy c -> t
-- ^ @c@ must be a value constructor of 0 arguments producing a @t@, raised to the type level.
typeToConstr0 p     = fromConstr $ fromMaybe (error ("typeToConstr0: " ++ s)) $
                        readConstr (dataTypeOf @t undefined) (unQuote s)
  where
    s       = tyConName (typeRepTyCon (typeRep p))
    unQuote ('\'' : r)  = r
    unQuote r           = r
-}


newtype VMPolyEV (n1 :: Nat) (g :: IsGraded)    = VMPolyEV { ev :: EV.Vector n1 Word }
    deriving (Show, Eq, Ord)
    -- includes total degree; @@ TODO: allow GrRevLexCmp monomial order

isGradedTB      :: forall (g :: IsGraded). Typeable g => Proxy g -> Bool
{-# INLINABLE isGradedTB #-}
isGradedTB p
    | typeEq p (Proxy @('IsGraded True))    = True
    | typeEq p (Proxy @('IsGraded False))   = False
    | otherwise                             = error "isGradedTB"

vmpEvExps       :: forall n1 g. Typeable g => VMPolyEV n1 g -> VU.Vector Word
{-# INLINABLE vmpEvExps #-}
vmpEvExps       =
    (if isGradedTB (Proxy @g) then VU.tail else VU.init) . EV.fromSized . (.ev)

vmpEvFromExps       :: forall n1 g. (KnownNat n1, Typeable g) => VU.Vector Word -> VMPolyEV n1 g
{-# INLINABLE vmpEvFromExps #-}
vmpEvFromExps es    = {-# SCC vmpEvFromExps #-} VMPolyEV $ fromJust $ EV.toSized $
    if isGradedTB (Proxy @g) then VU.cons td es else VU.snoc es td
  where
    td      = VU.sum es

instance (KnownNat n1, Typeable g) => GBEv (VMPolyEV n1 g) where
    evDivides _nVars    = {-# SCC evDivides #-} VU.eqBy (<=) `on` EV.fromSized . (.ev)
    {-# INLINABLE evDivides #-}
    evLCM _nVars v w    = {-# SCC evLCM #-} vmpEvFromExps (VU.zipWith max (vmpEvExps v) (vmpEvExps w))
    {-# INLINABLE evLCM #-}
    evTotDeg            =
        (if isGradedTB (Proxy @g) then VU.head else VU.last) . EV.fromSized . (.ev)
    {-# INLINABLE evTotDeg #-}

type VMPolyModPwTerm (n1 :: Nat) (p :: Nat)     = (EV.Vector n1 Word, Mod p)

newtype VMPolyModPw (n1 :: Nat) (p :: Nat) (g :: IsGraded)  =
    VMPolyModPw { poly :: VMultiPoly n1 (Mod p) }
    deriving (Show, Num, NFData)

vmpFromPV       :: PV.Vector (EV.Vector n1 Word, Mod p) -> VMPolyModPw n1 p g
vmpFromPV       = VMPolyModPw . MultiPoly

vmpToPV         :: VMPolyModPw n1 p g -> PV.Vector (EV.Vector n1 Word, Mod p)
vmpToPV         = unMultiPoly . (.poly)

instance (KnownNat p, KnownNat n1, Typeable g) =>
        GBPoly (VMPolyEV n1 g) (VMPolyModPwTerm n1 p) RVector (VMPolyModPw n1 p g) where
    leadEvNZ        = VMPolyEV . fst . PV.last . vmpToPV
    {-# INLINABLE leadEvNZ #-}

vmpModPwGbpOps  :: forall p n1 g. (KnownNat p, KnownNat n1, Typeable g) => UseSugar ->
                    GBPolyOps (VMPolyEV n1 g) (VMPolyModPw n1 p g)
-- ^ @p@ must be a prime, and fit in a 'Word'; @n1 = nVars + 1@; LexCmp or GrLexCmp order.
{-# INLINABLE vmpModPwGbpOps #-}
vmpModPwGbpOps useSugar     = {-# SCC vmpModPwGbpOps #-} GBPolyOps { .. }
  where
    toEVG ev        = VMPolyEV ev :: VMPolyEV n1 g
    toRV            :: VMultiPoly n1 (Mod p) -> RVector (VMPolyModPwTerm n1 p)
    toRV            = RVector . unMultiPoly
    fromRV          = MultiPoly . (.v)
    polyPop         = (second fromRV <$>) . pop . toRV
    polyPushRev r   = fromRV . pushRev r . toRV
    nVars           = (fromIntegral (natVal (Proxy :: Proxy n1)) :: Int) - 1
    isGraded        = IsGraded (isGradedTB (Proxy @g))
    evCmp           = compare               -- LexCmp or GrLexCmp monomial order
    nEvGroups       = nVars
    evGroup         = VU.toList . vmpEvExps
    isRev           = False     -- @@ TODO: allow GrRevLexCmp
    evShowPrec prec w   = showsPrec prec w ""
    -- @@ TODO: for pBDiv, is it faster to segregate?
    pBDiv doFull y m    = {-# SCC pBDiv #-} case polyPop m of
        Nothing                 -> (0, y)
        Just ((mEv, mC), mT)    -> go SL.Nil SL.Nil y
          where
            go qRev rRev x  = case polyPop x of
                Nothing                             -> done
                Just (xH@(xEv, xC), xT)
                    | evDivides nVars (toEVG mEv) (toEVG xEv)   ->
                        let qEv     = xEv - mEv
                            qC      = xC / mC
                        in  go ((qEv, qC) :! qRev) rRev (xT - scale qEv qC mT)
                    | not doFull.b || xEv < mEv     -> done
                    | otherwise                     -> go qRev (xH :! rRev) xT
              where
                ~done   = (polyPushRev qRev 0, polyPushRev rRev x)
    pR              = coerce (numRing integralDomainFlags pBDiv)
    varExps i       = {-# SCC varExps #-} VU.generate nVars (\k -> if k == i then 1 else 0)
    varIndsDesc     =   -- most main first
        (if isRev then reverse else id) [0 .. nVars - 1]
    descVarPs       =
        map (\i -> VMPolyModPw $ monomial (vmpEvFromExps (varExps i) :: VMPolyEV n1 g).ev 1)
            varIndsDesc
    monicizeU p     = {-# SCC monicizeU #-} vmpFromPV . PV.map (second (c *)) . vmpToPV $ p
      where
        c       = recip . snd . PV.last . vmpToPV $ p
    extraSPairs _ _ _   = []
    sPoly f g (SPair { m })     = {-# SCC sPoly #-} shift f - shift g
      where
        shift p     = {-# SCC shift #-} vmpFromPV . PV.map (first (d +)) . PV.init . vmpToPV $ p
          where
            d   = m.ev - (leadEvNZ p).ev
    homogDeg0 p
        | PV.null pv    = 0
        | isGraded.b    = termTotDeg $ PV.last pv
        | otherwise     = termTotDeg (PV.maximumOn termTotDeg pv)
      where
        pv          = vmpToPV p
        termTotDeg t    = evTotDeg (toEVG (fst t))
    pShow           = show
