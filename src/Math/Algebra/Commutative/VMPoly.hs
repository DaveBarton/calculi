{-# LANGUAGE Strict, ViewPatterns #-}

{- |  This module uses vector-backed multivariate polynomials from the @poly@ package.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.VMPoly (
    VMPolyEV, VMPolyModPwTerm, VMPolyModPw, vmpModPwGbpOps
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Commutative.GroebnerBasis (SPair(..), GBPolyOps(..))

import Data.Maybe (fromJust)
import Data.Mod.Word (Mod)
import Data.Poly.Multi (UMultiPoly, VMultiPoly, monomial, scale, toMultiPoly, unMultiPoly)
import Data.Proxy (Proxy(Proxy))
import Data.Tuple (swap)
import Data.Tuple.Extra (first, second)
import GHC.TypeNats (KnownNat, Nat, natVal)
import qualified Data.Vector.Unboxed as PV
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Sized as EV


type VMPolyEV (n :: Nat)    = EV.Vector n Word  -- includes total degree
    -- @@ TODO: allow GrRevLexCmp monomial order
type VMPolyModPwTerm (n :: Nat) (p :: Nat)  = (VMPolyEV n, Mod p)
type VMPolyModPw (n :: Nat) (p :: Nat)  = UMultiPoly n (Mod p)  -- @@ TODO: try VMultiPoly also

vmpModPwGbpOps              :: forall p n. (KnownNat p, KnownNat n) => Bool -> Bool ->
                                GBPolyOps (VMPolyEV n) (VMPolyModPwTerm n p) (VMPolyModPw n p)
-- ^ @p@ must be a prime, and fit in a 'Word'; @n = nVars + 1@; LexCmp or GrLexCmp order.
vmpModPwGbpOps isGraded useSugar    = GBPolyOps { .. }
  where
    nVars           = (fromIntegral (natVal (Proxy :: Proxy n)) :: Int) - 1
    evCmp           = compare               -- LexCmp monomial order
    evDivides       = VU.eqBy (<=) `on` EV.fromSized
    -- an "exps" is an unsized vector
    evExps          = (if isGraded then VU.tail else VU.init) . EV.fromSized
    fromExps es     = fromJust (EV.toSized (if isGraded then VU.cons td es else VU.snoc es td))
      where
        td      = VU.sum es
    evLCM v w       = fromExps (VU.zipWith max (evExps v) (evExps w))
    evTotDeg        = (if isGraded then VU.head else VU.last) . EV.fromSized
    nEvGroups       = nVars
    evGroup         = VU.toList . evExps
    isRev           = False     -- @@ TODO: allow GrRevLexCmp
    evShowPrec prec w   = showsPrec prec w ""
    uncons          = (second toMultiPoly . swap <$>) . PV.unsnoc . unMultiPoly
    -- @@ TODO: for pBDiv, is it faster to segregate?
    pBDiv _doFull y (uncons -> Nothing)                 = (0, y)
    pBDiv  doFull y (uncons -> Just ((mEv, mC), mT))    = go y
      where
        go   (uncons -> Nothing)        = (0, 0)
        go x@(uncons -> Just (xH@(xEv, xC), xT))
            | evDivides mEv xEv         =
                let qEv     = xEv - mEv
                    qC      = xC / mC
                in  first (cons (qEv, qC)) (go (xT - scale qEv qC mT))
            | not doFull || xEv < mEv   = (0, x)
            | otherwise                 = second (cons xH) (go xT)
    pR              = numRing integralDomainFlags pBDiv
    varExps i       = VU.generate nVars (\k -> if k == i then 1 else 0)
    varIndsDesc     =   -- most main first
        (if isRev then reverse else id) [0 .. nVars - 1]
    descVarPs       = map (\i -> monomial (fromExps (varExps i)) 1) varIndsDesc
    leadEvNZ        = fst . PV.last . unMultiPoly
    monicizeU p     = toMultiPoly . PV.map (second (c *)) . unMultiPoly $ p
      where
        c       = recip . snd . PV.last . unMultiPoly $ p
    extraSPairs _ _ _   = []
    sPoly f g (SPair { m })     = shift f - shift g
      where
        shift p     = toMultiPoly . PV.map (first (d +)) . PV.init . unMultiPoly $ p
          where
            d   = m - leadEvNZ p
    homogDeg0 p
        | PV.null pv    = 0
        | isGraded      = termTotDeg $ PV.last pv
        | otherwise     = termTotDeg (PV.maximumOn termTotDeg pv)
      where
        pv          = unMultiPoly p
        termTotDeg  = evTotDeg . fst
    numTerms        = PV.length . unMultiPoly
    cons t          = toMultiPoly . (`PV.snoc` t) . unMultiPoly
    unconsNZ        = fromJust . uncons
    pShow           = show
