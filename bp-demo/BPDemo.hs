{-# LANGUAGE Strict #-}

{- |  BinPoly demo examples  -}

import Math.Algebra.General.Algebra
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.BinPoly

import Control.Monad (when)
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import Data.Word (Word64)

import Control.Concurrent (forkOn, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)

-- import Debug.Trace


-- To run a demo, first set the "@@" lines below the way you want.

demoOps             :: Int -> StdEvCmp ->
                        (GBPolyOps EV58 EV58 (BinPoly EV58), BPOtherOps EV58 Word64)
demoOps nVars sec   = bp58Ops evCmp isGraded varSs useSugar
  where
    evCmp           = evCmp58 sec
    isGraded        = secIsGraded sec
    xVarSs          = ['X' : show n | n <- [1 :: Int ..]]
    varSs           = take nVars (map (: []) ['a' .. 'z'] ++ xVarSs)
    useSugar        = False     -- @@

bpDemo                  :: Int -> Int -> IO ()
bpDemo nCores gbTrace   = do
    putStrLn $ name ++ " " ++ show sec
    putStrLn $ show (bpCountZeros bpoA gens) ++ " zeros"
    when (Seq.length reducedGensSeq < 250) $ putStrLn $ showGens gbpA.pShow reducedGensL
    putStrLn $ show (bpCountZeros bpoA reducedGensL) ++ " zeros"
  where
    sec             = LexCmp   -- @@ LexCmp, GrLexCmp, or GrRevLexCmp
    (gbpA, bpoA@(BPOtherOps { .. }))    = demoOps (length varPs) sec
    infixl 7 ∧          -- same as (.&.) and (*)
    infixr 5 ∨          -- same as (.|.) except infixr, note (`xor`) and (+) are infixl 6
    SubmoduleOps { .. }         = gbiSmOps gbpA nCores gbTrace
    gbIdeal         = fromGens gens
    reducedGensSeq  = stdGens True gbIdeal
    reducedGensL    = toList reducedGensSeq
    -- @@ can compute (bMod doFullReduce p gbIdeal) where doFullReduce is True or False
    
    -- @@ choose a name, varPs & complements, and gens, commenting out the other examples:
    -- 'a' is the most main variable
    {- 
    name            = "logic0"
    varPs@[a, b, c, d]  = map bpVar [0 .. 3]
    [a_, b_, c_, d_]    = map bpNot varPs
    gens            = [a ∨ b ∨ c_, a ∨ d]
    -}
    {- 
    name            = "logic3"
    varPs@[a, b, c, d, e, f, g, h, i, j]        = map bpVar [0 .. 9]
    [a_, b_, c_, d_, e_, f_, g_, h_, i_, j_]    = map bpNot varPs
    [poly1, poly2, poly3]   = [
        (e ∨ f_ ∨ j) ∧ (d ∨ e ∨ g) ∧ (b_ ∨ f ∨ i) ∧ (e_ ∨ g_ ∨ i_) ∧ (d_ ∨ h ∨ j)
            ∧ (c ∨ e_ ∨ g) ∧ (e_ ∨ f ∨ h) ∧ (f ∨ g ∨ i) ∧ (c ∨ i_ ∨ j) ∧ (e ∨ h_ ∨ j_)
            ∧ (c ∨ f_ ∨ i_) ∧ (c_ ∨ f_ ∨ g_) ∧ (a_ ∨ e ∨ f_) ∧ (f ∨ h ∨ i_) ∧ (a ∨ f_ ∨ i_)
            ∧ (a_ ∨ d ∨ f) ∧ (a_ ∨ c_ ∨ j) ∧ (b_ ∨ e ∨ i_) ∧ (b_ ∨ g ∨ h) ∧ (a_ ∨ h ∨ i_)
            ∧ (d ∨ f_ ∨ i) ∧ (a_ ∨ f_ ∨ j_) ∧ (e_ ∨ f ∨ j) ∧ (g ∨ i ∨ j_) ∧ (e_ ∨ f_ ∨ h_)
            ∧ (b ∨ e_ ∨ f_) ∧ (b_ ∨ c_ ∨ g_) ∧ (c ∨ g ∨ i) ∧ (b ∨ f ∨ j_) ∧ (e_ ∨ h ∨ j)
            ∧ (a_ ∨ c_ ∨ g) ∧ (c_ ∨ f ∨ g_) ∧ (d_ ∨ g ∨ i_) ∧ (a ∨ d ∨ i) ∧ (e_ ∨ h_ ∨ j_)
            ∧ (a ∨ b_ ∨ g_) ∧ (d_ ∨ i ∨ j_) ∧ (c ∨ g ∨ h) ∧ (b_ ∨ h ∨ j_) ∧ (a_ ∨ i_ ∨ j_)
            ∧ (c_ ∨ d ∨ h_) ∧ (b_ ∨ d_ ∨ h_) ∧ (a_ ∨ b ∨ c) ∧ (b ∨ d ∨ g) ∧ (a ∨ g_ ∨ h)
            ∧ (b_ ∨ c ∨ d_) ∧ (b_ ∨ e ∨ i) ∧ (a_ ∨ c ∨ h) ∧ (d_ ∨ f_ ∨ i) ∧ (a_ ∨ e_ ∨ g_),
        (d ∨ e ∨ i) ∧ (b_ ∨ c_ ∨ d) ∧ (d_ ∨ g ∨ i_) ∧ (a_ ∨ b ∨ c) ∧ (b ∨ g ∨ i)
            ∧ (f ∨ i_ ∨ j_) ∧ (e ∨ f_ ∨ g) ∧ (a_ ∨ b_ ∨ d) ∧ (b_ ∨ e_ ∨ i_) ∧ (a ∨ f_ ∨ j_)
            ∧ (d_ ∨ f ∨ i_) ∧ (c_ ∨ d_ ∨ g) ∧ (b_ ∨ e_ ∨ i) ∧ (b_ ∨ c_ ∨ e) ∧ (a_ ∨ d ∨ h)
            ∧ (d ∨ h ∨ j_) ∧ (c_ ∨ f ∨ i) ∧ (e_ ∨ f ∨ h_) ∧ (b ∨ f ∨ j_) ∧ (d ∨ g ∨ j_)
            ∧ (a ∨ b ∨ c_) ∧ (b ∨ h ∨ j_) ∧ (a_ ∨ f_ ∨ i_) ∧ (c_ ∨ e_ ∨ g_) ∧ (b ∨ c_ ∨ d_)
            ∧ (f_ ∨ g ∨ h_) ∧ (e ∨ g ∨ i) ∧ (b ∨ c_ ∨ i) ∧ (c_ ∨ f ∨ h_) ∧ (a_ ∨ e ∨ i_)
            ∧ (a_ ∨ f_ ∨ g_) ∧ (a ∨ c ∨ i_) ∧ (b_ ∨ i ∨ j_) ∧ (b ∨ d_ ∨ g) ∧ (c_ ∨ f_ ∨ g)
            ∧ (b_ ∨ c ∨ e) ∧ (c ∨ d_ ∨ e_) ∧ (a_ ∨ h ∨ i_) ∧ (g_ ∨ i ∨ j_) ∧ (d_ ∨ e_ ∨ j_),
        (e ∨ h ∨ i)]
    gens = [bpNot poly1]
    -}
    {- 
    name            = "logic5"
    varPs@[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]             = map bpVar [0 .. 14]
    [a_, b_, c_, d_, e_, f_, g_, h_, i_, j_, k_, l_, m_, n_, o_]    = map bpNot varPs
    [poly1, poly2, poly3]   = [
        (l ∨ n_ ∨ o) ∧ (f ∨ l ∨ o_) ∧ (h ∨ j ∨ l) ∧ (e_ ∨ j_ ∨ n_) ∧ (a ∨ c ∨ l) ∧ (f ∨ g_ ∨
            j) ∧ (d ∨ j ∨ o_) ∧ (d_ ∨ f ∨ j) ∧ (a ∨ c ∨ o_) ∧ (g ∨ j ∨ l) ∧ (i ∨ m ∨ n) ∧ (c
            ∨ h_ ∨ i_) ∧ (c ∨ g_ ∨ i_) ∧ (a_ ∨ g_ ∨ h_) ∧ (a ∨ i ∨ j) ∧ (c ∨ d_ ∨ k) ∧ (i ∨ k
            ∨ l) ∧ (f ∨ l ∨ m_) ∧ (d ∨ j ∨ n_) ∧ (c ∨ g ∨ l) ∧ (e ∨ m ∨ o_) ∧ (e_ ∨ j_ ∨ m_)
            ∧ (c ∨ h_ ∨ l_) ∧ (e_ ∨ j_ ∨ k) ∧ (a_ ∨ e_ ∨ j_) ∧ (c_ ∨ e ∨ f) ∧ (e_ ∨ i ∨ j_) ∧
            (a ∨ e ∨ k_) ∧ (b ∨ h_ ∨ i) ∧ (a ∨ k_ ∨ m_) ∧ (a ∨ c_ ∨ g_) ∧ (b_ ∨ e ∨ n_) ∧ (b
            ∨ k_ ∨ o_) ∧ (e ∨ g_ ∨ l_) ∧ (a_ ∨ d ∨ g_) ∧ (a ∨ h_ ∨ o_) ∧ (d_ ∨ j ∨ o_) ∧ (e ∨
            f ∨ h) ∧ (c_ ∨ i_ ∨ l) ∧ (f ∨ l_ ∨ m) ∧ (f ∨ i_ ∨ l_) ∧ (h ∨ i_ ∨ k_) ∧ (c ∨ i ∨
            j) ∧ (j_ ∨ l_ ∨ n_) ∧ (e ∨ i ∨ k) ∧ (e_ ∨ h ∨ m) ∧ (d ∨ j_ ∨ k_) ∧ (a ∨ f ∨ o) ∧
            (b ∨ k_ ∨ n) ∧ (d ∨ e ∨ i_) ∧ (d ∨ e_ ∨ g) ∧ (c ∨ m ∨ n) ∧ (e_ ∨ f ∨ j) ∧ (a_ ∨ l
            ∨ o_) ∧ (j_ ∨ l ∨ o_) ∧ (b_ ∨ g ∨ k_) ∧ (d ∨ e ∨ o_) ∧ (f ∨ h ∨ m_) ∧ (c ∨ h ∨
            n_) ∧ (f ∨ h_ ∨ o) ∧ (e_ ∨ g_ ∨ i) ∧ (a_ ∨ d ∨ f_) ∧ (b ∨ c ∨ l_) ∧ (b_ ∨ i ∨ k_)
            ∧ (e ∨ j ∨ o) ∧ (b ∨ d ∨ o) ∧ (i_ ∨ k ∨ o_) ∧ (a ∨ k ∨ o_) ∧ (a_ ∨ e ∨ m_) ∧ (e ∨
            g ∨ l_) ∧ (i ∨ k ∨ n_) ∧ (a ∨ c ∨ e) ∧ (a_ ∨ c ∨ l_) ∧ (d ∨ f ∨ l_) ∧ (c ∨ h ∨ n)
            ∧ (e_ ∨ j_ ∨ l_) ∧ (b_ ∨ d_ ∨ k) ∧ (a ∨ c_ ∨ l_) ∧ (f_ ∨ j_ ∨ m_) ∧ (h_ ∨ j_ ∨
            o),
        (d ∨ g ∨ h_) ∧ (a ∨ f_ ∨ k_) ∧ (a ∨ k_ ∨ l_) ∧ (c ∨ g_ ∨ o_) ∧ (a ∨ b ∨ h) ∧ (a ∨ c_
            ∨ f) ∧ (c ∨ e ∨ g) ∧ (d ∨ l_ ∨ o_) ∧ (b_ ∨ f_ ∨ k_) ∧ (f_ ∨ h_ ∨ i) ∧ (c ∨ d ∨
            e_) ∧ (e ∨ k_ ∨ m) ∧ (e_ ∨ i_ ∨ l) ∧ (b_ ∨ f ∨ l) ∧ (f ∨ h ∨ k) ∧ (f_ ∨ j_ ∨ k_)
            ∧ (c ∨ h_ ∨ n_) ∧ (b ∨ f_ ∨ j_) ∧ (c ∨ k_ ∨ l_) ∧ (e ∨ f ∨ j_) ∧ (e ∨ l_ ∨ n_) ∧
            (b_ ∨ f_ ∨ k) ∧ (d_ ∨ m_ ∨ o_) ∧ (b_ ∨ c_ ∨ h_) ∧ (a ∨ g ∨ h) ∧ (a ∨ k_ ∨ l) ∧
            (b_ ∨ g ∨ j_) ∧ (c ∨ g_ ∨ k) ∧ (b_ ∨ h ∨ i) ∧ (c ∨ l_ ∨ o_) ∧ (c ∨ i_ ∨ j_) ∧ (f
            ∨ k ∨ o) ∧ (a_ ∨ m ∨ o_) ∧ (a ∨ d_ ∨ h_) ∧ (c_ ∨ e ∨ o) ∧ (d_ ∨ e ∨ f) ∧ (e ∨ i ∨
            l_) ∧ (f ∨ i ∨ o) ∧ (e ∨ f_ ∨ h_) ∧ (c_ ∨ l ∨ m_) ∧ (c ∨ f ∨ g_) ∧ (e ∨ h ∨ l) ∧
            (d ∨ f ∨ m) ∧ (g ∨ j_ ∨ n_) ∧ (c ∨ g ∨ j_) ∧ (j ∨ l ∨ m) ∧ (b ∨ d ∨ i) ∧ (g_ ∨ h
            ∨ m) ∧ (c ∨ g_ ∨ n) ∧ (f ∨ j_ ∨ o_) ∧ (c ∨ k_ ∨ m_) ∧ (b_ ∨ f ∨ g_) ∧ (e_ ∨ n_ ∨
            o_) ∧ (c_ ∨ d ∨ k) ∧ (e_ ∨ f ∨ j_) ∧ (c ∨ f ∨ n) ∧ (c ∨ i_ ∨ m_) ∧ (c_ ∨ d_ ∨ l)
            ∧ (g_ ∨ i ∨ j) ∧ (e ∨ f_ ∨ i) ∧ (c ∨ e ∨ l) ∧ (b_ ∨ h_ ∨ n_) ∧ (g ∨ l ∨ n) ∧ (g_
            ∨ i ∨ m_) ∧ (b ∨ e ∨ m_) ∧ (a_ ∨ i ∨ o_) ∧ (j_ ∨ k_ ∨ m_) ∧ (b ∨ g_ ∨ o_) ∧ (d ∨
            k_ ∨ n_) ∧ (k ∨ n ∨ o_) ∧ (f ∨ g ∨ m) ∧ (b_ ∨ k ∨ o_) ∧ (d ∨ f ∨ o_) ∧ (a_ ∨ e ∨
            h) ∧ (d_ ∨ j_ ∨ o_),
        (a_ ∨ b ∨ c ∨ e_ ∨ g ∨ h ∨ l_ ∨ n)]
    -- gens = [bpNot poly1]  -- gives 19 gens like in logic5.out.txt, looks like the same ideal
    gens = [bpNot poly2]    -- 65 zeros, 41 gens in all 3 monomial orders
    -}
    {- ⟨ o, ln+l+n+1, lm+l+m+1, kl+k, j, il+i, hl+h, hi+h, gl+g, gi+g, ghm+gh+gm+g, fl+f+l+1,
        fk+f+k+1, fi+f+i+1, fhm+fh+fm+f+hm+h+m+1, fgm+fg+fm+f+gm+g+m+1, e+1, dn+n, dl+d+l+1,
        dk+d+k+1, di+d+i+1, dgm+dg+dhm+dh+gm+g+hm+h, dgh+dh+gh+h, dfm+df+dm+d+fm+f+m+1, cl+c,
        ck+k, cim+im, chn+hn, chm+hm, cg+g, cf+c+f+1, cd+c+d+1, bm+b, bl+b, bk+b, bi+b, bh,
        bg, bf, bc+b, a+1 ⟩ LexCmp: 0.35 or 800+ (sugar) cpu seconds
    ⟨ o, j, e+1, a+1, ln+l+n+1, lm+l+m+1, kl+k, il+i, hl+h, hi+h, gl+g, gi+g, fl+f+l+1,
        fk+f+k+1, fi+f+i+1, dn+n, dl+d+l+1, dk+d+k+1, di+d+i+1, cl+c, ck+k, cg+g, cf+c+f+1,
        cd+c+d+1, bm+b, bl+b, bk+b, bi+b, bh, bg, bf, bc+b, ghm+gh+gm+g,
        fhm+fh+fm+hm+f+h+m+1, fgm+fg+fm+gm+f+g+m+1, dgm+dhm+dg+dh+gm+hm+g+h, dgh+dh+gh+h,
        dfm+df+dm+fm+d+f+m+1, cim+im, chn+hn, chm+hm ⟩ GrLexCmp: 0.4 or 3.8 (sugar) cpu seconds
    ⟨ o, j, e+1, a+1, ln+l+n+1, dn+n, lm+l+m+1, bm+b, kl+k, il+i, hl+h, gl+g, fl+f+l+1,
        dl+d+l+1, cl+c, bl+b, fk+f+k+1, dk+d+k+1, ck+k, bk+b, hi+h, gi+g, fi+f+i+1, di+d+i+1,
        bi+b, bh, cg+g, bg, cf+c+f+1, bf, cd+c+d+1, bc+b, chn+hn, cim+im, ghm+gh+gm+g,
        fhm+fh+fm+hm+f+h+m+1, chm+hm, fgm+fg+fm+gm+f+g+m+1, dgm+dhm+dg+dh+gm+hm+g+h,
        dfm+df+dm+fm+d+f+m+1, dgh+dh+gh+h ⟩ GrRevLexCmp: 0.4 or 26.7 (sugar) cpu seconds
    -}
    
    {- -}
    name            = "logic6"
    varPs@[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]             = map bpVar [0 .. 14]
    [a_, b_, c_, d_, e_, f_, g_, h_, i_, j_, k_, l_, m_, n_, o_]    = map bpNot varPs
    [poly1, poly2, poly3]   = [
        (g_ ∨ h_ ∨ j_ ∨ k ∨ m) ∧ (a_ ∨ b_ ∨ f ∨ k_ ∨ o_) ∧ (a ∨ d_ ∨ f_ ∨ n ∨ o) ∧ (f ∨ h ∨ i
            ∨ j ∨ o_) ∧ (a_ ∨ g_ ∨ i_ ∨ k_ ∨ n_) ∧ (a_ ∨ c ∨ e ∨ l_ ∨ m) ∧ (b ∨ c_ ∨ e ∨ f ∨
            j) ∧ (b ∨ d_ ∨ e_ ∨ g_ ∨ i_) ∧ (c ∨ e ∨ h_ ∨ j ∨ k_) ∧ (b ∨ c_ ∨ d_ ∨ k_ ∨ n_) ∧
            (b ∨ c_ ∨ g ∨ j_ ∨ o_) ∧ (c ∨ f ∨ g ∨ j_ ∨ m_) ∧ (a_ ∨ c ∨ d ∨ g ∨ l_) ∧ (b ∨ e ∨
            k ∨ m ∨ n_) ∧ (i ∨ j_ ∨ k ∨ l_ ∨ n_) ∧ (c_ ∨ d ∨ f_ ∨ h_ ∨ l) ∧ (e_ ∨ i ∨ k_ ∨ l
            ∨ n_) ∧ (a ∨ c ∨ d ∨ g ∨ m) ∧ (b ∨ g ∨ j ∨ k_ ∨ l_) ∧ (e ∨ i ∨ j ∨ k_ ∨ o_) ∧ (c_
            ∨ f_ ∨ g ∨ m_ ∨ o_) ∧ (e_ ∨ k_ ∨ l ∨ m ∨ o_) ∧ (f ∨ j_ ∨ k_ ∨ m ∨ n_) ∧ (a ∨ c ∨
            d ∨ f_ ∨ g_) ∧ (b ∨ i ∨ k ∨ n_ ∨ o) ∧ (c_ ∨ e ∨ i_ ∨ j ∨ o_) ∧ (c_ ∨ i ∨ j ∨ n ∨
            o_) ∧ (d ∨ f ∨ g ∨ l ∨ o_) ∧ (c_ ∨ e ∨ j ∨ l ∨ n_) ∧ (f_ ∨ h ∨ m_ ∨ n_ ∨ o) ∧ (e
            ∨ f ∨ h_ ∨ j ∨ n) ∧ (a_ ∨ f ∨ g_ ∨ k ∨ o_) ∧ (b_ ∨ e ∨ f ∨ i_ ∨ m_) ∧ (b_ ∨ c ∨ e
            ∨ l ∨ n_) ∧ (b ∨ c_ ∨ d_ ∨ g ∨ n_) ∧ (f ∨ g ∨ h_ ∨ j ∨ l) ∧ (a ∨ b_ ∨ j_ ∨ k_ ∨
            l) ∧ (a ∨ c ∨ h ∨ m_ ∨ n) ∧ (b ∨ g ∨ i_ ∨ m_ ∨ n) ∧ (a ∨ d ∨ f_ ∨ i ∨ k_) ∧ (a ∨
            d ∨ e ∨ h ∨ n_) ∧ (b ∨ c_ ∨ g_ ∨ i ∨ m_) ∧ (h ∨ j_ ∨ l ∨ n_ ∨ o_) ∧ (a ∨ c_ ∨ d_
            ∨ g ∨ l) ∧ (a ∨ h ∨ j ∨ k ∨ l_) ∧ (a ∨ b ∨ d_ ∨ f ∨ h_) ∧ (a ∨ c_ ∨ i ∨ k_ ∨ m) ∧
            (a ∨ b_ ∨ f ∨ g ∨ l_) ∧ (b ∨ e ∨ f ∨ l_ ∨ n) ∧ (a_ ∨ c ∨ d ∨ g_ ∨ l) ∧ (d_ ∨ e ∨
            h_ ∨ m_ ∨ o_) ∧ (c ∨ e ∨ f ∨ g_ ∨ n) ∧ (d ∨ e ∨ f ∨ k ∨ n) ∧ (a ∨ e_ ∨ h_ ∨ i_ ∨
            n) ∧ (d_ ∨ f ∨ g_ ∨ i_ ∨ k_) ∧ (c_ ∨ e_ ∨ i_ ∨ k_ ∨ m) ∧ (a_ ∨ c_ ∨ e ∨ h ∨ k_) ∧
            (d_ ∨ f ∨ h ∨ i ∨ n_) ∧ (a ∨ e_ ∨ i ∨ k ∨ o) ∧ (e_ ∨ h_ ∨ i_ ∨ j_ ∨ o) ∧ (a_ ∨ g_
            ∨ h ∨ j_ ∨ n) ∧ (c ∨ d ∨ h ∨ j ∨ n) ∧ (a ∨ d ∨ f_ ∨ g_ ∨ j_) ∧ (d ∨ h ∨ j_ ∨ m ∨
            n) ∧ (c_ ∨ g_ ∨ h_ ∨ j_ ∨ m) ∧ (c_ ∨ e ∨ j ∨ k ∨ o) ∧ (b ∨ e ∨ h ∨ k_ ∨ n) ∧ (a_
            ∨ d_ ∨ e ∨ i_ ∨ j_) ∧ (b ∨ g ∨ h_ ∨ j ∨ o_) ∧ (b_ ∨ e ∨ g_ ∨ i_ ∨ k_) ∧ (a_ ∨ e_
            ∨ i ∨ l ∨ n_) ∧ (a_ ∨ b_ ∨ d_ ∨ e_ ∨ o) ∧ (b ∨ d_ ∨ e_ ∨ h ∨ i_) ∧ (b ∨ g ∨ k_ ∨
            m_ ∨ o) ∧ (c_ ∨ i_ ∨ l_ ∨ m_ ∨ o_) ∧ (a_ ∨ f_ ∨ j ∨ k_ ∨ l) ∧ (b_ ∨ j_ ∨ k_ ∨ m ∨
            n) ∧ (b ∨ g ∨ h ∨ m ∨ n) ∧ (c_ ∨ l ∨ m_ ∨ n_ ∨ o) ∧ (e ∨ h ∨ j_ ∨ l ∨ n_) ∧ (a ∨
            c ∨ l ∨ m_ ∨ n) ∧ (c_ ∨ g ∨ i ∨ k_ ∨ o_) ∧ (b_ ∨ d_ ∨ f_ ∨ i ∨ j) ∧ (b ∨ f_ ∨ g ∨
            i_ ∨ k_) ∧ (c_ ∨ d_ ∨ f ∨ h_ ∨ n) ∧ (f_ ∨ h_ ∨ m_ ∨ n_ ∨ o_) ∧ (e_ ∨ h ∨ l_ ∨ m_
            ∨ n_) ∧ (c_ ∨ d ∨ h ∨ j_ ∨ o) ∧ (a ∨ f ∨ i_ ∨ j ∨ m) ∧ (b_ ∨ h_ ∨ l ∨ n ∨ o_) ∧
            (d_ ∨ e ∨ f_ ∨ k ∨ l_) ∧ (c_ ∨ f ∨ g ∨ k_ ∨ n_) ∧ (b_ ∨ e ∨ j ∨ l ∨ n_) ∧ (b ∨ d
            ∨ f ∨ i_ ∨ k) ∧ (c ∨ d ∨ g ∨ h ∨ o) ∧ (c_ ∨ d_ ∨ e_ ∨ g ∨ n_) ∧ (b_ ∨ f ∨ g ∨ j_
            ∨ o_) ∧ (a_ ∨ c_ ∨ e ∨ k ∨ m) ∧ (c_ ∨ h ∨ l_ ∨ m_ ∨ o) ∧ (a_ ∨ d_ ∨ e ∨ h_ ∨ o) ∧
            (b_ ∨ i ∨ j_ ∨ n_ ∨ o) ∧ (a_ ∨ g_ ∨ k ∨ l_ ∨ o_) ∧ (a_ ∨ d ∨ i_ ∨ k ∨ n_) ∧ (a ∨
            b ∨ k_ ∨ m_ ∨ n_) ∧ (a ∨ f ∨ g_ ∨ h ∨ j_) ∧ (b ∨ c_ ∨ d_ ∨ k_ ∨ l) ∧ (e ∨ j_ ∨ k
            ∨ l ∨ m_) ∧ (g_ ∨ h ∨ k ∨ n ∨ o_) ∧ (d ∨ e ∨ i_ ∨ n_ ∨ o_) ∧ (a_ ∨ i_ ∨ m_ ∨ n_ ∨
            o_) ∧ (b ∨ d ∨ j ∨ l ∨ n_) ∧ (a_ ∨ c ∨ h ∨ l ∨ m) ∧ (c ∨ h_ ∨ k_ ∨ n ∨ o) ∧ (b_ ∨
            e_ ∨ f_ ∨ k_ ∨ l) ∧ (e_ ∨ f_ ∨ g_ ∨ j_ ∨ o) ∧ (g ∨ h ∨ i_ ∨ j_ ∨ k_) ∧ (b_ ∨ c_ ∨
            e ∨ g_ ∨ i) ∧ (c_ ∨ f_ ∨ g ∨ i ∨ k) ∧ (d_ ∨ e_ ∨ i ∨ j_ ∨ k) ∧ (a_ ∨ c ∨ d_ ∨ i_
            ∨ o_) ∧ (c ∨ d ∨ j_ ∨ l_ ∨ m_) ∧ (c ∨ d ∨ f_ ∨ k_ ∨ o_) ∧ (c_ ∨ e_ ∨ g_ ∨ i_ ∨
            n_) ∧ (b ∨ g_ ∨ i ∨ n ∨ o_) ∧ (b_ ∨ d_ ∨ e ∨ k_ ∨ l) ∧ (g_ ∨ h ∨ k_ ∨ l ∨ m_) ∧
            (b_ ∨ e_ ∨ g_ ∨ k ∨ l) ∧ (b_ ∨ d_ ∨ f ∨ l_ ∨ o) ∧ (c ∨ i ∨ j ∨ k ∨ m_) ∧ (b ∨ c_
            ∨ e_ ∨ j_ ∨ l) ∧ (a ∨ h_ ∨ k ∨ l_ ∨ m_) ∧ (c_ ∨ d ∨ h_ ∨ i ∨ o_) ∧ (a_ ∨ b_ ∨ j_
            ∨ k ∨ n_) ∧ (a_ ∨ c ∨ d ∨ e_ ∨ f_) ∧ (e ∨ f_ ∨ g_ ∨ h ∨ k_) ∧ (b_ ∨ c ∨ h ∨ i_ ∨
            m_) ∧ (b ∨ c ∨ e_ ∨ f ∨ i_) ∧ (f ∨ i ∨ j_ ∨ k_ ∨ n_) ∧ (b ∨ d ∨ h ∨ i ∨ j_) ∧ (b_
            ∨ e ∨ g_ ∨ h ∨ j),
        (c ∨ d ∨ g ∨ h ∨ n) ∧ (a ∨ d ∨ f_ ∨ i ∨ k_) ∧ (g_ ∨ h ∨ j_ ∨ l ∨ o) ∧ (a ∨ g_ ∨ j_ ∨
            k ∨ o) ∧ (a_ ∨ c ∨ e_ ∨ h ∨ i_) ∧ (d ∨ e_ ∨ i_ ∨ k_ ∨ m) ∧ (a ∨ f_ ∨ i ∨ n ∨ o) ∧
            (c ∨ d ∨ h ∨ m ∨ n) ∧ (b ∨ c_ ∨ e ∨ m ∨ o_) ∧ (a_ ∨ f ∨ j_ ∨ k ∨ n_) ∧ (c ∨ e ∨ f
            ∨ h_ ∨ m_) ∧ (c_ ∨ i ∨ j_ ∨ m_ ∨ n_) ∧ (e ∨ h ∨ k ∨ m ∨ n_) ∧ (c ∨ i_ ∨ k_ ∨ n ∨
            o) ∧ (d_ ∨ g_ ∨ h_ ∨ j_ ∨ k) ∧ (h_ ∨ k ∨ l_ ∨ m_ ∨ o_) ∧ (a ∨ c_ ∨ d_ ∨ f ∨ j_) ∧
            (e ∨ f ∨ g_ ∨ k ∨ n) ∧ (d_ ∨ e ∨ f ∨ j_ ∨ m_) ∧ (b_ ∨ c_ ∨ i ∨ l ∨ o_) ∧ (a_ ∨ e_
            ∨ f ∨ i_ ∨ n_) ∧ (c_ ∨ e ∨ h_ ∨ i ∨ k) ∧ (a ∨ e ∨ i ∨ k ∨ m_) ∧ (c_ ∨ f ∨ l ∨ n_
            ∨ o_) ∧ (b ∨ c_ ∨ g ∨ k ∨ o_) ∧ (b ∨ c_ ∨ f ∨ i_ ∨ n_) ∧ (f_ ∨ h ∨ i ∨ k ∨ m_) ∧
            (b ∨ c ∨ d ∨ h ∨ l) ∧ (b ∨ g ∨ h_ ∨ j ∨ o_) ∧ (c ∨ d ∨ e ∨ i_ ∨ n_) ∧ (d_ ∨ i ∨
            j_ ∨ k ∨ l_) ∧ (a ∨ b ∨ h ∨ k ∨ l_) ∧ (b ∨ d ∨ g ∨ k_ ∨ o_) ∧ (c_ ∨ e ∨ f ∨ l_ ∨
            o_) ∧ (c_ ∨ e ∨ i ∨ k_ ∨ o_) ∧ (b ∨ c_ ∨ d ∨ g ∨ o_) ∧ (c_ ∨ e ∨ i ∨ l ∨ o_) ∧ (h
            ∨ i_ ∨ k_ ∨ l ∨ o_) ∧ (a_ ∨ f ∨ h ∨ j_ ∨ k_) ∧ (a_ ∨ f ∨ j_ ∨ n_ ∨ o_) ∧ (a ∨ b ∨
            h ∨ i ∨ m_) ∧ (a ∨ f ∨ g ∨ j ∨ l_) ∧ (a_ ∨ c_ ∨ e ∨ j ∨ o_) ∧ (c_ ∨ e ∨ i_ ∨ j ∨
            k) ∧ (b_ ∨ g_ ∨ h ∨ l ∨ o_) ∧ (c ∨ f ∨ j_ ∨ k_ ∨ o) ∧ (b_ ∨ c ∨ d ∨ e ∨ k_) ∧ (c_
            ∨ e ∨ g_ ∨ h ∨ n_) ∧ (d ∨ f ∨ h ∨ i ∨ o_) ∧ (d_ ∨ f ∨ g_ ∨ j_ ∨ l) ∧ (b_ ∨ f ∨ i
            ∨ l ∨ o_) ∧ (b_ ∨ d_ ∨ i ∨ l ∨ m_) ∧ (a_ ∨ f ∨ j_ ∨ l ∨ n_) ∧ (a_ ∨ b_ ∨ d_ ∨ g_
            ∨ i_) ∧ (g_ ∨ h ∨ j_ ∨ k ∨ n) ∧ (a_ ∨ b ∨ g ∨ j ∨ k_) ∧ (g_ ∨ h_ ∨ j_ ∨ k ∨ m) ∧
            (b_ ∨ f ∨ h ∨ l_ ∨ m_) ∧ (e ∨ f ∨ l_ ∨ m_ ∨ o_) ∧ (e ∨ f_ ∨ i ∨ l ∨ m_) ∧ (f ∨ i_
            ∨ k_ ∨ l_ ∨ m) ∧ (b ∨ d ∨ h ∨ k ∨ o_) ∧ (c_ ∨ f_ ∨ j_ ∨ l ∨ m_) ∧ (c_ ∨ d_ ∨ e ∨
            g_ ∨ j) ∧ (a ∨ b ∨ h ∨ n ∨ o_) ∧ (b ∨ c_ ∨ l_ ∨ m_ ∨ n_) ∧ (c_ ∨ e ∨ f_ ∨ l ∨ n_)
            ∧ (d ∨ e ∨ f ∨ i_ ∨ l_) ∧ (a ∨ b ∨ c_ ∨ m_ ∨ n_) ∧ (b ∨ c_ ∨ g ∨ l ∨ n_) ∧ (c_ ∨
            d_ ∨ e ∨ f ∨ m_) ∧ (i ∨ j_ ∨ k ∨ n_ ∨ o) ∧ (a ∨ c_ ∨ e ∨ i ∨ j_) ∧ (b ∨ c ∨ d ∨
            e_ ∨ i_) ∧ (a ∨ h ∨ j_ ∨ k_ ∨ l) ∧ (b ∨ f ∨ h_ ∨ i_ ∨ n_) ∧ (b ∨ c_ ∨ e ∨ i ∨ m_)
            ∧ (b_ ∨ g_ ∨ h ∨ l ∨ m_) ∧ (a ∨ d ∨ f_ ∨ i ∨ m) ∧ (f ∨ g_ ∨ h ∨ k_ ∨ o_) ∧ (e_ ∨
            f ∨ g_ ∨ h ∨ j_) ∧ (e ∨ i ∨ l ∨ m_ ∨ o_) ∧ (a ∨ b_ ∨ f ∨ g ∨ l_) ∧ (d_ ∨ i ∨ j_ ∨
            k ∨ m_) ∧ (c ∨ f ∨ j_ ∨ l_ ∨ o) ∧ (c_ ∨ k_ ∨ l ∨ m ∨ n_) ∧ (d_ ∨ e ∨ f ∨ j_ ∨ l_)
            ∧ (f ∨ h ∨ i ∨ k_ ∨ o_) ∧ (a ∨ b ∨ c_ ∨ g ∨ i) ∧ (d ∨ e_ ∨ h ∨ l_ ∨ m_) ∧ (b ∨ f
            ∨ i_ ∨ m ∨ o_) ∧ (b ∨ f ∨ h ∨ j_ ∨ k) ∧ (a ∨ c ∨ d ∨ e ∨ h) ∧ (a_ ∨ e ∨ f ∨ h ∨
            m) ∧ (f ∨ g ∨ k_ ∨ m_ ∨ o_) ∧ (a_ ∨ c_ ∨ e ∨ k ∨ m) ∧ (b ∨ e ∨ i ∨ m_ ∨ n) ∧ (b ∨
            d ∨ g ∨ m_ ∨ n_) ∧ (b ∨ c_ ∨ e ∨ f ∨ l_) ∧ (c ∨ d ∨ f_ ∨ h ∨ l) ∧ (f_ ∨ h ∨ k ∨
            l_ ∨ m_) ∧ (d ∨ f ∨ h ∨ j_ ∨ o_) ∧ (f ∨ g_ ∨ h ∨ i ∨ o_) ∧ (a ∨ b_ ∨ k ∨ l_ ∨ m_)
            ∧ (a_ ∨ g_ ∨ i_ ∨ k ∨ o_) ∧ (a ∨ b ∨ c ∨ d ∨ n) ∧ (c_ ∨ e ∨ h ∨ i_ ∨ k) ∧ (b ∨ e
            ∨ i ∨ l ∨ m_) ∧ (b ∨ c_ ∨ f ∨ k ∨ o_) ∧ (a ∨ f ∨ i_ ∨ k ∨ l_) ∧ (c_ ∨ e ∨ i ∨ k ∨
            m_) ∧ (a ∨ c_ ∨ d_ ∨ f ∨ h) ∧ (c_ ∨ g_ ∨ h ∨ j_ ∨ o) ∧ (a_ ∨ i_ ∨ j_ ∨ l ∨ n_) ∧
            (a_ ∨ c_ ∨ e ∨ g ∨ o_) ∧ (b ∨ e_ ∨ i_ ∨ j_ ∨ k_) ∧ (c_ ∨ d_ ∨ f ∨ h_ ∨ j_) ∧ (e ∨
            h ∨ j_ ∨ l ∨ n_) ∧ (e_ ∨ f ∨ g ∨ k_ ∨ n_) ∧ (a_ ∨ c ∨ f ∨ h ∨ j_) ∧ (a_ ∨ c ∨ f ∨
            i_ ∨ o_) ∧ (a_ ∨ i_ ∨ j ∨ n_ ∨ o_) ∧ (a_ ∨ f_ ∨ h ∨ i_ ∨ k_) ∧ (b_ ∨ f_ ∨ i_ ∨ m_
            ∨ o_) ∧ (c_ ∨ i ∨ l ∨ m_ ∨ n_) ∧ (b ∨ d ∨ j_ ∨ l_ ∨ o_) ∧ (a_ ∨ c_ ∨ e ∨ f_ ∨ l)
            ∧ (b_ ∨ h ∨ k ∨ m_ ∨ n_) ∧ (c_ ∨ d_ ∨ f ∨ j_ ∨ n_) ∧ (a ∨ h ∨ j ∨ l_ ∨ m_) ∧ (c ∨
            d ∨ f_ ∨ j ∨ o_) ∧ (a_ ∨ c_ ∨ e ∨ k ∨ n_) ∧ (a_ ∨ c ∨ i_ ∨ n_ ∨ o_) ∧ (b ∨ f ∨ j_
            ∨ n_ ∨ o) ∧ (d ∨ e ∨ h ∨ k ∨ o_),
        (b ∨ d_ ∨ g_ ∨ i ∨ j ∨ k_ ∨ l ∨ m_)]
    -- gens = [bpNot poly1]    -- 471 zeros; GrLexCmp, 807 gens, times vary:
            -- 786s cpu: generated (redundant) basis has 5917 elements with 1876000 monomials
            -- 3477s cpu: generated (redundant) basis has 6849 elements with 4039229 monomials
            -- note g0: abcdefghijklmno+... (10235 terms) - init gen is long high degree (15)
        -- with GrRevLexCmp, the generators seem to grow not shrink, so much slower
        -- LexCmp, 414 gens, 326s cpu,
            -- generated (redundant) basis has 4964 elements with 976490 monomials
    varSs           = map (: []) ['a' .. 'o']
    pRead           = (\ [(x,"")] -> x) . polynomReads gbpA.pR (zip varSs varPs)
    gens = map pRead
        ["ghj(k+1)(m+1)", "ab(f+1)ko", "(a+1)df(n+1)(o+1)", "(f+1)(h+1)(i+1)(j+1)o", "agikn",
        "a(c+1)(e+1)l(m+1)", "(b+1)c(e+1)(f+1)(j+1)", "(b+1)degi", "(c+1)(e+1)h(j+1)k", "(b+1)cdkn",
        "(b+1)c(g+1)jo", "(c+1)(f+1)(g+1)jm", "a(c+1)(d+1)(g+1)l", "(b+1)(e+1)(k+1)(m+1)n",
        "(i+1)j(k+1)ln", "c(d+1)fh(l+1)", "e(i+1)k(l+1)n", "(a+1)(c+1)(d+1)(g+1)(m+1)",
        "(b+1)(g+1)(j+1)kl", "(e+1)(i+1)(j+1)ko", "cf(g+1)mo", "ek(l+1)(m+1)o", "(f+1)jk(m+1)n",
        "(a+1)(c+1)(d+1)fg", "(b+1)(i+1)(k+1)n(o+1)", "c(e+1)i(j+1)o", "c(i+1)(j+1)(n+1)o",
        "(d+1)(f+1)(g+1)(l+1)o", "c(e+1)(j+1)(l+1)n", "f(h+1)mn(o+1)", "(e+1)(f+1)h(j+1)(n+1)",
        "a(f+1)g(k+1)o", "b(e+1)(f+1)im", "b(c+1)(e+1)(l+1)n", "(b+1)cd(g+1)n", "(f+1)(g+1)h(j+1)(l+1)",
        "(a+1)bjk(l+1)", "(a+1)(c+1)(h+1)m(n+1)", "(b+1)(g+1)im(n+1)", "(a+1)(d+1)f(i+1)k",
        "(a+1)(d+1)(e+1)(h+1)n", "(b+1)cg(i+1)m", "(h+1)j(l+1)no", "(a+1)cd(g+1)(l+1)",
        "(a+1)(h+1)(j+1)(k+1)l", "(a+1)(b+1)d(f+1)h", "(a+1)c(i+1)k(m+1)", "(a+1)b(f+1)(g+1)l",
        "(b+1)(e+1)(f+1)l(n+1)", "a(c+1)(d+1)g(l+1)", "d(e+1)hmo", "(c+1)(e+1)(f+1)g(n+1)",
        "(d+1)(e+1)(f+1)(k+1)(n+1)", "(a+1)ehi(n+1)", "d(f+1)gik", "ceik(m+1)", "ac(e+1)(h+1)k",
        "d(f+1)(h+1)(i+1)n", "(a+1)e(i+1)(k+1)(o+1)", "ehij(o+1)", "ag(h+1)j(n+1)",
        "(c+1)(d+1)(h+1)(j+1)(n+1)", "(a+1)(d+1)fgj", "(d+1)(h+1)j(m+1)(n+1)", "cghj(m+1)",
        "c(e+1)(j+1)(k+1)(o+1)", "(b+1)(e+1)(h+1)k(n+1)", "ad(e+1)ij", "(b+1)(g+1)h(j+1)o", "b(e+1)gik",
        "ae(i+1)(l+1)n", "abde(o+1)", "(b+1)de(h+1)i", "(b+1)(g+1)km(o+1)", "cilmo", "af(j+1)k(l+1)",
        "bjk(m+1)(n+1)", "(b+1)(g+1)(h+1)(m+1)(n+1)", "c(l+1)mn(o+1)", "(e+1)(h+1)j(l+1)n",
        "(a+1)(c+1)(l+1)m(n+1)", "c(g+1)(i+1)ko", "bdf(i+1)(j+1)", "(b+1)f(g+1)ik", "cd(f+1)h(n+1)",
        "fhmno", "e(h+1)lmn", "c(d+1)(h+1)j(o+1)", "(a+1)(f+1)i(j+1)(m+1)", "bh(l+1)(n+1)o",
        "d(e+1)f(k+1)l", "c(f+1)(g+1)kn", "b(e+1)(j+1)(l+1)n", "(b+1)(d+1)(f+1)i(k+1)",
        "(c+1)(d+1)(g+1)(h+1)(o+1)", "cde(g+1)n", "b(f+1)(g+1)jo", "ac(e+1)(k+1)(m+1)", "c(h+1)lm(o+1)",
        "ad(e+1)h(o+1)", "b(i+1)jn(o+1)", "ag(k+1)lo", "a(d+1)i(k+1)n", "(a+1)(b+1)kmn",
        "(a+1)(f+1)g(h+1)j", "(b+1)cdk(l+1)", "(e+1)j(k+1)(l+1)m", "g(h+1)(k+1)(n+1)o", "(d+1)(e+1)ino",
        "aimno", "(b+1)(d+1)(j+1)(l+1)n", "a(c+1)(h+1)(l+1)(m+1)", "(c+1)hk(n+1)(o+1)", "befk(l+1)",
        "efgj(o+1)", "(g+1)(h+1)ijk", "bc(e+1)g(i+1)", "cf(g+1)(i+1)(k+1)", "de(i+1)j(k+1)", "a(c+1)dio",
        "(c+1)(d+1)jlm", "(c+1)(d+1)fko", "cegin", "(b+1)g(i+1)(n+1)o", "bd(e+1)k(l+1)", "g(h+1)k(l+1)m",
        "beg(k+1)(l+1)", "bd(f+1)l(o+1)", "(c+1)(i+1)(j+1)(k+1)m", "(b+1)cej(l+1)", "(a+1)h(k+1)lm",
        "c(d+1)h(i+1)o", "abj(k+1)n", "a(c+1)(d+1)ef", "(e+1)fg(h+1)k", "b(c+1)(h+1)im",
        "(b+1)(c+1)e(f+1)i", "(f+1)(i+1)jkn", "(b+1)(d+1)(h+1)(i+1)j", "b(e+1)g(h+1)(j+1)"]
    -- 471 zeros;
        -- LexCmp 414 gens, 66s cpu,
            -- generated (redundant) basis has 3724 elements with 248171 monomials
        -- GrLexCmp 807 gens, 365s cpu,
            -- generated (redundant) basis has 4026 elements with 462290 monomials
    


main    :: IO ()
main    = do
    nCores      <- getNumCapabilities
    
    doneMVar    <- newEmptyMVar
    _           <- forkOn 0 $ do
        -- for gbTrace bits, see Math/Algebra/Commutative/GroebnerBasis.hs:
        let gbTrace     = gbTSummary -- .|. gbTResults
                -- .|. gbTProgressInfo .|. gbTQueues .|. gbTProgressDetails     -- @@
        bpDemo nCores gbTrace
        putMVar doneMVar ()
    takeMVar doneMVar
