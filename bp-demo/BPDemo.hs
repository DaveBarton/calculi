{-# LANGUAGE Strict #-}

{- |  BinPoly demo examples  -}

import Math.Algebra.General.Algebra
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.BinPoly

-- import Control.Monad (when)
import Data.Foldable (foldl', toList)
-- import qualified Data.Sequence as Seq
import Data.Word (Word64)

import Control.Concurrent (forkOn, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)

-- import Debug.Trace


demoOps             :: Int -> StdEvCmp ->
                        (GBPolyOps EV58 EV58 (BinPoly EV58), BPOtherOps EV58 Word64)
demoOps nVars sec   = bp58Ops evCmp isGraded varSs useSugar
  where
    evCmp           = evCmp58 sec
    isGraded        = secIsGraded sec
    xVarSs          = ['X' : show n | n <- [1 :: Int ..]]
    varSs           = take nVars (map (: []) ['a' .. 'z'] ++ xVarSs)
    useSugar        = False

bpDemo                  :: Int -> Int -> IO ()
bpDemo nCores gbTrace   = do
    putStrLn $ name ++ " " ++ show sec
    -- when (Seq.length reducedGBGensSeq < 250) $ mapM_ (putStrLn . pShow) reducedGBGensL
    putStrLn $ show (bpCountZeros bpoA reducedGBGensL) ++ " receiver zeros"
    putStrLn $ show (bpCountZeros bpoA toReduce) ++ " sender zeros"
    putStrLn $ show (length revSend) ++ " of " ++ show (length toReduce) ++
        " generators to send:"
    putStrLn $ showGens pShow (reverse revSend)
  where
    -- To run a demo, first set the "@@" lines below the way you want.

    sec             = LexCmp   -- @@ LexCmp, GrLexCmp, or GrRevLexCmp
    (gbpA@(GBPolyOps { pR, numTerms, pShow }), bpoA@(BPOtherOps { pRead }))
                    = demoOps nVars sec
    smA@(SubmoduleOps { .. })   = gbiSmOps gbpA nCores
    
    initGensL       = map (map pRead) initGenSsL
    gbIdeal         = fromGens smA gbTrace (initGensL !! 1)
    reducedGBGensSeq    = stdGens True gbIdeal
    reducedGBGensL      = toList reducedGBGensSeq
    toReduce        = initGensL !! 0                -- @@ more 0-based indexing, sender
    shorter p q     = if numTerms p <= numTerms q then p else q
    plus1 arg@(sm, gs) g    =
        let g1  = smA.bModBy True sm g
        in  if pR.isZero g1 then arg else (smA.plusGens 0 sm [g1], (shorter g1 g) : gs)
    (_recSm1, revSend)  = foldl' plus1 (gbIdeal, []) toReduce
    
    -- @@ choose a name, nVars, and gens, commenting out the other examples:
    -- 'a' is the most main variable
    {- 
    name            = "logic3"
    nVars           = 10
    initGenSsL      = [
        ["(e+1)f(j+1)", "(d+1)(e+1)(g+1)", "b(f+1)(i+1)", "egi", "d(h+1)(j+1)",
            "(c+1)e(g+1)", "e(f+1)(h+1)", "(f+1)(g+1)(i+1)", "(c+1)i(j+1)", "(e+1)hj",
            "(c+1)fi", "cfg", "a(e+1)f", "(f+1)(h+1)i", "(a+1)fi", "a(d+1)(f+1)", "ac(j+1)",
            "b(e+1)i", "b(g+1)(h+1)", "a(h+1)i", "(d+1)f(i+1)", "afj", "e(f+1)(j+1)",
            "(g+1)(i+1)j", "efh", "(b+1)ef", "bcg", "(c+1)(g+1)(i+1)", "(b+1)(f+1)j",
            "e(h+1)(j+1)", "ac(g+1)", "c(f+1)g", "d(g+1)i", "(a+1)(d+1)(i+1)", "ehj",
            "(a+1)bg", "d(i+1)j", "(c+1)(g+1)(h+1)", "b(h+1)j", "aij", "c(d+1)h", "bdh",
            "a(b+1)(c+1)", "(b+1)(d+1)(g+1)", "(a+1)g(h+1)", "b(c+1)d", "b(e+1)(i+1)",
            "a(c+1)(h+1)", "df(i+1)", "aeg"],
        ["(d+1)(e+1)(i+1)", "bc(d+1)", "d(g+1)i", "a(b+1)(c+1)", "(b+1)(g+1)(i+1)",
            "(f+1)ij", "(e+1)f(g+1)", "ab(d+1)", "bei", "(a+1)fj", "d(f+1)i", "cd(g+1)",
            "be(i+1)", "bc(e+1)", "a(d+1)(h+1)", "(d+1)(h+1)j", "c(f+1)(i+1)", "e(f+1)h",
            "(b+1)(f+1)j", "(d+1)(g+1)j", "(a+1)(b+1)c", "(b+1)(h+1)j", "afi", "ceg",
            "(b+1)cd", "f(g+1)h", "(e+1)(g+1)(i+1)", "(b+1)c(i+1)", "c(f+1)h", "a(e+1)i",
            "afg", "(a+1)(c+1)i", "b(i+1)j", "(b+1)d(g+1)", "cf(g+1)", "b(c+1)(e+1)",
            "(c+1)de", "a(h+1)i", "g(i+1)j", "dej"],
        ["(e+1)(h+1)(i+1)"]]
    -}
    {- 
    name            = "logic5"
    nVars           = 15
    initGenSsL      = [
        ["(l+1)n(o+1)", "(f+1)(l+1)o", "(h+1)(j+1)(l+1)", "ejn", "(a+1)(c+1)(l+1)",
            "(f+1)g(j+1)", "(d+1)(j+1)o", "d(f+1)(j+1)", "(a+1)(c+1)o", "(g+1)(j+1)(l+1)",
            "(i+1)(m+1)(n+1)", "(c+1)hi", "(c+1)gi", "agh", "(a+1)(i+1)(j+1)", "(c+1)d(k+1)",
            "(i+1)(k+1)(l+1)", "(f+1)(l+1)m", "(d+1)(j+1)n", "(c+1)(g+1)(l+1)",
            "(e+1)(m+1)o", "ejm", "(c+1)hl", "ej(k+1)", "aej", "c(e+1)(f+1)", "e(i+1)j",
            "(a+1)(e+1)k", "(b+1)h(i+1)", "(a+1)km", "(a+1)cg", "b(e+1)n", "(b+1)ko",
            "(e+1)gl", "a(d+1)g", "(a+1)ho", "d(j+1)o", "(e+1)(f+1)(h+1)", "ci(l+1)",
            "(f+1)l(m+1)", "(f+1)il", "(h+1)ik", "(c+1)(i+1)(j+1)", "jln", "(e+1)(i+1)(k+1)",
            "e(h+1)(m+1)", "(d+1)jk", "(a+1)(f+1)(o+1)", "(b+1)k(n+1)", "(d+1)(e+1)i",
            "(d+1)e(g+1)", "(c+1)(m+1)(n+1)", "e(f+1)(j+1)", "a(l+1)o", "j(l+1)o", "b(g+1)k",
            "(d+1)(e+1)o", "(f+1)(h+1)m", "(c+1)(h+1)n", "(f+1)h(o+1)", "eg(i+1)", "a(d+1)f",
            "(b+1)(c+1)l", "b(i+1)k", "(e+1)(j+1)(o+1)", "(b+1)(d+1)(o+1)", "i(k+1)o",
            "(a+1)(k+1)o", "a(e+1)m", "(e+1)(g+1)l", "(i+1)(k+1)n", "(a+1)(c+1)(e+1)",
            "a(c+1)l", "(d+1)(f+1)l", "(c+1)(h+1)(n+1)", "ejl", "bd(k+1)", "(a+1)cl", "fjm",
            "hj(o+1)"],
        ["(d+1)(g+1)h", "(a+1)fk", "(a+1)kl", "(c+1)go", "(a+1)(b+1)(h+1)", "(a+1)c(f+1)",
            "(c+1)(e+1)(g+1)", "(d+1)lo", "bfk", "fh(i+1)", "(c+1)(d+1)e", "(e+1)k(m+1)",
            "ei(l+1)", "b(f+1)(l+1)", "(f+1)(h+1)(k+1)", "fjk", "(c+1)hn", "(b+1)fj",
            "(c+1)kl", "(e+1)(f+1)j", "(e+1)ln", "bf(k+1)", "dmo", "bch", "(a+1)(g+1)(h+1)",
            "(a+1)k(l+1)", "b(g+1)j", "(c+1)g(k+1)", "b(h+1)(i+1)", "(c+1)lo", "(c+1)ij",
            "(f+1)(k+1)(o+1)", "a(m+1)o", "(a+1)dh", "c(e+1)(o+1)", "d(e+1)(f+1)",
            "(e+1)(i+1)l", "(f+1)(i+1)(o+1)", "(e+1)fh", "c(l+1)m", "(c+1)(f+1)g",
            "(e+1)(h+1)(l+1)", "(d+1)(f+1)(m+1)", "(g+1)jn", "(c+1)(g+1)j",
            "(j+1)(l+1)(m+1)", "(b+1)(d+1)(i+1)", "g(h+1)(m+1)", "(c+1)g(n+1)", "(f+1)jo",
            "(c+1)km", "b(f+1)g", "eno", "c(d+1)(k+1)", "e(f+1)j", "(c+1)(f+1)(n+1)",
            "(c+1)im", "cd(l+1)", "g(i+1)(j+1)", "(e+1)f(i+1)", "(c+1)(e+1)(l+1)", "bhn",
            "(g+1)(l+1)(n+1)", "g(i+1)m", "(b+1)(e+1)m", "a(i+1)o", "jkm", "(b+1)go",
            "(d+1)kn", "(k+1)(n+1)o", "(f+1)(g+1)(m+1)", "b(k+1)o", "(d+1)(f+1)o",
            "a(e+1)(h+1)", "djo"],
        ["a(b+1)(c+1)e(g+1)(h+1)l(n+1)"]]
    -- gens = [bpNot poly1] -- gives 19 gens like in logic5.out.txt, looks like the same ideal
    -- gens = [bpNot poly2] -- 65 zeros, 41 gens in all 3 monomial orders:
    ⟨ o, ln+l+n+1, lm+l+m+1, kl+k, j, il+i, hl+h, hi+h, gl+g, gi+g, ghm+gh+gm+g, fl+f+l+1,
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
    {- 
    name            = "logic6"
    nVars           = 15
    initGenSsL      = [
        ["ghj(k+1)(m+1)", "ab(f+1)ko", "(a+1)df(n+1)(o+1)", "(f+1)(h+1)(i+1)(j+1)o", "agikn",
            "a(c+1)(e+1)l(m+1)", "(b+1)c(e+1)(f+1)(j+1)", "(b+1)degi", "(c+1)(e+1)h(j+1)k",
            "(b+1)cdkn", "(b+1)c(g+1)jo", "(c+1)(f+1)(g+1)jm", "a(c+1)(d+1)(g+1)l",
            "(b+1)(e+1)(k+1)(m+1)n", "(i+1)j(k+1)ln", "c(d+1)fh(l+1)", "e(i+1)k(l+1)n",
            "(a+1)(c+1)(d+1)(g+1)(m+1)", "(b+1)(g+1)(j+1)kl", "(e+1)(i+1)(j+1)ko",
            "cf(g+1)mo", "ek(l+1)(m+1)o", "(f+1)jk(m+1)n", "(a+1)(c+1)(d+1)fg",
            "(b+1)(i+1)(k+1)n(o+1)", "c(e+1)i(j+1)o", "c(i+1)(j+1)(n+1)o",
            "(d+1)(f+1)(g+1)(l+1)o", "c(e+1)(j+1)(l+1)n", "f(h+1)mn(o+1)",
            "(e+1)(f+1)h(j+1)(n+1)", "a(f+1)g(k+1)o", "b(e+1)(f+1)im", "b(c+1)(e+1)(l+1)n",
            "(b+1)cd(g+1)n", "(f+1)(g+1)h(j+1)(l+1)", "(a+1)bjk(l+1)",
            "(a+1)(c+1)(h+1)m(n+1)", "(b+1)(g+1)im(n+1)", "(a+1)(d+1)f(i+1)k",
            "(a+1)(d+1)(e+1)(h+1)n", "(b+1)cg(i+1)m", "(h+1)j(l+1)no", "(a+1)cd(g+1)(l+1)",
            "(a+1)(h+1)(j+1)(k+1)l", "(a+1)(b+1)d(f+1)h", "(a+1)c(i+1)k(m+1)",
            "(a+1)b(f+1)(g+1)l", "(b+1)(e+1)(f+1)l(n+1)", "a(c+1)(d+1)g(l+1)", "d(e+1)hmo",
            "(c+1)(e+1)(f+1)g(n+1)", "(d+1)(e+1)(f+1)(k+1)(n+1)", "(a+1)ehi(n+1)",
            "d(f+1)gik", "ceik(m+1)", "ac(e+1)(h+1)k", "d(f+1)(h+1)(i+1)n",
            "(a+1)e(i+1)(k+1)(o+1)", "ehij(o+1)", "ag(h+1)j(n+1)",
            "(c+1)(d+1)(h+1)(j+1)(n+1)", "(a+1)(d+1)fgj", "(d+1)(h+1)j(m+1)(n+1)",
            "cghj(m+1)", "c(e+1)(j+1)(k+1)(o+1)", "(b+1)(e+1)(h+1)k(n+1)", "ad(e+1)ij",
            "(b+1)(g+1)h(j+1)o", "b(e+1)gik", "ae(i+1)(l+1)n", "abde(o+1)", "(b+1)de(h+1)i",
            "(b+1)(g+1)km(o+1)", "cilmo", "af(j+1)k(l+1)", "bjk(m+1)(n+1)",
            "(b+1)(g+1)(h+1)(m+1)(n+1)", "c(l+1)mn(o+1)", "(e+1)(h+1)j(l+1)n",
            "(a+1)(c+1)(l+1)m(n+1)", "c(g+1)(i+1)ko", "bdf(i+1)(j+1)", "(b+1)f(g+1)ik",
            "cd(f+1)h(n+1)", "fhmno", "e(h+1)lmn", "c(d+1)(h+1)j(o+1)",
            "(a+1)(f+1)i(j+1)(m+1)", "bh(l+1)(n+1)o", "d(e+1)f(k+1)l", "c(f+1)(g+1)kn",
            "b(e+1)(j+1)(l+1)n", "(b+1)(d+1)(f+1)i(k+1)", "(c+1)(d+1)(g+1)(h+1)(o+1)",
            "cde(g+1)n", "b(f+1)(g+1)jo", "ac(e+1)(k+1)(m+1)", "c(h+1)lm(o+1)",
            "ad(e+1)h(o+1)", "b(i+1)jn(o+1)", "ag(k+1)lo", "a(d+1)i(k+1)n", "(a+1)(b+1)kmn",
            "(a+1)(f+1)g(h+1)j", "(b+1)cdk(l+1)", "(e+1)j(k+1)(l+1)m", "g(h+1)(k+1)(n+1)o",
            "(d+1)(e+1)ino", "aimno", "(b+1)(d+1)(j+1)(l+1)n", "a(c+1)(h+1)(l+1)(m+1)",
            "(c+1)hk(n+1)(o+1)", "befk(l+1)", "efgj(o+1)", "(g+1)(h+1)ijk", "bc(e+1)g(i+1)",
            "cf(g+1)(i+1)(k+1)", "de(i+1)j(k+1)", "a(c+1)dio", "(c+1)(d+1)jlm",
            "(c+1)(d+1)fko", "cegin", "(b+1)g(i+1)(n+1)o", "bd(e+1)k(l+1)", "g(h+1)k(l+1)m",
            "beg(k+1)(l+1)", "bd(f+1)l(o+1)", "(c+1)(i+1)(j+1)(k+1)m", "(b+1)cej(l+1)",
            "(a+1)h(k+1)lm", "c(d+1)h(i+1)o", "abj(k+1)n", "a(c+1)(d+1)ef", "(e+1)fg(h+1)k",
            "b(c+1)(h+1)im", "(b+1)(c+1)e(f+1)i", "(f+1)(i+1)jkn", "(b+1)(d+1)(h+1)(i+1)j",
            "b(e+1)g(h+1)(j+1)"],
        ["(c+1)(d+1)(g+1)(h+1)(n+1)", "(a+1)(d+1)f(i+1)k", "g(h+1)j(l+1)(o+1)",
            "(a+1)gj(k+1)(o+1)", "a(c+1)e(h+1)i", "(d+1)eik(m+1)", "(a+1)f(i+1)(n+1)(o+1)",
            "(c+1)(d+1)(h+1)(m+1)(n+1)", "(b+1)c(e+1)(m+1)o", "a(f+1)j(k+1)n",
            "(c+1)(e+1)(f+1)hm", "c(i+1)jmn", "(e+1)(h+1)(k+1)(m+1)n", "(c+1)ik(n+1)(o+1)",
            "dghj(k+1)", "h(k+1)lmo", "(a+1)cd(f+1)j", "(e+1)(f+1)g(k+1)(n+1)",
            "d(e+1)(f+1)jm", "bc(i+1)(l+1)o", "ae(f+1)in", "c(e+1)h(i+1)(k+1)",
            "(a+1)(e+1)(i+1)(k+1)m", "c(f+1)(l+1)no", "(b+1)c(g+1)(k+1)o", "(b+1)c(f+1)in",
            "f(h+1)(i+1)(k+1)m", "(b+1)(c+1)(d+1)(h+1)(l+1)", "(b+1)(g+1)h(j+1)o",
            "(c+1)(d+1)(e+1)in", "d(i+1)j(k+1)l", "(a+1)(b+1)(h+1)(k+1)l",
            "(b+1)(d+1)(g+1)ko", "c(e+1)(f+1)lo", "c(e+1)(i+1)ko", "(b+1)c(d+1)(g+1)o",
            "c(e+1)(i+1)(l+1)o", "(h+1)ik(l+1)o", "a(f+1)(h+1)jk", "a(f+1)jno",
            "(a+1)(b+1)(h+1)(i+1)m", "(a+1)(f+1)(g+1)(j+1)l", "ac(e+1)(j+1)o",
            "c(e+1)i(j+1)(k+1)", "bg(h+1)(l+1)o", "(c+1)(f+1)jk(o+1)", "b(c+1)(d+1)(e+1)k",
            "c(e+1)g(h+1)n", "(d+1)(f+1)(h+1)(i+1)o", "d(f+1)gj(l+1)", "b(f+1)(i+1)(l+1)o",
            "bd(i+1)(l+1)m", "a(f+1)j(l+1)n", "abdgi", "g(h+1)j(k+1)(n+1)",
            "a(b+1)(g+1)(j+1)k", "ghj(k+1)(m+1)", "b(f+1)(h+1)lm", "(e+1)(f+1)lmo",
            "(e+1)f(i+1)(l+1)m", "(f+1)ikl(m+1)", "(b+1)(d+1)(h+1)(k+1)o", "cfj(l+1)m",
            "cd(e+1)g(j+1)", "(a+1)(b+1)(h+1)(n+1)o", "(b+1)clmn", "c(e+1)f(l+1)n",
            "(d+1)(e+1)(f+1)il", "(a+1)(b+1)cmn", "(b+1)c(g+1)(l+1)n", "cd(e+1)(f+1)m",
            "(i+1)j(k+1)n(o+1)", "(a+1)c(e+1)(i+1)j", "(b+1)(c+1)(d+1)ei",
            "(a+1)(h+1)jk(l+1)", "(b+1)(f+1)hin", "(b+1)c(e+1)(i+1)m", "bg(h+1)(l+1)m",
            "(a+1)(d+1)f(i+1)(m+1)", "(f+1)g(h+1)ko", "e(f+1)g(h+1)j", "(e+1)(i+1)(l+1)mo",
            "(a+1)b(f+1)(g+1)l", "d(i+1)j(k+1)m", "(c+1)(f+1)jl(o+1)", "ck(l+1)(m+1)n",
            "d(e+1)(f+1)jl", "(f+1)(h+1)(i+1)ko", "(a+1)(b+1)c(g+1)(i+1)", "(d+1)e(h+1)lm",
            "(b+1)(f+1)i(m+1)o", "(b+1)(f+1)(h+1)j(k+1)", "(a+1)(c+1)(d+1)(e+1)(h+1)",
            "a(e+1)(f+1)(h+1)(m+1)", "(f+1)(g+1)kmo", "ac(e+1)(k+1)(m+1)",
            "(b+1)(e+1)(i+1)m(n+1)", "(b+1)(d+1)(g+1)mn", "(b+1)c(e+1)(f+1)l",
            "(c+1)(d+1)f(h+1)(l+1)", "f(h+1)(k+1)lm", "(d+1)(f+1)(h+1)jo",
            "(f+1)g(h+1)(i+1)o", "(a+1)b(k+1)lm", "agi(k+1)o", "(a+1)(b+1)(c+1)(d+1)(n+1)",
            "c(e+1)(h+1)i(k+1)", "(b+1)(e+1)(i+1)(l+1)m", "(b+1)c(f+1)(k+1)o",
            "(a+1)(f+1)i(k+1)l", "c(e+1)(i+1)(k+1)m", "(a+1)cd(f+1)(h+1)", "cg(h+1)j(o+1)",
            "aij(l+1)n", "ac(e+1)(g+1)o", "(b+1)eijk", "cd(f+1)hj", "(e+1)(h+1)j(l+1)n",
            "e(f+1)(g+1)kn", "a(c+1)(f+1)(h+1)j", "a(c+1)(f+1)io", "ai(j+1)no", "af(h+1)ik",
            "bfimo", "c(i+1)(l+1)mn", "(b+1)(d+1)jlo", "ac(e+1)f(l+1)", "b(h+1)(k+1)mn",
            "cd(f+1)jn", "(a+1)(h+1)(j+1)lm", "(c+1)(d+1)f(j+1)o", "ac(e+1)(k+1)n",
            "a(c+1)ino", "(b+1)(f+1)jn(o+1)", "(d+1)(e+1)(h+1)(k+1)o"],
        ["(b+1)dg(i+1)(j+1)k(l+1)m"]]
    -- gens = [bpNot poly1]    -- 471 zeros; GrLexCmp, 807 gens, times vary:
            -- 786s cpu: generated (redundant) basis has 5917 elements with 1876000 monomials
            -- 3477s cpu: generated (redundant) basis has 6849 elements with 4039229 monomials
            -- note g0: abcdefghijklmno+... (10235 terms) - init gen is long high degree (15)
        -- with GrRevLexCmp, the generators seem to grow not shrink, so much slower
        -- LexCmp, 414 gens, 326s cpu,
            -- generated (redundant) basis has 4964 elements with 976490 monomials
    -- faster method, 471 zeros;
        -- LexCmp 414 gens, 66s cpu,
            -- generated (redundant) basis has 3724 elements with 248171 monomials
        -- GrLexCmp 807 gens, 365s cpu,
            -- generated (redundant) basis has 4026 elements with 462290 monomials
    -- receiver starts with 4080 zeros, GB LexCmp has 1270 gens, needs 413 new GB gens
    -}
    {- -}
    name            = "logic7"
    nVars           = 15
    initGenSsL      = [
        ["(b+1)(f+1)j", "(g+1)(k+1)(m+1)", "(a+1)cd(i+1)(m+1)(o+1)",
            "a(e+1)(j+1)k(l+1)(m+1)(n+1)", "b(c+1)(d+1)gh(m+1)", "(c+1)(k+1)(l+1)n",
            "ab(f+1)ln", "(b+1)(c+1)(g+1)ij(k+1)(n+1)(o+1)", "bg(n+1)",
            "(a+1)(b+1)c(i+1)(j+1)(k+1)l(n+1)", "(b+1)(k+1)lo", "(a+1)befi(k+1)(m+1)",
            "(c+1)df(h+1)i(k+1)(l+1)(o+1)", "c(f+1)g(m+1)", "(b+1)h(j+1)n", "ah(j+1)kn",
            "(b+1)(g+1)j(l+1)(m+1)(n+1)(o+1)", "acfh(i+1)(l+1)(n+1)", "cdgjl(o+1)",
            "(b+1)d(e+1)hl", "(d+1)(f+1)(h+1)kn", "c(e+1)(f+1)(h+1)(j+1)(m+1)",
            "a(e+1)fg(j+1)kl", "(a+1)em(n+1)", "(b+1)ceim(n+1)", "d(j+1)n",
            "c(e+1)(j+1)k(o+1)", "cef(g+1)(h+1)il(n+1)", "f(i+1)(o+1)",
            "bd(e+1)(g+1)(i+1)j(l+1)(o+1)", "(b+1)(d+1)(e+1)(f+1)ho", "ag(h+1)im(n+1)o",
            "(a+1)c(d+1)f(g+1)lo", "(d+1)(h+1)ik(l+1)", "(f+1)g(o+1)", "abe(h+1)ij",
            "e(g+1)(j+1)k(o+1)", "a(f+1)(j+1)(l+1)", "bcejkln(o+1)", "(j+1)lm",
            "g(h+1)(i+1)(o+1)", "(d+1)e(i+1)j(k+1)", "bce", "b(l+1)(o+1)", "(a+1)(d+1)fgjl",
            "bcef(g+1)(n+1)", "abl", "(b+1)de(g+1)", "(d+1)(f+1)(m+1)(n+1)", "ce(h+1)o",
            "(a+1)(c+1)(e+1)f(h+1)", "(b+1)cf(i+1)(j+1)l(m+1)", "ad(g+1)(k+1)n",
            "df(g+1)h(l+1)(n+1)o", "(c+1)(f+1)h(j+1)(l+1)(o+1)", "be(f+1)h(n+1)",
            "abch(i+1)(j+1)", "(a+1)fhil(o+1)", "ad(e+1)i(m+1)", "(d+1)(f+1)(h+1)(o+1)",
            "(a+1)ei", "(f+1)jln", "(a+1)(f+1)(i+1)", "ab(c+1)f(h+1)(l+1)m(n+1)", "(b+1)ko",
            "fh(m+1)", "(b+1)cd(e+1)(f+1)(g+1)(k+1)(m+1)", "(f+1)(g+1)(j+1)(l+1)o",
            "e(j+1)l", "(b+1)(c+1)hj(l+1)mo", "b(e+1)lm(n+1)", "bcdefh", "(e+1)k(o+1)",
            "(c+1)ik(n+1)o", "bdfg(h+1)i(l+1)(m+1)", "b(c+1)d(e+1)(i+1)lno", "(h+1)(i+1)l",
            "(a+1)(k+1)(l+1)(n+1)(o+1)", "b(e+1)jkn(o+1)", "abc(d+1)fh(j+1)m",
            "(a+1)d(e+1)i(m+1)o", "adef(h+1)(i+1)(k+1)(n+1)", "(e+1)i(k+1)l(o+1)",
            "(b+1)e(i+1)(k+1)(n+1)", "(f+1)hjkn(o+1)", "ab(e+1)(g+1)k(m+1)o", "c(f+1)l",
            "(a+1)e(g+1)h(k+1)l(n+1)", "(g+1)j(k+1)l", "(a+1)b(d+1)eg(h+1)l",
            "cf(g+1)l(m+1)", "bk(m+1)", "a(b+1)(d+1)ei(l+1)m", "(a+1)(b+1)ef(m+1)n",
            "(b+1)eg", "b(f+1)g(h+1)(i+1)lno", "d(f+1)(i+1)(j+1)(k+1)(n+1)o",
            "ace(l+1)(n+1)", "(d+1)(e+1)jn", "b(d+1)(e+1)ghm", "(a+1)gh(i+1)(m+1)(n+1)(o+1)",
            "(a+1)bde(g+1)", "(a+1)(c+1)(d+1)(i+1)(j+1)l(m+1)(o+1)", "df(h+1)(l+1)n",
            "(b+1)(c+1)de(i+1)(k+1)", "(b+1)c(d+1)(e+1)hi(m+1)(n+1)", "fikl(m+1)",
            "(a+1)bcde(f+1)gj", "(a+1)(b+1)de(i+1)(m+1)(n+1)", "ae(i+1)(j+1)l(o+1)",
            "bcde(h+1)(l+1)", "(a+1)(c+1)dfg(k+1)", "b(e+1)i(j+1)(k+1)(m+1)n(o+1)",
            "bc(e+1)(f+1)g(h+1)(j+1)", "(a+1)dg", "(a+1)bk", "af(h+1)i(k+1)n",
            "c(d+1)(e+1)ij(m+1)(o+1)", "b(g+1)n", "(a+1)c(l+1)(m+1)o", "(a+1)(e+1)(m+1)",
            "(i+1)(j+1)kl(m+1)o", "d(f+1)(k+1)m", "(b+1)def(g+1)i(m+1)(o+1)", "ghjm(n+1)o",
            "fi(j+1)(m+1)(o+1)", "acf(i+1)n(o+1)", "(c+1)(d+1)(e+1)fh(k+1)m(o+1)",
            "(g+1)(h+1)(m+1)", "(a+1)(b+1)dfh", "bdef(g+1)h(m+1)o", "(a+1)ch(i+1)klmn",
            "(a+1)(e+1)m(n+1)", "a(e+1)h", "agil", "ac(e+1)k(l+1)(m+1)", "dfgi(j+1)lmn",
            "ab(h+1)(i+1)n", "a(c+1)e(i+1)jmn(o+1)", "d(f+1)(j+1)(l+1)", "(a+1)bklo",
            "a(h+1)j(k+1)l(o+1)", "(e+1)h(i+1)(j+1)(l+1)(o+1)",
            "(d+1)(e+1)f(h+1)il(m+1)(n+1)", "d(e+1)(f+1)(g+1)mo", "b(f+1)(g+1)jkl(m+1)n",
            "(e+1)(g+1)(j+1)(o+1)", "(c+1)(d+1)(e+1)f(g+1)(o+1)", "(b+1)(d+1)fhj(n+1)(o+1)",
            "bcd(e+1)(l+1)(o+1)", "(a+1)(b+1)e(h+1)(k+1)", "abh(i+1)(l+1)(m+1)", "ac(m+1)",
            "(g+1)i(l+1)", "bc(d+1)(f+1)(j+1)k(n+1)", "(c+1)(f+1)(l+1)", "a(b+1)(k+1)l",
            "(d+1)f(h+1)(o+1)", "e(i+1)(j+1)kn", "a(b+1)(d+1)e(f+1)jk", "(a+1)cej",
            "a(d+1)e(h+1)o", "g(i+1)(j+1)(l+1)", "(b+1)(c+1)(f+1)(m+1)(n+1)", "cdfhi(o+1)",
            "b(c+1)dfkln(o+1)", "bfgh(k+1)lm(n+1)", "(a+1)de(f+1)(k+1)o", "a(b+1)c(e+1)gjl",
            "a(c+1)dg(h+1)(i+1)(m+1)n", "h(l+1)(n+1)", "(e+1)(f+1)(h+1)o",
            "(b+1)(c+1)ghilmn", "de(g+1)(h+1)n", "(b+1)(i+1)(m+1)", "a(b+1)(e+1)hn(o+1)",
            "dg(h+1)jk(l+1)mn", "(a+1)(b+1)(e+1)(k+1)(m+1)n", "(b+1)c(h+1)jl(m+1)(o+1)",
            "a(b+1)c(e+1)(n+1)o"],
        ["adeg(j+1)k(m+1)", "(a+1)(e+1)f(g+1)(l+1)(m+1)(o+1)", "def(h+1)(l+1)(m+1)",
            "a(d+1)(f+1)(i+1)j(l+1)(m+1)", "a(b+1)(h+1)(i+1)j(k+1)(m+1)(o+1)",
            "a(f+1)(h+1)(n+1)", "ace(g+1)(l+1)n", "(a+1)bdh(i+1)mn",
            "(a+1)b(c+1)(f+1)(g+1)i(m+1)(o+1)", "bh(i+1)j(m+1)(n+1)", "a(b+1)(e+1)fh(i+1)ln",
            "(a+1)c(d+1)(e+1)(f+1)lm(o+1)", "a(b+1)(c+1)h(i+1)(l+1)(o+1)",
            "ab(g+1)k(m+1)(n+1)o", "de(g+1)klmo", "(b+1)(d+1)(f+1)ijl(m+1)(o+1)",
            "(c+1)(d+1)(f+1)gik(m+1)", "(c+1)d(e+1)fg(m+1)n",
            "(a+1)(e+1)(f+1)(h+1)(i+1)(j+1)km", "(a+1)(b+1)(d+1)e(h+1)(i+1)kn",
            "b(d+1)(g+1)jk(m+1)", "ab(m+1)", "(b+1)cd(h+1)m(n+1)o", "(a+1)c(e+1)hjm(n+1)",
            "(c+1)(e+1)fl(n+1)", "e(h+1)(o+1)", "(i+1)(k+1)(m+1)", "k(n+1)(o+1)",
            "(e+1)(f+1)(i+1)", "(a+1)(c+1)d(e+1)(f+1)h", "abcj(l+1)n",
            "(b+1)(c+1)dh(i+1)j(l+1)o", "a(d+1)(e+1)fln", "bd(e+1)(h+1)i(m+1)o", "a(e+1)hk",
            "dh(l+1)n(o+1)", "de(i+1)k(l+1)m(n+1)(o+1)", "c(d+1)(f+1)(i+1)",
            "(a+1)(b+1)g(n+1)(o+1)", "(a+1)(b+1)dghi(k+1)n", "a(f+1)(g+1)i(k+1)",
            "b(d+1)(i+1)jn(o+1)", "b(f+1)(g+1)(k+1)(l+1)", "(e+1)(g+1)(h+1)(k+1)l",
            "a(c+1)(g+1)i(j+1)", "(b+1)cfg(i+1)(j+1)(k+1)o", "(a+1)(i+1)(j+1)(m+1)",
            "a(c+1)g(k+1)l", "d(f+1)(l+1)", "(e+1)(j+1)k(m+1)", "a(b+1)d(h+1)(i+1)kmo",
            "c(d+1)gj(k+1)l", "a(c+1)(i+1)jl", "(a+1)(c+1)de(h+1)(i+1)jl",
            "a(d+1)(f+1)hi(n+1)o", "(e+1)jk(o+1)", "(d+1)e(j+1)(k+1)m(n+1)",
            "bc(f+1)(h+1)ij(n+1)", "dghl(m+1)o", "(a+1)e(i+1)", "c(e+1)j(l+1)(m+1)n",
            "e(h+1)(n+1)(o+1)", "a(c+1)(d+1)(e+1)fhmo", "b(f+1)(l+1)n",
            "beg(h+1)(j+1)(l+1)(m+1)", "d(e+1)(m+1)", "de(f+1)(g+1)(h+1)jmo", "e(m+1)(o+1)",
            "(a+1)(b+1)(h+1)ikmn", "(b+1)(e+1)(f+1)(h+1)(l+1)mo", "b(c+1)efghkl",
            "bcfhj(l+1)(o+1)", "(c+1)df(i+1)(m+1)(n+1)", "(c+1)efil(m+1)",
            "(a+1)cj(l+1)(m+1)", "bcd(f+1)i(k+1)(m+1)(o+1)", "(a+1)(b+1)c(d+1)ej(o+1)",
            "(a+1)cdg", "(d+1)e(g+1)(h+1)jmo", "(a+1)d(e+1)fg(i+1)(l+1)",
            "(c+1)dfghj(k+1)(o+1)", "(a+1)(b+1)e", "(f+1)i(k+1)(o+1)", "(a+1)d(k+1)(l+1)m",
            "(a+1)(c+1)(f+1)hkl(n+1)(o+1)", "(b+1)(d+1)(e+1)hi(m+1)", "a(b+1)(d+1)(e+1)h",
            "(a+1)e(g+1)(h+1)(l+1)(n+1)", "(a+1)deg(i+1)k(l+1)o", "b(f+1)g(h+1)jm(o+1)",
            "(a+1)(b+1)e(f+1)j(l+1)", "(d+1)(k+1)ln", "a(b+1)(d+1)(h+1)(i+1)k(m+1)(o+1)",
            "eg(m+1)o", "(k+1)l(m+1)(o+1)", "(a+1)(b+1)de(f+1)(n+1)",
            "(b+1)(d+1)(e+1)(i+1)l(n+1)o", "cfgi(j+1)k", "bh(j+1)l", "(a+1)(b+1)(c+1)(j+1)",
            "a(b+1)(d+1)(f+1)(g+1)(h+1)ik", "(g+1)(i+1)kl(n+1)", "(b+1)f(g+1)l(m+1)o",
            "bc(d+1)g(i+1)m", "d(e+1)f(g+1)(k+1)(m+1)", "(a+1)(b+1)(c+1)i(k+1)l(m+1)o",
            "k(m+1)(o+1)", "c(f+1)gm(n+1)(o+1)", "(a+1)f(g+1)(h+1)(i+1)k(m+1)n",
            "(a+1)(c+1)(h+1)i(m+1)", "a(c+1)g(h+1)(i+1)kl(m+1)", "(c+1)h(j+1)(o+1)",
            "(a+1)d(h+1)ikmn(o+1)", "cdfgh(j+1)lo", "(a+1)(c+1)gi(j+1)(k+1)ln",
            "e(g+1)(h+1)(i+1)lmn", "df(g+1)(h+1)jk(o+1)", "(b+1)d(g+1)(i+1)jlmo",
            "bcdf(i+1)km(o+1)", "a(b+1)f(h+1)klm", "b(e+1)f(n+1)(o+1)",
            "(a+1)(b+1)efgh(n+1)(o+1)", "(f+1)(h+1)(i+1)jm", "(c+1)(d+1)(f+1)(g+1)jo",
            "(c+1)e(f+1)(g+1)(k+1)o", "bf(g+1)(h+1)i(l+1)n", "a(b+1)e(f+1)(i+1)",
            "df(j+1)(m+1)(o+1)", "(a+1)b(e+1)(f+1)(i+1)(l+1)", "(a+1)g(h+1)(i+1)(j+1)",
            "h(m+1)o", "acdef(k+1)m(n+1)", "(a+1)(c+1)m(n+1)", "(a+1)bdeho",
            "(a+1)(b+1)(e+1)gm(o+1)", "(c+1)dei(j+1)(n+1)o", "(a+1)(b+1)(c+1)(i+1)(n+1)",
            "bcdghi(l+1)", "ah(i+1)lm(o+1)", "(a+1)bjo", "(e+1)hk(m+1)(n+1)",
            "(a+1)(b+1)(c+1)dim(n+1)(o+1)", "(a+1)gh(j+1)(k+1)n(o+1)", "cdf(g+1)(j+1)(k+1)n",
            "(a+1)(d+1)f(h+1)(m+1)o", "(b+1)fg(h+1)ikmn", "e(g+1)(j+1)o", "bcfgh(j+1)(k+1)",
            "bd(f+1)(i+1)j(k+1)mn", "c(d+1)(f+1)(h+1)(j+1)(m+1)(n+1)", "(f+1)jn",
            "(a+1)c(d+1)(f+1)kl(m+1)", "ae(h+1)(n+1)(o+1)", "ac(e+1)(f+1)(n+1)",
            "(d+1)(f+1)(i+1)(n+1)", "(a+1)(b+1)deh(k+1)(n+1)o", "cg(i+1)klo", "(g+1)l(n+1)o",
            "be(f+1)(g+1)(h+1)i(j+1)m", "bchln(o+1)"],
        ["b(e+1)(f+1)(g+1)hik(l+1)"]]
    


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
