{-# LANGUAGE Strict #-}

{- |  Groebner Basis demo examples  -}

module Math.Algebra.Commutative.GBDemo (
    gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails,
    (.|.),
    gbDemo,
    simpleDemo, buchberger87, gerdt93, katsura5, katsura6, katsura7, katsura8, katsura10,
    hCyclic4, cyclic4, hCyclic5, cyclic5, hCyclic6, cyclic6, hCyclic7, cyclic7,
    hCyclic8, cyclic8, schransTroost, jason210, cyclic8big
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.EPoly
import Math.Algebra.Commutative.Field.ZModP32


-- See http://www.math.usm.edu/perry/Research/f5ex.lib as in
-- https://arxiv.org/pdf/0906.2967.pdf

gbDemo          :: String -> Integer -> [String] -> [String] -> Int -> Int -> IO ()
{- ^ @gbDemo name p varSs genSs nCores gbTrace@: @p@ is a prime that fits in a word, and @varSs@
    have precedence > '^' -}
gbDemo name p varSs genSs nCores gbTrace    = case someNatVal (fromInteger p) of
 SomeNat (Proxy :: Proxy p)     -> do
    putStr $ name ++ " "
    let _gbi    = fromGens gens
    putChar '\n'
  where
    (cField, cBalRep)   = zzModPW @p
    gbpA        = epGBPOps gRevLex True cField varSs (const (show . cBalRep)) True
    nVars       = length varSs
    epru        = withRing cField epRingUniv nVars gRevLex
    UnivL epRing (RingTgtXs _cToEp varEps) _epUnivF     = epru
    SubmoduleOps { .. }     = gbiSmOps gbpA nCores gbTrace
    gens        = map ((\ [(x,"")] -> x) . polynomReads epRing (zip varSs varEps)) genSs

simpleDemo, buchberger87, gerdt93, katsura5, katsura6, katsura7, katsura8, katsura10,
    hCyclic4, cyclic4, hCyclic5, cyclic5, hCyclic6, cyclic6, hCyclic7, cyclic7,
    hCyclic8, cyclic8, schransTroost, jason210, cyclic8big
                :: Int -> Int -> IO ()

simpleDemo      =
    gbDemo "simpleDemo" 7583 ["x", "y", "z", "t"]
        ["yz^3 - x^2t^2", "xz^2 - y^2t", "x^2y - z^2t"]
{-
in paper, over Q:
[x*z^2 - y^2*t,
x^2*y - z^2*t,
y*z^3 - x^2*t^2,
y^3*z*t - x^3*t^2,
x*y^3*t - z^4*t,
z^5*t - x^4*t^2,
y^5*t^2 - x^4*z*t^2,
x^5*t^2 - z^2*t^5] (z^2*t^5 ≡ y^2z^3t^2)
-}

buchberger87    =
    gbDemo "buchberger87" 7583 ["h", "r", "t", "x", "y", "z"]
        ["hx - rt", "hz - r^2", "h^2y - rt^2"]

gerdt93         =
    gbDemo "gerdt93" 7583 ["h", "l", "s", "x", "y", "z"]
        ["hl - l^2 - 4ls + hy", "h^2s - 6ls^2 + h^2z", "xh^2 - l^2s - h^3"]

katsura5        =
    gbDemo "katsura5" 7583 ["x", "y", "z", "t", "u", "v", "h"]
        [
            "2x^2 + 2y^2 + 2z^2 + 2t^2 + 2u^2 + v^2 - vh",
            "xy + yz + 2zt + 2tu + 2uv + uh",
            "2xz + 2yt + 2zu + u^2 + 2tv - th",
            "2xt + 2yu + 2tu + 2zv - zh",
            "t^2 + 2xv + 2yv + 2zv - yh",
            "2x + 2y + 2z + 2t + 2u + v - h"
        ]

katsura6        =
    gbDemo "katsura6" 7583 ["a", "b", "c", "d", "e", "f", "g", "h"]
        [
            "a + 2b + 2c + 2d + 2e + 2f + 2g - h",
            "2cd + 2be + 2af + 2bg - fh",
            "c^2 + 2bd + 2ae + 2bf + 2cg - eh",
            "2bc + 2ad + 2be + 2cf + 2dg - dh",
            "b^2 + 2ac + 2bd + 2ce + 2df + 2eg - ch",
            "2ab + 2bc + 2cd + 2de + 2ef + 2fg - bh",
            "a^2 + 2b^2 + 2c^2 + 2d^2 + 2e^2 + 2f^2 + 2g^2 - ah"
        ]

katsura7        =
    gbDemo "katsura7" 7583 ["a", "b", "c", "d", "e", "f", "g", "h", "t"]
        [
            "a^2 + 2b^2 + 2c^2 + 2d^2 + 2e^2 + 2f^2 + 2g^2 + 2h^2 - at",
            "2ab + 2bc + 2cd + 2de + 2ef + 2fg + 2gh - bt",
            "b^2 + 2ac + 2bd + 2ce + 2df + 2eg + 2fh - ct",
            "2bc + 2ad + 2be + 2cf + 2dg + 2eh - dt",
            "c^2 + 2bd + 2ae + 2bf + 2cg + 2dh - et",
            "2cd + 2be + 2af + 2bg + 2ch -ft",
            "d^2 + 2ce + 2bf + 2ag + 2bh - gt",
            "a + 2b + 2c + 2d + 2e + 2f + 2g + 2h - t"
        ]

katsura8        =
    gbDemo "katsura8" 7583 ["a", "b", "c", "d", "e", "f", "g", "h", "i", "t"]
        [
            "a^2 + 2b^2 + 2c^2 + 2d^2 + 2e^2 + 2f^2 + 2g^2 + 2h^2 + 2i^2 - at",
            "2ab + 2bc + 2cd + 2de + 2ef + 2fg + 2gh + 2hi- bt",
            "b^2 + 2ac + 2bd + 2ce + 2df + 2eg + 2fh + 2gi - ct",
            "2bc + 2ad + 2be + 2cf + 2dg + 2eh + 2fi - dt",
            "c^2 + 2bd + 2ae + 2bf + 2cg + 2dh + 2ei - et",
            "2cd + 2be + 2af + 2bg + 2ch + 2di -ft",
            "d^2 + 2ce + 2bf + 2ag + 2bh + 2ci - gt",
            "2de + 2cf + 2bg + 2ah + 2bi - ht",
            "a + 2b + 2c + 2d + 2e + 2f + 2g + 2h + 2i - t"
        ]

katsura10       =
    gbDemo "katsura10" 101 ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
        [
            "a+2b+2c+2d+2e +2f+2g+2h+2i+2j-1",
            "f^2+2eg-33fg-2g^2+2dh-33eh-4fh-12gh+22h^2+2ci-33di-4ei-12fi+44gi-38hi-28i^2+2bj-33cj-4dj-12ej+44fj-38gj+45hj-10ij+50j^2-16b+37c-43d+47e +4f+30g+24h-14i+17j",
            "ef+dg-33fg-49g^2+ch-33eh+3fh+7gh+40h^2+bi-33di+3ei+7fi-21gi+20hi-36i^2-2bj-35cj+dj+5ej-23fj+18gj+27hj+4ij+24j^2+8b+32c-29d+27e -2f-15g-12h+7i-8j",
            "e^2+2df+2cg+2bh-4bi-4ci-4di-4ei-4fi-4gi-4hi-4i^2+2bj-4ij+i",
            "de+cf+bg-2bh-2ch-2dh-2eh-2fh-2gh-2h^2+bi-2hi+cj-2hj-50h",
            "d^2+2ce+2bf-4bg-4cg-4dg-4eg-4fg-4g^2+2bh-4gh+2ci-4gi+2dj-4gj+g",
            "cd+be-2bf-2cf-2df+bg+2dg+4eg-33fg-g^2+3ch+4dh-31eh-4fh-10gh+23h^2+2bi+4ci-30di-2ei-12fi+46gi-36hi-27i^2-35cj-6dj-13ej+40fj-40gj+43hj-12ij+47j^2-16b+37c-43d+47e -46f+30g+24h-14i+18j",
            "c^2+2bd-4be-4ce+2bf+4cf+8df+4bg+10cg+4dg-4eg-31fg+6g^2-4ch-6dh-43eh+4fh+20gh-50h^2-8bi-16ci-47di-6ei+12fi+gi-45hi+42i^2-35cj+4dj+16ej+11fj-29gj-hj-5j^2+32b+27c-15d+8e -8f+41g-46h+32i-32j",
            "bc-2bd+3be+4ce-cf-6df-4bg-8cg-5dg+27fg-10g^2+2ch+2dh+36eh-12fh-32gh+42h^2+6bi+12ci+39di-4ei-23fi-17gi+25hi+47i^2+33cj-10dj-26ej-21fj+14gj-19hj-24ij-7j^2-32b-27c-35d-7e +9f-39g+49h-28i+36j",
            "b^2+2bd-2ce+2df+4bg+4cg+4dg+2eg-47fg-20g^2+50eh-46fh+13gh-41h^2-4ci+50di-48ei+9fi+21gi-22hi+46i^2+50cj-48dj+9ej+19fj-18gj-7hj-43ij+39j^2+37b+48c+32d-10e +22f+27g+7h-40i-13j"
        ]

hCyclic4        =
    gbDemo "hCyclic4" 7583 ["a", "b", "c", "d", "e"]
        [
            "a+b+c+d",
            "ab+bc+cd+da",
            "abc+bcd+cda+dab",
            "abcd-e^4"
        ]

cyclic4       =
    gbDemo "cyclic4" 7583 ["a", "b", "c", "d"]
        [
            "a+b+c+d",
            "ab+bc+cd+da",
            "abc+bcd+cda+dab",
            "abcd-1"
        ]

hCyclic5        =
    gbDemo "hCyclic5" 7583 ["a", "b", "c", "d", "e", "f"]
        [
            "a+b+c+d+e",
            "ab+bc+cd+de+ea",
            "abc+bcd+cde+dea+eab",
            "abcd+bcde+cdea+deab+eabc",
            "abcde-f^5"
        ]

cyclic5       =
    gbDemo "cyclic5" 7583 ["a", "b", "c", "d", "e"]
        [
            "a+b+c+d+e",
            "ab+bc+cd+de+ea",
            "abc+bcd+cde+dea+eab",
            "abcd+bcde+cdea+deab+eabc",
            "abcde-1"
        ]

hCyclic6        =
    gbDemo "hCyclic6" 7583 ["a", "b", "c", "d", "e", "f", "g"]
        [
            "a+b+c+d+e+f",
            "ab+bc+cd+de+ef+fa",
            "abc+bcd+cde+def+efa+fab",
            "abcd+bcde+cdef+defa+efab+fabc",
            "abcde+bcdef+cdefa+defab+efabc+fabcd",
            "abcdef-g^6"
        ]

cyclic6       =
    gbDemo "cyclic6" 7583 ["a", "b", "c", "d", "e", "f"]
        [
            "a+b+c+d+e+f",
            "ab+bc+cd+de+ef+fa",
            "abc+bcd+cde+def+efa+fab",
            "abcd+bcde+cdef+defa+efab+fabc",
            "abcde+bcdef+cdefa+defab+efabc+fabcd",
            "abcdef-1"
        ]

hCyclic7        =
    gbDemo "hCyclic7" 7583 ["a", "b", "c", "d", "e", "f", "g", "h"]
        [
            "a+b+c+d+e+f+g",
            "ab+bc+cd+de+ef+ag+fg",
            "abc+bcd+cde+def+abg+afg+efg",
            "abcd+bcde+cdef+abcg+abfg+aefg+defg",
            "abcde+bcdef+abcdg+abcfg+abefg+adefg+cdefg",
            "abcdef+abcdeg+abcdfg+abcefg+abdefg+acdefg+bcdefg",
            "abcdefg-h^7"
        ]

cyclic7       =
    gbDemo "cyclic7" 7583 ["a", "b", "c", "d", "e", "f", "g"]
        [
            "a+b+c+d+e+f+g",
            "ab+bc+cd+de+ef+ag+fg",
            "abc+bcd+cde+def+abg+afg+efg",
            "abcd+bcde+cdef+abcg+abfg+aefg+defg",
            "abcde+bcdef+abcdg+abcfg+abefg+adefg+cdefg",
            "abcdef+abcdeg+abcdfg+abcefg+abdefg+acdefg+bcdefg",
            "abcdefg-1"
        ]

hCyclic8        =
    gbDemo "hCyclic8" 7583 ["a", "b", "c", "d", "e", "f", "g", "h", "i"]
        [
            "a+b+c+d+e+f+g+h",
            "ab+bc+cd+de+ef+fg+gh+ha",
            "abc+bcd+cde+def+efg+fgh+gha+hab",
            "abcd+bcde+cdef+defg+efgh+fgha+ghab+habc",
            "abcde+bcdef+cdefg+defgh+efgha+fghab+ghabc+habcd",
            "abcdef+bcdefg+cdefgh+defgha+efghab+fghabc+ghabcd+habcde",
            "abcdefg+bcdefgh+cdefgha+defghab+efghabc+fghabcd+ghabcde+habcdef",
            "abcdefgh-i^8"
        ]

cyclic8         =
    gbDemo "cyclic8" 7583 ["a", "b", "c", "d", "e", "f", "g", "h"]
        [
            "a+b+c+d+e+f+g+h",
            "ab+bc+cd+de+ef+fg+gh+ha",
            "abc+bcd+cde+def+efg+fgh+gha+hab",
            "abcd+bcde+cdef+defg+efgh+fgha+ghab+habc",
            "abcde+bcdef+cdefg+defgh+efgha+fghab+ghabc+habcd",
            "abcdef+bcdefg+cdefgh+defgha+efghab+fghabc+ghabcd+habcde",
            "abcdefg+bcdefgh+cdefgha+defghab+efghabc+fghabcd+ghabcde+habcdef",
            "abcdefgh-1"
        ]

{- cyclic_n(int n)    // try 7, then later 8
{
   ring R = 7583,(x(1..(n)),h),dp;
   int l, j, k;
   ideal i, base_set;
   poly facs, addem;

   i = 0;
   for (int ctr = 1; ctr <= n; ctr++) {
       base_set[ctr] = x(ctr);
   }
   for (l = 1; l < n; l++) {
       addem = 0;
       for (j = 1; j <= n; j++) {
           facs = 1;
           for (k = j; k <= l + j - 1; k++) {
               if (k <= n) {
                   facs = facs * x(k);
               } else {
                   facs = facs * x(k - n);
               }
           }
           addem = addem + facs;
       }
       /* l[i] = addem; */
       i = i + addem;
   }
   facs = 1;
   for (l= 1; l<= n; l++) {
       facs = facs * x(l);
   }
   /* l[n] = facs - 1; */
   i = i + (facs - h^n); -}

schransTroost   =
    gbDemo "schransTroost" 7583 ["a", "b", "c", "d", "e", "f", "g", "h", "t"]
        [
            "8a^2 + 8ab + 8ac - 8bc + 2ad + 2ae + 2af - 2ef + 2ag - 2dg - at",
            "8ab + 8b^2 - 8ac + 8bc + 2bd + 2be + 2bf - 2df + 2bg - 2eg - bt",
            "-8ab + 8ac + 8bc + 8c^2 + 2cd + 2ce - 2de + 2cf + 2cg - 2fg - ct",
            "2ad 2bd + 2cd + 8d^2 - 2ce + 8de - 2bf + 2df - 2ag + 2dg + 6dh - 6eh - dt",
            "-2ad - 2be - 2cf + 2ag + 2bg + 2cg + 2dg + 2eg + 8fg + 8g^2 - 6fh + 6gh - gt",
            "-2bd - 2ae + 2af + 2bf + 2cf + 2df + 2ef + 8f^2 - 2cg + 8fg + 6fh - 6gh - ft",
            "-2cd + 2ae + 2be + 2ce + 8de + 8e^2 - 2af + 2ef - 2bg + 2eg - 6dh + 6eh - et",
            "-6de - 6fg + 6dh + 6eh + 6fh + 6gh + 8h^2 - ht"
        ]

jason210        =
    gbDemo "jason210" 32003 ["a", "b", "c", "d", "e", "f", "g", "h"]
        [
            "a^2c^4+b^2d^4+abc^2e^2+abd^2f^2+abcdeg+abcdfh",
            "b^6",
            "a^6"
        ]

cyclic8big      =
    gbDemo "cyclic8big" 7583 ["a", "b", "c", "d", "e", "f", "g", "h"]
        [
            "a+b+c+d+e+f+g+h",
            "b^2+bd-cd+be-de+bf-ef+bg-fg+2bh+ch+dh+eh+fh+h^2",
            "bc^2-bcd+c^2d+cef-def+cfg-efg-c^2h-ceh+deh-cfh+efh+bgh+cgh+dgh+egh+fgh+g^2h-bh^2-2ch^2-dh^2-eh^2-fh^2+gh^2-h^3",
            "bcd^2-bcde+cd^2e-cdef+d^2ef-cd^2h+cdeh-d^2eh+bcgh-bdgh-d^2gh+bfgh+cfgh+2efgh+f^2gh-dg^2h+2fg^2h-bch^2+bdh^2+d^2h^2+dfh^2-efh^2-2bgh^2-2cgh^2-3dgh^2-2egh^2-fgh^2-g^2h^2+bh^3+ch^3+2dh^3+eh^3+fh^3-2gh^3+h^4",
            "bcde^2-bcdef+cde^2f-cdefg+de^2fg-cde^2h+cdefh-de^2fh+bcdgh-bcegh-de^2gh+bcfgh+cdfgh+2defgh-e^2fgh+ef^2gh+f^2g^2h-bcdh^2+bceh^2+de^2h^2-defh^2+e^2fh^2-2bcgh^2-2cdgh^2+2begh^2+2cegh^2+2e^2gh^2-2bfgh^2-2cfgh^2-2dfgh^2-2efgh^2-2f^2gh^2-bg^2h^2-cg^2h^2-dg^2h^2-3fg^2h^2-g^3h^2+bch^3+cdh^3-beh^3-ceh^3-e^2h^3+3bgh^3+3cgh^3+3dgh^3+5egh^3+fgh^3-bh^4-ch^4-dh^4-2eh^4-fh^4+3gh^4-h^5",
            "bcdef^2-bcdefg+cdef^2g-cdef^2h+bcdegh+bcefgh+bdefgh+3cdefgh+d^2efgh+2de^2fgh-bcf^2gh-cdf^2gh-bef^2gh-cef^2gh-def^2gh-2ef^3gh+2defg^2h-f^3g^2h-bcdeh^2+bcdfh^2+def^2h^2-2bcdgh^2-2cdegh^2-2befgh^2-2cefgh^2-3defgh^2-2e^2fgh^2+2bf^2gh^2+2cf^2gh^2+2df^2gh^2-ef^2gh^2+2f^3gh^2-bcg^2h^2-cdg^2h^2-deg^2h^2-bfg^2h^2-cfg^2h^2-dfg^2h^2-4efg^2h^2-2fg^3h^2+bcdh^3+cdeh^3-bcfh^3-cdfh^3-ef^2h^3+3bcgh^3+3cdgh^3+3degh^3+efgh^3+2f^2gh^3+3bg^2h^3+3cg^2h^3+3dg^2h^3+3eg^2h^3+3fg^2h^3+2g^3h^3-bch^4-cdh^4-deh^4+bfh^4+cfh^4+dfh^4+f^2h^4-4bgh^4-4cgh^4-4dgh^4-4egh^4-4fgh^4+2g^2h^4+bh^5+ch^5+dh^5+eh^5+2fh^5-4gh^5+h^6",
            "bcdefg^2+4bcdefgh+c^2defgh+2cd^2efgh+2cde^2fgh+d^2e^2fgh+2cdef^2gh+2de^2f^2gh-bcdeg^2h-bcdfg^2h-bcefg^2h-bdefg^2h-2cdefg^2h-d^2efg^2h-2de^2fg^2h-2defg^3h-2ef^2g^3h-bcdefh^2-bcdegh^2-2bcdfgh^2-2bcefgh^2-2bdefgh^2-6cdefgh^2-2d^2efgh^2-4de^2fgh^2-4def^2gh^2-2e^2f^2gh^2+bcdg^2h^2+cdeg^2h^2-2defg^2h^2-bf^2g^2h^2-cf^2g^2h^2-df^2g^2h^2-3ef^2g^2h^2-f^3g^2h^2+bcg^3h^2+cdg^3h^2+deg^3h^2+2bfg^3h^2+2cfg^3h^2+2dfg^3h^2+2efg^3h^2+3fg^4h^2+bcdeh^3+cdefh^3+2bcdgh^3+2cdegh^3+3bcfgh^3+3cdfgh^3+3befgh^3+3cefgh^3+6defgh^3+3e^2fgh^3+6ef^2gh^3+3bfg^2h^3+3cfg^2h^3+3dfg^2h^3+5efg^2h^3+3f^2g^2h^3-2bg^3h^3-2cg^3h^3-2dg^3h^3-2eg^3h^3+4fg^3h^3-g^4h^3-bcdh^4-cdeh^4-defh^4-3bcgh^4-3cdgh^4-3degh^4-4bfgh^4-4cfgh^4-4dfgh^4-4efgh^4-4f^2gh^4-2bg^2h^4-2cg^2h^4-2dg^2h^4-2eg^2h^4-fg^2h^4-4g^3h^4+bch^5+cdh^5+deh^5+efh^5+4bgh^5+4cgh^5+4dgh^5+4egh^5-g^2h^5-bh^6-ch^6-dh^6-eh^6-fh^6+4gh^6-h^7",
            "bcdefgh^2-3033c^2defgh^2+1517cd^2efgh^2+1517cde^2fgh^2-3033d^2e^2fgh^2+1517cdef^2gh^2+1517de^2f^2gh^2+1517cdefg^2h^2+1517def^2g^2h^2-3033e^2f^2g^2h^2+3033bcdefh^3-1517bcdegh^3-1517bcdfgh^3-1517bcefgh^3-1517bdefgh^3-1518cdefgh^3-1517d^2efgh^3-3034de^2fgh^3-3034def^2gh^3-1517e^2f^2gh^3+3033bcdg^2h^3+3033cdeg^2h^3-1517bcfg^2h^3-1517cdfg^2h^3-1517befg^2h^3-1517cefg^2h^3-1518defg^2h^3-1517e^2fg^2h^3+3033bf^2g^2h^3+3033cf^2g^2h^3+3033df^2g^2h^3-1518ef^2g^2h^3+3033f^3g^2h^3+1516efg^3h^3+1516f^2g^3h^3-3033bcdeh^4-3033cdefh^4-1516bcdgh^4-1516cdegh^4-1516bcfgh^4-1516cdfgh^4-1516befgh^4-1516cefgh^4+1518defgh^4-1516e^2fgh^4-3032ef^2gh^4-1516bcg^2h^4-1516cdg^2h^4-1516deg^2h^4-3032bfg^2h^4-3032cfg^2h^4-3032dfg^2h^4+3035efg^2h^4-3032f^2g^2h^4-3033bg^3h^4-3033cg^3h^4-3033dg^3h^4-3033eg^3h^4+1518fg^3h^4-3033g^4h^4+3033bcdh^5+3033cdeh^5+3033defh^5-3034bcgh^5-3034cdgh^5-3034degh^5-3034bfgh^5-3034cfgh^5-3034dfgh^5-efgh^5-3034f^2gh^5+3032bg^2h^5+3032cg^2h^5+3032dg^2h^5+3032eg^2h^5-1517fg^2h^5-1517g^3h^5-3033bch^6-3033cdh^6-3033deh^6-3033efh^6+bgh^6+cgh^6+dgh^6+egh^6-3033fgh^6-g^2h^6+3033bh^7+3033ch^7+3033dh^7+3033eh^7+3033fh^7+gh^7+3033h^8+3033"
        ]
