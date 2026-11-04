module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ZeroSectionFormulaHolds

/-!
# The class of a subbundle, in constant rank

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules, with `𝒩'`
of constant rank `r'` and `ℰ` of constant rank `e` (so `𝒩` has rank `r' + e`). With
`N' = Spec_X(Sym((𝒩')^∨))`, `N = Spec_X(Sym(𝒩^∨))`, the closed embedding `i : N' ⟶ N` and the
projections `p'`, `p`, for every `α ∈ A_k(X)`

  `i_*(p')^*α = p^*(c_e(ℰ) ∩ α)`  in  `A_{k+r'}(N)`.

This is Stacks 0FAA when `ℰ` has constant rank, the top Chern class `c_top(ℰ)` being `c_e(ℰ)`. It
follows from the zero section formula for `ℰ` (`Stacks.Chow.zeroSectionFormula`) by
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_of_zeroSectionFormula`.

## Main results

* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_chernCap` — the formula, as a
  heterogeneous equality between the two degrees `k + r'` and `(k - e) + (r' + e)`.
* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_chernCap'` — the same equality in
  `A_{k+r'}(N)`, after transport along `(k - e) + (r' + e) = k + r'`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules) (r' e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [hN' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] in
include hseq in
/-- The middle term of the sequence has rank `r' + e`. -/
theorem isFiniteLocallyFreeOfRank_middle :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (r' + e) :=
  GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact (ShortComplex.mk inc pr w) hseq r' e hN' hE

/-- **Stacks 0FAA in constant rank**, as a heterogeneous equality: `i_*(p')^*α = p^*(c_e(ℰ) ∩ α)`,
the two sides lying in `A_{k+r'}(N)` and `A_{(k-e)+(r'+e)}(N)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_eq_chernCap (k : ℤ) (α : chowGroup C sX k) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
    haveI := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + r')
        (dualBundlePullback C sX N' r' k α) ≍
      dualBundlePullback C sX N (r' + e) (k - e)
        (GenuineChern.chernCap C e sX E k (Fin.last e) α) :=
  have := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
  subbundleEmbedding_pushforward_flatPullback_of_zeroSectionFormula C sX N' N E r' e inc pr w hseq
    (zeroSectionFormula C e sX E) k α

/-- **Stacks 0FAA in constant rank**: `i_*(p')^*α = p^*(c_e(ℰ) ∩ α)` in `A_{k+r'}(N)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_eq_chernCap' (k : ℤ)
    (α : chowGroup C sX k) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
    haveI := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + r')
        (dualBundlePullback C sX N' r' k α) =
      chowGroupCast C (dualVectorBundleToBase N ≫ sX)
        (show k - (e : ℤ) + ((r' + e : ℕ) : ℤ) = k + r' by push_cast; ring)
        (dualBundlePullback C sX N (r' + e) (k - e)
          (GenuineChern.chernCap C e sX E k (Fin.last e) α)) :=
  eq_of_heq ((subbundleEmbedding_pushforward_flatPullback_eq_chernCap C sX N' N E r' e inc pr w
    hseq k α).trans (chowGroupCast_heq C _ _ _).symm)

end Stacks.Chow

end
