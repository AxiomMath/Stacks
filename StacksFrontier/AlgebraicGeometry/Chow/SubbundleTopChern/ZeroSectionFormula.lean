module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.RankOne
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula

/-!
# The zero section of a vector bundle and the top Chern class

Let `ℰ` be a finite locally free `𝒪_X`-module of rank `e`, `E = 𝐕(ℰ^∨) = Spec_X(Sym(ℰ^∨))` its
vector bundle with projection `p : E ⟶ X` and zero section `o : X ⟶ E`. The **zero section
formula** for `ℰ` is

  `o_* α = p^*(c_e(ℰ) ∩ α)`  in  `A_k(E)`  for  `α ∈ A_k(X)`,

the case `𝒩' = 0`, `𝒩 = ℰ` of Stacks 0FAA. This file shows that it implies Stacks 0FAA for every
short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`: `N'` is the fibre of `q : N ⟶ E` over the zero
section, `q` is flat, so Stacks 02RG gives `i_*(p')^*α = q^* o_* α`, and `q ≫ p = p_N`. It also
proves the formula in rank zero, where `p` is an isomorphism and `c_0 = 1`.

## Main definitions

* `Stacks.Chow.dualVectorBundleZeroSection` — the zero section `o : X ⟶ 𝐕(ℰ^∨)`.
* `Stacks.Chow.ZeroSectionFormula` — the zero section formula for `ℰ`.

## Main results

* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_of_zeroSectionFormula` — Stacks 0FAA
  from the zero section formula for the quotient.
* `Stacks.Chow.zeroSectionFormula_of_rank_zero`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The zero section `o : X ⟶ 𝐕(ℰ^∨)`.** -/
def dualVectorBundleZeroSection (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    X ⟶ dualVectorBundle E :=
  (vectorBundleOverZeroSection (dualSheaf E)).left

/-- The zero section `o` is a section of the projection `p : 𝐕(ℰ^∨) ⟶ X`: `o ≫ p = 𝟙 X`. -/
@[reassoc]
theorem dualVectorBundleZeroSection_comp (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    dualVectorBundleZeroSection E ≫ dualVectorBundleToBase E = 𝟙 X :=
  vectorBundleOverZeroSection_left_comp _

/-- The zero section `o : X ⟶ 𝐕(ℰ^∨)` is a closed immersion. -/
instance isClosedImmersion_dualVectorBundleZeroSection (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsClosedImmersion (dualVectorBundleZeroSection E) := by
  have := isAffineHom_vectorBundleToBase X (dualSheaf E)
  have : IsSeparated (vectorBundleToBase X (dualSheaf E)) := IsSeparated.of_isAffineHom _
  exact Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section
    (vectorBundleToBase X (dualSheaf E)) _ (vectorBundleOverZeroSection_left_comp _)

omit [LocallyOfFiniteType sX] in
/-- The zero section `o` commutes with the structure morphisms to `S`: `o ≫ p ≫ s_X = s_X`. -/
theorem dualVectorBundleZeroSection_comp_base (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    dualVectorBundleZeroSection E ≫ dualVectorBundleToBase E ≫ sX = sX := by
  rw [dualVectorBundleZeroSection_comp_assoc]

/-- **The pushforward `o_* : A_k(X) ⟶ A_k(𝐕(ℰ^∨))` along the zero section.** -/
def dualZeroSectionPushforward (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (k : ℤ) :
    chowGroup C sX k →+ chowGroup C (dualVectorBundleToBase E ≫ sX) k :=
  properChowPushforward C sX _ (dualVectorBundleZeroSection E)
    (dualVectorBundleZeroSection_comp_base C sX E) k (properPushforwardDescends C _ _ _ _ _)

/-- **The zero section formula for `ℰ`**: `o_* α = p^*(c_e(ℰ) ∩ α)` for every `α ∈ A_k(X)`, the
two sides lying in the degrees `k` and `(k - e) + e`. -/
def ZeroSectionFormula (E : X.Modules) (e : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e] : Prop :=
  ∀ (k : ℤ) (α : chowGroup C sX k),
    dualZeroSectionPushforward C sX E k α ≍
      dualBundlePullback C sX E e (k - e) (GenuineChern.chernCap C e sX E k (Fin.last e) α)

section FromZeroSection

variable (K N E : X.Modules) (m e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} K]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [hKm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} K m]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (m + e)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (inc : K ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- **The morphism `q : N ⟶ E = 𝐕(ℰ^∨)`** of vector bundles induced by `ℰ^∨ ⟶ 𝒩^∨`. -/
def dualQuotientMap : dualVectorBundle N ⟶ dualVectorBundle E :=
  (vectorBundleMap X (dualMap pr)).left

/-- The morphism `q : N ⟶ E` lies over `X`: `q ≫ p_E = p_N`. -/
theorem dualQuotientMap_comp : dualQuotientMap N E pr ≫ dualVectorBundleToBase E =
    dualVectorBundleToBase N :=
  vectorBundleMap_left_comp X (dualMap pr)

include hseq hKm in
/-- The morphism `q : N ⟶ E` is locally of finite type. -/
theorem locallyOfFiniteType_dualQuotientMap : LocallyOfFiniteType (dualQuotientMap N E pr) :=
  locallyOfFiniteType_vectorBundleMap_dualMap K N E inc pr w hseq m

include hseq hKm in
/-- The morphism `q : N ⟶ E` is flat. -/
theorem flat_dualQuotientMap : Flat (dualQuotientMap N E pr) :=
  flat_vectorBundleMap_dualMap K N E inc pr w hseq m

include hseq hKm in
/-- The morphism `q : N ⟶ E` has relative dimension `m`, the rank of `𝒦`. -/
theorem relativeDimension_dualQuotientMap :
    haveI := locallyOfFiniteType_dualQuotientMap K N E m inc pr w hseq
    AlgebraicGeometry.RelativeDimension (dualQuotientMap N E pr) m :=
  relativeDimension_vectorBundleMap_dualMap K N E inc pr w hseq m

include hseq in
/-- The subbundle `K = 𝐕(𝒦^∨)` is the fibre of `q : N ⟶ E` over the zero section of `E`: the
square formed by `p_K`, the embedding `K ⟶ N`, the zero section `o` and `q` is cartesian. -/
theorem isPullback_dualQuotientMap :
    IsPullback (dualVectorBundleToBase K) (subbundleEmbedding K N inc)
      (dualVectorBundleZeroSection E) (dualQuotientMap N E pr) :=
  (isPullback_subbundleEmbedding K N E inc pr w hseq).flip

/-- **Stacks 0FAA from the zero section formula for the quotient.** For
`0 ⟶ 𝒦 ⟶ 𝒩 ⟶ ℰ ⟶ 0` short exact with `𝒦` of rank `m` and `ℰ` of rank `e`, if
`o_* β = p_E^*(c_e(ℰ) ∩ β)` for the zero section `o` of `E = 𝐕(ℰ^∨)`, then
`i_*(p')^*α = p^*(c_e(ℰ) ∩ α)` in `A_{k+m}(N)` for every `α ∈ A_k(X)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_of_zeroSectionFormula
    (hZ : ZeroSectionFormula C sX E e) (k : ℤ) (α : chowGroup C sX k) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact K N E inc pr w hseq
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase K ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding K N inc)
        (subbundleEmbedding_comp_base K N sX inc) (k + m)
        (dualBundlePullback C sX K m k α) ≍
      dualBundlePullback C sX N (m + e) (k - e)
        (GenuineChern.chernCap C e sX E k (Fin.last e) α) := by
  have := isClosedImmersion_subbundleEmbedding_of_shortExact K N E inc pr w hseq
  have := locallyOfFiniteType_dualVectorBundleToBase K m
  have := flat_dualVectorBundleToBase K m
  have := locallyOfFiniteType_dualVectorBundleToBase N (m + e)
  have := flat_dualVectorBundleToBase N (m + e)
  have := locallyOfFiniteType_dualVectorBundleToBase E e
  have := flat_dualVectorBundleToBase E e
  have := locallyOfFiniteType_dualQuotientMap K N E m inc pr w hseq
  have := flat_dualQuotientMap K N E m inc pr w hseq
  have hq := relativeDimension_dualQuotientMap K N E m inc pr w hseq
  have hsq := isPullback_dualQuotientMap K N E inc pr w hseq
  have hbase := dualQuotientMap_comp N E pr
  have hg : dualQuotientMap N E pr ≫ dualVectorBundleToBase E ≫ sX =
      dualVectorBundleToBase N ≫ sX :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ sX) hbase)
  -- Stacks 02RG for the cartesian square over the zero section
  have e1 := flatPullbackChow_properChowPushforward_unconditional C sX
    (dualVectorBundleToBase E ≫ sX) (dualVectorBundleToBase K ≫ sX)
    (dualVectorBundleToBase N ≫ sX) (dualVectorBundleZeroSection E)
    (dualQuotientMap N E pr) (dualVectorBundleToBase K) (subbundleEmbedding K N inc)
    hsq (dualVectorBundleZeroSection_comp_base C sX E) hg rfl m hq k α
  refine HEq.trans (heq_of_eq e1.symm) ?_
  refine (flatPullbackChow_heq_of_degree C _ _ (dualQuotientMap N E pr) hg m hq
    (show k = k - (e : ℤ) + (e : ℤ) by omega) _ (flatPullbackDescends C _ _ _ _ _ _ _)
    (hZ k α)).trans ?_
  refine (flatPullbackChow_comp C (dualVectorBundleToBase N ≫ sX)
    (dualVectorBundleToBase E ≫ sX) sX (dualQuotientMap N E pr)
    (dualVectorBundleToBase E) hg rfl m e hq (relativeDimension_dualVectorBundleToBase E e)
    (k - e) (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (GenuineChern.chernCap C e sX E k (Fin.last e) α)).trans ?_
  exact flatPullbackChow_heq_congr C _ sX _ (dualVectorBundleToBase N) _ rfl hbase
    (show m + e = m + e from rfl) _ (relativeDimension_dualVectorBundleToBase N (m + e))
    rfl _ (flatPullbackDescends C _ _ _ _ _ _ _) _ _ HEq.rfl

end FromZeroSection

section RankZero

variable (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]

/-- **The zero section formula in rank zero**: `p : 𝐕(ℰ^∨) ⟶ X` is an isomorphism with inverse the
zero section, and `c_0 = 1`. -/
theorem zeroSectionFormula_of_rank_zero : ZeroSectionFormula C sX E 0 := by
  intro k α
  have := locallyOfFiniteType_dualVectorBundleToBase E 0
  have := flat_dualVectorBundleToBase E 0
  have hq : IsIso (dualVectorBundleToBase E) :=
    isIso_vectorBundleToBase_zero (dualSheaf E)
  have : IsIso (dualVectorBundleZeroSection E) := by
    have h : dualVectorBundleZeroSection E = inv (dualVectorBundleToBase E) :=
      (IsIso.eq_inv_of_inv_hom_id (dualVectorBundleZeroSection_comp E))
    rw [h]
    infer_instance
  have key := flatPullbackChowOfRelativeDimension_of_isIso C (dualVectorBundleToBase E ≫ sX) sX
    (dualVectorBundleToBase E) rfl (relativeDimension_dualVectorBundleToBase E 0)
    (dualVectorBundleZeroSection E) (dualVectorBundleZeroSection_comp E)
    (dualVectorBundleZeroSection_comp_base C sX E) k α
  rw [GenuineChern.chernCap_zero]
  refine HEq.trans ?_ (flatPullbackChow_heq_of_degree C _ sX (dualVectorBundleToBase E) rfl 0
    (relativeDimension_dualVectorBundleToBase E 0) (show k = k - ((0 : ℕ) : ℤ) by simp)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupCast_heq C sX _ α).symm)
  refine HEq.trans ?_ (heq_of_eq key.symm)
  exact (chowGroupCast_heq C _ _ _).symm

end RankZero

end Stacks.Chow

end
