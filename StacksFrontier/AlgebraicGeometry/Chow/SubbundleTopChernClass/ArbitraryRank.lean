module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCover

/-!
# Chern classes and sections: the class of a subbundle, in arbitrary ranks

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules, whose ranks need not be constant.
Let `i : N' ⟶ N` be the closed embedding of the vector bundles `N' = Spec_X(Sym((𝒩')^∨))` and
`N = Spec_X(Sym(𝒩^∨))`, with projections `p' : N' ⟶ X` and `p : N ⟶ X`. [Stacks, Tag 0FAA]
says that for `α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`,

where `c_top(ℰ)` is the top Chern class of [Stacks, Tag 0FA4]. The ranks of `𝒩'` and `ℰ` are
locally constant, so `X` is the disjoint union of the open and closed loci on which both are
constant, and the morphisms `p'` and `p` are flat of the constant relative dimensions `r'` and
`r' + e` only over such a locus. Both sides of the identity are accordingly read on the parts of
`N` lying over the opens `U ⊆ X` on which `𝒩'` and `ℰ` have constant ranks `r'` and `e`: there
`p'` and `p` restrict to flat morphisms `p'⁻¹(U) ⟶ X` and `p⁻¹(U) ⟶ X` of relative dimensions
`r'` and `r' + e`, `i` restricts to a closed embedding `p'⁻¹(U) ⟶ p⁻¹(U)`, and `c_top(ℰ)` acts by
its degree-`e` part.

## Main results

* `Stacks.Chow.subbundleEmbeddingRestrict_pushforward_flatPullback_eq_topChernCap` —
  [Stacks, Tag 0FAA]: `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)` for modules of arbitrary rank.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

attribute [local instance] isFiniteLocallyFree_pullbackObj

/-! ### Ranks over an open subscheme -/

section Rank

variable {X : Scheme.{u}}

/-- A finite locally free module restricted to an open subscheme contained in its rank-`r` locus
has constant rank `r`. -/
theorem isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (U : X.Opens) (r : ℕ)
    (h : U ≤ rankLocus F r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r :=
  Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq F U r fun x hx ↦
    (fiberRank_eq_moduleRank F x).trans (h hx)

/-- In a short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free modules, on an open
subscheme on which `𝒩'` and `ℰ` have constant ranks `r'` and `e`, the module `𝒩` has constant
rank `r' + e`. -/
theorem isFiniteLocallyFreeOfRank_pullback_ι_of_shortExact (N' N E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) (U : X.Opens) (r' e : ℕ)
    (hN' : U ≤ rankLocus N' r') (hE : U ≤ rankLocus E e) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj N) (r' + e) :=
  GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _
    (Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree U.ι _ hseq) r' e
    (isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus N' U r' hN')
    (isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus E U e hE)

end Rank

/-! ### Flat pullback along a morphism through an isomorphism and an open immersion -/

section FlatPullback

variable (C : ChowSituation.{u}) {A B W X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Flat pullback along `ψ ≫ q ≫ j`**, for an isomorphism `ψ`, a flat morphism `q` of relative
dimension `r` and an open immersion `j : W ⟶ X`: it is restriction to `W`, followed by flat
pullback along `q`, followed by transport along `ψ` (Stacks 02RD). -/
theorem flatPullbackChow_heq_chowPushforwardOfIso_restrict (ψ : A ≅ B) (q : B ⟶ W)
    [LocallyOfFiniteType q] [Flat q] (r : ℕ) (hq : AlgebraicGeometry.RelativeDimension q r)
    (j : W ⟶ X) [IsOpenImmersion j] (f : A ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hf : f = ψ.hom ≫ q ≫ j) (hfr : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (α : chowGroup C sX k) :
    flatPullbackChow C (f ≫ sX) sX f rfl r hfr k (flatPullbackDescends C _ _ _ _ _ _ _) α ≍
      chowPushforwardOfIso C (q ≫ (j ≫ sX)) (f ≫ sX) (inv ψ.hom)
        (by simp [hf])
        (k + (r : ℤ))
        (flatPullbackChow C (q ≫ (j ≫ sX)) (j ≫ sX) q rfl r hq k
          (flatPullbackDescends C _ _ _ _ _ _ _) (chowGroupRestrict C sX (j ≫ sX) j rfl k α)) := by
  have hj0 := relativeDimension_of_isOpenImmersion j
  have hψ0 := relativeDimension_of_isOpenImmersion ψ.hom
  have hqj := AlgebraicGeometry.RelativeDimension.comp_of_flat q j hq hj0
  have hψqj := AlgebraicGeometry.RelativeDimension.comp_of_flat ψ.hom (q ≫ j) hψ0 hqj
  have h1 : flatPullbackChow C (f ≫ sX) sX f rfl r hfr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α ≍
      flatPullbackChow C (ψ.hom ≫ (q ≫ j) ≫ sX) sX (ψ.hom ≫ q ≫ j)
        (by rw [Category.assoc]) (0 + (r + 0)) hψqj k
        (flatPullbackDescends C _ _ _ _ _ _ _) α :=
    flatPullbackChow_heq_congr_base C (by rw [hf, Category.assoc]) rfl hf rfl _ (by simp) hfr
      hψqj rfl _ _ α α HEq.rfl
  have h2 := (flatPullbackChow_comp C (ψ.hom ≫ (q ≫ j) ≫ sX) ((q ≫ j) ≫ sX) sX ψ.hom (q ≫ j)
    rfl rfl 0 (r + 0) hψ0 hqj k (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α).symm
  have h3 := flatPullbackChow_heq_chowPushforwardOfIso C (ψ.hom ≫ (q ≫ j) ≫ sX) ((q ≫ j) ≫ sX)
    ψ.hom rfl hψ0 (k + ((r + 0 : ℕ) : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackChow C ((q ≫ j) ≫ sX) sX (q ≫ j) rfl (r + 0) hqj k
      (flatPullbackDescends C _ _ _ _ _ _ _) α)
  have h4 := (flatPullbackChow_comp C ((q ≫ j) ≫ sX) (j ≫ sX) sX q j
    (by rw [Category.assoc]) rfl r 0 hq hj0 k (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α).symm
  have h5 := heq_chowGroupRestrict_flatPullbackChow C sX (j ≫ sX) j rfl hj0 k
    (flatPullbackDescends C _ _ _ _ _ _ _) α
  have h6 : flatPullbackChow C ((q ≫ j) ≫ sX) (j ≫ sX) q (by rw [Category.assoc]) r hq
        (k + ((0 : ℕ) : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
        (flatPullbackChow C (j ≫ sX) sX j rfl 0 hj0 k (flatPullbackDescends C _ _ _ _ _ _ _) α) ≍
      flatPullbackChow C (q ≫ (j ≫ sX)) (j ≫ sX) q rfl r hq k
        (flatPullbackDescends C _ _ _ _ _ _ _) (chowGroupRestrict C sX (j ≫ sX) j rfl k α) :=
    flatPullbackChow_heq_congr_base C (Category.assoc _ _ _) rfl rfl _ _ rfl hq hq (by simp) _ _
      _ _ h5.symm
  refine h1.trans (h2.trans (h3.trans ?_))
  exact chowPushforwardOfIso_heq (inv ψ.hom) _ _ (Category.assoc _ _ _)
    (by rw [hf]; simp only [Category.assoc]) (by simp) (h4.trans h6)

end FlatPullback

/-! ### Stacks 0FAA -/

section Subbundle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`
and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules.
Let `i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` be the canonical closed embedding and
`p' : N' ⟶ X`, `p : N ⟶ X` the structure morphisms. Then for `α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`,

`c_top(ℰ)` being the top Chern class of Stacks 0FA4.

The ranks of `𝒩'` and `ℰ` are locally constant and the flat pullbacks are taken where they are
constant: for every open `U ⊆ X` on which `𝒩'` has rank `r'` and `ℰ` has rank `e`, the
projections restrict to flat morphisms `p'⁻¹(U) ⟶ X` and `p⁻¹(U) ⟶ X` of relative dimensions `r'`
and `r' + e`, `i` restricts to the closed embedding `p'⁻¹(U) ⟶ p⁻¹(U)`, `c_top(ℰ)` acts by its
degree-`e` part (`Stacks.Chow.topChernCap`), and the identity holds in
`CH_{k+r'}(p⁻¹(U)) = CH_{(k-e)+(r'+e)}(p⁻¹(U))`. Taking for `U` the pieces of the decomposition of
`X` by the ranks of `𝒩'` and `ℰ`, this is the identity of the tag in
`CH_*(N) = ∏_U CH_*(p⁻¹(U))`. -/
theorem subbundleEmbeddingRestrict_pushforward_flatPullback_eq_topChernCap (U : X.Opens)
    (r' e : ℕ) (hN' : U ≤ rankLocus N' r') (hE : U ≤ rankLocus E e) (k : ℤ)
    (α : chowGroup C sX k) :
    letI := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus N' U r' hN'
    letI := isFiniteLocallyFreeOfRank_pullback_ι_of_shortExact N' N E inc pr w hseq U r' e hN'
      hE
    letI := isClosedImmersion_subbundleEmbeddingRestrict N' N inc U E pr w hseq
    letI := locallyOfFiniteType_dualVectorBundleRestrict N' U r'
    letI := flat_dualVectorBundleRestrict N' U r'
    letI := locallyOfFiniteType_dualVectorBundleRestrict N U (r' + e)
    letI := flat_dualVectorBundleRestrict N U (r' + e)
    chowPushforwardOfIsClosedImmersion C
        (((dualVectorBundleToBase N' ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N') ≫ sX)
        (((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) ≫ sX)
        (subbundleEmbeddingRestrict N' N inc U)
        (subbundleEmbeddingRestrict_comp_base N' N inc U sX) (k + (r' : ℤ))
        (flatPullbackChow C (((dualVectorBundleToBase N' ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N') ≫ sX)
          sX ((dualVectorBundleToBase N' ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N') rfl r'
          (relativeDimension_dualVectorBundleRestrict N' U r') k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      Eq.mp (congrArg (chowGroup C
          (((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) ≫ sX))
          (by push_cast; ring))
        (flatPullbackChow C (((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) ≫ sX)
          sX ((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) rfl (r' + e)
          (relativeDimension_dualVectorBundleRestrict N U (r' + e)) (k - (e : ℤ))
          (flatPullbackDescends C _ _ _ _ _ _ _) (topChernCap C sX E k e α)) := by
  let := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus N' U r' hN'
  let := isFiniteLocallyFreeOfRank_pullback_ι_of_le_rankLocus E U e hE
  let := isFiniteLocallyFreeOfRank_pullback_ι_of_shortExact N' N E inc pr w hseq U r' e hN' hE
  let := isClosedImmersion_subbundleEmbeddingRestrict N' N inc U E pr w hseq
  let := locallyOfFiniteType_dualVectorBundleRestrict N' U r'
  let := flat_dualVectorBundleRestrict N' U r'
  let := locallyOfFiniteType_dualVectorBundleRestrict N U (r' + e)
  let := flat_dualVectorBundleRestrict N U (r' + e)
  let := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback U.ι).obj N') r'
  let := dualVectorBundleToBase_flat ((Scheme.Modules.pullback U.ι).obj N') r'
  let := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback U.ι).obj N)
    (r' + e)
  let := dualVectorBundleToBase_flat ((Scheme.Modules.pullback U.ι).obj N) (r' + e)
  set V := dualVectorBundleToBase N ⁻¹ᵁ U with hV
  set V' := dualVectorBundleToBase N' ⁻¹ᵁ U with hV'
  set ψ := dualVectorBundleRestrictIso N U with hψ
  set ψ' := dualVectorBundleRestrictIso N' U with hψ'
  set q := dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N) with hq
  set q' := dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N') with hq'
  have hpV : V.ι ≫ dualVectorBundleToBase N = ψ.hom ≫ q ≫ U.ι :=
    ι_comp_dualVectorBundleToBase_eq N U
  have hpV' : V'.ι ≫ dualVectorBundleToBase N' = ψ'.hom ≫ q' ≫ U.ι :=
    ι_comp_dualVectorBundleToBase_eq N' U
  have hsq : subbundleEmbeddingRestrict N' N inc U ≫ ψ.hom =
      ψ'.hom ≫ subbundleEmbedding ((Scheme.Modules.pullback U.ι).obj N')
        ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).map inc) :=
    subbundleEmbeddingRestrict_comp_dualVectorBundleRestrictIso_hom N' N inc U
  set β := chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k α with hβ
  set γ := flatPullbackChow C (q ≫ (U.ι ≫ sX)) (U.ι ≫ sX) q rfl (r' + e)
    (dualVectorBundleToBase_relativeDimension _ (r' + e)) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl _ _ k) β
  have hS := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree U.ι _ hseq
  have hA := subbundleEmbedding_pushforward_flatPullback_heq_chernCap C (U.ι ≫ sX)
    ((Scheme.Modules.pullback U.ι).obj N') ((Scheme.Modules.pullback U.ι).obj N)
    ((Scheme.Modules.pullback U.ι).obj E) r' (r' + e) e ((Scheme.Modules.pullback U.ι).map inc)
    ((Scheme.Modules.pullback U.ι).map pr)
    ((ShortComplex.mk inc pr w).map (Scheme.Modules.pullback U.ι)).zero hS (by push_cast; ring)
    k β
  have hL' := flatPullbackChow_heq_chowPushforwardOfIso_restrict C sX ψ' q' r'
    (dualVectorBundleToBase_relativeDimension _ r') U.ι
    (V'.ι ≫ dualVectorBundleToBase N') hpV' (relativeDimension_dualVectorBundleRestrict N' U r') k
    α
  have hL := flatPullbackChow_heq_chowPushforwardOfIso_restrict C sX ψ q (r' + e)
    (dualVectorBundleToBase_relativeDimension _ (r' + e)) U.ι
    (V.ι ≫ dualVectorBundleToBase N) hpV (relativeDimension_dualVectorBundleRestrict N U (r' + e))
    k α
  have hψ0 := relativeDimension_of_isOpenImmersion ψ.hom
  have hr := relativeDimension_dualVectorBundleRestrict N U (r' + e)
  have hm : ∀ t : V, (V.ι ≫ dualVectorBundleToBase N).base t ∈ rankLocus E e := fun t ↦ hE t.2
  let eE : (Scheme.Modules.pullback (V.ι ≫ dualVectorBundleToBase N)).obj E ≅
      (Scheme.Modules.pullback ψ.hom).obj
        ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback U.ι).obj E)) :=
    eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj E) hpV) ≪≫
      ((Scheme.Modules.pullbackComp ψ.hom (q ≫ U.ι)).app E).symm ≪≫
      (Scheme.Modules.pullback ψ.hom).mapIso ((Scheme.Modules.pullbackComp q U.ι).app E).symm
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (V.ι ≫ dualVectorBundleToBase N)).obj E) e :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} eE.symm
      inferInstance
  let := subbundleEmbedding_isClosedImmersion_of_shortExact ((Scheme.Modules.pullback U.ι).obj N')
    ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).obj E)
    ((Scheme.Modules.pullback U.ι).map inc) ((Scheme.Modules.pullback U.ι).map pr)
    ((ShortComplex.mk inc pr w).map (Scheme.Modules.pullback U.ι)).zero hS
  have hsA : inv ψ'.hom ≫ ((V'.ι ≫ dualVectorBundleToBase N') ≫ sX) = q' ≫ (U.ι ≫ sX) := by
    simp [hpV']
  have hsD : inv ψ.hom ≫ ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) = q ≫ (U.ι ≫ sX) := by
    simp [hpV]
  have hfψ : ψ.hom ≫ (q ≫ (U.ι ≫ sX)) = (V.ι ≫ dualVectorBundleToBase N) ≫ sX := by
    rw [hpV]; simp only [Category.assoc]
  have hcomp : inv ψ'.hom ≫ subbundleEmbeddingRestrict N' N inc U =
      subbundleEmbedding ((Scheme.Modules.pullback U.ι).obj N')
        ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).map inc) ≫
        inv ψ.hom := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have E1 := congrArg (chowPushforwardOfIsClosedImmersion C
    ((V'.ι ≫ dualVectorBundleToBase N') ≫ sX) ((V.ι ≫ dualVectorBundleToBase N) ≫ sX)
    (subbundleEmbeddingRestrict N' N inc U)
    (subbundleEmbeddingRestrict_comp_base N' N inc U sX) (k + (r' : ℤ))) (eq_of_heq hL')
  have E2 := properChowPushforward_comp_eq C (q' ≫ (U.ι ≫ sX))
    ((V'.ι ≫ dualVectorBundleToBase N') ≫ sX) (q ≫ (U.ι ≫ sX))
    ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) (inv ψ'.hom) (subbundleEmbeddingRestrict N' N inc U)
    (subbundleEmbedding ((Scheme.Modules.pullback U.ι).obj N')
      ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).map inc))
    (inv ψ.hom) hcomp hsA (subbundleEmbeddingRestrict_comp_base N' N inc U sX)
    (subbundleEmbedding_comp_base _ _ (U.ι ≫ sX) _) hsD (k + (r' : ℤ))
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (flatPullbackChow C (q' ≫ (U.ι ≫ sX)) (U.ι ≫ sX) q' rfl r'
      (dualVectorBundleToBase_relativeDimension _ r') k
      (flatPullbackDescends C _ _ _ _ _ _ _) β)
  have E4 := chowPushforwardOfIso_heq (inv ψ.hom) hsD hsD rfl rfl (by push_cast; ring) hA
  have E5 := (flatPullbackChow_heq_chowPushforwardOfIso C
    ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) (q ≫ (U.ι ≫ sX)) ψ.hom hfψ hψ0
    ((k + ((r' + e : ℕ) : ℤ)) - (e : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
    (GenuineChern.chernCap C e (q ≫ (U.ι ≫ sX))
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback U.ι).obj E))
      (k + ((r' + e : ℕ) : ℤ)) (Fin.last e)
      γ)).symm
  have E6 := (GenuineChern.chernCap_flatPullback_heq_general C (q ≫ (U.ι ≫ sX))
    ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) ψ.hom hfψ 0 hψ0
    ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback U.ι).obj E)) e
    ((Scheme.Modules.pullback (V.ι ≫ dualVectorBundleToBase N)).obj E) eE
    (k + ((r' + e : ℕ) : ℤ)) (Fin.last e)
    γ).symm
  have hψβ := (flatPullbackChow_heq_chowPushforwardOfIso C
    ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) (q ≫ (U.ι ≫ sX)) ψ.hom hfψ hψ0
    (k + ((r' + e : ℕ) : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
    γ).trans
    hL.symm
  have E7 := GenuineChern.chernCap_heq_of_degree C ((V.ι ≫ dualVectorBundleToBase N) ≫ sX)
    (F := (Scheme.Modules.pullback (V.ι ≫ dualVectorBundleToBase N)).obj E) (Fin.last e)
    (by simp) hψβ
  have E8 := (idRule_topChernTotalClass_self C sX E e (V.ι ≫ dualVectorBundleToBase N) hm
    (k + ((r' + e : ℕ) : ℤ))
    (flatPullbackChow C ((V.ι ≫ dualVectorBundleToBase N) ≫ sX) sX
      (V.ι ≫ dualVectorBundleToBase N) rfl (r' + e) hr k
      (flatPullbackDescends C _ _ _ _ _ _ _) α)).symm
  set α₁ := chowGroupCongr C (Category.id_comp sX).symm k α with hα₁
  have hαα₁ : α ≍ α₁ := (chowGroupCongr_heq C _ k α).symm
  have E9 := IdentityCapRule.heq_congr C sX
    ((topChernTotalClass C sX E e).idRule C sX (gysinSystemOfInvertible C)) rfl rfl
    (flatPullbackChow_heq_congr_base C rfl (Category.id_comp sX).symm rfl rfl
      (by rw [Category.id_comp]) rfl hr hr rfl (flatPullbackDescends C _ _ _ _ _ _ _)
      (flatPullbackDescends C _ _ _ _ _ _ _) α α₁ hαα₁)
  have E10 := (topChernTotalClass C sX E e).idRule_flatPullbackChow C
    (gysinSystemOfInvertible C) sX (𝟙 X) (V.ι ≫ dualVectorBundleToBase N) (r' + e) hr
    (V.ι ≫ dualVectorBundleToBase N) (Category.comp_id _) k α₁
  have E11 := flatPullbackChow_heq_congr_base C rfl (Category.id_comp sX) rfl
    (by rw [Category.id_comp]) rfl rfl hr hr rfl (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) _ _
    (topChernCap_heq C sX E k e α α₁ hαα₁).symm
  have key := (heq_of_eq (E1.trans E2)).trans (E4.trans (E5.trans (E6.trans (E7.trans
    ((heq_of_eq E8).trans (E9.trans (E10.trans E11)))))))
  exact eq_of_heq (key.trans (cast_heq _ _).symm)

end Subbundle

end Stacks.Chow

end
