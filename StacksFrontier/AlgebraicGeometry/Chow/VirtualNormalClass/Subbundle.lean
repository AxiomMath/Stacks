module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.Construction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.Global
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChernBivariantCommute
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactFlatScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The virtual normal class of a subbundle

Let `(S, δ)` be as in chapter 42 of the Stacks Project, let `X` be locally of finite type over
`S`, let `i : Z ⟶ X` be an immersion with virtual normal sheaf `𝒩` and let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_Z`-modules such that
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as `𝒩^∨ ⟶ (𝒩')^∨ ⟶ 𝒞_{Z/X}`. Stacks 0FBL says

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')`.

The proof is the source's: the factorization makes the closed immersion `C_ZX ⟶ N` factor as
`C_ZX ⟶ N' ⟶ N`, and the identity follows from Stacks 0FAA on every base change of `Z`.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.ofFactor` — the virtual normal sheaf `(𝒩', σ')` of a
  factorization `σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)`.
* `Stacks.Chow.dualBundlePullbackClass` — the flat pullback class `p^* ∈ A^{-n}(𝐕(ℱ^∨) ⟶ Z)`.

## Main results

* `Stacks.Chow.subbundleFlatPullbackBaseChange` — Stacks 0FAA on the base change of `Z` along
  any morphism `Y ⟶ Z`, read through the chosen fibre products.
* `Stacks.Chow.subbundleTestEmbedding_middleCap` — the same, read through capping with `p^*` on a
  test scheme `T ⟶ X`.
* `Stacks.Chow.VirtualNormalBundle.specialFibreEmbedding_ofFactor_comp_subbundleEmbedding` — the
  closed immersion `C_ZX ⟶ N` factors as `C_ZX ⟶ N' ⟶ N`.
* `Stacks.Chow.VirtualNormalBundle.virtualNormalClass_eq_composite` — Stacks 0FBL when `𝒩'` and
  `ℰ` have constant ranks `r'` and `e`: `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')`.
* `Stacks.Chow.topChernClassCompleted_apply_eq_of` — on a connected component the completed top
  Chern class is concentrated in the rank there.

## References

* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### Stacks 0FAA on a base change -/

section BaseChange

variable {Y Z : Scheme.{u}} (F : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (u : Y ⟶ Z)

/-- The base change `𝐕(ℱ^∨) ×_Z Y` is the vector bundle `𝐕((u^*ℱ)^∨)`. -/
@[ega "IV 18.5.1" "partial"]
def dualBundlePullbackIsoPullback :
    dualVectorBundle ((Scheme.Modules.pullback u).obj F) ≅
      pullback (dualVectorBundleToBase F) u :=
  (isPullback_dualBundleBaseChangeMap u F).isoPullback

/-- The identification `𝐕((u^*ℱ)^∨) ≅ 𝐕(ℱ^∨) ×_Z Y` followed by the first projection is the base
change map `𝐕((u^*ℱ)^∨) ⟶ 𝐕(ℱ^∨)`. -/
@[reassoc (attr := simp)]
theorem dualBundlePullbackIsoPullback_hom_fst :
    (dualBundlePullbackIsoPullback F u).hom ≫
        pullback.fst (dualVectorBundleToBase F) u =
      dualBundleBaseChangeMap u F :=
  (isPullback_dualBundleBaseChangeMap u F).isoPullback_hom_fst

/-- The identification `𝐕((u^*ℱ)^∨) ≅ 𝐕(ℱ^∨) ×_Z Y` followed by the second projection is the
projection `𝐕((u^*ℱ)^∨) ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem dualBundlePullbackIsoPullback_hom_snd :
    (dualBundlePullbackIsoPullback F u).hom ≫
        pullback.snd (dualVectorBundleToBase F) u =
      dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) :=
  (isPullback_dualBundleBaseChangeMap u F).isoPullback_hom_snd

variable {N' N : Z.Modules} [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (inc : N' ⟶ N)

/-- The base change `N' ×_Z Y ⟶ N ×_Z Y` of the embedding `N' ⟶ N` of vector bundles. -/
def subbundleEmbeddingBaseChange :
    pullback (dualVectorBundleToBase N') u ⟶
      pullback (dualVectorBundleToBase N) u :=
  pullback.lift (pullback.fst _ u ≫ subbundleEmbedding N' N inc) (pullback.snd _ u)
    ((Category.assoc _ _ _).trans
      ((congrArg (pullback.fst (dualVectorBundleToBase N') u ≫ ·)
        (subbundleEmbedding_comp_dualVectorBundleToBase N' N inc)).trans pullback.condition))

/-- The base change `N' ×_Z Y ⟶ N ×_Z Y` followed by the first projection to `N` is the first
projection to `N'` followed by the embedding `N' ⟶ N`. -/
@[reassoc (attr := simp)]
theorem subbundleEmbeddingBaseChange_fst :
    subbundleEmbeddingBaseChange u inc ≫
        pullback.fst (dualVectorBundleToBase N) u =
      pullback.fst (dualVectorBundleToBase N') u ≫
        subbundleEmbedding N' N inc :=
  pullback.lift_fst _ _ _

/-- The base change `N' ×_Z Y ⟶ N ×_Z Y` commutes with the second projections to `Y`. -/
@[reassoc (attr := simp)]
theorem subbundleEmbeddingBaseChange_snd :
    subbundleEmbeddingBaseChange u inc ≫
        pullback.snd (dualVectorBundleToBase N) u =
      pullback.snd (dualVectorBundleToBase N') u :=
  pullback.lift_snd _ _ _

/-- Through the identifications `N' ×_Z Y = 𝐕((u^*𝒩')^∨)` and `N ×_Z Y = 𝐕((u^*𝒩)^∨)`, the base
change of the embedding is the embedding of the pulled back subbundle. -/
theorem dualBundlePullbackIsoPullback_hom_comp_subbundleEmbeddingBaseChange :
    (dualBundlePullbackIsoPullback N' u).hom ≫ subbundleEmbeddingBaseChange u inc =
      subbundleEmbedding _ _ ((Scheme.Modules.pullback u).map inc) ≫
        (dualBundlePullbackIsoPullback N u).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, subbundleEmbeddingBaseChange_fst, ← Category.assoc,
      dualBundlePullbackIsoPullback_hom_fst, Category.assoc, dualBundlePullbackIsoPullback_hom_fst]
    exact dualBundleBaseChangeMap_comp_subbundleEmbedding u N' N inc
  · rw [Category.assoc, subbundleEmbeddingBaseChange_snd, dualBundlePullbackIsoPullback_hom_snd,
      Category.assoc, dualBundlePullbackIsoPullback_hom_snd]
    exact (subbundleEmbedding_comp_dualVectorBundleToBase _ _ _).symm

end BaseChange

/-! ### The flat pullback class of a vector bundle on a test scheme -/

section FlatPullback

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (F : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n]

/-- The flat pullback class `p^* ∈ A^{-n}(𝐕(ℱ^∨) ⟶ Z)` of the projection of the vector bundle of
a finite locally free module of rank `n` (Stacks 0B78). -/
def dualBundlePullbackClass :
    haveI := locallyOfFiniteType_dualVectorBundleToBase F n
    haveI := flat_dualVectorBundleToBase F n
    BivariantClass C (gysinSystemOfInvertible C) (dualVectorBundleToBase F ≫ sZ) sZ
      (dualVectorBundleToBase F) rfl (-(n : ℤ)) :=
  haveI := locallyOfFiniteType_dualVectorBundleToBase F n
  haveI := flat_dualVectorBundleToBase F n
  flatPullbackBivariantClassOfInvertible C (dualVectorBundleToBase F ≫ sZ) sZ
    (dualVectorBundleToBase F) rfl n (relativeDimension_dualVectorBundleToBase F n)

omit [LocallyOfFiniteType sZ] in
/-- The identification `𝐕((u^*ℱ)^∨) ≅ 𝐕(ℱ^∨) ×_Z Y` is compatible with the structure morphisms
to `S`. -/
theorem dualBundlePullbackIsoPullback_hom_comp_structure (u : Y ⟶ Z) :
    (dualBundlePullbackIsoPullback F u).hom ≫
        (pullback.fst (dualVectorBundleToBase F) u ≫ (dualVectorBundleToBase F ≫ sZ)) =
      dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) ≫ (u ≫ sZ) := by
  rw [← Category.assoc, dualBundlePullbackIsoPullback_hom_fst]
  exact dualBundleBaseChangeMap_comp_structure C sZ F u

/-- **On a test scheme `u : Y ⟶ Z`, capping with `p^*` is flat pullback along the projection of
`𝐕((u^*ℱ)^∨)`**, read on `𝐕(ℱ^∨) ×_Z Y` through `𝐕((u^*ℱ)^∨) ≅ 𝐕(ℱ^∨) ×_Z Y`. -/
theorem dualBundlePullbackClass_cap_heq (u : Y ⟶ Z) [LocallyOfFiniteType u] (m : ℤ)
    (γ : chowGroup C (u ≫ sZ) m) :
    haveI := locallyOfFiniteType_dualVectorBundleToBase F n
    (dualBundlePullbackClass C sZ F n).cap u m γ ≍
      chowPushforwardOfIso C (dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) ≫ (u ≫ sZ))
        (pullback.fst (dualVectorBundleToBase F) u ≫ (dualVectorBundleToBase F ≫ sZ))
        (dualBundlePullbackIsoPullback F u).hom
        (dualBundlePullbackIsoPullback_hom_comp_structure C sZ F u) (m + n)
        (dualBundlePullback C (u ≫ sZ) ((Scheme.Modules.pullback u).obj F) n m γ) := by
  have := locallyOfFiniteType_dualVectorBundleToBase F n
  have := flat_dualVectorBundleToBase F n
  have := locallyOfFiniteType_dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) n
  have := flat_dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) n
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans (heq_of_eq ?_)
  have hsq : dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) ≫ 𝟙 Y =
      (dualBundlePullbackIsoPullback F u).hom ≫ pullback.snd (dualVectorBundleToBase F) u := by
    rw [Category.comp_id, dualBundlePullbackIsoPullback_hom_snd]
  have key := flatPullbackChow_chowPushforwardOfIso C (u ≫ sZ)
    (dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F) ≫ (u ≫ sZ)) (u ≫ sZ)
    (pullback.fst (dualVectorBundleToBase F) u ≫ (dualVectorBundleToBase F ≫ sZ))
    (𝟙 Y) (Category.id_comp _) (dualBundlePullbackIsoPullback F u).hom
    (dualBundlePullbackIsoPullback_hom_comp_structure C sZ F u)
    (dualVectorBundleToBase ((Scheme.Modules.pullback u).obj F)) rfl
    (pullback.snd (dualVectorBundleToBase F) u)
    (pullbackSnd_comp_structureMorphism_eq C (dualVectorBundleToBase F ≫ sZ) sZ
      (dualVectorBundleToBase F) rfl u) hsq n
    (relativeDimension_dualVectorBundleToBase _ n)
    (relativeDimension_pullback_snd _ u n (relativeDimension_dualVectorBundleToBase F n)) m
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) γ
  rw [show chowPushforwardOfIso C (u ≫ sZ) (u ≫ sZ) (𝟙 Y) (Category.id_comp _) m γ = γ from
    DFunLike.congr_fun (properChowPushforward_id C (u ≫ sZ) m _) γ] at key
  exact key

end FlatPullback

/-! ### Stacks 0FAA on the base changes of the bundles -/

section Subbundle

variable {Y Z : Scheme.{u}} {N' N : Z.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (u : Y ⟶ Z) (inc : N' ⟶ N)

/-- The base change of the embedding `N' ⟶ N` along `u : Y ⟶ Z` is a base change of it. -/
theorem isPullback_subbundleEmbeddingBaseChange :
    IsPullback (pullback.fst (dualVectorBundleToBase N') u) (subbundleEmbeddingBaseChange u inc)
      (subbundleEmbedding N' N inc) (pullback.fst (dualVectorBundleToBase N) u) := by
  have hs : IsPullback (pullback.fst (dualVectorBundleToBase N') u)
      (subbundleEmbeddingBaseChange u inc ≫ pullback.snd (dualVectorBundleToBase N) u)
      (subbundleEmbedding N' N inc ≫ dualVectorBundleToBase N) u := by
    rw [subbundleEmbedding_comp_dualVectorBundleToBase, subbundleEmbeddingBaseChange_snd]
    exact IsPullback.of_hasPullback _ _
  exact hs.of_bot (subbundleEmbeddingBaseChange_fst u inc).symm (IsPullback.of_hasPullback _ _)

/-- The base change `N' ×_Z Y ⟶ N ×_Z Y` is compatible with the structure morphisms to `S`. -/
theorem subbundleEmbeddingBaseChange_comp_structure {C : ChowSituation.{u}} (sZ : Z ⟶ C.S) :
    subbundleEmbeddingBaseChange u inc ≫
        (pullback.fst (dualVectorBundleToBase N) u ≫ (dualVectorBundleToBase N ≫ sZ)) =
      pullback.fst (dualVectorBundleToBase N') u ≫ (dualVectorBundleToBase N' ≫ sZ) := by
  rw [subbundleEmbeddingBaseChange_fst_assoc, ← Category.assoc (subbundleEmbedding N' N inc),
    subbundleEmbedding_comp_dualVectorBundleToBase]

variable (C : ChowSituation.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (E : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r' e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- **Stacks 0FAA on a base change of `Z`.** Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence
of finite locally free `𝒪_Z`-modules, `𝒩'` of rank `r'` and `ℰ` of rank `e`, with vector bundles
`p' : N' ⟶ Z`, `p : N ⟶ Z` and embedding `j : N' ⟶ N`. For every `u : Y ⟶ Z` locally of finite
type and `γ ∈ A_m(Y)`,

  `j_{Y,*} (p'^* ∩ γ) = p^* ∩ (c_e(u^*ℰ) ∩ γ)`   in   `A_*(N ×_Z Y)`,

where `j_Y : N' ×_Z Y ⟶ N ×_Z Y` is the base change of `j` and `p^* ∩ -`, `p'^* ∩ -` are the cap
operations of the flat pullback classes on the test scheme `u`. -/
theorem subbundleFlatPullbackBaseChange [LocallyOfFiniteType u] (m : ℤ)
    (γ : chowGroup C (u ≫ sZ) m) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
    haveI : IsClosedImmersion (subbundleEmbeddingBaseChange u inc) :=
      MorphismProperty.of_isPullback (isPullback_subbundleEmbeddingBaseChange u inc)
        (P := @IsClosedImmersion) inferInstance
    haveI := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
    haveI := locallyOfFiniteType_dualVectorBundleToBase N' r'
    haveI := locallyOfFiniteType_dualVectorBundleToBase N (r' + e)
    properChowPushforward C
        (pullback.fst (dualVectorBundleToBase N') u ≫ (dualVectorBundleToBase N' ≫ sZ))
        (pullback.fst (dualVectorBundleToBase N) u ≫ (dualVectorBundleToBase N ≫ sZ))
        (subbundleEmbeddingBaseChange u inc) (subbundleEmbeddingBaseChange_comp_structure u inc sZ)
        (m - -(r' : ℤ)) (properPushforwardDescends C _ _ _ _ _)
        ((dualBundlePullbackClass C sZ N' r').cap u m γ) ≍
      (dualBundlePullbackClass C sZ N (r' + e)).cap u (m - e)
        (GenuineChern.chernCap C e (u ≫ sZ) ((Scheme.Modules.pullback u).obj E) m (Fin.last e)
          γ) := by
  have := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
  have : IsClosedImmersion (subbundleEmbeddingBaseChange u inc) :=
    MorphismProperty.of_isPullback (isPullback_subbundleEmbeddingBaseChange u inc)
      (P := @IsClosedImmersion) inferInstance
  have := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
  have := locallyOfFiniteType_dualVectorBundleToBase N' r'
  have := locallyOfFiniteType_dualVectorBundleToBase N (r' + e)
  have w' : (Scheme.Modules.pullback u).map inc ≫ (Scheme.Modules.pullback u).map pr = 0 :=
    pullback_map_comp_pullback_map_eq_zero N' N E inc pr w u
  have hseq' : (ShortComplex.mk ((Scheme.Modules.pullback u).map inc)
      ((Scheme.Modules.pullback u).map pr) w').ShortExact :=
    Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree u _ hseq
      (inferInstance)
  have := isClosedImmersion_subbundleEmbedding_of_shortExact _ _ _
    ((Scheme.Modules.pullback u).map inc) ((Scheme.Modules.pullback u).map pr) w' hseq'
  have h0FAA := subbundleEmbedding_pushforward_flatPullback_eq_chernCap C (u ≫ sZ) _ _ _ r' e
    ((Scheme.Modules.pullback u).map inc) ((Scheme.Modules.pullback u).map pr) w' hseq' m γ
  -- the structure morphisms of the four bundles over the base
  have hA : subbundleEmbedding _ _ ((Scheme.Modules.pullback u).map inc) ≫
      (dualVectorBundleToBase ((Scheme.Modules.pullback u).obj N) ≫ (u ≫ sZ)) =
      dualVectorBundleToBase ((Scheme.Modules.pullback u).obj N') ≫ (u ≫ sZ) :=
    subbundleEmbedding_comp_base _ _ (u ≫ sZ) _
  have hcomm := dualBundlePullbackIsoPullback_hom_comp_subbundleEmbeddingBaseChange u inc
  set x := dualBundlePullback C (u ≫ sZ) ((Scheme.Modules.pullback u).obj N') r' m γ
  have step1 := properChowPushforward_heq_congr C _ _ (subbundleEmbeddingBaseChange u inc)
    (subbundleEmbeddingBaseChange_comp_structure u inc sZ) (by ring : m - -(r' : ℤ) = m + r')
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    (dualBundlePullbackClass_cap_heq C sZ N' r' u m γ)
  refine step1.trans ?_
  have step2 : properChowPushforward C _ _ (subbundleEmbeddingBaseChange u inc)
      (subbundleEmbeddingBaseChange_comp_structure u inc sZ) (m + r')
      (properPushforwardDescends C _ _ _ _ _)
      (chowPushforwardOfIso C _ _ (dualBundlePullbackIsoPullback N' u).hom
        (dualBundlePullbackIsoPullback_hom_comp_structure C sZ N' u) (m + r') x) =
      properChowPushforward C _ _ (dualBundlePullbackIsoPullback N u).hom
        (dualBundlePullbackIsoPullback_hom_comp_structure C sZ N u) (m + r')
        (properPushforwardDescends C _ _ _ _ _)
        (properChowPushforward C _ _ (subbundleEmbedding _ _ ((Scheme.Modules.pullback u).map inc))
          hA (m + r') (properPushforwardDescends C _ _ _ _ _) x) := by
    refine (DFunLike.congr_fun (properChowPushforward_comp C _ _ _ _ _ _ _ (m + r')
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)) x).trans ?_
    refine (properChowPushforward_congr_hom C _ _ hcomm _
      (by rw [Category.assoc, dualBundlePullbackIsoPullback_hom_comp_structure C sZ N u, hA])
      (m + r') (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) x).trans ?_
    exact (DFunLike.congr_fun (properChowPushforward_comp C _ _ _ _ _ _ _ (m + r')
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)) x).symm
  refine (heq_of_eq step2).trans ?_
  refine (properChowPushforward_heq_congr C _ _ (dualBundlePullbackIsoPullback N u).hom
    (dualBundlePullbackIsoPullback_hom_comp_structure C sZ N u) (by push_cast; ring)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    h0FAA).trans ?_
  exact (dualBundlePullbackClass_cap_heq C sZ N (r' + e) u (m - e) _).symm

end Subbundle

/-! ### Stacks 0FAA read through capping with `p^*` on a test scheme -/

section TestScheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) {N' N : Z.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (inc : N' ⟶ N)

/-- The base change `N' ×_X T ⟶ N ×_X T` of the embedding `N' ⟶ N` along a test scheme
`t : T ⟶ X`, for a morphism `i : Z ⟶ X`. -/
abbrev subbundleTestEmbedding {T : Scheme.{u}} (t : T ⟶ X) :
    pullback (dualVectorBundleToBase N' ≫ i) t ⟶ pullback (dualVectorBundleToBase N ≫ i) t :=
  subbundleTestBaseChange i (dualVectorBundleToBase N) (subbundleEmbedding N' N inc)
    (subbundleEmbedding_comp_dualVectorBundleToBase N' N inc) t

/-- Through the associativity of fibre products, the base change of `N' ⟶ N` along a test scheme
`t : T ⟶ X` is its base change along `Z ×_X T ⟶ Z`. -/
theorem pullbackRightPullbackFstIso_hom_comp_subbundleTestEmbedding {T : Scheme.{u}}
    (t : T ⟶ X) :
    (pullbackRightPullbackFstIso i t (dualVectorBundleToBase N')).hom ≫
        subbundleTestEmbedding i inc t =
      subbundleEmbeddingBaseChange (pullback.fst i t) inc ≫
        (pullbackRightPullbackFstIso i t (dualVectorBundleToBase N)).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, subbundleTestBaseChange_fst, pullbackRightPullbackFstIso_hom_fst_assoc,
      Category.assoc, pullbackRightPullbackFstIso_hom_fst, subbundleEmbeddingBaseChange_fst]
  · rw [Category.assoc, subbundleTestBaseChange_snd, pullbackRightPullbackFstIso_hom_snd,
      Category.assoc, pullbackRightPullbackFstIso_hom_snd, subbundleEmbeddingBaseChange_snd_assoc]

variable (C : ChowSituation.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] [LocallyOfFiniteType i]
  (E : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r' e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

omit [LocallyOfFiniteType i] in
include hseq in
/-- The base change of the embedding along a test scheme is a closed immersion. -/
theorem isClosedImmersion_subbundleTestEmbedding {T : Scheme.{u}} (t : T ⟶ X) :
    IsClosedImmersion (subbundleTestEmbedding i inc t) :=
  have := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
  isClosedImmersion_subbundleTestBaseChange i _ _ _ t

omit [LocallyOfFiniteType i] in
include hseq in
/-- **Stacks 0FAA, read through capping with `p^*` on a test scheme.** For `t : T ⟶ X` and
`y ∈ A_m(Z ×_X T)`,

  `j_{T,*}((p')^* ∩ y) = p^* ∩ (c_e(ℰ) ∩ y)`   in   `A_*(N ×_X T)`,

where `p^* ∩ -`, `(p')^* ∩ -` are read on `N ×_X T`, `N' ×_X T` and `j_T` is the base change of
`j : N' ⟶ N`. -/
theorem subbundleTestEmbedding_middleCap {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (m : ℤ) (y : chowGroup C (pullback.fst i t ≫ sZ) m) :
    haveI := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
    haveI := locallyOfFiniteType_dualVectorBundleToBase N (r' + e)
    haveI := locallyOfFiniteType_dualVectorBundleToBase N' r'
    haveI := isClosedImmersion_subbundleTestEmbedding i inc E pr w hseq t
    properChowPushforward C
        (pullback.fst (dualVectorBundleToBase N' ≫ i) t ≫ (dualVectorBundleToBase N' ≫ sZ))
        (pullback.fst (dualVectorBundleToBase N ≫ i) t ≫ (dualVectorBundleToBase N ≫ sZ))
        (subbundleTestEmbedding i inc t)
        (subbundleTestBaseChange_comp_structureMorphism i _ sZ _ _ rfl rfl _ _ t)
        (m - -(r' : ℤ)) (properPushforwardDescends C _ _ _ _ _)
        (middleCap C (gysinSystemOfInvertible C) (dualVectorBundleToBase N' ≫ sZ) sZ
          (dualVectorBundleToBase N') i rfl (-(r' : ℤ)) (dualBundlePullbackClass C sZ N' r') t m
          y) ≍
      middleCap C (gysinSystemOfInvertible C) (dualVectorBundleToBase N ≫ sZ) sZ
        (dualVectorBundleToBase N) i rfl (-((r' + e : ℕ) : ℤ))
        (dualBundlePullbackClass C sZ N (r' + e)) t (m - e)
        (GenuineChern.chernCap C e (pullback.fst i t ≫ sZ)
          ((Scheme.Modules.pullback (pullback.fst i t)).obj E) m (Fin.last e) y) := by
  have := isFiniteLocallyFreeOfRank_middle N' N E r' e inc pr w hseq
  have := locallyOfFiniteType_dualVectorBundleToBase N (r' + e)
  have := locallyOfFiniteType_dualVectorBundleToBase N' r'
  have := isClosedImmersion_subbundleTestEmbedding i inc E pr w hseq t
  have := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
  have : IsClosedImmersion (subbundleEmbeddingBaseChange (pullback.fst i t) inc) :=
    MorphismProperty.of_isPullback (isPullback_subbundleEmbeddingBaseChange _ inc)
      (P := @IsClosedImmersion) inferInstance
  have hK := subbundleFlatPullbackBaseChange (pullback.fst i t) inc C sZ E r' e pr w hseq m y
  have hcomp := DFunLike.congr_fun (properChowPushforward_comp C _ _ _
    (pullbackRightPullbackFstIso i t (dualVectorBundleToBase N')).hom
    (subbundleTestEmbedding i inc t)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (dualVectorBundleToBase N' ≫ sZ)
      (dualVectorBundleToBase N') i t)
    (subbundleTestBaseChange_comp_structureMorphism i _ sZ _ _ rfl rfl _ _ t)
    (m - -(r' : ℤ)) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _))
    ((dualBundlePullbackClass C sZ N' r').cap (pullback.fst i t) m y)
  have hcomp' := DFunLike.congr_fun (properChowPushforward_comp C _ _ _
    (subbundleEmbeddingBaseChange (pullback.fst i t) inc)
    (pullbackRightPullbackFstIso i t (dualVectorBundleToBase N)).hom
    (subbundleEmbeddingBaseChange_comp_structure (pullback.fst i t) inc sZ)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (dualVectorBundleToBase N ≫ sZ)
      (dualVectorBundleToBase N) i t)
    (m - -(r' : ℤ)) (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _))
    ((dualBundlePullbackClass C sZ N' r').cap (pullback.fst i t) m y)
  refine (heq_of_eq (hcomp.trans ((properChowPushforward_congr_hom C _ _
    (pullbackRightPullbackFstIso_hom_comp_subbundleTestEmbedding i inc t) _ _ _
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _).trans
    hcomp'.symm))).trans ?_
  exact properChowPushforward_heq_congr C _ _ _ _ (by push_cast; ring)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _ hK

end TestScheme

/-- Capping on the middle fibre product depends on the degree and the class only up to equality
and heterogeneous equality. -/
theorem middleCap_heq_congr (C : ChowSituation.{u}) {G : GysinSystem C} {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hf : f ≫ sY = sX) (p : ℤ) (a : BivariantClass C G sX sY f hf p) {T : Scheme.{u}}
    (t : T ⟶ Z) [LocallyOfFiniteType t] {m m' : ℤ} (hm : m = m')
    {x : chowGroup C (pullback.fst g t ≫ sY) m} {x' : chowGroup C (pullback.fst g t ≫ sY) m'}
    (hx : x ≍ x') :
    middleCap C G sX sY f g hf p a t m x ≍ middleCap C G sX sY f g hf p a t m' x' := by
  subst hm
  obtain rfl := eq_of_heq hx
  rfl

/-! ### The top Chern class on a connected component -/

section TopChernComponent

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (E : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **Stacks 0FA4 on a connected component.** On the connected component `Y_j` of `Y`, on which
`ℰ` has rank `r_j`, the completed top Chern class `c_top(ℰ) ∈ A^*(Y)^∧` is concentrated in degree
`r_j`. -/
theorem topChernClassCompleted_apply_eq_of (j : _root_.ConnectedComponents Y) :
    (topChernClassCompleted C sY E).1 j =
      DirectSum.of _ (Scheme.Modules.rankOnConnectedComponent E j : ℤ)
        ((topChernClassCompleted C sY E).1 j (Scheme.Modules.rankOnConnectedComponent E j)) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine DirectSum.ext fun p ↦ ?_
  by_cases hp : p = (Scheme.Modules.rankOnConnectedComponent E j : ℤ)
  · subst hp
    exact (DirectSum.of_eq_same _ _).symm
  · refine Eq.trans ?_ (DirectSum.of_eq_of_ne _ _ _ hp).symm
    have hseq := completedBivariantSequenceOfInvertible_topChernClassCompleted C sY E
    have hr := restriction_completedBivariantSequence C (gysinSystemOfInvertible C) sY sY (𝟙 Y)
      (Category.id_comp sY) (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) (topChernClassCompleted C sY E).1 p j
    refine hr.symm.trans ?_
    refine Eq.trans ?_ (bivariantConnectedComponentRestriction_topChernClassComponent C sY E j hp)
    exact congrArg (fun c ↦ bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C)
      sY sY (𝟙 Y) (Category.id_comp sY) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      c j) (congrFun hseq p)

/-- **Stacks 0FA4 on a locus of constant rank.** On an open `U ⊆ Y` contained in the locus where
`ℰ` has rank `e`, and for any test scheme `g : T ⟶ U`, the degree `e` part of `c_top(ℰ)` caps at
`g ≫ (U ⟶ Y)` by `c_e(g^*(ℰ|_U)) ∩ -`. -/
theorem idRule_topChernClassComponent_comp_of_le (e : ℕ) (U : Y.Opens) (hU : U ≤ rankLocus E e)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj E) e]
    {T : Scheme.{u}} (g : T ⟶ (U : Scheme.{u})) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C ((g ≫ U.ι) ≫ sY) k) (β' : chowGroup C (g ≫ (U.ι ≫ sY)) k) (hβ : β' ≍ β) :
    (topChernClassComponent C sY E e).idRule C sY (gysinSystemOfInvertible C) (g ≫ U.ι) k β ≍
      GenuineChern.chernCap C e (g ≫ (U.ι ≫ sY))
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj E)) k (Fin.last e)
        β' := by
  have hj : Y.homOfLE hU ≫ (rankLocus E e).ι = U.ι := Y.homOfLE_ι hU
  have hjj : (g ≫ Y.homOfLE hU) ≫ (rankLocus E e).ι = g ≫ U.ι := by
    rw [Category.assoc, hj]
  have hs : g ≫ (U.ι ≫ sY) = (g ≫ Y.homOfLE hU) ≫ ((rankLocus E e).ι ≫ sY) := by
    rw [← hj]; simp only [Category.assoc]
  have hs' : (g ≫ U.ι) ≫ sY = ((g ≫ Y.homOfLE hU) ≫ (rankLocus E e).ι) ≫ sY := by rw [hjj]
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E e
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (g ≫ Y.homOfLE hU)).obj
        ((Scheme.Modules.pullback (rankLocus E e).ι).obj E)) e :=
    GenuineChern.isFiniteLocallyFreeOfRank_pullback _ _ e
  refine (IdentityCapRule.heq_congr C sY _ hjj.symm rfl
    (chowGroupCongr_heq C hs' k β).symm).trans ?_
  refine (idRule_topChernClassComponent_comp_heq C sY E e e (g ≫ Y.homOfLE hU) k _
    (chowGroupCongr C hs k β')
    ((chowGroupCongr_heq C hs k β').trans (hβ.trans (chowGroupCongr_heq C hs' k β).symm))).trans ?_
  rw [rankLocusTopChernFamily_self]
  refine (heq_of_eq (GenuineChern.idRule_chernClass C ((rankLocus E e).ι ≫ sY)
    ((Scheme.Modules.pullback (rankLocus E e).ι).obj E) e (Fin.last e) (g ≫ Y.homOfLE hU) k
    (chowGroupCongr C hs k β'))).trans ?_
  let iso : (Scheme.Modules.pullback (g ≫ Y.homOfLE hU)).obj
        ((Scheme.Modules.pullback (rankLocus E e).ι).obj E) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj E) :=
    (Scheme.Modules.pullbackComp g (Y.homOfLE hU)).symm.app _ ≪≫
      (Scheme.Modules.pullback g).mapIso
        ((Scheme.Modules.pullbackComp (Y.homOfLE hU) (rankLocus E e).ι).app E ≪≫
          eqToIso (congrArg (fun h ↦ (Scheme.Modules.pullback h).obj E) hj))
  exact chernCap_heq_of_iso C hs.symm e iso k (Fin.last e) (chowGroupCongr_heq C hs k β')

/-- **Stacks 0FA4 on a piece of constant rank.** The restriction (Stacks 0FDZ) of the degree `e`
part of `c_top(ℰ)` to an open `U_k ⊆ Y` on which `ℰ` has rank `e` is `c_e(ℰ|_{U_k})`. -/
theorem pieceIdentityCongr_topChernClassComponent {I : Type u} (U : I → Y.Opens) (k : I) (e : ℕ)
    (hU : U k ≤ rankLocus E e)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (U k).ι).obj E) e] :
    pieceIdentityCongr C (gysinSystemOfInvertible C) sY U (opens_le_preimage_id U) (e : ℤ) k
        (pieceMap_comp_structureMorphism C sY sY (𝟙 Y) (Category.id_comp sY) U U id
          (opens_le_preimage_id U) k)
        (bivariantPieceRestrictionOfInvertible C sY sY (𝟙 Y) (Category.id_comp sY) (e : ℤ) U U id
          (opens_le_preimage_id U) k (topChernClassComponent C sY E e)) =
      GenuineChern.chernClass C ((U k).ι ≫ sY) ((Scheme.Modules.pullback (U k).ι).obj E) e
        (Fin.last e) := by
  rw [← chowCohomologyRestriction_eq_pieceIdentityCongr]
  refine BivariantClass.eq_of_idRule_eq C ((U k).ι ≫ sY) _ _ _ fun {T} g _ m β ↦ eq_of_heq ?_
  refine (BivariantClass.idRule_chowCohomologyRestriction_heq (U k).ι
    (topChernClassComponent C sY E e) g m β
    (chowGroupCongr C (Category.assoc g (U k).ι sY).symm m β)
    (chowGroupCongr_heq C _ m β).symm).trans ?_
  refine (idRule_topChernClassComponent_comp_of_le C sY E e (U k) hU g m
    (chowGroupCongr C (Category.assoc g (U k).ι sY).symm m β) β
    (chowGroupCongr_heq C _ m β).symm).trans ?_
  exact heq_of_eq (GenuineChern.idRule_chernClass C ((U k).ι ≫ sY) _ e (Fin.last e) g m β).symm

end TopChernComponent

/-! ### Pushing forward out of equal fibre products -/

/-- Proper pushforward out of the chosen fibre products `A ×_{h,X} T` and `A ×_{h',X} T` for equal
`h = h'`, along two morphisms into `B ×_{g,X} T` with the same components, of heterogeneously
equal classes, gives heterogeneously equal classes. -/
theorem properChowPushforward_pullback_heq (C : ChowSituation.{u}) {A B X T : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {h h' : A ⟶ X} (hh : h = h') (g : B ⟶ X) (t : T ⟶ X) (φ : A ⟶ B)
    [LocallyOfFiniteType (pullback.fst h t ≫ sA)] [LocallyOfFiniteType (pullback.fst h' t ≫ sA)]
    [LocallyOfFiniteType (pullback.fst g t ≫ sB)]
    (v : pullback h t ⟶ pullback g t) [IsProper v] (v' : pullback h' t ⟶ pullback g t)
    [IsProper v'] (hv₁ : v ≫ pullback.fst g t = pullback.fst h t ≫ φ)
    (hv₁' : v' ≫ pullback.fst g t = pullback.fst h' t ≫ φ)
    (hv₂ : v ≫ pullback.snd g t = pullback.snd h t)
    (hv₂' : v' ≫ pullback.snd g t = pullback.snd h' t)
    (hs : v ≫ (pullback.fst g t ≫ sB) = pullback.fst h t ≫ sA)
    (hs' : v' ≫ (pullback.fst g t ≫ sB) = pullback.fst h' t ≫ sA) {d d' : ℤ} (hd : d = d')
    (y : chowGroup C (pullback.fst h t ≫ sA) d) (y' : chowGroup C (pullback.fst h' t ≫ sA) d')
    (hy : y ≍ y') :
    properChowPushforward C _ _ v hs d (properPushforwardDescends C _ _ _ _ _) y ≍
      properChowPushforward C _ _ v' hs' d' (properPushforwardDescends C _ _ _ _ _) y' := by
  subst hh
  subst hd
  obtain rfl : v = v' := pullback.hom_ext (hv₁.trans hv₁'.symm) (hv₂.trans hv₂'.symm)
  obtain rfl := eq_of_heq hy
  rfl

/-! ### The virtual normal sheaf of a subbundle and the factorization of `C_ZX ⟶ N` -/

namespace VirtualNormalBundle

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i)
  (N' : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  (inc : N' ⟶ 𝒩.bundle) (σ' : dualSheaf N' ⟶ Stacks.Thickenings.immersionConormalSheaf i)
  (hσ : dualMap inc ≫ σ' = 𝒩.surjection)

/-- **The virtual normal sheaf `𝒩'` of Stacks 0FBL.** If `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` factors as
`𝒩^∨ ⟶ (𝒩')^∨ ⟶ 𝒞_{Z/X}` through the dual of a map `𝒩' ⟶ 𝒩` from a finite locally free module,
then `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}` is surjective because `σ` is, so `𝒩'` is a virtual normal sheaf. -/
def ofFactor : VirtualNormalBundle i where
  bundle := N'
  surjection := σ'
  epi := epi_of_epi_fac hσ

/-- The bundle of `ofFactor` is `𝒩'`. -/
@[simp]
theorem ofFactor_bundle : (𝒩.ofFactor N' inc σ' hσ).bundle = N' :=
  rfl

/-- The bundle of `ofFactor` is finite locally free of rank `n` when `𝒩'` is. -/
instance isFiniteLocallyFreeOfRank_ofFactor (n : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' n] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.ofFactor N' inc σ' hσ).bundle n :=
  h

/-- The surjection of `ofFactor` is `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}`. -/
@[simp]
theorem ofFactor_surjection : (𝒩.ofFactor N' inc σ' hσ).surjection = σ' :=
  rfl

/-- **The closed immersion `C_ZX ⟶ N` factors as `C_ZX ⟶ N' ⟶ N`**, by the factorization of
`σ` through `σ'`. -/
theorem specialFibreEmbedding_ofFactor_comp_subbundleEmbedding :
    (𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding ≫ subbundleEmbedding N' 𝒩.bundle inc =
      𝒩.specialFibreEmbedding := by
  have h : 𝒩.surjectionDegreeOne =
      dualMap inc ≫ (𝒩.ofFactor N' inc σ' hσ).surjectionDegreeOne :=
    (congrArg (· ≫ (Stacks.Conormal.immersionConormalSheafIsoDegreeOne i).hom) hσ).symm.trans
      (Category.assoc _ _ _)
  have hb : 𝒩.bundleEmbedding =
      (𝒩.ofFactor N' inc σ' hσ).bundleEmbedding ≫ subbundleEmbedding N' 𝒩.bundle inc :=
    (congrArg (fun f => (Scheme.Modules.vectorBundleMap Z f).left) h).trans
      (congrArg Over.Hom.left (Scheme.Modules.vectorBundleMap_comp Z _ _))
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hb.symm)))

section BaseChange

variable {Z' X' : Scheme.{u}} {i' : Z' ⟶ X'} [IsImmersion i'] {g : Z' ⟶ Z} {h : X' ⟶ X}
  (sq : IsPullback i' g h i)

/-- **The factorization of `σ` survives base change**: the conormal surjection of the virtual
normal sheaf `g^*𝒩` of Stacks 0FBJ factors through that of `g^*𝒩'` along the dual of
`g^*𝒩' ⟶ g^*𝒩`. -/
theorem dualMap_pullback_comp_baseChange_surjection :
    dualMap ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).map inc) ≫
        ((𝒩.ofFactor N' inc σ' hσ).baseChange i i' g h sq).surjection =
      (𝒩.baseChange i i' g h sq).surjection := by
  rw [VirtualNormalBundle.baseChange_surjection, VirtualNormalBundle.baseChange_surjection]
  set eN' := @asIso _ _ _ _ (pullbackDualMap g N')
    (pullbackDualMap_isIso g N' ‹_›)
  set eN := @asIso _ _ _ _ (pullbackDualMap g 𝒩.bundle)
    (pullbackDualMap_isIso g 𝒩.bundle 𝒩.isFiniteLocallyFree)
  have hnat := pullbackDualMap_naturality' g inc
  have hinv : dualMap ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).map inc) ≫
      eN'.inv = eN.inv ≫
        (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).map (dualMap inc) :=
    ((Iso.inv_comp_eq eN).2 (((Iso.eq_comp_inv eN').2 hnat).trans (Category.assoc _ _ _))).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hinv).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (eN.inv ≫ ·) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (((RingedSpaceModuleAdjunction.modulePullback
    g.toLRSHom.toShHom).map_comp _ _).symm.trans (congrArg _ hσ))

/-- **The virtual normal sheaf `g^*𝒩'` of the base change is the subbundle sheaf of `g^*𝒩`**
attached to the pulled back factorization. -/
theorem ofFactor_baseChange :
    (𝒩.ofFactor N' inc σ' hσ).baseChange i i' g h sq =
      (𝒩.baseChange i i' g h sq).ofFactor
        ((𝒩.ofFactor N' inc σ' hσ).baseChange i i' g h sq).bundle
        ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).map inc)
        ((𝒩.ofFactor N' inc σ' hσ).baseChange i i' g h sq).surjection
        (𝒩.dualMap_pullback_comp_baseChange_surjection N' inc σ' hσ sq) :=
  rfl

end BaseChange

/-- The embedding `N' ⟶ N` is a morphism over `Z`. -/
theorem subbundleEmbedding_comp_proj :
    subbundleEmbedding N' 𝒩.bundle inc ≫ 𝒩.proj = (𝒩.ofFactor N' inc σ' hσ).proj :=
  subbundleEmbedding_comp_dualVectorBundleToBase N' 𝒩.bundle inc

/-- The base change `N' ×_X T ⟶ N ×_X T` of the embedding along a test scheme `t : T ⟶ X`. -/
abbrev subbundleTestMap {T : Scheme.{u}} (t : T ⟶ X) :
    pullback ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t ⟶ pullback (𝒩.proj ≫ i) t :=
  subbundleTestBaseChange i 𝒩.proj (subbundleEmbedding N' 𝒩.bundle inc)
    (𝒩.subbundleEmbedding_comp_proj N' inc σ' hσ) t

section Pushforward

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (hZ : i ≫ sX = sZ) (r r' : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  (E : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (pr : 𝒩.bundle ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

include hseq in
/-- The base change of the embedding along a test scheme is a closed immersion. -/
theorem isClosedImmersion_subbundleTestMap {T : Scheme.{u}} (t : T ⟶ X) :
    IsClosedImmersion (𝒩.subbundleTestMap N' inc σ' hσ t) :=
  @isClosedImmersion_subbundleTestBaseChange _ _ _ _ i 𝒩.proj _
    (subbundleEmbedding N' 𝒩.bundle inc)
    (isClosedImmersion_subbundleEmbedding_of_shortExact N' 𝒩.bundle E inc pr w hseq)
    (𝒩.subbundleEmbedding_comp_proj N' inc σ' hσ) _ t

include hseq in
/-- **`ι_* ∘ j^* ∘ C` for `𝒩` is `j_*` of `ι'_* ∘ j^* ∘ C` for `𝒩'`**, on every test scheme:
the closed immersion `C_ZX ⟶ N` is `C_ZX ⟶ N' ⟶ N`, and proper pushforward is functorial. -/
theorem pushforwardClass_cap_heq_ofFactor {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    haveI := 𝒩.locallyOfFiniteType_projection r
    haveI := (𝒩.ofFactor N' inc σ' hσ).locallyOfFiniteType_projection r'
    haveI := 𝒩.isClosedImmersion_subbundleTestMap N' inc σ' hσ E pr w hseq t
    (𝒩.pushforwardClass C sX sZ hZ r).cap t k α ≍
      properChowPushforward C
        (pullback.fst ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t ≫
          ((𝒩.ofFactor N' inc σ' hσ).proj ≫ sZ))
        (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ sZ)) (𝒩.subbundleTestMap N' inc σ' hσ t)
        (subbundleTestBaseChange_comp_structureMorphism i 𝒩.proj sZ _ _ rfl rfl
          (subbundleEmbedding N' 𝒩.bundle inc) (𝒩.subbundleEmbedding_comp_proj N' inc σ' hσ) t)
        (k - (-(r' : ℤ) + r')) (properPushforwardDescends C _ _ _ _ _)
        (((𝒩.ofFactor N' inc σ' hσ).pushforwardClass C sX sZ hZ r').cap t k α) := by
  have := 𝒩.locallyOfFiniteType_projection r
  have := (𝒩.ofFactor N' inc σ' hσ).locallyOfFiniteType_projection r'
  have := 𝒩.isClosedImmersion_subbundleTestMap N' inc σ' hσ E pr w hseq t
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have hfac := 𝒩.specialFibreEmbedding_ofFactor_comp_subbundleEmbedding N' inc σ' hσ
  have hh : 𝒩.specialFibreEmbedding ≫ (𝒩.proj ≫ i) =
      (𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding ≫ ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) :=
    𝒩.specialFibreEmbedding_projection_comp.trans
      (𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding_projection_comp.symm
  -- the inner classes at infinity
  set σ₁ := BivariantClass.copy C (canonicalGysinSystem C) _ sX
    (𝒩.specialFibreEmbedding_projection_comp).symm (Category.assoc _ _ _)
    (comp_comp_structureMorphism_eq (𝒩.specialFibreEmbedding_comp_structure C sX sZ hZ)
      (𝒩.projection_comp_structure C sX sZ hZ)) rfl (Stacks.Deformation.normalConeClass C sX i)
  set σ₂ := BivariantClass.copy C (canonicalGysinSystem C) _ sX
    ((𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding_projection_comp).symm (Category.assoc _ _ _)
    (comp_comp_structureMorphism_eq
      ((𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding_comp_structure C sX sZ hZ)
      ((𝒩.ofFactor N' inc σ' hσ).projection_comp_structure C sX sZ hZ)) rfl
    (Stacks.Deformation.normalConeClass C sX i)
  have hL : (𝒩.pushforwardClass C sX sZ hZ r).cap t k α ≍
      properChowPushforward C _ _
        (bivariantPushforwardBaseChange 𝒩.specialFibreEmbedding (𝒩.proj ≫ i) t)
        (bivariantPushforwardBaseChange_comp_structure
          (𝒩.specialFibreEmbedding_comp_structure C sX sZ hZ) (𝒩.proj ≫ i) t)
        (k - 0) (properPushforwardDescends C _ _ _ _ _) (σ₁.cap t k α) :=
    BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α
  have hR : ((𝒩.ofFactor N' inc σ' hσ).pushforwardClass C sX sZ hZ r').cap t k α ≍
      properChowPushforward C _ _
        (bivariantPushforwardBaseChange (𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding
          ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t)
        (bivariantPushforwardBaseChange_comp_structure
          ((𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding_comp_structure C sX sZ hZ)
          ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t)
        (k - 0) (properPushforwardDescends C _ _ _ _ _) (σ₂.cap t k α) :=
    BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α
  have hRHS := DFunLike.congr_fun (properChowPushforward_comp C _ _ _
    (bivariantPushforwardBaseChange (𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding
      ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t) (𝒩.subbundleTestMap N' inc σ' hσ t)
    (bivariantPushforwardBaseChange_comp_structure
      ((𝒩.ofFactor N' inc σ' hσ).specialFibreEmbedding_comp_structure C sX sZ hZ)
      ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t)
    (subbundleTestBaseChange_comp_structureMorphism i 𝒩.proj sZ _ _ rfl rfl
      (subbundleEmbedding N' 𝒩.bundle inc) (𝒩.subbundleEmbedding_comp_proj N' inc σ' hσ) t)
    (k - 0) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)) (σ₂.cap t k α)
  refine hL.trans (HEq.trans ?_ (properChowPushforward_heq_congr C _ _ _ _ (by ring)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _ hR).symm)
  refine HEq.trans ?_ (heq_of_eq hRHS).symm
  refine properChowPushforward_pullback_heq C _ _ hh (𝒩.proj ≫ i) t 𝒩.specialFibreEmbedding _ _
    (bivariantPushforwardBaseChange_fst _ _ _) ?_ (bivariantPushforwardBaseChange_snd _ _ _) ?_
    _ _ rfl _ _ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (subbundleTestBaseChange_fst _ _ _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ subbundleEmbedding N' 𝒩.bundle inc)
        (bivariantPushforwardBaseChange_fst _ _ _)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hfac)))))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (subbundleTestBaseChange_snd _ _ _ _ _)).trans
        (bivariantPushforwardBaseChange_snd _ _ _))
  · exact (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans
      (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).symm

end Pushforward


section Main

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (r' e : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  (E : Z.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (pr : 𝒩.bundle ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- Capping with the composite `c_e(ℰ) ∘ c'` of Stacks 0B75, read in degree `r' + e`, is capping
with `c'` followed by `c_e(ℰ)` on the middle fibre product. -/
private theorem cap_bivariantClassCongrDeg_composite_heq_chernCap (C : ChowSituation.{u})
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r' e : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
    (c' : BivariantClass C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl r') {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (bivariantClassCongrDeg C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl
      (by push_cast; ring : (r' : ℤ) + e = ((r' + e : ℕ) : ℤ))
      (bivariantCompositeIdLeftHom C (gysinSystemOfInvertible C) sX i
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) e r' c'
        (GenuineChern.chernClass C (i ≫ sX) E e (Fin.last e)))).cap t k α ≍
      GenuineChern.chernCap C e (pullback.fst i t ≫ (i ≫ sX))
        ((Scheme.Modules.pullback (pullback.fst i t)).obj E) (k - r') (Fin.last e)
        (c'.cap t k α) := by
  rw [bivariantClassCongrDeg_cap]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (bivariantCompositeIdLeftHom_cap_heq_idRule C (gysinSystemOfInvertible C) sX i
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) e r' c'
    (GenuineChern.chernClass C (i ≫ sX) E e (Fin.last e)) t k α).trans (heq_of_eq ?_)
  exact GenuineChern.idRule_chernClass C (i ≫ sX) E e (Fin.last e) (pullback.fst i t) (k - r')
    (c'.cap t k α)

include hseq in
/-- **Stacks 0FBL, constant ranks.** Let `i : Z ⟶ X` be an immersion with virtual normal sheaf
`𝒩`, let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_Z`-modules,
`𝒩'` of rank `r'` and `ℰ` of rank `e`, and let `σ' : (𝒩')^∨ ⟶ 𝒞_{Z/X}` with
`σ = σ' ∘ (𝒩^∨ ⟶ (𝒩')^∨)`. Then

  `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')`   in   `A^{r'+e}(Z ⟶ X)`,

where `c_e(ℰ) = c_top(ℰ)` is the top Chern class of `ℰ` (Stacks 0B7H, 0FA4). -/
theorem virtualNormalClass_eq_chernClass_comp :
    haveI := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
    𝒩.virtualNormalClass C sX (i ≫ sX) rfl (r' + e) =
      bivariantClassCongrDeg C (gysinSystemOfInvertible C) (i ≫ sX) sX i rfl
        (by push_cast; ring)
        (bivariantCompositeIdLeftHom C (gysinSystemOfInvertible C) sX i
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) e r'
          ((𝒩.ofFactor N' inc σ' hσ).virtualNormalClass C sX (i ≫ sX) rfl r')
          (GenuineChern.chernClass C (i ≫ sX) E e (Fin.last e))) := by
  have := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
  have := 𝒩.locallyOfFiniteType_projection (r' + e)
  have := 𝒩.flat_projection (r' + e)
  have := (𝒩.ofFactor N' inc σ' hσ).locallyOfFiniteType_projection r'
  have := (𝒩.ofFactor N' inc σ' hσ).flat_projection r'
  have := locallyOfFiniteType_dualVectorBundleToBase N' r'
  have := locallyOfFiniteType_dualVectorBundleToBase 𝒩.bundle (r' + e)
  refine (𝒩.eq_virtualNormalClass C sX (i ≫ sX) rfl (r' + e) _ ?_).symm
  rw [isBivariantClassComposition_iff]
  intro T t _ k α
  have := 𝒩.isClosedImmersion_subbundleTestMap N' inc σ' hσ E pr w hseq t
  refine eq_of_heq ((chowGroupDegreeEquiv_heq C _ _ _).trans ?_)
  refine (𝒩.pushforwardClass_cap_heq_ofFactor N' inc σ' hσ C sX (i ≫ sX) rfl (r' + e) r' E pr w
    hseq t k α).trans ?_
  set c' := (𝒩.ofFactor N' inc σ' hσ).virtualNormalClass C sX (i ≫ sX) rfl r'
  have h1 := (𝒩.ofFactor N' inc σ' hσ).middleCap_virtualNormalClass_cap C sX (i ≫ sX) rfl r' t k α
  have h2 := properChowPushforward_heq_congr C
    (pullback.fst ((𝒩.ofFactor N' inc σ' hσ).proj ≫ i) t ≫
      ((𝒩.ofFactor N' inc σ' hσ).proj ≫ (i ≫ sX)))
    (pullback.fst (𝒩.proj ≫ i) t ≫ (𝒩.proj ≫ (i ≫ sX))) (𝒩.subbundleTestMap N' inc σ' hσ t)
    (subbundleTestBaseChange_comp_structureMorphism i 𝒩.proj (i ≫ sX) _ _ rfl rfl
      (subbundleEmbedding N' 𝒩.bundle inc) (𝒩.subbundleEmbedding_comp_proj N' inc σ' hσ) t)
    (by ring : k - (-(r' : ℤ) + r') = k - r' - -(r' : ℤ))
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) _ _
    ((chowGroupDegreeEquiv_heq C _ _ _).symm.trans (heq_of_eq h1.symm))
  refine h2.trans ?_
  refine (subbundleTestEmbedding_middleCap i inc C (i ≫ sX) E r' e pr w hseq t (k - r')
    (c'.cap t k α)).trans ?_
  exact middleCap_heq_congr C _ _ _ _ _ _ _ t (by push_cast; ring)
    (cap_bivariantClassCongrDeg_composite_heq_chernCap C sX E r' e c' t k α).symm

include hseq in
/-- **Stacks 0FBL, constant ranks**, with the composite of Stacks 0B75 written as a class for
`𝟙 Z ≫ i` and read at `i`: for any structure morphism `s_Z` of `Z` with `i ≫ s_X = s_Z`,

  `c(Z ⟶ X, 𝒩) = c_e(ℰ) ∘ c(Z ⟶ X, 𝒩')`   in   `A^{r'+e}(Z ⟶ X)`. -/
theorem virtualNormalClass_eq_composite (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (hZ : i ≫ sX = sZ) :
    haveI := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
    𝒩.virtualNormalClass C sX sZ hZ (r' + e) =
      BivariantClass.copy C (gysinSystemOfInvertible C) sZ sX (Category.id_comp i)
        (comp_comp_structureMorphism_eq (Category.id_comp sZ) hZ) hZ (by push_cast; ring)
        (bivariantCompositeOfInvertible C sZ sZ sX (𝟙 Z) i (Category.id_comp sZ) hZ e r'
          (GenuineChern.chernClass C sZ E e (Fin.last e))
          ((𝒩.ofFactor N' inc σ' hσ).virtualNormalClass C sX sZ hZ r')) := by
  subst hZ
  have := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
  rw [𝒩.virtualNormalClass_eq_chernClass_comp N' inc σ' hσ C sX r' e E pr w hseq]
  refine BivariantClass.ext C _ _ _ _ _ _ fun {T} t _ k α ↦ eq_of_heq ?_
  rw [bivariantClassCongrDeg_cap]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine (bivariantCompositeIdLeftHom_cap C (gysinSystemOfInvertible C) sX i
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) e r' _ _ t k α).trans ?_
  refine HEq.trans ?_ (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).symm
  exact (chowGroupDegreeEquiv_heq C _ _ _).symm

include hseq in
/-- **Stacks 0FBL, constant ranks, on cap operations**: for every test scheme `t : T ⟶ X` and
`α ∈ A_k(T)`,

  `c(Z ⟶ X, 𝒩) ∩ α = c_e(ℰ) ∩ (c(Z ⟶ X, 𝒩') ∩ α)`   in   `A_*(Z ×_X T)`. -/
theorem virtualNormalClass_cap_heq_chernCap (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (hZ : i ≫ sX = sZ) {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    haveI := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
    (𝒩.virtualNormalClass C sX sZ hZ (r' + e)).cap t k α ≍
      GenuineChern.chernCap C e (pullback.fst i t ≫ sZ)
        ((Scheme.Modules.pullback (pullback.fst i t)).obj E) (k - r') (Fin.last e)
        (((𝒩.ofFactor N' inc σ' hσ).virtualNormalClass C sX sZ hZ r').cap t k α) := by
  subst hZ
  have := isFiniteLocallyFreeOfRank_middle N' 𝒩.bundle E r' e inc pr w hseq
  rw [𝒩.virtualNormalClass_eq_chernClass_comp N' inc σ' hσ C sX r' e E pr w hseq]
  exact cap_bivariantClassCongrDeg_composite_heq_chernCap C sX E r' e _ t k α

end Main

end VirtualNormalBundle

end Stacks.Chow

end
