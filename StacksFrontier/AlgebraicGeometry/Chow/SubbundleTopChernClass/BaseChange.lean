module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionFlatCommute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactLocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The class of a subbundle, after base change

Let `X` be a scheme locally of finite type over the base of chapter 42, let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules and let
`i : N' ⟶ N` be the closed embedding of the vector bundles `N' = 𝐕((𝒩')^∨)` and `N = 𝐕(𝒩^∨)` of
[Stacks, Tag 0FAA]. For a morphism `t : W ⟶ X` locally of finite type, the base change
`i_W : N' ×_X W ⟶ N ×_X W` is identified with the closed embedding of the vector bundles of the
pulled-back sequence `0 ⟶ t^*𝒩' ⟶ t^*𝒩 ⟶ t^*ℰ ⟶ 0`, which is short exact because `ℰ` is finite
locally free. So [Stacks, Tag 0FAA] holds on `W` for the base-changed bundles: for
`β ∈ CH_k(W)`,

  `(i_W)_* (p'_W)^* β = p_W^*(c_top(t^*ℰ) ∩ β)`,

where `p_W : N ×_X W ⟶ W` and `p'_W : N' ×_X W ⟶ W` are the base changes of the projections.

For the inclusion `j : U ⟶ X` of an open subscheme the identification `N ×_X U ≅ 𝐕((𝒩|_U)^∨)`
identifies the part `p⁻¹(U)` of `N` lying over `U` with the vector bundle of `𝒩|_U`, compatibly
with the embedding of a subbundle; on a locus where `𝒩` has constant rank `r` the restricted
projection `p⁻¹(U) ⟶ X` is therefore flat of relative dimension `r`.

## Main definitions

* `Stacks.Chow.subbundleEmbeddingPullbackMap` — the base change `N' ×_X W ⟶ N ×_X W` of `i`.
* `Stacks.Chow.dualVectorBundlePullbackIso` — `𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)`, over `W`.
* `Stacks.Chow.dualVectorBundleRestrictIso` — `p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)` for an open `U ⊆ X`.
* `Stacks.Chow.subbundleEmbeddingRestrict` — the embedding `p'⁻¹(U) ⟶ p⁻¹(U)` of the parts of
  the two bundles of a subbundle lying over `U`.

## Main results

* `Stacks.Chow.subbundleEmbeddingPullbackMap_comp_dualVectorBundlePullbackIso_hom` — the
  identification carries `i_W` to the closed embedding of the pulled-back sequence.
* `Stacks.Chow.subbundleEmbeddingPullbackMap_pushforward_flatPullback_eq_topChernCap` —
  [Stacks, Tag 0FAA] for the base-changed bundles.
* `Stacks.Chow.subbundleEmbeddingRestrict_comp_dualVectorBundleRestrictIso_hom` — over an open
  `U ⊆ X` the restricted embedding is the embedding of the restricted subbundle.
* `Stacks.Chow.relativeDimension_dualVectorBundleRestrict` — on a locus of constant rank `r` the
  restricted projection `p⁻¹(U) ⟶ X` has relative dimension `r`.

## Implementation notes

The identification `𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)` is the base change of the vector bundle
(`AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackOverIso`) followed by the vector bundle of
the dual base-change isomorphism `t^*(𝒩^∨) ≅ (t^*𝒩)^∨`; both are natural in the module
(`AlgebraicGeometry.Scheme.Modules.vectorBundlePullbackOverIso_hom_naturality` and
`Stacks.Chow.pullbackDualMap_naturality`), which is what makes the identification compatible with
the two embeddings.

The two sides lie in `CH_{k+r'}` and `CH_{(k-e)+r}` of `N ×_X W`, identified as in
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_chernCap_of_point` through
`r = r' + e`, read at a point of `X`; when `W` is empty both groups vanish.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The base change of the embedding of a subbundle -/

section Embedding

variable {X W : Scheme.{u}} (N' N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (t : W ⟶ X)

/-- **The base change `N' ×_X W ⟶ N ×_X W` of the morphism `i : N' ⟶ N` of [Stacks, Tag 0FAA]**
along `t : W ⟶ X`: it is `i` on the first factor and the identity on the second. -/
def subbundleEmbeddingPullbackMap (inc : N' ⟶ N) :
    pullback (dualVectorBundleToBase N') t ⟶ pullback (dualVectorBundleToBase N) t :=
  pullback.lift (pullback.fst _ _ ≫ subbundleEmbedding N' N inc) (pullback.snd _ _) <| by
    rw [Category.assoc, subbundleEmbedding_comp_dualVectorBundleToBase]
    exact pullback.condition

/-- The first projection of the base change of `i` is `i` composed with the first projection. -/
@[reassoc (attr := simp)]
theorem subbundleEmbeddingPullbackMap_fst (inc : N' ⟶ N) :
    subbundleEmbeddingPullbackMap N' N t inc ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ subbundleEmbedding N' N inc :=
  pullback.lift_fst _ _ _

/-- The base change of `i` commutes with the second projections to `W`. -/
@[reassoc (attr := simp)]
theorem subbundleEmbeddingPullbackMap_snd (inc : N' ⟶ N) :
    subbundleEmbeddingPullbackMap N' N t inc ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The base change of `i` is the base change, over `X`, of the morphism `𝐕(𝒩^∨ ⟶ (𝒩')^∨)` of
schemes over `X`. -/
theorem subbundleEmbeddingPullbackMap_eq (inc : N' ⟶ N) :
    subbundleEmbeddingPullbackMap N' N t inc =
      ((Over.pullback t).map (Scheme.Modules.vectorBundleMap X (dualMap inc))).left :=
  rfl

/-- The base change of `i` is a base change of `i` in the categorical sense. -/
theorem isPullback_subbundleEmbeddingPullbackMap (inc : N' ⟶ N) :
    IsPullback (pullback.fst _ _) (subbundleEmbeddingPullbackMap N' N t inc)
      (subbundleEmbedding N' N inc) (pullback.fst (dualVectorBundleToBase N) t) := by
  have hs : IsPullback (pullback.fst (dualVectorBundleToBase N') t)
      (subbundleEmbeddingPullbackMap N' N t inc ≫ pullback.snd _ _)
      (subbundleEmbedding N' N inc ≫ dualVectorBundleToBase N) t := by
    rw [subbundleEmbedding_comp_dualVectorBundleToBase, subbundleEmbeddingPullbackMap_snd]
    exact IsPullback.of_hasPullback _ t
  exact hs.of_bot (subbundleEmbeddingPullbackMap_fst N' N t inc).symm
    (IsPullback.of_hasPullback _ t)

/-- **The base change of the closed embedding of [Stacks, Tag 0FAA] is a closed immersion.** -/
theorem isClosedImmersion_subbundleEmbeddingPullbackMap (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (inc : N' ⟶ N)
    (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact) :
    IsClosedImmersion (subbundleEmbeddingPullbackMap N' N t inc) :=
  have := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
  MorphismProperty.of_isPullback (isPullback_subbundleEmbeddingPullbackMap N' N t inc)
    (P := @IsClosedImmersion) inferInstance

end Embedding

/-! ### The base change of the vector bundle of a dual -/

section BundleIso

variable {X W : Scheme.{u}} (t : W ⟶ X)

/-- The pullback of a finite locally free module is finite locally free. -/
instance isFiniteLocallyFree_pullback_obj (N : X.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback t).obj N) :=
  isFiniteLocallyFree_pullback t N hN

/-- **The vector bundle of the dual commutes with base change**, over `W`:
`𝐕(𝒩^∨) ×_X W ≅ 𝐕(t^*(𝒩^∨)) ≅ 𝐕((t^*𝒩)^∨)`, the second identification being the vector bundle
of the dual base-change isomorphism `t^*(𝒩^∨) ≅ (t^*𝒩)^∨` of [Stacks, Tag 0GMX]. -/
@[ega "IV 18.5.1" "partial"]
def dualVectorBundlePullbackOverIso (N : X.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    (Over.pullback t).obj (Scheme.Modules.vectorBundleOver X (F := dualSheaf N)) ≅
      Scheme.Modules.vectorBundleOver W (F := dualSheaf ((Scheme.Modules.pullback t).obj N)) :=
  Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N) ≪≫
    ({ hom := Scheme.Modules.vectorBundleMap W
         (F := dualSheaf ((Scheme.Modules.pullback t).obj N))
         (G := (Scheme.Modules.pullback t).obj (dualSheaf N))
         (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).inv
       inv := Scheme.Modules.vectorBundleMap W
         (F := (Scheme.Modules.pullback t).obj (dualSheaf N))
         (G := dualSheaf ((Scheme.Modules.pullback t).obj N))
         (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).hom
       hom_inv_id := (Scheme.Modules.vectorBundleMap_comp W
           (F := (Scheme.Modules.pullback t).obj (dualSheaf N))
           (G := dualSheaf ((Scheme.Modules.pullback t).obj N))
           (H := (Scheme.Modules.pullback t).obj (dualSheaf N))
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).hom
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).inv).symm.trans
         ((congrArg (Scheme.Modules.vectorBundleMap W
             (F := (Scheme.Modules.pullback t).obj (dualSheaf N))
             (G := (Scheme.Modules.pullback t).obj (dualSheaf N)))
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).hom_inv_id).trans
           (Scheme.Modules.vectorBundleMap_id W
             (F := (Scheme.Modules.pullback t).obj (dualSheaf N))))
       inv_hom_id := (Scheme.Modules.vectorBundleMap_comp W
           (F := dualSheaf ((Scheme.Modules.pullback t).obj N))
           (G := (Scheme.Modules.pullback t).obj (dualSheaf N))
           (H := dualSheaf ((Scheme.Modules.pullback t).obj N))
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).inv
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).hom).symm.trans
         ((congrArg (Scheme.Modules.vectorBundleMap W
             (F := dualSheaf ((Scheme.Modules.pullback t).obj N))
             (G := dualSheaf ((Scheme.Modules.pullback t).obj N)))
           (Stacks.FundamentalGroup.pullbackDualSheafIso t N hN).inv_hom_id).trans
           (Scheme.Modules.vectorBundleMap_id W
             (F := dualSheaf ((Scheme.Modules.pullback t).obj N)))) } :
      Scheme.Modules.vectorBundleOver W (F := (Scheme.Modules.pullback t).obj (dualSheaf N)) ≅
        Scheme.Modules.vectorBundleOver W (F := dualSheaf ((Scheme.Modules.pullback t).obj N)))

/-- **`𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)`**, on underlying schemes. -/
def dualVectorBundlePullbackIso (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    pullback (dualVectorBundleToBase N) t ≅ dualVectorBundle ((Scheme.Modules.pullback t).obj N) :=
  (Over.forget W).mapIso (dualVectorBundlePullbackOverIso t N)

/-- The identification `𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)` is one of schemes over `W`. -/
@[reassoc (attr := simp)]
theorem dualVectorBundlePullbackIso_hom_comp_dualVectorBundleToBase (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    (dualVectorBundlePullbackIso t N).hom ≫
        dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) =
      pullback.snd (dualVectorBundleToBase N) t :=
  Over.w (dualVectorBundlePullbackOverIso t N).hom

/-- **The identification carries the base change of `i` to the closed embedding of the
pulled-back sequence.** -/
theorem subbundleEmbeddingPullbackMap_comp_dualVectorBundlePullbackIso_hom (N' N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (inc : N' ⟶ N) :
    subbundleEmbeddingPullbackMap N' N t inc ≫ (dualVectorBundlePullbackIso t N).hom =
      (dualVectorBundlePullbackIso t N').hom ≫
        subbundleEmbedding ((Scheme.Modules.pullback t).obj N')
          ((Scheme.Modules.pullback t).obj N) ((Scheme.Modules.pullback t).map inc) := by
  have hdual : (Stacks.FundamentalGroup.pullbackDualSheafIso t N inferInstance).inv ≫
        (Scheme.Modules.pullback t).map (dualMap inc) =
      dualMap ((Scheme.Modules.pullback t).map inc) ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso t N' inferInstance).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact pullbackDualMap_naturality t inc
  have hover : (Over.pullback t).map (Scheme.Modules.vectorBundleMap X (dualMap inc)) ≫
        (Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N)).hom ≫
          Scheme.Modules.vectorBundleMap W
            (Stacks.FundamentalGroup.pullbackDualSheafIso t N inferInstance).inv =
      (Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N')).hom ≫
        Scheme.Modules.vectorBundleMap W
            (Stacks.FundamentalGroup.pullbackDualSheafIso t N' inferInstance).inv ≫
          Scheme.Modules.vectorBundleMap W (dualMap ((Scheme.Modules.pullback t).map inc)) := by
    have hnat := Scheme.Modules.vectorBundlePullbackOverIso_hom_naturality t (dualMap inc)
    have hcomp : Scheme.Modules.vectorBundleMap W ((Scheme.Modules.pullback t).map (dualMap inc)) ≫
          Scheme.Modules.vectorBundleMap W
            (Stacks.FundamentalGroup.pullbackDualSheafIso t N inferInstance).inv =
        Scheme.Modules.vectorBundleMap W
            (Stacks.FundamentalGroup.pullbackDualSheafIso t N' inferInstance).inv ≫
          Scheme.Modules.vectorBundleMap W (dualMap ((Scheme.Modules.pullback t).map inc)) :=
      (Scheme.Modules.vectorBundleMap_comp W _ _).symm.trans
        ((congrArg (Scheme.Modules.vectorBundleMap W) hdual).trans
          (Scheme.Modules.vectorBundleMap_comp W _ _))
    calc _ = ((Over.pullback t).map (Scheme.Modules.vectorBundleMap X (dualMap inc)) ≫
          (Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N)).hom) ≫
            Scheme.Modules.vectorBundleMap W
              (Stacks.FundamentalGroup.pullbackDualSheafIso t N inferInstance).inv :=
          (Category.assoc _ _ _).symm
      _ = _ := by rw [hnat, Category.assoc, hcomp]
  have h2 := congrArg CommaMorphism.left hover
  simp only [Over.comp_left] at h2
  have e1 : (dualVectorBundlePullbackIso t N).hom =
      (Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N)).hom.left ≫
        (Scheme.Modules.vectorBundleMap W
          (Stacks.FundamentalGroup.pullbackDualSheafIso t N inferInstance).inv).left := rfl
  have e2 : (dualVectorBundlePullbackIso t N').hom =
      (Scheme.Modules.vectorBundlePullbackOverIso t (dualSheaf N')).hom.left ≫
        (Scheme.Modules.vectorBundleMap W
          (Stacks.FundamentalGroup.pullbackDualSheafIso t N' inferInstance).inv).left := rfl
  rw [e1, e2, subbundleEmbeddingPullbackMap_eq]
  refine Eq.trans ?_ (h2.trans ?_)
  · rfl
  · refine (Category.assoc _ _ _).symm.trans ?_
    rfl

/-- The inverse form of the compatibility of the base change of `i` with the identification
`𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)`. -/
private theorem dualVectorBundlePullbackIso_inv_comp_subbundleEmbeddingPullbackMap
    (N' N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (inc : N' ⟶ N) :
    (dualVectorBundlePullbackIso t N').inv ≫ subbundleEmbeddingPullbackMap N' N t inc =
      subbundleEmbedding ((Scheme.Modules.pullback t).obj N') ((Scheme.Modules.pullback t).obj N)
          ((Scheme.Modules.pullback t).map inc) ≫ (dualVectorBundlePullbackIso t N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← subbundleEmbeddingPullbackMap_comp_dualVectorBundlePullbackIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end BundleIso

/-! ### Restriction to an open subscheme of the base -/

section Restrict

variable {X : Scheme.{u}} (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (U : X.Opens)

/-- **The part of `N = 𝐕(𝒩^∨)` over an open `U ⊆ X` is the vector bundle of `𝒩|_U`**:
`p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)`, the open subscheme `p⁻¹(U)` being the base change `N ×_X U`. -/
def dualVectorBundleRestrictIso :
    ((dualVectorBundleToBase N ⁻¹ᵁ U : (dualVectorBundle N).Opens) : Scheme.{u}) ≅
      dualVectorBundle ((Scheme.Modules.pullback U.ι).obj N) :=
  (isPullback_morphismRestrict (dualVectorBundleToBase N) U).flip.isoPullback ≪≫
    dualVectorBundlePullbackIso U.ι N

/-- The identification `p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)` is one over `U`. -/
@[reassoc (attr := simp)]
theorem dualVectorBundleRestrictIso_hom_comp :
    (dualVectorBundleRestrictIso N U).hom ≫
        dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N) =
      dualVectorBundleToBase N ∣_ U := by
  rw [dualVectorBundleRestrictIso, Iso.trans_hom, Category.assoc,
    dualVectorBundlePullbackIso_hom_comp_dualVectorBundleToBase, IsPullback.isoPullback_hom_snd]

/-- The inverse of `p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)` followed by the inclusion of `p⁻¹(U)` into `N` is the
projection of the base change. -/
@[reassoc]
theorem dualVectorBundleRestrictIso_inv_ι :
    (dualVectorBundleRestrictIso N U).inv ≫ (dualVectorBundleToBase N ⁻¹ᵁ U).ι =
      (dualVectorBundlePullbackIso U.ι N).inv ≫ pullback.fst (dualVectorBundleToBase N) U.ι := by
  rw [dualVectorBundleRestrictIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst]

/-- The restriction of the projection `p : N ⟶ X` to the part `p⁻¹(U)` lying over `U`, read
through `p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)`: it is the projection of `𝐕((𝒩|_U)^∨)` followed by the
inclusion of `U`. -/
theorem ι_comp_dualVectorBundleToBase_eq :
    (dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N =
      (dualVectorBundleRestrictIso N U).hom ≫
        dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N) ≫ U.ι := by
  rw [dualVectorBundleRestrictIso_hom_comp_assoc, morphismRestrict_ι]

/-- On a locus where `𝒩` has constant rank, the restricted projection `p⁻¹(U) ⟶ X` is locally
of finite type. -/
theorem locallyOfFiniteType_dualVectorBundleRestrict (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj N) r] :
    LocallyOfFiniteType ((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) := by
  have := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback U.ι).obj N) r
  rw [ι_comp_dualVectorBundleToBase_eq]
  infer_instance

/-- On a locus where `𝒩` has constant rank, the restricted projection `p⁻¹(U) ⟶ X` is flat. -/
theorem flat_dualVectorBundleRestrict (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj N) r] :
    Flat ((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) := by
  have := dualVectorBundleToBase_flat ((Scheme.Modules.pullback U.ι).obj N) r
  rw [ι_comp_dualVectorBundleToBase_eq]
  infer_instance

/-- **On a locus where `𝒩` has constant rank `r`, the restricted projection `p⁻¹(U) ⟶ X` has
relative dimension `r`.** -/
theorem relativeDimension_dualVectorBundleRestrict (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj N) r] :
    letI := locallyOfFiniteType_dualVectorBundleRestrict N U r
    AlgebraicGeometry.RelativeDimension
      ((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N) r := by
  have := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback U.ι).obj N) r
  have := dualVectorBundleToBase_flat ((Scheme.Modules.pullback U.ι).obj N) r
  have h1 := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (dualVectorBundleToBase ((Scheme.Modules.pullback U.ι).obj N)) U.ι
    (dualVectorBundleToBase_relativeDimension ((Scheme.Modules.pullback U.ι).obj N) r)
    (relativeDimension_of_isOpenImmersion U.ι)
  have h2 := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (dualVectorBundleRestrictIso N U).hom _
    (relativeDimension_of_isOpenImmersion (dualVectorBundleRestrictIso N U).hom) h1
  simp only [add_zero, zero_add] at h2
  convert h2 using 1
  exact ι_comp_dualVectorBundleToBase_eq N U

end Restrict

/-! ### The embedding of a subbundle over an open subscheme of the base -/

section SubbundleRestrict

variable {X : Scheme.{u}} (N' N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  (inc : N' ⟶ N) (U : X.Opens)

/-- The part `p'⁻¹(U)` of `N'` over `U` is mapped into the part `p⁻¹(U)` of `N` by the
embedding `i : N' ⟶ N`. -/
theorem preimage_le_preimage_subbundleEmbedding :
    dualVectorBundleToBase N' ⁻¹ᵁ U ≤
      subbundleEmbedding N' N inc ⁻¹ᵁ (dualVectorBundleToBase N ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, subbundleEmbedding_comp_dualVectorBundleToBase]

/-- **The embedding `p'⁻¹(U) ⟶ p⁻¹(U)`** of the parts over an open `U ⊆ X` of the two bundles of
a subbundle `𝒩' ⟶ 𝒩`: the restriction of `i : N' ⟶ N`. -/
def subbundleEmbeddingRestrict :
    ((dualVectorBundleToBase N' ⁻¹ᵁ U : (dualVectorBundle N').Opens) : Scheme.{u}) ⟶
      ((dualVectorBundleToBase N ⁻¹ᵁ U : (dualVectorBundle N).Opens) : Scheme.{u}) :=
  (subbundleEmbedding N' N inc).resLE _ _ (preimage_le_preimage_subbundleEmbedding N' N inc U)

/-- The restricted embedding composed with the inclusion `p⁻¹(U) ⟶ 𝐕(𝒩^∨)` is the inclusion
`p'⁻¹(U) ⟶ 𝐕((𝒩')^∨)` composed with `i`. -/
@[reassoc (attr := simp)]
theorem subbundleEmbeddingRestrict_ι :
    subbundleEmbeddingRestrict N' N inc U ≫ (dualVectorBundleToBase N ⁻¹ᵁ U).ι =
      (dualVectorBundleToBase N' ⁻¹ᵁ U).ι ≫ subbundleEmbedding N' N inc :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The restricted embedding is a morphism over `X`. -/
theorem subbundleEmbeddingRestrict_comp_base {Y : Scheme.{u}} (q : X ⟶ Y) :
    subbundleEmbeddingRestrict N' N inc U ≫
        ((dualVectorBundleToBase N ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N ≫ q) =
      (dualVectorBundleToBase N' ⁻¹ᵁ U).ι ≫ dualVectorBundleToBase N' ≫ q := by
  rw [subbundleEmbeddingRestrict_ι_assoc, subbundleEmbedding_comp_base]

/-- **Over an open `U ⊆ X` the restricted embedding is the embedding of the restricted
subbundle**: under `p⁻¹(U) ≅ 𝐕((𝒩|_U)^∨)` and `p'⁻¹(U) ≅ 𝐕((𝒩'|_U)^∨)` the restriction of
`i : N' ⟶ N` is the embedding `𝐕((𝒩'|_U)^∨) ⟶ 𝐕((𝒩|_U)^∨)` induced by `inc|_U`. -/
theorem subbundleEmbeddingRestrict_comp_dualVectorBundleRestrictIso_hom :
    subbundleEmbeddingRestrict N' N inc U ≫ (dualVectorBundleRestrictIso N U).hom =
      (dualVectorBundleRestrictIso N' U).hom ≫
        subbundleEmbedding ((Scheme.Modules.pullback U.ι).obj N')
          ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).map inc) := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  refine (cancel_mono (dualVectorBundleToBase N ⁻¹ᵁ U).ι).mp ?_
  simp only [Category.assoc, subbundleEmbeddingRestrict_ι, dualVectorBundleRestrictIso_inv_ι,
    dualVectorBundleRestrictIso_inv_ι_assoc]
  rw [← subbundleEmbeddingPullbackMap_fst,
    reassoc_of% dualVectorBundlePullbackIso_inv_comp_subbundleEmbeddingPullbackMap U.ι N' N inc]

/-- The restricted embedding is a closed immersion when `inc` is the inclusion of a short exact
sequence of finite locally free modules. -/
theorem isClosedImmersion_subbundleEmbeddingRestrict (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (pr : N ⟶ E)
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact) :
    IsClosedImmersion (subbundleEmbeddingRestrict N' N inc U) := by
  have hS := Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree U.ι _ hseq
  have := subbundleEmbedding_isClosedImmersion_of_shortExact ((Scheme.Modules.pullback U.ι).obj N')
    ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).obj E)
    ((Scheme.Modules.pullback U.ι).map inc) ((Scheme.Modules.pullback U.ι).map pr)
    (by rw [← Functor.map_comp, w, Functor.map_zero]) hS
  have h : subbundleEmbeddingRestrict N' N inc U =
      (dualVectorBundleRestrictIso N' U).hom ≫
        subbundleEmbedding ((Scheme.Modules.pullback U.ι).obj N')
          ((Scheme.Modules.pullback U.ι).obj N) ((Scheme.Modules.pullback U.ι).map inc) ≫
        (dualVectorBundleRestrictIso N U).inv := by
    rw [← Category.assoc, ← subbundleEmbeddingRestrict_comp_dualVectorBundleRestrictIso_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

end SubbundleRestrict

/-! ### Stacks 0FAA after base change -/

section ChernCap

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r' r e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact) (t : W ⟶ X) [LocallyOfFiniteType t]

omit [LocallyOfFiniteType t] in
/-- The base change `N ×_X W ⟶ W` of the projection of `𝐕(𝒩^∨)` is flat. -/
theorem flat_pullback_snd_dualVectorBundleToBase (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N n] :
    Flat (pullback.snd (dualVectorBundleToBase N) t) :=
  have := dualVectorBundleToBase_flat N n
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback (dualVectorBundleToBase N) t)
    (P := @Flat) inferInstance

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType t] in
/-- The identification `𝐕(𝒩^∨) ×_X W ≅ 𝐕((t^*𝒩)^∨)` is compatible with the structure morphisms
to the base of chapter 42. -/
theorem dualVectorBundlePullbackIso_inv_comp_structure (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] :
    (dualVectorBundlePullbackIso t N).inv ≫
        (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX) =
      dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX := by
  have h : (dualVectorBundlePullbackIso t N).inv ≫ pullback.snd (dualVectorBundleToBase N) t =
      dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) :=
    (Iso.inv_comp_eq _).mpr (dualVectorBundlePullbackIso_hom_comp_dualVectorBundleToBase t N).symm
  rw [← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc,
    ← Category.assoc (dualVectorBundlePullbackIso t N).inv, h]

/-- **Flat pullback along the base change `N ×_X W ⟶ W` of the projection of `𝐕(𝒩^∨)` is flat
pullback along the projection of `𝐕((t^*𝒩)^∨)`**, read through
`Stacks.Chow.dualVectorBundlePullbackIso`. -/
theorem flatPullbackChow_pullback_snd_dualVectorBundleToBase (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N n] (k : ℤ)
    (β : chowGroup C (t ≫ sX) k) :
    letI := dualVectorBundleToBase_locallyOfFiniteType N n
    letI := flat_pullback_snd_dualVectorBundleToBase t N n
    letI := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback t).obj N) n
    letI := dualVectorBundleToBase_flat ((Scheme.Modules.pullback t).obj N) n
    flatPullbackChow C
        (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
        (t ≫ sX) (pullback.snd (dualVectorBundleToBase N) t)
        (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) n
        (relativeDimension_pullback_snd _ t n (dualVectorBundleToBase_relativeDimension N n)) k
        (flatPullbackDescends C _ _ _ _ _ _ _) β =
      chowPushforwardOfIso C
        (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX)
        (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
        (dualVectorBundlePullbackIso t N).inv
        (dualVectorBundlePullbackIso_inv_comp_structure C sX t N) (k + (n : ℤ))
        (flatPullbackChow C
          (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX) (t ≫ sX)
          (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N)) rfl n
          (dualVectorBundleToBase_relativeDimension _ n) k
          (flatPullbackDescends C _ _ _ _ _ _ _) β) := by
  let := dualVectorBundleToBase_locallyOfFiniteType N n
  let := flat_pullback_snd_dualVectorBundleToBase t N n
  let := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback t).obj N) n
  let := dualVectorBundleToBase_flat ((Scheme.Modules.pullback t).obj N) n
  have hsq : dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ 𝟙 W =
      (dualVectorBundlePullbackIso t N).inv ≫ pullback.snd (dualVectorBundleToBase N) t := by
    rw [Category.comp_id, ← dualVectorBundlePullbackIso_hom_comp_dualVectorBundleToBase,
      Iso.inv_hom_id_assoc]
  have h := flatPullbackChow_chowPushforwardOfIso C (t ≫ sX)
    (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX) (t ≫ sX)
    (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX) (𝟙 W)
    (Category.id_comp _) (dualVectorBundlePullbackIso t N).inv
    (dualVectorBundlePullbackIso_inv_comp_structure C sX t N)
    (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N)) rfl
    (pullback.snd (dualVectorBundleToBase N) t)
    (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) hsq n
    (dualVectorBundleToBase_relativeDimension _ n)
    (relativeDimension_pullback_snd _ t n (dualVectorBundleToBase_relativeDimension N n)) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) β
  rw [chowPushforwardOfIso_id] at h
  exact h

include hseq in
/-- **[Stacks, Tag 0FAA] after base change.** For a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free `𝒪_X`-modules of constant ranks `r'`, `r` and `e`,
and a morphism `t : W ⟶ X` locally of finite type, the base changes
`i_W : N' ×_X W ⟶ N ×_X W`, `p'_W : N' ×_X W ⟶ W` and `p_W : N ×_X W ⟶ W` of the closed
embedding and of the two projections satisfy, for `β ∈ CH_k(W)`,

  `(i_W)_* (p'_W)^* β = p_W^*(c_e(t^*ℰ) ∩ β)`

in `CH_{k+r'}(N ×_X W)`, the degrees `k + r'` and `(k - e) + r` being identified through
`r = r' + e`. -/
theorem subbundleEmbeddingPullbackMap_pushforward_flatPullback_eq_topChernCap (x : X) (k : ℤ)
    (β : chowGroup C (t ≫ sX) k) :
    letI := isClosedImmersion_subbundleEmbeddingPullbackMap N' N t E inc pr w hseq
    letI := dualVectorBundleToBase_locallyOfFiniteType N' r'
    letI := dualVectorBundleToBase_locallyOfFiniteType N r
    letI := flat_pullback_snd_dualVectorBundleToBase t N' r'
    letI := flat_pullback_snd_dualVectorBundleToBase t N r
    chowPushforwardOfIsClosedImmersion C
        (pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX)
        (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
        (subbundleEmbeddingPullbackMap N' N t inc)
        (by rw [subbundleEmbeddingPullbackMap_fst_assoc, subbundleEmbedding_comp_base])
        (k + (r' : ℤ))
        (flatPullbackChow C
          (pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX)
          (t ≫ sX) (pullback.snd (dualVectorBundleToBase N') t)
          (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) r'
          (relativeDimension_pullback_snd _ t r' (dualVectorBundleToBase_relativeDimension N' r'))
          k (flatPullbackDescends C _ _ _ _ _ _ _) β) =
      Eq.mp (congrArg (chowGroup C
          (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX))
          (subbundleDegree_eq N' N E r' r e inc pr w hseq x k))
        (flatPullbackChow C
          (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
          (t ≫ sX) (pullback.snd (dualVectorBundleToBase N) t)
          (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) r
          (relativeDimension_pullback_snd _ t r (dualVectorBundleToBase_relativeDimension N r))
          (k - (e : ℤ)) (flatPullbackDescends C _ _ _ _ _ _ _)
          (GenuineChern.chernCap C e (t ≫ sX) ((Scheme.Modules.pullback t).obj E) k
            (Fin.last e) β)) := by
  let := isClosedImmersion_subbundleEmbeddingPullbackMap N' N t E inc pr w hseq
  let := dualVectorBundleToBase_locallyOfFiniteType N' r'
  let := dualVectorBundleToBase_locallyOfFiniteType N r
  let := flat_pullback_snd_dualVectorBundleToBase t N' r'
  let := flat_pullback_snd_dualVectorBundleToBase t N r
  by_cases hW : Nonempty W
  swap
  · have : IsEmpty W := not_nonempty_iff.mp hW
    have : IsEmpty ↥(Limits.pullback (dualVectorBundleToBase N) t : Scheme.{u}) :=
      ⟨fun p => isEmptyElim ((pullback.snd (dualVectorBundleToBase N) t).base p)⟩
    have := subsingleton_chowGroup_of_isEmpty C
      (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX) (k + (r' : ℤ))
    exact Subsingleton.elim _ _
  obtain ⟨y⟩ := hW
  have wW : (Scheme.Modules.pullback t).map inc ≫ (Scheme.Modules.pullback t).map pr = 0 := by
    rw [← Functor.map_comp, w, Functor.map_zero]
  have hseqW : (ShortComplex.mk ((Scheme.Modules.pullback t).map inc)
      ((Scheme.Modules.pullback t).map pr) wW).ShortExact :=
    @Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree W X t
      (ShortComplex.mk inc pr w) hseq (inferInstanceAs
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E))
  let := subbundleEmbedding_isClosedImmersion_of_shortExact ((Scheme.Modules.pullback t).obj N')
    ((Scheme.Modules.pullback t).obj N) ((Scheme.Modules.pullback t).obj E)
    ((Scheme.Modules.pullback t).map inc) ((Scheme.Modules.pullback t).map pr) wW hseqW
  let := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback t).obj N') r'
  let := dualVectorBundleToBase_locallyOfFiniteType ((Scheme.Modules.pullback t).obj N) r
  let := dualVectorBundleToBase_flat ((Scheme.Modules.pullback t).obj N') r'
  let := dualVectorBundleToBase_flat ((Scheme.Modules.pullback t).obj N) r
  have h0FAA := subbundleEmbedding_pushforward_flatPullback_eq_chernCap_of_point C (t ≫ sX)
    ((Scheme.Modules.pullback t).obj N') ((Scheme.Modules.pullback t).obj N)
    ((Scheme.Modules.pullback t).obj E) r' r e ((Scheme.Modules.pullback t).map inc)
    ((Scheme.Modules.pullback t).map pr) wW hseqW y k β
  have hF' := flatPullbackChow_pullback_snd_dualVectorBundleToBase C sX t N' r' k β
  have hF := flatPullbackChow_pullback_snd_dualVectorBundleToBase C sX t N r (k - (e : ℤ))
    (GenuineChern.chernCap C e (t ≫ sX) ((Scheme.Modules.pullback t).obj E) k (Fin.last e) β)
  have hJ : subbundleEmbeddingPullbackMap N' N t inc ≫
      (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX) =
      pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX := by
    rw [subbundleEmbeddingPullbackMap_fst_assoc, subbundleEmbedding_comp_base]
  have hsub : subbundleEmbedding ((Scheme.Modules.pullback t).obj N')
      ((Scheme.Modules.pullback t).obj N) ((Scheme.Modules.pullback t).map inc) ≫
        (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX) =
      dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX :=
    subbundleEmbedding_comp_base _ _ (t ≫ sX) _
  have hB : ∀ z : chowGroup C (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫
      t ≫ sX) (k + (r' : ℤ)),
      chowPushforwardOfIsClosedImmersion C
          (pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX)
          (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
          (subbundleEmbeddingPullbackMap N' N t inc) hJ (k + (r' : ℤ))
          (chowPushforwardOfIso C
            (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX)
            (pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX)
            (dualVectorBundlePullbackIso t N').inv
            (dualVectorBundlePullbackIso_inv_comp_structure C sX t N') (k + (r' : ℤ)) z) =
        chowPushforwardOfIso C
          (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX)
          (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
          (dualVectorBundlePullbackIso t N).inv
          (dualVectorBundlePullbackIso_inv_comp_structure C sX t N) (k + (r' : ℤ))
          (chowPushforwardOfIsClosedImmersion C
            (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX)
            (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX)
            (subbundleEmbedding ((Scheme.Modules.pullback t).obj N')
              ((Scheme.Modules.pullback t).obj N) ((Scheme.Modules.pullback t).map inc))
            hsub (k + (r' : ℤ)) z) := by
    intro z
    have e1 := properChowPushforward_comp C
      (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX)
      (pullback.fst (dualVectorBundleToBase N') t ≫ dualVectorBundleToBase N' ≫ sX)
      (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
      (dualVectorBundlePullbackIso t N').inv (subbundleEmbeddingPullbackMap N' N t inc)
      (dualVectorBundlePullbackIso_inv_comp_structure C sX t N') hJ (k + (r' : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ _ _)
    have e2 := properChowPushforward_comp C
      (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX)
      (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N) ≫ t ≫ sX)
      (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX)
      (subbundleEmbedding ((Scheme.Modules.pullback t).obj N')
        ((Scheme.Modules.pullback t).obj N) ((Scheme.Modules.pullback t).map inc))
      (dualVectorBundlePullbackIso t N).inv hsub
      (dualVectorBundlePullbackIso_inv_comp_structure C sX t N) (k + (r' : ℤ))
      (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion _ C _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    have e3 := chowPushforwardOfIsClosedImmersion_congr C
      (dualVectorBundleToBase ((Scheme.Modules.pullback t).obj N') ≫ t ≫ sX)
      (pullback.fst (dualVectorBundleToBase N) t ≫ dualVectorBundleToBase N ≫ sX) _ _
      (dualVectorBundlePullbackIso_inv_comp_subbundleEmbeddingPullbackMap t N' N inc)
      (by rw [Category.assoc, hJ, dualVectorBundlePullbackIso_inv_comp_structure])
      (by rw [Category.assoc, dualVectorBundlePullbackIso_inv_comp_structure, hsub])
      (k + (r' : ℤ))
    exact (congrFun (congrArg DFunLike.coe e1) z).trans
      ((congrFun (congrArg DFunLike.coe e3) z).trans (congrFun (congrArg DFunLike.coe e2) z).symm)
  have hdeg : k + (r' : ℤ) = k - (e : ℤ) + (r : ℤ) :=
    (subbundleDegree_eq N' N E r' r e inc pr w hseq x k).symm
  refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
  refine HEq.trans (heq_of_eq ((congrArg _ hF').trans (hB _))) ?_
  refine HEq.trans ?_ (heq_of_eq hF.symm)
  refine properChowPushforward_heq_congr C _ _ _ _ hdeg _ _ _ _ ?_
  exact (heq_of_eq h0FAA).trans (cast_heq _ _)

end ChernCap

end Stacks.Chow

end
