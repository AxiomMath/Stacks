module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ArbitraryRank
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.DualBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The class of a subbundle, globally

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules of
arbitrary ranks. **Stacks 0FAA**: for `α ∈ A_k(X)`,

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`  in  `A_*(N)`.

The ranks of the modules are only locally constant, so the projections `p : N ⟶ X` and
`p' : N' ⟶ X` have locally constant relative dimension, and both sides live in the product
`∏_d A_d(N)` of all the Chow groups of `N`. The flat pullback `p^*` is assembled from the flat
pullbacks of constant relative dimension over a decomposition `X = ∐ U_i` into open and closed
subschemes on which the rank is constant, through `A_d(N) = ∏_i A_d(p^{-1}(U_i))`; the class
`c_top(ℰ) ∩ α ∈ ∏_m A_m(X)` has degree `m` part `c_top(ℰ)_{k-m} ∩ α`, where `c_top(ℰ)_p` is the
degree `p` part of the completed class of Stacks 0FA4. The identity is checked on each joint rank
locus `X_{a,b}`, where it is
`Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_topChernClass`;
the comparison of the embedding over `X_{a,b}` with the restriction of `i` uses the naturality of
the dual base-change map `g^*(ℳ^∨) ≅ (g^*ℳ)^∨` in `ℳ`.

## Main definitions

* `Stacks.Chow.dualBundleFlatPullback` — flat pullback `∏_m A_m(X) ⟶ ∏_d A_d(𝐕(ℱ^∨))` along the
  projection of the vector bundle of a finite locally free module of locally constant rank.
* `Stacks.Chow.homogeneousChowFamily` — a class of `A_k(X)` as an element of `∏_m A_m(X)`.
* `Stacks.Chow.topChernCapFamily` — `c_top(ℰ) ∩ α ∈ ∏_m A_m(X)`.

## Main results

* `Stacks.Chow.pullbackDualMap_naturality'` — the dual base-change map is natural in the module.
* `Stacks.Chow.dualBundleBaseChangeMap_comp_subbundleEmbedding`,
  `Stacks.Chow.isPullback_dualBundleBaseChangeMap_subbundleEmbedding` — the embedding of the
  restricted bundles is the base change of `i`.
* `Stacks.Chow.dualBundleFlatPullback_restrict`, `Stacks.Chow.bundleChow_ext` — `p^*β` restricts
  to `p_i^*(β|_{U_i})` over `U_i`, and classes on `N` are determined by these restrictions.
* `Stacks.Chow.subbundleEmbedding_pushforward_dualBundleFlatPullback` — Stacks 0FAA, for the
  flat pullbacks assembled over the joint rank loci; the decomposition-free statement is
  `Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback`.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (vectorBundleMap vectorBundleMap_comp
  vectorBundleMap_pullback_comp_vectorBundleBaseChangeMap vectorBundleBaseChangeMap)
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### Naturality of the dual base-change map -/

section DualNaturality

variable {Y X : Scheme.{u}} (g : Y ⟶ X) {M M' : X.Modules} (f : M' ⟶ M)

/-- The two pairings `g^*(M^∨) ⊗ g^*M' ⟶ 𝒪_Y` obtained from `f : M' ⟶ M` agree: pull back the
functional and pair with `M'`, or pair with the image of `M'` in `M`. -/
theorem pullbackEvaluation_dualMap :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullback g).map (dualMap f)),
          𝟙 ((Scheme.Modules.pullback g).obj M')) : (_, _) ⟶ (_, _))) ≫
        pullbackEvaluation g M' =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩)).map
        ((𝟙 ((Scheme.Modules.pullback g).obj (dualSheaf M)),
          (Scheme.Modules.pullback g).map f) : (_, _) ⟶ (_, _))) ≫
        pullbackEvaluation g M := by
  refine tensor_hom_ext_of_pullbackUnit g (dualSheaf M) M' (fun U s m => ?_)
  refine (comp_val_app _ _ _ _).trans ?_
  refine Eq.trans (val_app_congr _ _ ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
    (tensorSheafPure_congr _ _ _ (pullback_map_unit_app g (dualMap f) U s) rfl))) ?_
  refine (pullbackEvaluation_unit_tmul g M' U _ m).trans ?_
  refine Eq.trans ?_ ((comp_val_app _ _ _ _).trans (val_app_congr _ _
    ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
      (tensorSheafPure_congr _ _ _ rfl (pullback_map_unit_app g f U m))))).symm
  exact (pullbackEvaluation_unit_tmul g M U s _).symm

/-- **The dual base-change map `g^*(M^∨) ⟶ (g^*M)^∨` is natural in `M`.** -/
theorem pullbackDualMap_naturality' :
    (Scheme.Modules.pullback g).map (dualMap f) ≫ pullbackDualMap g M' =
      pullbackDualMap g M ≫ dualMap ((Scheme.Modules.pullback g).map f) := by
  refine hom_ext_dualSheaf_of_terminal (fun V a b => ?_)
  have h := congrArg (fun φ => φ.val.app (op V)
      (tensorSheafPure Y _ _ V (a ⊗ₜ[Y.presheaf.obj (op V)] b)))
    (pullbackEvaluation_dualMap g f)
  have h1 := (comp_val_app _ _ _ _).symm.trans (h.trans (comp_val_app _ _ _ _))
  refine (pullbackDualMap_eval g M' V
    (((Scheme.Modules.pullback g).map (dualMap f)).val.app (op V) a) b).trans ?_
  refine Eq.trans ?_ (pullbackDualMap_eval g M V a
    (((Scheme.Modules.pullback g).map f).val.app (op V) b)).symm
  refine (val_app_congr (pullbackEvaluation g M') V (tensorSheafMap_tensorSheafPure
    ((Scheme.Modules.pullback g).map (dualMap f)) (𝟙 ((Scheme.Modules.pullback g).obj M'))
    V a b)).symm.trans ?_
  exact h1.trans (val_app_congr (pullbackEvaluation g M) V (tensorSheafMap_tensorSheafPure
    (𝟙 ((Scheme.Modules.pullback g).obj (dualSheaf M))) ((Scheme.Modules.pullback g).map f)
    V a b))

end DualNaturality

/-! ### The subbundle embedding commutes with base change -/

section EmbeddingBaseChange

variable {T X : Scheme.{u}} (g : T ⟶ X) (N' N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (inc : N' ⟶ N)

/-- **The embedding `N'_T ⟶ N_T` is the base change of `i : N' ⟶ N`**: it commutes with the
base-change morphisms `𝐕((g^*𝒩')^∨) ⟶ 𝐕((𝒩')^∨)` and `𝐕((g^*𝒩)^∨) ⟶ 𝐕(𝒩^∨)`. -/
theorem dualBundleBaseChangeMap_comp_subbundleEmbedding :
    dualBundleBaseChangeMap g N' ≫ subbundleEmbedding N' N inc =
      subbundleEmbedding _ _ ((Scheme.Modules.pullback g).map inc) ≫
        dualBundleBaseChangeMap g N := by
  have hbc := vectorBundleMap_pullback_comp_vectorBundleBaseChangeMap g (dualSheaf N)
    (dualMap inc)
  have hmod : (Scheme.Modules.pullback g).map (dualMap inc) ≫
      (Stacks.FundamentalGroup.pullbackDualSheafIso g N' inferInstance).hom =
      (Stacks.FundamentalGroup.pullbackDualSheafIso g N inferInstance).hom ≫
        dualMap ((Scheme.Modules.pullback g).map inc) :=
    pullbackDualMap_naturality' g inc
  have hvb : (vectorBundleMap T
        (Stacks.FundamentalGroup.pullbackDualSheafIso g N' inferInstance).hom).left ≫
        (vectorBundleMap T ((Scheme.Modules.pullback g).map (dualMap inc))).left =
      (vectorBundleMap T (dualMap ((Scheme.Modules.pullback g).map inc))).left ≫
        (vectorBundleMap T
          (Stacks.FundamentalGroup.pullbackDualSheafIso g N inferInstance).hom).left :=
    (congrArg (fun h => Over.Hom.left h) (vectorBundleMap_comp T
        ((Scheme.Modules.pullback g).map (dualMap inc))
        (Stacks.FundamentalGroup.pullbackDualSheafIso g N' inferInstance).hom)).symm.trans
      ((congrArg (fun h => (vectorBundleMap T h).left) hmod).trans
        (congrArg (fun h => Over.Hom.left h) (vectorBundleMap_comp T
          (Stacks.FundamentalGroup.pullbackDualSheafIso g N inferInstance).hom
          (dualMap ((Scheme.Modules.pullback g).map inc)))))
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hbc.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hvb).trans (Category.assoc _ _ _))))

end EmbeddingBaseChange

/-! ### Flat pullback to a vector bundle of locally constant rank -/

section PiecewisePullback

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
  {I : Type u} (U : I → X.Opens)

/-- Over an open immersion `j : V ⟶ X`, the morphism `𝐕((j^*ℱ)^∨) ⟶ 𝐕(ℱ^∨)` is an open
immersion, being a base change of `j`. -/
instance isOpenImmersion_dualBundleBaseChangeMap {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] : IsOpenImmersion (dualBundleBaseChangeMap j F) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_dualBundleBaseChangeMap j F).flip
    ‹_›

omit [LocallyOfFiniteType sX] in
/-- The base change map `𝐕((j^*ℱ)^∨) ⟶ 𝐕(ℱ^∨)` commutes with the structure morphisms to `C.S`. -/
theorem dualBundleBaseChangeMap_comp_structure {V : Scheme.{u}} (j : V ⟶ X) :
    dualBundleBaseChangeMap j F ≫ (dualVectorBundleToBase F ≫ sX) =
      dualVectorBundleToBase ((Scheme.Modules.pullback j).obj F) ≫ (j ≫ sX) := by
  rw [← Category.assoc, (isPullback_dualBundleBaseChangeMap j F).w, Category.assoc]

/-- The pieces `𝐕((ℱ|_{U_i})^∨) = p^{-1}(U_i)` of `𝐕(ℱ^∨)` over a decomposition of `X` into open
and closed subschemes decompose `𝐕(ℱ^∨)`. -/
theorem isClopenDecomposition_opensRange_dualBundleBaseChangeMap (hU : IsClopenDecomposition U) :
    IsClopenDecomposition fun i ↦ (dualBundleBaseChangeMap (U i).ι F).opensRange := by
  have h : (fun i ↦ (dualBundleBaseChangeMap (U i).ι F).opensRange) =
      fun i ↦ dualVectorBundleToBase F ⁻¹ᵁ U i := by
    funext i
    rw [← preimage_opensRange_of_isPullback (isPullback_dualBundleBaseChangeMap (U i).ι F),
      Scheme.Opens.opensRange_ι]
  rw [h]
  exact hU.preimage _

variable (hU : IsClopenDecomposition U) (ρ : I → ℕ)
  (hρ : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i))

/-- The product decomposition `A_d(𝐕(ℱ^∨)) = ∏_i A_d(𝐕((ℱ|_{U_i})^∨))`. -/
def bundleChowPieceEquiv (d : ℤ) :
    chowGroup C (dualVectorBundleToBase F ≫ sX) d ≃+
      ∀ i, chowGroup C
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX)) d :=
  chowGroupClopenRestrictEquiv C (dualVectorBundleToBase F ≫ sX)
    (fun i ↦ dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
    (fun i ↦ dualBundleBaseChangeMap (U i).ι F)
    (fun i ↦ dualBundleBaseChangeMap_comp_structure C sX F (U i).ι)
    (isClopenDecomposition_opensRange_dualBundleBaseChangeMap F U hU) d

/-- The `i`-th component of `bundleChowPieceEquiv` is restriction to `𝐕((ℱ|_{U_i})^∨)`. -/
theorem bundleChowPieceEquiv_apply (d : ℤ)
    (x : chowGroup C (dualVectorBundleToBase F ≫ sX) d) (i : I) :
    bundleChowPieceEquiv C sX F U hU d x i =
      chowGroupRestrict C (dualVectorBundleToBase F ≫ sX)
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
        (dualBundleBaseChangeMap (U i).ι F) (dualBundleBaseChangeMap_comp_structure C sX F (U i).ι)
        d x :=
  chowGroupClopenRestrictEquiv_apply C _ _ _ _ _ d x i

include hU in
/-- A class on `𝐕(ℱ^∨)` is determined by its restrictions to the pieces over the `U_i`. -/
theorem bundleChow_ext {d : ℤ} {x y : chowGroup C (dualVectorBundleToBase F ≫ sX) d}
    (h : ∀ i, chowGroupRestrict C (dualVectorBundleToBase F ≫ sX)
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
        (dualBundleBaseChangeMap (U i).ι F) (dualBundleBaseChangeMap_comp_structure C sX F (U i).ι)
        d x =
      chowGroupRestrict C (dualVectorBundleToBase F ≫ sX)
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
        (dualBundleBaseChangeMap (U i).ι F) (dualBundleBaseChangeMap_comp_structure C sX F (U i).ι)
        d y) : x = y :=
  (bundleChowPieceEquiv C sX F U hU d).injective (funext fun i ↦
    (bundleChowPieceEquiv_apply C sX F U hU d x i).trans
      ((h i).trans (bundleChowPieceEquiv_apply C sX F U hU d y i).symm))

/-- **Flat pullback `p^* : ∏_m A_m(X) ⟶ ∏_d A_d(𝐕(ℱ^∨))` along the projection of the vector
bundle of a finite locally free module of locally constant rank.** Over a decomposition
`X = ∐ U_i` on which `ℱ` has constant rank `ρ_i`, the degree `d` part of `p^*β` is the class whose
restriction to `p^{-1}(U_i) = 𝐕((ℱ|_{U_i})^∨)` is the flat pullback `p_i^*(β_{d-ρ_i}|_{U_i})` of
relative dimension `ρ_i` (Stacks 02S1). -/
def dualBundleFlatPullback (β : ∀ m : ℤ, chowGroup C sX m) (d : ℤ) :
    chowGroup C (dualVectorBundleToBase F ≫ sX) d :=
  (bundleChowPieceEquiv C sX F U hU d).symm fun i ↦
    haveI := hρ i
    chowGroupCast C _ (show d - (ρ i : ℤ) + (ρ i : ℤ) = d by ring)
      (dualBundlePullback C ((U i).ι ≫ sX) ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)
        (d - ρ i) (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - ρ i) (β (d - ρ i))))

/-- **The restriction of `p^*β` to the piece over `U_i` is `p_i^*(β|_{U_i})`.** -/
theorem dualBundleFlatPullback_restrict (β : ∀ m : ℤ, chowGroup C sX m) (d : ℤ) (i : I) :
    chowGroupRestrict C (dualVectorBundleToBase F ≫ sX)
        (dualVectorBundleToBase ((Scheme.Modules.pullback (U i).ι).obj F) ≫ ((U i).ι ≫ sX))
        (dualBundleBaseChangeMap (U i).ι F) (dualBundleBaseChangeMap_comp_structure C sX F (U i).ι)
        d (dualBundleFlatPullback C sX F U hU ρ hρ β d) =
      haveI := hρ i
      chowGroupCast C _ (show d - (ρ i : ℤ) + (ρ i : ℤ) = d by ring)
        (dualBundlePullback C ((U i).ι ≫ sX) ((Scheme.Modules.pullback (U i).ι).obj F) (ρ i)
          (d - ρ i) (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - ρ i) (β (d - ρ i)))) :=
  (bundleChowPieceEquiv_apply C sX F U hU d _ i).symm.trans
    (congrFun ((bundleChowPieceEquiv C sX F U hU d).apply_symm_apply _) i)

end PiecewisePullback

/-! ### Heterogeneous congruences -/

section Congr

variable (C : ChowSituation.{u})

/-- Restriction to an open subscheme respects heterogeneous equality across equal degrees. -/
theorem chowGroupRestrict_heq {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU)
    {k k' : ℤ} (hk : k = k') {x : chowGroup C sX k} {x' : chowGroup C sX k'} (hx : x ≍ x') :
    chowGroupRestrict C sX sU j hj k x ≍ chowGroupRestrict C sX sU j hj k' x' := by
  subst hk; cases hx; rfl

/-- Flat pullback to `𝐕(ℱ^∨)` respects heterogeneous equality across equal degrees. -/
theorem dualBundlePullback_heq {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (F : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    {k k' : ℤ} (hk : k = k') {x : chowGroup C sX k} {x' : chowGroup C sX k'} (hx : x ≍ x') :
    dualBundlePullback C sX F r k x ≍ dualBundlePullback C sX F r k' x' := by
  subst hk; cases hx; rfl

/-- For equal codegrees `p = p'`, capping with the components `c p` and `c p'` of a family of
bivariant classes gives heterogeneously equal results. -/
theorem chowCohomologyCap_heq {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (c : ∀ p : ℤ, chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {p p' : ℤ}
    (hp : p = p') (k : ℤ) (α : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX p (c p) k α ≍
      chowCohomologyCap C (gysinSystemOfInvertible C) sX p' (c p') k α := by
  subst hp; rfl

/-- The zero classes of `A_k(X)` and `A_{k'}(X)` are heterogeneously equal when `k = k'`. -/
theorem zero_heq_zero_of_degree {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    {k k' : ℤ} (hk : k = k') : (0 : chowGroup C sX k) ≍ (0 : chowGroup C sX k') := by
  subst hk; rfl

end Congr

/-! ### The two families on `X` -/

section Families

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- A class `α ∈ A_k(X)`, as the element of `∏_m A_m(X)` concentrated in degree `k`. -/
def homogeneousChowFamily (k : ℤ) (α : chowGroup C sX k) (m : ℤ) : chowGroup C sX m :=
  if h : k = m then chowGroupCast C sX h α else 0

/-- **`c_top(ℰ) ∩ α ∈ ∏_m A_m(X)`** for `α ∈ A_k(X)`: its degree `m` part is `c_top(ℰ)_{k-m} ∩ α`,
the cap product with the degree `k - m` part of the top Chern class `c_top(ℰ) ∈ A^*(X)^∧` of
Stacks 0FA4. -/
def topChernCapFamily (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (k : ℤ) (α : chowGroup C sX k) (m : ℤ) : chowGroup C sX m :=
  chowGroupCast C sX (show k - (k - m) = m by ring)
    (chowCohomologyCap C (gysinSystemOfInvertible C) sX (k - m)
      (topChernClassCompletedComponent C sX E (k - m)) k α)

end Families

/-! ### Stacks 0FAA -/

section Global

variable {T X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- The square formed by `N'_T ⟶ N'`, `N_T ⟶ N` and the two embeddings is cartesian. -/
theorem isPullback_dualBundleBaseChangeMap_subbundleEmbedding (g : T ⟶ X) :
    IsPullback (dualBundleBaseChangeMap g N')
      (subbundleEmbedding _ _ ((Scheme.Modules.pullback g).map inc))
      (subbundleEmbedding N' N inc) (dualBundleBaseChangeMap g N) := by
  refine IsPullback.of_bot ?_ (dualBundleBaseChangeMap_comp_subbundleEmbedding g N' N inc)
    (isPullback_dualBundleBaseChangeMap g N)
  rw [subbundleEmbedding_comp_dualVectorBundleToBase,
    subbundleEmbedding_comp_dualVectorBundleToBase]
  exact isPullback_dualBundleBaseChangeMap g N'

/-- `𝒩'` has rank `a` on the joint rank locus `X_{a,b}`. -/
theorem isFiniteLocallyFreeOfRank_jointRankLocus_fst (ab : ULift.{u} (ℕ × ℕ)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (jointRankLocus N' E ab).ι).obj N') ab.down.1 :=
  isFiniteLocallyFreeOfRank_of_le_rankLocus inf_le_left

/-- `ℰ` has rank `b` on the joint rank locus `X_{a,b}`. -/
theorem isFiniteLocallyFreeOfRank_jointRankLocus_snd (ab : ULift.{u} (ℕ × ℕ)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (jointRankLocus N' E ab).ι).obj E) ab.down.2 :=
  isFiniteLocallyFreeOfRank_of_le_rankLocus inf_le_right

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] in
include hseq in
/-- `𝒩` has rank `a + b` on the joint rank locus `X_{a,b}`. -/
theorem isFiniteLocallyFreeOfRank_jointRankLocus_middle (ab : ULift.{u} (ℕ × ℕ)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (jointRankLocus N' E ab).ι).obj N) (ab.down.1 + ab.down.2) :=
  have := isFiniteLocallyFreeOfRank_jointRankLocus_fst N' E ab
  have := isFiniteLocallyFreeOfRank_jointRankLocus_snd N' E ab
  isFiniteLocallyFreeOfRank_middle _ _ _ ab.down.1 ab.down.2
    ((Scheme.Modules.pullback (jointRankLocus N' E ab).ι).map inc)
    ((Scheme.Modules.pullback (jointRankLocus N' E ab).ι).map pr)
    (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w _)
    (shortExact_pullback_map N' N E inc pr w hseq _)

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0FAA.** Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free
`𝒪_X`-modules, let `i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` be the closed embedding
and `p'`, `p` the projections. For `α ∈ A_k(X)`,

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`  in  `∏_d A_d(N)`.

Here `c_top(ℰ) ∩ α ∈ ∏_m A_m(X)` is the cap product with the top Chern class of Stacks 0FA4
(`Stacks.Chow.topChernCapFamily`), `α` is read in `∏_m A_m(X)` in degree `k`, and `p^*`, `(p')^*`
are the flat pullbacks along the projections, which have locally constant relative dimension
(`Stacks.Chow.dualBundleFlatPullback`), computed over the decomposition of `X` into the open and
closed loci `X_{a,b}` on which `𝒩'` and `ℰ` have ranks `a` and `b`. The same identity for the
flat pullbacks independent of any decomposition is
`Stacks.Chow.subbundleEmbedding_pushforward_canonicalDualBundleFlatPullback`. -/
theorem subbundleEmbedding_pushforward_dualBundleFlatPullback (k : ℤ) (α : chowGroup C sX k) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
    (fun d ↦ chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) d
        (dualBundleFlatPullback C sX N' (jointRankLocus N' E)
          (isClopenDecomposition_jointRankLocus N' E) (fun ab ↦ ab.down.1)
          (isFiniteLocallyFreeOfRank_jointRankLocus_fst N' E)
          (homogeneousChowFamily C sX k α) d)) =
      dualBundleFlatPullback C sX N (jointRankLocus N' E)
        (isClopenDecomposition_jointRankLocus N' E) (fun ab ↦ ab.down.1 + ab.down.2)
        (isFiniteLocallyFreeOfRank_jointRankLocus_middle N' N E inc pr w hseq)
        (topChernCapFamily C sX E k α) := by
  have := isClosedImmersion_subbundleEmbedding_of_shortExact N' N E inc pr w hseq
  funext d
  refine bundleChow_ext C sX N (jointRankLocus N' E) (isClopenDecomposition_jointRankLocus N' E)
    fun ab ↦ ?_
  obtain ⟨⟨a, b⟩⟩ := ab
  have := isFiniteLocallyFreeOfRank_jointRankLocus_fst N' E ⟨(a, b)⟩
  have := isFiniteLocallyFreeOfRank_jointRankLocus_snd N' E ⟨(a, b)⟩
  have := isFiniteLocallyFreeOfRank_jointRankLocus_middle N' N E inc pr w hseq ⟨(a, b)⟩
  have : IsClosedImmersion
      (subbundleEmbedding _ _
        ((Scheme.Modules.pullback (jointRankLocus N' E ⟨(a, b)⟩).ι).map inc)) :=
    isClosedImmersion_subbundleEmbedding_of_shortExact _ _ _ _ _
      (pullback_map_comp_pullback_map_eq_zero N' N E inc pr w (jointRankLocus N' E ⟨(a, b)⟩).ι)
      (shortExact_pullback_map N' N E inc pr w hseq _)
  have hpo := subbundleEmbedding_pushforward_flatPullback_eq_topChernClass C sX N' N E inc pr w
    hseq (jointRankLocus N' E ⟨(a, b)⟩) a b inf_le_left inf_le_right k α
  refine (chowGroupRestrict_properChowPushforward C (dualVectorBundleToBase N' ≫ sX)
    (dualVectorBundleToBase N ≫ sX)
    (dualVectorBundleToBase ((Scheme.Modules.pullback (jointRankLocus N' E ⟨(a, b)⟩).ι).obj N') ≫
      ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX))
    (dualVectorBundleToBase ((Scheme.Modules.pullback (jointRankLocus N' E ⟨(a, b)⟩).ι).obj N) ≫
      ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX))
    (subbundleEmbedding N' N inc) (subbundleEmbedding_comp_base N' N sX inc)
    (dualBundleBaseChangeMap (jointRankLocus N' E ⟨(a, b)⟩).ι N')
    (dualBundleBaseChangeMap_comp_structure C sX N' (jointRankLocus N' E ⟨(a, b)⟩).ι)
    (dualBundleBaseChangeMap (jointRankLocus N' E ⟨(a, b)⟩).ι N)
    (dualBundleBaseChangeMap_comp_structure C sX N (jointRankLocus N' E ⟨(a, b)⟩).ι)
    (subbundleEmbedding _ _ ((Scheme.Modules.pullback (jointRankLocus N' E ⟨(a, b)⟩).ι).map inc))
    (subbundleEmbedding_comp_base _ _ ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX)
      ((Scheme.Modules.pullback (jointRankLocus N' E ⟨(a, b)⟩).ι).map inc))
    (isPullback_dualBundleBaseChangeMap_subbundleEmbedding N' N inc
      (jointRankLocus N' E ⟨(a, b)⟩).ι)
    d
    (properPushforwardDescends C _ _ _ _ d) (properPushforwardDescends C _ _ _ _ d) _).trans ?_
  rw [dualBundleFlatPullback_restrict, dualBundleFlatPullback_restrict]
  by_cases hd : d = k + a
  · subst hd
    refine eq_of_heq (HEq.trans ?_ (hpo.1.trans ?_))
    · refine heq_of_eq (congrArg _ (eq_of_heq ((chowGroupCast_heq _ _ _ _).trans
        (dualBundlePullback_heq C _ _ _ (by ring) (chowGroupRestrict_heq C sX
          ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX) (jointRankLocus N' E ⟨(a, b)⟩).ι rfl (by ring)
          ?_)))))
      have hk : k = k + (a : ℤ) - (a : ℤ) := by ring
      simp only [homogeneousChowFamily, dite_eq_left hk]
      exact chowGroupCast_heq _ _ _ _
    · refine HEq.symm ((chowGroupCast_heq _ _ _ _).trans (dualBundlePullback_heq C _ _ _
        (by push_cast; ring) (chowGroupRestrict_heq C sX
          ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX) (jointRankLocus N' E ⟨(a, b)⟩).ι rfl
          (by push_cast; ring)
          ((chowGroupCast_heq _ _ _ _).trans (chowCohomologyCap_heq C sX
            (topChernClassCompletedComponent C sX E) (by push_cast; ring) k α)))))
  · have h0 : homogeneousChowFamily C sX k α (d - a) = 0 := dite_eq_right (by omega)
    have hz : chowGroupRestrict C sX ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX)
        (jointRankLocus N' E ⟨(a, b)⟩).ι rfl
        (d - ((a + b : ℕ) : ℤ))
        (topChernCapFamily C sX E k α (d - ((a + b : ℕ) : ℤ))) = 0 := by
      have h2 := hpo.2 (k - (d - ((a + b : ℕ) : ℤ))) (by push_cast; omega)
      exact eq_of_heq ((chowGroupRestrict_heq C sX
        ((jointRankLocus N' E ⟨(a, b)⟩).ι ≫ sX) (jointRankLocus N' E ⟨(a, b)⟩).ι rfl (by ring)
        (chowGroupCast_heq _ _ _ _)).trans
        ((heq_of_eq h2).trans (zero_heq_zero_of_degree C _ (by ring))))
    simp only [h0, hz, map_zero]

end Global

end Stacks.Chow

end
