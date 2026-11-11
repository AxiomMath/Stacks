module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts
public import StacksFrontier.Algebra.Homology.LeftExactHomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.KInjectiveTowerCocone
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# Sections of `H⁰(RP(⊕_m X[m]))` over acyclic objects

Let `A` be a Grothendieck abelian category with enough injectives, `(C, O)` a ringed site and
`P : A ⥤ Mod(O)` an additive functor whose left adjoint is exact. Let `X ∈ A` and suppose that
the canonical map `⊕_{m ≥ 0} X[m] ⟶ ∏_{m ≥ 0} X[m]` is an isomorphism in `D(A)`.  This file
computes the sections of `H⁰(RP(⊕_m X[m]))` over the members `U` of a class `𝔅` of objects
covering the site, assuming that the cohomology sheaves of `RP(⊕_m X[m])` and the higher direct
images `R^m P(X)` have no higher cohomology over the members of `𝔅`:

`Γ(U, H⁰(RP(⊕_m X[m]))) ≅ ∏_m Γ(U, R^m P(X))`,

linearly over `O(U)` and naturally in `U`.  This is the computation in the proof of
**Stacks 07DD**, where `P` is the direct image along a morphism of algebraic stacks and
`X = 𝒪_𝒳`.

## The argument

Let `X → I` be an injective resolution.  By the hypothesis `⊕_m X[m] ≅ ∏_m I[m]` in `D(A)`, and
the product of the K-injective complexes `I[m]` is K-injective and computes the product in
`D(A)`.  The left adjoint of `P` being exact, `P` preserves K-injective complexes, so
`RP(⊕_m X[m])` is represented by the K-injective complex `P(∏_m I[m]) = ∏_m P(I)[m]`.

Over `U ∈ 𝔅` the sections of the cohomology sheaves of a K-injective complex whose cohomology
sheaves are acyclic over `𝔅` are the cohomology of its complex of sections (**Stacks 0BKZ**,
`Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_app_of_acyclic_cover`).  Applied
to `P(∏_m I[m])` in degree `0` and to `P(I)` in degree `m`, together with the exactness of
products of presheaves of modules, this gives

`Γ(U, H⁰) ≅ H⁰(∏_m Γ(U, P(I))[m]) ≅ ∏_m H^m(Γ(U, P(I))) ≅ ∏_m Γ(U, R^m P(X))`.

Every step except the two applications of 0BKZ is an isomorphism of presheaves of modules, and
those two are morphisms of presheaves of modules invertible over the members of `𝔅`; this is
what makes the final isomorphism `O(U)`-linear and natural in `U`.

## Main results

* `PresheafOfModules.hasExactLimitsOfShape_discrete_nat`: countable products of presheaves of
  modules are exact.
* `Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_forget_app_of_acyclic_cover`:
  Stacks 0BKZ for the comparison of presheaves of *modules* `H^q(I(-)) ⟶ H^q(I)(-)`.
* `PresheafOfModules.exists_linearEquiv_of_isIso_app`: a span of morphisms of presheaves of
  modules invertible over a class of objects gives linear isomorphisms of sections over that
  class, natural in the object.
* `Stacks.DerivedFunctor.exists_linearEquiv_sections_homology_zero_totalRightDerived_sigma`:
  the computation above.
* `Stacks.DerivedFunctor.sectionsRightDerivedIsoRightDerivedSections`: over `U ∈ 𝔅`,
  `Γ(U, R^m P(X))` is the `m`-th right derived functor of `Γ(U, P(-))` at `X`.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe uA vA uB vB g d dB u v w g' d'

/-! ### Countable products of presheaves of modules are exact -/

namespace PresheafOfModules

/-- Countable products of presheaves of modules are exact: they are computed objectwise in
abelian groups, where they are exact. -/
instance hasExactLimitsOfShape_discrete_nat {C : Type u} [Category.{v} C]
    (R : Cᵒᵖ ⥤ RingCat.{w}) :
    HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{w} R) := by
  have : ReflectsFiniteColimits (toPresheaf.{w} R) :=
    { reflects := fun _ _ _ => reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : HasLimitsOfShape (Discrete ℕ) AddCommGrpCat.{w} := AddCommGrpCat.hasLimitsOfShape
  have : HasLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{w}) := inferInstance
  have : HasProducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{w}) := fun _ =>
    @functorCategoryHasLimitsOfShape _ _ _ _ _ _ AddCommGrpCat.hasLimitsOfShape
  have : HasExactLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{w}) := inferInstance
  exact HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (toPresheaf.{w} R)

end PresheafOfModules

/-! ### Stacks 0BKZ for presheaves of modules -/

namespace Stacks.Cohomology.HypercohomologyEdge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The homology comparison `H^q(K(-)) ⟶ H^q(K)(-)` of presheaves of modules is invertible over
an object as soon as the one of underlying abelian presheaves is. -/
theorem isIso_homologyComparison_forget_app_of_isIso_app
    (K : CochainComplex (SheafOfModules.{w} O) ℤ) (q : ℤ) (U : C)
    (h : IsIso ((homologyComparison (underlyingPresheaf O) K q).app (op U))) :
    IsIso ((homologyComparison (SheafOfModules.forget O) K q).app (op U)) := by
  let F₁ := SheafOfModules.forget O
  let F₂ := PresheafOfModules.toPresheaf O.obj
  let e : F₁ ⋙ F₂ ≅ underlyingPresheaf O := Iso.refl _
  have hc := homologyComparison_comp_of_iso_leftExactHomologyComparison F₁ F₂
    (underlyingPresheaf O) e K q
  have hr := F₂.isIso_homologyComparison_of_preservesFiniteLimits_rightExactHomologyComparison
    ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q
  have hl := homologyComparison_comp_homologyComparison_leftExactHomologyComparison F₂
    ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q
  have h₂ : IsIso (homologyComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      q) := by
    rw [IsIso.eq_inv_of_hom_inv_id hl]
    infer_instance
  have hU := congr_app hc (op U)
  simp only [NatTrans.comp_app] at hU
  have h₃ : IsIso (((HomologicalComplex.homologyMap
      (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison F₁ F₂
        (underlyingPresheaf O) e K).hom q).app (op U)) ≫
      (homologyComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).app
        (op U) ≫
      (F₂.map (homologyComparison F₁ K q)).app (op U)) := by
    rw [hU]; infer_instance
  have h₄ : IsIso ((F₂.map (homologyComparison F₁ K q)).app (op U)) := by
    have h₃' : IsIso ((homologyComparison F₂ ((F₁.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) q).app (op U) ≫
          (F₂.map (homologyComparison F₁ K q)).app (op U)) :=
      IsIso.of_isIso_comp_left ((HomologicalComplex.homologyMap
        (Functor.mapHomologicalComplexCompIsoOfIsoRightExactHomologyComparison F₁ F₂
          (underlyingPresheaf O) e K).hom q).app (op U)) _
    exact IsIso.of_isIso_comp_left
      ((homologyComparison F₂ ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).app
        (op U)) _
  have h₅ : IsIso ((forget₂ (ModuleCat.{w} (O.obj.obj (op U))) AddCommGrpCat.{w}).map
      ((homologyComparison F₁ K q).app (op U))) := h₄
  exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{w} (O.obj.obj (op U))) AddCommGrpCat.{w})

variable [IsGrothendieckAbelian.{g} (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O)]

/-- **Stacks 0BKZ for presheaves of modules.** Over a member `U` of a covering class over whose
members the cohomology sheaves of the K-injective complex `I` have no higher cohomology, the
comparison `H^q(I(U)) ⟶ H^q(I)(U)` of `O(U)`-modules is an isomorphism. -/
theorem isIso_homologyComparison_forget_app_of_acyclic_cover
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (hI : I.IsKInjective)
    (B : ObjectProperty C) (hB : J.HasEnoughObjects B)
    (hvan : ∀ V : C, B V → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (((SheafOfModules.evaluation O (.op V)).rightDerived p).obj (I.homology m)))
    {U : C} (hU : B U) (q : ℤ) :
    IsIso ((homologyComparison (SheafOfModules.forget O) I q).app (op U)) :=
  isIso_homologyComparison_forget_app_of_isIso_app O I q U
    (isIso_homologyComparison_app_of_acyclic_cover O I hI B hB hvan hU q)

end Stacks.Cohomology.HypercohomologyEdge

/-! ### Linear isomorphisms of sections from a span of presheaves of modules -/

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- The inverse of an isomorphism of modules undoes it elementwise. -/
lemma inv_apply_apply {S : RingCat.{w}} {X Y : ModuleCat.{w} S} (f : X ⟶ Y) [IsIso f] (x : X) :
    inv f (f x) = x := by
  change (f ≫ inv f) x = x
  simp

/-- The sections of a countable product of presheaves of modules are the product of the
sections. -/
def evaluationPiIso (N : ℕ → PresheafOfModules.{w} R) (U : Cᵒᵖ) :
    (∏ᶜ N).obj U ≅ ModuleCat.of (R.obj U) ((m : ℕ) → (N m).obj U) :=
  PreservesProduct.iso (evaluation R U) N ≪≫ ModuleCat.piIsoPi _

/-- The `m`-th component of a section of `∏_m N_m` is its image under the `m`-th projection. -/
lemma evaluationPiIso_hom_apply (N : ℕ → PresheafOfModules.{w} R) (U : Cᵒᵖ)
    (z : (∏ᶜ N).obj U) (m : ℕ) :
    ((evaluationPiIso N U).hom z : (m : ℕ) → (N m).obj U) m = (Pi.π N m).app U z := by
  change ((ModuleCat.piIsoPi _).hom ((PreservesProduct.iso (evaluation R U) N).hom z) :
    (m : ℕ) → (N m).obj U) m = _
  refine (ModuleCat.piIsoPi_hom_ker_subtype_apply (fun m => (N m).obj U) m _).trans ?_
  change (piComparison (evaluation R U) N ≫ Pi.π _ m) z = _
  rw [piComparison_comp_π]
  rfl

/-- A product of morphisms of presheaves of modules is invertible over an object as soon as each
factor is. -/
lemma isIso_app_piMap {N N' : ℕ → PresheafOfModules.{w} R} (f : ∀ m, N m ⟶ N' m) (U : Cᵒᵖ)
    (hf : ∀ m, IsIso ((f m).app U)) : IsIso ((Limits.Pi.map f).app U) := by
  have : ∀ m, IsIso ((evaluation R U).map (f m)) := fun m => by
    rw [evaluation_map]; exact hf m
  have hc : (evaluation R U).map (Limits.Pi.map f) ≫ piComparison (evaluation R U) N' =
      piComparison (evaluation R U) N ≫ Limits.Pi.map (fun m => (evaluation R U).map (f m)) := by
    refine Pi.hom_ext _ _ fun m => ?_
    rw [Category.assoc, Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, ← Functor.map_comp, ← Functor.map_comp, Limits.Pi.map_π]
  have h : IsIso ((evaluation R U).map (Limits.Pi.map f)) := by
    have : IsIso ((evaluation R U).map (Limits.Pi.map f) ≫ piComparison (evaluation R U) N') := by
      rw [hc]; infer_instance
    exact IsIso.of_isIso_comp_right _ (piComparison (evaluation R U) N')
  rwa [evaluation_map] at h

/-- A morphism of presheaves of modules which is an isomorphism is invertible over every
object. -/
lemma isIso_app_of_isIso {M N : PresheafOfModules.{w} R} (f : M ⟶ N) [IsIso f] (U : Cᵒᵖ) :
    IsIso (f.app U) := by
  have : IsIso ((evaluation R U).map f) := inferInstance
  rwa [evaluation_map] at this

/-- **Sections from a span invertible over a class of objects.** Let `a : W ⟶ M` and
`b : W ⟶ ∏_m N_m` be morphisms of presheaves of modules which are invertible over every member
of a class `𝔅` of objects.  Then over every `U ∈ 𝔅` there is an `R(U)`-linear isomorphism
`M(U) ≃ ∏_m N_m(U)`, natural in `U ∈ 𝔅`. -/
theorem exists_linearEquiv_of_isIso_app {W M : PresheafOfModules.{w} R}
    {N : ℕ → PresheafOfModules.{w} R} (a : W ⟶ M) (b : W ⟶ ∏ᶜ N) (𝔅 : ObjectProperty C)
    (ha : ∀ U : C, 𝔅 U → IsIso (a.app (op U))) (hb : ∀ U : C, 𝔅 U → IsIso (b.app (op U))) :
    ∃ α : ∀ U : C, 𝔅 U → (M.obj (op U) ≃ₗ[R.obj (op U)] ((m : ℕ) → (N m).obj (op U))),
      ∀ (U U' : C) (hU : 𝔅 U) (hU' : 𝔅 U') (ι : U ⟶ U') (x : M.obj (op U')) (m : ℕ),
        α U hU (M.map ι.op x) m = (N m).map ι.op (α U' hU' x m) := by
  let e : ∀ U : C, 𝔅 U → (M.obj (op U) ≅ ModuleCat.of (R.obj (op U))
      ((m : ℕ) → (N m).obj (op U))) := fun U hU =>
    haveI := ha U hU
    haveI := hb U hU
    (asIso (a.app (op U))).symm ≪≫ asIso (b.app (op U)) ≪≫ evaluationPiIso N (op U)
  refine ⟨fun U hU => (e U hU).toLinearEquiv, ?_⟩
  intro U U' hU hU' ι x m
  have := ha U hU
  have := ha U' hU'
  have := hb U hU
  have := hb U' hU'
  obtain ⟨w, rfl⟩ : ∃ w, a.app (op U') w = x :=
    ⟨inv (a.app (op U')) x, by simp⟩
  have hw : inv (a.app (op U)) (M.map ι.op (a.app (op U') w)) = W.map ι.op w := by
    rw [← naturality_apply]
    exact inv_apply_apply _ _
  change ((evaluationPiIso N (op U)).hom (b.app (op U) (inv (a.app (op U))
      (M.map ι.op (a.app (op U') w)))) : (m : ℕ) → (N m).obj (op U)) m =
    (N m).map ι.op ((((evaluationPiIso N (op U')).hom
      (b.app (op U') (inv (a.app (op U')) (a.app (op U') w)))) : (m : ℕ) → (N m).obj (op U')) m)
  rw [hw, evaluationPiIso_hom_apply, evaluationPiIso_hom_apply, naturality_apply,
    naturality_apply, inv_apply_apply]

end PresheafOfModules

/-! ### The computation -/

namespace Stacks.DerivedFunctor

section Countable

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{g} A]

/-- A Grothendieck abelian category has countable products. -/
instance hasProductsOfShape_nat_of_isGrothendieckAbelian : HasProductsOfShape ℕ A :=
  haveI : HasLimitsOfSize.{0, 0} A := hasLimitsOfSizeShrink.{0, 0, g, g} A
  inferInstance

variable [HasDerivedCategory.{d} A]

/-- The derived category of a Grothendieck abelian category has countable direct sums
(**Stacks 07D9**). -/
instance hasCoproductsOfShape_nat_derivedCategory :
    HasCoproductsOfShape ℕ (DerivedCategory A) :=
  haveI : HasCoproducts.{0} (DerivedCategory A) := hasCoproducts_shrink.{0, g}
  inferInstance

/-- The derived category of a Grothendieck abelian category has countable products
(**Stacks 07D9**). -/
instance hasProductsOfShape_nat_derivedCategory :
    HasProductsOfShape ℕ (DerivedCategory A) :=
  haveI : HasProducts.{0} (DerivedCategory A) := hasProducts_shrink.{0, g}
  inferInstance

end Countable

section Transfer

/-- The canonical map `⊕_m Y_m ⟶ ∏_m Y_m` is invertible after an equivalence of categories as soon
as it is invertible before it. -/
theorem isIso_piLift_sigmaπ_of_equivalence {D₁ : Type*} {D₂ : Type*} [Category D₁]
    [Category D₂] [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] (E : D₁ ≌ D₂)
    [E.functor.PreservesZeroMorphisms]
    [HasCoproductsOfShape ℕ D₁] [HasProductsOfShape ℕ D₁] [HasCoproductsOfShape ℕ D₂]
    [HasProductsOfShape ℕ D₂] {Y₁ : ℕ → D₁} {Y₂ : ℕ → D₂}
    (iY : ∀ m, E.functor.obj (Y₁ m) ≅ Y₂ m) (h : IsIso (Pi.lift (Sigma.π Y₁))) :
    IsIso (Pi.lift (Sigma.π Y₂)) := by
  have heq : Pi.lift (Sigma.π Y₂) = (Sigma.mapIso iY).inv ≫ sigmaComparison E.functor Y₁ ≫
      E.functor.map (Pi.lift (Sigma.π Y₁)) ≫ piComparison E.functor Y₁ ≫
        (Pi.mapIso iY).hom := by
    refine Sigma.hom_ext _ _ fun i => Pi.hom_ext _ _ fun j => ?_
    simp only [Category.assoc, Pi.mapIso_hom_π, piComparison_comp_π_assoc, Pi.lift_comp_π,
      Sigma.ι_mapIso_inv_assoc, ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc]
    rw [Sigma.ι_π, Sigma.ι_π]
    split_ifs with hij
    · subst hij
      simp
    · simp
  rw [heq]
  infer_instance

/-- **Transport of `⊕_m X_m[m] ≅ ∏_m X_m[m]` between models of the derived category.** If the
canonical map `⊕_m X_m[m] ⟶ ∏_m X_m[m]` is invertible in one model `H'` of `D(A)` (for instance
the standard model `HasDerivedCategory.standard`), it is invertible in every model. -/
theorem isIso_piLift_sigmaπ_singleFunctor_of_standard {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{g} A] [H' : HasDerivedCategory A] [H : HasDerivedCategory.{d} A]
    (X : ℕ → A)
    (hX : letI := H';
      IsIso (Pi.lift (Sigma.π fun m : ℕ =>
        (DerivedCategory.singleFunctor A (-(m : ℤ))).obj (X m)))) :
    IsIso (Pi.lift (Sigma.π fun m : ℕ =>
      (DerivedCategory.singleFunctor A (-(m : ℤ))).obj (X m))) := by
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let L₁ := @DerivedCategory.Q A _ _ H'
  let L₂ := @DerivedCategory.Q A _ _ H
  let E := Localization.uniq L₁ L₂ W
  let eQ : L₁ ⋙ E.functor ≅ L₂ := Localization.compUniqFunctor L₁ L₂ W
  exact isIso_piLift_sigmaπ_of_equivalence E (fun m => eQ.app _) hX

/-- **The cohomology of `⊕_m X_m[m]` does not depend on the model of the derived category**: it
is the same in any two models `H` and `H'`, for instance in every model and the standard one
`HasDerivedCategory.standard`. -/
theorem nonempty_homologyFunctor_obj_sigma_singleFunctor_iso_standard {A : Type uA}
    [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{g} A] [H' : HasDerivedCategory A]
    [H : HasDerivedCategory.{d} A] (X : ℕ → A) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor A n).obj
        (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj (X m)) ≅
      (letI := H';
        (DerivedCategory.homologyFunctor A n).obj
          (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj (X m)))) := by
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let L₁ := @DerivedCategory.Q A _ _ H'
  let L₂ := @DerivedCategory.Q A _ _ H
  let E := Localization.uniq L₁ L₂ W
  let eQ : L₁ ⋙ E.functor ≅ L₂ := Localization.compUniqFunctor L₁ L₂ W
  let K : ℕ → CochainComplex A ℤ := fun m => (CochainComplex.singleFunctor A (-(m : ℤ))).obj (X m)
  let i₁ : E.functor.obj (∐ fun m => L₁.obj (K m)) ≅ ∐ fun m => L₂.obj (K m) :=
    (asIso (sigmaComparison E.functor fun m => L₁.obj (K m))).symm ≪≫
      Sigma.mapIso fun m => eQ.app (K m)
  let Z := ∐ fun m => L₁.obj (K m)
  let C := L₁.objPreimage Z
  let eZ : L₁.obj C ≅ Z := L₁.objObjPreimageIso Z
  exact ⟨(DerivedCategory.homologyFunctor A n).mapIso
      (i₁.symm ≪≫ E.functor.mapIso eZ.symm ≪≫ eQ.app C) ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app C ≪≫
    ((@DerivedCategory.homologyFunctorFactors A _ _ H' n).app C).symm ≪≫
    (@DerivedCategory.homologyFunctor A _ _ H' n).mapIso eZ⟩

end Transfer

section Resolution

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]

/-- The chosen injective resolution `I` of `X`, extended by zero to a complex indexed by `ℤ`
and shifted by `m`: the complex `I[m]`. -/
abbrev shiftedResolution (X : A) (m : ℕ) : CochainComplex A ℤ :=
  (injectiveResolution X).cochainComplex⟦(m : ℤ)⟧

/-- **The higher right derived functors on the extended injective resolution.** For an additive
functor `F`, the cohomology `H^m(F(I))` of `F` applied to the chosen injective resolution of `X`,
extended by zero, is `R^m F(X)`. -/
def homologyMapResolutionIsoRightDerived {B : Type uB} [Category.{vB} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (X : A) (m : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex).homology (m : ℤ) ≅ (F.rightDerived m).obj X :=
  letI := HasDerivedCategory.standard A
  letI := HasDerivedCategory.standard B
  ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (m : ℤ)).mapIso
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app _) ≪≫
    (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (m : ℤ)).app _).symm ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIsoRes F m).app X).symm

variable [HasDerivedCategory.{d} A]

/-- `X[m] ≅ I[m]` in `D(A)`, for the chosen injective resolution `X ⟶ I`. -/
def singleFunctorObjIsoQObjShiftedResolution (X : A) (m : ℕ) :
    (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X ≅
      DerivedCategory.Q.obj (shiftedResolution X m) :=
  (((DerivedCategory.singleFunctors A).shiftIso (m : ℤ) (-(m : ℤ)) 0 (by simp)).app X).symm ≪≫
    (shiftFunctor (DerivedCategory A) (m : ℤ)).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (injectiveResolution X).ι')
        ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance)) ≪≫
    ((DerivedCategory.Q.commShiftIso (m : ℤ)).app _).symm

end Resolution

section KInjective

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
  [HasDerivedCategory.{d} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]

/-- **The unbounded right derived functor at a K-injective complex** is the functor applied
degreewise. -/
def totalRightDerivedObjQIsoOfIsKInjective (F : A ⥤ B) [F.Additive] (I : CochainComplex A ℤ)
    [I.IsKInjective] :
    (totalRightDerived F).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have hunit := isIso_totalRightDerivedUnit_app_of_isKInjective F I
  (totalRightDerived F).mapIso ((DerivedCategory.quotientCompQhIso A).app I).symm ≪≫
    (@asIso _ _ _ _ _ hunit).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso B).app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

variable [EnoughInjectives A]

/-- If the canonical map `⊕_m X[m] ⟶ ∏_m X[m]` is an isomorphism in `D(A)`, then
`⊕_m X[m] ≅ ∏_m I[m]`, the product of complexes of the shifted injective resolutions. -/
def sigmaSingleIsoQPiShiftedResolution (X : A)
    (hX : IsIso (Pi.lift (Sigma.π fun m : ℕ =>
      (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X))) :
    (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X) ≅
      DerivedCategory.Q.obj (∏ᶜ shiftedResolution X) :=
  @asIso _ _ _ _ _ hX ≪≫ Pi.mapIso (singleFunctorObjIsoQObjShiftedResolution X) ≪≫
    (@asIso _ _ _ _ (piComparison DerivedCategory.Q (shiftedResolution X))
      (Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective _ fun _ => inferInstance)).symm

end KInjective

section Sections

variable {A : Type uA} [Category.{vA} A] [Abelian A] [hA : IsGrothendieckAbelian.{g} A]
  [EnoughInjectives A] [HasDerivedCategory.{d} A]
  {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hO : IsGrothendieckAbelian.{g'} (SheafOfModules.{w} O)]
  [EnoughInjectives (SheafOfModules.{w} O)]
  [HasDerivedCategory.{d'} (SheafOfModules.{w} O)]
  (P : A ⥤ SheafOfModules.{w} O) [hP : P.Additive] {L : SheafOfModules.{w} O ⥤ A} (adj : L ⊣ P)
  [PreservesFiniteLimits L]

omit hA [EnoughInjectives A] [HasDerivedCategory.{d} A] hO
  [EnoughInjectives (SheafOfModules.{w} O)] [HasDerivedCategory.{d'} (SheafOfModules.{w} O)] in
include adj in
/-- A functor with an exact left adjoint preserves K-injective complexes. -/
lemma isKInjective_mapHomologicalComplex_of_adjunction (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have := adj.isLeftAdjoint
  have : L.Additive := adj.left_adjoint_additive
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact P L adj I

omit hA [HasDerivedCategory.{d} A] hO
  [HasDerivedCategory.{d'} (SheafOfModules.{w} O)] in
/-- The cohomology sheaves of `P(I)`, for the extended injective resolution `I` of `X`, have no
higher cohomology over the members of `𝔅` as soon as the `R^m P(X)` have none. -/
lemma isZero_rightDerived_evaluation_homology_mapResolution (X : A) (𝔅 : ObjectProperty C)
    (hvan : ∀ V : C, 𝔅 V → ∀ p : ℕ, 0 < p → ∀ m : ℕ,
      IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj
        ((P.rightDerived m).obj X)))
    (V : C) (hV : 𝔅 V) (p : ℕ) (hp : 0 < p) (n : ℤ) :
    IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj
      (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex).homology n)) := by
  rcases lt_or_ge n 0 with hn | hn
  · have := isStrictlyGE_mapHomologicalComplex P (injectiveResolution X).cochainComplex 0
    have := Stacks.DerivedLinear.rightDerived_additive (SheafOfModules.evaluation O (op V)) p
    exact Functor.map_isZero _
      ((CochainComplex.exactAt_of_isGE ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex) 0 n hn).isZero_homology)
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (hvan V hV p hp k).of_iso (((SheafOfModules.evaluation O (op V)).rightDerived p).mapIso
      (homologyMapResolutionIsoRightDerived P X k))

include adj in
/-- **Sections of `H⁰(RP(⊕_m X[m]))` over acyclic objects** (the computation in the proof of
Stacks 07DD).  Let `P : A ⥤ Mod(O)` have an exact left adjoint, let `X ∈ A` be such that
`⊕_{m ≥ 0} X[m] ⟶ ∏_{m ≥ 0} X[m]` is an isomorphism in `D(A)`, and let `𝔅` be a class of
objects covering the site over whose members the cohomology sheaves of `RP(⊕_m X[m])` and the
higher direct images `R^m P(X)` have no higher cohomology.  Then over every `U ∈ 𝔅`

`Γ(U, H⁰(RP(⊕_m X[m]))) ≅ ∏_m Γ(U, R^m P(X))`

as `O(U)`-modules, naturally in `U ∈ 𝔅`. -/
theorem exists_linearEquiv_sections_homology_zero_totalRightDerived_sigma (X : A)
    (hX : IsIso (Pi.lift (Sigma.π fun m : ℕ =>
      (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X)))
    (𝔅 : ObjectProperty C) (h𝔅 : J.HasEnoughObjects 𝔅)
    (hvanE : ∀ V : C, 𝔅 V → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj
        ((DerivedCategory.homologyFunctor _ n).obj ((totalRightDerived P).obj
          (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X)))))
    (hvanF : ∀ V : C, 𝔅 V → ∀ p : ℕ, 0 < p → ∀ m : ℕ,
      IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj
        ((P.rightDerived m).obj X))) :
    ∃ α : ∀ U : C, 𝔅 U →
      ((((DerivedCategory.homologyFunctor _ 0).obj ((totalRightDerived P).obj
          (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X))).val.obj
            (op U)) ≃ₗ[O.obj.obj (op U)]
        ((m : ℕ) → ((P.rightDerived m).obj X).val.obj (op U))),
      ∀ (U U' : C) (hU : 𝔅 U) (hU' : 𝔅 U') (ι : U ⟶ U')
        (x : ((DerivedCategory.homologyFunctor _ 0).obj ((totalRightDerived P).obj
          (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X))).val.obj (op U'))
        (m : ℕ),
        α U hU (((DerivedCategory.homologyFunctor _ 0).obj ((totalRightDerived P).obj
          (∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X))).val.map
            ι.op x) m =
          ((P.rightDerived m).obj X).val.map ι.op (α U' hU' x m) := by
  -- The K-injective complexes `∏_m I[m]`, `P(∏_m I[m])` and `P(I)`.
  let R := (injectiveResolution X).cochainComplex
  have hProd : (∏ᶜ shiftedResolution X).IsKInjective :=
    Stacks.Injectives.KInjectiveProduct.product_mathlib_isKInjective _ (fun _ => inferInstance)
  let Jc := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ shiftedResolution X)
  let Kc := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj R
  have hJ : CochainComplex.IsKInjective Jc :=
    isKInjective_mapHomologicalComplex_of_adjunction P adj _
  have hK : CochainComplex.IsKInjective Kc :=
    isKInjective_mapHomologicalComplex_of_adjunction P adj _
  -- `RP(⊕_m X[m])` is represented by `P(∏_m I[m])`.
  let E := ∐ fun m : ℕ => (DerivedCategory.singleFunctor A (-(m : ℤ))).obj X
  let eRP : (totalRightDerived P).obj E ≅ DerivedCategory.Q.obj Jc :=
    (totalRightDerived P).mapIso (sigmaSingleIsoQPiShiftedResolution X hX) ≪≫
      totalRightDerivedObjQIsoOfIsKInjective P _
  let eH : ∀ n : ℤ, (DerivedCategory.homologyFunctor _ n).obj ((totalRightDerived P).obj E) ≅
      Jc.homology n := fun n =>
    (DerivedCategory.homologyFunctor _ n).mapIso eRP ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app Jc
  have hvanJ : ∀ V : C, 𝔅 V → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj (Jc.homology n)) :=
    fun V hV p hp n => (hvanE V hV p hp n).of_iso
      (((SheafOfModules.evaluation O (op V)).rightDerived p).mapIso (eH n)).symm
  have hvanK := isZero_rightDerived_evaluation_homology_mapResolution P X 𝔅 hvanF
  -- The presheaf complexes and the isomorphism `P(∏_m I[m]) ≅ ∏_m P(I)[m]`.
  let Fg := SheafOfModules.forget O
  let Kp := (Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj Kc
  let Jp := (Fg.mapHomologicalComplex (ComplexShape.up ℤ)).obj Jc
  have : PreservesLimitsOfSize.{0, 0} P := adj.rightAdjoint_preservesLimits
  let eJ : Jp ≅ ∏ᶜ fun m : ℕ => Kp⟦(m : ℤ)⟧ :=
    (Fg.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (PreservesProduct.iso (P.mapHomologicalComplex (ComplexShape.up ℤ)) (shiftedResolution X) ≪≫
        Pi.mapIso fun m => (P.mapCochainComplexShiftIso (m : ℤ)).app R) ≪≫
    PreservesProduct.iso (Fg.mapHomologicalComplex (ComplexShape.up ℤ))
      (fun m : ℕ => Kc⟦(m : ℤ)⟧) ≪≫
    Pi.mapIso fun m => (Fg.mapCochainComplexShiftIso (m : ℤ)).app Kc
  -- `H⁰(∏_m P(I)[m]) ≅ ∏_m H^m(P(I))` on presheaves.
  let γ : Jp.homology 0 ≅ ∏ᶜ fun m : ℕ => Kp.homology (m : ℤ) :=
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso eJ ≪≫
      (haveI := preservesProducts_homologyFunctor
        (A := PresheafOfModules.{w} O.obj) (ComplexShape.up ℤ) 0;
        PreservesProduct.iso (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0)
          (fun m : ℕ => Kp⟦(m : ℤ)⟧)) ≪≫
      Pi.mapIso fun m =>
        (CochainComplex.ShiftSequence.shiftIso _ (m : ℤ) 0 (m : ℤ) (by simp)).app Kp
  let a := homologyComparison Fg Jc 0 ≫ Fg.map (eH 0).inv
  let b := γ.hom ≫ Limits.Pi.map fun m : ℕ =>
    homologyComparison Fg Kc (m : ℤ) ≫ Fg.map (homologyMapResolutionIsoRightDerived P X m).hom
  refine PresheafOfModules.exists_linearEquiv_of_isIso_app a b 𝔅 (fun U hU => ?_)
    (fun U hU => ?_)
  · have :=
      Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_forget_app_of_acyclic_cover
        O Jc hJ 𝔅 h𝔅 hvanJ hU 0
    have := PresheafOfModules.isIso_app_of_isIso (Fg.map (eH 0).inv) (op U)
    rw [PresheafOfModules.comp_app]
    infer_instance
  · have hm : ∀ m : ℕ, IsIso ((homologyComparison Fg Kc (m : ℤ) ≫
        Fg.map (homologyMapResolutionIsoRightDerived P X m).hom).app (op U)) := fun m => by
      have :=
        Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_forget_app_of_acyclic_cover
          O Kc hK 𝔅 h𝔅 hvanK hU (m : ℤ)
      have := PresheafOfModules.isIso_app_of_isIso
        (Fg.map (homologyMapResolutionIsoRightDerived P X m).hom) (op U)
      rw [PresheafOfModules.comp_app]
      infer_instance
    have := PresheafOfModules.isIso_app_piMap _ (op U) hm
    have := PresheafOfModules.isIso_app_of_isIso γ.hom (op U)
    rw [PresheafOfModules.comp_app]
    infer_instance

omit hA [HasDerivedCategory.{d} A] [HasDerivedCategory.{d'} (SheafOfModules.{w} O)] in
include adj in
/-- **Sections of the higher direct images over acyclic objects.** If the `R^m P(X)` have no
higher cohomology over the members of a covering class `𝔅`, then over every `U ∈ 𝔅` the
module `Γ(U, R^m P(X))` is the `m`-th right derived functor of `Γ(U, P(-))` at `X`, as an
`O(U)`-module: both are `H^m(Γ(U, P(I)))` for an injective resolution `X ⟶ I`, the first by
Stacks 0BKZ. -/
def sectionsRightDerivedIsoRightDerivedSections (X : A) (𝔅 : ObjectProperty C)
    (h𝔅 : J.HasEnoughObjects 𝔅)
    (hvanF : ∀ V : C, 𝔅 V → ∀ p : ℕ, 0 < p → ∀ m : ℕ,
      IsZero (((SheafOfModules.evaluation O (op V)).rightDerived p).obj
        ((P.rightDerived m).obj X)))
    (m : ℕ) {U : C} (hU : 𝔅 U) :
    ((P.rightDerived m).obj X).val.obj (op U) ≅
      ((P ⋙ SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj (op U)).rightDerived
        m).obj X :=
  have hK := isKInjective_mapHomologicalComplex_of_adjunction P adj
    (injectiveResolution X).cochainComplex
  have := Stacks.Cohomology.HypercohomologyEdge.isIso_homologyComparison_forget_app_of_acyclic_cover
    O _ hK 𝔅 h𝔅 (isZero_rightDerived_evaluation_homology_mapResolution P X 𝔅 hvanF) hU m
  (PresheafOfModules.evaluation O.obj (op U)).mapIso
      ((SheafOfModules.forget O).mapIso (homologyMapResolutionIsoRightDerived P X m).symm) ≪≫
    (asIso ((homologyComparison (SheafOfModules.forget O)
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj (injectiveResolution X).cochainComplex)
        m).app (op U))).symm ≪≫
    (ShortComplex.mapHomologyIso ((((SheafOfModules.forget O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex)).sc m)
          (PresheafOfModules.evaluation O.obj (op U))).symm ≪≫
    homologyMapResolutionIsoRightDerived
      (P ⋙ SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj (op U)) X m

end Sections

end Stacks.DerivedFunctor
