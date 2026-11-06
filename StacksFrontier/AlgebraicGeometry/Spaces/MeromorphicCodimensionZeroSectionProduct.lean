module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroSectionComparison

/-!
# `𝒦_X(F)` is the direct sum and the product of the direct images at the codimension-zero points

Let `X` be an algebraic space over a scheme `S` satisfying hypotheses (a), (b) and (c) of
Stacks 0ENA and let `F` be a quasi-coherent `𝒪_X`-module.  This file assembles the affine-chart
computation of
`StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroSectionComparison` into the
second conclusion of Stacks 0ENA: the sheaf of meromorphic sections of `F` is both the direct
sum and the product over the codimension-zero points `η ∈ X⁰` of the direct images
`j_{η, *}j_η^*F`,

`𝒦_X(F) = ⨁_{η ∈ X⁰} j_{η, *}j_η^*F = ∏_{η ∈ X⁰} j_{η, *}j_η^*F`.

The comparison into the product is the transpose across sheafification of the family of
comparisons `𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F`; it is an isomorphism because that family is
jointly bijective on the sections over every affine étale chart, and the affine étale charts are
a cover-dense family, so the transposed family is locally bijective and a sheaf receiving a
locally bijective morphism from a presheaf is its sheafification.  The comparison out of the
direct sum is `CategoryTheory.Limits.sigmaPiComparison`; it is an isomorphism because the direct
sum of sheaves is locally the sectionwise direct sum, which injects into the product, and over an
affine chart only the finitely many `η` in the image contribute.

## Main definitions

* `AlgebraicGeometry.Space.CodimensionZeroPresentation.meromorphicSectionGenericPointComparison`
  and `…meromorphicSectionGenericPointComparisonPi`: the comparisons.

## Main results

* `…CodimensionZeroPresentation.isIso_meromorphicSectionGenericPointComparisonPi`: the comparison
  into the product is an isomorphism.
* `…CodimensionZeroPresentation.isIso_sigmaPiComparison_genericPointMeromorphicModule`: the
  comparison out of the direct sum is an isomorphism.
* `…exists_codimensionZeroPresentation_isIso_meromorphicSectionComparison`: **the second
  conclusion of Stacks 0ENA.**

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

/-! ### The sections of a product of sheaves of modules -/

/-- **The sections of a product of sheaves of modules over an object are the product of the
sections.**  The sections functor preserves products, so the comparison into the product of the
sections is an isomorphism. -/
theorem bijective_pi_val_app.{m, r, v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {ι : Type m} (M : ι → SheafOfModules.{m} R) [HasProduct M] (U : Cᵒᵖ)
    [PreservesLimitsOfShape (Discrete ι)
      (SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U)))] :
    Function.Bijective fun t : (∏ᶜ M).val.obj U => fun i => (Pi.π M i).val.app U t := by
  let E := SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U))
  let q := piComparison E M ≫ (Types.productIso fun i => E.obj (M i)).hom
  have hqbij : Function.Bijective q := ConcreteCategory.bijective_of_isIso q
  have hval : ∀ (t : (∏ᶜ M).val.obj U) (i : ι), q t i = (Pi.π M i).val.app U t := by
    intro t i
    show (Types.productIso fun j => E.obj (M j)).hom (piComparison E M t) i = _
    rw [Types.productIso_hom_comp_eval_apply]
    exact ConcreteCategory.congr_hom (piComparison_comp_π E M i) t
  refine ⟨fun t t' h => hqbij.injective (funext fun i => ?_), fun v => ?_⟩
  · exact (hval t i).trans ((congrFun h i).trans (hval t' i).symm)
  · obtain ⟨t, ht⟩ := hqbij.surjective v
    exact ⟨t, funext fun i => (hval t i).symm.trans (congrFun ht i)⟩

/-- **A morphism of presheaves of modules into a product of sheaves of modules is bijective on
the sections over an object as soon as the family of its components is.** -/
theorem bijective_app_of_bijective_pi.{m, r, v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {ι : Type m} (M : ι → SheafOfModules.{m} R) [HasProduct M]
    {A : PresheafOfModules.{m} R.obj} (f : A ⟶ (∏ᶜ M).val) (U : Cᵒᵖ)
    [PreservesLimitsOfShape (Discrete ι)
      (SheafOfModules.evaluation.{m} R U ⋙ forget (ModuleCat (R.obj.obj U)))]
    (h : Function.Bijective fun z : A.obj U =>
      fun i => (Pi.π M i).val.app U (PresheafOfModules.Hom.app f U z)) :
    Function.Bijective (PresheafOfModules.Hom.app f U) :=
  ((bijective_pi_val_app M U).of_comp_iff' (PresheafOfModules.Hom.app f U)).mp h

namespace CodimensionZeroPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1) {x : points B S hS X.1}
    (hx : localRingDimension B S hS x = 0)

/-! ### The comparisons -/

/-- **The comparison `𝒦_X(F) ⟶ j_{η, *}j_η^*F`** of sheaves of `𝒦_X`-modules: the transpose
across sheafification of the comparison `𝒦_X ⊗_{𝒪_X} F ⟶ j_{η, *}j_η^*F`, read in the module
universe in which the codimension-zero points live. -/
noncomputable def meromorphicSectionGenericPointComparison
    (F : Modules.{u, u} B S hS X.1 X.2) :
    meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 F ⟶
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule hx F) :=
  let : HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
    moduleHasWeakSheafify.{u, u} B S hS X.1
  let : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)).symm
      (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
        (P.genericPointMeromorphicComparison hx F))

/-- **The comparison `𝒦_X(F) ⟶ ∏_{η ∈ X⁰} j_{η, *}j_η^*F`** of sheaves of `𝒦_X`-modules. -/
noncomputable def meromorphicSectionGenericPointComparisonPi
    (F : Modules.{u, u} B S hS X.1 X.2) :
    meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 F ⟶
      ∏ᶜ fun η : CodimensionZeroPoints B S hS X.1 =>
        SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicModule η.2 F) :=
  Pi.lift fun η => P.meromorphicSectionGenericPointComparison η.2 F

/-! ### The comparison into the product is an isomorphism -/

/-- **The comparison `𝒦_X(F) ⟶ ∏_{η ∈ X⁰} j_{η, *}j_η^*F` is an isomorphism** for a
quasi-coherent `𝒪_X`-module `F`.  The family of comparisons of presheaves it transposes is
jointly bijective on the sections over every affine étale chart, and the affine étale charts are
cover-dense in the small étale site, so the transposed family is locally bijective; and a sheaf
of modules receiving a locally bijective morphism from a presheaf is its sheafification. -/
theorem isIso_meromorphicSectionGenericPointComparisonPi
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    IsIso (P.meromorphicSectionGenericPointComparisonPi F) := by
  let : HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
    moduleHasWeakSheafify.{u, u} B S hS X.1
  let : (SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  let : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS X.1)
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).presheaf) :=
    ((SmallEtale.topology B S hS X.1).W_toSheafify
      (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).presheaf).isLocallyInjective
  let : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).presheaf) :=
    ((SmallEtale.topology B S hS X.1).W_toSheafify
      (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).presheaf).isLocallySurjective
  set eta : meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F ⟶
      (meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 F).val :=
    PresheafOfModules.toSheafify
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS X.1 X.2).O).obj)
      (CategoryTheory.toSheafify (SmallEtale.topology B S hS X.1)
        (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).presheaf) with heta
  have : PresheafOfModules.IsLocallyInjective (meromorphicRingedSite B S hS X.1 X.2).J eta :=
    inferInstanceAs (PresheafOfModules.IsLocallyInjective _ (PresheafOfModules.toSheafify _ _))
  have : PresheafOfModules.IsLocallySurjective (meromorphicRingedSite B S hS X.1 X.2).J eta :=
    inferInstanceAs (PresheafOfModules.IsLocallySurjective _ (PresheafOfModules.toSheafify _ _))
  -- the components of the composite with the sheafification unit
  have hcomp : ∀ (ξ : CodimensionZeroPoints B S hS X.1) (W : SmallEtale B S hS X.1)
      (z : (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).obj (op W)),
      (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 =>
            SheafOfModules.uliftObj.{_, _, _, _, u + 1}
              (P.genericPointMeromorphicModule η.2 F)) ξ).val.app (op W)
          (PresheafOfModules.Hom.app
            (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) (op W) z) =
        PresheafOfModules.Hom.app (PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicComparison ξ.2 F)) (op W) z := by
    intro ξ W z
    have h1 : P.meromorphicSectionGenericPointComparisonPi F ≫
        Pi.π (fun η : CodimensionZeroPoints B S hS X.1 =>
          SheafOfModules.uliftObj.{_, _, _, _, u + 1}
            (P.genericPointMeromorphicModule η.2 F)) ξ =
          P.meromorphicSectionGenericPointComparison ξ.2 F := Pi.lift_comp_π _ ξ
    have h2 : (P.meromorphicSectionGenericPointComparisonPi F).val ≫
        (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 =>
          SheafOfModules.uliftObj.{_, _, _, _, u + 1}
            (P.genericPointMeromorphicModule η.2 F)) ξ).val =
          (P.meromorphicSectionGenericPointComparison ξ.2 F).val :=
      congrArg (fun m : meromorphicSectionSheaf.{u, u} B S hS X.1 X.2 F ⟶
        SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicModule ξ.2 F) => m.val) h1
    have h3 : (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) ≫
          (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 =>
            SheafOfModules.uliftObj.{_, _, _, _, u + 1}
              (P.genericPointMeromorphicModule η.2 F)) ξ).val =
        PresheafOfModules.uliftMap.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicComparison ξ.2 F) := by
      rw [Category.assoc, h2, heta]
      exact (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _
    exact congrFun (congrArg (fun m : meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F ⟶
      (SheafOfModules.uliftObj.{_, _, _, _, u + 1}
        (P.genericPointMeromorphicModule ξ.2 F)).val =>
      fun y => PresheafOfModules.Hom.app m (op W) y) h3) z
  -- the composite is bijective on the sections over an affine étale chart
  have hgbij : ∀ W : SmallEtale B S hS X.1, IsAffine (smallEtaleScheme B S hS X.1 W) →
      Function.Bijective (PresheafOfModules.Hom.app
        (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) (op W)) := by
    intro W hW
    refine bijective_app_of_bijective_pi _
      (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) (op W) ?_
    have hrw : (fun z : (meromorphicSectionPresheaf.{u, u} B S hS X.1 X.2 F).obj (op W) =>
          fun ξ : CodimensionZeroPoints B S hS X.1 =>
            (Pi.π (fun η : CodimensionZeroPoints B S hS X.1 =>
              SheafOfModules.uliftObj.{_, _, _, _, u + 1}
                (P.genericPointMeromorphicModule η.2 F)) ξ).val.app (op W)
                (PresheafOfModules.Hom.app
                  (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) (op W) z)) =
        fun z => fun ξ : CodimensionZeroPoints B S hS X.1 =>
          ULift.up (PresheafOfModules.Hom.app
            (P.genericPointMeromorphicComparison ξ.2 F) (op W) z.down) :=
      funext fun z => funext fun ξ => hcomp ξ W z
    rw [hrw]
    have hb := P.bijective_pi_genericPointMeromorphicComparison_app hwa hfin F hF W hW
    refine ⟨fun z z' h => ?_, fun v => ?_⟩
    · exact ULift.ext (hb.injective (funext fun ξ => congrArg ULift.down (congrFun h ξ)))
    · obtain ⟨y, hy⟩ := hb.surjective fun ξ => (v ξ).down
      exact ⟨ULift.up y, funext fun ξ => ULift.ext (congrFun hy ξ)⟩
  have hdense := SmallEtale.isCoverDense_affineEtaleInclusion B S hS X.1 X.2
  have : PresheafOfModules.IsLocallyInjective (meromorphicRingedSite B S hS X.1 X.2).J
      (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) :=
    isLocallyInjective_of_injective_of_isCoverDense _ (AffineEtale.inclusion B S hS X.1) hdense
      _ fun V => (hgbij ((AffineEtale.inclusion B S hS X.1).obj V) V.2).injective
  have : PresheafOfModules.IsLocallySurjective (meromorphicRingedSite B S hS X.1 X.2).J
      (eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val) :=
    Stacks.PresheafOfModules.isLocallySurjective_of_surjective_of_isCoverDense _
      (AffineEtale.inclusion B S hS X.1) hdense _
      fun V => (hgbij ((AffineEtale.inclusion B S hS X.1).obj V) V.2).surjective
  exact Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective
    (η := eta) (g := eta ≫ (P.meromorphicSectionGenericPointComparisonPi F).val)
    (P.meromorphicSectionGenericPointComparisonPi F) rfl

/-! ### The direct sum -/

/-- The family of direct images has a direct sum: the small étale site admits sheafification of
presheaves of abelian groups in the universe of the codimension-zero points. -/
theorem hasCoproduct_genericPointMeromorphicModule (F : Modules.{u, u} B S hS X.1 X.2) :
    HasCoproduct fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule η.2 F) := by
  let := moduleHasWeakSheafify.{u, u} B S hS X.1
  let := moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  infer_instance

/-- **A chart no point of which lies over `η` has no nonzero sections of `j_{η, *}j_η^*F`**: the
base-changed chart is then empty, its regular functions are the zero ring, and a module over the
zero ring is trivial. -/
theorem subsingleton_genericPointMeromorphicModule_obj (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1)
    (hV : ∀ z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom z ≠ x) :
    Subsingleton ((SheafOfModules.uliftObj.{_, _, _, _, u + 1}
      (P.genericPointMeromorphicModule hx F)).val.obj (op V)) := by
  have : Subsingleton (chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2
      (P.genericPointChart hx V)) :=
    P.subsingleton_genericPointStructureSheaf_obj hx V hV
  have : Subsingleton
      ((P.genericPointPullback hx F).val.obj (op (P.genericPointChart hx V))) :=
    Module.subsingleton (chartRing B S hS (P.specStalkSpace hx).1 (P.specStalkSpace hx).2
      (P.genericPointChart hx V)) _
  exact inferInstanceAs (Subsingleton (ULift.{u + 1}
    ((P.genericPointPullback hx F).val.obj (op (P.genericPointChart hx V)))))

/-- The comparison from the direct sum of the direct images to their product is locally
injective: the direct sum of sheaves of modules is locally the sectionwise direct sum, which
injects into the product. -/
theorem isLocallyInjective_sigmaPiComparison_genericPointMeromorphicModule
    (F : Modules.{u, u} B S hS X.1 X.2) :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointMeromorphicModule F
    PresheafOfModules.IsLocallyInjective (meromorphicRingedSite B S hS X.1 X.2).J
      (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
        SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicModule η.2 F)).val := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := moduleHasWeakSheafify.{u, u} B S hS X.1
  let := moduleWEqualsLocallyBijective.{u, u} B S hS X.1
  let := P.hasCoproduct_genericPointMeromorphicModule F
  exact Stacks.SheafOfModules.isLocallyInjective_of_comparison
    (fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule η.2 F))
    (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule η.2 F))
    fun i j => ι_comp_sigmaPiComparison_comp_π _ i j

/-- The comparison from the direct sum of the direct images to their product is surjective on
the sections over an affine étale chart: only finitely many of the direct images have nonzero
sections there, and a section of the product with finitely many nonzero components is the image
of the sum of its components. -/
theorem surjective_sigmaPiComparison_genericPointMeromorphicModule_app
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (A : AffineEtale B S hS X.1) :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointMeromorphicModule F
    Function.Surjective ((sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1}
        (P.genericPointMeromorphicModule η.2 F)).val.app
      (op ((AffineEtale.inclusion B S hS X.1).obj A))) := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := P.hasCoproduct_genericPointMeromorphicModule F
  intro b
  refine Stacks.SheafOfModules.exists_preimage_of_finite_support
    (fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule η.2 F))
    (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1} (P.genericPointMeromorphicModule η.2 F))
    (fun i j => ι_comp_sigmaPiComparison_comp_π _ i j)
    (op ((AffineEtale.inclusion B S hS X.1).obj A)) b
    (finite_codimensionZeroPoints_mem_range (X := X) hfin
      ((AffineEtale.inclusion B S hS X.1).obj A) A.2).toFinset fun η hη => ?_
  have hV : ∀ z : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
        ((AffineEtale.inclusion B S hS X.1).obj A))),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
          ((AffineEtale.inclusion B S hS X.1).obj A)))
        ((AffineEtale.inclusion B S hS X.1).obj A).1.hom z ≠ η.1 :=
    fun z hz => hη ((Set.Finite.mem_toFinset _).mpr ⟨z, hz⟩)
  have := P.subsingleton_genericPointMeromorphicModule_obj η.2 F
    ((AffineEtale.inclusion B S hS X.1).obj A) hV
  exact Subsingleton.elim _ _

/-- **The direct sum of the direct images is their product.**  The comparison is locally
injective because the direct sum of sheaves is locally the sectionwise direct sum, which injects
into the product; and it is surjective on the sections over every affine étale chart, because
only finitely many of the direct images have nonzero sections there, so it is locally
surjective. -/
theorem isIso_sigmaPiComparison_genericPointMeromorphicModule
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
    letI := P.hasCoproduct_genericPointMeromorphicModule F
    IsIso (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
      SheafOfModules.uliftObj.{_, _, _, _, u + 1}
        (P.genericPointMeromorphicModule η.2 F)) := by
  let : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
  let := P.hasCoproduct_genericPointMeromorphicModule F
  have := P.isLocallyInjective_sigmaPiComparison_genericPointMeromorphicModule F
  have : PresheafOfModules.IsLocallySurjective (meromorphicRingedSite B S hS X.1 X.2).J
      (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
        SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          (P.genericPointMeromorphicModule η.2 F)).val :=
    Stacks.PresheafOfModules.isLocallySurjective_of_surjective_of_isCoverDense _
      (AffineEtale.inclusion B S hS X.1)
      (SmallEtale.isCoverDense_affineEtaleInclusion B S hS X.1 X.2) _
      fun A => P.surjective_sigmaPiComparison_genericPointMeromorphicModule_app hfin F A
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective _

/-! ### Stacks 0ENA, the second conclusion -/

/-- **Stacks 0ENA, the second conclusion.** Let `X` be an algebraic space over a scheme `S` such
that

* (a) every weakly associated point of `X` is a point of codimension `0`,
* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many irreducible
  components, the condition of Stacks 0BB1, and
* (c) every point of codimension `0` of `X` is represented by a monomorphism from the spectrum
  of a field.

Then the local rings `𝒪_{X, η}` at the points `η ∈ X⁰` of codimension `0` and the canonical
morphisms `j_η : Spec(𝒪_{X, η}) ⟶ X` are defined — this is the presentation `P` of the
schematic locus whose existence is `AlgebraicGeometry.Space.exists_codimensionZeroPresentation`
— and for every quasi-coherent `𝒪_X`-module `F` the sheaf `𝒦_X(F)` of meromorphic sections of
`F` is both the direct sum and the product over `X⁰` of the direct images `j_{η, *}j_η^*F` of the
inverse images of `F`:

`𝒦_X(F) = ⨁_{η ∈ X⁰} j_{η, *}j_η^*F = ∏_{η ∈ X⁰} j_{η, *}j_η^*F`.

The two identifications are the canonical comparisons: the one into the product is
`AlgebraicGeometry.Space.CodimensionZeroPresentation.meromorphicSectionGenericPointComparisonPi`,
the transpose across sheafification of the family `a ⊗ s ↦ a · s|_{U ×_X Spec(𝒪_{X, η})}`, and
the one out of the direct sum is `CategoryTheory.Limits.sigmaPiComparison`, the identity on the
diagonal and zero off it. -/
@[stacks 0ENA "the second conclusion: for every quasi-coherent module the sheaf of its
meromorphic sections is the direct sum, and equally the product, over the codimension-zero points
of the direct images of its inverse images there, through the canonical comparisons"]
theorem exists_codimensionZeroPresentation_isIso_meromorphicSectionComparison
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X.1) :
    ∃ P : CodimensionZeroPresentation B S hS X.1,
      ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
        IsIso (P.meromorphicSectionGenericPointComparisonPi F) ∧
          letI : DecidableEq (CodimensionZeroPoints B S hS X.1) := Classical.decEq _
          letI := P.hasCoproduct_genericPointMeromorphicModule F
          IsIso (sigmaPiComparison fun η : CodimensionZeroPoints B S hS X.1 =>
            SheafOfModules.uliftObj.{_, _, _, _, u + 1}
              (P.genericPointMeromorphicModule η.2 F)) := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS X.2 hfin hmono
  exact ⟨P, fun F hF => ⟨P.isIso_meromorphicSectionGenericPointComparisonPi hwa hfin F hF,
    P.isIso_sigmaPiComparison_genericPointMeromorphicModule hfin F⟩⟩

end CodimensionZeroPresentation

end AlgebraicGeometry.Space

end
