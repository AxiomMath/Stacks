module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartConormalTensor
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatTangentLiftClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.RetractionSection
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentLiftClassIdentification
public import StacksFrontier.Deformation.ToposThickening.SplitBaseSolutionCotangentClass

/-!
# The tangent space of `Spaces'_{fp, flat, proper}` at a chart is `Ext¹(L_{X/A}, 𝒪_X ⊗_A M)`

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart. This file
identifies the lift classes of `x` over `A[M]` with `T¹(M) = Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)`,
naturally in `M`, and so the tangent functor of `x` (Stacks 07Y9) with `T¹` as `A`-linear functors.
This is the tangent part of the deformation theory of Remark 0D1P.

The identification is the composite of

* lifts of `x` along `Spec A ⊂ Spec A'` are flat deformations of `X → Spec A` (Stacks 0D17);
* flat deformations are solutions of the extension problem of [Stacks, Section 08V3]
  (`AlgebraicGeometry.Space.FlatThickeningDeformation.classesEquiv`);
* solutions on the small étale site are solutions on its `Type u` model;
* over a base thickening retracted onto `Spec A`, a solution is an extension of
  `f⁻¹𝒪_{Spec A}`-algebras, classified by `Ext¹(L, 𝒢)` (Stacks 0GQ5, 08V2);
* `L` of the problem is `L_{X/A}` and `𝒢 = 𝒪_X ⊗_A I`.

## Conventions

The tangent class is **minus** the class of Stacks 0GQ5 of the extension of algebras. This is the
sign for which the obstruction class `o = −(δ.comp γ)` of the problem is the connecting map of a
tangent class without a sign (condition (iv) of Stacks 07YY), the class of a solution being minus
its class of Stacks 0GQ5
(`Deformation.ToposThickening.RingedToposExtensionProblem.solutionNaiveClass_eq_neg_extClass`).

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.retractedLiftClassesEquivCotangentExtOne`: for a
  square-zero thickening `Spec A ⊂ Spec A'` retracted onto `Spec A`, lift classes are
  `T¹(I)`.
* `AlgebraicGeometry.Space.properFlatLiftClassExtEquiv`: lift classes over `A[M]` are `T¹(M)`.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Deformation.ToposThickening RingedToposExtensionProblem

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')
  (ρ : ambient (T' := Over.mk D.toS') ⟶
    (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
      (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS))
  (hρ : subspaceInclusion B S hS ambient
    (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)) ≫ ρ = 𝟙 _)

/-- The extension problem of `X → Spec A ⊂ Spec A'`, on the small étale site of `X`. -/
abbrev tangentEtaleProblem :=
  FlatThickeningDeformation.problem (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx)
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))

/-- The extension problem of `X → Spec A ⊂ Spec A'`, on the `Type u` model of the small étale site
of `X`. -/
abbrev tangentModelProblem :=
  (tangentEtaleProblem x hx D).siteTransport (smallEtaleModelTopology B S hS x.obj.obj.left.1)
    (smallEtaleModelEquiv B S hS x.obj.obj.left)

/-- **Lift classes are solution classes on the model**: Stacks 0D17 followed by the transport of
the problem to the model of the small étale site. -/
def liftClassesEquivModelSolutionClasses :
    Quotient (isIsomorphicSetoid (Lift D.arrow x hx)) ≃
      CompatibleFirstOrderThickening.IsomorphismClasses.{u, u, u, u, u + 1, u}
        (tangentModelProblem x hx D) :=
  (liftClassesEquivDeformationClasses D.arrow (isSquareZeroClosedImmersion_arrow D) x hx).trans
    ((FlatThickeningDeformation.classesEquiv _ _ (isFlat_specialMap_arrow x hx D)).trans
      (siteTransportIsomorphismClassesEquiv _ _ (tangentEtaleProblem x hx D)))

/-- The section `𝒪_{Spec A} ⟶ t⁻¹𝒪_{Spec A'}` of the base thickening given by the retraction
`ρ`. -/
abbrev tangentRetractionSection :
    (smallEtaleRingedTopos B S hS
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
          AlgebraicSpaces B S hS)).O ⟶ (tangentModelProblem x hx D).baseExtension :=
  FlatThickeningDeformation.retractionSection
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))
    ρ hρ

/-- The section `tangentRetractionSection` is a section of the reduction
`t⁻¹𝒪_{Spec A'} ⟶ 𝒪_{Spec A}`. -/
theorem tangentRetractionSection_comp :
    tangentRetractionSection x hx D ρ hρ ≫ (tangentModelProblem x hx D).baseReduction = 𝟙 _ :=
  FlatThickeningDeformation.retractionSection_comp_reduction
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))
    ρ hρ

variable [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The tangent class of a solution over a retracted thickening**: minus the class of
Stacks 0GQ5 of the solution, read through the retraction as an extension of
`f⁻¹𝒪_{Spec A}`-algebras, in `Ext¹(L, 𝒢)` of the problem on the model. -/
def tangentSolutionClass
    (P : (tangentModelProblem x hx D).CompatibleFirstOrderThickening) :
    (tangentModelProblem x hx D).f.cotangentExt ((tangentModelProblem x hx D).targetG) 1 :=
  -(tangentModelProblem x hx D).splitCotangentClass (tangentRetractionSection x hx D ρ hρ)
    (tangentRetractionSection_comp x hx D ρ hρ) P

/-- **The tangent classes over a retracted thickening are `Ext¹(L, 𝒢)` of the problem.** -/
def modelSolutionClassesEquivCotangentExt :
    CompatibleFirstOrderThickening.IsomorphismClasses.{u, u, u, u, u + 1, u}
        (tangentModelProblem x hx D) ≃
      (tangentModelProblem x hx D).f.cotangentExt ((tangentModelProblem x hx D).targetG) 1 :=
  ((tangentModelProblem x hx D).splitSolutionClassesEquivCotangentExt
    (tangentRetractionSection x hx D ρ hρ) (tangentRetractionSection_comp x hx D ρ hρ)).trans
    (Equiv.neg _)

/-- The pulled-back conormal module `f^*𝒞` of the problem, on the model: the prescribed module of
`tangentModelProblem`. -/
abbrev tangentModelConormal :=
  (Deformation.AlgebraExtension.moduleRes (smallEtaleModelTopology B S hS x.obj.obj.left.1)
        (smallEtaleModelEquiv B S hS x.obj.obj.left).inverse
        (smallEtaleRingedTopos B S hS x.obj.obj.left).O).obj
        (FlatThickeningDeformation.pulledBackConormal (Z := baseSubspace D.arrow
          (isSquareZeroClosedImmersion_arrow D))
          (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x hx))

/-- The cotangent complex `L` of the problem on the model is `L_{X/A}`. -/
def tangentProblemCotangentComplexIso :
    (modelRingedToposHom (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x
      hx)).cotangentComplexDerived ≅
        (modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived :=
  eqToIso (congrArg (fun g : x.obj.obj.left ⟶
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ :
          AlgebraicSpaces B S hS) => (modelRingedToposHom g).cotangentComplexDerived)
    (specialMap_arrow_eq x hx D)) ≪≫ chartCotangentComplexIso x hx D

/-- `Ext¹(L, 𝒢)` of the problem on the model is `Ext¹(L_{X/A}, 𝒪_X ⊗_A I)`, through
`L = L_{X/A}` (`tangentProblemCotangentComplexIso`) and `𝒢 = 𝒪_X ⊗_A I`
(`thickeningModelConormalIso`). -/
def tangentCotangentExtHomEquiv :
    (tangentModelProblem x hx D).f.cotangentExt (tangentModelProblem x hx D).targetG 1 ≃
      ((modelRingedToposHom (chartStructureMap x hx)).cotangentComplexDerived ⟶
        ((DerivedCategory.singleFunctor (modelModules x.obj.obj.left) 0).obj
          ((modelTensorFunctor (chartBaseRingHom x hx)).obj D.kernel))⟦(1 : ℤ)⟧) :=
  (Iso.homCongr (tangentProblemCotangentComplexIso x hx D)
      ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).mapIso
        (thickeningModelConormalIso x hx D)) :
    ((modelRingedToposHom (specialMap D.arrow (isSquareZeroClosedImmersion_arrow D) x
      hx)).cotangentComplexDerived ⟶
        ((DerivedCategory.singleFunctor (modelModules x.obj.obj.left) 0).obj
          (tangentModelConormal x hx D))⟦(1 : ℤ)⟧) ≃ _)

/-- `Ext¹(L, 𝒢)` of the problem on the model is `T¹(I)`. -/
def tangentCotangentExtEquiv :
    (tangentModelProblem x hx D).f.cotangentExt (tangentModelProblem x hx D).targetG 1 ≃
      (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj D.kernel :=
  (tangentCotangentExtHomEquiv x hx D).trans
    (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 1
      D.kernel).symm.toEquiv

/-- **Lift classes over a retracted square-zero thickening are `T¹(I)`.** For a square-zero
thickening `Spec A ⊂ Spec A'` of Situation 07YX with ideal `I`, retracted onto `Spec A` by `ρ`,
the isomorphism classes of lifts of `x` to `Spec A'` are in bijection with
`Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`: a lift is a flat deformation, hence a solution of the
extension problem of [Stacks, Section 08V3], hence (through `ρ`) an extension of
`f⁻¹𝒪_{Spec A}`-algebras, sent to minus its class of Stacks 0GQ5. -/
def retractedLiftClassesEquivCotangentExtOne :
    Quotient (isIsomorphicSetoid (Lift D.arrow x hx)) ≃
      (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj D.kernel :=
  (liftClassesEquivModelSolutionClasses x hx D).trans
    ((modelSolutionClassesEquivCotangentExt x hx D ρ hρ).trans (tangentCotangentExtEquiv x hx D))

end AlgebraicGeometry.Space.ProperFlatLift

namespace AlgebraicGeometry.Space

open Deformation.Artin ProperFlatLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-! ### The trivial square-zero thickening `Spec A ⊂ Spec A[M]` -/

section Trivial

variable (hS toS hA) (M : SiteModule A B)

/-- **The trivial square-zero extension `A[M] → A` as a thickening of Situation 07YX**: its closed
immersion is `Spec A ⟶ Spec A[M]` of the tangent functor (Stacks 07Y9). -/
def squareZeroThickeningOfModule :
    SquareZeroThickening A B S hS toS hA (TrivSqZeroExt A M.obj) where
  q := (TrivSqZeroExt.fstHom A A M.obj).toRingHom
  squareZeroSurjection := ⟨fun a => ⟨TrivSqZeroExt.inl a, rfl⟩, squareZeroProjection_ker_sq A M.obj⟩
  hA' := M.property
  toS' := (squareZeroOver A B S hS toS M).hom
  arrow := squareZeroArrow A B S hS toS hA M
  arrow_spec := rfl

/-- The constants `A ⟶ A[M]`, as the retraction `Spec A[M] ⟶ Spec A` over `S`. -/
def squareZeroConstants : squareZeroOver A B S hS toS M ⟶ algebraOver A B S hS toS hA :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))) :
    B.obj M.property ⟶ B.obj hA) rfl

/-- The closed immersion `Spec A ⟶ Spec A[M]` followed by the constants `Spec A[M] ⟶ Spec A` is the
identity. -/
theorem squareZeroArrow_comp_squareZeroConstants :
    squareZeroArrow A B S hS toS hA M ≫ squareZeroConstants hS toS hA M = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) = 𝟙 _
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom = 𝟙 (CommRingCat.of A) :=
    CommRingCat.hom_ext (RingHom.ext fun _ => rfl)
  rw [← Spec.map_comp, h, Spec.map_id]

/-- The retraction of the closed subspace `Spec A ⊆ Spec A[M]` by the constants. -/
def squareZeroRetraction :
    ambient (T' := Over.mk (squareZeroThickeningOfModule hS toS hA M).toS') ⟶
      (⟨(baseSubspace (squareZeroThickeningOfModule hS toS hA M).arrow
          (isSquareZeroClosedImmersion_arrow
            (squareZeroThickeningOfModule hS toS hA M))).1.toFunctor,
        (baseSubspace (squareZeroThickeningOfModule hS toS hA M).arrow
          (isSquareZeroClosedImmersion_arrow (squareZeroThickeningOfModule hS toS hA M))).2.1⟩ :
            AlgebraicSpaces B S hS) :=
  schemeSpaceMap (squareZeroConstants hS toS hA M) ≫
    (rangeSpaceIso B S hS (squareZeroThickeningOfModule hS toS hA M).arrow
      (isSquareZeroClosedImmersion_arrow (squareZeroThickeningOfModule hS toS hA M)).1).hom

/-- `squareZeroRetraction` is a retraction of the inclusion of the closed subspace
`Spec A ⊆ Spec A[M]`. -/
theorem subspaceInclusion_comp_squareZeroRetraction :
    subspaceInclusion B S hS ambient (baseSubspace (squareZeroThickeningOfModule hS toS hA M).arrow
        (isSquareZeroClosedImmersion_arrow (squareZeroThickeningOfModule hS toS hA M))) ≫
      squareZeroRetraction hS toS hA M = 𝟙 _ := by
  let ρ := rangeSpaceIso B S hS (squareZeroThickeningOfModule hS toS hA M).arrow
    (isSquareZeroClosedImmersion_arrow (squareZeroThickeningOfModule hS toS hA M)).1
  have h₁ : subspaceInclusion B S hS ambient (baseSubspace
      (squareZeroThickeningOfModule hS toS hA M).arrow
      (isSquareZeroClosedImmersion_arrow (squareZeroThickeningOfModule hS toS hA M))) =
        ρ.inv ≫ schemeSpaceMap (squareZeroThickeningOfModule hS toS hA M).arrow :=
    (Iso.eq_inv_comp ρ).2 (rangeSpaceIso_hom_comp_subspaceInclusion B S hS _ _)
  have h₂ : schemeSpaceMap (squareZeroThickeningOfModule hS toS hA M).arrow ≫
      schemeSpaceMap (squareZeroConstants hS toS hA M) = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact (yoneda.map_comp (squareZeroArrow A B S hS toS hA M)
      (squareZeroConstants hS toS hA M)).symm.trans
        ((congrArg yoneda.map (squareZeroArrow_comp_squareZeroConstants hS toS hA M)).trans
          (yoneda.map_id _))
  rw [h₁]
  exact (Category.assoc _ _ _).trans ((congrArg (ρ.inv ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ρ.hom) h₂).trans (Category.id_comp _)))).trans ρ.inv_hom_id)

/-- The kernel of `A[M] → A` is `M`. -/
def squareZeroThickeningKernelIso :
    (squareZeroThickeningOfModule hS toS hA M).kernel ≅ M.obj :=
  letI := Stacks.Smooth.kerModule
    (squareZeroThickeningOfModule hS toS hA M).squareZeroSurjection.1
    (squareZeroThickeningOfModule hS toS hA M).squareZeroSurjection.2
  LinearEquiv.toModuleIso
    { toFun := fun k => (k : RingHom.ker (TrivSqZeroExt.fstHom A A M.obj).toRingHom).1.snd
      invFun := fun m => (⟨TrivSqZeroExt.inr m, TrivSqZeroExt.fst_inr A m⟩ :
        RingHom.ker (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
      map_add' := fun _ _ => rfl
      map_smul' := fun a k => by
        have h := Stacks.Smooth.kerModule_smul
          (squareZeroThickeningOfModule hS toS hA M).squareZeroSurjection.1
          (squareZeroThickeningOfModule hS toS hA M).squareZeroSurjection.2
          (TrivSqZeroExt.inl a) (k : RingHom.ker (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
        refine (congrArg (fun y : RingHom.ker (TrivSqZeroExt.fstHom A A M.obj).toRingHom =>
          (y : TrivSqZeroExt A M.obj).snd) h).trans ?_
        change (TrivSqZeroExt.inl a * (k.1 : TrivSqZeroExt A M.obj)).snd = a • (k.1.snd : M.obj)
        rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero,
          add_zero]
      left_inv := fun k => Subtype.ext (TrivSqZeroExt.ext
        ((k : RingHom.ker (TrivSqZeroExt.fstHom A A M.obj).toRingHom).2.symm) rfl)
      right_inv := fun _ => rfl }

end Trivial

/-! ### The tangent identification -/

variable (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The lift classes of `Spaces'_{fp, flat, proper}` over `A[M]` are
`Ext¹_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)`** (Remark 0D1P). A lift of `x = (X → Spec A)` to `Spec A[M]` is
a flat deformation of `X` over `Spec A[M]` (Stacks 0D17), hence a solution of the extension
problem of [Stacks, Section 08V3], hence, through the constants `A → A[M]`, an extension
`0 → 𝒪_X ⊗_A M → 𝒪' → 𝒪_X → 0` of `f⁻¹𝒪_{Spec A}`-algebras, sent to minus its class of
Stacks 0GQ5 in `Ext¹(NL_{X/A}, 𝒪_X ⊗_A M) = Ext¹(L_{X/A}, 𝒪_X ⊗_A M)`. -/
def properFlatLiftClassExtEquiv (M : SiteModule A B) :
    squareZeroLiftClasses A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx M ≃
      (cotangentExtOne (ProperFlatLift.chartStructureMap x hx)
        (ProperFlatLift.chartBaseRingHom x hx)).obj M.obj :=
  (retractedLiftClassesEquivCotangentExtOne x hx (squareZeroThickeningOfModule hS toS hA M)
      (squareZeroRetraction hS toS hA M)
      (subspaceInclusion_comp_squareZeroRetraction hS toS hA M)).trans
    ((cotangentExtOne (ProperFlatLift.chartStructureMap x hx)
      (ProperFlatLift.chartBaseRingHom x hx)).mapIso
        (squareZeroThickeningKernelIso hS toS hA M)).toLinearEquiv.toEquiv

end AlgebraicGeometry.Space

end
