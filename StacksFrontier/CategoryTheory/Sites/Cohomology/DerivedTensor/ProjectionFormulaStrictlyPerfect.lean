module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackAsATriangulatedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# Exactness of the two sides of the projection formula on a ringed topos

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites, and let `E ∈ D(O_C)`.  Equation 21.50.0.1 of [Stacks, Tag 0B56] is a map

`Rf_*E ⊗^L_{O_D} K ⟶ Rf_*(E ⊗^L_{O_C} Lf^*K)`

natural in `K ∈ D(O_D)`, so it is the component at `K` of a natural transformation between two
functors `D(O_D) ⥤ D(O_D)`.  This module exhibits that transformation, proves that both of its
functors are exact, and proves that invertibility of its component at `K` depends only on the
isomorphism class of `K`.

## Main definitions

All in the namespace `Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi`.

* `derivedPushforwardCommShift` — the derived pushforward of a morphism of ringed topoi
  commutes with the shift.
* `projectionFormulaSource`, `projectionFormulaTarget` — the two functors of `K` whose
  components Equation 21.50.0.1 relates.
* `projectionFormulaTransformation` — Equation 21.50.0.1 as a natural transformation.
* `projectionFormulaSourceCommShift`, `projectionFormulaTargetCommShift` — the source and the
  target functors commute with the shift.

## Main results

* `derivedPushforward_isTriangulated` — the derived pushforward of a morphism of ringed topoi
  is exact.
* `projectionFormulaSource_isTriangulated`, `projectionFormulaTarget_isTriangulated` — the two
  sides of Equation 21.50.0.1 are exact functors of `K`.
* `isIso_projectionFormulaMap_of_iso_target`, `isIso_projectionFormulaMap_congr_target` —
  invertibility of Equation 21.50.0.1 depends on `K` only through its isomorphism class.

## Implementation notes

The derived pushforward is the right adjoint of `Lf^*` in the derived adjunction of
[Stacks, Tag 07A6], and `Lf^*` commutes with the shift ([Stacks, Tag 06YY],
`Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_commShift`) and is exact when `f` is
presented by a morphism of sites
(`DerivedPullbackOnRingedTopoi.derivedPullback_isTriangulated_of_isMorphismOfSites`); so
`CategoryTheory.Adjunction.rightAdjointCommShift` and
`CategoryTheory.Adjunction.isTriangulated_rightAdjoint` give the shift compatibility and the
exactness of the pushforward.

The shift compatibilities are `@[instance_reducible] def`s, not instances, and the exactness
statements carry them in a `letI` in their own types: `derivedPushforwardCommShift` depends on
`hmos`, which is not an instance, and the shift compatibility of the derived tensor product of
[Stacks, Tag 06YU] is the `commShift_right` field of a structure.

Invertibility of Equation 21.50.0.1 for perfect `K`, [Stacks, Tag 0944], is not proved here. Its
proof also needs the case `K = O_D[n]`, which uses the right-unitor coherence of the comparison of
[Stacks, Tag 07A4] (as in the ringed-space base case, Tag 08EU), and the compatibility of Equation
21.50.0.1 with base change along a localization morphism.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-! ### Shift compatibility and exactness of the derived pushforward -/

include hmos in
/-- **The derived pushforward of a morphism of ringed topoi commutes with the shift.**  It is
the right adjoint in the derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6], and its left
adjoint `Lf^*` commutes with the shift by [Stacks, Tag 06YY]. -/
@[instance_reducible]
def derivedPushforwardCommShift : (derivedPushforward f).CommShift ℤ :=
  (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).rightAdjointCommShift ℤ

include hmos in
/-- **The derived pushforward of a morphism of ringed topoi is exact.**  It is the right adjoint
of `Lf^*`, which is exact by [Stacks, Tag 06YY] when `f` is presented by a morphism of sites. -/
theorem derivedPushforward_isTriangulated :
    letI := derivedPushforwardCommShift f hmos
    (derivedPushforward f).IsTriangulated :=
  let := derivedPushforwardCommShift f hmos
  let : (derivedPullback f).IsTriangulated :=
    DerivedPullbackOnRingedTopoi.derivedPullback_isTriangulated_of_isMorphismOfSites f hmos
  let : (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).CommShift ℤ :=
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).commShift_of_leftAdjoint ℤ
  (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).isTriangulated_rightAdjoint

/-! ### Equation 21.50.0.1 as a natural transformation -/

section Transformation

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The functor `K ↦ Rf_*E ⊗^L_{O_D} K`, the source of Equation 21.50.0.1. -/
abbrev projectionFormulaSource :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E)

/-- The functor `K ↦ Rf_*(E ⊗^L_{O_C} Lf^*K)`, the target of Equation 21.50.0.1. -/
abbrev projectionFormulaTarget :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f

include hmos in
/-- **Equation 21.50.0.1 of [Stacks, Tag 0B56] as a natural transformation** of functors of the
complex on the base.  Its component at `K` is
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K`, and its
naturality is `projectionFormulaMap_naturality_target`. -/
@[stacks 0B56 "the map as a natural transformation in the target complex"]
def projectionFormulaTransformation :
    projectionFormulaSource f E ⟶ projectionFormulaTarget f E where
  app := ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
  naturality _ _ k := ProjectionFormulaOnRingedTopoi.projectionFormulaMap_naturality_target
    f hmos E k

/-- The component of `projectionFormulaTransformation f hmos E` at `K` is
`ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K`. -/
@[simp]
lemma projectionFormulaTransformation_app
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (projectionFormulaTransformation f hmos E).app K =
      ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K :=
  rfl

/-- The source functor `K ↦ Rf_*E ⊗^L_{O_D} K` commutes with the shift: it is the derived
tensor product of [Stacks, Tag 06YU] with a fixed object in the first variable. -/
@[instance_reducible]
def projectionFormulaSourceCommShift : (projectionFormulaSource f E).CommShift ℤ :=
  (canonicalDerivedTensorProduct Y.O).commShift_right _

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)] in
/-- The source functor is exact: tensoring with a fixed object is exact by
[Stacks, Tag 06YU]. -/
theorem projectionFormulaSource_isTriangulated :
    letI := projectionFormulaSourceCommShift f E
    (projectionFormulaSource f E).IsTriangulated :=
  (canonicalDerivedTensorProduct Y.O).exact_right _

include hmos in
/-- The target functor `K ↦ Rf_*(E ⊗^L_{O_C} Lf^*K)` commutes with the shift: it is a composite
of three functors that do. -/
@[instance_reducible]
def projectionFormulaTargetCommShift : (projectionFormulaTarget f E).CommShift ℤ :=
  letI : ((derivedTensorProductFunctor X.O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.O).commShift_right _
  letI := derivedPushforwardCommShift f hmos
  Functor.CommShift.comp _ _

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)] in
include hmos in
/-- The target functor is exact: it is a composite of the three exact functors `Lf^*`,
`E ⊗^L_{O_C} -` and `Rf_*`. -/
theorem projectionFormulaTarget_isTriangulated :
    letI := projectionFormulaTargetCommShift f hmos E
    (projectionFormulaTarget f E).IsTriangulated :=
  let : ((derivedTensorProductFunctor X.O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.O).commShift_right _
  let : ((derivedTensorProductFunctor X.O).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct X.O).exact_right _
  let := derivedPushforwardCommShift f hmos
  let := derivedPushforward_isTriangulated f hmos
  let : (derivedPullback f).IsTriangulated :=
    DerivedPullbackOnRingedTopoi.derivedPullback_isTriangulated_of_isMorphismOfSites f hmos
  let : ((derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f).CommShift ℤ :=
    Functor.CommShift.comp _ _
  inferInstanceAs ((derivedPullback f ⋙ ((derivedTensorProductFunctor X.O).obj E ⋙
    derivedPushforward f)).IsTriangulated)

end Transformation

section IsoTransport

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]

/-! ### Invariance under isomorphism of the complex on the base

Invertibility of Equation 21.50.0.1 at `K` is a property of the isomorphism class of `K`, the form
in which the dévissage of [Stacks, Tag 0944] uses it. -/

include hmos in
/-- **Invertibility of Equation 21.50.0.1 transports along an isomorphism of the complex on the
base.** -/
theorem isIso_projectionFormulaMap_of_iso_target
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (i : K ≅ K')
    (h : IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K)) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K') :=
  IsIso.of_isIso_fac_left
    (ProjectionFormulaOnRingedTopoi.projectionFormulaMap_naturality_target f hmos E i.hom)

include hmos in
/-- Invertibility of Equation 21.50.0.1 depends on the complex on the base only through its
isomorphism class. -/
theorem isIso_projectionFormulaMap_congr_target
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (i : K ≅ K') :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K) ↔
      IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E K') :=
  ⟨isIso_projectionFormulaMap_of_iso_target f hmos E i,
    isIso_projectionFormulaMap_of_iso_target f hmos E i.symm⟩

end IsoTransport

end Stacks.Cohomology.ProjectionFormulaPerfectOnRingedTopoi

end
