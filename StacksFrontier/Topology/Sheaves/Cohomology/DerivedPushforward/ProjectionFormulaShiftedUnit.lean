module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaFiniteFreeSummand
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract

/-!
# The projection formula at every shift of the structure sheaf, and the direct sums it needs

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E` an object of `D(𝒪_X)`.
This file proves, with **no hypothesis at all**, that the derived projection-formula morphism of
[Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism for every `K` isomorphic to a shift `𝒪_Y[0]⟦n⟧` of the structure sheaf in
degree zero — hence for `𝒪_Y` placed in *every* degree, and not only in degree zero as
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_single_zero` had it.  The
dévissage of [Stacks, Tag 0B54] is then unconditional for a strictly perfect complex.

## Main results

* `Stacks.Cohomology.ProjectionFormulaShiftedUnit.isIso_projectionFormulaMap_of_iso_shift_unit`:
  the projection-formula morphism is invertible at every `K ≅ 𝒪_Y[0]⟦n⟧`.
* `Stacks.Cohomology.ProjectionFormulaShiftedUnit.isIso_projectionFormulaMap_single_shift`: the
  same in the form `∀ i n : ℤ`, at `(𝒪_Y[i])⟦n⟧`, which is the hypothesis `hunit` of
  `Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect`.
* `Stacks.Cohomology.ProjectionFormulaShiftedUnit.isIso_projectionFormulaMap_isStrictlyPerfect`:
  **the dévissage half of [Stacks, Tag 0B54] with no hypothesis**: the projection-formula
  morphism is invertible at every strictly perfect complex of `𝒪_Y`-modules.
* `Stacks.Cohomology.ProjectionFormulaShiftedUnit.isLeftAdjoint_derivedTensorProductFunctor_obj`
  and `preservesColimitsOfSize_projectionFormulaSource`: the functor
  `K ↦ Rf_*E ⊗^𝐋_{𝒪_Y} K` is a left adjoint, so it commutes with arbitrary direct sums.
* `Stacks.Cohomology.ProjectionFormulaShiftedUnit.preservesColimitsOfSize_projectionFormulaTarget`:
  the functor `K ↦ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)` commutes with direct sums as soon as `Rf_*` does;
  the two other factors are left adjoints.

## Implementation notes

*What replaces the right-unitor coherence.*  The degree-zero case,
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`,
is proved from the right-unitor coherence of the comparison of [Stacks, Tag 079U] on K-flat
representatives, and that route does not move off degree zero: it would need a right unitor
`Z ⊗^𝐋 𝒪_Y[i] ≅ Z⟦-i⟧` natural in `Z` together with a shifted analogue of the coherence.  The
implementation notes of the modules
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaFiniteFreeSummand`
and `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect` record
that obstruction, and conclude from it that the degrees other than zero are unavailable.
**That conclusion is what this file removes**, by not using the coherence at all.

The route is `Stacks.ProjectionFormula.isIso_adjunctionTensorMap`, which asks instead that
tensoring on the right by `K` and by `Lf^*K` be *equivalences* and that the comparison of
[Stacks, Tag 079U] be invertible in its first argument at `K`.  The last is free: the comparison
is the `hom` of the natural isomorphism
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`.  The first two are
invertibility of the object `𝒪_Y[0]⟦n⟧`, and that is formal in any monoidal category whose
tensor product commutes with the shift on the left:
`(𝟙_)⟦n⟧ ⊗ (𝟙_)⟦-n⟧ ≅ 𝟙_` by `shiftUnitInverseIso`, so `- ⊗ (𝟙_)⟦n⟧` is an equivalence.

*Where the monoidal structure comes from.*  `Stacks.SheafOfModules.DerivedMonoidal`'s
`canonicalDerivedMonoidal` is the symmetric monoidal structure of [Stacks, Tag 0FPT] re-seated so
that its curried tensor product **equals** `Stacks.DerivedTensor.RingedSite`'s
`derivedTensorProductFunctor` and its unit **equals** the structure sheaf in degree zero
(`curriedTensor_canonicalDerivedMonoidal`, `tensorUnit_canonicalDerivedMonoidal`).  Those two
equalities are what make the formal argument land on the bifunctor [Stacks, Tag 0B53] is stated
over; no transport of the projection-formula morphism is involved.  The shift compatibility
`(tensorLeft A).CommShift ℤ` the formal argument needs is the `commShift_right` projection of
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` read across the first equality —
only the existence of that datum is used, never a formula for it, which is why the fact that the
structure is made opaque with `irreducible_def` is no obstruction here.

*The passage from `tensorRightOf` to `tensorRight`.*  The abstract statement is phrased with
`Stacks.ProjectionFormula.tensorRightOf A H`, `M ↦ A (M, H)`, for the *uncurried* bifunctor; the
monoidal `tensorRight H` is `M ↦ (T.obj M).obj H` for the curried one.  The two differ only by
the identity `A.map (g ×ₘ 𝟙 H) = (T.map g).app H`, which is
`Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right`, so they are identified by a
natural isomorphism with identity components.

*The direct sums.*  Both halves of the last two results come from adjunctions already in the
library and neither is a new computation: `- ⊗^𝐋_{𝒪} B` is the left adjoint of
`RSheafHom(B, -)` by [Stacks, Tag 08J8]
(`AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction`), and `Lf^*` is the left
adjoint in the derived adjunction of [Stacks, Tag 079W].  What is *not* here, and is the
remaining input of the dévissage of [Stacks, Tag 08EU] over a general `K` in `D_QCoh(𝒪_Y)`, is
that `Rf_*` itself commutes with direct sums; it is a right adjoint, and on a bare ringed space
nothing forces it.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.ProjectionFormulaPerfect
open Stacks.DerivedTensor.RingedSite

universe v u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaShiftedUnit

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing Stacks.SheafOfModules.Tensor.ringSheaf
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-! ### Tensoring by a shift of the unit, in an arbitrary monoidal category -/

section Monoidal

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- **Tensoring on the right by an invertible object is an equivalence.**  An inverse is
tensoring by the object inverting it, the two unit laws being the two isomorphisms carried. -/
theorem isEquivalence_tensorRight_of_tensorIsoUnit (K L : C) (e₁ : K ⊗ L ≅ 𝟙_ C)
    (e₂ : L ⊗ K ≅ 𝟙_ C) : (MonoidalCategory.tensorRight K).IsEquivalence :=
  Functor.IsEquivalence.mk' (MonoidalCategory.tensorRight L)
    ((MonoidalCategory.tensorRightTensor K L).symm ≪≫
        (MonoidalCategory.tensoringRight C).mapIso e₁ ≪≫
      MonoidalCategory.rightUnitorNatIso C).symm
    ((MonoidalCategory.tensorRightTensor L K).symm ≪≫
      (MonoidalCategory.tensoringRight C).mapIso e₂ ≪≫
        MonoidalCategory.rightUnitorNatIso C)

variable [HasShift C ℤ] [∀ A : C, (MonoidalCategory.tensorLeft A).CommShift ℤ]

/-- **The shifts of the unit object are invertible**: `𝟙⟦n⟧ ⊗ 𝟙⟦-n⟧ ≅ 𝟙`.  Tensoring on the
left by `𝟙⟦n⟧` commutes with the shift, so the left-hand side is `(𝟙⟦n⟧ ⊗ 𝟙)⟦-n⟧`, which the
right unitor and `shiftFunctorCompIsoId` identify with `𝟙`. -/
def shiftUnitInverseIso (n : ℤ) : ((𝟙_ C)⟦n⟧) ⊗ ((𝟙_ C)⟦-n⟧) ≅ 𝟙_ C :=
  ((MonoidalCategory.tensorLeft ((𝟙_ C)⟦n⟧)).commShiftIso (-n)).app (𝟙_ C) ≪≫
    (shiftFunctor C (-n)).mapIso (ρ_ ((𝟙_ C)⟦n⟧)) ≪≫
    (shiftFunctorCompIsoId C n (-n) (by simp)).app (𝟙_ C)

/-- **Tensoring on the right by a shift of the unit object is an equivalence.** -/
theorem isEquivalence_tensorRight_shiftUnit (n : ℤ) :
    (MonoidalCategory.tensorRight ((𝟙_ C)⟦n⟧)).IsEquivalence := by
  apply isEquivalence_tensorRight_of_tensorIsoUnit _ ((𝟙_ C)⟦-n⟧) (shiftUnitInverseIso n)
  simpa using shiftUnitInverseIso (C := C) (-n)

end Monoidal

/-! ### The derived tensor product of a ringed space as a monoidal structure -/

section Concrete

variable (Y : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.SheafOfModules.DerivedMonoidal

/-- The symmetric monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪_Y)`, re-seated so that its
tensor product is the derived tensor product of [Stacks, Tag 06YU] and its unit is the structure
sheaf in degree zero.  It is a local instance: `D(𝒪_Y)` carries no monoidal structure globally,
and the two equalities below are what this file uses it for. -/
local instance monoidalDerivedCategory : MonoidalCategory
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  canonicalDerivedMonoidal Y.sheaf

/-- The curried tensor product of `monoidalDerivedCategory` is the derived tensor product of
[Stacks, Tag 06YU], the bifunctor [Stacks, Tag 0B53] is stated over. -/
theorem curriedTensor_eq :
    @MonoidalCategory.curriedTensor
          (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) _
        (monoidalDerivedCategory Y) =
      derivedTensorProductFunctor Y.sheaf :=
  curriedTensor_canonicalDerivedMonoidal Y.sheaf

/-- The unit of `monoidalDerivedCategory` is the structure sheaf placed in degree zero. -/
theorem tensorUnit_eq :
    (𝟙_ (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))) = singleUnit Y :=
  tensorUnit_canonicalDerivedMonoidal Y.sheaf

/-- Tensoring on the left commutes with the shift.  This is the `commShift_right` projection of the
canonical derived tensor product of [Stacks, Tag 06YU], read across `curriedTensor_eq`; only the
existence of the datum is used. -/
@[instance_reducible]
def tensorLeftCommShift (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (MonoidalCategory.tensorLeft A).CommShift ℤ := by
  have h : MonoidalCategory.tensorLeft A = (derivedTensorProductFunctor Y.sheaf).obj A :=
    congrArg (fun T => Functor.obj T A) (curriedTensor_eq Y)
  rw [h]
  exact (canonicalDerivedTensorProduct Y.sheaf).commShift_right A

/-- **Tensoring on the right by a shift of the structure sheaf in degree zero is an
equivalence of `D(𝒪_Y)`**, for the derived tensor product of [Stacks, Tag 06YU]. -/
theorem isEquivalence_derivedTensorFlip_shiftUnit (n : ℤ) :
    ((derivedTensorProductFunctor Y.sheaf).flip.obj
      ((shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n).obj
        (singleUnit Y))).IsEquivalence := by
  have := tensorLeftCommShift Y
  have hequiv := isEquivalence_tensorRight_shiftUnit
    (C := DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n
  have h : (derivedTensorProductFunctor Y.sheaf).flip.obj
      ((shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n).obj
        (singleUnit Y)) =
      MonoidalCategory.tensorRight ((𝟙_ (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing Y))))⟦n⟧) := by
    rw [← curriedTensor_eq Y, tensorUnit_eq Y]
  rw [h]
  exact hequiv

/-- `Stacks.ProjectionFormula.tensorRightOf` of the uncurried derived tensor product is the
functor `- ⊗^𝐋 K` of the curried one: the two differ only by
`Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right`, so they are identified by a
natural isomorphism with identity components. -/
theorem isEquivalence_tensorRightOf_of_flip
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (h : ((derivedTensorProductFunctor Y.sheaf).flip.obj K).IsEquivalence) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)) K).IsEquivalence := by
  have := h
  refine Functor.isEquivalence_of_iso (F := (derivedTensorProductFunctor Y.sheaf).flip.obj K)
    (NatIso.ofComponents (fun M => Iso.refl _) ?_)
  intro M N g
  exact (Category.comp_id _).trans
    ((uncurry_map_id_right (derivedTensorProductFunctor Y.sheaf) g K).symm.trans
      (Category.id_comp _).symm)

/-- **Tensoring on the right by any object isomorphic to a shift of the structure sheaf in
degree zero is an equivalence**, in the form the abstract projection formula asks for. -/
theorem isEquivalence_tensorRightOf_of_iso_shift_unit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (n : ℤ)
    (e : K ≅ (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n).obj
      (singleUnit Y)) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)) K).IsEquivalence := by
  have := isEquivalence_derivedTensorFlip_shiftUnit Y n
  exact isEquivalence_tensorRightOf_of_flip Y K
    (Functor.isEquivalence_of_iso ((derivedTensorProductFunctor Y.sheaf).flip.mapIso e).symm)

end Concrete

/-! ### The projection formula at every shift of the structure sheaf -/

section Main

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived projection-formula morphism of [Stacks, Tag 0B53] is invertible at every shift
of the structure sheaf in degree zero**, with no hypothesis: for an arbitrary morphism of ringed
spaces `f : X ⟶ Y`, an arbitrary `E` in `D(𝒪_X)`, an arbitrary `n : ℤ` and any `K` in `D(𝒪_Y)`
isomorphic to `𝒪_Y[0]⟦n⟧`, the morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism.

This is `Stacks.ProjectionFormula.isIso_adjunctionTensorMap` at the derived adjunction of
[Stacks, Tag 079W] and the comparison of [Stacks, Tag 079U].  Its three inputs are all
discharged: the comparison is the `hom` of a natural isomorphism, so it is invertible at every
pair; tensoring on the right by `K` is an equivalence by
`isEquivalence_tensorRightOf_of_iso_shift_unit`; and so is tensoring by `Lf^*K`, because `Lf^*`
commutes with the shift and carries `𝒪_Y[0]` to `𝒪_X[0]` by
`Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso`. -/
theorem isIso_projectionFormulaMap_of_iso_shift_unit
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (n : ℤ)
    (e : K ≅ (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) n).obj
      (singleUnit Y)) :
    IsIso (projectionFormulaMap f E K) := by
  have h1 := isEquivalence_tensorRightOf_of_iso_shift_unit Y K n e
  have e' : (derivedPullback f).obj K ≅
      (shiftFunctor (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) n).obj
        (singleUnit X) :=
    (derivedPullback f).mapIso e ≪≫ ((derivedPullback f).commShiftIso n).app (singleUnit Y) ≪≫
      (shiftFunctor _ n).mapIso (derivedPullbackUnitIso f)
  have h2 := isEquivalence_tensorRightOf_of_iso_shift_unit X ((derivedPullback f).obj K) n e'
  have hiso : IsIso (pullbackTensorComparison f) :=
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).isIso_hom
  exact @Stacks.ProjectionFormula.isIso_adjunctionTensorMap _ _ _ _ _ _
    (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) E K h1 h2
    (fun M => @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (pullbackTensorComparison f) hiso (M, K))

/-- **The projection-formula morphism is invertible at every shift of the structure sheaf placed
in every degree.**  This is the hypothesis `hunit` of
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect`,
discharged: `(𝒪_Y[i])⟦n⟧ ≅ 𝒪_Y[0]⟦-i + n⟧`, by the shift isomorphism of the family of
single-object functors and the additivity of the shift. -/
theorem isIso_projectionFormulaMap_single_shift
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i n : ℤ) :
    IsIso (projectionFormulaMap f E
      (((DerivedCategory.singleFunctor (OXMod.{u, u} Y) i).obj (structureModule Y))⟦n⟧)) := by
  refine isIso_projectionFormulaMap_of_iso_shift_unit f E _ (-i + n) ?_
  exact (shiftFunctor _ n).mapIso
      (((DerivedCategory.singleFunctors (OXMod.{u, u} Y)).shiftIso (-i) i 0 (by omega)).app
        (structureModule Y)).symm ≪≫
    ((shiftFunctorAdd _ (-i) n).app
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (structureModule Y))).symm

/-- **The dévissage half of [Stacks, Tag 0B54] with no hypothesis at all.**  For an arbitrary
morphism of ringed spaces `f : X ⟶ Y`, an arbitrary `E` in `D(𝒪_X)` and a strictly perfect
complex `P` of `𝒪_Y`-modules, the derived projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} P ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*P)`

of [Stacks, Tag 0B53] is an isomorphism.

This is
`Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect` with
its hypothesis `hunit` supplied by `isIso_projectionFormulaMap_single_shift`. -/
@[stacks 0B54 "the dévissage from the structure sheaf to a strictly perfect complex, now with \
NO hypothesis: the case K = O_Y[i] shifted by any amount, which \
Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isStrictlyPerfect \
carries as the hypothesis hunit, is discharged here. What is still not covered of the tag is \
the reduction of a PERFECT complex to a strictly perfect one, which is local on the base and \
needs the base-change square of Tag 0B6B along an open immersion composed with a locality \
statement for invertibility of the map; so this is the tag for a strictly perfect complex, not \
for a perfect one"]
theorem isIso_projectionFormulaMap_isStrictlyPerfect
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsIso (projectionFormulaMap f E (DerivedCategory.Q.obj P)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect f E P hP

/-! ### Direct sums -/

/-- **`- ⊗^𝐋_{𝒪_Y} B` is a left adjoint**, namely of `RSheafHom(B, -)`: this is
[Stacks, Tag 08J8] tensoring on the first slot,
`AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction`, read at the ringed site
of the space. -/
theorem isLeftAdjoint_derivedTensorProductFunctor_obj
    (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((derivedTensorProductFunctor Y.sheaf).obj B).IsLeftAdjoint :=
  (AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction
    (Stacks.RingedSpace.toRingedSite Y) B).isLeftAdjoint

/-- **Tensoring with a fixed object commutes with all colimits**, in particular with arbitrary
direct sums. -/
theorem preservesColimitsOfSize_derivedTensorProductFunctor_obj
    (B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    PreservesColimitsOfSize.{v, v} ((derivedTensorProductFunctor Y.sheaf).obj B) :=
  let := isLeftAdjoint_derivedTensorProductFunctor_obj (Y := Y) B
  inferInstance

/-- **The source of the projection-formula morphism commutes with arbitrary direct sums.**  This
is one of the three functors the dévissage of [Stacks, Tag 08EU] over a general `K` needs to
commute with direct sums. -/
theorem preservesColimitsOfSize_projectionFormulaSource
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    PreservesColimitsOfSize.{v, v} (projectionFormulaSource f E) :=
  preservesColimitsOfSize_derivedTensorProductFunctor_obj _

/-- **`Lf^*` commutes with all colimits**: it is the left adjoint in the derived adjunction of
[Stacks, Tag 079W]. -/
theorem preservesColimitsOfSize_derivedPullback :
    PreservesColimitsOfSize.{v, v} (derivedPullback f) :=
  (derivedAdjunction f).leftAdjoint_preservesColimits

/-- **The target of the projection-formula morphism commutes with arbitrary direct sums as soon
as `Rf_*` does.**  Of the three functors it is composed of, `Lf^*` and `- ⊗^𝐋_{𝒪_X} E` are left
adjoints; so the whole of the remaining direct-sum input of the dévissage of [Stacks, Tag 08EU]
is the hypothesis carried here, that the derived pushforward commutes with direct sums. -/
theorem preservesColimitsOfSize_projectionFormulaTarget
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hpush : PreservesColimitsOfSize.{v, v} (derivedPushforward f)) :
    PreservesColimitsOfSize.{v, v} (projectionFormulaTarget f E) := by
  have := hpush
  have := preservesColimitsOfSize_derivedPullback.{v} f
  have := preservesColimitsOfSize_derivedTensorProductFunctor_obj.{v} (Y := X) E
  exact comp_preservesColimits _ _

end Main

end Stacks.Cohomology.ProjectionFormulaShiftedUnit

end

end
