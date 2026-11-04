module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedColimits
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomologyNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology in every degree on the derived category of a differential graded algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. Degree-zero cohomology
of the underlying cochain complex inverts the quasi-isomorphisms, so it descends to the derived
category `D(A, d)`; composing that descent with the `i`-fold shift of `D(A, d)` gives cohomology
in degree `i` as a functor `H^i : D(A, d) ⥤ Mod_R`. This file constructs that family and proves
that each member is a homological functor, which is what makes the long exact cohomology sequence
of a distinguished triangle available in `D(A, d)`.

## Main definitions

* `DifferentialGradedModule.cohomologyFunctor`: the functor `H^i : D(A, d) ⥤ Mod_R`.

## Main results

* `CategoryTheory.Functor.isHomological_shiftFunctor_comp`: the composite of a shift functor of a
  pre-triangulated category with a homological functor is homological.
* `DifferentialGradedModule.degreeZeroCohomologyOnLocalization_isHomological`: degree-zero
  cohomology on `D(A, d)` is a homological functor.
* `DifferentialGradedModule.cohomologyFunctor_isHomological`: `H^i` is a homological functor.
* `DifferentialGradedModule.cohomologyFunctorIso`: on a differential graded module, `H^i` is
  cohomology of the underlying cochain complex in degree `i`.

## Implementation notes

That `shiftFunctor D i ⋙ H` is homological when `H` is does not follow from the composition
instance for homological functors, since the shift functor of a pre-triangulated category carries
no `CategoryTheory.Functor.IsTriangulated` instance: the shift of a distinguished triangle is
distinguished only after its three maps are multiplied by `(-1)^i`. The proof instead reads off
the required exactness from Mathlib's long exact cohomology sequence, whose middle exactness
`CategoryTheory.Functor.homologySequence_exact₂` is stated for the shift sequence of `H`; for the
tautological shift sequence that sequence is the family `shiftFunctor D i ⋙ H`, and the two short
complexes agree.

Two pre-triangulated structures on `K(A, d)` are in scope once the differential graded interface
is imported. The homological functor used here is the one of Tag 09KW on the cone-triangle
structure, `DifferentialGradedModule.instPretriangulatedHomotopyCategory`, which is also the
structure the derived colimit of Tag 0CRL is read in, so that is the structure given priority
throughout.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW), where degree-zero
  cohomology on the homotopy category is shown to be homological;
  [Tag 09KX](https://stacks.math.columbia.edu/tag/09KX) for the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Functor

/-- The composite of the `n`-fold shift of a pre-triangulated category with a homological functor
is a homological functor: the exactness it requires of a distinguished triangle `T` is the middle
exactness of the long exact cohomology sequence of `T` in degree `n`. -/
@[sga "4½ Etat_0 1.3" "partial"]
theorem isHomological_shiftFunctor_comp {D : Type u} [Category.{v} D] [HasZeroObject D]
    [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
    [Pretriangulated D] {A : Type*} [Category* A] [Abelian A] (H : D ⥤ A) [H.IsHomological]
    (n : ℤ) : (CategoryTheory.shiftFunctor D n ⋙ H).IsHomological := by
  let _ : H.ShiftSequence ℤ := ShiftSequence.tautological H ℤ
  have : (CategoryTheory.shiftFunctor D n ⋙ H).PreservesZeroMorphisms := inferInstance
  exact ⟨fun T hT => H.homologySequence_exact₂ T hT n⟩

end CategoryTheory.Functor

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/- Degree-zero cohomology on `K(A, d)` is homological for the cone-triangle structure of
Tag 09KW, and the derived colimit of Tag 0CRL is read in the same structure, so that is the
structure given priority here. -/
attribute [local instance 10000] instPretriangulatedHomotopyCategory

variable (A : DifferentialGradedAlgebra.{u, u} R)

/-- **Tag 09KW for the derived category.** Degree-zero cohomology on `D(A, d)` is a homological
functor: it is the descent along the localization functor of degree-zero cohomology on `K(A, d)`,
which is homological, and the localization functor is triangulated and essentially surjective on
arrows. -/
instance degreeZeroCohomologyOnLocalization_isHomological :
    (degreeZeroCohomologyOnLocalization.{u, u, u} A).IsHomological := by
  have : (quasiIsomorphisms.{u, u, u} A).Q.mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (quasiIsomorphisms.{u, u, u} A).Q (quasiIsomorphisms A)
  have : (degreeZeroCohomologyOnHomotopy.{u, u, u} A).IsHomological :=
    degreeZeroCohomologyLift_isHomological.{u, u, u} A
  exact Functor.isHomological_of_localization (quasiIsomorphisms.{u, u, u} A).Q
    (degreeZeroCohomologyOnLocalization.{u, u, u} A) (degreeZeroCohomologyOnHomotopy.{u, u, u} A)
    (degreeZeroCohomologyOnLocalizationIso.{u, u, u} A)

/-- Cohomology in degree `i` on the derived category `D(A, d)`: the `i`-fold shift followed by
degree-zero cohomology. -/
def cohomologyFunctor (i : ℤ) : derivedCategory.{u, u, u} A ⥤ ModuleCat.{u} R :=
  CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) i ⋙
    degreeZeroCohomologyOnLocalization.{u, u, u} A

/-- Cohomology in degree `i` on `D(A, d)` is a homological functor, so a distinguished triangle of
`D(A, d)` has a long exact cohomology sequence. -/
instance cohomologyFunctor_isHomological (i : ℤ) : (cohomologyFunctor A i).IsHomological :=
  Functor.isHomological_shiftFunctor_comp (degreeZeroCohomologyOnLocalization.{u, u, u} A) i

/-- On a differential graded module, cohomology in degree `i` on `D(A, d)` is cohomology of the
underlying cochain complex in degree `i`. -/
def cohomologyFunctorIso (i : ℤ) :
    toDerivedCategory A ⋙ cohomologyFunctor A i ≅ gradedCohomologyFunctor A i :=
  let Q := toHomotopyCategory.{u, u, u} A
  let L := (quasiIsomorphisms.{u, u, u} A).Q
  let S := CategoryTheory.shiftFunctor (derivedCategory.{u, u, u} A) i
  let T := CategoryTheory.shiftFunctor (HomotopyCategory.{u, u, u} A) i
  let Hl := degreeZeroCohomologyOnLocalization.{u, u, u} A
  Functor.associator Q L (S ⋙ Hl) ≪≫
    Functor.isoWhiskerLeft Q ((Functor.associator L S Hl).symm ≪≫
      Functor.isoWhiskerRight (L.commShiftIso i).symm Hl ≪≫
      Functor.associator T L Hl ≪≫
      Functor.isoWhiskerLeft T (degreeZeroCohomologyOnLocalizationIso.{u, u, u} A)) ≪≫
    homologyShiftFactorsIso A i ≪≫ gradedCohomologyFunctorIso A i

end DifferentialGradedModule

end
