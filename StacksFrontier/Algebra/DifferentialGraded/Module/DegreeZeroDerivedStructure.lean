module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.Linear
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated

@[expose] public noncomputable section

/-!
# Structure carried by the degree-zero comparison equivalence

Let `R` be a commutative ring, `S` an `R`-algebra, not necessarily commutative, and `A` an
`R`-algebra identified with the opposite algebra of `S`. The equivalence
`DifferentialGradedModule.degreeZeroDerivedEquivalence` between the derived category of
differential graded modules over `S` placed in degree zero and the derived category of ordinary
`A`-modules is obtained from the uniqueness of localizations, so every property of it has to be
read through the two localization functors it compares. This module records the structure the
equivalence carries: it is additive, and it is `R`-linear.

## Main definitions

* `DifferentialGradedModule.degreeZeroDerivedComponentIso`: the equivalence read through the
  localizations, carrying the class of a differential graded module to the class of its complex
  of homogeneous components.

## Main results

* `DifferentialGradedModule.degreeZeroComponent_isLocalization`: the homogeneous-components
  functor followed by the localization of cochain complexes is a localization of differential
  graded modules in degree zero at the quasi-isomorphisms.
* `DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_additive`: the equivalence is
  additive.
* `DifferentialGradedModule.degreeZeroComponentFunctor_linear` and
  `DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_linear`: the
  homogeneous-components functor and the equivalence are `R`-linear.
* `DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_commShift`: the equivalence
  commutes with the shift.

## Implementation notes

Everything here is stated at an arbitrary chosen derived category of `A`-modules, that is under a
`[HasDerivedCategory.{w} (ModuleCat.{u} A)]` binder, and not only at
`HasDerivedCategory.standard`: the two localization facts the arguments rest on,
`DifferentialGradedModule.degreeZero_localization` and
`DifferentialGradedModule.degreeZeroComponent_isLocalization`, hold at any chosen model, and so
does `DifferentialGradedModule.degreeZeroDerivedEquivalence` itself.

Linearity is read off the localizations by
`CategoryTheory.Localization.functor_linear_iff`, which needs the equivalence to be known as the
lift of `degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q` along the differential graded
localization; `DifferentialGradedModule.degreeZeroDerivedLifting` records that, which is possible
because `degreeZeroDerivedEquivalence` is `CategoryTheory.Localization.uniq` of the two
localization functors and `CategoryTheory.Functor.IsLocalization` is a proposition.

Linearity of the homogeneous-components functor is the identity
`op (algebraMap R S r) • y = r • y` on a differential graded module over `degreeZero R S`: the
base ring acts on a differential graded module through the scalar tower over the opposite of the
algebra, and on a homogeneous component read as an `A`-module through `algebraMap R A` carried
to `Sᵐᵒᵖ` by `DifferentialGradedAlgebra.oppositeEquiv_algebraMap`.

Commutation with the shift is again read off the localizations, by
`CategoryTheory.Functor.commShiftOfLocalization`: the differential graded localization commutes
with the shift because the quotient functor to the homotopy category and the localization at the
quasi-isomorphisms do, and the functor being lifted commutes with the shift because
`DifferentialGradedModule.degreeZeroComponentFunctor_commShift` and `DerivedCategory.Q` do. The
comparison of the two shifts — the grading shift `DifferentialGradedModule.shift`, whose degree
`n` part is the old degree `n + k`, against `CochainComplex.shiftFunctor` — is
`DifferentialGradedModule.degreeZeroComponentShiftNatIso`, in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroShift.lean`.

`CategoryTheory.Functor.IsTriangulated` for the equivalence is *not* treated here. It does not
follow from the commutation with the shift: it needs the comparison of the distinguished
triangles, which are the admissible short exact sequences on the differential graded side and the
mapping cones on the cochain side. That comparison is
`DifferentialGradedModule.degreeZeroHomotopyFunctor_isTriangulated`, and the exactness it yields
for the equivalence is `DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact`, in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroTriangulated.lean`.
-/

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedAlgebra
open scoped ModuleCat.Algebra

universe u w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]

attribute [local instance] degreeZeroOppositeModule degreeZeroComponentModule
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- The base ring acts on a differential graded module through the opposite of the algebra: the
opposite of the image of `r` acts as `r` does. -/
private theorem op_algebraMap_smul (B : DifferentialGradedAlgebra.{u, u} R)
    (N : DifferentialGradedModule B) (s : R) (y : N.M) :
    MulOpposite.op (algebraMap R B.A s) • y = s • y := by
  rw [show MulOpposite.op (algebraMap R B.A s) = algebraMap R B.Aᵐᵒᵖ s from rfl,
    IsScalarTower.algebraMap_smul B.Aᵐᵒᵖ s y]

variable {S : Type u} [Ring S] [Algebra R S] [IsOppositeAlgebra R S A]

/-- **The homogeneous-components functor is `R`-linear.** -/
instance degreeZeroComponentFunctor_linear :
    (degreeZeroComponentFunctor R A).Linear R where
  map_smul {_ N} f r := by
    ext n x
    apply Subtype.ext
    have h : oppositeEquiv R S A (algebraMap R A r) • (f.toFun x.1) = r • f.toFun x.1 := by
      rw [oppositeEquiv_algebraMap]
      exact op_algebraMap_smul (degreeZero R S) N r (f.toFun x.1)
    exact h.symm

section Derived

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **Cochain complexes of `A`-modules are a localization of differential graded modules over
`S` in degree zero.** Taking homogeneous components and then passing to the derived category of
`A`-modules inverts exactly the quasi-isomorphisms.

This is `DifferentialGradedModule.degreeZeroEquivalence` carried along the localization
`DerivedCategory.Q`, by `CategoryTheory.Functor.IsLocalization.of_equivalence_source`. -/
theorem degreeZeroComponent_isLocalization :
    (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R A)) := by
  refine Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) _ _ degreeZeroEquivalence.symm ?_
    (fun _ _ _ hf ↦ Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)) _ hf)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight degreeZeroEquivalence.counitIso DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q)
  intro X Y f hf
  apply MorphismProperty.le_isoClosure
  change HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)
    ((degreeZeroComponentFunctor R A).map (degreeZeroEquivalence.inverse.map f))
  exact ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoMk (degreeZeroEquivalence.counitIso.app X)
      (degreeZeroEquivalence.counitIso.app Y)
      (degreeZeroEquivalence.counitIso.hom.naturality f).symm)).mpr hf

/-- The comparison equivalence is the lift of the second localization functor along the first.
This is how it is built, by `CategoryTheory.Localization.uniq`. -/
instance degreeZeroDerivedLifting :
    Localization.Lifting
      (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
      ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R A))
      (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q)
      (degreeZeroDerivedEquivalence (R := R) (A := A)).functor := by
  have := degreeZero_localization (R := R) (A := A)
  have := degreeZeroComponent_isLocalization (R := R) (A := A)
  exact inferInstanceAs (Localization.Lifting _ _ _
    (Localization.uniq
      (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
      (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q)
      ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
        (degreeZeroComponentFunctor R A))).functor)

/-- **The derived equivalence of an algebra in degree zero, read through the localizations.**
The equivalence `D(degreeZero R S, d) ≌ D(A)` carries the class of a differential graded module
to the class of its complex of homogeneous components. -/
def degreeZeroDerivedComponentIso :
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q) ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := A)).functor ≅
      degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q := by
  have := degreeZero_localization (R := R) (A := A)
  have := degreeZeroComponent_isLocalization (R := R) (A := A)
  exact Localization.compUniqFunctor _ _ _

/-- The equivalence `D(degreeZero R S, d) ≌ D(A)` is additive: both categories are
pre-triangulated, so they have binary products, and an equivalence preserves them. -/
instance degreeZeroDerivedEquivalence_functor_additive :
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The equivalence `D(degreeZero R S, d) ≌ D(A)` is `R`-linear.** It is the lift of the
`R`-linear functor `degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q` along the differential
graded localization, and linearity of a lift is equivalent to linearity of what it lifts. -/
instance degreeZeroDerivedEquivalence_functor_linear :
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.Linear R := by
  have := degreeZero_localization (R := R) (A := A)
  rw [← Localization.functor_linear_iff
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
    ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
      (degreeZeroComponentFunctor R A)) R
    (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q)
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor]
  infer_instance

/-- **The equivalence `D(degreeZero R S, d) ≌ D(A)` commutes with the shift.** It is the lift of
`degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q` along the differential graded localization;
that functor commutes with the shift because both of its factors do, and so does the
localization, so `CategoryTheory.Functor.commShiftOfLocalization` carries the commutation to the
lift. -/
instance degreeZeroDerivedEquivalence_functor_commShift :
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.CommShift ℤ := by
  have := degreeZero_localization (R := R) (S := S) (A := A)
  exact Functor.commShiftOfLocalization
    (toHomotopyCategory (degreeZero R S) ⋙ (quasiIsomorphisms' (degreeZero R S)).Q)
    ((HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).inverseImage
      (degreeZeroComponentFunctor R A)) ℤ
    (degreeZeroComponentFunctor R A ⋙ DerivedCategory.Q)
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor

end Derived

end DifferentialGradedModule

end
