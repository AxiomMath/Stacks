module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExt
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomOrthogonal
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of derived Hom is Ext

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tag 0CS5 asserts, for every `n`, an isomorphism of
`R`-modules

`H^n(RHom(N, M)) = Ext^n_{D(B,d)}(N, M) = Hom_{D(B,d)}(N, M[n])`,

natural in `M`.

Both sides are right derived functors of one and the same functor on the homotopy category
`K(B, d)`, with comparison maps `DifferentialGradedModule.extCohomologyComparisonUnit` and
`DifferentialGradedModule.extComparisonUnit`.

## Main definitions

* `DifferentialGradedModule.extIso`: the isomorphism of functors
  `RHom(N, -) ⋙ H^n ≅ Ext^n_{D(B,d)}(N, -)` on `D(B, d)`.
* `DifferentialGradedModule.extLinearEquiv`: its value at an object, as an `R`-linear
  equivalence, with the universe lift undone.

## Main results

* `DifferentialGradedModule.isRightDerivedFunctor_extComparisonUnit`: `Ext^n_{D(B,d)}(N, -)`,
  with the comparison map of
  `DifferentialGradedModule.extComparisonUnit`, is the right derived functor of degree-`n`
  cohomology of the ordinary internal hom out of `N`.
* `DifferentialGradedModule.extIso_fac`: the isomorphism is compatible with the two comparison
  maps.
* `DifferentialGradedModule.extLinearEquiv_naturality`: the identification is natural in the
  target object of `D(B, d)`.

## Implementation notes

The left-hand side is a right derived functor because a right derived functor obtained from
coresolutions is absolute (`CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions`),
the right-hand side by `CategoryTheory.Functor.isRightDerivedFunctor_of_coresolutions`, and the
identification is `CategoryTheory.Functor.rightDerivedIso`.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5); the derived functor is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), the morphism-module computation is
  [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), the resolutions are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU) and their orthogonality is
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra R)
  (N : DifferentialGradedModule B) (L : BimoduleStructure A B N)

/-! ### Resolutions on the homotopy category -/

/-- Every object of `K(B, d)` admits a quasi-isomorphism into an object orthogonal on the right
to the acyclic modules. This is Tag 09KU followed by Tag 09KS, read on the homotopy category. -/
theorem exists_quasiIso_rightOrthogonal_homotopyCategory (X : HomotopyCategory B) :
    ∃ (I : HomotopyCategory B) (s : X ⟶ I), quasiIsomorphisms' B s ∧
      (acyclic' B).rightOrthogonal I := by
  obtain ⟨I, s, hs, hI⟩ := exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal B
    (exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions B
      (exists_propertyI_resolution B)) X
  refine ⟨I, s, ?_, hI⟩
  rwa [← acyclic_trW_eq_quasiIsomorphisms']

/-- The right orthogonal of the acyclic modules is stable under the shift, the acyclic modules
forming a triangulated subcategory. -/
theorem rightOrthogonal_acyclic_shiftFunctor_obj {I : HomotopyCategory B}
    (hI : (acyclic' B).rightOrthogonal I) (n : ℤ) :
    (acyclic' B).rightOrthogonal (I⟦n⟧) :=
  ObjectProperty.le_shift (acyclic' B).rightOrthogonal n _ hI

/-! ### `Ext^n` is the right derived functor of the cohomology of ordinary internal hom -/

/-- The localization map on morphism modules is invertible at an object into which the
localization functor is bijective on morphisms. -/
theorem isIso_coyonedaLocalizationMap_app (X : HomotopyCategory B)
    (hX : Function.Bijective ((quasiIsomorphisms' B).Q.map :
      ((toHomotopyCategory B).obj N ⟶ X) →
        ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N) ⟶
          (quasiIsomorphisms' B).Q.obj X))) :
    IsIso ((coyonedaLocalizationMap B N).app X) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hX.comp (ULift.moduleEquiv (R := R)
    (M := ((toHomotopyCategory B).obj N ⟶ X))).bijective

/-- The comparison map of Tag 0CS5 on `K(B, d)`, read componentwise. -/
theorem extComparisonUnit_app (n : ℤ) (I : HomotopyCategory B) :
    (extComparisonUnit A B N L n).app I =
      (homShiftCohomologyUliftIso A B N L n).hom.app I ≫
        (coyonedaLocalizationMap B N).app
          ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj I) ≫
        (extFunctorRestrictedIso B N n).inv.app I :=
  rfl

/-- The comparison map of Tag 0CS5 is invertible at an object orthogonal on the right to the
acyclic modules. -/
theorem isIso_extComparisonUnit_app (n : ℤ) {I : HomotopyCategory B}
    (hI : (acyclic' B).rightOrthogonal I) :
    IsIso ((extComparisonUnit A B N L n).app I) := by
  have h : IsIso ((coyonedaLocalizationMap B N).app
      ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj I)) :=
    isIso_coyonedaLocalizationMap_app B N _
      (quasiIsomorphismsQ_map_bijective_of_rightOrthogonal B
        (rightOrthogonal_acyclic_shiftFunctor_obj B hI n) _)
  rw [extComparisonUnit_app]
  infer_instance

/-- `Ext^n_{D(B,d)}(N, -)`, with the comparison map `DifferentialGradedModule.extComparisonUnit`,
is the right derived functor of `H^n(Hom^•_B(N, -))`. -/
theorem isRightDerivedFunctor_extComparisonUnit (n : ℤ) :
    (extFunctor B N n).IsRightDerivedFunctor (extComparisonUnit A B N L n)
      (quasiIsomorphisms' B) :=
  Functor.isRightDerivedFunctor_of_coresolutions (quasiIsomorphisms' B)
    (extComparisonUnit A B N L n) (acyclic' B).rightOrthogonal
    (exists_quasiIso_rightOrthogonal_homotopyCategory B)
    (fun _ hI Y => quasiIsomorphismsQ_map_bijective_of_rightOrthogonal B hI Y)
    (fun _ hI => isIso_extComparisonUnit_app A B N L n hI)

/-! ### Degree-`n` cohomology of derived Hom is the right derived functor of the same functor -/

/-- The comparison map from degree-`n` cohomology of ordinary internal hom out of `N` to
degree-`n` cohomology of derived Hom: the comparison map of Tag 09LI, followed by degree-`n`
cohomology. -/
def extCohomologyComparisonUnit (D : DerivedHomData A B N L) (n : ℤ) :
    homShiftCohomologyFunctor A B N L n ⟶
      (quasiIsomorphisms' B).Q ⋙ (D.functor ⋙ extCohomologyFunctor A n) :=
  Functor.whiskerRight D.comparison (extCohomologyFunctor A n) ≫
    (Functor.associator (quasiIsomorphisms' B).Q D.functor (extCohomologyFunctor A n)).hom

/-- **Degree-`n` cohomology of derived Hom is a right derived functor of degree-`n` cohomology of
ordinary internal hom.** -/
theorem isRightDerivedFunctor_extCohomologyComparisonUnit (D : DerivedHomData A B N L) (n : ℤ) :
    (D.functor ⋙ extCohomologyFunctor A n).IsRightDerivedFunctor
      (extCohomologyComparisonUnit A B N L D n) (quasiIsomorphisms' B) :=
  have := D.isRightDerived
  Functor.isRightDerivedFunctor_comp_of_coresolutions (quasiIsomorphisms' B) D.comparison
    (extCohomologyFunctor A n)
    (exists_coresolution_map_bijective_of_propertyI_resolutions B
      (exists_propertyI_resolution B))

/-! ### Tag 0CS5 -/

/-- Degree-`n` cohomology of derived Hom out of `N` is
`Ext^n_{D(B,d)}(N, -) = Hom_{D(B,d)}(N, (-)[n])`, as functors on `D(B, d)`. -/
@[stacks 0CS5 "the identification of the cohomology of derived Hom with Ext"]
def extIso (D : DerivedHomData A B N L) (n : ℤ) :
    D.functor ⋙ extCohomologyFunctor A n ≅ extFunctor B N n :=
  have := isRightDerivedFunctor_extCohomologyComparisonUnit A B N L D n
  have := isRightDerivedFunctor_extComparisonUnit A B N L n
  Functor.rightDerivedIso (quasiIsomorphisms' B) (extCohomologyComparisonUnit A B N L D n)
    (extComparisonUnit A B N L n)

/-- The identification of Tag 0CS5 is compatible with the two comparison maps from the ordinary
internal hom, which determines it uniquely. -/
theorem extIso_fac (D : DerivedHomData A B N L) (n : ℤ) :
    extCohomologyComparisonUnit A B N L D n ≫
        Functor.whiskerLeft (quasiIsomorphisms' B).Q (extIso A B N L D n).hom =
      extComparisonUnit A B N L n :=
  have := isRightDerivedFunctor_extCohomologyComparisonUnit A B N L D n
  have := isRightDerivedFunctor_extComparisonUnit A B N L n
  Functor.rightDerivedIso_fac (quasiIsomorphisms' B)
    (extCohomologyComparisonUnit A B N L D n) (extComparisonUnit A B N L n)

/-- The identification of Tag 0CS5 is natural in the object of `D(B, d)`, as a square of
morphisms of `R`-modules. -/
theorem extIso_hom_naturality (D : DerivedHomData A B N L) (n : ℤ)
    {M M' : derivedCategory' B} (g : M ⟶ M') :
    (extCohomologyFunctor A n).map (D.functor.map g) ≫ (extIso A B N L D n).hom.app M' =
      (extIso A B N L D n).hom.app M ≫ (extFunctor B N n).map g :=
  (extIso A B N L D n).hom.naturality g

/-- Degree-`n` cohomology of derived Hom out of `N`, evaluated at an object `M` of `D(B, d)`, is
the `Ext`-module `Hom_{D(B,d)}(N, M[n])`, as an `R`-linear equivalence.

The `R`-module structure on the right is the one of
`DifferentialGradedModule.instLinearDerivedCategory`; the universe lift that
`DifferentialGradedModule.extIso` carries is undone by `ULift.moduleEquiv`. -/
def extLinearEquiv (D : DerivedHomData A B N L) (n : ℤ) (M : derivedCategory' B) :
    ((degreeZeroCohomologyOnLocalization' A).obj ((D.functor.obj M)⟦n⟧) : Type u) ≃ₗ[R]
      ((quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N) ⟶ M⟦n⟧) :=
  (ULift.moduleEquiv (R := R)
    (M := ((degreeZeroCohomologyOnLocalization' A).obj ((D.functor.obj M)⟦n⟧) : Type u))).symm.trans
      ((extIso A B N L D n).app M).toLinearEquiv

/-- The identification of Tag 0CS5 at an object is the component of
`DifferentialGradedModule.extIso`, read on the universe lift. -/
theorem extLinearEquiv_apply (D : DerivedHomData A B N L) (n : ℤ) (M : derivedCategory' B)
    (x : (degreeZeroCohomologyOnLocalization' A).obj ((D.functor.obj M)⟦n⟧)) :
    extLinearEquiv A B N L D n M x = (extIso A B N L D n).hom.app M (ULift.up x) :=
  rfl

/-- Degree-`n` cohomology on `D(A, d)` acts on a universe-lifted class by acting on the
class. -/
private theorem extCohomologyFunctor_map_up (n : ℤ) {X Y : derivedCategory' A} (h : X ⟶ Y)
    (x : (degreeZeroCohomologyOnLocalization' A).obj (X⟦n⟧)) :
    (extCohomologyFunctor A n).map h (ULift.up x) =
      ULift.up ((degreeZeroCohomologyOnLocalization' A).map (h⟦n⟧') x) :=
  rfl

/-- `Ext^n_{D(B,d)}(N, -)` acts by postcomposition with the `n`-shift. -/
private theorem extFunctor_map_apply (n : ℤ) {X Y : derivedCategory' B} (g : X ⟶ Y)
    (y : (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N) ⟶ X⟦n⟧) :
    (extFunctor B N n).map g y = y ≫ g⟦n⟧' :=
  rfl

/-- The identification `DifferentialGradedModule.extLinearEquiv` is natural in the target: a
cohomology class of derived Hom pushed forward along `g` is sent to the `Ext`-class followed by
the `n`-shift of `g`. -/
@[stacks 0CS5 "the identification is natural in the target"]
theorem extLinearEquiv_naturality (D : DerivedHomData A B N L) (n : ℤ)
    {M M' : derivedCategory' B} (g : M ⟶ M')
    (x : (degreeZeroCohomologyOnLocalization' A).obj ((D.functor.obj M)⟦n⟧)) :
    extLinearEquiv A B N L D n M'
        ((degreeZeroCohomologyOnLocalization' A).map ((D.functor.map g)⟦n⟧') x) =
      extLinearEquiv A B N L D n M x ≫ g⟦n⟧' :=
  ConcreteCategory.congr_hom (extIso_hom_naturality A B N L D n g) (ULift.up x)

end DifferentialGradedModule

end
