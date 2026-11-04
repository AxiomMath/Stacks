module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolution

/-!
# The resolving bimodule of a differential graded resolution is compact

In Situation 0BZB — a differential graded `R`-algebra `(E, d)` together with a
quasi-isomorphism to a commutative `R`-algebra `A` placed in degree zero — the complex `E^•`
of `R`-modules underlying `E` is quasi-isomorphic to `A`. So if `A` is a perfect `R`-module,
then `E^•` is a perfect object of `D(R)`, hence a compact one by Tag 07LT. This is hypothesis
(1) of Tag 0BZD for the resolving bimodule, `Dualizing.IsCompactBimodule`.

The derived category of `R` that Tag 0BZD works in is the derived category of `R` viewed as a
differential graded algebra concentrated in degree zero; the identification with the derived
category of `R`-modules is `DifferentialGradedModule.degreeZeroDerivedEquivalence`, and
compactness is transported along it.

## Main definitions

* `DifferentialGradedModule.degreeZeroComponentForgetIso`: over the base ring itself, the
  complex of homogeneous components of a differential graded module is its underlying complex
  of `R`-modules.
* `DifferentialGradedModule.degreeZeroRegularSingleIso`: the complex of `R`-modules underlying
  the regular module of `A` placed in degree zero is `A` placed in degree zero.
* `Dualizing.DGAResolution.regularRestrictIso`: in `D(E, d)` the class of the regular
  `E`-module is the class of `A`, read over `E`.
* `Dualizing.DGAResolution.resolvingSingleIso`: consequently the class of `E^•` in `D(R)` is
  the class of `A`.

## Main results

* `Dualizing.DGAResolution.isCompactBimodule_resolvingBimodule`: **hypothesis (1) of Tag 0BZD
  for the resolving bimodule**, from perfectness of `A` as an `R`-module.

The comparison `DifferentialGradedModule.degreeZeroDerivedComponentIso` through which the
transport runs, and the additivity of the equivalence that makes the transport possible, are
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroDerivedStructure.lean`, where they are
stated at an arbitrary chosen derived category of `A`-modules rather than only at the standard
one.

## Implementation notes

*Why the class of `E^•` is the class of `A`.* The quasi-isomorphism `E → A` makes extension of
scalars an equivalence `D(E, d) ≌ D(A)` (Tag 09S6); its quasi-inverse is restriction of
scalars, and the regular `E`-module goes to the regular `A`-module under the first and comes
back as `A` read over `E`. Forgetting the `E`-action then gives the comparison in `D(R)`
directly, with no use of the second diagram of Situation 0BZB.

*The two readings of the underlying complex.* A differential graded module over `R` placed in
degree zero has two `R`-module structures on each homogeneous component: the right action of
the algebra and the base-ring action recorded in the scalar tower. They agree, and
`DifferentialGradedModule.degreeZeroComponentForgetIso` is the resulting identification of the
two complexes; it is the case `A = R` of
`DifferentialGradedModule.degreeZeroForgetIso`, where restriction of scalars along the
identity no longer intervenes.

## References

* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation.
* [Stacks Project, Tag 0BZD](https://stacks.math.columbia.edu/tag/0BZD), whose hypothesis (1)
  this discharges, and [Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE), where the
  discharge is carried out in prose.
* [Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT), that a perfect object
  of `D(R)` is a compact one.
* [Stacks Project, Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), the equivalence
  attached to a quasi-isomorphism of differential graded algebras.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

section Forget

variable {R : Type u} [CommRing R]

/-- The two `R`-module structures on a homogeneous component of a differential graded module
over `R` placed in degree zero — the right action of the algebra and the base-ring action —
agree. -/
def degreeZeroComponentForgetLinearEquiv (M : DifferentialGradedModule (degreeZero R R))
    (n : ℤ) :
    ((degreeZeroComponentFunctor R R).obj M).X n ≃ₗ[R]
      ((forgetToCochainComplex (degreeZero R R)).obj M).X n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := Subtype.ext (by
    have key : ∀ (B : DifferentialGradedAlgebra.{u, u} R) (N : DifferentialGradedModule B)
        (s : R) (y : N.M), MulOpposite.op (algebraMap R B.A s) • y = s • y := by
      intro B N s y
      rw [show MulOpposite.op (algebraMap R B.A s) = algebraMap R B.Aᵐᵒᵖ s from rfl,
        IsScalarTower.algebraMap_smul B.Aᵐᵒᵖ s y]
    exact key (degreeZero R R) M r x.1)

/-- **Over the base ring the two underlying complexes agree.** The complex of homogeneous
components of a differential graded module over `R` placed in degree zero is its underlying
complex of `R`-modules. -/
def degreeZeroComponentForgetIso (M : DifferentialGradedModule (degreeZero R R)) :
    (degreeZeroComponentFunctor R R).obj M ≅ (forgetToCochainComplex (degreeZero R R)).obj M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (degreeZeroComponentForgetLinearEquiv M n).toModuleIso)
    (by
      intro i j hij
      obtain rfl : j = i + 1 := hij.symm
      simp only [degreeZeroComponentFunctor, degreeZeroComplex, forgetToCochainComplex,
        toCochainComplex, CochainComplex.of_d]
      rfl)

/-- The forgetful functor on derived categories, read through the localization: the class of a
differential graded module goes to the class of its underlying complex of `R`-modules. -/
def derivedForgetCompIso (B : DifferentialGradedAlgebra.{u, u} R) :
    (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q) ⋙ derivedForget B ≅
      forgetToCochainComplex B ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toHomotopyCategory B) (derivedForgetFactorization B) ≪≫
    forgetHomotopyToDerivedCategoryIso B

end Forget

section Single

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The degree-`n` homogeneous component of `A` placed in degree zero, read over `R`: it is `A`
for `n = 0` and zero otherwise, which is the degree-`n` term of `A` placed in degree zero as a
complex of `R`-modules. -/
def degreeZeroGradingSingleIso (n : ℤ) :
    ((forgetToCochainComplex (degreeZero R A)).obj (regularModule (degreeZero R A))).X n ≅
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A)).X n := by
  by_cases hn : n = 0
  · subst hn
    exact ((LinearEquiv.ofEq _ _ (degreeZeroGrading_zero R A)).trans
      Submodule.topEquiv).toModuleIso ≪≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R A)).symm
  · have hs : Subsingleton (degreeZeroGrading R A n) := by
      rw [degreeZeroGrading_eq_bot R A hn]
      infer_instance
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (degreeZeroGrading R A n))).iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of R A) n hn)

/-- **The complex of `R`-modules underlying `A` in degree zero is `A` in degree zero.** Both
complexes have zero differential, so only the terms have to be matched. -/
def degreeZeroRegularSingleIso :
    (forgetToCochainComplex (degreeZero R A)).obj (regularModule (degreeZero R A)) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A) :=
  HomologicalComplex.Hom.isoOfComponents (degreeZeroGradingSingleIso R A) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    have hd : ((forgetToCochainComplex (degreeZero R A)).obj
        (regularModule (degreeZero R A))).d i (i + 1) = 0 := by
      change (regularModule (degreeZero R A)).toCochainComplex.d i (i + 1) = 0
      rw [toCochainComplex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subtype.ext rfl)
    rw [hd]
    simp)

end Single

end DifferentialGradedModule

namespace Dualizing.DGAResolution

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable (S : Dualizing.DGAResolution R A)

/-- **In `D(E, d)` the regular `E`-module is `A`.** Extension of scalars along the
quasi-isomorphism `E → A` is an equivalence carrying the regular `E`-module to the regular
`A`-module, and its quasi-inverse is restriction of scalars, which carries the latter back to
`A` read as a differential graded `E`-module. -/
def regularRestrictIso :
    (toHomotopyCategory S.E ⋙ (quasiIsomorphisms' S.E).Q).obj (regularModule S.E) ≅
      (toHomotopyCategory S.E ⋙ (quasiIsomorphisms' S.E).Q).obj
        (restrictScalars S.toTarget (regularModule (degreeZero R A))) :=
  (Bimodule.derivedExtensionEquivalence S.toTarget S.quasiIso).unitIso.app _ ≪≫
    (derivedRestriction S.toTarget).mapIso
      (Bimodule.derivedTensorRegularIso (Bimodule.regular S.toTarget)) ≪≫
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toHomotopyCategory (degreeZero R A))
        (derivedRestrictionFactorization S.toTarget) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso S.toTarget) _ ≪≫
      Functor.associator _ _ _).app (regularModule (degreeZero R A))

/-- **In `D(R)` the complex `E^•` is `A`.** The class of the right module underlying the
resolving bimodule, carried to the derived category of `R`-modules, is the class of `A` placed
in degree zero. -/
def resolvingSingleIso :
    (degreeZeroDerivedEquivalence (R := R) (A := R)).functor.obj
        ((toHomotopyCategory (Dualizing.baseAlgebra R) ⋙
          (quasiIsomorphisms' (Dualizing.baseAlgebra R)).Q).obj
            (Dualizing.resolvingBimodule S.E).rightModule) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R A) :=
  degreeZeroDerivedComponentIso.app (Dualizing.resolvingBimodule S.E).rightModule ≪≫
    DerivedCategory.Q.mapIso
      (degreeZeroComponentForgetIso (Dualizing.resolvingBimodule S.E).rightModule) ≪≫
    ((derivedForgetCompIso S.E).app (regularModule S.E)).symm ≪≫
    (derivedForget S.E).mapIso S.regularRestrictIso ≪≫
    (derivedForgetCompIso S.E).app (restrictScalars S.toTarget (regularModule (degreeZero R A))) ≪≫
    DerivedCategory.Q.mapIso (degreeZeroRegularSingleIso R A)

/-- **Hypothesis (1) of Tag 0BZD for the resolving bimodule.** In Situation 0BZB, if `A` is a
perfect `R`-module then the complex `E^•` of `R`-modules underlying `E` is a compact object of
`D(R)`.

The quasi-isomorphism `E → A` identifies `E^•` with `A` in `D(R)`
(`Dualizing.DGAResolution.resolvingSingleIso`), perfectness is invariant under isomorphism, and
a perfect object of `D(R)` is a compact one by Tag 07LT. -/
theorem isCompactBimodule_resolvingBimodule
    (hperf : StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) A) :
    Dualizing.IsCompactBimodule (Dualizing.resolvingBimodule S.E) := by
  rw [Dualizing.IsCompactBimodule,
    CategoryTheory.isCompactObject_iff_isCompactObject_obj
      (degreeZeroDerivedEquivalence (R := R) (A := R)).functor]
  exact CategoryTheory.isCompactObject_of_iso S.resolvingSingleIso
    ((StacksDraft.Perfect.isPerfect_iff_isCompactObject _).1 hperf)

end Dualizing.DGAResolution

end
