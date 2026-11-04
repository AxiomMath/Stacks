module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.HomotopyCategoryShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExtIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology

/-! # The regular module represents cohomology on the derived category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, regarded as a right
differential graded module over itself. For every object `X` of the derived category `D(A, d)`
and every `n` there is an isomorphism of `R`-modules
$$H^n(X) \longrightarrow \Hom_{D(A, d)}(A, X[n]),$$
natural in `X`.

## Main definitions

* `DifferentialGradedAlgebra.idHom`: the identity homomorphism of a differential graded algebra.
* `DifferentialGradedModule.derivedRestrictionIdIso`: derived restriction of scalars along the
  identity is the identity functor of `D(A, d)`.
* `DifferentialGradedModule.cohomologyIsoHomRegular`: degree-`n` cohomology on `D(A, d)`
  is `Hom_{D(A, d)}(A, (-)[n])`, as functors to `R`-modules.
* `DifferentialGradedModule.cohomologyLinearEquivHomRegular`: the same at an object, as an
  `R`-linear equivalence with the universe lift undone.
* `DifferentialGradedModule.regularShiftCompare`: the comparison between the image in `D(A, d)`
  of the shifted regular module and the shift of its image.
* `DifferentialGradedModule.cohomologyEquivDerivedCohomology`: the degree-`k` cohomology of the
  algebra is the degree-`k` cohomology, taken in `D(A, d)`, of the regular module.

## Main results

* `DifferentialGradedModule.cohomologyLinearEquivHomRegular_naturality`: the
  identification is natural in the object of `D(A, d)`; a cohomology class pushed forward along
  `g` is the morphism followed by the `n`-shift of `g`.
* `DifferentialGradedModule.cohomologyLinearEquivHomRegular_cohomologyEquivDerivedCohomology`:
  the identification of the cohomology of the algebra with the cohomology of the regular module
  is the one induced by the canonical map
  `DifferentialGradedModule.cohomologyToDerivedCategory`.
* `DifferentialGradedModule.cohomologyLinearEquivHomRegular_map_cohomologyEquivDerivedCohomology`:
  the map `H^k(A) → H^k(X)` induced by a morphism `g : A ⟶ X` of `D(A, d)` is, through the
  representability isomorphism, postcomposition with `g[k]`.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5) for the cohomology of
  derived Hom, [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) for derived Hom out of the
  regular bimodule, and [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the
  homotopy-category form.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The identity homomorphism of a differential graded algebra. -/
def idHom (A : DifferentialGradedAlgebra R) : A.Hom A where
  toAlgebraHom := AlgHom.id R A.A
  map_grading _ _ ha := ha
  map_d _ := rfl

/-- The underlying algebra homomorphism of `DifferentialGradedAlgebra.idHom A` is the identity. -/
@[simp] theorem idHom_toAlgebraHom (A : DifferentialGradedAlgebra R) :
    (idHom A).toAlgebraHom = AlgHom.id R A.A :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-! ### Restriction of scalars along the identity -/

/-- Restriction of scalars along the identity homomorphism is the identity functor on
differential graded modules: neither the module, nor the grading, nor the differential, nor the
right action is changed. -/
theorem restrictScalarsFunctor_idHom :
    restrictScalarsFunctor A.idHom = Functor.id (DifferentialGradedModule A) :=
  rfl

/-- Restriction of scalars along the identity homomorphism is the identity functor on the
homotopy category. -/
theorem restrictScalarsHomotopyFunctor_idHom :
    restrictScalarsHomotopyFunctor A.idHom = Functor.id (HomotopyCategory A) :=
  (CategoryTheory.Quotient.lift_unique _ _ _ (Functor.id (HomotopyCategory A)) rfl).symm

/-- **Derived restriction of scalars along the identity is the identity functor of `D(A, d)`**,
as a natural isomorphism. -/
def derivedRestrictionIdIso :
    derivedRestriction A.idHom ≅ Functor.id (derivedCategory' A) :=
  Localization.liftNatIso (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
    ((quasiIsomorphisms' A).Q ⋙ derivedRestriction A.idHom)
    ((quasiIsomorphisms' A).Q ⋙ Functor.id (derivedCategory' A))
    (derivedRestriction A.idHom) (Functor.id (derivedCategory' A))
    (derivedRestrictionFactorization A.idHom ≪≫
      eqToIso (by rw [restrictScalarsHomotopyFunctor_idHom, Functor.id_comp, Functor.comp_id]))

/-- Derived Hom out of the regular differential graded `(A, A)`-bimodule of the identity
homomorphism, as a right derived functor given by derived restriction of scalars along the
identity. -/
abbrev regularSelfDerivedHomData :
    DerivedHomData A A (regularModule A) (regularBimoduleStructure A.idHom) :=
  DerivedHomData.regular A.idHom

/-! ### The representability isomorphism -/

/-- Degree-`n` cohomology of the restriction along the identity of an object of `D(A, d)`,
identified with its degree-`n` cohomology. -/
def shiftedRestrictionIdIso (n : ℤ) (X : derivedCategory' A) :
    (degreeZeroCohomologyOnLocalization' A).obj
        (((derivedRestriction A.idHom).obj X)⟦n⟧) ≅
      (degreeZeroCohomologyOnLocalization' A).obj (X⟦n⟧) :=
  (degreeZeroCohomologyOnLocalization' A).mapIso
    ((CategoryTheory.shiftFunctor (derivedCategory' A) n).mapIso
      ((derivedRestrictionIdIso A).app X))

/-- **The regular module represents cohomology.** Degree-`n` cohomology on `D(A, d)` is
`Ext^n_{D(A, d)}(A, -) = Hom_{D(A, d)}(A, (-)[n])`, as functors to `R`-modules. -/
def cohomologyIsoHomRegular (n : ℤ) :
    extCohomologyFunctor A n ≅ extFunctor A (regularModule A) n :=
  (Functor.leftUnitor (extCohomologyFunctor A n)).symm ≪≫
    Functor.isoWhiskerRight (derivedRestrictionIdIso A).symm (extCohomologyFunctor A n) ≪≫
    extIso A A (regularModule A) (regularBimoduleStructure A.idHom)
      (regularSelfDerivedHomData A) n

/-- **The regular module represents cohomology, at an object.** The degree-`n` cohomology of an
object `X` of `D(A, d)` is the module of morphisms `A ⟶ X[n]` of `D(A, d)`, as an `R`-linear
equivalence.

The `R`-module structure on the right is the one of
`DifferentialGradedModule.instLinearDerivedCategory`; the universe lift that
`DifferentialGradedModule.cohomologyIsoHomRegular` carries is undone. -/
def cohomologyLinearEquivHomRegular (n : ℤ) (X : derivedCategory' A) :
    ((degreeZeroCohomologyOnLocalization' A).obj (X⟦n⟧) : Type u) ≃ₗ[R]
      ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)) ⟶ X⟦n⟧) :=
  (shiftedRestrictionIdIso A n X).symm.toLinearEquiv.trans
    (extLinearEquiv A A (regularModule A) (regularBimoduleStructure A.idHom)
      (regularSelfDerivedHomData A) n X)

/-- The square of the comparison isomorphisms of
`DifferentialGradedModule.shiftedRestrictionIdIso` against a morphism of `D(A, d)`. -/
private theorem map_shift_comp_shiftedRestrictionIdIso_hom (n : ℤ)
    {X Y : derivedCategory' A} (g : X ⟶ Y) :
    (degreeZeroCohomologyOnLocalization' A).map
          (((derivedRestriction A.idHom).map g)⟦n⟧') ≫
        (shiftedRestrictionIdIso A n Y).hom =
      (shiftedRestrictionIdIso A n X).hom ≫
        (degreeZeroCohomologyOnLocalization' A).map (g⟦n⟧') := by
  simp only [shiftedRestrictionIdIso, Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp]
  exact congrArg _ (congrArg _ ((derivedRestrictionIdIso A).hom.naturality g))

/-- **The representability isomorphism is natural in the object of `D(A, d)`.** A degree-`n`
cohomology class pushed forward along `g` is sent to the corresponding morphism out of the
regular module followed by the `n`-shift of `g`. -/
theorem cohomologyLinearEquivHomRegular_naturality (n : ℤ)
    {X Y : derivedCategory' A} (g : X ⟶ Y)
    (x : (degreeZeroCohomologyOnLocalization' A).obj (X⟦n⟧)) :
    cohomologyLinearEquivHomRegular A n Y
        ((degreeZeroCohomologyOnLocalization' A).map (g⟦n⟧') x) =
      cohomologyLinearEquivHomRegular A n X x ≫ g⟦n⟧' := by
  have hsq : (degreeZeroCohomologyOnLocalization' A).map (g⟦n⟧') ≫
      (shiftedRestrictionIdIso A n Y).inv =
      (shiftedRestrictionIdIso A n X).inv ≫
        (degreeZeroCohomologyOnLocalization' A).map
          (((derivedRestriction A.idHom).map g)⟦n⟧') := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (map_shift_comp_shiftedRestrictionIdIso_hom A n g).symm
  have hx : (shiftedRestrictionIdIso A n Y).inv
        ((degreeZeroCohomologyOnLocalization' A).map (g⟦n⟧') x) =
      (degreeZeroCohomologyOnLocalization' A).map
        (((derivedRestriction A.idHom).map g)⟦n⟧')
        ((shiftedRestrictionIdIso A n X).inv x) := by
    simpa using ConcreteCategory.congr_hom hsq x
  exact (congrArg (extLinearEquiv A A (regularModule A) (regularBimoduleStructure A.idHom)
    (regularSelfDerivedHomData A) n Y) hx).trans (extLinearEquiv_naturality A A (regularModule A)
      (regularBimoduleStructure A.idHom) (regularSelfDerivedHomData A) n g _)

/-! ### The cohomology of the algebra, read in the derived category -/

/-- The image in `D(A, d)` of the `k`-th shift of the regular module, identified with the `k`-th
shift of its image: the comparison isomorphism of the quotient functor onto the homotopy
category, followed by that of the localization functor. -/
def regularShiftCompare (k : ℤ) :
    (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj ((regularModule A).shift k)) ≅
      ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)))⟦k⟧ :=
  (quasiIsomorphisms' A).Q.mapIso (quotientShiftIso (regularModule A) k) ≪≫
    ((quasiIsomorphisms' A).Q.commShiftIso k).app ((toHomotopyCategory A).obj (regularModule A))

/-- **The degree-`k` cohomology of a differential graded algebra is the degree-`k` cohomology,
taken in `D(A, d)`, of the regular module.** This reads the bijection
`H^k(A) ≃ Hom_{D(A, d)}(A, A[k])` of
`DifferentialGradedModule.cohomologyEquivDerivedHom` through the representability
isomorphism. -/
def cohomologyEquivDerivedCohomology (k : ℤ) :
    A.Cohomology k ≃
      ((degreeZeroCohomologyOnLocalization' A).obj
        (((quasiIsomorphisms' A).Q.obj
          ((toHomotopyCategory A).obj (regularModule A)))⟦k⟧) : Type u) :=
  ((cohomologyEquivDerivedHom A k).trans
      ((Iso.refl _).homCongr (regularShiftCompare A k))).trans
    (cohomologyLinearEquivHomRegular A k
      ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)))).toEquiv.symm

/-- The identification of the cohomology of the algebra with the cohomology of the regular
module is the canonical map `H^k(A) → Hom_{D(A, d)}(A, A[k])`, read through the shift
comparison. -/
theorem cohomologyLinearEquivHomRegular_cohomologyEquivDerivedCohomology (k : ℤ)
    (x : A.Cohomology k) :
    cohomologyLinearEquivHomRegular A k
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)))
        (cohomologyEquivDerivedCohomology A k x) =
      cohomologyToDerivedCategory A k x ≫ (regularShiftCompare A k).hom := by
  have h : cohomologyEquivDerivedCohomology A k x =
      (cohomologyLinearEquivHomRegular A k
          ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)))).symm
        (cohomologyToDerivedCategory A k x ≫ (regularShiftCompare A k).hom) := by
    simp only [cohomologyEquivDerivedCohomology, Equiv.trans_apply,
      LinearEquiv.coe_toEquiv_symm, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      cohomologyEquivDerivedHom_apply]
    rfl
  rw [h, LinearEquiv.apply_symm_apply]

/-- **The map induced on the cohomology of the algebra by a morphism out of the regular
module.** Read through the representability isomorphism, the map
`H^k(A) → H^k(X)` induced by a morphism `g : A ⟶ X` of `D(A, d)` sends a cohomology class to the
morphism it names, followed by `g[k]`. -/
theorem cohomologyLinearEquivHomRegular_map_cohomologyEquivDerivedCohomology (k : ℤ)
    {X : derivedCategory' A}
    (g : (quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (regularModule A)) ⟶ X)
    (x : A.Cohomology k) :
    cohomologyLinearEquivHomRegular A k X
        ((degreeZeroCohomologyOnLocalization' A).map (g⟦k⟧')
          (cohomologyEquivDerivedCohomology A k x)) =
      cohomologyToDerivedCategory A k x ≫ (regularShiftCompare A k).hom ≫ g⟦k⟧' := by
  rw [cohomologyLinearEquivHomRegular_naturality,
    cohomologyLinearEquivHomRegular_cohomologyEquivDerivedCohomology, Category.assoc]

end DifferentialGradedModule

end
