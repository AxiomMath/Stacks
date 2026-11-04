module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChange
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionComposite
public import StacksFrontier.RingTheory.Koszul.BaseCellFiltration

/-! # The base change of the base ring is the target ring

Let `R → R'` be a map of commutative rings. The base change of the differential graded
`R`-algebra `R` — the base ring placed in degree zero with zero differential — along `R → R'` is
`R ⊗_R R'`, and this file identifies it with `R'` placed in degree zero: the inclusion
`r' ↦ 1 ⊗ r'` of `DifferentialGradedAlgebra.tensorIncludeRightHom` and the multiplication
`r ⊗ r' ↦ r r'` are mutually inverse homomorphisms of differential graded algebras.

The module-level counterpart is `DifferentialGraded.unitBaseChangeIso`, which identifies
`(R ⊗_R B)_B` with the regular right differential graded `B`-module. Here both factors are in
degree zero and the statement is about the algebras themselves, so it also gives an equivalence
of derived categories `D(R ⊗_R R', d) ≌ D(R', d)`: restriction of scalars along either of the two
homomorphisms, the two composites being derived restriction along the identity.

## Main definitions

* `DifferentialGradedAlgebra.degreeZeroBaseChangeUnitor`: the homomorphism `R ⊗_R R' → R'`.
* `DifferentialGradedModule.degreeZeroBaseChangeEquivalence`: the induced equivalence
  `D(R ⊗_R R', d) ≌ D(R', d)`.

## Main results

* `DifferentialGradedAlgebra.Hom.ext_toAlgebraHom`: a homomorphism of differential graded algebras
  is determined by its underlying algebra homomorphism.
* `DifferentialGradedAlgebra.degreeZeroBaseChangeUnitor_comp_includeRight` and
  `DifferentialGradedAlgebra.includeRight_comp_degreeZeroBaseChangeUnitor`: **the unitor and the
  inclusion are mutually inverse**, which is the assertion that
  `(degreeZero R R).baseChange R' ≅ degreeZero R R'` as differential graded algebras.

## Implementation notes

The unitor is the lift of the pair of homomorphisms `R → R'` and `R' → R'` through the universal
property `DifferentialGradedAlgebra.tensorLift` of the graded tensor product of Tag 065W. The
first of those is `DifferentialGradedAlgebra.baseHom`, the structure homomorphism of a
differential graded algebra from the base ring in degree zero.

The Koszul anticommutation hypothesis is vacuous here: both factors are concentrated in degree
zero, so a homogeneous element of nonzero degree vanishes and the Koszul sign in degree zero is
`+1`; what remains is the commutativity of `R'`.

A homomorphism of differential graded algebras carries, besides the algebra homomorphism, only
propositions, so `DifferentialGradedAlgebra.Hom.ext_toAlgebraHom` reduces each identity to one of
algebra homomorphisms. On `R ⊗_R R'` these are compared on the two inclusions
(`DifferentialGradedAlgebra.tensorHom_ext`); on the left inclusion both sides are `R`-algebra
homomorphisms out of `R`, of which there is only one (`AlgHom.subsingleton_id`).

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W), the tensor product of
  differential graded algebras and its universal property.
* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), whose part (2) has
  `- ⊗_R^𝐋 R' : D(R) → D(R')` for its bottom edge; in the spelling of this tree that functor
  lands in `D(R ⊗_R R', d)`, and the identification above is what reads it in `D(R', d)`.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars
  and its derived functor.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **A homomorphism of differential graded algebras is determined by its underlying algebra
homomorphism**: the compatibility with the grading and with the differential are propositions. -/
theorem Hom.ext_toAlgebraHom {A B : DifferentialGradedAlgebra.{u, u} R} {f g : A.Hom B}
    (h : f.toAlgebraHom = g.toAlgebraHom) : f = g := by
  cases f
  cases g
  subst h
  rfl

variable (R' : Type u) [CommRing R'] [Algebra R R']

/-- An element of nonzero degree of the degree-zero algebra vanishes. -/
private theorem degreeZero_coe_eq_zero (S : Type u) [CommRing S] [Algebra R S] {i : ℤ} (hi : i ≠ 0)
    (a : degreeZeroGrading R S i) : (a : S) = 0 := by
  obtain ⟨a, h⟩ := a
  rwa [degreeZeroGrading_eq_bot R S hi, Submodule.mem_bot] at h

/-- The structure homomorphism `R → R'` and the identity of `R'` anticommute in the Koszul sense,
vacuously: both algebras are concentrated in degree zero, so a homogeneous element of nonzero
degree vanishes, and in degree zero the sign is `+1` and `R'` is commutative. -/
theorem anticommutesAlong_degreeZeroBaseHom_idHom :
    AnticommutesAlong (degreeZero R R) (degreeZero R R') (degreeZero R R')
      (baseHom (degreeZero R R')) (idHom (degreeZero R R')) := by
  intro i j a b
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi
      subst hj
      rw [mul_zero, zpow_zero, one_smul]
      exact mul_comm _ _
    · simp [degreeZero_coe_eq_zero R' hj b]
  · simp [degreeZero_coe_eq_zero R hi a]

/-- **The unitor `R ⊗_R R' → R'`**, the homomorphism of differential graded algebras sending the
pure tensor `r ⊗ r'` to `r r'`: the lift of the structure homomorphism `R → R'` and of the
identity of `R'` through the universal property of the graded tensor product. -/
def degreeZeroBaseChangeUnitor :
    ((degreeZero R R).baseChange R').Hom (degreeZero R R') :=
  tensorLift (anticommutesAlong_degreeZeroBaseHom_idHom R')

/-- The unitor sends the pure tensor `r ⊗ r'` to `algebraMap R R' r * r'`. -/
@[simp] theorem degreeZeroBaseChangeUnitor_tmul (r : R) (r' : R') :
    (degreeZeroBaseChangeUnitor R').toAlgebraHom
        ((r ᵍ⊗ₜ[R] r' : (degreeZero R R).grading ᵍ⊗[R] (degreeZero R R').grading)) =
      algebraMap R R' r * r' := rfl

/-- **The unitor undoes the inclusion `r' ↦ 1 ⊗ r'`.** -/
theorem degreeZeroBaseChangeUnitor_comp_includeRight :
    (degreeZeroBaseChangeUnitor R').comp
        (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')) =
      idHom (degreeZero R R') :=
  Hom.ext_toAlgebraHom (by
    rw [Hom.comp_toAlgebraHom]
    exact tensorLiftAlgebraHom_comp_includeRight (anticommutesAlong_degreeZeroBaseHom_idHom R'))

/-- **The inclusion `r' ↦ 1 ⊗ r'` undoes the unitor.** -/
theorem includeRight_comp_degreeZeroBaseChangeUnitor :
    (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')).comp
        (degreeZeroBaseChangeUnitor R') =
      idHom ((degreeZero R R).baseChange R') :=
  Hom.ext_toAlgebraHom (tensorHom_ext (Subsingleton.elim _ _) (by
    have h := congrArg Hom.toAlgebraHom
      (degreeZeroBaseChangeUnitor_comp_includeRight (R := R) R')
    rw [Hom.comp_toAlgebraHom] at h
    rw [Hom.comp_toAlgebraHom, AlgHom.comp_assoc]
    erw [h]
    rfl))

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']

/-- **Restriction along the inclusion `R' → R ⊗_R R'` is an equivalence of derived categories**,
`D(R ⊗_R R', d) ≌ D(R', d)`, with restriction along the unitor `R ⊗_R R' → R'` for its
inverse. -/
def degreeZeroBaseChangeEquivalence :
    derivedCategory' ((degreeZero R R).baseChange R') ≌ derivedCategory' (degreeZero R R') :=
  CategoryTheory.Equivalence.mk
    (derivedRestriction (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')))
    (derivedRestriction (degreeZeroBaseChangeUnitor R'))
    ((derivedRestrictionComp (degreeZeroBaseChangeUnitor R')
        (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')) ≪≫
      eqToIso (congrArg derivedRestriction
        (includeRight_comp_degreeZeroBaseChangeUnitor R')) ≪≫
      derivedRestrictionIdIso ((degreeZero R R).baseChange R')).symm)
    (derivedRestrictionComp (tensorIncludeRightHom (degreeZero R R) (degreeZero R R'))
        (degreeZeroBaseChangeUnitor R') ≪≫
      eqToIso (congrArg derivedRestriction
        (degreeZeroBaseChangeUnitor_comp_includeRight R')) ≪≫
      derivedRestrictionIdIso (degreeZero R R'))

/-- The functor of `degreeZeroBaseChangeEquivalence` is derived restriction along the inclusion
`r' ↦ 1 ⊗ r'`. -/
@[simp] theorem degreeZeroBaseChangeEquivalence_functor :
    (degreeZeroBaseChangeEquivalence (R := R) R').functor =
      derivedRestriction (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')) :=
  rfl

end DifferentialGradedModule

end
