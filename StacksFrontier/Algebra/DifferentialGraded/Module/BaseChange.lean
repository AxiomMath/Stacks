module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorInclusion
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor

/-! # Base change of a differential graded algebra

Let `R → R'` be a map of commutative rings and let `(A, d)` be a differential graded
`R`-algebra. Its base change is the differential graded algebra `A' = A ⊗_R R'`, obtained by
tensoring `A` with `DifferentialGradedAlgebra.degreeZero R R'`, that is with `R'` placed in
degree zero with zero differential, and `a ↦ a ⊗ 1` is a
homomorphism of differential graded algebras `A → A'`. Tensoring with the resulting
`(A, A')`-bimodule is base change of differential graded modules, `M ↦ M ⊗_A A' = M ⊗_R R'`,
and its total left derived functor is `- ⊗_A^𝐋 A' : D(A, d) ⥤ D(A', d)`.

## Main definitions

* `DifferentialGradedAlgebra.baseChange`: the differential graded algebra `A ⊗_R R'`.
* `DifferentialGradedAlgebra.toBaseChange`: the homomorphism `a ↦ a ⊗ 1`.
* `DifferentialGraded.Bimodule.baseChange`: `A'` as a differential graded `(A, A')`-bimodule.
* `DifferentialGraded.Bimodule.derivedBaseChangeFunctor`: the functor `- ⊗_A^𝐋 A'`.

## Main results

* `DifferentialGradedAlgebra.tmul_mem_baseChange_grading` and
  `DifferentialGradedAlgebra.baseChange_d_tmul`: the degree-`n` part of `A ⊗_R R'` contains
  `A^n ⊗_R R'` and its differential is `d_A ⊗ 1`.
* `DifferentialGraded.Bimodule.derivedBaseChangeFunctor_isLeftDerivedFunctor`: the derived
  tensor product with `A'` is the total left derived functor of base change. This is part (1) of
  Tag 0BYZ; parts (2) and (3), and the `A'`-linearity of the canonical map `c_M` of the proof,
  are formalized elsewhere, and the implementation notes say where.

## Implementation notes

*Which algebra `A'` is an algebra over.* The source regards `A' = A ⊗_R R'` as a differential
graded `R'`-algebra. Here it is the differential graded `R`-algebra `A ⊗_R R'`, so that its
grading is by `R`-submodules; since `1 ⊗ R'` is central in `A ⊗_R R'` and lies in degree zero,
a grading of a right `A'`-module by `R`-submodules is automatically by `R'`-submodules, so the
two readings of `D(A', d)` differ only by that encoding.

*Base change of modules, and what of Tag 0BYZ is covered.* The base change `M ⊗_R R'` of a
differential graded `A`-module is realized here as `M ⊗_A A'`, tensoring with the bimodule `A'`.
The canonical map `c_M : M ⊗_R R' → M ⊗_A A'` of the source is the base-change associativity
isomorphism `M ⊗_A (A ⊗_R R') ≅ M ⊗_R R'`. It is constructed over `R'` as
`DifferentialGraded.Bimodule.baseChangeTensorIso` in
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorRestrictRight.lean`, and over `A'` —
the `A'`-linearity the source asserts — as
`DifferentialGraded.Bimodule.baseChangeTensorAlgebraIso` in
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeAbsoluteTensor.lean`, where `M ⊗_R R'`
is built as a differential graded `A ⊗_R R'`-module with `(m ⊗ t) · (a ⊗ s) = (m · a) ⊗ (t s)`;
both files are downstream of this one, so neither construction can be quoted here. What is
covered here is therefore part (1) of Tag 0BYZ with its functor `M ↦ M ⊗_R R'` presented as
`M ↦ M ⊗_A A'`, and with that identification available both over `R'` and over `A'`. Nothing of
Tag 0BYZ is left unformalized.

Parts (2) and (3) ARE formalized. Part (3) is
`DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRepresents.lean`. It rests on the claim
of the source's proof — a differential graded `A`-module with property (P) is K-flat as a complex
of `R`-modules when `A` is — which is
`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration` of
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyPKFlat.lean`, and that in turn on the three
closure properties of `CochainComplex.KFlat` (Tag 06XZ) in
`StacksFrontier/Homology/KFlat/Closure.lean`: `kFlat_shift`, `kFlat_coproduct` and
`kFlat_two_out_of_three_of_degreewiseSplit`. The last is the degreewise-split form, which is what
the source actually cites (Tag 06Y2) rather than `kFlat_two_over_three` (Tag 0BYH), whose demand
that the quotient be termwise flat a direct sum of shifts of a merely K-flat `A` does not meet.

Part (2) is `DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRestrictionSquare.lean`. Its two columns
are restriction of scalars along the structure homomorphism
`DifferentialGradedAlgebra.baseHom` and along `r' ↦ 1 ⊗ r'`, and its bottom edge is
derived base change of the base ring in degree zero read in `D(R', d)` through the algebra-level
unitor `(degreeZero R R).baseChange R' ≅ degreeZero R R'` of
`DifferentialGradedAlgebra.degreeZeroBaseChangeUnitor`, whose derived restriction is the
equivalence `DifferentialGradedModule.degreeZeroBaseChangeEquivalence`. The isomorphism itself is
the uniqueness of a left derived functor: both composites derive the same functor
`M ↦ M ⊗_R R'`, the plain square commutes by the canonical map `c_M`
(`DifferentialGraded.Bimodule.baseChangeStructureTensorTrans`, which over `R'` is an isomorphism
for every `M`), and the left-hand composite's comparison is invertible at property-(P) modules by
the claim above.

The source's K-flatness hypothesis on `A` is consumed in part (3) and in the claim, not in part
(1): `c_M` is an isomorphism for every `M`, so part (1) as stated does not need it.

*One correction to the source's wording.* Part (1) of Tag 0BYZ says that `- ⊗_A^𝐋 A'` is the
total **right** derived functor of base change. That is a slip: base change is a tensor product,
hence left derived, as the existence statement the source itself appeals to
([Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)) has it. What is formalized here is
accordingly `IsLeftDerivedFunctor`.

*Universes.* The bimodule stack of
`StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs` is stated with the base ring,
the algebras and the modules in a single universe, so `R`, `R'` and the algebras here are taken
at `Type u` and `DifferentialGradedAlgebra.{u, u}`.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ); the tensor product of
  differential graded algebras is [Tag 065W](https://stacks.math.columbia.edu/tag/065W), the
  regular bimodule of a homomorphism is [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX),
  and the existence of the derived tensor product is
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS).
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-! ### The base change `A ⊗_R R'` -/

variable (A : DifferentialGradedAlgebra.{u, u} R) (R' : Type u) [CommRing R'] [Algebra R R']

/-- The base change `A' = A ⊗_R R'` of a differential graded `R`-algebra along a ring map
`R → R'`: the tensor product of `A` with `R'` placed in degree zero. -/
abbrev baseChange : DifferentialGradedAlgebra.{u, u} R :=
  A.tensorProduct (degreeZero R R')

/-- A pure tensor `a ⊗ r` with `a` of degree `n` has degree `n` in `A ⊗_R R'`. -/
theorem tmul_mem_baseChange_grading (n : ℤ) (a : A.A) (ha : a ∈ A.grading n) (r : R') :
    (a ᵍ⊗ₜ[R] r : A.grading ᵍ⊗[R] (degreeZero R R').grading) ∈ (A.baseChange R').grading n := by
  simpa using tmul_mem_grading A (degreeZero R R') n 0 a r ha
    ((degreeZeroGrading_zero R R').ge Submodule.mem_top)

/-- The degree-`n` part of `A ⊗_R R'` is `A^n ⊗_R R'`: it is spanned by the pure tensors
`a ⊗ r` with `a` of degree `n`. -/
theorem baseChange_grading (n : ℤ) :
    (A.baseChange R').grading n =
      Submodule.span R {x : A.grading ᵍ⊗[R] (degreeZero R R').grading |
        ∃ (a : A.A) (r : R'), a ∈ A.grading n ∧ x = (a ᵍ⊗ₜ[R] r)} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro x ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hq : q = 0
    · subst hq
      refine Submodule.subset_span ⟨a, b, ?_, rfl⟩
      rw [add_zero] at hpq
      exact hpq ▸ ha
    · have hb0 : b = 0 := by simpa [degreeZeroGrading, hq] using hb
      subst hb0
      have hz : (a ᵍ⊗ₜ[R] (0 : R') : A.grading ᵍ⊗[R] (degreeZero R R').grading) = 0 := by
        simp [GradedTensorProduct.tmul]
      rw [hz]
      exact Submodule.zero_mem _
  · rintro x ⟨a, r, ha, rfl⟩
    exact tmul_mem_baseChange_grading A R' n a ha r

/-- The differential of `A ⊗_R R'` is `d_A ⊗ 1`. -/
theorem baseChange_d_tmul (n : ℤ) (a : A.grading n) (r : R') :
    (A.baseChange R').d ((a : A.A) ᵍ⊗ₜ[R] r : A.grading ᵍ⊗[R] (degreeZero R R').grading) =
      ((A.d a) ᵍ⊗ₜ[R] r : A.grading ᵍ⊗[R] (degreeZero R R').grading) := by
  rw [tensorProductDifferential_tmul A (degreeZero R R') n a r]
  simp

/-- The inclusion `a ↦ a ⊗ 1` of `A` into its base change, as a homomorphism of differential
graded algebras. -/
def toBaseChange : A.Hom (A.baseChange R') := tensorIncludeLeftHom A (degreeZero R R')

/-- The inclusion of `A` into its base change sends `a` to `a ⊗ 1`. -/
theorem toBaseChange_apply (a : A.A) :
    (A.toBaseChange R').toAlgebraHom a =
      (a ᵍ⊗ₜ[R] (1 : R') : A.grading ᵍ⊗[R] (degreeZero R R').grading) := rfl

end DifferentialGradedAlgebra

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The base change `A' = A ⊗_R R'` as a differential graded `(A, A')`-bimodule: `A'` acts on
the right by multiplication and `A` on the left through `a ↦ a ⊗ 1`. Tensoring with it is base
change of differential graded modules, `M ↦ M ⊗_A A' = M ⊗_R R'`. -/
def baseChange : Bimodule A (A.baseChange R') := regular (A.toBaseChange R')

/-- Base change of differential graded modules on homotopy categories,
`K(A, d) ⥤ K(A', d)`, `M ↦ M ⊗_R R'`. -/
abbrev baseChangeHomotopyFunctor :
    HomotopyCategory A ⥤ HomotopyCategory (A.baseChange R') :=
  tensorHomotopyFunctor (baseChange A R')

/-- The derived base change `- ⊗_A^𝐋 A' : D(A, d) ⥤ D(A', d)`. -/
abbrev derivedBaseChangeFunctor :
    derivedCategory' A ⥤ derivedCategory' (A.baseChange R') :=
  derivedTensorFunctor (baseChange A R')

/-- The canonical comparison from the derived to the ordinary base change, the counit of the
Kan extension defining `- ⊗_A^𝐋 A'`. -/
abbrev derivedBaseChangeCounit :
    (quasiIsomorphisms' A).Q ⋙ derivedBaseChangeFunctor A R' ⟶
      tensorFunctorToDerivedCategory (baseChange A R') :=
  derivedTensorFunctorCounit (baseChange A R')

/-- **Stacks 0BYZ, part (1).** The derived tensor product `- ⊗_A^𝐋 A'` with the base change
`A' = A ⊗_R R'` is the total left derived functor of base change
`K(A, d) → K(A', d)`, `M ↦ M ⊗_R R'`, followed by localization.

The functor derived here is `M ↦ M ⊗_A A'`; it is base change `M ↦ M ⊗_R R'` by the canonical map
`c_M` of the source's proof, which is `DifferentialGraded.Bimodule.baseChangeTensorIso` as an
isomorphism of differential graded `R'`-modules and
`DifferentialGraded.Bimodule.baseChangeTensorAlgebraIso` as one of differential graded
`A'`-modules. Part (3) is
`DifferentialGraded.Bimodule.isIso_derivedBaseChangeCounit_app_of_kFlat` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRepresents.lean` and part (2) is
`DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare` of
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeRestrictionSquare.lean`. -/
@[stacks 0BYZ "part (1) only, with the functor being derived presented as M |-> M (x)_A A': the \
identification c_M with the source's M |-> M (x)_R R' is baseChangeTensorIso over R' and \
baseChangeTensorAlgebraIso over A'. Corrected: the source says \"right derived functor\", but \
base change is a tensor product and so is LEFT derived, as Tag 09LS has it. Parts (2) and (3) \
are elsewhere, per the docstrings; nothing of Tag 0BYZ remains uncovered"]
theorem derivedBaseChangeFunctor_isLeftDerivedFunctor :
    (derivedBaseChangeFunctor A R').IsLeftDerivedFunctor
      (derivedBaseChangeCounit A R') (quasiIsomorphisms' A) :=
  derivedTensorFunctor_isLeftDerivedFunctor (baseChange A R')

end DifferentialGraded.Bimodule

end
