module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.CategoryTheory.Linear.EndomorphismAlgEquiv
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms

/-! # A derived equivalence produces a compact generator with the expected endomorphisms

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and assume
`A = H^0(A)`, that is, that `A` is concentrated in degree zero. [Stacks, Tag 09S8] says that
`D(A, d)` and `D(B, d)` are equivalent as `R`-linear triangulated categories if and only if
`D(B, d)` contains an object `P` which is compact, which weakly generates, and whose graded
endomorphism ring is `A` in degree `0` and vanishes in every other degree; and that the
equivalence built from such a `P` carries `A` to `P`.

This file proves the direction `(1) ⇒ (2)`, with `P` the image `E(A)` of the regular module
under the given equivalence `E : D(A, d) ≌ D(B, d)`.

## Main definitions

* `DifferentialGradedAlgebra.cohomologyZeroEquiv`: for an algebra concentrated in degree zero,
  `H^0(A) ≃ A`.
* `DifferentialGradedModule.cohomologyEquivDerivedShiftHom`: the bijection
  `H^i(A) ≃ Hom_{D(A,d)}(A, A[i])` with the translation taken in the derived category.
* `DifferentialGradedModule.regularMulLeft` and `DifferentialGradedModule.regularEndAlgHom`: left
  multiplication by a degree-zero cocycle as an endomorphism of the regular module, and the
  resulting `R`-algebra homomorphism `A →ₐ[R] End_{D(A,d)}(A)`.
* `DifferentialGradedModule.shiftedHomEquivOfEquivalence`: a shift-commuting equivalence
  identifies `Hom(X, Y[i])` with `Hom(E X, (E Y)[i])`.

## Main results

* `DifferentialGradedAlgebra.grading_zero_eq_top` and
  `DifferentialGradedAlgebra.subsingleton_cohomology`: an algebra concentrated in degree zero is
  its own degree-zero part and has no cohomology away from degree zero.
* `DifferentialGradedModule.regularEndAlgEquiv`: for an algebra concentrated in degree zero, `A`
  *is* the endomorphism `R`-algebra of the regular module in `D(A, d)`.
* `exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence`, in the namespace
  `DifferentialGradedModule`: **Stacks 09S8**, the implication `(1) ⇒ (2)` together with the
  statement that the witness `P` may be taken to be the image `E(A)` of the regular module.

## Implementation notes

*The final clause.* The source asserts that *the equivalence constructed in (2)* sends `A` to
`P`, a statement about the converse direction. The final clause of the theorem below is a
different statement: in the direction `(1) ⇒ (2)` the witness `P` may be taken to be `E(A)`.

*The hypotheses used, against the source's condition (1).* The source's (1) is an equivalence of
`R`-linear triangulated categories. What is assumed below is additivity, `R`-linearity and
commutation with the shift; `Functor.IsTriangulated` is not used, and it implies
`Functor.Additive`. The `R`-linearity is genuinely needed, and only for the degree-zero clause:
without it the endomorphism algebras could be compared only as rings.

*How `A = H^0(A)` is expressed.* The hypothesis is `∀ i ≠ 0, A.grading i = ⊥`: every homogeneous
component outside degree zero vanishes. This gives `A.grading 0 = ⊤`
(`DifferentialGradedAlgebra.grading_zero_eq_top`), hence that the differential is zero, hence that
`H^i(A)` is a singleton for `i ≠ 0` and that `H^0(A) ≃ A`. Vanishing of a `Hom` group is stated as
"every morphism is zero". The clause "equal to `A`" is stated as an isomorphism of `R`-algebras
`A ≃ₐ[R] End P`: the target is `Hom_{D(B,d)}(P, P[0])` with the shift by zero undone, so that it
carries the ring structure given by composition, which is what makes "equal to the algebra `A`"
a statement about algebras rather than about bare types.

*Universes.* `D(A, d)` has objects and morphisms in `Type (u + 1)` while compactness throughout
this chapter is taken with respect to coproducts indexed by `Type u`, so the compactness below is
`IsCompactObject.{u}`, matching Tags 09R9 and 09S7.

## References

* [Stacks Project, Tag 09S8](https://stacks.math.columbia.edu/tag/09S8)
* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY) for morphisms in `D(A, d)`
  out of a resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- A homogeneous element of a vanishing graded piece is zero. -/
theorem coe_eq_zero_of_grading_eq_bot {A : DifferentialGradedAlgebra R} {i : ℤ}
    (hi : A.grading i = ⊥) (a : A.grading i) : (a : A.A) = 0 :=
  (Submodule.eq_bot_iff _).1 hi _ a.2

/-- **An algebra concentrated in degree zero is its own degree-zero part.** If every homogeneous
component of `A` outside degree zero vanishes then `A^0 = A`. -/
theorem grading_zero_eq_top (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) : A.grading 0 = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  have hsum := DirectSum.sum_support_decompose A.grading x
  have hmem : (∑ i ∈ (DirectSum.decompose A.grading x).support,
      ((DirectSum.decompose A.grading x i : A.grading i) : A.A)) ∈ A.grading 0 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h0 : i = 0
    · subst h0
      exact (DirectSum.decompose A.grading x 0).2
    · rw [coe_eq_zero_of_grading_eq_bot (hA i h0) _]
      exact zero_mem _
  rwa [hsum] at hmem

/-- **The differential of an algebra concentrated in degree zero vanishes.** -/
theorem d_eq_zero_of_grading_eq_bot (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.A) : A.d x = 0 := by
  have hx : x ∈ A.grading 0 := by
    rw [A.grading_zero_eq_top hA]
    exact Submodule.mem_top
  exact coe_eq_zero_of_grading_eq_bot (hA (0 + 1) (by decide)) ⟨A.d x, A.d_mem 0 x hx⟩

/-- **An algebra concentrated in degree zero has no cohomology away from degree zero.** -/
theorem subsingleton_cohomology (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (A.Cohomology i) := by
  have hs : Subsingleton (A.Cocycle i) :=
    ⟨fun x y => Subtype.ext (Subtype.ext ((coe_eq_zero_of_grading_eq_bot (hA i hi) x.1).trans
      (coe_eq_zero_of_grading_eq_bot (hA i hi) y.1).symm))⟩
  exact ⟨fun x y => Quotient.inductionOn₂ x y fun a b => congrArg _ (Subsingleton.elim a b)⟩

/-- **`H^0(A) = A` for an algebra concentrated in degree zero**: the class of a degree-zero
cocycle is sent to the cocycle. -/
def cohomologyZeroEquiv (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) : A.Cohomology 0 ≃ A.A where
  toFun := Quotient.lift (fun a : A.Cocycle 0 => (a.1 : A.A)) (by
    intro a b hab
    obtain ⟨c, hc⟩ := hab
    rw [coe_eq_zero_of_grading_eq_bot (hA (0 - 1) (by decide)) c, map_zero] at hc
    exact sub_eq_zero.1 hc)
  invFun x := Quotient.mk _ ⟨⟨x, by rw [A.grading_zero_eq_top hA]; exact Submodule.mem_top⟩,
    A.d_eq_zero_of_grading_eq_bot hA x⟩
  left_inv := Quotient.ind fun _ => congrArg _ (Subtype.ext (Subtype.ext rfl))
  right_inv _ := rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **The cohomology of `A` computes the derived endomorphisms of the regular module**, with the
translation taken in `D(A, d)`: the bijection `H^i(A) ≃ Hom_{D(A,d)}(A, A[i])` of
`DifferentialGradedModule.cohomologyEquivDerivedHom`, read through the comparison
`DifferentialGradedModule.regularShiftCompare` between the image of the shifted regular module and
the shift of its image. -/
def cohomologyEquivDerivedShiftHom (A : DifferentialGradedAlgebra R) (i : ℤ) :
    A.Cohomology i ≃
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A) ⟶
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦i⟧) :=
  (cohomologyEquivDerivedHom A i).trans ((Iso.refl _).homCongr (regularShiftCompare A i))

/-! ### The endomorphism algebra of the regular module in degree zero -/

/-- **Left multiplication by a degree-zero cocycle, as an endomorphism of the regular module.**
This is the homomorphism `A ⟶ A[0]` attached to the cocycle by
`DifferentialGradedModule.regularCocycleHom`, read through the identification `A[0] = A` of
`DifferentialGradedModule.shiftZeroHom`; its underlying linear map is multiplication on the
left. -/
def regularMulLeft (A : DifferentialGradedAlgebra R) (a : A.Cocycle 0) :
    regularModule A ⟶ regularModule A :=
  regularCocycleHom A 0 a ≫ shiftZeroHom A (regularModule A)

/-- Left multiplication by a degree-zero cocycle acts by multiplication. -/
theorem regularMulLeft_toFun_apply (A : DifferentialGradedAlgebra R) (a : A.Cocycle 0) (x : A.A) :
    (regularMulLeft A a).toFun x = (a.1 : A.A) * x := by
  show (shiftZeroHom A (regularModule A)).toFun ((regularCocycleHom A 0 a).toFun x) = _
  rw [regularCocycleHom_toFun]
  rfl

section ConcentratedInDegreeZero

variable (A : DifferentialGradedAlgebra R) (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)

/-- An element of an algebra concentrated in degree zero, as a degree-zero cocycle: it is
homogeneous of degree zero because `A^0 = A`, and closed because the differential vanishes. -/
def degreeZeroCocycle (a : A.A) : A.Cocycle 0 :=
  ⟨⟨a, by rw [A.grading_zero_eq_top hA]; exact Submodule.mem_top⟩,
    A.d_eq_zero_of_grading_eq_bot hA a⟩

/-- **The derived endomorphisms of the regular module, as an `R`-algebra homomorphism out of
`A`.** For an algebra concentrated in degree zero, the homomorphism sending `a` to the class in
`D(A, d)` of left multiplication by `a`. -/
def regularEndAlgHom :
    A.A →ₐ[R] End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) where
  toFun a := End.of ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
    (regularMulLeft A (degreeZeroCocycle A hA a)))
  map_one' := by
    ext1
    dsimp only [End.one_asHom]
    rw [show regularMulLeft A (degreeZeroCocycle A hA 1) = 𝟙 _ from
      Hom.ext (LinearMap.ext fun x => by
        rw [regularMulLeft_toFun_apply]
        exact one_mul x)]
    exact (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map_id _
  map_mul' a b := by
    ext1
    dsimp only [End.mul_asHom]
    rw [show regularMulLeft A (degreeZeroCocycle A hA (a * b)) =
        regularMulLeft A (degreeZeroCocycle A hA b) ≫
          regularMulLeft A (degreeZeroCocycle A hA a) from
      Hom.ext (LinearMap.ext fun x => by
        rw [regularMulLeft_toFun_apply, Hom.comp_toFun_apply, regularMulLeft_toFun_apply,
          regularMulLeft_toFun_apply]
        exact mul_assoc a b x)]
    exact (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map_comp _ _
  map_zero' := by
    ext1
    change _ = (0 : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶ ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))
    rw [show regularMulLeft A (degreeZeroCocycle A hA 0) = 0 from
      Hom.ext (LinearMap.ext fun x => by
        rw [regularMulLeft_toFun_apply]
        change (0 : A.A) * x = (0 : regularModule A ⟶ regularModule A).toFun x
        rw [zero_mul]
        rfl)]
    exact (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map_zero _ _
  map_add' a b := by
    ext1
    change _ = (_ : ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶ ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) + _
    rw [show regularMulLeft A (degreeZeroCocycle A hA (a + b)) =
        regularMulLeft A (degreeZeroCocycle A hA a) +
          regularMulLeft A (degreeZeroCocycle A hA b) from
      Hom.ext (LinearMap.ext fun x => by
        rw [regularMulLeft_toFun_apply, Hom.hom_add_toFun, LinearMap.add_apply,
          regularMulLeft_toFun_apply, regularMulLeft_toFun_apply]
        exact add_mul a b x)]
    exact (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map_add
  commutes' r := by
    have he : regularMulLeft A (degreeZeroCocycle A hA (algebraMap R A.A r)) = r • 𝟙 _ :=
      Hom.ext (LinearMap.ext fun x => by
        rw [regularMulLeft_toFun_apply]
        change algebraMap R A.A r * x = _
        rw [← Algebra.smul_def]
        rfl)
    ext1
    change _ = r • 𝟙 ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))
    rw [he, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- The bijection `A ≃ End_{D(A, d)}(A)` for an algebra concentrated in degree zero: the
identification `H^0(A) ≃ A` of `DifferentialGradedAlgebra.cohomologyZeroEquiv`, the bijection
`H^0(A) ≃ Hom_{D(A,d)}(A, A[0])` of `DifferentialGradedModule.cohomologyEquivDerivedHom`, and the
identification `A[0] = A`. -/
def regularEndEquiv :
    A.A ≃ End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  (((A.cohomologyZeroEquiv hA).symm.trans (cohomologyEquivDerivedHom A 0)).trans
    ((Iso.refl _).homCongr
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).mapIso
        ((shiftZeroIso A).app (regularModule A))))).trans End.homEquiv.symm

/-- The bijection `A ≃ End_{D(A, d)}(A)` is left multiplication. -/
theorem regularEndEquiv_apply (a : A.A) :
    regularEndEquiv A hA a = End.of ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
      (regularMulLeft A (degreeZeroCocycle A hA a))) := by
  simp only [regularEndEquiv, Equiv.trans_apply, regularMulLeft, Functor.map_comp]
  rfl

/-- **`A` is the endomorphism `R`-algebra of the regular module in `D(A, d)`**, for an algebra
concentrated in degree zero: the homomorphism `DifferentialGradedModule.regularEndAlgHom`, which
sends `a` to the class of left multiplication by `a`, is an isomorphism of `R`-algebras. -/
@[sga "5 IIIB 5.7" "partial"]
def regularEndAlgEquiv :
    A.A ≃ₐ[R] End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  AlgEquiv.ofBijective (regularEndAlgHom A hA)
    ((funext fun a => (regularEndEquiv_apply A hA a).symm :
      (regularEndAlgHom A hA : A.A → _) = regularEndEquiv A hA) ▸
      (regularEndEquiv A hA).bijective)

end ConcentratedInDegreeZero

variable {A B : DifferentialGradedAlgebra R}

/-- **A shift-commuting equivalence identifies the groups `Hom(X, Y[i])`**, with
`Hom(E X, (E Y)[i])`. -/
def shiftedHomEquivOfEquivalence (E : derivedCategory' A ≌ derivedCategory' B)
    [E.functor.CommShift ℤ] (X Y : derivedCategory' A) (i : ℤ) :
    (X ⟶ Y⟦i⟧) ≃ (E.functor.obj X ⟶ (E.functor.obj Y)⟦i⟧) :=
  E.fullyFaithfulFunctor.homEquiv.trans
    ((Iso.refl _).homCongr ((E.functor.commShiftIso i).app Y))

/-- **The derived endomorphisms of the image of the regular module compute the cohomology of
`A`.** For a shift-commuting equivalence `E : D(A, d) ≌ D(B, d)` and `P = E(A)` the group
`Hom_{D(B,d)}(P, P[i])` is `H^i(A)`. -/
def cohomologyEquivShiftHomFunctorObjRegularModule
    (E : derivedCategory' A ≌ derivedCategory' B) [E.functor.CommShift ℤ] (i : ℤ) :
    A.Cohomology i ≃
      (E.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ⟶
        (E.functor.obj
          ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)))⟦i⟧) :=
  (cohomologyEquivDerivedShiftHom A i).trans (shiftedHomEquivOfEquivalence E _ _ i)

/-- Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, and
assume `A = H^0(A)`, i.e. that every homogeneous component of `A` outside degree zero vanishes. Let
`E : D(A, d) ≌ D(B, d)` be an `R`-linear, additive, shift-commuting equivalence. Then there is an
object `P` of `D(B, d)` such that

* `P` is a compact object of `D(B, d)`;
* an object `N` of `D(B, d)` with `Hom_{D(B,d)}(P, N[i]) = 0` for every `i : ℤ` is zero;
* `Hom_{D(B,d)}(P, P[i]) = 0` for `i ≠ 0`, and the endomorphism `R`-algebra of `P` is `A`;

and `E` sends the regular module `A` to `P`. Indeed `P` is the image of the regular module.

The degree-zero half of the third clause is an isomorphism of `R`-algebras `A ≃ₐ[R] End P`, which
is what the source's "equal to `A`" says: `End P` is `Hom_{D(B,d)}(P, P[0])` with the shift by
zero undone, and its ring structure is composition.

The source's condition (1) is an equivalence of `R`-linear triangulated categories. What is
assumed here is less: `Functor.IsTriangulated` is not used, only `Functor.Additive`, which it
implies, together with `Functor.CommShift ℤ` and the `R`-linearity that "`R`-linear" provides.
The final clause is the statement that the witness `P` may be taken to be `E(A)`, not the source's
final clause about the equivalence constructed from (2). -/
@[stacks 09S8 "(1) ⇒ (2), including the degree-zero clause as an R-algebra isomorphism \
A ≃ₐ[R] End P, with P the image of the regular module under the given equivalence; NOT (2) ⇒ (1) \
and NOT the source's final clause about the equivalence constructed from (2) — those are \
exists_derivedEquivalence_of_isCompactObject_and_isWeakGenerator and the iff \
derivedEquivalence_iff_exists_isCompactObject_and_isWeakGenerator, in the Converse file"]
theorem exists_isCompactObject_and_isWeakGenerator_of_derivedEquivalence
    (A B : DifferentialGradedAlgebra R) (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥)
    (E : derivedCategory' A ≌ derivedCategory' B) [E.functor.Additive]
    [E.functor.Linear R] [E.functor.CommShift ℤ] :
    ∃ P : derivedCategory' B,
      IsCompactObject.{u} P ∧
      (∀ N : derivedCategory' B, (∀ (i : ℤ) (f : P ⟶ N⟦i⟧), f = 0) → IsZero N) ∧
      (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
      Nonempty (A.A ≃ₐ[R] End P) ∧
      Nonempty (E.functor.obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅ P) := by
  refine ⟨E.functor.obj ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj
    (regularModule A)), ?_, ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · exact (isCompactObject_iff_isCompactObject_obj E.functor _).1 inferInstance
  · exact (ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1
      (isWeakTriangulatedGenerator_obj_of_equivalence E _
        (isWeakTriangulatedGenerator_q_regularModule A))
  · intro i hi f
    exact (cohomologyEquivShiftHomFunctorObjRegularModule E i).symm.injective
      (@Subsingleton.elim _ (A.subsingleton_cohomology hA hi) _ _)
  · exact ⟨(regularEndAlgEquiv A hA).trans
      (E.fullyFaithfulFunctor.algEquivEndOfFullyFaithful (R := R) _)⟩

end DifferentialGradedModule

end
