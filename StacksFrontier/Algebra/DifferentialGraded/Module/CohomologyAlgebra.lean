module

public import StacksFrontier.Algebra.DifferentialGraded.CohomologyRing
public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyEndomorphism
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceCompactGenerator
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceQuasiIso

/-! # The degree-zero cohomology as an algebra: comparisons upgraded from bijections to algebra
maps

The instances `DifferentialGradedAlgebra.instAlgebraCocycleZero` and
`DifferentialGradedAlgebra.instAlgebraCohomologyZero` make `Z^0(A)` and `H^0(A)` into
`R`-algebras for a differential graded algebra `(A, d)` over a commutative ring `R`. This file
upgrades the comparison maps of the chapter, which were bijections of bare types, to
homomorphisms and isomorphisms of `R`-algebras:

* the map `H^0(φ)` induced by a homomorphism of differential graded algebras;
* `H^0(A) ≃ A` for an algebra concentrated in degree zero
  (`DifferentialGradedAlgebra.cohomologyZeroEquiv`);
* `H^0(A) ≃ Hom_{D(A, d)}(A, A)` for the regular module
  (`DifferentialGradedModule.cohomologyEquivDerivedHom` in degree `0`);
* the action of a degree-zero cocycle on a differential graded bimodule, which is multiplicative
  and unital in the cocycle.

The chain these assemble into is the one the proof of [Stacks, Tag 09SA] runs along: for `P` a
compact generator of `D(B, d)` with a property-(P) resolution `Q` and `E = End(Q)`,
`Z^0(E) ↠ H^0(E) ≅ Hom_{D(B,d)}(Q, Q) ≅ Hom_{D(A,d)}(A, A) ≅ H^0(A) = A`, and that chain is of no
use unless every step is a map of algebras.

## Main definitions

* `DifferentialGradedAlgebra.gradingZeroAlgEquivCocycleZero`: for an algebra with nothing in
  positive degrees, `A^0 = Z^0(A)` as `R`-algebras.
* `DifferentialGradedAlgebra.Hom.cocycleZeroAlgHom` and
  `DifferentialGradedAlgebra.Hom.cohomologyZeroAlgHom`: the maps `Z^0(A) → Z^0(B)` and
  `H^0(A) → H^0(B)` induced by a homomorphism of differential graded algebras, as homomorphisms of
  `R`-algebras.
* `DifferentialGradedAlgebra.cohomologyZeroAlgEquiv`: **`H^0(A) ≃ₐ[R] A` for an algebra
  concentrated in degree zero**, the algebra upgrade of
  `DifferentialGradedAlgebra.cohomologyZeroEquiv`.
* `DifferentialGradedModule.cohomologyZeroRegularEndAlgEquiv`: **`H^0(A) ≃ₐ[R] End_{D(A,d)}(A)`**
  for an arbitrary differential graded algebra, the algebra upgrade of
  `DifferentialGradedModule.cohomologyEquivDerivedHom` in degree `0`.
* `DifferentialGraded.Bimodule.cohomologyZeroBimoduleEnd` and
  `DifferentialGraded.Bimodule.cohomologyZeroBimoduleEndAlgHom`: **the action of `H^0(A)` on a
  differential graded `(A, B)`-bimodule `N`, as a homomorphism of `R`-algebras
  `H^0(A) →ₐ[R] End_{D(B,d)}(N)`** — the degree-zero comparison of
  `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` with the shift by zero undone.
* `DifferentialGraded.Bimodule.cocycleActionZero`: the action of a degree-zero cocycle of `A` on a
  differential graded `(A, B)`-bimodule, as an endomorphism of the underlying right
  `B`-module (the shift by zero undone).

## Main results

* `DifferentialGradedAlgebra.cocycleOne_eq_one` and
  `DifferentialGradedAlgebra.cocycleMul_eq_mul`: in degree zero the ring operations of
  `DifferentialGradedAlgebra.instRingCocycleZero` *are* the degree-general cocycle unit and
  product `DifferentialGradedAlgebra.cocycleOne` and `DifferentialGradedAlgebra.cocycleMul`.
* `DifferentialGraded.Bimodule.leftMultiplication_cocycleMul` and
  `DifferentialGraded.Bimodule.leftMultiplication_cocycleOne`: left multiplication on a bimodule
  by a product of degree-zero cocycles is the composite of the two left multiplications, and the
  unit acts as the identity.
* `DifferentialGraded.Bimodule.cocycleActionZero_mul`,
  `DifferentialGraded.Bimodule.cocycleActionZero_one` and their additive siblings: consequently
  the action of a degree-zero cocycle is functorial — a product acts by the composite, the unit by
  the identity — and additive and `R`-linear in the cocycle.
* `DifferentialGraded.Bimodule.bijective_cohomologyZeroBimoduleEnd_iff`: the map
  `H^0(A) → End_{D(B,d)}(N)` is bijective exactly when the degree-zero comparison
  `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is, the two differing by the
  identification `N[0] = N`.
* `DifferentialGradedModule.regularMulLeft_mul`, `DifferentialGradedModule.regularMulLeft_one`
  and their siblings: left multiplication on the regular module is a unital, multiplicative,
  `R`-linear function of the degree-zero cocycle.
* `DifferentialGradedModule.regularEndAlgEquiv_cohomologyZeroAlgEquiv`: the isomorphism
  `H^0(A) ≃ₐ[R] End_{D(A,d)}(A)` specialises to `DifferentialGradedModule.regularEndAlgEquiv`
  when `A` is concentrated in degree zero. So there is only one identification of `A` with the
  endomorphism algebra: `DifferentialGradedModule.regularEndAlgEquiv` is this one, read through
  `DifferentialGradedAlgebra.cohomologyZeroAlgEquiv`.

## Implementation notes

*What is reused.* No comparison map is redefined. Each algebra homomorphism below takes as its
underlying function the existing bijection — `DifferentialGradedAlgebra`
`.cohomologyZeroEquiv`, `DifferentialGradedModule.cohomologyEquivDerivedHom`,
`DifferentialGradedAlgebra.Hom.cohomologyMap` — and proves the algebra laws for it; the
isomorphisms are `AlgEquiv.ofBijective` applied to the bijectivity already available. In
particular `DifferentialGradedModule.cohomologyZeroEquivRegularEnd` is the second half of
`DifferentialGradedModule.regularEndEquiv`, which is why the two agree.

*The generality of the endomorphism-algebra isomorphism.* `DifferentialGradedModule`
`.cohomologyZeroRegularEndAlgEquiv` holds for every differential graded algebra: the hypothesis
`A = H^0(A)` of [Stacks, Tag 09S8] enters only in identifying the left-hand side with `A` itself,
which is `DifferentialGradedAlgebra.cohomologyZeroAlgEquiv`.

*The bimodule comparison in degree zero.* The upgrade for the comparison
`H^0(A) → Hom_{D(B,d)}(N, N[0])` attached to a general differential graded `(A, B)`-bimodule `N` —
the one [Stacks, Tag 09SA] needs for the tautological bimodule of `End(Q)` — is
`DifferentialGraded.Bimodule.cohomologyZeroBimoduleEndAlgHom`. Its four non-multiplicative algebra
laws rest on left multiplication being additive and `R`-linear in the acting element, which is
`DifferentialGraded.Bimodule.leftMultiplication_zero` and `.leftMultiplication_sub` together
with `.leftMultiplication_add` and `.leftMultiplication_smul` below; the multiplicative and unital
halves are `DifferentialGraded.Bimodule.cocycleActionZero_mul` and `.cocycleActionZero_one`.

*Why the algebra map is needed and not just the bijection.* The degree-zero map of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is a bijection of bare types, and
the proof of [Stacks, Tag 09SA] feeds it to
`DifferentialGradedAlgebra.exists_hom_of_degreeZero`, which asks for a *unital multiplicative*
`R`-linear map. So the algebra structure, not merely the bijection, is what that proof consumes.

## References

* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), whose proof runs along
  the chain of algebra maps assembled here.
* [Stacks Project, Tag 09S8](https://stacks.math.columbia.edu/tag/09S8) for the clause
  "`Hom_{D(B,d)}(P, P[0])` is equal to `A`", and
  [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY) for the identification of `H^k(A)` with
  the derived endomorphisms of the regular module.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-! ### The degree-general cocycle unit and product, in degree zero -/

/-- The unit of the ring `Z^0(A)` is the unit cocycle `DifferentialGradedAlgebra.cocycleOne`. -/
theorem cocycleOne_eq_one (A : DifferentialGradedAlgebra R) : A.cocycleOne = 1 := rfl

/-- The product of the ring `Z^0(A)` is the degree-general cocycle product
`DifferentialGradedAlgebra.cocycleMul` in degree zero. So the ring structure introduces no second
notion of product. -/
theorem cocycleMul_eq_mul (a b : A.Cocycle 0) : cocycleMul a b = a * b := rfl

/-- **For an algebra with nothing in positive degrees, `A^0 = Z^0(A)` as `R`-algebras.** The
differential of a degree-zero element is homogeneous of degree one, hence zero, so every
degree-zero element is a cocycle.

This is the shape in which the degree-zero part of a degree-`≤ 0` algebra — the truncation `E'` of
the proof of [Stacks, Tag 09SA] — is a ring: the input `A^0 → B` of
`DifferentialGradedAlgebra.exists_hom_of_degreeZero` may be given as a map out of `Z^0(A)`, where
the projection to `H^0(A)` is available. -/
def gradingZeroAlgEquivCocycleZero (A : DifferentialGradedAlgebra R)
    (hA : ∀ n : ℤ, 0 < n → A.grading n = ⊥) : ↥(A.grading 0) ≃ₐ[R] A.Cocycle 0 where
  toFun a := ⟨a, (Submodule.mem_bot R).mp
    (hA 1 (by norm_num) ▸ A.d_mem 0 (a : A.A) a.property)⟩
  invFun a := a.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The identification `A^0 = Z^0(A)` is the identity on underlying elements. -/
@[simp] theorem gradingZeroAlgEquivCocycleZero_apply (A : DifferentialGradedAlgebra R)
    (hA : ∀ n : ℤ, 0 < n → A.grading n = ⊥) (a : A.grading 0) :
    ((A.gradingZeroAlgEquivCocycleZero hA a).1 : A.grading 0) = a :=
  rfl

/-! ### The map induced by a homomorphism of differential graded algebras -/

/-- **The map `Z^0(A) → Z^0(B)` induced by a homomorphism of differential graded algebras, as a
homomorphism of `R`-algebras.** Its underlying function is
`DifferentialGradedAlgebra.Hom.cocycleMap` in degree zero; multiplicativity and unitality are
`DifferentialGradedAlgebra.Hom.cocycleMap_cocycleMul` and `.cocycleMap_cocycleOne`. -/
def Hom.cocycleZeroAlgHom (φ : A.Hom B) : A.Cocycle 0 →ₐ[R] B.Cocycle 0 where
  toFun := φ.cocycleMap 0
  map_one' := φ.cocycleMap_cocycleOne
  map_mul' a b := by
    change φ.cocycleMap 0 (cocycleMul a b) = cocycleMul (φ.cocycleMap 0 a) (φ.cocycleMap 0 b)
    exact φ.cocycleMap_cocycleMul a b
  map_zero' := Subtype.ext (Subtype.ext (map_zero φ.toAlgebraHom))
  map_add' a b := Subtype.ext (Subtype.ext (map_add φ.toAlgebraHom _ _))
  commutes' r := Subtype.ext (Subtype.ext (AlgHom.commutes φ.toAlgebraHom r))

/-- The induced algebra map on degree-zero cocycles is
`DifferentialGradedAlgebra.Hom.cocycleMap`. -/
@[simp] theorem Hom.cocycleZeroAlgHom_apply (φ : A.Hom B) (a : A.Cocycle 0) :
    φ.cocycleZeroAlgHom a = φ.cocycleMap 0 a :=
  rfl

/-- **The map `H^0(A) → H^0(B)` induced by a homomorphism of differential graded algebras, as a
homomorphism of `R`-algebras.** Its underlying function is
`DifferentialGradedAlgebra.Hom.cohomologyMap` in degree zero; this is the precise sense in which
that map is a homomorphism of cohomology *algebras*, the hypothesis of [Stacks, Tag 09S6]. -/
def Hom.cohomologyZeroAlgHom (φ : A.Hom B) : A.Cohomology 0 →ₐ[R] B.Cohomology 0 where
  toFun := φ.cohomologyMap 0
  map_one' := congrArg (Quotient.mk _) (map_one φ.cocycleZeroAlgHom)
  map_mul' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    exact congrArg (Quotient.mk _) (map_mul φ.cocycleZeroAlgHom a b)
  map_zero' := congrArg (Quotient.mk _) (map_zero φ.cocycleZeroAlgHom)
  map_add' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    exact congrArg (Quotient.mk _) (map_add φ.cocycleZeroAlgHom a b)
  commutes' r := congrArg (Quotient.mk _) (AlgHom.commutes φ.cocycleZeroAlgHom r)

/-- The induced algebra map on degree-zero cohomology is
`DifferentialGradedAlgebra.Hom.cohomologyMap`. -/
@[simp] theorem Hom.cohomologyZeroAlgHom_apply (φ : A.Hom B) (x : A.Cohomology 0) :
    φ.cohomologyZeroAlgHom x = φ.cohomologyMap 0 x :=
  rfl

/-! ### An algebra concentrated in degree zero is its own degree-zero cohomology -/

/-- The bijection `H^0(A) ≃ A` of `DifferentialGradedAlgebra.cohomologyZeroEquiv`, for an algebra
concentrated in degree zero, as a homomorphism of `R`-algebras: on representatives it is the
inclusion of the degree-zero cocycles, so every algebra law holds by definition. -/
def cohomologyZeroAlgHom (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) : A.Cohomology 0 →ₐ[R] A.A where
  toFun := A.cohomologyZeroEquiv hA
  map_one' := rfl
  map_mul' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rfl
  map_zero' := rfl
  map_add' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rfl
  commutes' _ := rfl

/-- The algebra map `H^0(A) → A` is `DifferentialGradedAlgebra.cohomologyZeroEquiv`. -/
@[simp] theorem cohomologyZeroAlgHom_apply (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.Cohomology 0) :
    cohomologyZeroAlgHom A hA x = A.cohomologyZeroEquiv hA x :=
  rfl

/-- **`H^0(A) = A` as `R`-algebras, for an algebra concentrated in degree zero.** This is the
algebra upgrade of `DifferentialGradedAlgebra.cohomologyZeroEquiv`, and the precise content of the
hypothesis `A = H^0(A)` of [Stacks, Tag 09S8] and of [Stacks, Tag 09SA]: not a bijection of types
but an isomorphism of `R`-algebras. -/
def cohomologyZeroAlgEquiv (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) : A.Cohomology 0 ≃ₐ[R] A.A :=
  AlgEquiv.ofBijective (cohomologyZeroAlgHom A hA) (A.cohomologyZeroEquiv hA).bijective

/-- The algebra isomorphism `H^0(A) ≃ₐ[R] A` is
`DifferentialGradedAlgebra.cohomologyZeroEquiv`. -/
@[simp] theorem cohomologyZeroAlgEquiv_apply (A : DifferentialGradedAlgebra R)
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.Cohomology 0) :
    cohomologyZeroAlgEquiv A hA x = A.cohomologyZeroEquiv hA x :=
  rfl

end DifferentialGradedAlgebra

/-! ### The degree-zero cohomology is the endomorphism algebra of the regular module -/

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- Left multiplication by the unit cocycle is the identity of the regular module. -/
theorem regularMulLeft_one : regularMulLeft A 1 = 𝟙 _ :=
  Hom.ext (LinearMap.ext fun x => by
    rw [regularMulLeft_toFun_apply, Cocycle.coe_one]
    exact one_mul x)

/-- **Left multiplication on the regular module is multiplicative in the cocycle**: left
multiplication by a product is the composite of the two left multiplications, in the order which
makes it a homomorphism into the endomorphism monoid (whose product is composition). -/
theorem regularMulLeft_mul (a b : A.Cocycle 0) :
    regularMulLeft A (a * b) = regularMulLeft A b ≫ regularMulLeft A a :=
  Hom.ext (LinearMap.ext fun x => by
    rw [regularMulLeft_toFun_apply, Cocycle.coe_mul, Hom.comp_toFun_apply,
      regularMulLeft_toFun_apply, regularMulLeft_toFun_apply]
    exact mul_assoc _ _ _)

/-- Left multiplication by the zero cocycle is zero. -/
theorem regularMulLeft_zero : regularMulLeft A 0 = 0 :=
  Hom.ext (LinearMap.ext fun x => by
    rw [regularMulLeft_toFun_apply, Cocycle.coe_zero, Hom.hom_zero_toFun]
    exact zero_mul x)

/-- Left multiplication on the regular module is additive in the cocycle. -/
theorem regularMulLeft_add (a b : A.Cocycle 0) :
    regularMulLeft A (a + b) = regularMulLeft A a + regularMulLeft A b :=
  Hom.ext (LinearMap.ext fun x => by
    rw [regularMulLeft_toFun_apply, Cocycle.coe_add, Hom.hom_add_toFun, LinearMap.add_apply,
      regularMulLeft_toFun_apply, regularMulLeft_toFun_apply]
    exact add_mul _ _ x)

/-- Left multiplication by the image of a scalar is that scalar acting on the identity. -/
theorem regularMulLeft_algebraMap (r : R) :
    regularMulLeft A (algebraMap R (A.Cocycle 0) r) = r • 𝟙 _ :=
  Hom.ext (LinearMap.ext fun x => by
    rw [regularMulLeft_toFun_apply, Cocycle.coe_algebraMap]
    show algebraMap R A.A r * x = _
    rw [← Algebra.smul_def]
    rfl)

/-- The bijection `H^0(A) ≃ End_{D(A, d)}(A)`: the bijection
`H^0(A) ≃ Hom_{D(A,d)}(A, A[0])` of `DifferentialGradedModule.cohomologyEquivDerivedHom` read
through the identification `A[0] = A`. This is the second half of
`DifferentialGradedModule.regularEndEquiv`, which is the composite of this bijection with
`DifferentialGradedAlgebra.cohomologyZeroEquiv`. -/
def cohomologyZeroEquivRegularEnd :
    A.Cohomology 0 ≃
      End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  (cohomologyEquivDerivedHom A 0).trans
    ((Iso.refl _).homCongr
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).mapIso
        ((shiftZeroIso A).app (regularModule A))))

/-- On the class of a cocycle, the bijection `H^0(A) ≃ End_{D(A, d)}(A)` is the class in
`D(A, d)` of left multiplication by that cocycle. -/
theorem cohomologyZeroEquivRegularEnd_mk (a : A.Cocycle 0) :
    cohomologyZeroEquivRegularEnd A (Quotient.mk _ a) =
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (regularMulLeft A a) := by
  simp only [cohomologyZeroEquivRegularEnd, Equiv.trans_apply, regularMulLeft, Functor.map_comp]
  rfl

/-- The map `H^0(A) → End_{D(A, d)}(A)` of
`DifferentialGradedModule.cohomologyZeroEquivRegularEnd`, as a homomorphism of `R`-algebras: a
class acts by left multiplication by a representative, which is unital, multiplicative, additive
and `R`-linear in the representative, and the quotient and localization functors preserve all of
that. -/
def cohomologyZeroRegularEndAlgHom :
    A.Cohomology 0 →ₐ[R]
      End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) where
  toFun := cohomologyZeroEquivRegularEnd A
  map_one' := by
    rw [show (1 : A.Cohomology 0) = Quotient.mk _ (1 : A.Cocycle 0) from rfl,
      cohomologyZeroEquivRegularEnd_mk, regularMulLeft_one]
    exact CategoryTheory.Functor.map_id _ _
  map_mul' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rw [show (Quotient.mk _ a * Quotient.mk _ b : A.Cohomology 0) = Quotient.mk _ (a * b) from rfl,
      cohomologyZeroEquivRegularEnd_mk, cohomologyZeroEquivRegularEnd_mk,
      cohomologyZeroEquivRegularEnd_mk, regularMulLeft_mul]
    exact Functor.map_comp _ _ _
  map_zero' := by
    rw [show (0 : A.Cohomology 0) = Quotient.mk _ (0 : A.Cocycle 0) from rfl,
      cohomologyZeroEquivRegularEnd_mk, regularMulLeft_zero]
    exact Functor.map_zero _ _ _
  map_add' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rw [show (Quotient.mk _ a + Quotient.mk _ b : A.Cohomology 0) = Quotient.mk _ (a + b) from rfl,
      cohomologyZeroEquivRegularEnd_mk, cohomologyZeroEquivRegularEnd_mk,
      cohomologyZeroEquivRegularEnd_mk, regularMulLeft_add]
    exact Functor.map_add _
  commutes' r := by
    rw [show algebraMap R (A.Cohomology 0) r = Quotient.mk _ (algebraMap R (A.Cocycle 0) r) from
        rfl,
      cohomologyZeroEquivRegularEnd_mk, regularMulLeft_algebraMap]
    change _ = r • 𝟙 _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- The algebra map `H^0(A) → End_{D(A,d)}(A)` is
`DifferentialGradedModule.cohomologyZeroEquivRegularEnd`. -/
@[simp] theorem cohomologyZeroRegularEndAlgHom_apply (x : A.Cohomology 0) :
    cohomologyZeroRegularEndAlgHom A x = cohomologyZeroEquivRegularEnd A x :=
  rfl

/-- **The degree-zero cohomology of a differential graded algebra is the endomorphism `R`-algebra
of the regular module in `D(A, d)`**: `H^0(A) ≃ₐ[R] Hom_{D(A,d)}(A, A)`, the multiplication on the
right-hand side being composition.

This is the algebra upgrade of `DifferentialGradedModule.cohomologyEquivDerivedHom` in degree
zero ([Stacks, Tag 09KY] for the regular module), and it needs no hypothesis on `A`. -/
def cohomologyZeroRegularEndAlgEquiv :
    A.Cohomology 0 ≃ₐ[R]
      End ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) :=
  AlgEquiv.ofBijective (cohomologyZeroRegularEndAlgHom A)
    (cohomologyZeroEquivRegularEnd A).bijective

/-- The algebra isomorphism `H^0(A) ≃ₐ[R] End_{D(A,d)}(A)` is
`DifferentialGradedModule.cohomologyZeroEquivRegularEnd`. -/
@[simp] theorem cohomologyZeroRegularEndAlgEquiv_apply (x : A.Cohomology 0) :
    cohomologyZeroRegularEndAlgEquiv A x = cohomologyZeroEquivRegularEnd A x :=
  rfl

/-- **The identification of `A` with the endomorphism algebra of the regular module is the
general one, read through `H^0(A) = A`.** For `A` concentrated in degree zero,
`DifferentialGradedModule.regularEndAlgEquiv` composed with
`DifferentialGradedAlgebra.cohomologyZeroAlgEquiv` is
`DifferentialGradedModule.cohomologyZeroRegularEndAlgEquiv`. So the hypothesis `A = H^0(A)` of
[Stacks, Tag 09S8] is used only to rewrite the source of a hypothesis-free isomorphism. -/
theorem regularEndAlgEquiv_cohomologyZeroAlgEquiv
    (hA : ∀ i : ℤ, i ≠ 0 → A.grading i = ⊥) (x : A.Cohomology 0) :
    regularEndAlgEquiv A hA (A.cohomologyZeroAlgEquiv hA x) =
      cohomologyZeroRegularEndAlgEquiv A x := by
  induction x using Quotient.ind with | _ a => ?_
  rw [cohomologyZeroRegularEndAlgEquiv_apply, cohomologyZeroEquivRegularEnd_mk]
  show (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
    (regularMulLeft A (degreeZeroCocycle A hA (a.1 : A.A))) = _
  rw [show degreeZeroCocycle A hA (a.1 : A.A) = a from Subtype.ext (Subtype.ext rfl)]

end DifferentialGradedModule

/-! ### The action of a degree-zero cocycle on a bimodule is functorial -/

/- The underlying cochain complex is made locally reducible: the components of the left-action
cochain are elements of `N.rightModule.toCochainComplex.X i`, which is the homogeneous piece
`N.rightModule.grading i` by definition but not reducibly so. -/
attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex

namespace DifferentialGraded.Bimodule

open CochainComplex.HomComplex DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} (N : Bimodule A B)

/-- Two `R`-linear endomorphisms of the underlying module of a bimodule agree if they agree on
every homogeneous element. -/
private theorem linearMap_apply_eq_of_forall_homogeneous
    {f g : N.rightModule.M →ₗ[R] N.rightModule.M}
    (h : ∀ (p : ℤ) (x : N.rightModule.grading p), f x = g x) (x : N.rightModule.M) : f x = g x :=
  LinearMap.congr_fun (DirectSum.decompose_lhom_ext N.rightModule.grading fun p =>
    LinearMap.ext (h p)) x

/-- **Left multiplication on a bimodule is multiplicative in the acting degree-zero cocycle**:
left multiplication by a product is left multiplication by the right factor followed by left
multiplication by the left factor. This is the `LeftAction.map_mul` law of the left action, read
through `DifferentialGraded.Bimodule.leftMultiplication_apply`. -/
theorem leftMultiplication_cocycleMul (a b : A.Cocycle 0) (x : N.rightModule.M) :
    (N.leftMultiplication 0 (a * b).1).1 x =
      (N.leftMultiplication 0 a.1).1 ((N.leftMultiplication 0 b.1).1 x) := by
  have key : N.leftAction.1.action 0 (a * b).1 =
      (N.leftAction.1.action 0 b.1).comp (N.leftAction.1.action 0 a.1) (by omega) :=
    N.leftAction.1.map_mul 0 0 a.1 b.1
  have hcomponent (i j : ℤ) (hij : i + 0 = j) (c : A.grading 0)
      (y : N.rightModule.grading i) :
      ((show N.rightModule.grading j from
        (N.leftAction.1.action 0 c).v i j hij y) : N.rightModule.M) =
        (N.leftMultiplication 0 c).1 y := by
    subst j
    exact (leftMultiplication_apply N 0 i c y).symm
  refine N.linearMap_apply_eq_of_forall_homogeneous
    (g := (N.leftMultiplication 0 a.1).1 ∘ₗ (N.leftMultiplication 0 b.1).1) (fun p x => ?_) x
  rw [LinearMap.comp_apply, leftMultiplication_apply N 0 p (a * b).1 x, key,
    Cochain.comp_v _ _ _ p (p + 0) (p + 0) (by omega) (by omega),
    ← hcomponent p (p + 0) (by omega) b.1 x]
  exact hcomponent (p + 0) (p + 0) (by omega) a.1 _

/-- **The unit cocycle acts on a bimodule as the identity.** This is the `LeftAction.map_one` law
of the left action. -/
theorem leftMultiplication_cocycleOne (x : N.rightModule.M) :
    (N.leftMultiplication 0 (1 : A.Cocycle 0).1).1 x = x := by
  have key : N.leftAction.1.action 0 (1 : A.Cocycle 0).1 =
      Cochain.ofHom (𝟙 N.rightModule.toCochainComplex) :=
    N.leftAction.1.map_one
  have hone (i j : ℤ) (hij : i + 0 = j) (y : N.rightModule.grading i) :
      ((show N.rightModule.grading j from
        (Cochain.ofHom (𝟙 N.rightModule.toCochainComplex)).v i j hij y) :
          N.rightModule.M) = y := by
    obtain rfl : j = i := by omega
    rw [Cochain.ofHom_v]
    rfl
  refine N.linearMap_apply_eq_of_forall_homogeneous (g := LinearMap.id) (fun p x => ?_) x
  rw [leftMultiplication_apply N 0 p (1 : A.Cocycle 0).1 x, key]
  exact hone p (p + 0) (by omega) x

/-- The action of a degree-zero cocycle of `A` on a differential graded `(A, B)`-bimodule, as an
endomorphism of the underlying right `B`-module: the homomorphism `N ⟶ N[0]` of
`DifferentialGraded.Bimodule.cocycleAction`, read through the identification `N[0] = N` of
`DifferentialGradedModule.shiftZeroHom`. -/
def cocycleActionZero (a : A.Cocycle 0) : N.rightModule ⟶ N.rightModule :=
  N.cocycleAction 0 a ≫ shiftZeroHom B N.rightModule

/-- The action of a degree-zero cocycle is left multiplication by it. -/
theorem cocycleActionZero_toFun_apply (a : A.Cocycle 0) (x : N.rightModule.M) :
    (N.cocycleActionZero a).toFun x = (N.leftMultiplication 0 a.1).1 x := by
  show (shiftZeroHom B N.rightModule).toFun ((N.cocycleAction 0 a).toFun x) = _
  rw [N.cocycleAction_toFun 0 a]
  rfl

/-- **The unit cocycle acts on a bimodule by the identity.** -/
theorem cocycleActionZero_one : N.cocycleActionZero 1 = 𝟙 _ :=
  DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => by
    rw [cocycleActionZero_toFun_apply, leftMultiplication_cocycleOne]
    rfl)

/-- **The action of degree-zero cocycles on a bimodule is functorial**: a product of cocycles acts
by the composite of their actions. Together with
`DifferentialGraded.Bimodule.cocycleActionZero_one` this makes
`DifferentialGraded.Bimodule.cocycleActionZero` a homomorphism of monoids from `Z^0(A)` into the
endomorphism monoid of the right module, and hence — after `DifferentialGraded.Bimodule`
`.toHomotopyCategory_map_cocycleAction_eq` descends it to cohomology classes — makes the
comparison `H^0(A) → Hom_{D(B,d)}(N, N)` of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` multiplicative. -/
theorem cocycleActionZero_mul (a b : A.Cocycle 0) :
    N.cocycleActionZero (a * b) = N.cocycleActionZero b ≫ N.cocycleActionZero a :=
  DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => by
    rw [cocycleActionZero_toFun_apply, DifferentialGradedModule.Hom.comp_toFun_apply,
      cocycleActionZero_toFun_apply, cocycleActionZero_toFun_apply,
      leftMultiplication_cocycleMul])


/-! ### Left multiplication is additive and `R`-linear in the acting element -/

/-- Left multiplication on a bimodule is `R`-linear in the acting homogeneous element: the left
action records the action of the degree-`k` part by an `R`-linear family of cochains. -/
theorem leftMultiplication_smul (k : ℤ) (r : R) (a : A.grading k) :
    N.leftMultiplication k (r • a) = r • N.leftMultiplication k a := by
  refine Subtype.ext (LinearMap.ext (N.linearMap_apply_eq_of_forall_homogeneous fun p x => ?_))
  show (N.leftMultiplication k (r • a)).1 x = r • (N.leftMultiplication k a).1 x
  simp only [leftMultiplication_apply, map_smul, Cochain.smul_v]
  rfl

/-- Left multiplication by the negative of a homogeneous element is the negative of left
multiplication by it. -/
theorem leftMultiplication_neg (k : ℤ) (a : A.grading k) :
    N.leftMultiplication k (-a) = -N.leftMultiplication k a := by
  have h := N.leftMultiplication_sub k 0 a
  rwa [zero_sub, leftMultiplication_zero, zero_sub] at h

/-- Left multiplication on a bimodule is additive in the acting homogeneous element. -/
theorem leftMultiplication_add (k : ℤ) (a b : A.grading k) :
    N.leftMultiplication k (a + b) =
      N.leftMultiplication k a + N.leftMultiplication k b := by
  have h := N.leftMultiplication_sub k a (-b)
  rwa [sub_neg_eq_add, leftMultiplication_neg, sub_neg_eq_add] at h

/-! ### The degree-zero cohomology acts on a bimodule by an algebra homomorphism -/

/-- **The zero cocycle acts by zero.** -/
theorem cocycleActionZero_zero : N.cocycleActionZero 0 = 0 := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  rw [cocycleActionZero_toFun_apply, show ((0 : A.Cocycle 0).1 : A.grading 0) = 0 from rfl,
    leftMultiplication_zero]
  rfl

/-- **The action of degree-zero cocycles on a bimodule is additive.** -/
theorem cocycleActionZero_add (a b : A.Cocycle 0) :
    N.cocycleActionZero (a + b) = N.cocycleActionZero a + N.cocycleActionZero b := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  rw [cocycleActionZero_toFun_apply,
    show ((a + b).1 : A.grading 0) = a.1 + b.1 from rfl, leftMultiplication_add,
    DifferentialGradedModule.Hom.hom_add_toFun, LinearMap.add_apply,
    cocycleActionZero_toFun_apply, cocycleActionZero_toFun_apply]
  rfl

/-- **The action of degree-zero cocycles on a bimodule is `R`-linear.** -/
theorem cocycleActionZero_smul (r : R) (a : A.Cocycle 0) :
    N.cocycleActionZero (r • a) = r • N.cocycleActionZero a := by
  refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => ?_)
  rw [cocycleActionZero_toFun_apply, show ((r • a).1 : A.grading 0) = r • a.1 from rfl,
    leftMultiplication_smul, DifferentialGradedModule.Hom.smul_toFun, LinearMap.smul_apply,
    cocycleActionZero_toFun_apply]
  rfl

/-- The image of a scalar acts by that scalar multiple of the identity. -/
theorem cocycleActionZero_algebraMap (r : R) :
    N.cocycleActionZero (algebraMap R (A.Cocycle 0) r) = r • 𝟙 N.rightModule := by
  rw [Algebra.algebraMap_eq_smul_one, cocycleActionZero_smul, cocycleActionZero_one]

/-- **The action of a degree-zero cohomology class of `A` on a differential graded
`(A, B)`-bimodule `N`, as an endomorphism of the class of `N` in `D(B, d)`.** It is the
degree-zero comparison `H^0(A) → Hom_{D(B,d)}(N, N[0])` of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` read through the identification
`N[0] = N` of `DifferentialGradedModule.shiftZeroIso`. -/
def cohomologyZeroBimoduleEnd :
    A.Cohomology 0 →
      End ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) :=
  fun x => N.cohomologyEndomorphismComparison 0 x ≫
    (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map (shiftZeroHom B N.rightModule)

/-- On the class of a cocycle, the action of `H^0(A)` on the bimodule is the class in `D(B, d)`
of the action of that cocycle. -/
theorem cohomologyZeroBimoduleEnd_mk (a : A.Cocycle 0) :
    N.cohomologyZeroBimoduleEnd (Quotient.mk _ a) =
      (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).map (N.cocycleActionZero a) := by
  show N.cohomologyEndomorphismComparison 0 (Quotient.mk _ a) ≫ _ = _
  rw [cohomologyEndomorphismComparison_mk, cocycleActionZero, Functor.map_comp]

/-- **The action of `H^0(A)` on the bimodule is bijective exactly when the degree-zero comparison
of Tag 09R9 is.** The two differ by composition with the isomorphism `N[0] ≅ N`. -/
theorem bijective_cohomologyZeroBimoduleEnd_iff :
    Function.Bijective N.cohomologyZeroBimoduleEnd ↔
      Function.Bijective (N.cohomologyEndomorphismComparison 0) := by
  have h : N.cohomologyZeroBimoduleEnd =
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).mapIso
          ((shiftZeroIso B).app N.rightModule)).homToEquiv ∘
        N.cohomologyEndomorphismComparison 0 := rfl
  rw [h, Equiv.comp_bijective]

/-- **The action of `H^0(A)` on a differential graded `(A, B)`-bimodule `N`, as a homomorphism of
`R`-algebras `H^0(A) →ₐ[R] End_{D(B,d)}(N)`.** A class acts by the action of a representative,
which is unital and multiplicative by
`DifferentialGraded.Bimodule.cocycleActionZero_one` and `.cocycleActionZero_mul`, additive and
`R`-linear by `.cocycleActionZero_add`, `.cocycleActionZero_zero` and `.cocycleActionZero_smul`,
and the quotient and localization functors preserve all of that.

This is the shape in which [Stacks, Tag 09SA] uses the comparison of Tag 09R9: its proof feeds
the composite `Z^0(E') ↠ H^0(E') ≅ H^0(E) ≅ End_{D(B,d)}(Q) ≅ A` to
`DifferentialGradedAlgebra.exists_hom_of_degreeZero`, which needs every step to be a map of
`R`-algebras. -/
def cohomologyZeroBimoduleEndAlgHom :
    A.Cohomology 0 →ₐ[R]
      End ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule) where
  toFun := N.cohomologyZeroBimoduleEnd
  map_one' := by
    rw [show (1 : A.Cohomology 0) = Quotient.mk _ (1 : A.Cocycle 0) from rfl,
      cohomologyZeroBimoduleEnd_mk, cocycleActionZero_one]
    exact CategoryTheory.Functor.map_id _ _
  map_mul' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rw [show (Quotient.mk _ a * Quotient.mk _ b : A.Cohomology 0) = Quotient.mk _ (a * b) from rfl,
      cohomologyZeroBimoduleEnd_mk, cohomologyZeroBimoduleEnd_mk, cohomologyZeroBimoduleEnd_mk,
      cocycleActionZero_mul]
    exact Functor.map_comp _ _ _
  map_zero' := by
    rw [show (0 : A.Cohomology 0) = Quotient.mk _ (0 : A.Cocycle 0) from rfl,
      cohomologyZeroBimoduleEnd_mk, cocycleActionZero_zero]
    exact Functor.map_zero _ _ _
  map_add' x y := by
    induction x using Quotient.ind with | _ a => ?_
    induction y using Quotient.ind with | _ b => ?_
    rw [show (Quotient.mk _ a + Quotient.mk _ b : A.Cohomology 0) = Quotient.mk _ (a + b) from rfl,
      cohomologyZeroBimoduleEnd_mk, cohomologyZeroBimoduleEnd_mk, cohomologyZeroBimoduleEnd_mk,
      cocycleActionZero_add]
    exact Functor.map_add _
  commutes' r := by
    rw [show algebraMap R (A.Cohomology 0) r =
        Quotient.mk _ (algebraMap R (A.Cocycle 0) r) from rfl,
      cohomologyZeroBimoduleEnd_mk, cocycleActionZero_algebraMap]
    change _ = r • 𝟙 _
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- The algebra map `H^0(A) → End_{D(B,d)}(N)` is
`DifferentialGraded.Bimodule.cohomologyZeroBimoduleEnd`. -/
@[simp] theorem cohomologyZeroBimoduleEndAlgHom_apply (x : A.Cohomology 0) :
    N.cohomologyZeroBimoduleEndAlgHom x = N.cohomologyZeroBimoduleEnd x :=
  rfl

end DifferentialGraded.Bimodule

end
