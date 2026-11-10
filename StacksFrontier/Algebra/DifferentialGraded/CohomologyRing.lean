module

public import Mathlib.RingTheory.Congruence.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Cohomology

/-! # The algebra structure on the degree-zero cocycles and on the degree-zero cohomology

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. The degree-zero part
`A^0` is an `R`-subalgebra of `A` (Mathlib's `SetLike.GradeZero.instAlgebra`), the degree-zero
cocycles `Z^0(A) = Ker(d : A^0 → A^1)` are an `R`-subalgebra of `A^0` — the Leibniz rule in degree
`0` reads `d(ab) = (d a) b + a (d b)`, so both terms vanish on cocycles — and the degree-zero
coboundaries `d(A^{-1})` are a two-sided ideal of `Z^0(A)`, because `d(x b) = (d x) b` and
`d(a y) = a (d y)` for `a, b` degree-zero cocycles and `x, y` of degree `-1`. Hence
`H^0(A) = Z^0(A)/d(A^{-1})` is a quotient `R`-algebra and the projection is a homomorphism of
`R`-algebras.

This file installs that structure on the *existing* `DifferentialGradedAlgebra.Cocycle` and
`DifferentialGradedAlgebra.Cohomology` of `Algebra/DifferentialGraded/Cohomology.lean`: no new
carrier is introduced, and the ring operations are the ones induced by the operations of `A` on
representatives, definitionally.

## Main definitions

* `DifferentialGradedAlgebra.cocycleZeroSubalgebra`: `Z^0(A)` as an `R`-subalgebra of `A^0`. Its
  coercion to a type *is* `A.Cocycle 0`, which is what gives the instances below.
* `DifferentialGradedAlgebra.instRingCocycleZero` and
  `DifferentialGradedAlgebra.instAlgebraCocycleZero`: the `Ring` and `Algebra R` structures on
  `A.Cocycle 0`.
* `DifferentialGradedAlgebra.cohomologyZeroRingCon`: being cohomologous, as a ring congruence on
  `Z^0(A)`. Its underlying setoid *is* `A.cohomologySetoid 0`, which is what gives the instances
  below.
* `DifferentialGradedAlgebra.instRingCohomologyZero` and
  `DifferentialGradedAlgebra.instAlgebraCohomologyZero`: the `Ring` and `Algebra R` structures on
  `A.Cohomology 0`.
* `DifferentialGradedAlgebra.Cocycle.valAlgHom`: the inclusion `Z^0(A) → A`, as a homomorphism of
  `R`-algebras.
* `DifferentialGradedAlgebra.cohomologyZeroMk`: the projection `Z^0(A) → H^0(A)`, as a
  homomorphism of `R`-algebras.

## Main results

* `DifferentialGradedAlgebra.Cocycle.coe_mul`, `DifferentialGradedAlgebra.Cocycle.coe_one` and
  their siblings: the ring operations on `A.Cocycle 0` are those of `A` on underlying elements.
* `DifferentialGradedAlgebra.Cohomology.mk_mul`, `DifferentialGradedAlgebra.Cohomology.mk_one`
  and their siblings: the ring operations on `A.Cohomology 0` are those of `Z^0(A)` on
  representatives.
* `DifferentialGradedAlgebra.Cohomology.mk_eq_zero_iff`: a class vanishes exactly when a
  representative is a coboundary.

## Implementation notes

*Why a `Subalgebra` and a `RingCon` rather than hand-written instances.* `A.Cocycle 0` is by
definition the subtype of `A^0` cut out by `d a = 0`, so it is the coercion to a type of the
`R`-subalgebra of `A^0` with that carrier — definitionally, not merely isomorphically. Likewise
`A.Cohomology 0` is by definition the quotient of `A.Cocycle 0` by the setoid of being
cohomologous, and that setoid is the one underlying a ring congruence. So both structures are
obtained by `inferInstanceAs` from Mathlib's `Subalgebra` and `RingCon` instances, and every
compatibility lemma below holds by `rfl`. In particular the multiplication on `A.Cohomology 0`
agrees with `DifferentialGradedAlgebra.cocycleMul` in degree `0` on representatives (see
`Algebra/DifferentialGraded/Module/DerivedEquivalenceQuasiIso.lean`, which is where the
degree-general cocycle product lives); no second notion of product is introduced.

*Only degree zero.* `A.Cocycle k` is a ring only for `k = 0`: the product of a degree-`k` and a
degree-`l` cocycle has degree `k + l`. The degree-general product is
`DifferentialGradedAlgebra.cocycleMul`, and the graded algebra `⨁_k H^k(A)` is not formed here.

*Two-sidedness.* `Ideal` in Mathlib is a left ideal, so the quotient of a possibly
noncommutative ring is taken along a `RingCon`; the `mul'` field below is exactly the assertion
that the coboundaries are a *two-sided* ideal of `Z^0(A)`.

As everywhere in this chapter's differential graded interface, the base ring and the algebra live
in a single universe `u`, following the `DifferentialGradedAlgebra` encoding of Stacks Tag 09JJ.

## References

* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V) for the differential
  graded algebra, and [Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) for its cohomology.
-/

@[expose] public section

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The differential of a differential graded algebra kills the unit: the Leibniz rule for
`1 = 1 · 1` reads `d 1 = 2 d 1`, since `1` has degree `0`.

Kept `private`, following `Algebra/DifferentialGraded/Module/LeftNativeCover.lean:130`: a public
theorem of this statement already exists under the name `DifferentialGradedAlgebra.d_one` at
`Algebra/DifferentialGraded/Endomorphism/BimoduleTotalization.lean:70`, and importing that file
here would pull the whole `Endomorphism` tree into the import closure of this module for a
two-line fact. Collapsing the copies is a repo-tier job: hoist the fact into a low module below
all of the trees that want it. -/
private theorem dOne (A : DifferentialGradedAlgebra R) : A.d 1 = 0 := by
  have h1 : (1 : A.A) ∈ A.grading 0 := SetLike.one_mem_graded A.grading
  simpa using A.leibniz 0 0 1 1 h1 h1

/-! ### The degree-zero cocycles as an `R`-algebra -/

/-- **The degree-zero cocycles `Z^0(A)` of a differential graded algebra, as an `R`-subalgebra of
the degree-zero part `A^0`.** The unit is a cocycle because the differential kills it, and the
product of two degree-zero cocycles is a cocycle by the Leibniz rule, which in degree `0` reads
`d(ab) = (d a) b + a (d b)`.

Its coercion to a type is `A.Cocycle 0` on the nose, which is what installs
`DifferentialGradedAlgebra.instRingCocycleZero` and
`DifferentialGradedAlgebra.instAlgebraCocycleZero`. -/
def cocycleZeroSubalgebra (A : DifferentialGradedAlgebra R) : Subalgebra R ↥(A.grading 0) where
  carrier := {a | A.d a = 0}
  mul_mem' := by
    intro a b ha hb
    change A.d ((a * b : ↥(A.grading 0)) : A.A) = 0
    rw [SetLike.GradeZero.coe_mul, A.leibniz 0 0 _ _ a.property b.property,
      show A.d (a : A.A) = 0 from ha, show A.d (b : A.A) = 0 from hb]
    simp
  one_mem' := by
    change A.d ((1 : ↥(A.grading 0)) : A.A) = 0
    rw [SetLike.GradeZero.coe_one]
    exact dOne A
  add_mem' := by
    intro a b ha hb
    change A.d ((a + b : ↥(A.grading 0)) : A.A) = 0
    rw [Submodule.coe_add, map_add, show A.d (a : A.A) = 0 from ha,
      show A.d (b : A.A) = 0 from hb, add_zero]
  zero_mem' := by
    change A.d ((0 : ↥(A.grading 0)) : A.A) = 0
    rw [Submodule.coe_zero, map_zero]
  algebraMap_mem' := by
    intro r
    change A.d ((algebraMap R ↥(A.grading 0) r : ↥(A.grading 0)) : A.A) = 0
    rw [SetLike.GradeZero.coe_algebraMap, Algebra.algebraMap_eq_smul_one, map_smul, dOne A,
      smul_zero]

/-- The degree-zero cocycles of a differential graded algebra are the `R`-subalgebra
`DifferentialGradedAlgebra.cocycleZeroSubalgebra` of `A^0`, by definition. -/
theorem coe_cocycleZeroSubalgebra (A : DifferentialGradedAlgebra R) :
    ↥A.cocycleZeroSubalgebra = A.Cocycle 0 :=
  rfl

/-- **The degree-zero cocycles of a differential graded algebra form a ring**, the operations
being those of `A` on underlying elements. -/
instance instRingCocycleZero {A : DifferentialGradedAlgebra R} : Ring (A.Cocycle 0) :=
  inferInstanceAs (Ring ↥A.cocycleZeroSubalgebra)

/-- **The degree-zero cocycles of a differential graded algebra form an `R`-algebra.** -/
instance instAlgebraCocycleZero {A : DifferentialGradedAlgebra R} : Algebra R (A.Cocycle 0) :=
  inferInstanceAs (Algebra R ↥A.cocycleZeroSubalgebra)

namespace Cocycle

variable {A : DifferentialGradedAlgebra R}

/-- The unit of `Z^0(A)` is the unit of `A`. -/
@[simp] theorem coe_one : (((1 : A.Cocycle 0).1 : A.grading 0) : A.A) = 1 := rfl

/-- The product in `Z^0(A)` is the product in `A`. -/
@[simp] theorem coe_mul (a b : A.Cocycle 0) :
    (((a * b).1 : A.grading 0) : A.A) = ((a.1 : A.A)) * ((b.1 : A.A)) :=
  rfl

/-- The zero of `Z^0(A)` is the zero of `A`. -/
@[simp] theorem coe_zero : (((0 : A.Cocycle 0).1 : A.grading 0) : A.A) = 0 := rfl

/-- The sum in `Z^0(A)` is the sum in `A`. -/
@[simp] theorem coe_add (a b : A.Cocycle 0) :
    (((a + b).1 : A.grading 0) : A.A) = ((a.1 : A.A)) + ((b.1 : A.A)) :=
  rfl

/-- The negation in `Z^0(A)` is the negation in `A`. -/
@[simp] theorem coe_neg (a : A.Cocycle 0) : (((-a).1 : A.grading 0) : A.A) = -((a.1 : A.A)) :=
  rfl

/-- The difference in `Z^0(A)` is the difference in `A`. -/
@[simp] theorem coe_sub (a b : A.Cocycle 0) :
    (((a - b).1 : A.grading 0) : A.A) = ((a.1 : A.A)) - ((b.1 : A.A)) :=
  rfl

/-- The structure map of `Z^0(A)` is the structure map of `A`. -/
@[simp] theorem coe_algebraMap (r : R) :
    (((algebraMap R (A.Cocycle 0) r).1 : A.grading 0) : A.A) = algebraMap R A.A r :=
  rfl

/-- **The inclusion `Z^0(A) → A` of the degree-zero cocycles, as a homomorphism of
`R`-algebras.** -/
def valAlgHom (A : DifferentialGradedAlgebra R) : A.Cocycle 0 →ₐ[R] A.A where
  toFun a := (a.1 : A.A)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The inclusion `Z^0(A) → A` is the underlying element. -/
@[simp] theorem valAlgHom_apply (a : A.Cocycle 0) : valAlgHom A a = (a.1 : A.A) := rfl

end Cocycle

/-! ### The degree-zero cohomology as an `R`-algebra -/

/-- **Being cohomologous in degree zero, as a ring congruence on `Z^0(A)`.** The relation is the
one of `DifferentialGradedAlgebra.cohomologySetoid` in degree `0` — the underlying setoid of this
congruence *is* `A.cohomologySetoid 0` — and the two fields record that the degree-zero
coboundaries are an ideal of `Z^0(A)`:

* `mul'` is two-sidedness. If `w - x = d p` and `y - z = d q` with `p, q` of degree `-1`, then
  `w y - x z = (d p) y + x (d q) = d (p y + x q)`, the Leibniz rule contributing nothing extra
  because `d y = 0` and `d x = 0`;
* `add'` is additivity, `d p + d q = d (p + q)`. -/
def cohomologyZeroRingCon (A : DifferentialGradedAlgebra R) : RingCon (A.Cocycle 0) where
  r a b := ∃ c : A.grading (0 - 1), (a.1 : A.A) - b.1 = A.d c
  iseqv := (A.cohomologySetoid 0).iseqv
  mul' := by
    rintro w x y z ⟨p, hp⟩ ⟨q, hq⟩
    have hy : A.d (y.1 : A.A) = 0 := y.2
    have hx : A.d (x.1 : A.A) = 0 := x.2
    have hmem : (p : A.A) * (y.1 : A.A) + (x.1 : A.A) * (q : A.A) ∈ A.grading (0 - 1) := by
      refine add_mem ?_ ?_
      · simpa using SetLike.mul_mem_graded p.property y.1.property
      · simpa using SetLike.mul_mem_graded x.1.property q.property
    refine ⟨⟨_, hmem⟩, ?_⟩
    change (w.1 : A.A) * (y.1 : A.A) - (x.1 : A.A) * (z.1 : A.A) =
      A.d ((p : A.A) * (y.1 : A.A) + (x.1 : A.A) * (q : A.A))
    rw [map_add, A.leibniz (0 - 1) 0 _ _ p.property y.1.property,
      A.leibniz 0 (0 - 1) _ _ x.1.property q.property, hy, hx,
      show ((0 : ℤ).negOnePow : ℤ) = 1 by simp,
      show A.d (p : A.A) = (w.1 : A.A) - (x.1 : A.A) from hp.symm,
      show A.d (q : A.A) = (y.1 : A.A) - (z.1 : A.A) from hq.symm]
    simp only [mul_zero, smul_zero, zero_mul, add_zero, zero_add, one_smul]
    rw [sub_mul, mul_sub]
    abel
  add' := by
    rintro w x y z ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p + q, ?_⟩
    change (w.1 : A.A) + (y.1 : A.A) - ((x.1 : A.A) + (z.1 : A.A)) = _
    rw [Submodule.coe_add, map_add, ← hp, ← hq]
    abel

/-- The degree-zero cohomology of a differential graded algebra is the quotient of `Z^0(A)` by
the ring congruence `DifferentialGradedAlgebra.cohomologyZeroRingCon`, by definition. -/
theorem quotient_cohomologyZeroRingCon (A : DifferentialGradedAlgebra R) :
    (cohomologyZeroRingCon A).Quotient = A.Cohomology 0 :=
  rfl

/-- **The degree-zero cohomology of a differential graded algebra is a ring**, the quotient ring
of the degree-zero cocycles by the degree-zero coboundaries. -/
instance instRingCohomologyZero {A : DifferentialGradedAlgebra R} : Ring (A.Cohomology 0) :=
  inferInstanceAs (Ring (cohomologyZeroRingCon A).Quotient)

namespace Cohomology

variable {A : DifferentialGradedAlgebra R}

/-- The unit of `H^0(A)` is the class of the unit cocycle. -/
@[simp] theorem mk_one : (Quotient.mk _ (1 : A.Cocycle 0) : A.Cohomology 0) = 1 := rfl

/-- The product in `H^0(A)` is computed on representatives. -/
@[simp] theorem mk_mul (a b : A.Cocycle 0) :
    (Quotient.mk _ (a * b) : A.Cohomology 0) = Quotient.mk _ a * Quotient.mk _ b :=
  rfl

/-- The zero of `H^0(A)` is the class of the zero cocycle. -/
@[simp] theorem mk_zero : (Quotient.mk _ (0 : A.Cocycle 0) : A.Cohomology 0) = 0 := rfl

/-- The sum in `H^0(A)` is computed on representatives. -/
@[simp] theorem mk_add (a b : A.Cocycle 0) :
    (Quotient.mk _ (a + b) : A.Cohomology 0) = Quotient.mk _ a + Quotient.mk _ b :=
  rfl

/-- The negation in `H^0(A)` is computed on representatives. -/
@[simp] theorem mk_neg (a : A.Cocycle 0) :
    (Quotient.mk _ (-a) : A.Cohomology 0) = -Quotient.mk _ a :=
  rfl

/-- The difference in `H^0(A)` is computed on representatives. -/
@[simp] theorem mk_sub (a b : A.Cocycle 0) :
    (Quotient.mk _ (a - b) : A.Cohomology 0) = Quotient.mk _ a - Quotient.mk _ b :=
  rfl

/-- **A degree-zero cohomology class vanishes exactly when a representative is a coboundary.** -/
theorem mk_eq_zero_iff (a : A.Cocycle 0) :
    (Quotient.mk _ a : A.Cohomology 0) = 0 ↔ ∃ c : A.grading (0 - 1), (a.1 : A.A) = A.d c := by
  rw [← mk_zero, Cohomology.mk_eq_mk_iff]
  simp

end Cohomology

/-- The structure map of the degree-zero cohomology as an `R`-algebra: the class of the image of
a scalar in the degree-zero cocycles. -/
def cohomologyZeroAlgebraMap (A : DifferentialGradedAlgebra R) : R →+* A.Cohomology 0 :=
  (cohomologyZeroRingCon A).mk'.comp (algebraMap R (A.Cocycle 0))

/-- The structure map of `H^0(A)` is the class of the structure map of `Z^0(A)`. -/
@[simp] theorem cohomologyZeroAlgebraMap_apply (A : DifferentialGradedAlgebra R) (r : R) :
    cohomologyZeroAlgebraMap A r = Quotient.mk _ (algebraMap R (A.Cocycle 0) r) :=
  rfl

/-- The scalars act centrally on the degree-zero cohomology: they do already on the degree-zero
cocycles, `A` being an `R`-algebra, and the projection is multiplicative. -/
theorem cohomologyZeroAlgebraMap_commutes (A : DifferentialGradedAlgebra R) (r : R)
    (x : A.Cohomology 0) :
    cohomologyZeroAlgebraMap A r * x = x * cohomologyZeroAlgebraMap A r := by
  induction x using Quotient.ind with
  | _ a =>
    change (Quotient.mk _ (algebraMap R (A.Cocycle 0) r * a) : A.Cohomology 0) =
      Quotient.mk _ (a * algebraMap R (A.Cocycle 0) r)
    rw [Algebra.commutes]

/-- **The degree-zero cohomology of a differential graded algebra is an `R`-algebra**, the
quotient `R`-algebra of the degree-zero cocycles by the degree-zero coboundaries. -/
instance instAlgebraCohomologyZero {A : DifferentialGradedAlgebra R} :
    Algebra R (A.Cohomology 0) :=
  (cohomologyZeroAlgebraMap A).toAlgebra' (cohomologyZeroAlgebraMap_commutes A)

/-- **The projection `Z^0(A) → H^0(A)`, as a homomorphism of `R`-algebras.** -/
def cohomologyZeroMk (A : DifferentialGradedAlgebra R) : A.Cocycle 0 →ₐ[R] A.Cohomology 0 where
  toFun a := Quotient.mk _ a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The projection `Z^0(A) → H^0(A)` sends a cocycle to its class. -/
@[simp] theorem cohomologyZeroMk_apply {A : DifferentialGradedAlgebra R} (a : A.Cocycle 0) :
    cohomologyZeroMk A a = Quotient.mk _ a :=
  rfl

/-- The projection `Z^0(A) → H^0(A)` is surjective. -/
theorem cohomologyZeroMk_surjective (A : DifferentialGradedAlgebra R) :
    Function.Surjective (cohomologyZeroMk A) :=
  Quotient.mk_surjective

/-- The `Algebra R` structure on `H^0(A)` is the one induced by the projection. -/
@[simp] theorem algebraMap_cohomologyZero {A : DifferentialGradedAlgebra R} (r : R) :
    algebraMap R (A.Cohomology 0) r = Quotient.mk _ (algebraMap R (A.Cocycle 0) r) :=
  rfl

end DifferentialGradedAlgebra

end
