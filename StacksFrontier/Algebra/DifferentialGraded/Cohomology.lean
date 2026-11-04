module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-! # The cohomology of a differential graded algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. Its degree-`k`
cohomology `H^k(A)` is the homogeneous elements of degree `k` killed by the differential, modulo
the differentials of the homogeneous elements of degree `k - 1`.

## Main definitions

* `DifferentialGradedAlgebra.Cocycle`: the degree-`k` cocycles.
* `DifferentialGradedAlgebra.cohomologySetoid`: being cohomologous, as an equivalence relation on
  them.
* `DifferentialGradedAlgebra.Cohomology`: the quotient, `H^k(A)`.

## Main results

* `DifferentialGradedAlgebra.Cohomology.mk_eq_mk_iff`: two cocycles have the same class exactly
  when their difference is a coboundary.

## Implementation notes

The cocycles and the coboundaries are taken inside the homogeneous pieces `A.grading k`, so that
`H^k(A)` is a quotient of a subtype of `A.grading k` and no cohomology of the underlying cochain
complex is involved. This is the form in which the cohomology is used as the source of the
canonical map to the derived graded endomorphisms of a differential graded bimodule
([Stacks, Tag 09R9]).

As everywhere in this chapter's differential graded interface, the base ring and the algebra live
in a single universe `u`, following the `DifferentialGradedAlgebra` encoding of Stacks Tag 09JJ.

## References

* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
-/

@[expose] public section

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The degree-`k` cocycles of a differential graded algebra: the homogeneous elements of degree
`k` killed by the differential. -/
abbrev Cocycle (A : DifferentialGradedAlgebra R) (k : ℤ) := {a : A.grading k // A.d a = 0}

/-- Two degree-`k` cocycles of a differential graded algebra are cohomologous when their
difference is the differential of a homogeneous element of degree `k - 1`. -/
def cohomologySetoid (A : DifferentialGradedAlgebra R) (k : ℤ) : Setoid (A.Cocycle k) where
  r a b := ∃ c : A.grading (k - 1), (a.1 : A.A) - b.1 = A.d c
  iseqv :=
    { refl := fun a => ⟨0, by simp⟩
      symm := by
        rintro a b ⟨c, hc⟩
        exact ⟨-c, by simpa only [Submodule.coe_neg, map_neg, neg_sub] using congrArg Neg.neg hc⟩
      trans := by
        rintro a b c ⟨x, hx⟩ ⟨y, hy⟩
        refine ⟨x + y, ?_⟩
        simp only [Submodule.coe_add, map_add, ← hx, ← hy]
        abel }

/-- The degree-`k` cohomology of a differential graded algebra: homogeneous cocycles of degree `k`
modulo the differentials of homogeneous elements of degree `k - 1`. -/
abbrev Cohomology (A : DifferentialGradedAlgebra R) (k : ℤ) := Quotient (A.cohomologySetoid k)

/-- Two cocycles have the same cohomology class precisely when their difference is a
coboundary. -/
theorem Cohomology.mk_eq_mk_iff (A : DifferentialGradedAlgebra R) (k : ℤ) (a b : A.Cocycle k) :
    (Quotient.mk _ a : A.Cohomology k) = Quotient.mk _ b ↔
      ∃ c : A.grading (k - 1), (a.1 : A.A) - b.1 = A.d c :=
  Quotient.eq

end DifferentialGradedAlgebra

end
