module

public import StacksFrontier.AlgebraicGeometry.Curves.Node.Multicross
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Quadric

/-!
# The completed local ring of a node

Over an algebraically closed field `k`, a complete local `k`-algebra is a nondegenerate
quadratic hypersurface `k[[x, y]]/(a x² + b x y + c y²)`, `4ac - b² ≠ 0`, if and only if it is
the two-branch multicross ring: the subring of `k[[t]] × k[[t]]` of pairs with equal constant
coefficient. This is the step "the only nondegenerate quadric in two variables is `xy` up to
change in coordinates" in the proof of Stacks Tag 0C4D, in the form in which that proof uses
it, and it compares the two descriptions of a node used in Tags 0C49 and 0C1W: the
quadratic-form description and the multicross description.

Both directions are elementary given the two halves. The hypersurface of a nondegenerate form
is `k[[x, y]]/(xy)` by `Stacks.Curves.nonempty_quotient_nodalBinaryQuadratic_algEquiv`, and
`k[[x, y]]/(xy)` is the multicross ring by `Stacks.Curves.quotientAlgEquivMulticross`.
Conversely `xy` is itself a nondegenerate binary quadratic form — the one with coefficients
`(0, 1, 0)`, of discriminant `-1` — so the multicross ring is a nondegenerate hypersurface over
any field, with no hypothesis on `k`.

## Main results

* `Stacks.Curves.nonempty_algEquiv_multicross_of_nondegenerate` — over an algebraically closed
  field, the hypersurface of a nondegenerate binary quadratic form is the two-branch multicross
  ring.
* `Stacks.Curves.nonempty_algEquiv_multicross_iff` — over an algebraically closed field, being
  a nondegenerate quadratic hypersurface and being the two-branch multicross ring are the same
  condition on a `k`-algebra.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
-/

@[expose] public noncomputable section

open MvPowerSeries

universe u v

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- The binary quadratic form with coefficients `(0, 1, 0)` is `xy`. -/
@[simp]
theorem nodalBinaryQuadratic_zero_one_zero :
    nodalBinaryQuadratic (0 : k) 1 0 = (X 0 : MvPowerSeries (Fin 2) k) * X 1 := by
  simp [nodalBinaryQuadratic]

/-- `xy` is a nondegenerate binary quadratic form: its discriminant is `-1`. -/
theorem nondegenerate_zero_one_zero : 4 * (0 : k) * 0 - (1 : k) ^ 2 ≠ 0 := by
  simp

/-- Over an algebraically closed field, the power-series hypersurface cut out by a
nondegenerate binary quadratic form is the two-branch multicross ring. -/
theorem nonempty_algEquiv_multicross_of_nondegenerate [IsAlgClosed k] (a b c : k)
    (h : 4 * a * c - b ^ 2 ≠ 0) :
    Nonempty ((MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic a b c}) ≃ₐ[k]
      ↥(multicross k 2)) :=
  (nonempty_quotient_nodalBinaryQuadratic_algEquiv a b c h).map fun e ↦
    e.trans quotientAlgEquivMulticross

/-- The two-branch multicross ring over any field is the power-series hypersurface cut out by a
nondegenerate binary quadratic form, namely `xy`. -/
theorem nonempty_algEquiv_multicross_quotient :
    Nonempty ((↥(multicross k 2)) ≃ₐ[k]
      MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic (0 : k) 1 0}) :=
  ⟨(quotientAlgEquivMulticross (k := k)).symm.trans
    (Ideal.quotientEquivAlgOfEq (I := Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1})
      (J := Ideal.span {nodalBinaryQuadratic (0 : k) 1 0}) k
      (by rw [nodalBinaryQuadratic_zero_one_zero]))⟩

/-- **Stacks Tag 0C4D, the step over an algebraically closed field.** For a `k`-algebra over an
algebraically closed field `k`, being a power-series hypersurface cut out by a nondegenerate
binary quadratic form is the same as being the two-branch multicross ring. The first condition
is the completed-local-ring description of a node used in Tag 0C49, the second the one used in
Tag 0C1W. -/
theorem nonempty_algEquiv_multicross_iff [IsAlgClosed k] (A : Type v) [CommRing A]
    [Algebra k A] :
    (∃ a b c : k, 4 * a * c - b ^ 2 ≠ 0 ∧
        Nonempty (A ≃ₐ[k]
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic a b c}))) ↔
      Nonempty (A ≃ₐ[k] ↥(multicross k 2)) := by
  constructor
  · rintro ⟨a, b, c, h, ⟨e⟩⟩
    exact (nonempty_algEquiv_multicross_of_nondegenerate a b c h).map e.trans
  · rintro ⟨e⟩
    exact ⟨0, 1, 0, nondegenerate_zero_one_zero,
      nonempty_algEquiv_multicross_quotient.map e.trans⟩

end Stacks.Curves

end
