module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.SetTheory.Cardinal.Order
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.SplittingAlgebra

/-!
# The cardinality of the ind-étale splitting construction

For a commutative ring `A`, the underlying set of `T(A)` has cardinality at most any infinite
cardinal bounding the cardinality of `A`, and so does the colimit of `A → T(A) → T²(A) → ⋯`.

The bound for `T(A)` comes from its presentation: a standard étale presentation over `A` is a
number of variables together with that many polynomials, so there are at most `k` of them when
`ℵ₀ ≤ k` and `#A ≤ k`; the variables of `T(A)` are indexed by a presentation together with one of
its variables, so there are at most `k` of those as well, and a quotient of a polynomial ring in
at most `k` variables over `A` has at most `k` elements. The bound for the colimit follows because
a sequential colimit of rings is the quotient of the disjoint union of its stages.

## Main results

* `AlgebraicGeometry.ProEtale.mk_splittingAlgebra_le`
* `AlgebraicGeometry.ProEtale.mk_iteratedSplittingColimit_le`

## References

* [Stacks Project, Tag 097S](https://stacks.math.columbia.edu/tag/097S)
-/

open Cardinal CategoryTheory CategoryTheory.Limits

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u

/-- The raw data underlying a standard étale presentation over `A`: a number of variables
together with that many polynomials in them. -/
private def presentationData (A : Type u) [CommRing A] :=
  Σ n : ℕ, Fin n → MvPolynomial (Fin n) A

/-- A sigma type over `ℕ` has at most `k` elements if `k` is infinite and bounds every fibre. -/
private lemma mk_sigma_nat_le (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) {f : ℕ → Type u}
    (h : ∀ n, Cardinal.mk (f n) ≤ k) : Cardinal.mk (Σ n, f n) ≤ k := by
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ ↦ Cardinal.mk (f n)) ≤
        Cardinal.lift #(ℕ) * ⨆ n : ℕ, Cardinal.mk (f n) := Cardinal.sum_le_lift_mk_mul_iSup _
    _ ≤ k * k := by
      rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
      exact mul_le_mul hk (ciSup_le' h) zero_le zero_le
    _ = k := Cardinal.mul_eq_self hk

/-- There are at most `k` standard étale presentations over `A`, for every infinite cardinal `k`
bounding the cardinality of `A`. -/
private lemma presentations_mk_le (A : Type u) [CommRing A]
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) :
    Cardinal.mk (StandardEtalePresentation A) ≤ k := by
  let encode : StandardEtalePresentation A → presentationData A :=
    fun p ↦ ⟨p.variableCount, p.relations⟩
  have hencode : Function.Injective encode := by
    rintro ⟨np, fp, hp, hf⟩ ⟨nq, fq, hq, hfq⟩ h
    simp only [encode, presentationData, Sigma.mk.injEq] at h
    cases h.1
    cases h.2
    rfl
  have hpoly (n : ℕ) : Cardinal.mk (MvPolynomial (Fin n) A) ≤ k := by
    calc
      Cardinal.mk (MvPolynomial (Fin n) A) ≤
          Cardinal.mk A ⊔ Cardinal.lift #(Fin n) ⊔ ℵ₀ :=
        by simpa only [Cardinal.lift_id'] using
          (MvPolynomial.cardinalMk_le_max_lift (σ := Fin n) (R := A))
      _ ≤ k := sup_le (sup_le hA
        ((Cardinal.lift_mk_fin n).trans_le (Cardinal.natCast_le_aleph0.trans hk))) hk
  have hfun (n : ℕ) : Cardinal.mk (Fin n → MvPolynomial (Fin n) A) ≤ k := by
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id', Cardinal.lift_mk_fin]
    exact (Cardinal.power_le_power_right (hpoly n)).trans (Cardinal.power_nat_le hk)
  have hdata : Cardinal.mk (presentationData A) ≤ k := mk_sigma_nat_le k hk hfun
  exact (Cardinal.mk_le_of_injective hencode).trans hdata

/-- There are at most `k` variables of `T(A)`, for every infinite cardinal `k` bounding the
cardinality of `A`. -/
private lemma splittingVariables_mk_le (A : Type u) [CommRing A]
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) :
    Cardinal.mk (Σ p : StandardEtalePresentation A, Fin p.variableCount) ≤ k := by
  let encode : (Σ p : StandardEtalePresentation A, Fin p.variableCount) →
      StandardEtalePresentation A × ℕ := fun x ↦ (x.1, x.2.val)
  have hencode : Function.Injective encode := by
    rintro ⟨p, i⟩ ⟨q, j⟩ h
    simp only [encode, Prod.mk.injEq] at h
    cases h.1
    cases Fin.ext h.2
    rfl
  calc
    Cardinal.mk (Σ p : StandardEtalePresentation A, Fin p.variableCount) ≤
        Cardinal.mk (StandardEtalePresentation A × ℕ) := Cardinal.mk_le_of_injective hencode
    _ = Cardinal.mk (StandardEtalePresentation A) * Cardinal.lift #(ℕ) := by simp
    _ ≤ k * k := by
      rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
      exact mul_le_mul (presentations_mk_le A k hk hA) hk zero_le zero_le
    _ = k := Cardinal.mul_eq_self hk

/-- The cardinality of `T(A)` is at most every infinite cardinal which bounds the cardinality
of `A`. -/
@[stacks 097S "the bound on T(A)"]
theorem mk_splittingAlgebra_le (A : Type u) [CommRing A]
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) :
    Cardinal.mk (splittingAlgebra A) ≤ k := by
  unfold splittingAlgebra
  exact (Cardinal.mk_quotient_le).trans <|
    (MvPolynomial.cardinalMk_le_max.trans <|
      sup_le (sup_le hA (splittingVariables_mk_le A k hk hA)) hk)

/-- Every stage of the sequence `A, T(A), T²(A), …` obeys the cardinality bound of its base. -/
private lemma iteratedSplittingRing_mk_le (A : CommRingCat.{u})
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) (n : ℕ) :
    Cardinal.mk (iteratedSplittingRing A n) ≤ k := by
  induction n with
  | zero => simpa [iteratedSplittingRing] using hA
  | succ n ih =>
    simpa [iteratedSplittingRing, splittingRing] using
      (mk_splittingAlgebra_le (iteratedSplittingRing A n) k hk ih)

/-- The colimit ring obtained by iterating `T` has the same cardinality bound as the ring it is
built from. -/
@[stacks 097S "the bound on the iterated construction"]
theorem mk_iteratedSplittingColimit_le (A : CommRingCat.{u})
    (k : Cardinal.{u}) (hk : ℵ₀ ≤ k) (hA : Cardinal.mk A ≤ k) :
    Cardinal.mk (iteratedSplittingColimit A) ≤ k := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits.{u, u} _
  let D := iteratedSplittingDiagram A
  have hf : Function.Surjective fun x : Σ n : ℕ, iteratedSplittingRing A n ↦
      (colimit.ι D x.1 x.2 : iteratedSplittingColimit A) := fun x ↦ by
    obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit D)) x
    exact ⟨⟨n, y⟩, hy⟩
  exact (Cardinal.mk_le_of_surjective hf).trans
    (mk_sigma_nat_le k hk (iteratedSplittingRing_mk_le A k hk hA))

end AlgebraicGeometry.ProEtale

end
