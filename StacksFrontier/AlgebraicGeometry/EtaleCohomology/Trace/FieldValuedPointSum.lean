module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount

/-!
# Sums over the points of a scheme with values in a finite extension

Let `k` be a finite field, `X` a quasi-compact scheme locally of finite type over `k`, and `K` an
extension of `k` of degree `n`. A `K`-valued point of `X` is a closed point `x` of degree dividing
`n` together with one of the `deg x` embeddings `κ(x) → K`. Hence for any function `F` on the
points of `X`,

`∑_{y ∈ X(K)} F(y) = ∑_{x ∈ |X|, deg x ∣ n} deg x · F(x)`,

where `F(y)` means `F` at the image of `y`. This regroups the local terms of the trace formula
over `k_n` by closed points, the passage from the traces of the powers of Frobenius to the Euler
product in [Stacks, Tag 03UZ].

## Main results

* `Stacks.EtaleCohomology.finsum_fieldValuedPoints_eq_sum`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [Finite K] [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]

/-- **Regrouping a sum over `X(K)` by closed points.** For a function `F` on the points of `X`
with values in an additive commutative monoid,
`∑_{y ∈ X(K)} F(y) = ∑_{x ∈ |X|, deg x ∣ [K : k]} deg x · F(x)`. -/
theorem finsum_fieldValuedPoints_eq_sum {M : Type*} [AddCommMonoid M] (F : X → M) :
    ∑ᶠ y : fieldValuedPoints f K, F (fieldValuedPointsEquiv f K y).1 =
      ∑ x ∈ (closedPointsDegreeLE f (Module.finrank k K)).filter
        (fun x => residueDegree f x.1 ∣ Module.finrank k K), residueDegree f x.1 • F x.1 := by
  classical
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  set S := (closedPointsDegreeLE f (Module.finrank k K)).filter
    (fun x => residueDegree f x.1 ∣ Module.finrank k K)
  have hmem : ∀ (x : X) (σ : residueEmbeddings f K x),
      ∃ h : IsClosed ({x} : Set X), (⟨x, h⟩ : closedPoints X) ∈ S := by
    intro x σ
    obtain ⟨hc, hd⟩ := isClosed_and_dvd_of_residueEmbeddings f K x σ
    refine ⟨hc, Finset.mem_filter.2 ⟨?_, hd⟩⟩
    simp only [closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact Nat.le_of_dvd hpos hd
  let e : (Σ x : X, residueEmbeddings f K x) ≃ Σ y : S, residueEmbeddings f K y.1.1 :=
    { toFun := fun c => ⟨⟨⟨c.1, (hmem c.1 c.2).1⟩, (hmem c.1 c.2).2⟩, c.2⟩
      invFun := fun c => ⟨c.1.1.1, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard (y : S) : Nat.card (residueEmbeddings f K y.1.1) = residueDegree f y.1.1 := by
    rw [natCard_residueEmbeddings, ite_eq_left (Finset.mem_filter.1 y.2).2]
  let : ∀ y : S, Fintype (residueEmbeddings f K y.1.1) := fun y =>
    have := Nat.finite_of_card_ne_zero
      ((hcard y).symm ▸ (residueDegree_pos f y.1.1 y.1.2).ne')
    Fintype.ofFinite _
  let e' := (fieldValuedPointsEquiv f K).trans e
  rw [← finsum_comp_equiv e'.symm]
  have hpt : ∀ c : Σ y : S, residueEmbeddings f K y.1.1,
      (fieldValuedPointsEquiv f K (e'.symm c)).1 = c.1.1.1 := fun c => by
    simp [e', e]
  simp only [hpt]
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun y _ => ?_
  show ∑ _σ : residueEmbeddings f K y.1.1, F y.1.1 = _
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]

end Stacks.EtaleCohomology
