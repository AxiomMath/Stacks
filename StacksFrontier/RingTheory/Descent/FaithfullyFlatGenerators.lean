module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Descent of the number of generators along a faithfully flat ring map

Let `R → T` be faithfully flat and `M` an `R`-module.  If the base change `T ⊗_R M` is
spanned over `T` by a set `s`, then `M` is a quotient of a free `R`-module on an index set of
cardinality at most `max ℵ₀ #s`, and hence `#M ≤ max ℵ₀ (max #R #s)`.

Consequently, for a faithfully flat `R`-algebra `C` such that `C ⊗_R C` is spanned over `C` by a
family indexed by a ring `R'`, the spectrum `Spec C` is an object of every big fppf site
containing `Spec R` and `Spec R'`.

## Main results

* `Module.exists_finsupp_surjective_of_span_tensorProduct_eq_top`: a faithfully flat base change
  spanned by `s` gives a surjection `(ι →₀ R) → M` with `#ι ≤ max ℵ₀ #s`.
* `Module.mk_le_of_span_tensorProduct_eq_top`: then `#M ≤ max ℵ₀ (max #R #s)`.
* `AlgebraicGeometry.BigFppfSite.contains_spec_of_span_tensorProduct`: for a faithfully flat
  `R`-algebra `C` whose square `C ⊗_R C` is spanned over `C` by a family indexed by a ring `R'`,
  `Spec C` is an object of a big fppf site containing `Spec R` and `Spec R'`.
-/

@[expose] public section

open TensorProduct Cardinal

universe u v w

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (T : Type w) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

/-- **Generators descend along a faithfully flat ring map.**  If `T ⊗_R M` is spanned over `T`
by `s` and `T` is faithfully flat over `R`, then `M` is a quotient of a free `R`-module on an
index set of cardinality at most `max ℵ₀ #s`. -/
theorem exists_finsupp_surjective_of_span_tensorProduct_eq_top {s : Set (T ⊗[R] M)}
    (hs : Submodule.span T s = ⊤) :
    ∃ (ι : Type (max v w)) (f : (ι →₀ R) →ₗ[R] M),
      Function.Surjective f ∧ #ι ≤ max ℵ₀ #s := by
  choose k t m h using fun i : s ↦ TensorProduct.exists_sum_tmul_eq (i : T ⊗[R] M)
  let f₀ : ((Σ i : s, Fin (k i)) →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R fun p : Σ i : s, Fin (k i) ↦ m p.1 p.2
  refine ⟨Σ i : s, Fin (k i), f₀, ?_, ?_⟩
  · have hsurj : Function.Surjective (AlgebraTensorModule.lTensor T T f₀) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
      intro x hx
      refine ⟨∑ j : Fin (k ⟨x, hx⟩), t ⟨x, hx⟩ j ⊗ₜ Finsupp.single ⟨⟨x, hx⟩, j⟩ 1, ?_⟩
      simp only [map_sum, AlgebraTensorModule.lTensor_tmul, f₀, Finsupp.linearCombination_single,
        one_smul]
      exact (h ⟨x, hx⟩).symm
    rwa [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T]
  · rw [mk_sigma]
    refine (sum_le_sum _ (fun _ ↦ ℵ₀) fun _ ↦ by simp).trans ?_
    rw [sum_const, lift_aleph0, lift_uzero]
    exact (mul_le_max _ _).trans (max_le (max_le le_sup_right le_sup_left) le_sup_left)

end Module

namespace Module

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

/-- **Cardinality descends along a faithfully flat ring map.**  If `T ⊗_R M` is spanned over
`T` by `s` and `T` is faithfully flat over `R`, then `#M ≤ max ℵ₀ (max #R #s)`. -/
theorem mk_le_of_span_tensorProduct_eq_top {s : Set (T ⊗[R] M)}
    (hs : Submodule.span T s = ⊤) : #M ≤ max ℵ₀ (max #R #s) := by
  classical
  obtain ⟨ι, f, hf, hι⟩ := exists_finsupp_surjective_of_span_tensorProduct_eq_top T hs
  calc #M ≤ #(ι →₀ R) := mk_le_of_surjective hf
    _ ≤ #(Finset (ι × R)) := mk_le_of_injective (Finsupp.graph_injective ι R)
    _ ≤ max ℵ₀ #(ι × R) := (mk_le_of_surjective List.toFinset_surjective).trans (mk_list_le_max _)
    _ ≤ max ℵ₀ (max #R #s) := by
      rw [mk_prod, lift_id, lift_id]
      exact max_le le_sup_left ((mul_le_max _ _).trans (max_le (max_le
        (hι.trans (max_le le_sup_left (le_sup_right.trans' le_sup_right)))
        (le_sup_left.trans le_sup_right)) le_sup_left))

end Module

namespace AlgebraicGeometry.BigFppfSite

/-- **The spectrum of a faithfully flat algebra with a small square lies in the site.**  Let
`R → C` be faithfully flat with `Spec R` an object of the big fppf site `B`, and suppose
`C ⊗_R C` is spanned over `C` by the values of a family indexed by a ring `R'` with `Spec R'`
an object of `B`.  Then `Spec C` is an object of `B`. -/
theorem contains_spec_of_span_tensorProduct (B : BigFppfSite.{u}) {R C R' : Type u}
    [CommRing R] [CommRing C] [CommRing R'] [Algebra R C] [Module.FaithfullyFlat R C]
    (hR : B.Contains (Spec (CommRingCat.of R))) (hR' : B.Contains (Spec (CommRingCat.of R')))
    (v : R' → C ⊗[R] C) (hv : Submodule.span C (Set.range v) = ⊤) :
    B.Contains (Spec (CommRingCat.of C)) := by
  have hmk : ∀ A : Type u, [CommRing A] → B.Contains (Spec (CommRingCat.of A)) → #A < B.cutoff :=
    fun A _ hA ↦ (le_sup_right.trans (Scheme.size_Spec (CommRingCat.of A)).ge).trans_lt hA
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff
    ((Module.mk_le_of_span_tensorProduct_eq_top C hv).trans_lt
      (max_lt B.aleph0_lt_cutoff (max_lt (hmk R hR) ?_)))
  exact mk_range_le.trans_lt (hmk R' hR')

end AlgebraicGeometry.BigFppfSite

