module

public import StacksCore.Algebra.Split.DivisionRing
public import StacksCore.Algebra.Split.Embedding
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterisations of finite central simple algebras

Stacks tag 0753: for a `k`-algebra `A`, being finite central simple is equivalent to each of
five other conditions, four of them phrased through splitting fields. The equivalence is
`Algebra.isCentralSimple_tfae`.

The substance is the *descent* direction, `Algebra.IsSplit.finite_central_simple`: if some
field extension splits `A`, then `A` was finite central simple to begin with. Each of its
three conclusions comes from a different place, and only simplicity is routine:

* simplicity, from `IsSimpleRing.right_of_tensor`;
* centrality, from `Algebra.IsCentral.of_baseChange` — this is the one genuinely new
  ingredient, and it is why that lemma exists;
* finiteness, from `Module.rank_baseChange`. Note `Module.finrank_baseChange` is *not* usable
  here: `finrank` is `0` for an infinite-dimensional space, so it cannot distinguish the case
  being ruled out. The argument has to go through `Module.rank` and `Module.rank_lt_aleph0_iff`.

Two points where the Lean statement and the tag's prose differ, neither losing content:

* Clauses (1) and (2) are near-tautologous here. "Finite central simple" *is* the typeclass
  bundle `Module.Finite` + `Algebra.IsCentral` + `IsSimpleRing`, and (2) spells those out as
  `Subalgebra.center k A = ⊥` and `IsSimpleOrder (TwoSidedIdeal A)`. Stacks states both
  because it does not have the typeclasses; we keep both because the tag does.
* Clause (5) quantifies over `IntermediateField k k_bar` rather than an abstract finite Galois
  extension, and the whole list is stated relative to a chosen algebraic closure. A consumer
  holding an abstract splitting field routes through `Algebra.IsSplit.finite_central_simple`,
  which is stated for an arbitrary `L`.

The tag's closing sentence — "the integer `d` is called the degree of `A`" — asserts that the
`d` of clauses (3), (4) and (5) is one well-defined invariant. The `TFAE` does not say this,
since each clause quantifies its own witness, so it is recorded separately as
`Algebra.IsSplit.matrix_size_eq_degree`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Being finite central simple descends along *any* splitting field: if `L ⊗[k] A` is a
matrix algebra over `L`, then `A` is finite, central and simple over `k`.

This is the engine behind the (3) ⇒ (1), (4) ⇒ (1) and (5) ⇒ (1) directions of Stacks tag
0753, and unlike the clauses themselves it does not mention a chosen algebraic closure. -/
theorem Algebra.IsSplit.finite_central_simple (L : Type*) [Field L] [Algebra k L]
    (h : Algebra.IsSplit k A L) :
    Module.Finite k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hn)
  have hsimp : IsSimpleRing (L ⊗[k] A) :=
    .of_ringEquiv e.symm.toRingEquiv (IsSimpleRing.matrix (Fin n) L)
  -- `Algebra.IsCentral.of_algEquiv` is universe-monomorphic (`D D' : Type v`), so it cannot
  -- carry centrality from `Matrix (Fin n) (Fin n) L` to `L ⊗[k] A`; transport by hand.
  have hcent : Algebra.IsCentral L (L ⊗[k] A) := by
    have hM : Algebra.IsCentral L (Matrix (Fin n) (Fin n) L) := Algebra.IsCentral.matrix L L (Fin n)
    exact ⟨fun {x} hx => by
      obtain ⟨c, hc⟩ := hM.out ((MulEquivClass.apply_mem_center_iff e).mpr hx)
      exact ⟨c, by simpa using congr(e.symm $hc)⟩⟩
  have hfin : Module.Finite L (L ⊗[k] A) := Module.Finite.equiv e.symm.toLinearEquiv
  refine ⟨?_, Algebra.IsCentral.of_baseChange L, IsSimpleRing.right_of_tensor k L A⟩
  -- Finiteness must go through `rank`, not `finrank`; see the module docstring.
  rw [← Module.rank_lt_aleph0_iff]
  have hr := Module.rank_baseChange (R := L) (S := k) (M' := A)
  have h2 : Module.rank L (L ⊗[k] A) < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.2 hfin
  rw [hr] at h2
  simpa using h2

/-- **Stacks 0753**, closing sentence: the matrix size in *any* splitting of `A` is the degree
of `A`. This is what licenses calling it "the" integer `d` — clauses (3), (4) and (5) of
`Algebra.isCentralSimple_tfae` each quantify their own witness, and this identifies them all
with `Algebra.IsCentralSimple.degree k A`.

No central-simple hypotheses are needed: a splitting already forces `finrank k A = n * n`,
and `degree` is by definition `Nat.sqrt` of that. In the tag's setting `A` is of course
central simple, but the identification of the witness does not depend on it. -/
@[stacks 0753 "the integer d is called the degree of A"]
theorem Algebra.IsSplit.matrix_size_eq_degree (L : Type w) [Field L] [Algebra k L]
    {n : ℕ} (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    n = Algebra.IsCentralSimple.degree k A := by
  have h : Module.finrank k A = n * n := by
    rw [← Module.finrank_baseChange (R := L) (S := k) (M' := A), e.toLinearEquiv.finrank_eq]
    simp [Module.finrank_matrix]
  rw [Algebra.IsCentralSimple.degree, h, ← pow_two, Nat.sqrt_eq']

variable (k A)

/-- **Stacks 0753**: for a `k`-algebra `A` the following are equivalent.

1. `A` is a finite central simple `k`-algebra.
2. `A` is a finite-dimensional `k`-vector space, `k` is the centre of `A`, and `A` has no
   nontrivial two-sided ideal.
3. `A ⊗ k̄` is a matrix algebra over `k̄`.
4. `A ⊗ kˢᵉᵖ` is a matrix algebra over `kˢᵉᵖ`.
5. `A ⊗ k'` is a matrix algebra over `k'` for some finite Galois `k'/k`.
6. `A ≅ Mat(n, K)` for some `n ≥ 1` and some finite central division algebra `K` over `k`.

The proof is a star around (1): each of (2)–(6) is proved equivalent to (1) directly. The
forward directions are the splitting constructions of §11.08; the return directions
(3) ⇒ (1), (4) ⇒ (1), (5) ⇒ (1) all factor through
`Algebra.IsSplit.finite_central_simple`. -/
@[stacks 0753, sga "4½ Arcata 3.1.1"]
theorem Algebra.isCentralSimple_tfae (k_bar : Type w) [Field k_bar] [Algebra k k_bar]
    [IsAlgClosed k_bar] [Algebra.IsAlgebraic k k_bar] :
    [ Module.Finite k A ∧ Algebra.IsCentral k A ∧ IsSimpleRing A,
      Module.Finite k A ∧ Subalgebra.center k A = ⊥ ∧ IsSimpleOrder (TwoSidedIdeal A),
      Algebra.IsSplit k A k_bar,
      Algebra.IsSplit k A (separableClosure k k_bar),
      ∃ K : IntermediateField k k_bar, Module.Finite k K ∧ IsGalois k K ∧ Algebra.IsSplit k A K,
      ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra k D)
        (_ : Module.Finite k D) (_ : Algebra.IsCentral k D),
        Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) D) ].TFAE := by
  tfae_have 1 → 2 := fun ⟨h1, h2, h3⟩ => ⟨h1, h2.center_eq_bot, h3.simple⟩
  tfae_have 2 → 1 := fun ⟨h1, h2, h3⟩ => ⟨h1, ⟨h2.le⟩, ⟨h3⟩⟩
  tfae_have 1 → 3 := fun ⟨_, _, _⟩ => Algebra.IsSplit.of_isAlgClosed
  tfae_have 1 → 4 := fun ⟨_, _, _⟩ => by
    obtain ⟨K, _, _, hK⟩ := Algebra.IsCentralSimple.exists_finite_sep_split
      (k := k) (A := A) (k_bar := k_bar)
    let : Algebra K (separableClosure k k_bar) :=
      (IntermediateField.inclusion (le_separableClosure k k_bar K)).toRingHom.toAlgebra
    have : IsScalarTower k K (separableClosure k k_bar) := .of_algebraMap_eq fun _ => rfl
    exact hK.of_isScalarTower _
  tfae_have 1 → 5 := fun ⟨_, _, _⟩ =>
    Algebra.IsCentralSimple.exists_finite_galois_split
  tfae_have 1 → 6 := fun ⟨_, _, _⟩ => by
    have : IsArtinianRing A := IsArtinianRing.of_finite k A
    obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
    have : Algebra.IsCentral k D := .of_matrix (Fin n) (h := .of_algEquiv k _ _ e)
    exact ⟨n, hn, D, ‹_›, ‹_›, ‹_›, ‹_›, ⟨e⟩⟩
  tfae_have 3 → 1 := fun h => h.finite_central_simple _
  tfae_have 4 → 1 := fun h => h.finite_central_simple _
  tfae_have 5 → 1 := fun ⟨K, _, _, hK⟩ => hK.finite_central_simple _
  tfae_have 6 → 1 := fun ⟨n, _, D, _, _, _, _, ⟨e⟩⟩ => by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (NeZero.pos n)
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv, .of_algEquiv k _ _ e.symm,
      .of_ringEquiv e.symm.toRingEquiv (IsSimpleRing.matrix (Fin n) D)⟩
  tfae_finish
