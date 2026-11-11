module

public import StacksCore.Algebra.BrauerGroup.Basic
public import StacksCore.Algebra.Central.Matrix
public import StacksCore.RingTheory.SimpleModule.WedderburnArtin
import StacksCore.Tactic.StacksAttribute

/-!
# Similarity of finite central simple algebras

Let `k` be a field. Two finite central simple `k`-algebras `A` and `B` are *similar*
(`IsBrauerEquivalent A B`) if `Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B` for some
`n, m ≠ 0`. This file proves the three parts of Stacks Lemma 074K.

## Main results

* `IsBrauerEquivalent.equivalence_and_iff_of_algEquiv`: similarity is an equivalence relation
  on finite central simple `k`-algebras which only depends on their isomorphism classes, i.e. an
  equivalence relation on the set of isomorphism classes.
* `IsBrauerEquivalent.exists_divisionRing_unique`: every similarity class contains a finite
  central division algebra over `k`, unique up to isomorphism.
* `IsBrauerEquivalent.iff_nonempty_algEquiv_of_algEquiv_matrix`: if `A ≃ Mₙ(K)` and
  `B ≃ Mₘ(K')` with `K`, `K'` division algebras over `k`, then `A` and `B` are similar if and
  only if `K ≃ₐ[k] K'`.
-/

@[expose] public section

universe u v w

variable {k : Type u} [Field k]

namespace IsBrauerEquivalent

/-- Isomorphic finite central simple algebras are similar. -/
theorem of_algEquiv {A B : CSA.{u, v} k} (e : A ≃ₐ[k] B) : IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- **Stacks 074K (1).** Similarity is an equivalence relation on finite central simple
`k`-algebras, and whether `A` and `B` are similar depends only on the isomorphism classes of `A`
and `B`. Together these say that similarity is an equivalence relation on the set of isomorphism
classes of finite central simple `k`-algebras. -/
@[stacks 074K "part (1): similarity is an equivalence relation on the isomorphism classes of \
  finite central simple k-algebras (an equivalence on `CSA k` invariant under isomorphism)"]
theorem equivalence_and_iff_of_algEquiv :
    Equivalence (IsBrauerEquivalent (K := k)) ∧
      ∀ {A A' B B' : CSA.{u, v} k}, Nonempty (A ≃ₐ[k] A') → Nonempty (B ≃ₐ[k] B') →
        (IsBrauerEquivalent A B ↔ IsBrauerEquivalent A' B') :=
  ⟨is_eqv, fun ⟨eA⟩ ⟨eB⟩ =>
    ⟨fun h => ((of_algEquiv eA).symm.trans h).trans (of_algEquiv eB),
      fun h => ((of_algEquiv eA).trans h).trans (of_algEquiv eB).symm⟩⟩

/-- **Stacks 074K (3).** Let `A ≃ₐ[k] Mₙ(K)` and `B ≃ₐ[k] Mₘ(K')` be finite central simple
`k`-algebras presented as matrix algebras over division algebras `K` and `K'` over `k`. Then `A`
and `B` are similar if and only if `K ≃ₐ[k] K'`. The division algebras are automatically finite
and central over `k`, since `A` and `B` are, so no such hypothesis is needed on them. -/
@[stacks 074K "part (3): for A ≃ Mat(n × n, K) and B ≃ Mat(m × m, K') with K, K' skew fields \
  over k, A and B are similar iff K ≃ K' as k-algebras"]
theorem iff_nonempty_algEquiv_of_algEquiv_matrix {A B : CSA.{u, v} k}
    {K : Type w} [DivisionRing K] [Algebra k K] {K' : Type w} [DivisionRing K'] [Algebra k K']
    {n m : ℕ} [NeZero n] [NeZero m]
    (eA : A ≃ₐ[k] Matrix (Fin n) (Fin n) K) (eB : B ≃ₐ[k] Matrix (Fin m) (Fin m) K') :
    IsBrauerEquivalent A B ↔ Nonempty (K ≃ₐ[k] K') := by
  constructor
  · rintro ⟨p, q, hp, hq, ⟨e⟩⟩
    have : NeZero p := ⟨hp⟩
    have : NeZero q := ⟨hq⟩
    have : Module.Finite k (Matrix (Fin n) (Fin n) K) := .equiv eA.toLinearEquiv
    have : Module.Finite k K := Module.finite_of_matrix (Fin n) (Fin n)
    exact IsSimpleRing.wedderburn_artin_divisionring_unique k
      (Matrix (Fin (p * n)) (Fin (p * n)) K) AlgEquiv.refl <|
      (Matrix.compFinAlgEquiv p n K k).symm.trans <| eA.symm.mapMatrix.trans <| e.trans <|
        eB.mapMatrix.trans <| Matrix.compFinAlgEquiv q m K' k
  · rintro ⟨σ⟩
    exact ⟨m, n, NeZero.ne m, NeZero.ne n, ⟨eA.mapMatrix.trans <|
      (Matrix.compFinAlgEquiv m n K k).trans <| σ.mapMatrix.trans <|
        (Matrix.reindexAlgEquiv k K' (finCongr (Nat.mul_comm m n))).trans <|
          (Matrix.compFinAlgEquiv n m K' k).symm.trans eB.symm.mapMatrix⟩⟩

/-- **Stacks 074K (2).** Every similarity class of finite central simple `k`-algebras contains a
finite central division algebra `D` over `k`, and `D` is unique up to isomorphism: every finite
central division algebra over `k` similar to `A` is isomorphic to `D`. -/
@[stacks 074K "part (2): every similarity class contains a finite central skew field over k, \
  unique up to isomorphism"]
theorem exists_divisionRing_unique (A : CSA.{u, v} k) :
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D) (_ : Algebra.IsCentral k D)
      (_ : FiniteDimensional k D), IsBrauerEquivalent A ⟨.of k D⟩ ∧
        ∀ (D' : Type v) [DivisionRing D'] [Algebra k D'] [Algebra.IsCentral k D']
          [FiniteDimensional k D'], IsBrauerEquivalent A ⟨.of k D'⟩ → Nonempty (D ≃ₐ[k] D') := by
  have : IsArtinianRing A := .of_finite k A
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  have : Algebra.IsCentral k D := .of_matrix (Fin n) (h := .of_algEquiv k _ _ e)
  let e₁ (E : Type v) [DivisionRing E] [Algebra k E] : E ≃ₐ[k] Matrix (Fin 1) (Fin 1) E :=
    { toFun := Matrix.scalar (Fin 1)
      invFun M := M 0 0
      left_inv x := by simp
      right_inv M := by ext i j; fin_cases i; fin_cases j; simp
      map_mul' := map_mul _
      map_add' := map_add _
      commutes' r := by ext i j; fin_cases i; fin_cases j; simp [Matrix.algebraMap_matrix_apply] }
  refine ⟨D, _, _, this, inferInstance, ?_, fun D' _ _ _ _ h => ?_⟩
  · exact (iff_nonempty_algEquiv_of_algEquiv_matrix (B := ⟨.of k D⟩) e (e₁ D)).2 ⟨AlgEquiv.refl⟩
  · exact (iff_nonempty_algEquiv_of_algEquiv_matrix (B := ⟨.of k D'⟩) e (e₁ D')).1 h

end IsBrauerEquivalent
