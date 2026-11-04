module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.RootExtraction

/-!
# The Artin–Schreier algebra

For a finite field `k = 𝔽_q`, a `k`-algebra `A` and `g ∈ A`, the Artin–Schreier algebra
`A[T]/(T^q - T - g)` is finite (the polynomial is monic) and étale (its derivative is `-1`), and
`𝔽_q` acts on it by the translations `T ↦ T + a`.

## Main definitions

* `Stacks.ArtinSchreier.Ring`, `Stacks.ArtinSchreier.translate`.

## Main results

* `Stacks.ArtinSchreier.etale_ring`, `Stacks.ArtinSchreier.finite_ring`.
* `Stacks.ArtinSchreier.exists_algebraMap_eq_of_pow_card_eq`: the roots of `T^q - T` in a field
  containing `𝔽_q` are the elements of `𝔽_q`.
* `Stacks.ArtinSchreier.pow_card_pow_of_pow_card_eq`: iterating `t^q = t + c`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.ArtinSchreier

variable (k : Type*) [Field k] [Fintype k] {A : Type*} [CommRing A] [Algebra k A] (g : A)

/-- The Artin–Schreier polynomial `T^q - T - g` over a `𝔽_q`-algebra `A`. -/
public def poly : A[X] := X ^ Fintype.card k - (X + C g)

omit [Algebra k A] in
/-- The Artin–Schreier polynomial `T^q - T - g` is monic. -/
public theorem monic_poly : (poly k g).Monic :=
  monic_X_pow_sub (degree_X_add_C_lt g (Fintype.one_lt_card (α := k)))

/-- The cardinality of `𝔽_q` vanishes in an `𝔽_q`-algebra. -/
public theorem card_cast_eq_zero : (Fintype.card k : A) = 0 := by
  rw [← map_natCast (algebraMap k A), FiniteField.cast_card_eq_zero, map_zero]

/-- The derivative of `T^q - T - g` is `-1`, since `q = 0` in an `𝔽_q`-algebra. -/
public theorem derivative_poly : derivative (poly k g) = -1 := by
  have h : (C (Fintype.card k : A)) = 0 := by rw [card_cast_eq_zero, C_0]
  rw [poly, derivative_sub, derivative_X_pow, derivative_add, derivative_X, derivative_C,
    add_zero, h, zero_mul, zero_sub]

/-- The Artin–Schreier polynomial with the unit `1` is a standard étale pair. -/
public def standardEtalePair : StandardEtalePair A where
  f := poly k g
  monic_f := monic_poly k g
  g := 1
  cond := ⟨-1, 0, 0, by rw [derivative_poly]; ring⟩

/-- The Artin–Schreier algebra `A[T]/(T^q - T - g)`. -/
public abbrev Ring := AdjoinRoot (poly k g)

/-- The Artin–Schreier algebra is the standard étale algebra of `standardEtalePair`. -/
public def ringEquiv : (standardEtalePair k g).Ring ≃ₐ[A] Ring k g :=
  (standardEtalePair k g).equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnits (Ring k g) (Submonoid.powers (AdjoinRoot.mk (poly k g) (1 : A[X])))
      (S := Localization.Away (AdjoinRoot.mk (poly k g) (1 : A[X]))) (by
        rintro _ ⟨n, rfl⟩
        change IsUnit ((AdjoinRoot.mk (poly k g) (1 : A[X])) ^ n)
        rw [map_one, one_pow]
        exact isUnit_one)).symm.restrictScalars A)

/-- **The Artin–Schreier algebra is étale.** -/
public instance etale_ring : Algebra.Etale A (Ring k g) :=
  haveI := Algebra.IsStandardEtale.of_equiv (ringEquiv k g)
  inferInstance

/-- **The Artin–Schreier algebra is finite**, `T^q - T - g` being monic. -/
public instance finite_ring : Module.Finite A (Ring k g) :=
  (AdjoinRoot.powerBasis' (monic_poly k g)).finite

/-! ### The `q`-th power map -/

section Frobenius

variable {S : Type*} [CommRing S] [Algebra k S]

/-- **`x ↦ x ^ q` is additive on an `𝔽_q`-algebra.** -/
public theorem add_pow_card (x y : S) :
    (x + y) ^ Fintype.card k = x ^ Fintype.card k + y ^ Fintype.card k := by
  rcases subsingleton_or_nontrivial S with h | h
  · exact Subsingleton.elim _ _
  obtain ⟨n, hp, hn⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  have := charP_of_injective_algebraMap' k (A := S) (ringChar k)
  rw [hn]
  exact add_pow_char_pow x y (ringChar k) n

/-- Elements of `𝔽_q` are fixed by `x ↦ x ^ q` in any `𝔽_q`-algebra. -/
public theorem algebraMap_pow_card (a : k) :
    (algebraMap k S a) ^ Fintype.card k = algebraMap k S a := by
  rw [← map_pow, FiniteField.pow_card]

/-- **Iterating the Artin–Schreier relation**: if `t ^ q = t + c`, then
`t ^ (q ^ n) = t + ∑_{i < n} c ^ (q ^ i)`. -/
public theorem pow_card_pow_of_pow_card_eq {t c : S} (h : t ^ Fintype.card k = t + c) (n : ℕ) :
    t ^ (Fintype.card k ^ n) = t + ∑ i ∈ Finset.range n, c ^ (Fintype.card k ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ (m : ℕ) (z : S), (∑ i ∈ Finset.range m, z ^ (Fintype.card k ^ i)) ^
        Fintype.card k = ∑ i ∈ Finset.range m, z ^ (Fintype.card k ^ (i + 1)) := by
      intro m z
      induction m with
      | zero => simp [zero_pow (Fintype.card_ne_zero)]
      | succ m ihm =>
        rw [Finset.sum_range_succ, add_pow_card, ihm, Finset.sum_range_succ, ← pow_mul,
          pow_succ]
    rw [pow_succ, pow_mul, ih, add_pow_card, h, hsum, Finset.sum_range_succ',
      pow_zero, pow_one]
    ring

end Frobenius

/-- **The roots of `T^q - T` in a field containing `𝔽_q` are the elements of `𝔽_q`.** -/
public theorem exists_algebraMap_eq_of_pow_card_eq {L : Type*} [Field L] [Algebra k L] {d : L}
    (h : d ^ Fintype.card k = d) : ∃ a : k, algebraMap k L a = d := by
  classical
  by_contra hd
  push Not at hd
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  set P : L[X] := X ^ Fintype.card k - X
  have hdeg : P.natDegree = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroot : ∀ z : L, z ^ Fintype.card k = z → z ∈ P.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp [P, hz]
  have hsub : insert d (Finset.univ.image (algebraMap k L)) ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact hroot _ h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      exact hroot _ (algebraMap_pow_card k a)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact hd),
    Finset.card_image_of_injective _ (algebraMap k L).injective, Finset.card_univ] at h1
  have h2 := (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
  omega

/-! ### The translations `T ↦ T + a` -/

omit [Field k] [Algebra k A] in
/-- The root `T` of the Artin–Schreier polynomial satisfies `T ^ q = T + g`. -/
public theorem root_pow_card :
    (AdjoinRoot.root (poly k g)) ^ Fintype.card k =
      AdjoinRoot.root (poly k g) + algebraMap A (Ring k g) g := by
  have h := AdjoinRoot.eval₂_root (poly k g)
  rw [poly, eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

/-- **The translation `T ↦ T + a` by `a ∈ 𝔽_q`**, an `A`-algebra automorphism of the
Artin–Schreier algebra. -/
public def translate (a : k) : Ring k g →ₐ[A] Ring k g :=
  AdjoinRoot.liftAlgHom (poly k g) (Algebra.ofId A (Ring k g))
    (AdjoinRoot.root (poly k g) + algebraMap k (Ring k g) a) (by
      change eval₂ _ _ (X ^ Fintype.card k - (X + C g)) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X, eval₂_C, add_pow_card,
        algebraMap_pow_card, root_pow_card]
      change _ - (_ + algebraMap A (Ring k g) g) = 0
      ring)

/-- The translation by `a` sends the root `T` to `T + a`. -/
@[simp]
public theorem translate_root (a : k) :
    translate k g a (AdjoinRoot.root (poly k g)) =
      AdjoinRoot.root (poly k g) + algebraMap k (Ring k g) a :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The translation by `0` is the identity. -/
public theorem translate_zero : translate k g 0 = AlgHom.id A (Ring k g) := by
  apply AdjoinRoot.algHom_ext
  simp

/-- Translation is additive: translating by `a + b` is translating by `b`, then by `a`. -/
public theorem translate_add (a b : k) :
    translate k g (a + b) = (translate k g a).comp (translate k g b) := by
  apply AdjoinRoot.algHom_ext
  rw [translate_root, AlgHom.comp_apply, translate_root, map_add (translate k g a),
    translate_root,
    show translate k g a (algebraMap k (Ring k g) b) = algebraMap k (Ring k g) b from by
      rw [IsScalarTower.algebraMap_apply k A (Ring k g), AlgHom.commutes], map_add]
  ring

end Stacks.ArtinSchreier
