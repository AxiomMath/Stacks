module

public import Mathlib.RingTheory.Derivation.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Obstructions to the existence of a weak solution

Lemmas on ramification indices of extensions of discrete valuation rings, on powers landing in
subfields, on algebraic extensions of bounded degree and on derivations in characteristic `p`,
together with an arithmetic contradiction combining the resulting bounds.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_mul_ramificationIdx`: for an
  extension of discrete valuation rings, the `B`-valuation of the image of a nonzero element of
  `A` is a multiple of the ramification index.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_dvd_of_forall_pow_mem_range`: if
  every `q`-th power in `L` lies in `K`, then the ramification index of `B` over `A` divides `q`.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_le_of_forall_pow_mem_range`: under
  the same hypothesis, the ramification index is at most `q`.
* `Subfield.pow_max_mem_of_inf_eq`: if the `p ^ n₁`-th powers of a set lie in `Q₁` and its
  `p ^ n₂`-th powers lie in `Q₂`, then its `p ^ max n₁ n₂`-th powers lie in `Q₁ ⊓ Q₂`.
* `IntermediateField.finiteDimensional_and_finrank_le_of_forall_adjoin_finrank_le`: an algebraic
  extension whose finitely generated subextensions have degree at most `N` is finite of degree at
  most `N`.
* `Derivation.not_isPow_of_apply_ne_zero`: in characteristic `p`, an element on which some
  derivation does not vanish is not a `p`-th power.
* `Stacks.WeakSolution.Obstruction.false_of_ramificationIdx_bookkeeping`: the identities
  `δ * p ^ nᵢ = d`, the bound `d ≤ p ^ n`, `2 ≤ δ` and `max n₁ n₂ = n` are contradictory.

## References

* [The Stacks Project, Tag 09ET](https://stacks.math.columbia.edu/tag/09ET)
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.Ramification

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]

/-- For an extension of discrete valuation rings `A → B` and a nonzero `a : A`, the `B`-valuation
of the image of `a` is a multiple of the ramification index of `B` over `A`. -/
theorem addVal_algebraMap_eq_mul_ramificationIdx (a : A) (ha : a ≠ 0) :
    ∃ k : ℕ, IsDiscreteValuationRing.addVal B (algebraMap A B a)
      = ((k * ramificationIdx A B : ℕ) : ℕ∞) := by
  obtain ⟨πA, hπAprime⟩ := IsDiscreteValuationRing.exists_prime A
  have hπA : Irreducible πA := hπAprime.irreducible
  have hval : IsDiscreteValuationRing.addVal B (algebraMap A B πA)
      = (ramificationIdx A B : ℕ∞) := addVal_algebraMap_eq_ramificationIdx A B πA hπA
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπA
  refine ⟨k, ?_⟩
  obtain ⟨w, hw⟩ := (u.isUnit).map (algebraMap A B)
  rw [hk, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, ← hw,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, hval]
  simp [nsmul_eq_mul]

variable (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
  [IsScalarTower A K L]

/-- If every `q`-th power of an element of `L` already lies in (the image of) `K`, then the
ramification index of `B` over `A` divides `q`. -/
theorem ramificationIdx_dvd_of_forall_pow_mem_range {q : ℕ} (hq : q ≠ 0)
    (h : ∀ x : L, x ^ q ∈ (algebraMap K L).range) : ramificationIdx A B ∣ q := by
  obtain ⟨πB, hπBprime⟩ := IsDiscreteValuationRing.exists_prime B
  have hπB : Irreducible πB := hπBprime.irreducible
  set E := ramificationIdx A B with hE
  have hinjBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hfne : ∀ a : A, a ≠ 0 → algebraMap A B a ≠ 0 := fun a =>
    (map_ne_zero_iff _ hinjAB).2
  obtain ⟨c, hc⟩ := h (algebraMap B L πB)
  obtain ⟨a₁, a₂, ha₂mem, hdiv⟩ := IsFractionRing.div_surjective (A := A) c
  have ha₂ne : a₂ ≠ 0 := nonZeroDivisors.ne_zero ha₂mem
  have htowerAKL : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap A L x := fun x => by
    rw [← IsScalarTower.algebraMap_apply A K L]
  have htowerABL : ∀ x : A, algebraMap A L x = algebraMap B L (algebraMap A B x) := fun x => by
    rw [IsScalarTower.algebraMap_apply A B L]
  have ha₂L : algebraMap A L a₂ ≠ 0 := by
    rw [htowerABL]
    exact (map_ne_zero_iff _ hinjBL).2 (hfne a₂ ha₂ne)
  have hclc : algebraMap K L c = algebraMap A L a₁ / algebraMap A L a₂ := by
    rw [← hdiv, map_div₀, htowerAKL, htowerAKL]
  have hkey : algebraMap A L a₁ / algebraMap A L a₂ = algebraMap B L (πB ^ q) := by
    rw [← hclc, hc, map_pow]
  have hcross : algebraMap A L a₁ = algebraMap B L (πB ^ q) * algebraMap A L a₂ := by
    field_simp at hkey
    linear_combination hkey
  rw [htowerABL, htowerABL, ← map_mul] at hcross
  have hBeq : algebraMap A B a₁ = πB ^ q * algebraMap A B a₂ := hinjBL hcross
  have ha₁ne : a₁ ≠ 0 := by
    rintro rfl
    simp [hq, hπB.ne_zero, hfne a₂ ha₂ne] at hBeq
  have hvalEq : IsDiscreteValuationRing.addVal B (algebraMap A B a₁)
      = (q : ℕ∞) + IsDiscreteValuationRing.addVal B (algebraMap A B a₂) := by
    rw [hBeq, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hπB, nsmul_eq_mul, mul_one]
  obtain ⟨k₁, hk₁⟩ := addVal_algebraMap_eq_mul_ramificationIdx A B a₁ ha₁ne
  obtain ⟨k₂, hk₂⟩ := addVal_algebraMap_eq_mul_ramificationIdx A B a₂ ha₂ne
  rw [hk₁, hk₂] at hvalEq
  have hnat : k₁ * E = q + k₂ * E := by exact_mod_cast hvalEq
  exact ⟨k₁ - k₂, by rw [Nat.mul_sub, Nat.mul_comm E k₁, Nat.mul_comm E k₂]; omega⟩

/-- The sharp ramification bound: if every `q`-th power of `L` lies in `K`, then the ramification
index of `B` over `A` is at most `q`. -/
theorem ramificationIdx_le_of_forall_pow_mem_range {q : ℕ} (hq : q ≠ 0)
    (h : ∀ x : L, x ^ q ∈ (algebraMap K L).range) : ramificationIdx A B ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hq)
    (ramificationIdx_dvd_of_forall_pow_mem_range A B K L hq h)

end Stacks.DiscreteValuationRing.Ramification

namespace Subfield

/-- If the `p ^ n₁`-th powers of a set `U` lie in `Q₁` and its `p ^ n₂`-th powers lie in `Q₂`,
then its `p ^ max n₁ n₂`-th powers lie in `Q₁ ⊓ Q₂`. -/
theorem pow_max_mem_of_inf_eq {Ω : Type*} [Field Ω] {S Q₁ Q₂ : Subfield Ω} (hQ : Q₁ ⊓ Q₂ = S)
    {U : Set Ω} {p n₁ n₂ : ℕ} (h₁ : ∀ x ∈ U, x ^ p ^ n₁ ∈ Q₁)
    (h₂ : ∀ x ∈ U, x ^ p ^ n₂ ∈ Q₂) : ∀ x ∈ U, x ^ p ^ max n₁ n₂ ∈ S := by
  have key : ∀ (m : ℕ) (Q : Subfield Ω) (x : Ω), m ≤ max n₁ n₂ → x ^ p ^ m ∈ Q →
      x ^ p ^ max n₁ n₂ ∈ Q := by
    intro m Q x hm hmem
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk, pow_add, pow_mul]
    exact pow_mem hmem _
  intro x hx
  rw [← hQ]
  exact ⟨key n₁ Q₁ x (le_max_left _ _) (h₁ x hx), key n₂ Q₂ x (le_max_right _ _) (h₂ x hx)⟩

end Subfield

namespace IntermediateField

/-- An algebraic extension all of whose finitely generated subextensions have degree at most `N`
is itself finite, of degree at most `N`. -/
theorem finiteDimensional_and_finrank_le_of_forall_adjoin_finrank_le {F E : Type*} [Field F]
    [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] {N : ℕ}
    (h : ∀ s : Finset E, Module.finrank F (adjoin F (s : Set E)) ≤ N) :
    FiniteDimensional F E ∧ Module.finrank F E ≤ N := by
  classical
  set J : Finset E → IntermediateField F E := fun s => adjoin F (s : Set E) with hJ
  have hfd : ∀ s, FiniteDimensional F (J s) := fun s =>
    finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  set T : Set ℕ := Set.range (fun s : Finset E => Module.finrank F (J s)) with hT
  have hTne : T.Nonempty := ⟨_, ⟨∅, rfl⟩⟩
  have hTbdd : BddAbove T := ⟨N, by rintro m ⟨s, rfl⟩; exact h s⟩
  obtain ⟨s₀, hs₀⟩ := Nat.sSup_mem hTne hTbdd
  simp only at hs₀
  have hall : ∀ x : E, x ∈ J s₀ := by
    intro x
    have hmono : J s₀ ≤ J (insert x s₀) :=
      adjoin.mono F _ _ (by simp [Finset.coe_insert, Set.subset_insert])
    have := hfd (insert x s₀)
    have hub : Module.finrank F (J (insert x s₀)) ≤ sSup T :=
      le_csSup hTbdd ⟨insert x s₀, rfl⟩
    have hge : Module.finrank F (J s₀) ≤ Module.finrank F (J (insert x s₀)) :=
      Submodule.finrank_mono (show (J s₀).toSubmodule ≤ (J (insert x s₀)).toSubmodule from hmono)
    have heq : Module.finrank F (J s₀) = Module.finrank F (J (insert x s₀)) := by omega
    rw [eq_of_le_of_finrank_eq hmono heq]
    exact subset_adjoin F _ (by simp)
  have htop : J s₀ = ⊤ := eq_top_iff.mpr fun x _ => hall x
  have htopfd : FiniteDimensional F (⊤ : IntermediateField F E) := htop ▸ hfd s₀
  have hEfd : FiniteDimensional F E :=
    LinearEquiv.finiteDimensional (topEquiv (F := F) (E := E)).toLinearEquiv
  refine ⟨hEfd, ?_⟩
  rw [← finrank_top', ← htop]
  exact h s₀

end IntermediateField

namespace Derivation

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (p : ℕ) [CharP K p]

/-- In characteristic `p`, a derivation kills `p`-th powers: `D (y ^ p) = 0`. -/
@[ega "0 21.1.5" "(i)"]
theorem map_pow_charP_eq_zero (D : Derivation R K K) (y : K) : D (y ^ p) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

/-- If some derivation does not vanish at `x`, then `x` is not a `p`-th power. -/
theorem not_isPow_of_apply_ne_zero (D : Derivation R K K) {x : K} (hx : D x ≠ 0) (y : K) :
    y ^ p ≠ x := fun hy => hx (hy ▸ map_pow_charP_eq_zero p D y)

end Derivation

namespace Stacks.WeakSolution.Obstruction

/-- If `0 < p`, `2 ≤ δ`, `d ≤ p ^ n`, `max n₁ n₂ = n` and `δ * p ^ n₁ = d = δ * p ^ n₂`, then
`False`. -/
theorem false_of_ramificationIdx_bookkeeping {p δ d n n₁ n₂ : ℕ} (hp : 0 < p) (hδ : 2 ≤ δ)
    (hd : d ≤ p ^ n) (hmax : max n₁ n₂ = n) (h₁ : δ * p ^ n₁ = d) (h₂ : δ * p ^ n₂ = d) :
    False := by
  have hpn : 0 < p ^ n := pow_pos hp n
  have : 2 * p ^ n ≤ δ * p ^ n := Nat.mul_le_mul_right _ hδ
  rcases max_choice n₁ n₂ with h | h <;> rw [h] at hmax <;> subst hmax <;> omega

end Stacks.WeakSolution.Obstruction
