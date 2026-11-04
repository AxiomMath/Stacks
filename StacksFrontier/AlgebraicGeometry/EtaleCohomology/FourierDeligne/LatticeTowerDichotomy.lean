module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SpanLatticeBound
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Towers of stable submodules of `(O/ℓⁿ⁺¹)ᵐ`: bounded below or eventually invisible

Let `O` be a commutative ring, `ℓ ∈ O` with `O` precomplete for the `ℓ`-adic topology and every
`O/ℓⁿ⁺¹` finite, and `S₀` a set of `m × m` matrices over `O`. Suppose every `S₀`-stable submodule
of `Oᵐ` is zero or contains `ℓᶜ Oᵐ` for some `c`; for `O` a domain with fraction field `E` this
follows from the irreducibility of `S₀` acting on `Eᵐ`
(`Stacks.EtaleCohomology.eq_bot_or_exists_pow_smul_mem_of_irreducible`).

Let `Aₙ ⊆ (O/ℓⁿ⁺¹)ᵐ` be `S₀`-stable submodules with `Aₙ₊₁` reducing into `Aₙ`. Then either all
`Aₙ` contain `ℓᶜ (O/ℓⁿ⁺¹)ᵐ` for one `c`, or the image of `Aₙ₊ₖ` in `(O/ℓⁿ⁺¹)ᵐ` vanishes for `k`
large depending on `n` (`Stacks.EtaleCohomology.lattice_tower_dichotomy`). Indeed, if some level
`n₀` keeps seeing nonzero images from every higher level, König's lemma for the finite sets of
elements of `A_{n₀+k}` with nonzero image produces a compatible family, whose limit in `Oᵐ` is a
nonzero element of the `S₀`-stable submodule `{v | v mod ℓⁿ⁺¹ ∈ Aₙ for all n}`.
-/

@[expose] public noncomputable section

open Matrix CategoryTheory Opposite

namespace Stacks.EtaleCohomology

section Irreducible

variable {O : Type*} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A stable lattice of an irreducible representation is zero or of finite index**: for `S₀`
acting irreducibly on `ι → E`, a nonzero `S₀`-stable `O`-submodule of `ι → O` contains
`ℓᶜ • (ι → O)` for some `c`, provided every nonzero element of `O` divides a power of `ℓ` (as in a
discrete valuation ring with `ℓ` in the maximal ideal,
`Stacks.EtaleCohomology.exists_dvd_pow_of_ne_zero`). -/
theorem eq_bot_or_exists_pow_smul_mem_of_irreducible {ℓ : O}
    (hℓ : ∀ d : O, d ≠ 0 → ∃ c : ℕ, d ∣ ℓ ^ c) (S₀ : Set (Matrix ι ι O))
    (hirr : ∀ W : Submodule E (ι → E), (∀ M ∈ S₀, ∀ v ∈ W, M.map (algebraMap O E) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (N : Submodule O (ι → O)) (hN : ∀ M ∈ S₀, ∀ v ∈ N, M *ᵥ v ∈ N) :
    N = ⊥ ∨ ∃ c : ℕ, ∀ v : ι → O, ℓ ^ c • v ∈ N := by
  classical
  let W : Submodule E (ι → E) :=
    Submodule.span E ((fun v : ι → O => algebraMap O E ∘ v) '' N)
  have hW : ∀ M ∈ S₀, ∀ v ∈ W, M.map (algebraMap O E) *ᵥ v ∈ W := by
    intro M hM v hv
    have hle : W ≤ W.comap (Matrix.toLin' (M.map (algebraMap O E))) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      refine Submodule.subset_span ⟨M *ᵥ w, hN M hM w hw, ?_⟩
      ext i
      simp only [Function.comp_apply, Matrix.toLin'_apply]
      exact RingHom.map_mulVec _ _ _ i
    simpa [Matrix.toLin'_apply] using hle hv
  rcases hirr W hW with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => funext fun i => ?_
    have : algebraMap O E ∘ v ∈ W := Submodule.subset_span ⟨v, hv, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact IsFractionRing.injective O E (by simpa using congrFun this i)
  · right
    obtain ⟨d, hd, hdN⟩ := exists_ne_zero_smul_mem_of_span_eq_top E N h
    obtain ⟨c, e, he⟩ := hℓ d hd
    refine ⟨c, fun v => ?_⟩
    rw [he, mul_smul]
    exact hdN _

omit [Fintype ι] [DecidableEq ι] in
/-- In a discrete valuation ring, every nonzero element divides a power of a nonunit `ℓ`. -/
theorem exists_dvd_pow_of_ne_zero [IsDiscreteValuationRing O] {ℓ : O} (hℓ : ¬IsUnit ℓ)
    (d : O) (hd : d ≠ 0) : ∃ c : ℕ, d ∣ ℓ ^ c := by
  by_cases hℓ0 : ℓ = 0
  · exact ⟨1, by simp [hℓ0]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨b, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
  have hb : b ≠ 0 := by
    rintro rfl
    exact hℓ (by simp)
  refine ⟨a, ?_⟩
  rw [mul_pow, ← pow_mul]
  exact (Units.isUnit u).mul_left_dvd.2
    ((pow_dvd_pow ϖ (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb))).mul_left _)

end Irreducible

section Tower

variable {O : Type*} [CommRing O] (ℓ : O) {ι : Type*} [Fintype ι]

/-- `ℓⁿ'⁺¹ O ⊆ ℓⁿ⁺¹ O` for `n ≤ n'`: the ideals defining the reduction maps of the tower. -/
theorem span_pow_succ_le_span_pow_succ {n n' : ℕ} (h : n ≤ n') :
    Ideal.span {ℓ ^ (n' + 1)} ≤ Ideal.span {ℓ ^ (n + 1)} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ℓ (by omega))

omit [Fintype ι] in
/-- Membership of the reductions: a family `Aₙ` with `Aₙ₊₁` reducing into `Aₙ` has `Aₙ'` reducing
into `Aₙ` for every `n ≤ n'`. -/
private theorem reduce_mem_of_le (A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)})
      (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)}))
    (hA : ∀ n, ∀ v ∈ A (n + 1),
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_succ n)) ∘ v ∈ A n)
    {n n' : ℕ} (h : n ≤ n') {v : ι → O ⧸ Ideal.span {ℓ ^ (n' + 1)}} (hv : v ∈ A n') :
    Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ h) ∘ v ∈ A n := by
  induction n', h using Nat.le_induction with
  | base => simpa using hv
  | succ n' hn ih =>
    convert ih (hA n' v hv) using 1
    ext i
    simp

/-- The `O`-submodule of `ι → O` of the vectors whose reduction mod `ℓⁿ⁺¹` lies in `Aₙ` for
every `n`. -/
def towerLimitSubmodule (A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)})
      (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)})) : Submodule O (ι → O) where
  carrier := {v | ∀ n, Ideal.Quotient.mk (Ideal.span {ℓ ^ (n + 1)}) ∘ v ∈ A n}
  add_mem' := fun {v w} hv hw n => by
    convert (A n).add_mem (hv n) (hw n) using 1
    ext i
    simp
  zero_mem' := fun n => by
    convert (A n).zero_mem using 1
    ext i
    simp
  smul_mem' := fun c v hv n => by
    convert (A n).smul_mem (Ideal.Quotient.mk _ c) (hv n) using 1
    ext i
    simp

omit [Fintype ι] in
/-- Membership in `towerLimitSubmodule ℓ A` is membership of every reduction. -/
theorem mem_towerLimitSubmodule {A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)})
      (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)})} {v : ι → O} :
    v ∈ towerLimitSubmodule ℓ A ↔ ∀ n, Ideal.Quotient.mk (Ideal.span {ℓ ^ (n + 1)}) ∘ v ∈ A n :=
  Iff.rfl

/-- `towerLimitSubmodule ℓ A` is `S₀`-stable when every `Aₙ` is. -/
theorem towerLimitSubmodule_stable {S₀ : Set (Matrix ι ι O)}
    {A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)}) (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)})}
    (hS : ∀ n, ∀ M ∈ S₀, ∀ v ∈ A n, M.map (algebraMap O _) *ᵥ v ∈ A n) :
    ∀ M ∈ S₀, ∀ v ∈ towerLimitSubmodule ℓ A, M *ᵥ v ∈ towerLimitSubmodule ℓ A := by
  intro M hM v hv
  refine (mem_towerLimitSubmodule ℓ).2 fun n => ?_
  convert hS n M hM _ ((mem_towerLimitSubmodule ℓ).1 hv n) using 1
  ext i
  exact RingHom.map_mulVec _ _ _ i

omit [Fintype ι] in
/-- **König's lemma for the tower**: if level `n₀` receives a nonzero image from every `A_{n₀+k}`,
there is a compatible family `aₖ ∈ A_{n₀+k}` with nonzero images at level `n₀`. -/
theorem exists_compatible_of_forall_exists_ne_zero [Finite ι]
    [hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ (n + 1)})]
    (A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)}) (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)}))
    (hA : ∀ n, ∀ v ∈ A (n + 1),
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_succ n)) ∘ v ∈ A n)
    {n₀ : ℕ} (hn₀ : ∀ k, ∃ v ∈ A (n₀ + k),
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_add_right n₀ k)) ∘ v ≠ 0) :
    ∃ a : ∀ k : ℕ, ι → O ⧸ Ideal.span {ℓ ^ (n₀ + k + 1)},
      (∀ k, a k ∈ A (n₀ + k) ∧
        Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_add_right n₀ k)) ∘ a k ≠
          0) ∧
      ∀ {k k' : ℕ} (h : k ≤ k'),
        Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.add_le_add_left h n₀)) ∘ a k' =
          a k := by
  let F : ℕᵒᵖ ⥤ Type _ :=
    { obj := fun k => {a : ι → O ⧸ Ideal.span {ℓ ^ (n₀ + k.unop + 1)} // a ∈ A (n₀ + k.unop) ∧
        Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_add_right n₀ k.unop)) ∘ a ≠
          0}
      map := fun {k k'} f => TypeCat.ofHom fun a => ⟨Ideal.Quotient.factor
          (span_pow_succ_le_span_pow_succ ℓ (Nat.add_le_add_left (leOfHom f.unop) n₀)) ∘ a.1,
        reduce_mem_of_le ℓ A hA (Nat.add_le_add_left (leOfHom f.unop) n₀) a.2.1, by
          convert a.2.2 using 1
          ext i
          simp⟩
      map_id := fun k => by
        ext : 2
        funext a
        refine Subtype.ext (funext fun i => ?_)
        simp
      map_comp := fun f g => by
        ext : 2
        funext a
        refine Subtype.ext (funext fun i => ?_)
        simp }
  have : ∀ k, Finite (F.obj k) := fun k => by
    have := hfin (n₀ + k.unop)
    exact Subtype.finite
  have : ∀ k, Nonempty (F.obj k) := fun k => by
    obtain ⟨v, hv⟩ := hn₀ k.unop
    exact ⟨⟨v, hv⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  exact ⟨fun k => (s (op k)).1, fun k => (s (op k)).2,
    fun h => congrArg Subtype.val (hs (homOfLE h).op)⟩

omit [Fintype ι] in
/-- An `ℓ`-adically compatible family `aₖ ∈ ι → O/ℓ^{n₀+k+1}` lifts to a vector of `ι → O` when
`O` is `ℓ`-adically precomplete. -/
theorem exists_lift_of_compatible [IsPrecomplete (Ideal.span {ℓ}) O] (n₀ : ℕ)
    (a : ∀ k : ℕ, ι → O ⧸ Ideal.span {ℓ ^ (n₀ + k + 1)})
    (ha : ∀ {k k' : ℕ} (h : k ≤ k'),
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.add_le_add_left h n₀)) ∘ a k' =
        a k) :
    ∃ L : ι → O, ∀ n, Ideal.Quotient.mk (Ideal.span {ℓ ^ (n + 1)}) ∘ L =
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (by omega : n ≤ n₀ + (n + 1))) ∘
        a (n + 1) := by
  choose r hr using fun k i => Ideal.Quotient.mk_surjective (a k i)
  have hrr : ∀ {k k' : ℕ}, k ≤ k' → ∀ i, r k' i - r k i ∈ Ideal.span {ℓ ^ (n₀ + k + 1)} := by
    intro k k' h i
    rw [← Ideal.Quotient.eq]
    have := congrFun (ha h) i
    simp only [Function.comp_apply] at this
    rwa [← hr k' i, ← hr k i, Ideal.Quotient.factor_mk] at this
  have hpow : ∀ m : ℕ, ((Ideal.span {ℓ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ℓ ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hL : ∀ i, ∃ L : O, ∀ k, r k i ≡ L [SMOD ((Ideal.span {ℓ}) ^ k • ⊤ : Submodule O O)] := by
    intro i
    refine IsPrecomplete.prec inferInstance fun {k k'} h => ?_
    rw [SModEq.sub_mem, hpow, ← neg_mem_iff, neg_sub]
    exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ℓ (by omega)) (hrr h i)
  choose L hL using hL
  refine ⟨L, fun n => funext fun i => ?_⟩
  have := hL i (n + 1)
  rw [SModEq.sub_mem, hpow] at this
  simp only [Function.comp_apply, ← hr (n + 1) i, Ideal.Quotient.factor_mk]
  exact (Ideal.Quotient.eq.2 this).symm

/-- **Stable towers in `(O/ℓⁿ⁺¹)ᵐ` are bounded below or eventually invisible.** Let `O` be
`ℓ`-adically precomplete with every `O/ℓⁿ⁺¹` finite, and `S₀` a set of matrices such that every
`S₀`-stable submodule of `ι → O` is zero or contains some `ℓᶜ • (ι → O)`. For `S₀`-stable
submodules `Aₙ ⊆ ι → O/ℓⁿ⁺¹` with `Aₙ₊₁` reducing into `Aₙ`, either every `Aₙ` contains
`ℓᶜ • (ι → O/ℓⁿ⁺¹)` for one `c`, or every level `n` receives only zero from `A_{n+k}` for some
`k`. -/
theorem lattice_tower_dichotomy
    [IsPrecomplete (Ideal.span {ℓ}) O] [hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ (n + 1)})]
    (S₀ : Set (Matrix ι ι O))
    (hirr : ∀ N : Submodule O (ι → O), (∀ M ∈ S₀, ∀ v ∈ N, M *ᵥ v ∈ N) →
      N = ⊥ ∨ ∃ c : ℕ, ∀ v : ι → O, ℓ ^ c • v ∈ N)
    (A : ∀ n : ℕ, Submodule (O ⧸ Ideal.span {ℓ ^ (n + 1)}) (ι → O ⧸ Ideal.span {ℓ ^ (n + 1)}))
    (hA : ∀ n, ∀ v ∈ A (n + 1),
      Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_succ n)) ∘ v ∈ A n)
    (hS : ∀ n, ∀ M ∈ S₀, ∀ v ∈ A n, M.map (algebraMap O _) *ᵥ v ∈ A n) :
    (∃ c : ℕ, ∀ n, ∀ w : ι → O ⧸ Ideal.span {ℓ ^ (n + 1)}, ℓ ^ c • w ∈ A n) ∨
      ∀ n, ∃ k, ∀ v ∈ A (n + k),
        Ideal.Quotient.factor (span_pow_succ_le_span_pow_succ ℓ (Nat.le_add_right n k)) ∘ v =
          0 := by
  classical
  refine or_iff_not_imp_right.2 fun hvis => ?_
  push Not at hvis
  obtain ⟨n₀, hn₀⟩ := hvis
  obtain ⟨a, ha₀, ha⟩ := exists_compatible_of_forall_exists_ne_zero ℓ A hA hn₀
  obtain ⟨L, hL⟩ := exists_lift_of_compatible ℓ n₀ a ha
  have hLN : L ∈ towerLimitSubmodule ℓ A := (mem_towerLimitSubmodule ℓ).2 fun n => by
    rw [hL n]
    exact reduce_mem_of_le ℓ A hA (n := n) (n' := n₀ + (n + 1)) (by omega) (ha₀ (n + 1)).1
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact (ha₀ (n₀ + 1)).2 ((hL n₀).symm.trans (by ext; simp))
  rcases hirr _ (towerLimitSubmodule_stable ℓ hS) with h | ⟨c, hc⟩
  · exact absurd (h ▸ hLN) (by simpa using hL0)
  refine ⟨c, fun n w => ?_⟩
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective.comp_left w
  convert (mem_towerLimitSubmodule ℓ).1 (hc v) n using 1
  ext i
  simp [Algebra.smul_def]

end Tower

end Stacks.EtaleCohomology

end
