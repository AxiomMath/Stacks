module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Data.Set.Card

/-!
# Invariant `ℓ`-adic characters from bounded invariant characters mod `ℓⁿ`

Let `G` be a compact group (the geometric fundamental group of a finite étale Galois cover of a
curve over a finite field) with a relation `R` on it (`R a b`: `b` is the conjugate of `a` by a
power of a Frobenius element). The geometric input of Weil II 1.3.4 asks that every continuous
homomorphism `ψ : G → K`, `K` an ultrametric field over `ℚ_ℓ`, which is `R`-invariant, vanish.

This file reduces it to a finiteness statement mod `ℓⁿ`: **if for every `e` there are at most `C`
locally constant `R`-invariant homomorphisms `G → ℤ/ℓᵉ`, with `C` independent of `e`, then every
continuous `R`-invariant homomorphism `G → K` is zero.** Geometrically the invariant characters
mod `ℓᵉ` are Frobenius-eigenvectors with cyclotomic eigenvalue in `H¹(Ȳ, ℤ/ℓᵉ)`, i.e. (Kummer) in
`Pic(Ȳ)[ℓᵉ]`, and the Weil pairing bounds their number by the number of Frobenius-fixed points
of `Pic(Ȳ)[ℓᵉ]`, which lie in the finite group of rational points of the Jacobian.

The proof: if `ψ(g₀) = a ≠ 0`, the closed ball `B` of radius `‖a‖ ℓ⁻ⁿ` is an open subgroup of
`K`, so the image `A` of `G` in `K / B` is finite (compactness) and killed by a power `ℓᵉ`
(boundedness). The multiples `j • ā`, `j < ℓⁿ`, are distinct, so `#A ≥ ℓⁿ`; and `A` has `#A`
homomorphisms to `ℤ/ℓᵉ` (Pontryagin duality for finite abelian groups), each giving an invariant
character of `G`. Hence `ℓⁿ ≤ C` for every `n`, which is absurd.

## Main results

* `Stacks.LAdic.exists_addMonoidHom_zmod_of_addChar` — a complex character of a finite abelian
  group killed by `N` comes from a homomorphism to `ℤ/N`.
* `Stacks.LAdic.natCard_le_natCard_addMonoidHom_zmod` — such a group has at least as many
  homomorphisms to `ℤ/N` as elements.
* `Stacks.LAdic.eq_zero_of_encard_invariant_zmod_le` — the reduction described above.
* `Stacks.LAdic.sub_one_nsmul_eq_zero_of_tame` — a Frobenius-invariant character mod `ℓᵉ` of tame
  inertia is killed by `q ^ M - 1`, independently of `e`.
* `Stacks.LAdic.forall_eq_zero_of_forall_encard_invariant_zmod_le` — the same in the shape of the
  hypothesis `hD1` of the determinantal weights.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.3.4)
-/

@[expose] public noncomputable section

open Function

namespace Stacks.LAdic

/-- An additive-valued function on a group that turns products into sums sends `1` to `0`. -/
private theorem map_one_eq_zero_of_map_mul {G M : Type*} [Group G] [AddGroup M] (f : G → M)
    (hadd : ∀ a b, f (a * b) = f a + f b) : f 1 = 0 := by
  have h := hadd 1 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

section Characters

variable {A : Type*} [AddCommGroup A] {N : ℕ} [NeZero N]

/-- The standard character of `ℤ/N` sends `1` to a primitive `N`-th root of unity. -/
theorem isPrimitiveRoot_stdAddChar_one : IsPrimitiveRoot (ZMod.stdAddChar (N := N) 1) N := by
  have h1 : ZMod.stdAddChar (N := N) 1 = Complex.exp (2 * Real.pi * Complex.I / N) := by
    simpa using ZMod.stdAddChar_coe (N := N) 1
  rw [h1]
  exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- **A complex character of a finite abelian group killed by `N` comes from a homomorphism to
`ℤ/N`** through the standard character of `ℤ/N`: its values are `N`-th roots of unity. -/
theorem exists_addMonoidHom_zmod_of_addChar (hA : ∀ a : A, N • a = 0) (χ : AddChar A ℂ) :
    ∃ f : A →+ ZMod N, ∀ a, ZMod.stdAddChar (f a) = χ a := by
  have hroot : ∀ a, ∃ j : ZMod N, ZMod.stdAddChar j = χ a := by
    intro a
    have h1 : (χ a) ^ N = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, hA, AddChar.map_zero_eq_one]
    obtain ⟨i, -, hi⟩ := isPrimitiveRoot_stdAddChar_one.eq_pow_of_pow_eq_one h1
    exact ⟨(i : ℕ) • (1 : ZMod N), by rw [AddChar.map_nsmul_eq_pow, hi]⟩
  choose f hf using hroot
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply ZMod.injective_stdAddChar
    rw [hf, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]
  · intro a b
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_add_eq_mul, hf, hf, hf, AddChar.map_add_eq_mul]

/-- **A finite abelian group killed by `N` has at least as many homomorphisms to `ℤ/N` as it has
elements**: they map onto its complex characters, which are as many as its elements. -/
theorem natCard_le_natCard_addMonoidHom_zmod [Finite A] (hA : ∀ a : A, N • a = 0) :
    Nat.card A ≤ Nat.card (A →+ ZMod N) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hsurj : Surjective
      (fun f : A →+ ZMod N => (ZMod.stdAddChar (N := N)).compAddMonoidHom f) := by
    intro χ
    obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_of_addChar hA χ
    exact ⟨f, DFunLike.ext _ _ hf⟩
  have : Finite (A →+ ZMod N) := Finite.of_injective _ DFunLike.coe_injective
  calc Nat.card A = Fintype.card A := Nat.card_eq_fintype_card
    _ = Fintype.card (AddChar A ℂ) := (AddChar.card_eq).symm
    _ = Nat.card (AddChar A ℂ) := Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (A →+ ZMod N) := Nat.card_le_card_of_surjective _ hsurj

end Characters

/-- The norm of a natural number in a normed field over `ℚ_ℓ` is its `ℓ`-adic norm. -/
private theorem norm_natCast_eq_padicNorm {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[ℓ] K] (j : ℕ) : ‖(j : K)‖ = ‖(j : ℚ_[ℓ])‖ := by
  rw [← norm_algebraMap' K (j : ℚ_[ℓ]), map_natCast]

section Bound

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K]

omit [IsUltrametricDist K] in
/-- The norm of an integer in a normed field over `ℚ_ℓ` is its `ℓ`-adic norm. -/
theorem norm_intCast_eq_padicNorm (j : ℤ) : ‖(j : K)‖ = ‖(j : ℚ_[ℓ])‖ := by
  rw [← norm_algebraMap' K (j : ℚ_[ℓ]), map_intCast]

/-- **Invariant `ℓ`-adic characters from bounded invariant characters mod `ℓᵉ`** (the reduction
of the geometric input of Weil II 1.3.4 to a finiteness statement). Let `G` be a compact group
with a relation `R`. If for every `e` the locally constant `R`-invariant homomorphisms
`G → ℤ/ℓᵉ` are at most `C` in number, `C` independent of `e`, then every continuous
`R`-invariant homomorphism from `G` to an ultrametric normed field over `ℚ_ℓ` is zero. -/
theorem eq_zero_of_encard_invariant_zmod_le {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] (R : G → G → Prop) (C : ℕ)
    (hC : ∀ e : ℕ, {χ : G → ZMod (ℓ ^ e) | (∀ a b, χ (a * b) = χ a + χ b) ∧
      IsLocallyConstant χ ∧ ∀ a b, R a b → χ b = χ a}.encard ≤ C)
    (ψ : G → K) (hadd : ∀ a b, ψ (a * b) = ψ a + ψ b) (hψ : Continuous ψ)
    (hinv : ∀ a b, R a b → ψ b = ψ a) : ψ = 0 := by
  classical
  by_contra hne
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, ψ g₀ ≠ 0 := by
    by_contra h
    exact hne (funext fun g => not_not.1 fun hg => h ⟨g, hg⟩)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- a bound for `‖ψ‖`
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, ∀ g, ‖ψ g‖ ≤ Rb := by
    obtain ⟨Rb, hRb⟩ := (isCompact_range hψ).isBounded.exists_norm_le
    exact ⟨Rb, fun g => hRb _ ⟨g, rfl⟩⟩
  -- `n` with `ℓ ^ n > C`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, C < ℓ ^ n := ⟨C, Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt⟩
  set a := ψ g₀ with ha
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 hg₀
  set r : ℝ := ‖a‖ * ((ℓ : ℝ) ^ n)⁻¹ with hr
  have hr0 : 0 < r := mul_pos ha0 (inv_pos.2 (pow_pos hℓ0 n))
  let B : AddSubgroup K := (IsUltrametricDist.closedBall_openAddSubgroup K hr0).toAddSubgroup
  have hB : ∀ y : K, y ∈ B ↔ ‖y‖ ≤ r := fun y => by
    change y ∈ Metric.closedBall (0 : K) r ↔ _
    rw [mem_closedBall_zero_iff]
  have hBopen : IsOpen (B : Set K) := (IsUltrametricDist.closedBall_openAddSubgroup K hr0).isOpen
  have : DiscreteTopology (K ⧸ B) := QuotientAddGroup.discreteTopology hBopen
  -- the homomorphism `G → K ⧸ B`
  have hψ1 : ψ 1 = 0 := map_one_eq_zero_of_map_mul ψ hadd
  let ψ' : Additive G →+ K :=
    { toFun := fun g => ψ (Additive.toMul g)
      map_zero' := hψ1
      map_add' := fun x y => hadd _ _ }
  let f : Additive G →+ K ⧸ B := (QuotientAddGroup.mk' B).comp ψ'
  let A : AddSubgroup (K ⧸ B) := f.range
  have hfcont : Continuous fun g : G => (QuotientAddGroup.mk (ψ g) : K ⧸ B) :=
    continuous_quot_mk.comp hψ
  have hAfin : Finite A := by
    have hfin := (isCompact_range hfcont).finite_of_discrete
    refine Set.Finite.to_subtype (hfin.subset ?_)
    rintro _ ⟨g, rfl⟩
    exact ⟨Additive.toMul g, rfl⟩
  -- an exponent killing `A`
  obtain ⟨e, he⟩ : ∃ e : ℕ, Rb / r < (ℓ : ℝ) ^ e := pow_unbounded_of_one_lt _ hℓ1
  have hkill : ∀ x : A, (ℓ ^ e) • x = 0 := by
    rintro ⟨_, g, rfl⟩
    apply Subtype.ext
    change (ℓ ^ e) • (QuotientAddGroup.mk (ψ (Additive.toMul g)) : K ⧸ B) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hB, nsmul_eq_mul, norm_mul]
    have h1 : ‖((ℓ ^ e : ℕ) : K)‖ = ((ℓ : ℝ) ^ e)⁻¹ := by
      rw [norm_natCast_eq_padicNorm (ℓ := ℓ)]
      push_cast
      rw [norm_pow, Padic.norm_p]
      simp
    rw [h1]
    have hpos : 0 < (ℓ : ℝ) ^ e := pow_pos hℓ0 e
    rw [inv_mul_le_iff₀ hpos]
    have := (div_lt_iff₀ hr0).1 he
    nlinarith [hRb (Additive.toMul g)]
  -- `ℓ ^ n ≤ #A`
  have hlow : ℓ ^ n ≤ Nat.card A := by
    let x : A := ⟨f (Additive.ofMul g₀), ⟨_, rfl⟩⟩
    have hinj : Injective fun j : Fin (ℓ ^ n) => (j : ℕ) • x := by
      intro j j' hjj
      by_contra hne'
      wlog hlt : (j : ℕ) < j' generalizing j j'
      · exact this hjj.symm (Ne.symm hne') (lt_of_le_of_ne (not_lt.1 hlt)
          (fun h => hne' (Fin.ext h.symm)))
      have h1 : ((j' : ℕ) - j) • x = 0 := by
        have hjj' : (j : ℕ) • x = (j' : ℕ) • x := hjj
        rw [sub_nsmul x hlt.le, ← hjj']
        exact add_neg_cancel ((j : ℕ) • x)
      have h2 : (((j' : ℕ) - j) • a) ∈ B := by
        have := congrArg Subtype.val h1
        change ((j' : ℕ) - j) • (QuotientAddGroup.mk a : K ⧸ B) = 0 at this
        rwa [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at this
      rw [hB, nsmul_eq_mul, norm_mul] at h2
      have h3 : ‖(((j' : ℕ) - j : ℕ) : ℚ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
        have h4 : ‖(((j' : ℕ) - j : ℕ) : K)‖ ≤ ((ℓ : ℝ) ^ n)⁻¹ := by
          rw [hr, mul_comm ‖a‖] at h2
          exact le_of_mul_le_mul_right h2 ha0
        rw [norm_natCast_eq_padicNorm (ℓ := ℓ)] at h4
        rw [zpow_neg, zpow_natCast]
        exact_mod_cast h4
      have h5 := (Padic.norm_int_le_pow_iff_dvd (((j' : ℕ) - j : ℕ) : ℤ) n).1
        (by exact_mod_cast h3)
      have h6 : ℓ ^ n ∣ (j' : ℕ) - j := by exact_mod_cast h5
      have h7 : (j' : ℕ) - j < ℓ ^ n := lt_of_le_of_lt (Nat.sub_le _ _) j'.2
      have h8 : 0 < (j' : ℕ) - j := Nat.sub_pos_of_lt hlt
      exact absurd (Nat.le_of_dvd h8 h6) (not_le.2 h7)
    calc ℓ ^ n = Nat.card (Fin (ℓ ^ n)) := (Nat.card_fin _).symm
      _ ≤ Nat.card A := Nat.card_le_card_of_injective _ hinj
  -- each homomorphism `A → ℤ/ℓᵉ` gives an invariant character of `G`
  have hNe : NeZero (ℓ ^ e) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let toA : G → A := fun g => ⟨f (Additive.ofMul g), ⟨_, rfl⟩⟩
  have htoA : Surjective toA := by
    rintro ⟨_, g, rfl⟩
    exact ⟨Additive.toMul g, rfl⟩
  have htoAlc : IsLocallyConstant toA := by
    have : DiscreteTopology A := inferInstance
    rw [IsLocallyConstant.iff_continuous]
    exact Continuous.subtype_mk hfcont _
  let Φ : (A →+ ZMod (ℓ ^ e)) → G → ZMod (ℓ ^ e) := fun lam g => lam (toA g)
  have hΦinj : Injective Φ := by
    intro lam μ h
    ext y
    obtain ⟨g, rfl⟩ := htoA y
    exact congrFun h g
  have hΦmem : Set.range Φ ⊆ {χ : G → ZMod (ℓ ^ e) | (∀ a b, χ (a * b) = χ a + χ b) ∧
      IsLocallyConstant χ ∧ ∀ a b, R a b → χ b = χ a} := by
    rintro _ ⟨lam, rfl⟩
    refine ⟨fun g h => ?_, htoAlc.comp _, fun g h hgh => ?_⟩
    · change lam (toA (g * h)) = lam (toA g) + lam (toA h)
      rw [← map_add]
      congr 1
      exact Subtype.ext (map_add f (Additive.ofMul g) (Additive.ofMul h))
    · change lam (toA h) = lam (toA g)
      congr 1
      exact Subtype.ext (congrArg (fun y : K => (QuotientAddGroup.mk y : K ⧸ B)) (hinv g h hgh))
  have hcard : Nat.card (A →+ ZMod (ℓ ^ e)) ≤ C := by
    have h1 := (Set.encard_le_encard hΦmem).trans (hC e)
    rw [hΦinj.encard_range] at h1
    have : Finite (A →+ ZMod (ℓ ^ e)) := by
      refine Finite.of_injective (fun f : A →+ ZMod (ℓ ^ e) => (f : A → ZMod (ℓ ^ e))) ?_
      intro f g h
      exact AddMonoidHom.ext (congrFun h)
    rw [ENat.card_eq_coe_natCard] at h1
    exact_mod_cast h1
  have := natCard_le_natCard_addMonoidHom_zmod (N := ℓ ^ e) hkill
  omega

/-- **The geometric input of Weil II 1.3.4 from bounded invariant characters mod `ℓᵉ`**, in the
shape of the hypothesis `hD1` of the determinantal weights
(`AlgebraicGeometry.exists_geometricFrobeniusFamily_determinantal_weights`). Let `Γ` be a compact
group, `H` a closed subgroup and `φ ∈ Γ`. If for every open normal `U` the locally constant
homomorphisms `H ⊓ U → ℤ/ℓᵉ` invariant under conjugation by `φ ^ [Γ : U]` are bounded in number
independently of `e`, then every continuous homomorphism `H ⊓ U → K` with the same invariance
vanishes. -/
theorem forall_eq_zero_of_forall_encard_invariant_zmod_le {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (H : Subgroup Γ)
    (hH : IsClosed (H : Set Γ)) (φ : Γ)
    (hbound : ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∃ C : ℕ, ∀ e : ℕ,
      {χ : ↥(H ⊓ U) → ZMod (ℓ ^ e) | (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ ∧
        ∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → χ b = χ a}.encard ≤ C) :
    ∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) →
      ∀ ψ : ↥(H ⊓ U) → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥(H ⊓ U), (b : Γ) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) →
        ψ = 0 := by
  intro U hU hUo ψ hadd hcont hinv
  obtain ⟨C, hC⟩ := hbound U hU hUo
  have hclosed : IsClosed ((H ⊓ U : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_inf]
    exact hH.inter (U.isClosed_of_isOpen hUo)
  have : CompactSpace ↥(H ⊓ U) := isCompact_iff_compactSpace.1 hclosed.isCompact
  exact eq_zero_of_encard_invariant_zmod_le _ C hC ψ hadd hcont hinv

end Bound

section Tame

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A character mod `ℓᵉ` of tame inertia invariant under a power of Frobenius has bounded
order** (the boundary part of the geometric input of Weil II 1.3.4). Let `I` be a subgroup of a
topological group `Γ` with a homomorphism `t : I → ℤ_ℓ` whose kernel consists of
pro-prime-to-`ℓ` elements, and `Fr ∈ Γ` with `Fr σ Fr⁻¹ σ^{-q} ∈ ker t` for every `σ ∈ I` (the
shape of `exists_ladicTameCharacter`). A homomorphism `χ : I → ℤ/ℓᵉ` with open kernel that is
invariant under conjugation by `Fr ^ M` is killed by `q ^ M - 1`, a bound independent of `e`. -/
theorem sub_one_nsmul_eq_zero_of_tame {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (I : Subgroup Γ) (t : I →* Multiplicative ℤ_[ℓ])
    (ht : ∀ σ : I, t σ = 1 → ∀ U : OpenSubgroup Γ, ∃ m : ℕ, ℓ.Coprime m ∧ (σ : Γ) ^ m ∈ U)
    (Fr : Γ) (q : ℕ)
    (hFr : ∀ σ : I, ∃ τ : I, (τ : Γ) = Fr * σ * Fr⁻¹ * ((σ : Γ) ^ q)⁻¹ ∧ t τ = 1)
    (e : ℕ) (χ : I → ZMod (ℓ ^ e)) (hadd : ∀ a b, χ (a * b) = χ a + χ b)
    (hχ : ∃ U : OpenSubgroup Γ, ∀ σ : I, (σ : Γ) ∈ U → χ σ = 0) (M : ℕ)
    (hinv : ∀ σ τ : I, (τ : Γ) = Fr ^ M * σ * (Fr ^ M)⁻¹ → χ τ = χ σ) (σ : I) :
    (q ^ M - 1 : ℕ) • χ σ = 0 := by
  obtain ⟨U, hU⟩ := hχ
  have hone : χ 1 = 0 := map_one_eq_zero_of_map_mul χ hadd
  have hpow : ∀ (a : I) (m : ℕ), χ (a ^ m) = m • χ a := by
    intro a m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hadd, ih, succ_nsmul]
  -- `χ` vanishes on the kernel of `t`
  have hker : ∀ τ : I, t τ = 1 → χ τ = 0 := by
    intro τ hτ
    obtain ⟨m, hm, hmU⟩ := ht τ hτ U
    have h1 : m • χ τ = 0 := by
      rw [← hpow]
      exact hU _ (by simpa using hmU)
    have hunit : IsUnit (m : ZMod (ℓ ^ e)) :=
      (ZMod.unitOfCoprime m (Nat.Coprime.pow_left e hm).symm).isUnit
    rw [nsmul_eq_mul] at h1
    exact (hunit.mul_right_eq_zero).1 h1
  -- conjugation by `Fr` stays in `I` and multiplies `χ` by `q`
  have hconj : ∀ a : I, ∃ b : I, (b : Γ) = Fr * a * Fr⁻¹ ∧ χ b = q • χ a := by
    intro a
    obtain ⟨τ, hτ, htτ⟩ := hFr a
    refine ⟨τ * a ^ q, ?_, ?_⟩
    · rw [Subgroup.coe_mul, hτ, Subgroup.coe_pow]
      group
    · rw [hadd, hker τ htτ, zero_add, hpow]
  have hconjM : ∀ (m : ℕ) (a : I), ∃ b : I, (b : Γ) = Fr ^ m * a * (Fr ^ m)⁻¹ ∧
      χ b = (q ^ m) • χ a := by
    intro m
    induction m with
    | zero => exact fun a => ⟨a, by simp, by simp⟩
    | succ m ih =>
      intro a
      obtain ⟨b, hb, hχb⟩ := ih a
      obtain ⟨c, hc, hχc⟩ := hconj b
      refine ⟨c, ?_, ?_⟩
      · rw [hc, hb, pow_succ']
        group
      · rw [hχc, hχb, ← mul_nsmul, pow_succ', mul_comm]
  obtain ⟨b, hb, hχb⟩ := hconjM M σ
  rw [hinv σ b hb, nsmul_eq_mul] at hχb
  rw [nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (q ^ M) with hq | hq
  · rw [hq, Nat.zero_sub, Nat.cast_zero, zero_mul]
  · rw [Nat.cast_sub hq, sub_mul, Nat.cast_one, one_mul, ← hχb, sub_self]

end Tame

end Stacks.LAdic

end
