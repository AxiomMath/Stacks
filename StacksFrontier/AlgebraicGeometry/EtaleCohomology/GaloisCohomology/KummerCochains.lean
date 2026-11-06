module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains

/-!
# The Kummer sequence in degree two

Let `Ω` be a separably closed field, `K` a subfield with `Ω/K` Galois and `Br(K) = 0`, and `p` a
prime invertible in `Ω` such that `K` contains a primitive `p`-th root of unity. Then every
locally constant `2`-cocycle of `Gal(Ω/K)` with values in `ℤ/p`, with the trivial action, is a
coboundary: `H ²(Gal(Ω/K), ℤ/p) = 0`.

## Main results

* `Stacks.GaloisCohomology.isOpen_stabilizer_units`: the stabilizer in `Gal(Ω/K)` of a unit of `Ω`
  is open.
* `Stacks.GaloisCohomology.isLocallyConstant_smul_units`: the orbit map of a unit of `Ω` is locally
  constant.
* `Stacks.GaloisCohomology.exists_dOne_eq_kummer`: the degree-two Kummer vanishing, in cochain
  form.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence.
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
-/

@[expose] public noncomputable section

open groupCohomology IntermediateField Stacks.GroupCohomology

universe u

namespace Stacks.GaloisCohomology

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The stabilizer in `Gal(Ω/K)` of a unit of `Ω` is open. -/
theorem isOpen_stabilizer_units (b : Ωˣ) : IsOpen {g : Gal(Ω/K) | g • b = b} := by
  have hfd : FiniteDimensional K K⟮(b : Ω)⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : Ω))
  have hle : (K⟮(b : Ω)⟯).fixingSubgroup ≤ MulAction.stabilizer Gal(Ω/K) b := by
    intro g hg
    simp only [IntermediateField.mem_fixingSubgroup_iff] at hg
    have hga : g (b : Ω) = (b : Ω) :=
      hg (b : Ω) (IntermediateField.mem_adjoin_simple_self K (b : Ω))
    exact MulAction.mem_stabilizer_iff.mpr (Units.val_inj.mp (by simpa using hga))
  exact Subgroup.isOpen_mono hle (K⟮(b : Ω)⟯).fixingSubgroup_isOpen

/-- The orbit map of a unit of `Ω` is locally constant. -/
theorem isLocallyConstant_smul_units (b : Ωˣ) :
    IsLocallyConstant fun g : Gal(Ω/K) ↦ g • b := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g : Gal(Ω/K) ↦ g₀⁻¹ * g) ⁻¹' {g : Gal(Ω/K) | g • b = b},
    (isOpen_stabilizer_units b).preimage (by fun_prop),
    by simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, one_smul],
    fun g hg ↦ ?_⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
  calc g • b = (g₀ * (g₀⁻¹ * g)) • b := by rw [mul_inv_cancel_left]
    _ = g₀ • ((g₀⁻¹ * g) • b) := mul_smul _ _ _
    _ = g₀ • b := by rw [hg]

omit [IsGalois K Ω] in
/-- An automorphism of `Ω` fixing a unit `ζ` fixes every integer power of `ζ`. -/
theorem smul_eq_of_mem_zpowers {ζ : Ωˣ} (g : Gal(Ω/K)) (hfix : g • ζ = ζ) {u : Ωˣ}
    (hu : u ∈ Subgroup.zpowers ζ) : g • u = u := by
  obtain ⟨n, rfl⟩ := hu
  show g • ζ ^ n = ζ ^ n
  rw [smul_zpow', hfix]

/-- **The degree-two Kummer vanishing.** If `Ω` is separably closed, `p` is a prime invertible in
`Ω`, the Brauer group of `K` vanishes and `K` contains a primitive `p`-th root of unity, then
every locally constant `2`-cocycle of `Gal(Ω/K)` with values in `ℤ/p` with the trivial action is
the coboundary of a locally constant `1`-cochain. -/
theorem exists_dOne_eq_kummer [IsSepClosed Ω] (p : ℕ) (hp : p.Prime) [NeZero (p : Ω)]
    (hBr : ∀ y : BrauerGroup K, y = 1) (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ g : Gal(Ω/K), g • ζ = ζ)
    (F : Gal(Ω/K) × Gal(Ω/K) → ZMod p) (hFlc : IsLocallyConstant F)
    (hF : ∀ g₁ g₂ g₃ : Gal(Ω/K), F (g₁ * g₂, g₃) + F (g₁, g₂) = F (g₂, g₃) + F (g₁, g₂ * g₃)) :
    ∃ x : Gal(Ω/K) → ZMod p, IsLocallyConstant x ∧
      ∀ g₁ g₂ : Gal(Ω/K), x g₂ - x (g₁ * g₂) + x g₁ = F (g₁, g₂) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set e : ZMod p ≃+ Additive (Subgroup.zpowers ζ) := hζ.zmodEquivZPowers with hedef
  set ε : ZMod p → Ωˣ := fun k ↦ ((Additive.toMul (e k) : Subgroup.zpowers ζ) : Ωˣ) with hεdef
  have hεmem : ∀ k, ε k ∈ Subgroup.zpowers ζ := fun k ↦ (Additive.toMul (e k)).2
  have hεmul : ∀ k l, ε (k + l) = ε k * ε l := fun k l ↦ by
    simp only [hεdef, map_add, toMul_add, Subgroup.coe_mul]
  have hεinj : Function.Injective ε := fun k l hkl ↦
    e.injective (Additive.toMul.injective (Subtype.ext hkl))
  have hεsub : ∀ k l, ε (k - l) = ε k / ε l := fun k l ↦
    eq_div_iff_mul_eq'.2 (by rw [← hεmul, sub_add_cancel])
  have hεfix : ∀ (g : Gal(Ω/K)) (k : ZMod p), g • ε k = ε k :=
    fun g k ↦ smul_eq_of_mem_zpowers g (hfix g) (hεmem k)
  have hmem_iff : ∀ u : Ωˣ, u ∈ Subgroup.zpowers ζ ↔ u ^ p = 1 := fun u ↦ by
    rw [hζ.zpowers_eq]
    simp
  have hεpow : ∀ k, (ε k) ^ p = 1 := fun k ↦ (hmem_iff _).1 (hεmem k)
  set f : Gal(Ω/K) × Gal(Ω/K) → Ωˣ := fun q ↦ ε (F q) with hfdef
  have hflc : IsLocallyConstant f := hFlc.comp ε
  have hfcoc : IsMulCocycle₂ f := by
    intro g h j
    simp only [hfdef, hεfix]
    rw [← hεmul, ← hεmul, hF g h j]
  have H : ∀ (L : FiniteGaloisIntermediateField K Ω) (C : Gal(↥L/K) × Gal(↥L/K) → Lˣ),
      IsMulCocycle₂ C → IsMulCoboundary₂ C := fun L C hC ↦
    isMulCoboundary₂_of_brauer (fun y _ ↦ hBr y) C hC
  obtain ⟨x₁, hx₁lc, hx₁⟩ :=
    exists_isLocallyConstant_isMulCoboundary₂_of_forall_finiteGalois H f hflc hfcoc
  have hu : IsMulCocycle₁ fun g ↦ (x₁ g) ^ p := by
    intro g h
    have h1 : (g • x₁ h) ^ p / (x₁ (g * h)) ^ p * (x₁ g) ^ p = 1 := by
      have h0 := congrArg (fun z : Ωˣ ↦ z ^ p) (hx₁ g h)
      simp only [div_pow, mul_pow] at h0
      rw [h0, hfdef]
      exact hεpow (F (g, h))
    have h2 : (g • x₁ h) ^ p * (x₁ g) ^ p / (x₁ (g * h)) ^ p = 1 := by
      rwa [← div_mul_eq_mul_div]
    simpa only [smul_pow'] using (div_eq_one.1 h2).symm
  have hulc : IsLocallyConstant fun g ↦ (x₁ g) ^ p := hx₁lc.comp fun z : Ωˣ ↦ z ^ p
  obtain ⟨a, ha⟩ := isMulCoboundary₁_of_isLocallyConstant_of_isMulCocycle₁ _ hulc hu
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (a : Ω) p
  have hzne : z ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hz
    exact a.ne_zero hz.symm
  set b : Ωˣ := Units.mk0 z hzne with hbdef
  have hbp : b ^ p = a := Units.val_injective (by simpa [hbdef] using hz)
  set β : Gal(Ω/K) → Ωˣ := fun g ↦ g • b / b with hβdef
  have hdiv : ∀ (x y : Gal(Ω/K) → Ωˣ) (g h : Gal(Ω/K)),
      g • (x h / y h) / (x (g * h) / y (g * h)) * (x g / y g) =
        (g • x h / x (g * h) * x g) / (g • y h / y (g * h) * y g) := by
    intro x y g h
    rw [smul_div', div_div_div_comm, div_mul_div_comm]
  have hβcob : ∀ g h : Gal(Ω/K), g • β h / β (g * h) * β g = 1 := by
    intro g h
    simp only [hβdef]
    rw [hdiv (fun g : Gal(Ω/K) ↦ g • b) (fun _ ↦ b) g h, ← mul_smul, div_self', one_mul,
      div_mul_cancel, div_self']
  have hβpow : ∀ g : Gal(Ω/K), (β g) ^ p = g • a / a := by
    intro g
    simp only [hβdef, div_pow, ← smul_pow', hbp]
  set x₂ : Gal(Ω/K) → Ωˣ := fun g ↦ x₁ g / β g with hx₂def
  have hβlc : IsLocallyConstant β :=
    (isLocallyConstant_smul_units b).comp₂ (IsLocallyConstant.const b) (· / ·)
  have hx₂lc : IsLocallyConstant x₂ := hx₁lc.comp₂ hβlc (· / ·)
  have hx₂pow : ∀ g, (x₂ g) ^ p = 1 := by
    intro g
    simp only [hx₂def, div_pow, hβpow, ha g]
    exact div_self' _
  have hx₂ : ∀ g h : Gal(Ω/K), g • x₂ h / x₂ (g * h) * x₂ g = f (g, h) := by
    intro g h
    simp only [hx₂def]
    rw [hdiv x₁ β g h, hx₁ g h, hβcob g h, div_one]
  have hx₂mem : ∀ g, x₂ g ∈ Subgroup.zpowers ζ := fun g ↦ (hmem_iff _).2 (hx₂pow g)
  have hx₂range : ∀ g, ∃ k : ZMod p, ε k = x₂ g := fun g ↦ by
    obtain ⟨n, hn⟩ := e.surjective (Additive.ofMul ⟨x₂ g, hx₂mem g⟩)
    exact ⟨n, by simp only [hεdef, hn, toMul_ofMul]⟩
  choose y hy using hx₂range
  refine ⟨y, isLocallyConstant_of_comp_injective hεinj (by simpa only [hy] using hx₂lc),
    fun g₁ g₂ ↦ hεinj ?_⟩
  rw [hεmul, hεsub, hy, hy, hy, ← smul_eq_of_mem_zpowers g₁ (hfix g₁) (hx₂mem g₂)]
  exact hx₂ g₁ g₂

end Stacks.GaloisCohomology

end
