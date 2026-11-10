module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsLinearEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# From an integral specialization map to an `E`-linear map into the inertia invariants

Let `St` be a `ℤ_ℓ`-module (the stalk of an ℓ-adic sheaf with coefficients in `O`, `E = O[1/ℓ]`)
and `s : St → ℤ_ℓ^r` a `ℤ_ℓ`-linear map whose kernel is killed by `ℓᴹ`, landing in the vectors
fixed by `ρ₀(g)` for `g` in a subgroup `I`, carrying an endomorphism `F` of `St` to `ρ₀(g_F)` and
each `o ∈ O` to `ℓ⁻ᴺ Mₒ`. If matrices `P`, `Q` with `P Q = 1` conjugate `ρ₀` to `Res_b τ` and
`ℓ⁻ᴺ Mₒ` to `Res_b(o · 1)`, then `x ↦ Q (ℚ_ℓ ⊗ s)(x)`, read in `E^m`, is an injective `E`-linear
map from `ℚ_ℓ ⊗ St` to the `τ(I)`-invariants of `E^m` carrying `ℚ_ℓ ⊗ F` to `τ(g_F)`
(`Stacks.EtaleCohomology.exists_linearMap_invariants_of_integral`).

This is the algebraic last step of the specialization map of Laumon's degeneration
(`Stacks.EtaleCohomology.CurveSpecializationInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `s` is the limit of the level maps
`(Gₙ)_ȳ → (j_* ℱ_{ρ,n})_ȳ ↪ (ℤ/ℓⁿ⁺¹)^r`.

## Main results

* `Stacks.EtaleCohomology.exists_algebraMap_smul_eq_one_tmul_padic`: every element of
  `ℚ_ℓ ⊗ St` is `σ⁻¹ ⊗ v`.
* `Stacks.EtaleCohomology.exists_linearMap_invariants_of_integral`.
-/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Every element of `ℚ_ℓ ⊗ St` is `σ⁻¹ ⊗ v`**: `ℚ_ℓ ⊗ St` is the localization of `St` at the
nonzero elements of `ℤ_ℓ`. -/
public theorem exists_algebraMap_smul_eq_one_tmul_padic {St : Type*} [AddCommGroup St]
    [Module ℤ_[ℓ] St] (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) :
    ∃ (σ : ℤ_[ℓ]) (v : St), σ ≠ 0 ∧
      algebraMap ℤ_[ℓ] ℚ_[ℓ] σ • x = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v := by
  have hl : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] St 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[ℓ]) ℚ_[ℓ] _).2
      (TensorProduct.isBaseChange ℤ_[ℓ] St ℚ_[ℓ])
  obtain ⟨⟨v, σ⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[ℓ])
    (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] St 1) x
  exact ⟨σ, v, nonZeroDivisors.ne_zero σ.2, by rwa [algebraMap_smul]⟩

section Main

variable {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {O : Type*} [CommRing O]
  [Algebra O E] [IsLocalization (Submonoid.powers (ℓ : O)) E]
  {d m r : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
  {St : Type*} [AddCommGroup St] [Module ℤ_[ℓ] St]
  [Module E (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St)] [IsScalarTower ℚ_[ℓ] E (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St)]

/-- The rationalization `ℚ_ℓ ⊗ St → ℚ_ℓ^r` of `s : St → ℤ_ℓ^r`. -/
def rationalIntegralMap (s : St →ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) :
    (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) →ₗ[ℚ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  LinearMap.liftBaseChange ℚ_[ℓ]
    ((LinearMap.compLeft (Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ]) (Fin r)) ∘ₗ s)

/-- The rationalization of `s` sends `c ⊗ v` to `c` times the image of `s v` in `ℚ_ℓ^r`. -/
theorem rationalIntegralMap_tmul (s : St →ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) (c : ℚ_[ℓ]) (v : St) :
    rationalIntegralMap s (c ⊗ₜ v) = c • fun i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (s v i) := by
  rw [rationalIntegralMap, LinearMap.liftBaseChange_tmul]
  rfl

/-- **An integral specialization map gives an `E`-linear injection into the invariants.** -/
public theorem exists_linearMap_invariants_of_integral
    (act : O → St →ₗ[ℤ_[ℓ]] St)
    (hact : ∀ (o : O) (v : St), algebraMap O E o • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] act o v)
    (s : St →ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) (M : ℕ)
    (hker : ∀ v, s v = 0 → (ℓ ^ M : ℤ_[ℓ]) • v = 0)
    (N : ℕ) (Mo : O → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hO : ∀ o v, (ℓ ^ N : ℤ_[ℓ]) • s (act o v) = Mo o *ᵥ s v)
    (Pm : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Qm : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
    (hPQ : Pm * Qm = 1)
    (hα : ∀ o, Qm * (((ℓ : ℚ_[ℓ]) ^ N)⁻¹ • (Mo o).map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) * Pm =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) (algebraMap O E o)))
    {G : Type*} [Group G] (ρ₀ : G → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (τ : G →* GL (Fin m) E)
    (hτ : ∀ g, Qm * (ρ₀ g).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) * Pm =
      restrictScalarsMatrix b (τ g : Matrix (Fin m) (Fin m) E))
    (I : Subgroup G) (hinv : ∀ v, ∀ g ∈ I, ρ₀ g *ᵥ s v = s v)
    (Fs : St →ₗ[ℤ_[ℓ]] St) (gF : G) (hF : ∀ v, s (Fs v) = ρ₀ gF *ᵥ s v)
    (FE : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) →ₗ[E] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St))
    (hFE : ∀ v, FE ((1 : ℚ_[ℓ]) ⊗ₜ v) = (1 : ℚ_[ℓ]) ⊗ₜ Fs v)
    (hgF : ∀ v ∈ Representation.invariants ((matrixRepresentation τ).comp I.subtype),
      Matrix.toLin' ((τ gF : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) v ∈
        Representation.invariants ((matrixRepresentation τ).comp I.subtype)) :
    ∃ sp : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) →ₗ[E]
        Representation.invariants ((matrixRepresentation τ).comp I.subtype),
      Function.Injective sp ∧
      sp ∘ₗ FE = (Matrix.toLin' ((τ gF : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)).restrict hgF ∘ₗ
        sp := by
  classical
  set sQ := rationalIntegralMap (r := r) s with hsQ
  let coe : (Fin r → ℤ_[ℓ]) → (Fin r → ℚ_[ℓ]) := fun w i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (w i)
  have hcoe_mulVec : ∀ (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (w : Fin r → ℤ_[ℓ]),
      coe (A *ᵥ w) = A.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) *ᵥ coe w := fun A w =>
    funext fun i => RingHom.map_mulVec (algebraMap ℤ_[ℓ] ℚ_[ℓ]) A w i
  have hcoe_inj : Function.Injective coe := fun w w' h => funext fun i =>
    IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ] (congrFun h i)
  have hcoe_smul : ∀ (c : ℤ_[ℓ]) (w : Fin r → ℤ_[ℓ]),
      coe (c • w) = algebraMap ℤ_[ℓ] ℚ_[ℓ] c • coe w := fun c w => funext fun i => by
    simp only [coe, Pi.smul_apply, smul_eq_mul, map_mul]
  have hsQ1 : ∀ v, sQ ((1 : ℚ_[ℓ]) ⊗ₜ v) = coe (s v) := fun v => by
    rw [hsQ, rationalIntegralMap_tmul, one_smul]
  -- the `ℚ_ℓ`-linear map `Φ₀ = equiv ∘ Q ∘ sQ`
  let Φ₀ : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) →ₗ[ℚ_[ℓ]] (Fin m → E) :=
    (restrictScalarsEquiv b m).toLinearMap ∘ₗ Matrix.mulVecLin Qm ∘ₗ sQ
  have hΦ₀ : ∀ z, Φ₀ z = restrictScalarsEquiv b m (Qm *ᵥ sQ z) := fun _ => rfl
  have hPQv : ∀ w : Fin r → ℚ_[ℓ], Pm *ᵥ (Qm *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  -- a matrix `A` with `Q A P = Res_b N` is carried to `N`
  have hconj : ∀ (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]) (Nm : Matrix (Fin m) (Fin m) E),
      Qm * A * Pm = restrictScalarsMatrix b Nm → ∀ w,
        restrictScalarsEquiv b m (Qm *ᵥ (A *ᵥ w)) = Nm *ᵥ restrictScalarsEquiv b m (Qm *ᵥ w) := by
    intro A Nm h w
    rw [← restrictScalarsEquiv_mulVec, ← h, ← Matrix.mulVec_mulVec, hPQv, ← Matrix.mulVec_mulVec]
  -- every `z` is `σ⁻¹ ⊗ v`
  have hσ : ∀ z, ∃ (σ : ℤ_[ℓ]) (v : St), σ ≠ 0 ∧
      algebraMap ℤ_[ℓ] ℚ_[ℓ] σ • z = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v :=
    exists_algebraMap_smul_eq_one_tmul_padic
  have hσne : ∀ σ : ℤ_[ℓ], σ ≠ 0 → algebraMap ℤ_[ℓ] ℚ_[ℓ] σ ≠ 0 := fun σ hσ h =>
    hσ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ] (h.trans (map_zero _).symm))
  have hℓne : ∀ k : ℕ, ((ℓ : ℚ_[ℓ]) ^ k) ≠ 0 := fun k =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  -- two maps commuting with `ℚ_ℓ`-scalars and agreeing on every `1 ⊗ v` agree
  have hext : ∀ {f g : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) → (Fin m → E)},
      (∀ (c : ℚ_[ℓ]) z, f (c • z) = c • f z) → (∀ (c : ℚ_[ℓ]) z, g (c • z) = c • g z) →
      (∀ v, f ((1 : ℚ_[ℓ]) ⊗ₜ v) = g ((1 : ℚ_[ℓ]) ⊗ₜ v)) → ∀ z, f z = g z := by
    intro f g hf hg h z
    obtain ⟨σ, v, hσ0, hz⟩ := hσ z
    refine smul_right_injective _ (hσne σ hσ0) ?_
    change algebraMap ℤ_[ℓ] ℚ_[ℓ] σ • f z = algebraMap ℤ_[ℓ] ℚ_[ℓ] σ • g z
    rw [← hf, ← hg, hz, h]
  -- the action of `o ∈ O`
  have hΦO : ∀ (o : O) z, Φ₀ (algebraMap O E o • z) = algebraMap O E o • Φ₀ z := by
    refine fun o => hext (fun c z => by rw [smul_comm, map_smul])
      (fun c z => by rw [map_smul, smul_comm]) fun v => ?_
    have h : coe (s (act o v)) =
        (((ℓ : ℚ_[ℓ]) ^ N)⁻¹ • (Mo o).map (algebraMap ℤ_[ℓ] ℚ_[ℓ])) *ᵥ coe (s v) := by
      rw [Matrix.smul_mulVec, ← hcoe_mulVec, ← hO, hcoe_smul, map_pow, map_natCast, smul_smul,
        inv_mul_cancel₀ (hℓne N), one_smul]
    rw [hact, hΦ₀, hΦ₀, hsQ1, hsQ1, h, hconj _ _ (hα o)]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  -- `E`-linearity
  have hΦE : ∀ (e : E) z, Φ₀ (e • z) = e • Φ₀ z := by
    intro e z
    obtain ⟨⟨o, ⟨_, k, rfl⟩⟩, he⟩ := IsLocalization.mk'_surjective (Submonoid.powers (ℓ : O)) e
    have hℓk : algebraMap O E ((ℓ : O) ^ k) = algebraMap ℚ_[ℓ] E ((ℓ : ℚ_[ℓ]) ^ k) := by
      simp only [map_pow, map_natCast]
    have hmul : algebraMap ℚ_[ℓ] E ((ℓ : ℚ_[ℓ]) ^ k) * e = algebraMap O E o := by
      rw [← he, ← hℓk]
      exact IsLocalization.mk'_spec' (M := Submonoid.powers (ℓ : O)) E o ⟨(ℓ : O) ^ k, k, rfl⟩
    refine smul_right_injective _ (hℓne k) ?_
    change ((ℓ : ℚ_[ℓ]) ^ k) • Φ₀ (e • z) = ((ℓ : ℚ_[ℓ]) ^ k) • (e • Φ₀ z)
    rw [← Φ₀.map_smul, ← algebraMap_smul E ((ℓ : ℚ_[ℓ]) ^ k) (e • z), smul_smul, hmul, hΦO,
      ← algebraMap_smul E ((ℓ : ℚ_[ℓ]) ^ k) (e • Φ₀ z), smul_smul, hmul]
  -- invariance
  have hΦI : ∀ g ∈ I, ∀ z, (τ g : Matrix (Fin m) (Fin m) E) *ᵥ Φ₀ z = Φ₀ z := fun g hg =>
    hext (fun c z => by rw [map_smul, Matrix.mulVec_smul]) (fun _ _ => map_smul Φ₀ _ _)
      fun v => by rw [hΦ₀, hsQ1, ← hconj _ _ (hτ g), ← hcoe_mulVec, hinv v g hg]
  -- the Frobenius
  have hΦF : ∀ z, Φ₀ (FE z) = (τ gF : Matrix (Fin m) (Fin m) E) *ᵥ Φ₀ z :=
    hext (fun c z => by rw [FE.map_smul_of_tower, map_smul])
      (fun c z => by rw [map_smul, Matrix.mulVec_smul]) fun v => by
        rw [hFE, hΦ₀, hΦ₀, hsQ1, hsQ1, hF, hcoe_mulVec, hconj _ _ (hτ gF)]
  -- injectivity
  have hΦinj : Function.Injective Φ₀ := by
    refine (injective_iff_map_eq_zero Φ₀).2 fun z hz0 => ?_
    obtain ⟨σ, v, hσ0, hz⟩ := hσ z
    have h1 : sQ z = 0 := by
      rw [hΦ₀, LinearEquiv.map_eq_zero_iff] at hz0
      rw [← hPQv (sQ z), hz0, Matrix.mulVec_zero]
    have h2' : coe (s v) = 0 := by
      rw [← hsQ1, ← hz, sQ.map_smul, h1, smul_zero]
    have h2 : s v = 0 := hcoe_inj (h2'.trans (funext fun i => (map_zero _).symm))
    have h3 : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) = 0 := by
      have : ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] v) =
          ((ℓ : ℚ_[ℓ]) ^ M)⁻¹ ⊗ₜ[ℤ_[ℓ]] ((ℓ ^ M : ℤ_[ℓ]) • v) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, map_natCast,
          mul_inv_cancel₀ (hℓne M)]
      rw [this, hker v h2, TensorProduct.tmul_zero]
    rw [h3] at hz
    exact (smul_eq_zero.1 hz).resolve_left (hσne σ hσ0)
  -- assemble
  let Φ : (ℚ_[ℓ] ⊗[ℤ_[ℓ]] St) →ₗ[E] (Fin m → E) :=
    { Φ₀ with map_smul' := hΦE }
  have hmem : ∀ z, Φ z ∈ Representation.invariants ((matrixRepresentation τ).comp I.subtype) :=
    fun z h => by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, matrixRepresentation_apply]
      exact hΦI h.1 h.2 z
  refine ⟨Φ.codRestrict _ hmem, fun z z' h => hΦinj (congrArg Subtype.val h), ?_⟩
  exact LinearMap.ext fun z => Subtype.ext <| (hΦF z).trans (Matrix.toLin'_apply _ _).symm

end Main

end Stacks.EtaleCohomology

end
