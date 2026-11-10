module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.AwayUnramified
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.BoundaryUnramified
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ClassificationField
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.DeckProperties
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.TowerPoints

/-!
# A tame cover of `𝐆_m` is unramified over `𝐏¹` after a Kummer base change

Let `C` be a finite formally unramified `k[x]_x`-algebra, tame at `0` and at `∞`, and
`ψ : C → Ω` a point over the geometric generic point. At the layer `m` of the Kummer tower put
`F = 𝔽_{m!}`, `K'' = F(t_m)` with generator `s = t_m` (`s^{N_m} = x`), and `N = K''(ψ(C))`.
For `m` with the ramification indices at `0` and `∞` dividing `N_m`, the integral closures of
`F[s]` and of `F[s⁻¹]` in `N` are unramified at every prime: at the primes containing `s`
(resp. `s⁻¹`) by Abhyankar's lemma at `0` (resp. at `∞`, after the inversion `x ↦ x⁻¹`), and at
the others because `C` is unramified over `k[x]_x`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.exists_level_forall_isUnramifiedAt`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial IntermediateField

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

attribute [local instance high] localAwayAlgebra localAwayToAlgebra

attribute [local instance 20000] integralClosureAlgebraOfBase

variable (k : Type u) [Field k]

/-- `x ↦ w` for a unit `w`, as a ring map `k[x]_x → R`. -/
def awayLift {R : Type*} [CommRing R] (ι₀ : k →+* R) (w : Rˣ) : Ring k →+* R :=
  IsLocalization.Away.lift (X : k[X]) (g := eval₂RingHom ι₀ (w : R))
    (by rw [coe_eval₂RingHom, eval₂_X]; exact w.isUnit)

/-- `awayLift k ι₀ w` sends a polynomial `p` to its evaluation `p(w)` along `ι₀`. -/
theorem awayLift_algebraMap {R : Type*} [CommRing R] (ι₀ : k →+* R) (w : Rˣ) (p : k[X]) :
    awayLift k ι₀ w (algebraMap k[X] (Ring k) p) = eval₂ ι₀ (w : R) p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The base map `k[x]_x → Ω` sends a constant `a` to its image in `Ω`. -/
theorem baseHom_algebraMap_C (a : k) :
    baseHom k (algebraMap k[X] (Ring k) (C a)) = algebraMap k (Omega k) a := by
  rw [algebraMap_omega, IsScalarTower.algebraMap_apply k k[X] (Ring k), C_eq_algebraMap]

/-- A ring map `k[x]_x → R` composed with `R → Ω` is the base map when it sends `x` to `x`. -/
theorem comp_awayLift {R : Type*} [CommRing R] (ι₀ : k →+* R) (w : Rˣ) (ι : R →+* Omega k)
    (h₀ : ∀ a, ι (ι₀ a) = algebraMap k (Omega k) a) (hw : ι w = xΩ k) :
    ι.comp (awayLift k ι₀ w) = baseHom k := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : k[X]))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [awayLift_algebraMap, eval₂_C, h₀, baseHom_algebraMap_C]
  · simp only [RingHom.comp_apply]
    rw [awayLift_algebraMap, eval₂_X, hw]

/-- The base map `k[x]_x → Ω` sends `x⁻¹` to `(xΩ k)⁻¹`. -/
theorem baseHom_invSelf :
    baseHom k (IsLocalization.Away.invSelf (X : k[X])) = (xΩ k)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [xΩ, coord, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one])

/-- Composing the inversion `x ↦ x⁻¹` with the base map evaluates a polynomial at `(xΩ k)⁻¹`. -/
theorem baseHom_inversionHom_algebraMap (r : k[X]) :
    baseHom k (inversionHom k (algebraMap k[X] (Ring k) r)) = aeval (xΩ k)⁻¹ r := by
  rw [inversionHom_algebraMap, inverseCoordinate, coe_eval₂RingHom, hom_eval₂, baseHom_invSelf,
    aeval_def]
  rfl

/-- The inversion `x ↦ x⁻¹` of `k[x]_x` is surjective. -/
theorem inversionHom_surjective : Function.Surjective (inversionHom k) :=
  fun z ↦ ⟨inversionHom k z, inversionHom_inversionHom k z⟩

/-- The inverse `(xΩ k)⁻¹` of the coordinate is transcendental over `k`. -/
theorem transcendental_xΩ_inv : Transcendental k (xΩ k)⁻¹ :=
  fun h ↦ transcendental_xΩ k (IsAlgebraic.inv_iff.mp h)

variable [Fintype k]

/-- The function field `F(t_m)` of the `m`-th layer, `F = 𝔽_{m!}`. -/
abbrev levelField (m : ℕ) : IntermediateField (towerField k m) (Omega k) :=
  (towerField k m)⟮towerRoot k m⟯

/-- The generator `s = t_m` of the `m`-th layer. -/
abbrev levelGen (m : ℕ) : levelField k m := AdjoinSimple.gen _ _

/-- The field `N = F(t_m)(ψ(C))` of a point at the `m`-th layer. -/
abbrev coverField {C : Type*} [CommRing C] (m : ℕ) (ψ : C →+* Omega k) :
    IntermediateField (levelField k m) (Omega k) :=
  IntermediateField.adjoin (levelField k m) (Set.range ψ)

/-- The generator `s = t_m` of the `m`-th layer is nonzero. -/
theorem levelGen_ne_zero (m : ℕ) : levelGen k m ≠ 0 := fun h ↦
  towerRoot_ne_zero k m (congrArg Subtype.val h)

/-- The generator `s = t_m` is transcendental over `F = 𝔽_{m!}`. -/
theorem transcendental_levelGen (m : ℕ) : Transcendental (towerField k m) (levelGen k m) :=
  (transcendental_algebraMap_iff (algebraMap (levelField k m) (Omega k)).injective).mp
    (transcendental_towerRoot k m)

/-- The inverse `s⁻¹` of the generator is transcendental over `F = 𝔽_{m!}`. -/
theorem transcendental_levelGen_inv (m : ℕ) :
    Transcendental (towerField k m) (levelGen k m)⁻¹ :=
  fun h ↦ transcendental_levelGen k m (IsAlgebraic.inv_iff.mp h)

/-- `F(s)` is the fraction field of `F[s]`. -/
instance (m : ℕ) :
    IsFractionRing (Algebra.adjoin (towerField k m) {levelGen k m}) (levelField k m) :=
  isFractionRing_adjoin_gen _

/-- `F(s)` is the fraction field of `F[s⁻¹]`. -/
instance (m : ℕ) :
    IsFractionRing (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) (levelField k m) :=
  isFractionRing_adjoin_inv (levelGen_ne_zero k m)

/-- The generator satisfies `s ^ N_m = x` in `Ω`. -/
theorem levelGen_pow (m : ℕ) :
    ((levelGen k m : levelField k m) : Omega k) ^ towerN k m = xΩ k :=
  towerRoot_pow k m

/-- The inverse generator satisfies `(s⁻¹) ^ N_m = x⁻¹` in `Ω`. -/
theorem levelGen_inv_pow (m : ℕ) :
    (((levelGen k m)⁻¹ : levelField k m) : Omega k) ^ towerN k m = (xΩ k)⁻¹ := by
  rw [IntermediateField.coe_inv, inv_pow, levelGen_pow]

omit [Fintype k] in
/-- The characteristic of a finite field is prime. -/
theorem prime_ringChar [Finite k] : (ringChar k).Prime := by
  have := Fintype.ofFinite k
  have := ringChar.charP k
  obtain ⟨_, hp, -⟩ := FiniteField.card k (ringChar k)
  exact hp

/-- The characteristic of `k` is coprime to the exponent `N_m` of every layer. -/
theorem coprime_ringChar_towerN (m : ℕ) : (ringChar k).Coprime (towerN k m) := by
  refine (Nat.Prime.coprime_iff_not_dvd (prime_ringChar k)).mpr fun hdvd ↦ ?_
  have := ringChar.charP k
  have h := (CharP.cast_eq_zero_iff k (ringChar k) _).mpr hdvd
  rw [natCast_towerN k (R := k) m] at h
  exact one_ne_zero (neg_eq_zero.mp h)

/-- A natural number coprime to the characteristic of `k` is coprime to the cardinality of `k`. -/
theorem coprime_card_of_coprime_ringChar {n : ℕ} (h : (ringChar k).Coprime n) :
    (Fintype.card k).Coprime n := by
  have := ringChar.charP k
  obtain ⟨_, -, hcard⟩ := FiniteField.card k (ringChar k)
  rw [hcard]
  exact Nat.Coprime.pow_left _ h

section Cover

variable {k} {C : Type u} [CommRing C] (φ : Ring k →+* C) (hfin : φ.Finite)
  (hfu : φ.FormallyUnramified) (ψ : C →+* Omega k) (hψ : ψ.comp φ = baseHom k)

include hfin hfu hψ in
/-- There is `E₀ ≠ 0` coprime to the characteristic such that, at every layer `m` with `E₀ ∣ N_m`,
the integral closure of `F[s]` in `N` is unramified at every prime containing `s`. -/
theorem exists_forall_level_isUnramifiedAt_zero
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
      (Spec.map (CommRingCat.ofHom φ))) :
    ∃ E₀ : ℕ, E₀ ≠ 0 ∧ (ringChar k).Coprime E₀ ∧ ∀ m, E₀ ∣ towerN k m →
      ∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m})
        (coverField k m ψ))) [P.IsPrime],
        algebraMap (Algebra.adjoin (towerField k m) {levelGen k m})
          (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m}) (coverField k m ψ))
          (adjoinGen (towerField k m) (levelGen k m)) ∈ P →
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {levelGen k m}) P := by
  have hψ' : ∀ r : k[X], ψ (φ (algebraMap k[X] (Ring k) r)) = aeval (xΩ k) r := fun r ↦ by
    rw [aeval_xΩ, ← hψ, RingHom.comp_apply]
  obtain ⟨E₀, hE₀, hcop, H⟩ :=
    exists_forall_isUnramifiedAt_of_tame φ hfin hfu htame ψ (transcendental_xΩ k) hψ'
  exact ⟨E₀, hE₀, hcop, fun m hm P _ hP ↦ H (towerN k m) hm (coprime_ringChar_towerN k m)
    (towerField k m) (levelField k m) (levelGen k m) (transcendental_levelGen k m)
    (levelGen_pow k m) (coverField k m ψ) rfl P hP⟩

include hfin hfu hψ in
/-- There is `E₁ ≠ 0` coprime to the characteristic such that, at every layer `m` with `E₁ ∣ N_m`,
the integral closure of `F[s⁻¹]` in `N` is unramified at every prime containing `s⁻¹`. -/
theorem exists_forall_level_isUnramifiedAt_infty
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k)
      (Spec.map (CommRingCat.ofHom φ))) :
    ∃ E₁ : ℕ, E₁ ≠ 0 ∧ (ringChar k).Coprime E₁ ∧ ∀ m, E₁ ∣ towerN k m →
      ∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
        (coverField k m ψ))) [P.IsPrime],
        algebraMap (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
          (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
            (coverField k m ψ))
          (adjoinGen (towerField k m) (levelGen k m)⁻¹) ∈ P →
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) P := by
  have hψ' : ∀ r : k[X], ψ ((φ.comp (inversionHom k)) (algebraMap k[X] (Ring k) r)) =
      aeval (xΩ k)⁻¹ r := fun r ↦ by
    rw [RingHom.comp_apply, ← RingHom.comp_apply ψ φ, hψ, baseHom_inversionHom_algebraMap]
  have hfin' : (φ.comp (inversionHom k)).Finite :=
    hfin.comp (RingHom.Finite.of_surjective _ (inversionHom_surjective k))
  have hfu' : (φ.comp (inversionHom k)).FormallyUnramified :=
    RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective
      (inversionHom_surjective k)) hfu
  obtain ⟨E₁, hE₁, hcop, H⟩ := exists_forall_isUnramifiedAt_of_tame (φ.comp (inversionHom k))
    hfin' hfu' ((isTamelyRamifiedInCodimensionOne_chartInfty_iff φ).mp htame) ψ
    (transcendental_xΩ_inv k) hψ'
  exact ⟨E₁, hE₁, hcop, fun m hm P _ hP ↦ H (towerN k m) hm (coprime_ringChar_towerN k m)
    (towerField k m) (levelField k m) (levelGen k m)⁻¹ (transcendental_levelGen_inv k m)
    (levelGen_inv_pow k m) (coverField k m ψ) rfl P hP⟩

/-- The integral closure of `F[s]` in `N` is unramified at every prime not containing `s`, when
`s` is transcendental and `F[s, s⁻¹]` contains a unit mapping to `x`. -/
private theorem isUnramifiedAt_of_not_mem_of_unit (φ : Ring k →+* C) (hfin : φ.Finite)
    (hfu : φ.FormallyUnramified) (ψ : C →+* Omega k) (hψ : ψ.comp φ = baseHom k)
    (m : ℕ) {s : levelField k m}
    (hs : Transcendental (towerField k m) s)
    [IsFractionRing (Algebra.adjoin (towerField k m) {s}) (levelField k m)]
    (w : (localAway hs)ˣ) (hw : (((w : localAway hs) : levelField k m) : Omega k) = xΩ k)
    (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {s}) (coverField k m ψ)))
    [P.IsPrime]
    (hP : algebraMap (Algebra.adjoin (towerField k m) {s})
      (integralClosure (Algebra.adjoin (towerField k m) {s}) (coverField k m ψ))
      (adjoinGen (towerField k m) s) ∉ P) :
    Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {s}) P := by
  let ι₀ : k →+* localAway hs :=
    (algebraMap (Algebra.adjoin (towerField k m) {s}) _).comp
      ((algebraMap (towerField k m) (Algebra.adjoin (towerField k m) {s})).comp
        (algebraMap k (towerField k m)))
  let ι : localAway hs →+* Omega k :=
    (algebraMap (levelField k m) (Omega k)).comp (localAway hs).val.toRingHom
  exact isUnramifiedAt_of_cover_of_not_mem hs φ hfin hfu ψ (awayLift k ι₀ w)
    (fun z ↦ (RingHom.congr_fun (comp_awayLift k ι₀ w ι (fun _ ↦ rfl) hw) z).trans
      (RingHom.congr_fun hψ z).symm) rfl P hP

include hfin hfu hψ in
/-- At every layer, the integral closure of `F[s]` in `N` is unramified at every prime not
containing `s`. -/
theorem isUnramifiedAt_level_of_not_mem (m : ℕ)
    (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m})
      (coverField k m ψ))) [P.IsPrime]
    (hP : algebraMap (Algebra.adjoin (towerField k m) {levelGen k m})
      (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m}) (coverField k m ψ))
      (adjoinGen (towerField k m) (levelGen k m)) ∉ P) :
    Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {levelGen k m}) P := by
  have := isLocalization_localAway (transcendental_levelGen k m)
  refine isUnramifiedAt_of_not_mem_of_unit φ hfin hfu ψ hψ m (transcendental_levelGen k m)
    (IsLocalization.map_units (M := Submonoid.powers (adjoinGen (towerField k m) (levelGen k m)))
      (localAway (transcendental_levelGen k m))
      ⟨adjoinGen (towerField k m) (levelGen k m) ^ towerN k m, towerN k m, rfl⟩).unit ?_ P hP
  rw [IsUnit.unit_spec]
  change (((adjoinGen (towerField k m) (levelGen k m) ^ towerN k m :
    Algebra.adjoin (towerField k m) {levelGen k m}) : levelField k m) : Omega k) = xΩ k
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  exact levelGen_pow k m

include hfin hfu hψ in
/-- At every layer, the integral closure of `F[s⁻¹]` in `N` is unramified at every prime not
containing `s⁻¹`. -/
theorem isUnramifiedAt_level_inv_of_not_mem (m : ℕ)
    (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
      (coverField k m ψ))) [P.IsPrime]
    (hP : algebraMap (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
      (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) (coverField k m ψ))
      (adjoinGen (towerField k m) (levelGen k m)⁻¹) ∉ P) :
    Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) P := by
  have := isLocalization_localAway (transcendental_levelGen_inv k m)
  let u := (IsLocalization.map_units
    (M := Submonoid.powers (adjoinGen (towerField k m) (levelGen k m)⁻¹))
    (localAway (transcendental_levelGen_inv k m))
    ⟨adjoinGen (towerField k m) (levelGen k m)⁻¹ ^ towerN k m, towerN k m, rfl⟩).unit
  refine isUnramifiedAt_of_not_mem_of_unit φ hfin hfu ψ hψ m (transcendental_levelGen_inv k m)
    u⁻¹ ((map_units_inv ((algebraMap (levelField k m) (Omega k)).comp
      (localAway _).val.toRingHom) u).trans ?_) P hP
  change ((((adjoinGen (towerField k m) (levelGen k m)⁻¹ ^ towerN k m :
    Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) : levelField k m) : Omega k))⁻¹ = xΩ k
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, levelGen_inv_pow, inv_inv]

include hfin hfu hψ in
/-- For a cover tame at `0` and at `∞`, there is a layer `m` at which the integral closures of
`F[s]` and of `F[s⁻¹]` in `N` are unramified at every prime. -/
theorem exists_level_forall_isUnramifiedAt
    (h₀ : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
      (Spec.map (CommRingCat.ofHom φ)))
    (h₁ : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k)
      (Spec.map (CommRingCat.ofHom φ))) :
    ∃ m, (∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m})
        (coverField k m ψ))) [P.IsPrime],
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {levelGen k m}) P) ∧
      ∀ (P : Ideal (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
        (coverField k m ψ))) [P.IsPrime],
        Algebra.IsUnramifiedAt (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹}) P := by
  obtain ⟨E₀, hE₀, hcop₀, H₀⟩ := exists_forall_level_isUnramifiedAt_zero φ hfin hfu ψ hψ h₀
  obtain ⟨E₁, hE₁, hcop₁, H₁⟩ := exists_forall_level_isUnramifiedAt_infty φ hfin hfu ψ hψ h₁
  obtain ⟨m, hm⟩ := exists_dvd_towerN_of_coprime k (E₀ * E₁) (mul_ne_zero hE₀ hE₁)
    (coprime_card_of_coprime_ringChar k (Nat.Coprime.mul_right hcop₀ hcop₁))
  refine ⟨m, fun P _ ↦ ?_, fun P _ ↦ ?_⟩
  · by_cases hP : algebraMap (Algebra.adjoin (towerField k m) {levelGen k m})
        (integralClosure (Algebra.adjoin (towerField k m) {levelGen k m}) (coverField k m ψ))
        (adjoinGen (towerField k m) (levelGen k m)) ∈ P
    · exact H₀ m (dvd_of_mul_right_dvd hm) P hP
    · exact isUnramifiedAt_level_of_not_mem φ hfin hfu ψ hψ m P hP
  · by_cases hP : algebraMap (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
        (integralClosure (Algebra.adjoin (towerField k m) {(levelGen k m)⁻¹})
          (coverField k m ψ))
        (adjoinGen (towerField k m) (levelGen k m)⁻¹) ∈ P
    · exact H₁ m (dvd_of_mul_left_dvd hm) P hP
    · exact isUnramifiedAt_level_inv_of_not_mem φ hfin hfu ψ hψ m P hP

end Cover

end AlgebraicGeometry.TameMultiplicativeGroup

end
