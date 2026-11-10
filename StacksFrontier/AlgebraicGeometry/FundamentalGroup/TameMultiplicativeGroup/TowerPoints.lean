module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.KummerTower

/-!
# The covers, base points and transition maps of the Kummer tower

For the Kummer tower of `𝐆_{m,k}` (`AlgebraicGeometry.TameMultiplicativeGroup.towerData`) this file
defines the tame covers `K_m = Spec 𝔽_{m!}[X]_X`, `x ↦ X^{N_m}`, the base points
`k₀^{(m)} : 𝔽_{m!}[X]_X → Ω`, `X ↦ t_m`, compatible with the base map of `𝐆_m` and injective
(`t_m` is transcendental), and the transition maps `T_m : 𝔽_{m!}[X]_X → 𝔽_{(m+1)!}[X]_X`,
`X ↦ X^{N_{m+1}/N_m}`, with `k₀^{(m+1)} ∘ T_m = k₀^{(m)}`.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.towerCover k m`: the tame cover `K_m`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerPoint k m`: the base point `k₀^{(m)}`.
* `AlgebraicGeometry.TameMultiplicativeGroup.towerTransition k m`: the transition `T_m`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

/-- A ring map out of `F[X]_X` into a domain is injective as soon as it is injective on `F[X]`. -/
theorem injective_of_injective_comp_algebraMap {F L : Type*} [Field F] [CommRing L]
    [IsDomain L] (g : Ring F →+* L) (hg : Function.Injective (g.comp (algebraMap F[X] (Ring F)))) :
    Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (X : F[X])) z
  rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul] at hz
  have hu : IsUnit (g (IsLocalization.mk' (Ring F) (1 : F[X]) s)) :=
    (IsUnit.of_mul_eq_one _ (by rw [IsLocalization.mk'_spec, map_one] :
      IsLocalization.mk' (Ring F) (1 : F[X]) s * algebraMap F[X] (Ring F) s = 1)).map g
  have hp : p = 0 := hg (by rw [RingHom.comp_apply, hu.mul_left_eq_zero.mp hz, map_zero])
  rw [hp, IsLocalization.mk'_zero]

variable (k : Type u) [Field k] [Fintype k]

/-- Two ring maps out of `F[X]_X` agreeing on constants and on `X` are equal. -/
private theorem ringHom_ext_away {F S : Type*} [Field F] [CommRing S] {f g : Ring F →+* S}
    (hC : ∀ a : F, f (algebraMap F[X] (Ring F) (C a)) = g (algebraMap F[X] (Ring F) (C a)))
    (hX : f (coord F) = g (coord F)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (X : F[X])) (Polynomial.ringHom_ext hC hX)

/-- The field `𝔽_{m!} ⊆ Ω` of the `m`-th layer. -/
abbrev towerField (m : ℕ) : IntermediateField k (Omega k) := frobField k m.factorial

/-- The root of unity `ζ_m` lies in `𝔽_{m!}`. -/
theorem towerZeta_mem (m : ℕ) : towerZeta k m ∈ towerField k m :=
  mem_frobField_of_pow_eq_one k (isPrimitiveRoot_towerZeta k m).pow_eq_one

/-- **The `m`-th cover of the Kummer tower**, `K_m = Spec 𝔽_{m!}[X]_X ⟶ 𝐆_{m,k}`,
`x ↦ X^{N_m}`, as a tame cover. -/
def towerCover (m : ℕ) : TameCover k :=
  ⟨kummerCover k (towerField k m) (towerN k m) (isUnit_towerN k m) (towerN_pos k m),
    isTameCover_kummerCover k _ _ _ _⟩

/-- **The base point** `k₀^{(m)} : 𝔽_{m!}[X]_X → Ω`, the identity on constants and `X ↦ t_m`. -/
def towerPoint (m : ℕ) : Ring (towerField k m) →+* Omega k :=
  IsLocalization.Away.lift (X : (towerField k m)[X])
    (g := eval₂RingHom (algebraMap (towerField k m) (Omega k)) (towerRoot k m))
    (by rw [coe_eval₂RingHom, eval₂_X]; exact (towerRoot_ne_zero k m).isUnit)

/-- On a polynomial `p ∈ 𝔽_{m!}[X]`, the base point `k₀^{(m)}` evaluates `p` at `t_m`. -/
theorem towerPoint_algebraMap (m : ℕ) (p : (towerField k m)[X]) :
    towerPoint k m (algebraMap _ (Ring (towerField k m)) p) =
      eval₂ (algebraMap (towerField k m) (Omega k)) (towerRoot k m) p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The base point `k₀^{(m)}` sends the coordinate `X` to `t_m`. -/
theorem towerPoint_coord (m : ℕ) : towerPoint k m (coord (towerField k m)) = towerRoot k m := by
  rw [coord, towerPoint_algebraMap, eval₂_X]

/-- The base point `k₀^{(m)}` is the identity on the constants `𝔽_{m!}`. -/
theorem towerPoint_const (m : ℕ) (a : towerField k m) :
    towerPoint k m (algebraMap (towerField k m) (Ring (towerField k m)) a) = a := by
  rw [IsScalarTower.algebraMap_apply (towerField k m) (towerField k m)[X] (Ring (towerField k m)),
    towerPoint_algebraMap, ← C_eq_algebraMap, eval₂_C]
  rfl

/-- The base points are compatible with the base map of `𝐆_m`. -/
theorem towerPoint_comp_kummerMap (m : ℕ) :
    (towerPoint k m).comp (kummerMap k (towerField k m) (towerN k m)) = baseHom k := by
  refine ringHom_ext_away (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, kummerMap_C, towerPoint_algebraMap, eval₂_C, algebraMap_C,
      ← algebraMap_omega, ← IsScalarTower.algebraMap_apply]
  · change towerPoint k m (kummerMap k (towerField k m) (towerN k m) (coord k)) = xΩ k
    rw [kummerMap_coord, map_pow, towerPoint_coord, towerRoot_pow]

/-- For `z ∈ k[X]_X`, the base point `k₀^{(m)}` applied to the image of `z` under the Kummer map
`k[X]_X → 𝔽_{m!}[X]_X`, `X ↦ X^{N_m}`, is the image of `z` under the base map of `𝐆_m`. -/
theorem towerPoint_kummerMap (m : ℕ) (z : Ring k) :
    towerPoint k m (kummerMap k (towerField k m) (towerN k m) z) = baseHom k z :=
  RingHom.congr_fun (towerPoint_comp_kummerMap k m) z

/-- `t_m` is transcendental over `𝔽_{m!}`. -/
theorem transcendental_towerRoot (m : ℕ) : Transcendental (towerField k m) (towerRoot k m) := by
  intro h
  apply transcendental_xΩ k
  rw [← towerRoot_pow k m]
  exact (h.restrictScalars k : IsAlgebraic k (towerRoot k m)).pow _

/-- **The base points are injective.** -/
theorem towerPoint_injective (m : ℕ) : Function.Injective (towerPoint k m) := by
  refine injective_of_injective_comp_algebraMap _ ?_
  have : (towerPoint k m).comp (algebraMap _ (Ring (towerField k m))) =
      (aeval (towerRoot k m) : (towerField k m)[X] →ₐ[towerField k m] Omega k).toRingHom := by
    refine RingHom.ext fun p ↦ ?_
    rw [RingHom.comp_apply, towerPoint_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_def]
  rw [this]
  exact (transcendental_iff_injective).mp (transcendental_towerRoot k m)

/-- The inclusion `𝔽_{m!} ⊆ 𝔽_{(m+1)!}`. -/
def towerIncl (m : ℕ) : towerField k m →+* towerField k (m + 1) :=
  (IntermediateField.inclusion
    (frobField_mono k (Nat.factorial_dvd_factorial (Nat.le_succ m)))).toRingHom

/-- The inclusion `𝔽_{m!} ⊆ 𝔽_{(m+1)!}` is the identity on underlying elements of `Ω`. -/
theorem coe_towerIncl (m : ℕ) (a : towerField k m) : (towerIncl k m a : Omega k) = a := rfl

/-- **The transition** `T_m : 𝔽_{m!}[X]_X → 𝔽_{(m+1)!}[X]_X`, `X ↦ X^{N_{m+1}/N_m}`. -/
def towerTransition (m : ℕ) : Ring (towerField k m) →+* Ring (towerField k (m + 1)) :=
  IsLocalization.Away.lift (X : (towerField k m)[X])
    (g := (algebraMap _ (Ring (towerField k (m + 1)))).comp
      (eval₂RingHom (C.comp (towerIncl k m)) (X ^ towerRatio k m)))
    (by
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, map_pow]
      exact (isUnit_coord _).pow _)

/-- On a polynomial `p ∈ 𝔽_{m!}[X]`, the transition `T_m` substitutes `X^{N_{m+1}/N_m}` for
`X` in `p`. -/
theorem towerTransition_algebraMap (m : ℕ) (p : (towerField k m)[X]) :
    towerTransition k m (algebraMap _ (Ring (towerField k m)) p) =
      algebraMap _ (Ring (towerField k (m + 1)))
        (eval₂ (C.comp (towerIncl k m)) (X ^ towerRatio k m) p) :=
  IsLocalization.Away.lift_eq _ _ p

/-- **The base points are compatible with the transitions.** -/
theorem towerPoint_comp_transition (m : ℕ) :
    (towerPoint k (m + 1)).comp (towerTransition k m) = towerPoint k m := by
  refine ringHom_ext_away (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, towerTransition_algebraMap, eval₂_C, RingHom.comp_apply,
      towerPoint_algebraMap, eval₂_C, towerPoint_algebraMap, eval₂_C]
    rfl
  · rw [RingHom.comp_apply, towerTransition_algebraMap, eval₂_X, map_pow, map_pow,
      towerPoint_algebraMap, towerPoint_algebraMap, eval₂_X, eval₂_X, towerRoot_succ_pow]

/-- `k₀^{(m+1)}(T_m(z)) = k₀^{(m)}(z)` for every `z ∈ 𝔽_{m!}[X]_X`. -/
theorem towerPoint_transition (m : ℕ) (z : Ring (towerField k m)) :
    towerPoint k (m + 1) (towerTransition k m z) = towerPoint k m z :=
  RingHom.congr_fun (towerPoint_comp_transition k m) z

/-- The images of the base points increase. -/
theorem range_towerPoint_le (m : ℕ) : (towerPoint k m).range ≤ (towerPoint k (m + 1)).range := by
  rintro _ ⟨z, rfl⟩
  exact ⟨towerTransition k m z, towerPoint_transition k m z⟩

/-- The image of `k₀^{(m)}` is contained in that of `k₀^{(m')}` whenever `m ≤ m'`. -/
theorem range_towerPoint_mono {m m' : ℕ} (h : m ≤ m') :
    (towerPoint k m).range ≤ (towerPoint k m').range := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (range_towerPoint_le k _)

end AlgebraicGeometry.TameMultiplicativeGroup

end
