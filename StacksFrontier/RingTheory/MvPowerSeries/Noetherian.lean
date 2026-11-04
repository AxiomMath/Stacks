module

public import Mathlib.RingTheory.PowerSeries.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal power series in finitely many variables over a Noetherian ring

Let `R` be a Noetherian commutative ring and `n : ℕ`. Then the formal power series ring
`R⟦x₁, …, xₙ⟧`, modelled as `MvPowerSeries (Fin n) R`, is Noetherian.

## Main results

* `mvPowerSeries_fin_isNoetherianRing`: `MvPowerSeries (Fin n) R` is a Noetherian ring when `R` is.

## Implementation notes

The variables are indexed by `Fin n`; this is equivalent to the version for an arbitrary finite
index type, since every finite type is in bijection with some `Fin n`.
-/

@[expose] public section

open MvPowerSeries

/-! ### The power series ring in zero variables -/

/-- The ring isomorphism `MvPowerSeries (Fin 0) R ≃+* R` given by the constant coefficient, with
inverse `r ↦ C r`. -/
private noncomputable def mvPowerSeriesFin0Equiv (R : Type*) [CommRing R] :
    MvPowerSeries (Fin 0) R ≃+* R :=
  RingEquiv.ofRingHom
    (constantCoeff (σ := Fin 0) (R := R)) (C (σ := Fin 0) (R := R))
    (by
      ext r
      simp)
    (by
      ext φ d
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [Subsingleton.elim d 0, coeff_zero_C, ← coeff_zero_eq_constantCoeff_apply])

/-! ### Reindexing the variables along an equivalence of index types -/

/-- The exponent-reindexing bijection `Finsupp.equivCongrLeft e` is additive. -/
private theorem equivCongrLeft_add {σ τ : Type*} (e : σ ≃ τ) (x y : σ →₀ ℕ) :
    Finsupp.equivCongrLeft e (x + y)
      = Finsupp.equivCongrLeft e x + Finsupp.equivCongrLeft e y := by
  simp only [Finsupp.equivCongrLeft_apply]
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_add]

-- needed: without it `reindexRingEquiv` fails (2 sites): Tactic `rewrite` failed: Did not find an
-- occurrence of the pat…
set_option backward.isDefEq.respectTransparency false in
/-- The ring isomorphism `MvPowerSeries σ R ≃+* MvPowerSeries τ R` induced by an equivalence
`e : σ ≃ τ` of index types, sending `φ` to the series whose coefficient at `d` is the coefficient
of `φ` at `(Finsupp.equivCongrLeft e).symm d`. -/
private noncomputable def reindexRingEquiv {σ τ : Type*} (R : Type*) [CommRing R] (e : σ ≃ τ) :
    MvPowerSeries σ R ≃+* MvPowerSeries τ R where
  toFun φ := fun d => φ ((Finsupp.equivCongrLeft e).symm d)
  invFun ψ := fun d => ψ ((Finsupp.equivCongrLeft e) d)
  left_inv φ := by
    funext d
    simp only [Equiv.symm_apply_apply]
  right_inv ψ := by
    funext d
    simp only [Equiv.apply_symm_apply]
  map_add' φ ψ := by funext d; rfl
  map_mul' φ ψ := by
    classical
    apply MvPowerSeries.ext
    intro d
    rw [MvPowerSeries.coeff_apply, ← MvPowerSeries.coeff_apply (φ * ψ), MvPowerSeries.coeff_mul,
      MvPowerSeries.coeff_mul]
    apply Finset.sum_nbij'
      (i := fun p => (Finsupp.equivCongrLeft e p.fst, Finsupp.equivCongrLeft e p.snd))
      (j := fun p => ((Finsupp.equivCongrLeft e).symm p.fst, (Finsupp.equivCongrLeft e).symm p.snd))
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp ⊢
      rw [← equivCongrLeft_add, hp, Equiv.apply_symm_apply]
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp ⊢
      rw [← hp, Finsupp.equivCongrLeft_symm, equivCongrLeft_add]
    · intro p hp
      exact Prod.ext (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)
    · intro p hp
      exact Prod.ext (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)
    · intro p hp
      simp only [MvPowerSeries.coeff_apply]
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### Splitting off one variable -/

/-- The exponent-splitting equivalence `Finsupp.optionEquiv` is additive. -/
private theorem optionEquiv_add {α : Type*} (x y : Option α →₀ ℕ) :
    Finsupp.optionEquiv (x + y) = Finsupp.optionEquiv x + Finsupp.optionEquiv y := by
  simp [Finsupp.optionEquiv_apply, Finsupp.some_add, Prod.add_def, Finsupp.add_apply]

/-- The inverse of the exponent-splitting equivalence respects addition: the
`none`-exponent and the `σ`-exponent add independently. -/
private theorem optionEquiv_symm_add {α : Type*} (a b : ℕ) (e g : α →₀ ℕ) :
    Finsupp.optionEquiv.symm (a, e) + Finsupp.optionEquiv.symm (b, g)
      = Finsupp.optionEquiv.symm (a + b, e + g) := by
  apply Finsupp.optionEquiv.injective
  rw [optionEquiv_add]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Prod.mk_add_mk]

-- needed: without it `optionVarSplitEquiv` fails (4 sites): unsolved goals
set_option backward.isDefEq.respectTransparency false in
/-- The ring isomorphism `MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R)` splitting
off the variable indexed by `none`, with exponent vectors over `Option σ` split as `ℕ × (σ →₀ ℕ)`
by `Finsupp.optionEquiv`. -/
private noncomputable def optionVarSplitEquiv {σ : Type*} (R : Type*) [CommRing R] :
    MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun φ := PowerSeries.mk (fun k => (fun d => φ (Finsupp.optionEquiv.symm (k, d)) : MvPowerSeries
      σ R))
  invFun ψ := fun e => (PowerSeries.coeff (Finsupp.optionEquiv e).fst ψ) (Finsupp.optionEquiv e).snd
  left_inv φ := by
    funext e; simp only [PowerSeries.coeff_mk]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv ψ := by
    apply PowerSeries.ext; intro k; apply MvPowerSeries.ext; intro d
    rw [PowerSeries.coeff_mk]; simp only [MvPowerSeries.coeff_apply]; rw [Equiv.apply_symm_apply]
  map_add' φ ψ := by
    apply PowerSeries.ext; intro k; apply MvPowerSeries.ext; intro d
    simp only [map_add, PowerSeries.coeff_mk, MvPowerSeries.coeff_apply]; rfl
  map_mul' φ ψ := by
    classical
    apply PowerSeries.ext; intro k; apply MvPowerSeries.ext; intro d
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_apply, ← MvPowerSeries.coeff_apply (φ*ψ),
      MvPowerSeries.coeff_mul]
    rw [PowerSeries.coeff_mul, map_sum]
    conv_rhs => rw [Finset.sum_congr rfl fun x _ => MvPowerSeries.coeff_mul d _ _]
    simp only [PowerSeries.coeff_mk, MvPowerSeries.coeff_apply]
    rw [Finset.sum_sigma' (Finset.antidiagonal k) (fun _ => Finset.antidiagonal d)]
    apply Finset.sum_nbij'
      (i := fun p => (⟨((Finsupp.optionEquiv p.fst).fst, (Finsupp.optionEquiv p.snd).fst),
                       ((Finsupp.optionEquiv p.fst).snd, (Finsupp.optionEquiv p.snd).snd)⟩ :
                       Σ _ : ℕ × ℕ, (σ →₀ ℕ) × (σ →₀ ℕ)))
      (j := fun x => (Finsupp.optionEquiv.symm (x.fst.fst, x.snd.fst),
                      Finsupp.optionEquiv.symm (x.fst.snd, x.snd.snd)))
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal]
      have h2 : Finsupp.optionEquiv (p.fst + p.snd) = (k, d) := by
        rw [hp, Equiv.apply_symm_apply]
      rw [optionEquiv_add] at h2
      refine ⟨?_, ?_⟩
      · have := congrArg Prod.fst h2; simpa [Prod.add_def] using this
      · have := congrArg Prod.snd h2; simpa [Prod.add_def] using this
    · intro a ha
      rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at ha
      rw [Finset.mem_antidiagonal]; simp only
      rw [optionEquiv_symm_add, ha.left, ha.right]
    · intro a ha
      simp only [Prod.mk.eta, Equiv.symm_apply_apply]
    · intro a ha
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · intro a ha
      simp only [Prod.mk.eta, Equiv.symm_apply_apply]

open MvPowerSeries in
/-- The formal power series ring in `n` variables over a Noetherian commutative ring is
Noetherian. -/
@[stacks 0306]
theorem mvPowerSeries_fin_isNoetherianRing
    (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (mvPowerSeriesFin0Equiv R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _
      ((reindexRingEquiv R (finSuccEquiv n)).trans (optionVarSplitEquiv R)).symm

end
