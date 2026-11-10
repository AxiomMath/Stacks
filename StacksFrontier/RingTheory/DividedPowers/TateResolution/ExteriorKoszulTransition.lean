module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorKoszulCompatibility
public import StacksFrontier.RingTheory.Koszul.Defs

/-! # The Koszul transition map is a morphism of divided power algebras

For a finite sequence `f₁, …, f_r` in `R` and `n ≤ m`, the Koszul complex on the `m`-th powers
maps to the Koszul complex on the `n`-th powers by scaling the `i`-th generator by `fᵢ^(m-n)`.
On the exterior algebra this transition map is `ExteriorAlgebra.map` of the diagonal
endomorphism `x ↦ c * x` of `Rʳ` with `cᵢ = fᵢ^(m-n)`, which is `LinearMap.mulLeft R c` for the
componentwise algebra structure of `Rʳ`.

Tag 0GZ4 compares a Tate resolution with two Koszul algebras at once and re-bases along these
transitions, so it needs each transition to be a morphism of *differential graded divided power*
algebras. Two of the three clauses are already available — it preserves the exterior degree by
`ExteriorAlgebra.map_mem_exteriorPower`, and it commutes with the two Koszul differentials by
`DividedPowers.TateResolution.contractLeft_exteriorAlgebraMap` together with
`DividedPowers.TateResolution.seqDual_comp_mulLeft` below. This file supplies the third, that it
preserves the divided powers of
`DividedPowers.TateResolution.exteriorDividedPowerStructure`.

The proof follows the construction of those divided powers: induction along the odd-variable
extensions `⋀[R] (Fin (r+1) → R) ≃ₐ[R] ⋀[R] ((Fin r → R) × R)`. The point that makes the
induction possible is that a *diagonal* endomorphism of `Rʳ⁺¹` splits as a diagonal endomorphism
of `Rʳ` on the coefficients and a scalar on the new coordinate, so it respects the flag of
coordinate subspaces along which the divided powers were built. The inductive step is stated for
any endomorphism of `M × R` with that shape, recorded by the two hypotheses
`L ∘ₗ inl = inl ∘ₗ l` and `L (0, 1) = (0, c)`.

## Main results

* `DividedPowers.TateResolution.exteriorDividedPowerStructure_dpow_map_mulLeft` — the divided
  powers of `⋀[R] (Fin r → R)` commute with `ExteriorAlgebra.map` of a diagonal endomorphism.
* `DividedPowers.TateResolution.exteriorProd_map_dpow` — the inductive step.
* `DividedPowers.TateResolution.seqDual_comp_mulLeft` — the diagonal endomorphism pulls the
  Koszul functional of the `n`-th powers back to that of the `m`-th powers.
* `DividedPowers.TateResolution.contraction_map_mulLeft` — consequently the transition map
  commutes with the two Koszul differentials.

## References

* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u v w

section PositiveEvenPart

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- `ExteriorAlgebra.map` preserves the positive even part. -/
public theorem map_mem_positiveEvenPart (l : M →ₗ[R] N) {u : ExteriorAlgebra R M}
    (hu : u ∈ positiveEvenPart (exteriorGrade R M)) :
    ExteriorAlgebra.map l u ∈ positiveEvenPart (exteriorGrade R N) := by
  induction hu using Submodule.iSup_induction' with
  | mem k u hu => exact Submodule.mem_iSup_of_mem k (ExteriorAlgebra.map_mem_exteriorPower l hu)
  | zero => simp
  | add u u' _ _ ihu ihu' => rw [_root_.map_add]; exact Submodule.add_mem _ ihu ihu'

/-- `ExteriorAlgebra.map` turns a commuting square of linear maps into a commuting square. -/
private theorem map_map_comm {M' : Type*} [AddCommGroup M'] [Module R M']
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (L : N' →ₗ[R] N') (φ : M' →ₗ[R] N') (l : M' →ₗ[R] M') (h : L ∘ₗ φ = φ ∘ₗ l)
    (u : ExteriorAlgebra R M') :
    ExteriorAlgebra.map L (ExteriorAlgebra.map φ u) =
      ExteriorAlgebra.map φ (ExteriorAlgebra.map l u) := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h, ← ExteriorAlgebra.map_comp_map,
    AlgHom.comp_apply]

end PositiveEvenPart

namespace ExteriorOddVariable

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- An endomorphism of `M × R` restricting to `l` on `M` carries the coefficient embedding of
`⋀[R] M` into `⋀[R] (M × R)` to `ExteriorAlgebra.map l`. -/
public theorem map_incl (l : M →ₗ[R] M) (L : (M × R) →ₗ[R] (M × R))
    (hL : L ∘ₗ LinearMap.inl R M R = LinearMap.inl R M R ∘ₗ l) (u : ExteriorAlgebra R M) :
    ExteriorAlgebra.map L (incl u) = incl (ExteriorAlgebra.map l u) := by
  exact map_map_comm L (LinearMap.inl R M R) l hL u

/-- An endomorphism of `M × R` sending `(0, 1)` to `(0, c)` scales the adjoined wedge generator
by `c`. -/
public theorem map_gen (c : R) (L : (M × R) →ₗ[R] (M × R))
    (hL : L ((0, 1) : M × R) = ((0, c) : M × R)) :
    ExteriorAlgebra.map L (gen : ExteriorAlgebra R (M × R)) = c • gen := by
  rw [show (gen : ExteriorAlgebra R (M × R)) = ExteriorAlgebra.ι R ((0, 1) : M × R) from rfl,
    ExteriorAlgebra.map_apply_ι, hL,
    show ((0, c) : M × R) = c • ((0, 1) : M × R) by simp, _root_.map_smul]

end ExteriorOddVariable

section Step

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

open ExteriorOddVariable

/-- **The inductive step: adjoining one odd variable preserves functoriality of the divided
powers.** Let `l` be an endomorphism of `M` under which the divided powers of `⋀[R] M` are
functorial, and let `L` be an endomorphism of `M × R` restricting to `l` on `M` and acting on the
new coordinate by the scalar `c`. Then the divided powers of `⋀[R] (M × R)` of
`DividedPowers.TateResolution.exteriorProdDividedPowerStructure` are functorial under `L`.

The proof writes a positive even element as `a + bT` and applies the formula of
`DividedPowers.TateResolution.exteriorProdDividedPowerStructure_dpow` on both sides; the scalar
`c` comes out of the one factor of `T` that each side carries. -/
public theorem exteriorProd_map_dpow (γ : DividedPowerStructure (exteriorGrade R M))
    (l : M →ₗ[R] M) (c : R)
    (hγ : ∀ (k : ℕ) (u : ExteriorAlgebra R M), u ∈ positiveEvenPart (exteriorGrade R M) →
      γ.dpow k (ExteriorAlgebra.map l u) = ExteriorAlgebra.map l (γ.dpow k u))
    (L : (M × R) →ₗ[R] (M × R))
    (hL₁ : L ∘ₗ LinearMap.inl R M R = LinearMap.inl R M R ∘ₗ l)
    (hL₂ : L ((0, 1) : M × R) = ((0, c) : M × R))
    (k : ℕ) {z : ExteriorAlgebra R (M × R)}
    (hz : z ∈ positiveEvenPart (exteriorGrade R (M × R))) :
    (exteriorProdDividedPowerStructure γ).dpow k (ExteriorAlgebra.map L z) =
      ExteriorAlgebra.map L ((exteriorProdDividedPowerStructure γ).dpow k z) := by
  have hz' : equiv.symm z ∈
      positiveEvenPart (OddVariableExtension.grade (exteriorGrade R M) 1) :=
    (mem_positiveEvenPart_equiv_iff (OddVariableExtension.grade (exteriorGrade R M) 1)
      (exteriorGrade R (M × R)) equiv mem_grade_iff z).mp hz
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_coeff_of_mem_positiveEvenPart_oddVariable (exteriorGrade R M) hz'
  have hzab : z = incl a + incl b * gen := by
    rw [← equiv.apply_symm_apply z, hab, _root_.map_add, _root_.map_mul, equiv_apply,
      equiv_apply, equiv_apply, hom_inclusion, hom_inclusion, hom_generator]
  have hLa : ExteriorAlgebra.map l a ∈ positiveEvenPart (exteriorGrade R M) :=
    map_mem_positiveEvenPart l ha
  have hLb : c • ExteriorAlgebra.map l b ∈ oddPart (exteriorGrade R M) :=
    Submodule.smul_mem _ c (map_mem_oddPart l hb)
  have hmapz : ExteriorAlgebra.map L z =
      incl (ExteriorAlgebra.map l a) + incl (c • ExteriorAlgebra.map l b) * gen := by
    rw [hzab, _root_.map_add, _root_.map_mul, map_incl l L hL₁, map_incl l L hL₁,
      map_gen c L hL₂, _root_.map_smul, smul_mul_assoc, mul_smul_comm]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(exteriorProdDividedPowerStructure γ).dpow_zero hz,
      (exteriorProdDividedPowerStructure γ).dpow_zero
        (map_mem_positiveEvenPart L hz), _root_.map_one]
  · have hk' : k ≠ 0 := hk.ne'
    have hinner : incl (ExteriorAlgebra.map l (γ.dpow (k - 1) a) *
          (c • ExteriorAlgebra.map l b)) * gen =
        c • (incl (ExteriorAlgebra.map l (γ.dpow (k - 1) a * b)) * gen) := by
      rw [mul_smul_comm, ← _root_.map_mul, _root_.map_smul, smul_mul_assoc]
    have hRHS : ExteriorAlgebra.map L ((exteriorProdDividedPowerStructure γ).dpow k z) =
        incl (ExteriorAlgebra.map l (γ.dpow k a)) +
          c • (incl (ExteriorAlgebra.map l (γ.dpow (k - 1) a * b)) * gen) := by
      rw [hzab, exteriorProdDividedPowerStructure_dpow γ hk' ha hb, _root_.map_add,
        _root_.map_mul, map_incl l L hL₁, map_incl l L hL₁, map_gen c L hL₂, mul_smul_comm]
    rw [hmapz, exteriorProdDividedPowerStructure_dpow γ hk' hLa hLb, hγ k a ha,
      hγ (k - 1) a ha, hinner, hRHS]

end Step

section Fin

variable (R : Type u) [CommRing R]

/-- **The divided powers of `⋀[R] (Fin r → R)` are functorial under a diagonal endomorphism of
`Rʳ`.** The endomorphism is written `LinearMap.mulLeft R c`, which is `x ↦ c * x` for the
componentwise algebra structure of `Rʳ`, that is the diagonal matrix with entries `cᵢ`.

This is what makes the Koszul transition map of Tag 0GZ4 a morphism of divided power algebras:
the transition scaling the `i`-th generator by `fᵢ^(m-n)` is `ExteriorAlgebra.map` of exactly
such an endomorphism. -/
public theorem exteriorDividedPowerStructure_dpow_map_mulLeft :
    ∀ (r : ℕ) (c : Fin r → R) (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
      x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
      (exteriorDividedPowerStructure R r).dpow k
          (ExteriorAlgebra.map (LinearMap.mulLeft R c) x) =
        ExteriorAlgebra.map (LinearMap.mulLeft R c)
          ((exteriorDividedPowerStructure R r).dpow k x) := by
  intro r
  induction r with
  | zero =>
    intro c k x hx
    have hx0 : x = 0 := by
      rw [positiveEvenPart_exteriorGrade_eq_bot R (Fin 0 → R)] at hx
      exact hx
    subst hx0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [_root_.map_zero, (exteriorDividedPowerStructure R 0).dpow_zero (Submodule.zero_mem _),
        _root_.map_one]
    · rw [_root_.map_zero, DividedPowerStructure.dpow_apply_zero _ hk.ne', _root_.map_zero]
  | succ r ih =>
    intro c k x hx
    set e := ExteriorAlgebra.mapAlgEquiv (finSuccLinearEquiv R r) with hedef
    set D : (Fin (r + 1) → R) →ₗ[R] (Fin (r + 1) → R) := LinearMap.mulLeft R c with hD
    set D' : ((Fin r → R) × R) →ₗ[R] ((Fin r → R) × R) :=
      LinearMap.mulLeft R ((fun i => c i.succ, c 0) : (Fin r → R) × R) with hD'
    have hgr : ∀ (m : ℕ) (y : ExteriorAlgebra R ((Fin r → R) × R)),
        y ∈ exteriorGrade R ((Fin r → R) × R) m ↔ e y ∈ exteriorGrade R (Fin (r + 1) → R) m :=
      fun m y => mem_grade_iff_of_mapsTo (exteriorGrade R ((Fin r → R) × R))
        (exteriorGrade R (Fin (r + 1) → R)) e
        (fun _ _ h => ExteriorAlgebra.map_mem_exteriorPower _ h) m y
    have hcomm : D ∘ₗ (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R)) =
        (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R)) ∘ₗ D' := by
      refine LinearMap.ext fun w => funext fun i => ?_
      induction i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    have hmapD : ∀ w : ExteriorAlgebra R ((Fin r → R) × R),
        ExteriorAlgebra.map D (e w) = e (ExteriorAlgebra.map D' w) :=
      map_map_comm D (finSuccLinearEquiv R r : ((Fin r → R) × R) →ₗ[R] (Fin (r + 1) → R)) D' hcomm
    have hsymm : e.symm (ExteriorAlgebra.map D x) = ExteriorAlgebra.map D' (e.symm x) := by
      apply e.injective
      rw [e.apply_symm_apply, ← hmapD, e.apply_symm_apply]
    have hxs : e.symm x ∈ positiveEvenPart (exteriorGrade R ((Fin r → R) × R)) :=
      (mem_positiveEvenPart_equiv_iff (exteriorGrade R ((Fin r → R) × R))
        (exteriorGrade R (Fin (r + 1) → R)) e hgr x).mp hx
    rw [exteriorDividedPowerStructure_succ R r]
    change e ((exteriorProdDividedPowerStructure (exteriorDividedPowerStructure R r)).dpow k
        (e.symm (ExteriorAlgebra.map D x))) =
      ExteriorAlgebra.map D (e ((exteriorProdDividedPowerStructure
        (exteriorDividedPowerStructure R r)).dpow k (e.symm x)))
    rw [hsymm, exteriorProd_map_dpow (exteriorDividedPowerStructure R r)
        (LinearMap.mulLeft R (fun i => c i.succ)) (c 0) (fun k u hu => ih _ k u hu) D'
        (by refine LinearMap.ext fun v => ?_; simp [hD']) (by simp [hD']) k hxs, hmapD]

end Fin

section Differential

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The diagonal endomorphism scaling the `i`-th coordinate by `fᵢ^(m-n)` pulls the Koszul
functional of the `(n+1)`-st powers back to the Koszul functional of the `(m+1)`-st powers. -/
public theorem seqDual_comp_mulLeft (f : Fin r → R) {m n : ℕ} (h : n ≤ m) :
    Koszul.seqDual (fun i => f i ^ (n + 1)) ∘ₗ
        LinearMap.mulLeft R (fun i => f i ^ (m - n)) =
      Koszul.seqDual (fun i => f i ^ (m + 1)) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, Koszul.seqDual_apply, Koszul.seqDual_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : (LinearMap.mulLeft R (fun j => f j ^ (m - n)) v) i = f i ^ (m - n) * v i := rfl
  rw [hv, mul_comm (f i ^ (m - n)) (v i), mul_assoc, ← pow_add,
    show m - n + (n + 1) = m + 1 by omega]

/-- **The Koszul transition map commutes with the two Koszul differentials.** Scaling the `i`-th
generator by `fᵢ^(m-n)` is a chain map from the Koszul complex on the `(m+1)`-st powers to the
Koszul complex on the `(n+1)`-st powers. -/
@[ega "III 1.1.6" "(1.1.6.1)"]
public theorem contraction_map_mulLeft (f : Fin r → R) {m n : ℕ} (h : n ≤ m)
    (x : ExteriorAlgebra R (Fin r → R)) :
    Koszul.contraction (Koszul.seqDual (fun i => f i ^ (n + 1)))
        (ExteriorAlgebra.map (LinearMap.mulLeft R (fun i => f i ^ (m - n))) x) =
      ExteriorAlgebra.map (LinearMap.mulLeft R (fun i => f i ^ (m - n)))
        (Koszul.contraction (Koszul.seqDual (fun i => f i ^ (m + 1))) x) := by
  rw [Koszul.contraction, Koszul.contraction,
    contractLeft_exteriorAlgebraMap (LinearMap.mulLeft R (fun i => f i ^ (m - n)))
      (Koszul.seqDual (fun i => f i ^ (n + 1))) x, seqDual_comp_mulLeft f h]

end Differential

end DividedPowers.TateResolution

end
