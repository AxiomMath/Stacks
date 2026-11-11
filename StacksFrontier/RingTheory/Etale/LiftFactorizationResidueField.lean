module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a coprime factorization over the residue field to an étale neighbourhood

Let `R` be a ring, `p ∈ R[X]` monic and `P ⊂ R` a prime. A factorization `p mod P = f g` in
`κ(P)[X]` into coprime factors lifts, over an étale `R`-algebra `R'` with a prime `Q` over `P`
and `κ(P) = κ(Q)`, to a factorization `p = f' g'` in `R'[X]` with `f'`, `g'` coprime and
reducing to `f`, `g` (Stacks 00UH).

Mathlib proves this as
`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime` when `f` and `g`
are monic. This file removes that restriction as the source's proof does: the leading coefficient
`u = a / s` of `f` is made a unit by inverting `a s`, and the factors are rescaled by `u`.

## Main results

* `Algebra.exists_etale_bijective_residueFieldMap_lift_isCoprime_factorization`: Stacks 00UH,
  for an arbitrary coprime factorization in `κ(P)[X]`.

## References

* [Stacks Project, Tag 00UH](https://stacks.math.columbia.edu/tag/00UH)
-/

open Polynomial

@[expose] public section

namespace Algebra

/-- **Stacks 00UH.** Let `p ∈ R[X]` be monic and `P ⊂ R` a prime. If `p mod P = f g` in
`κ(P)[X]` with `f` and `g` coprime, then there are an étale ring map `R → R'`, a prime `Q ⊂ R'`
lying over `P` with `κ(P) = κ(Q)`, and a factorization `p = f' g'` in `R'[X]` such that
`f = f' mod Q`, `g = g' mod Q` and `f'`, `g'` generate the unit ideal of `R'[X]`. -/
@[stacks 00UH]
theorem exists_etale_bijective_residueFieldMap_lift_isCoprime_factorization.{u}
    {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (p : R[X])
    (f g : P.ResidueField[X]) (hp : p.Monic)
    (H : p.map (algebraMap R _) = f * g) (Hpq : IsCoprime f g) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (Q : Ideal R') (_ : Q.IsPrime) (_ : Q.LiesOver P) (f' g' : R'[X]),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    p.map (algebraMap R R') = f' * g' ∧ IsCoprime f' g' ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      f'.map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      g'.map (algebraMap _ _) := by
  -- Normalize: `f₁ = u⁻¹ f` and `g₁ = u g` are monic, where `u` is the leading coefficient of `f`.
  have hpm : (p.map (algebraMap R P.ResidueField)).Monic := hp.map _
  have hfg : f * g ≠ 0 := H ▸ hpm.ne_zero
  have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg
  set u := f.leadingCoeff with hu
  have hu0 : u ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hlc : u * g.leadingCoeff = 1 := by
    rw [hu, ← leadingCoeff_mul, ← H]; exact hpm.leadingCoeff
  set f₁ := C u⁻¹ * f
  set g₁ := C u * g
  have hf₁ : f₁.Monic := by
    simp only [Monic, f₁, leadingCoeff_mul, leadingCoeff_C, ← hu, inv_mul_cancel₀ hu0]
  have hg₁ : g₁.Monic := by
    simp only [Monic, g₁, leadingCoeff_mul, leadingCoeff_C, hlc]
  have H₁ : p.map (algebraMap R _) = f₁ * g₁ := by
    rw [H, show f₁ * g₁ = (C u⁻¹ * C u) * (f * g) by simp only [f₁, g₁]; ring, ← C_mul,
      inv_mul_cancel₀ hu0, C_1, one_mul]
  have Hpq₁ : IsCoprime f₁ g₁ :=
    (isCoprime_mul_unit_left_left (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hu0))) _ _).mpr
      ((isCoprime_mul_unit_left_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu0)) _ _).mpr Hpq)
  obtain ⟨R', _, _, _, Q, _, _, f', g', hbij, -, -, hmul, hcop, hf', hg'⟩ :=
    exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime P p f₁ g₁ hp hf₁ hg₁ H₁
      Hpq₁
  -- Write `u = a / s` and invert `a s` in `R'`.
  obtain ⟨a', s', hs', has'⟩ := IsFractionRing.div_surjective (A := R ⧸ P) u
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  simp only [Ideal.algebraMap_quotient_residueField_mk] at has'
  have hsP : s ∉ P := by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem] at hs'
    exact hs'
  have haP : a ∉ P := by
    intro ha
    rw [← Ideal.algebraMap_residueField_eq_zero] at ha
    rw [ha, zero_div] at has'
    exact hu0 has'.symm
  set t := algebraMap R R' (a * s)
  have htQ : t ∉ Q := by
    intro ht
    have : a * s ∈ Q.comap (algebraMap R R') := ht
    rw [← Ideal.under_def, ← Ideal.over_def Q P] at this
    exact (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).not.mpr (not_or.mpr ⟨haP, hsP⟩) this
  let R'' := Localization.Away t
  have hdisj : Disjoint (Submonoid.powers t : Set R') Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr htQ
  let Q'' : Ideal R'' := Q.map (algebraMap R' R'')
  have hQ''prime : Q''.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) R'' Q ‹_› hdisj
  have hQ''comap : Q''.comap (algebraMap R' R'') = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers t) R'' ‹_› hdisj
  have hQ''P : Q''.LiesOver P := ⟨by
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq R R' R'', ← Ideal.comap_comap, hQ''comap,
      ← Ideal.under_def, ← Ideal.over_def Q P]⟩
  -- The residue field map `κ(P) → κ(Q'')` factors through the bijection `κ(Q) → κ(Q'')`.
  let φ := Ideal.ResidueField.mapₐ P Q (Algebra.ofId R R') (Ideal.over_def Q P)
  let θ := Ideal.ResidueField.mapₐ Q Q'' (IsScalarTower.toAlgHom R R' R'') hQ''comap.symm
  let ψ := Ideal.ResidueField.mapₐ P Q'' (Algebra.ofId R R'') (Ideal.over_def Q'' P)
  have hψ : ψ = θ.comp φ := by
    ext
  have hθ : Function.Bijective θ :=
    RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      (RingHom.surjectiveOnStalks_of_isLocalization (M := Submonoid.powers t) R'') Q Q''
      hQ''comap.symm
  have hθalg : ∀ x : R', θ (algebraMap R' Q.ResidueField x) =
      algebraMap R'' Q''.ResidueField (algebraMap R' R'' x) := fun x ↦
    Ideal.ResidueField.map_algebraMap _ _ _ _ x
  -- The unit `w = a / s` of `R''` reduces to the image of `u`.
  have htu : IsUnit
      (algebraMap R' R'' (algebraMap R R' a) * algebraMap R' R'' (algebraMap R R' s)) := by
    rw [← map_mul, ← map_mul]; exact IsLocalization.Away.algebraMap_isUnit t
  have hA : IsUnit (algebraMap R' R'' (algebraMap R R' a)) := isUnit_of_mul_isUnit_left htu
  have hS : IsUnit (algebraMap R' R'' (algebraMap R R' s)) := isUnit_of_mul_isUnit_right htu
  let w : R''ˣ := hA.unit * hS.unit⁻¹
  have hsκ : algebraMap R Q''.ResidueField s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R R'' Q''.ResidueField, Ne,
      Ideal.algebraMap_residueField_eq_zero, ← Ideal.mem_comap, ← Ideal.under_def,
      ← Ideal.over_def Q'' P]
    exact hsP
  have hψu : ψ u = algebraMap R Q''.ResidueField a / algebraMap R Q''.ResidueField s := by
    rw [← has', map_div₀, AlgHom.commutes, AlgHom.commutes]
  have hwS : (w : R'') * algebraMap R' R'' (algebraMap R R' s) =
      algebraMap R' R'' (algebraMap R R' a) := by
    simp only [w, Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
  have hw : algebraMap R'' Q''.ResidueField (w : R'') = ψ u := by
    rw [hψu, eq_div_iff hsκ]
    simp only [IsScalarTower.algebraMap_apply R R'' Q''.ResidueField,
      IsScalarTower.algebraMap_apply R R' R'']
    rw [← map_mul, hwS]
  have hwinv : algebraMap R'' Q''.ResidueField ((w⁻¹ : R''ˣ) : R'') = ψ u⁻¹ := by
    rw [map_inv₀, ← hw, map_units_inv]
  have hmapψ : ∀ q : P.ResidueField[X], q.map ψ.toRingHom =
      (q.map φ.toRingHom).map θ.toRingHom := fun q ↦ by
    simp only [Polynomial.map_map, hψ, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  have hmapR' : ∀ q : R'[X], (q.map (algebraMap R' Q.ResidueField)).map θ.toRingHom =
      (q.map (algebraMap R' R'')).map (algebraMap R'' Q''.ResidueField) := fun q ↦ by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    exact hθalg x
  have hC : C (w : R'') * C ((w⁻¹ : R''ˣ) : R'') = 1 := by rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨R'', inferInstance, inferInstance, Algebra.Etale.comp R R' R'', Q'', hQ''prime, hQ''P,
    C (w : R'') * f'.map (algebraMap R' R''), C ((w⁻¹ : R''ˣ) : R'') * g'.map (algebraMap R' R''),
    ?_, ?_, ?_, ?_, ?_⟩
  · change Function.Bijective ψ
    rw [hψ]
    exact hθ.comp hbij
  · rw [IsScalarTower.algebraMap_eq R R' R'', ← Polynomial.map_map, hmul, Polynomial.map_mul]
    linear_combination (-(f'.map (algebraMap R' R'') * g'.map (algebraMap R' R''))) * hC
  · exact (isCoprime_mul_unit_left_left (isUnit_C.mpr w.isUnit) _ _).mpr
      ((isCoprime_mul_unit_left_right (isUnit_C.mpr w⁻¹.isUnit) _ _).mpr
        (hcop.map (Polynomial.mapRingHom (algebraMap R' R''))))
  · change f.map ψ.toRingHom = _
    rw [Polynomial.map_mul, Polynomial.map_C, ← hmapR', ← hf', ← hmapψ]
    simp only [f₁, Polynomial.map_mul, Polynomial.map_C, RingHom.coe_coe, hw,
      AlgHom.toRingHom_eq_coe]
    rw [← mul_assoc, ← C_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, C_1, one_mul]
  · change g.map ψ.toRingHom = _
    rw [Polynomial.map_mul, Polynomial.map_C, ← hmapR', ← hg', ← hmapψ]
    simp only [g₁, Polynomial.map_mul, Polynomial.map_C, RingHom.coe_coe, hwinv,
      AlgHom.toRingHom_eq_coe]
    rw [← mul_assoc, ← C_mul, ← map_mul, inv_mul_cancel₀ hu0, map_one, C_1, one_mul]

end Algebra
