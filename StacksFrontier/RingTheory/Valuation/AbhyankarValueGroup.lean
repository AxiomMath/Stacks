module

public import StacksFrontier.RingTheory.Valuation.AbhyankarInequality
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Abhyankar's inequality for the value group and the residue field

Let `R` be a Noetherian local domain with fraction field `K` and `V` a valuation ring of `K`
dominating `R` (`R ⊆ V` and `𝔪_V ∩ R = 𝔪_R`), with value group `Γ = K^×/V^×` and residue field
`κ(V)`. **Abhyankar's inequality** states

  `rat.rank Γ + trdeg_{κ(R)} κ(V) ≤ dim R`,

where the rational rank `rat.rank Γ = dim_ℚ (Γ ⊗ ℚ)` is the rank of `Γ` as an abelian group,
i.e. `Module.rank ℤ Γ` (the supremum of the cardinalities of `ℤ`-linearly independent families).
In particular both terms are finite.

The value group is `(ValuationRing.ValueGroup V K)ˣ`, written additively. A finite
`ℤ`-linearly independent family of values is realized by elements of `V` whose monomials are
pairwise non-associated, and a finite algebraically independent family of `κ(V)` lifts to `V`;
`Stacks.Abhyankar.add_le_ringKrullDim` then bounds their total number by `dim R`.

## Main results

* `Stacks.Abhyankar.rank_valueGroup_add_trdeg_le`: `rank_ℤ Γ + trdeg_{κ(R)} κ(V) ≤ d` when
  `dim R = d`.
* `Stacks.Abhyankar.toENat_rank_valueGroup_add_trdeg_le_ringKrullDim`: the same with
  `ringKrullDim`.
* `Stacks.Abhyankar.rank_rat_tensor_valueGroup_add_trdeg_le`: the same with the rational rank
  written as `dim_ℚ (ℚ ⊗ Γ)`.

## References

* S. Abhyankar, *On the valuations centered in a local domain*, Amer. J. Math. 78 (1956),
  Theorem 1.
* O. Zariski, P. Samuel, *Commutative Algebra*, vol. II, Appendix 2.
* N. Bourbaki, *Algèbre commutative*, chapitre VI, §10, no. 3.
-/

@[expose] public section

namespace Stacks.Abhyankar

open IsLocalRing
open scoped TensorProduct

universe u v

section ValueGroup

variable {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] {K : Type v} [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem valuation_surjective' : Function.Surjective (ValuationRing.valuation V K) := by
  unfold ValuationRing.valuation
  exact Quotient.mk_surjective

theorem valuation_algebraMap_le_one (a : V) :
    ValuationRing.valuation V K (algebraMap V K a) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp ((ValuationRing.mem_integer_iff V K _).mpr ⟨a, rfl⟩)

theorem valuation_algebraMap_unit (u : Vˣ) :
    ValuationRing.valuation V K (algebraMap V K u) = 1 := by
  have h1 := valuation_algebraMap_le_one (K := K) (u : V)
  have h2 := valuation_algebraMap_le_one (K := K) (↑u⁻¹ : V)
  have h3 : ValuationRing.valuation V K (algebraMap V K u) *
      ValuationRing.valuation V K (algebraMap V K ↑u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValuationRing.ValueGroup V K) = _ := h3.symm
    _ ≤ ValuationRing.valuation V K (algebraMap V K u) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

theorem valuation_algebraMap_ne_zero {a : V} (ha : a ≠ 0) :
    ValuationRing.valuation V K (algebraMap V K a) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr ha)

/-- Elements of `V` whose values are `ℤ`-linearly independent in the value group have pairwise
non-associated monomials. -/
theorem monomialIndependent_of_linearIndependent {r : ℕ} (x : Fin r → V) (hx0 : ∀ i, x i ≠ 0)
    (hli : LinearIndependent ℤ (fun i => Additive.ofMul (Units.mk0
      (ValuationRing.valuation V K (algebraMap V K (x i)))
        (valuation_algebraMap_ne_zero (hx0 i))))) :
    MonomialIndependent x := by
  intro α β hass
  obtain ⟨u, hu⟩ := hass
  set w : Fin r → (ValuationRing.ValueGroup V K)ˣ := fun i =>
    Units.mk0 (ValuationRing.valuation V K (algebraMap V K (x i)))
      (valuation_algebraMap_ne_zero (hx0 i))
  have hval : ∀ γ : Fin r → ℕ, ValuationRing.valuation V K (algebraMap V K (monom x γ)) =
      ((∏ i, w i ^ γ i : (ValuationRing.ValueGroup V K)ˣ) : ValuationRing.ValueGroup V K) := by
    intro γ
    simp only [monom, map_prod, map_pow, Units.coe_prod, Units.val_pow_eq_pow_val, w,
      Units.val_mk0]
  have heq : (∏ i, w i ^ α i : (ValuationRing.ValueGroup V K)ˣ) = ∏ i, w i ^ β i := by
    apply Units.ext
    rw [← hval, ← hval, ← hu, map_mul, map_mul, valuation_algebraMap_unit, mul_one]
  have hadd : ∑ i, ((α i : ℤ) - β i) • Additive.ofMul (w i) = 0 := by
    have := congrArg Additive.ofMul heq
    simp only [ofMul_prod, ofMul_pow] at this
    simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul, this, sub_self]
  have hzero := Fintype.linearIndependent_iff.mp hli _ hadd
  funext i
  have := hzero i
  rw [sub_eq_zero] at this
  exact_mod_cast this

/-- A finite `ℤ`-linearly independent family of values is the family of values of elements of `V`
up to sign, so it is realized by a monomially independent family in `V`. -/
theorem exists_monomialIndependent {r : ℕ}
    (γ : Fin r → Additive (ValuationRing.ValueGroup V K)ˣ) (hγ : LinearIndependent ℤ γ) :
    ∃ x : Fin r → V, MonomialIndependent x := by
  have hlift : ∀ i, ∃ a : V, ∃ ε : ℤˣ, ∃ ha : a ≠ 0,
      Additive.ofMul (Units.mk0 (ValuationRing.valuation V K (algebraMap V K a))
        (valuation_algebraMap_ne_zero ha)) = ε • γ i := by
    intro i
    obtain ⟨c, hc⟩ := valuation_surjective' (V := V) (K := K)
      ((Additive.toMul (γ i) : (ValuationRing.ValueGroup V K)ˣ) : ValuationRing.ValueGroup V K)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (Additive.toMul (γ i)).ne_zero hc.symm
    rcases Valuation.val_le_one_or_val_inv_lt_one (ValuationRing.valuation V K) c with h | h
    · obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff V K c).mp
        ((Valuation.mem_integer_iff _ _).mpr h)
      have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hc0 ha.symm
      refine ⟨a, 1, ha0, ?_⟩
      rw [one_smul]
      apply Additive.toMul.injective
      apply Units.ext
      simp [ha, hc]
    · obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff V K c⁻¹).mp
        ((Valuation.mem_integer_iff _ _).mpr h.le)
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [map_zero] at ha; exact inv_ne_zero hc0 ha.symm
      refine ⟨a, -1, ha0, ?_⟩
      apply Additive.toMul.injective
      apply Units.ext
      simp [ha, hc, map_inv₀]
  choose a ε ha0 ha using hlift
  refine ⟨a, monomialIndependent_of_linearIndependent (K := K) a ha0 ?_⟩
  have : (fun i => Additive.ofMul (Units.mk0 (ValuationRing.valuation V K (algebraMap V K (a i)))
      (valuation_algebraMap_ne_zero (ha0 i)))) = ε • γ := funext ha
  rw [this]
  exact hγ.units_smul ε

end ValueGroup

section RationalRank

/-- The rank of an abelian group is the dimension of its rationalization:
`dim_ℚ (ℚ ⊗ M) = rank_ℤ M`. -/
theorem rank_rat_tensor_eq (M : Type*) [AddCommGroup M] :
    Module.rank ℚ (ℚ ⊗[ℤ] M) = Module.rank ℤ M := by
  have : IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (TensorProduct.isBaseChange ℤ M ℚ)
  have h := IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl (TensorProduct.mk ℤ ℚ M 1)
  rw [IsFractionRing.rank_right_eq (R := ℤ) (S := ℚ) (N := ℚ ⊗[ℤ] M)]
  convert h using 2
  exact Subsingleton.elim _ _

end RationalRank

section Trdeg

/-- If `n ≤ trdeg_F L`, there are `n` algebraically independent elements of `L`. -/
theorem exists_algebraicIndependent_fin {F L : Type*} [Field F] [Field L] [Algebra F L] {n : ℕ}
    (h : (n : Cardinal) ≤ Algebra.trdeg F L) : ∃ z : Fin n → L, AlgebraicIndependent F z := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  rw [← hs.cardinalMk_eq_trdeg] at h
  obtain ⟨p, hps, hp⟩ := Cardinal.le_mk_iff_exists_subset.mp h
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hp
  refine ⟨fun i => (e.symm i : L), ?_⟩
  have h1 : AlgebraicIndependent F ((↑) : p → L) :=
    hs.1.comp (Set.inclusion hps) (Set.inclusion_injective hps)
  exact h1.comp e.symm e.symm.injective

end Trdeg

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type v} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V K] [IsFractionRing V K]
  [Algebra R V] [IsScalarTower R V K] [IsLocalHom (algebraMap R V)]

omit [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain V] [ValuationRing V]
  [IsFractionRing V K] [IsLocalHom (algebraMap R V)] in
include K in
theorem algebraMap_injective_of_isFractionRing : Function.Injective (algebraMap R V) := by
  intro a b h
  apply IsFractionRing.injective R K
  rw [IsScalarTower.algebraMap_apply R V K, h, ← IsScalarTower.algebraMap_apply]

omit [IsDomain R] [IsNoetherianRing R] [IsDomain V] [ValuationRing V]
  [IsLocalHom (algebraMap R V)] in
include K in
theorem isAlgebraic_of_isFractionRing : Algebra.IsAlgebraic R V := by
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  refine ⟨fun a => ?_⟩
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R V K)
    (IsFractionRing.injective V K)).mp (Algebra.IsAlgebraic.isAlgebraic _)

include K in
/-- Natural numbers below the rational rank and the residue transcendence degree add up to at
most `dim R`. -/
theorem add_le_of_le_rank_of_le_trdeg (d : ℕ) (hd : ringKrullDim R = d) (a b : ℕ)
    (ha : (a : Cardinal) ≤ Module.rank ℤ (Additive (ValuationRing.ValueGroup V K)ˣ))
    (hb : (b : Cardinal) ≤ Algebra.trdeg (ResidueField R) (ResidueField V)) : a + b ≤ d := by
  classical
  obtain ⟨s, hs, hsli⟩ := exists_finset_linearIndependent_of_le_rank ha
  let es : Fin a ≃ s := (s.equivFinOfCardEq hs).symm
  have hγ :
      LinearIndependent ℤ (fun i => ((es i : s) : Additive (ValuationRing.ValueGroup V K)ˣ)) :=
    (LinearIndepOn.linearIndependent hsli).comp es es.injective
  obtain ⟨x, hx⟩ := exists_monomialIndependent (K := K) _ hγ
  obtain ⟨z, hz⟩ := exists_algebraicIndependent_fin hb
  choose y hy using fun i => IsLocalRing.residue_surjective (z i)
  have hyz : residue V ∘ y = z := funext hy
  have := isAlgebraic_of_isFractionRing (R := R) (K := K) (V := V)
  have h := add_le_ringKrullDim (algebraMap_injective_of_isFractionRing (K := K)) x hx y
    (by rw [hyz]; exact hz)
  rw [hd] at h
  exact_mod_cast h

include K in
/-- **Abhyankar's inequality.** Let `R` be a Noetherian local domain of dimension `d` with
fraction field `K`, and `V` a valuation ring of `K` dominating `R`. Then the rational rank of
the value group `Γ = K^×/V^×` (its rank as an abelian group) plus the transcendence degree of
`κ(V)` over `κ(R)` is at most `d`. -/
theorem rank_valueGroup_add_trdeg_le (d : ℕ) (hd : ringKrullDim R = d) :
    Module.rank ℤ (Additive (ValuationRing.ValueGroup V K)ˣ) +
      Algebra.trdeg (ResidueField R) (ResidueField V) ≤ d := by
  have key := add_le_of_le_rank_of_le_trdeg (K := K) (V := V) d hd
  have hfin : ∀ c : Cardinal, (∀ a : ℕ, (a : Cardinal) ≤ c → a ≤ d) → c < Cardinal.aleph0 := by
    intro c hc
    by_contra hge
    push Not at hge
    have := hc (d + 1) ((Cardinal.natCast_lt_aleph0).le.trans hge)
    omega
  have hr := hfin _ fun a ha => by simpa using key a 0 ha (by simp)
  have ht := hfin _ fun b hb => by simpa using key 0 b (by simp) hb
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp hr
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.mp ht
  rw [ha, hb]
  exact_mod_cast key a b ha.ge hb.ge

include K in
/-- **Abhyankar's inequality**, with the Krull dimension:
`rat.rank Γ + trdeg_{κ(R)} κ(V) ≤ dim R`, both summands being finite. -/
theorem toENat_rank_valueGroup_add_trdeg_le_ringKrullDim :
    ((Module.rank ℤ (Additive (ValuationRing.ValueGroup V K)ˣ) +
      Algebra.trdeg (ResidueField R) (ResidueField V)).toENat : WithBot ℕ∞) ≤
      ringKrullDim R := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim R = d := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact ⟨_, congrArg _ (ENat.coe_toNat
      (Ideal.height_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top)).symm⟩
  have h := rank_valueGroup_add_trdeg_le (K := K) (V := V) d hd
  rw [hd]
  have : (Module.rank ℤ (Additive (ValuationRing.ValueGroup V K)ˣ) +
      Algebra.trdeg (ResidueField R) (ResidueField V)).toENat ≤ d := by
    simpa using Cardinal.toENat.monotone' h
  exact_mod_cast this

include K in
/-- **Abhyankar's inequality**, with the rational rank written as `dim_ℚ (ℚ ⊗ Γ)`:
`rat.rank Γ + trdeg_{κ(R)} κ(V) ≤ dim R = d`. -/
theorem rank_rat_tensor_valueGroup_add_trdeg_le (d : ℕ) (hd : ringKrullDim R = d) :
    Module.rank ℚ (ℚ ⊗[ℤ] Additive (ValuationRing.ValueGroup V K)ˣ) +
      Algebra.trdeg (ResidueField R) (ResidueField V) ≤ d := by
  rw [rank_rat_tensor_eq]
  exact rank_valueGroup_add_trdeg_le (K := K) (V := V) d hd

end Main

end Stacks.Abhyankar
