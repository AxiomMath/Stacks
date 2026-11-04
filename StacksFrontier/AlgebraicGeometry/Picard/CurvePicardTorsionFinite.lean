module

public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDivisorFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier

/-!
# The torsion of the Picard group of a smooth proper curve over a finite field is finite

Let `Z` be a smooth proper curve over a finite field `E`, of genus `g`. Then the torsion
subgroup of `Pic(Z)` is finite. (In fact `Pic⁰(Z)` is finite; the torsion is what the Frobenius
fixed points of the Picard group of `Z_{Ē}` are bounded by.)

Fix a closed point `P₀`, an effective Cartier divisor of degree `δ = [κ(P₀) : E] ≥ 1`. A torsion
class `z` has degree `0`, so `z + g [P₀]` has degree `g δ ≥ g` and is the class of an effective
Cartier divisor `D` (`Stacks.Picard.exists_divisorPicardClass_eq_of_genus_le`), with
`dim_E Γ(D, 𝒪_D) = g δ`. Such `D` have at most `q ^ (g δ)` functions and form a finite set
(`Stacks.Picard.finite_setOf_idealSheafData_natCard_le`).

## Main results

* `Stacks.Picard.finite_and_natCard_globalSections_divisor`: `Γ(D, 𝒪_D)` is a finite set with
  `q ^ deg D` elements, for an effective Cartier divisor `D`.
* `Stacks.Picard.finite_setOf_isOfFinAddOrder`: the torsion of `Pic(Z)` is finite.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Picard

variable {E : Type u} [Field E] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of E)) [IsProper f]
  (hdim : topologicalKrullDim Z ≤ 1)

include hdim in
/-- **The functions on an effective Cartier divisor.** For an effective Cartier divisor `D` on a
scheme proper of dimension at most one over a finite field with `q` elements, `D` is affine and
`Γ(D, 𝒪_D)` is finite with `q ^ dim_E Γ(D, 𝒪_D)` elements. -/
theorem finite_and_natCard_globalSections_divisor [Finite E] (D : Z.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Algebra E Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of E)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    IsAffine D.subscheme ∧ Module.Finite E Γ(D.subscheme, ⊤) ∧ Finite Γ(D.subscheme, ⊤) ∧
      Nat.card Γ(D.subscheme, ⊤) = Nat.card E ^ Module.finrank E Γ(D.subscheme, ⊤) := by
  let : Algebra E Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of E)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have : IsFinite (D.subschemeι ≫ f) := isFinite_divisorSubscheme E f hdim D
  have : IsAffine D.subscheme := isAffine_of_isAffineHom (D.subschemeι ≫ f)
  have hfin : Module.Finite E Γ(D.subscheme, ⊤) := by
    have hiso : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of E)).inv).hom :=
      (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (CommRingCat.of E)).inv)).surjective
    have h : ((Scheme.ΓSpecIso (.of E)).inv ≫ (D.subschemeι ≫ f).appTop).hom.Finite := by
      rw [CommRingCat.hom_comp]
      exact RingHom.Finite.comp (Scheme.Hom.finite_appTop (D.subschemeι ≫ f))
        (RingHom.Finite.of_surjective _ hiso)
    exact h
  have := hfin
  have : Finite Γ(D.subscheme, ⊤) := Module.finite_of_finite E
  refine ⟨inferInstance, hfin, inferInstance, ?_⟩
  have := Fintype.ofFinite E
  have := Fintype.ofFinite Γ(D.subscheme, ⊤)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := E) (V := Γ(D.subscheme, ⊤))]

variable [IsCurve E f] [Smooth f]

include f in
/-- **The torsion of the Picard group of a smooth proper curve over a finite field is finite.** -/
theorem finite_setOf_isOfFinAddOrder [Finite E] :
    {z : ofScheme Z | IsOfFinAddOrder z}.Finite := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim : topologicalKrullDim Z ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hdvr : ∀ x : Z, IsClosed ({x} : Set Z) → IsDiscreteValuationRing (Z.presheaf.stalk x) :=
    fun x hx => IsCurve.isDiscreteValuationRing_stalk_of_isClosed E f hx
  -- a closed point and its divisor
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨P₀, -, hP₀⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  have := hdvr P₀ hP₀
  set D₀ := Scheme.IdealSheafData.vanishingIdeal (⟨{P₀}, hP₀⟩ : Closeds Z)
  have hD₀ : Stacks.Divisors.IsEffectiveCartierDivisor D₀ :=
    isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing hP₀
  set c₀ := Stacks.Divisors.picardClass D₀
  set δ := picardDegree f hdim c₀
  have hδ : 1 ≤ δ := by
    obtain ⟨-, hfin, -, -⟩ := finite_and_natCard_globalSections_divisor f hdim D₀
    let : Algebra E Γ(D₀.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of E)).inv ≫ (D₀.subschemeι ≫ f).appTop).hom.toAlgebra
    have hne : Nonempty D₀.subscheme := by
      have : P₀ ∈ Set.range D₀.subschemeι := by
        rw [D₀.range_subschemeι]
        simp [D₀]
      obtain ⟨y, -⟩ := this
      exact ⟨y⟩
    have : Nonempty (⊤ : D₀.subscheme.Opens) := ⟨⟨hne.some, trivial⟩⟩
    have hpos : 0 < Module.finrank E Γ(D₀.subscheme, ⊤) := Module.finrank_pos
    rw [show δ = _ from picardDegree_divisorPicardClass f hdim D₀]
    exact_mod_cast hpos
  set g := genus f
  -- the effective representatives
  set M := Nat.card E ^ (g * δ.toNat)
  set Φ : Z.IdealSheafData → ofScheme Z := fun D =>
    if h : Stacks.Divisors.IsEffectiveCartierDivisor D then
      @Stacks.Divisors.picardClass _ D h - (g : ℤ) • c₀ else 0
  refine ((finite_setOf_idealSheafData_natCard_le f hdvr M).image Φ).subset ?_
  intro z hz
  -- a torsion class has degree zero
  have hz0 : picardDegree f hdim z = 0 := by
    obtain ⟨n, hn, hnz'⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (show IsOfFinAddOrder z from hz)
    have hnz := congrArg (picardDegree f hdim) hnz'
    rw [map_nsmul, map_zero, nsmul_eq_mul] at hnz
    exact (mul_eq_zero.1 hnz).resolve_left (by exact_mod_cast hn.ne')
  set w := z + (g : ℤ) • c₀
  have hw : picardDegree f hdim w = g * δ := by
    rw [map_add, map_zsmul, hz0, zero_add, smul_eq_mul]
  obtain ⟨D, hD, hDw⟩ := exists_divisorPicardClass_eq_of_genus_le f hdim w (by
    rw [hw]
    nlinarith [Int.natCast_nonneg g])
  obtain ⟨haff, -, hfin, hcard⟩ := finite_and_natCard_globalSections_divisor f hdim D
  refine ⟨D, ⟨haff, hfin, ?_⟩, ?_⟩
  · rw [hcard]
    refine le_of_eq (congrArg _ ?_)
    have h := picardDegree_divisorPicardClass f hdim D
    rw [hDw, hw] at h
    have h' : ((g * δ.toNat : ℕ) : ℤ) = g * δ := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
    omega
  · simp only [Φ, dif_pos hD, hDw, w, add_sub_cancel_right]

end Stacks.Picard

end
