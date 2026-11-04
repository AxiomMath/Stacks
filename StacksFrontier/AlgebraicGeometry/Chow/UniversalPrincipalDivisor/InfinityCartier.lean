module

public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier
import all StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier

/-!
# The infinity divisor of `ℙ¹_S` is an effective Cartier divisor

Let `S` be a scheme and `D_∞ ⊆ ℙ¹_S` the infinity divisor, the closed subscheme cut out by the
kernel ideal sheaf of the infinity section. This file proves that `D_∞` is an effective Cartier
divisor, which together with
`Stacks.Chow.lineZeroDivisor_isEffectiveCartierDivisor` completes the Cartier half of Tag 02RQ
part (3).

The zero-divisor statement does not transport to this one. The affine chart
`Stacks.Chow.affineChart` of `ℙ¹_S` is the base change of the *first* chart of the two-chart
gluing of `ℙ¹_ℤ`, and `D_∞` is the unit ideal there
(`Stacks.Chow.lineInfinityDivisor_ideal_comap_affineChart`), so that chart records nothing about
the support of `D_∞`; and there is no automorphism of `ℙ¹_ℤ` exchanging the two charts in this
development. What is needed instead is the *second* chart, and that is what this file adds:
`Stacks.Chow.affineYChart`, the base change of `AlgebraicGeometry.projectiveLineYChart` along
the terminal morphism of `S`.

Both charts of `ℙ¹_ℤ` have the same source `Spec ℤ[T]`, so the second chart of `ℙ¹_S` is an open
immersion of the *same* scheme
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOver S` with the *same* coordinate
`Stacks.Chow.affineCoordinate S`. Consequently nothing about nonzerodivisors has to be redone:
`Stacks.Chow.exists_affineOpens_isRegular_affineCoordinate` applies to the second chart
verbatim, and the only new work is the local equation of `D_∞` on it. That equation is the
computation of `Stacks.Chow.zeroDivisor_ideal_comap_affineChart` with the second chart in place
of the first, and it is available because the point `∞` of `ℙ¹_ℤ` is the origin of the second
chart exactly as `0` is the origin of the first: both are
`Stacks.Chow.integralAffineZeroSection`, read in the respective chart.

## Main definitions

* `Stacks.Chow.affineYChart`: the second affine chart `𝔸¹_S ⟶ ℙ¹_S`, the base change of the
  second chart of the two-chart gluing of `ℙ¹_ℤ`.

## Main results

* `Stacks.Chow.infinityDivisor_ideal_comap_affineYChart`: **in the coordinate of the second
  chart, `D_∞` is cut out by the coordinate itself.**
* `Stacks.Chow.lineInfinityDivisor_isEffectiveCartierDivisor`: **`D_∞` is an effective Cartier
  divisor.**

## Implementation notes

The chain of lemmas mirrors the first chart one for one — `Stacks.Chow.affineYChart_comp`,
`Stacks.Chow.isPullback_affineYChart`, `Stacks.Chow.isOpenImmersion_affineYChart`,
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineConstantSection_comp_affineYChart`,
`Stacks.Chow.comap_lineInfinityDivisor_affineYChart` — because
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineConstantSection` and
`Stacks.Chow.ker_ideal_top_integralAffineZeroSection` are already stated for an arbitrary point
of `𝔸¹_ℤ` and are reused unchanged.

The criterion is applied in the form
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen`, which asks for a
principal-on-a-nonzerodivisor presentation around *every* point of `ℙ¹_S`. Away from the second
chart there is nothing to do: the support of `D_∞` is the image of the infinity section, which
factors through that chart, so
`Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_notMem_support` applies there.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The second affine chart of `ℙ¹_S` -/

/-- The canonical morphism `𝔸¹_S ⟶ ℙ¹_S` onto the second chart, the base change of the second
chart of the two-chart gluing of `ℙ¹_ℤ`. Its source is the same `𝔸¹_S` as that of
`Stacks.Chow.affineChart`, because both charts of `ℙ¹_ℤ` have source `Spec ℤ[T]`. -/
def affineYChart (S : Scheme.{u}) : affineLineOver S ⟶ relativeProjectiveLine S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ projectiveLineYChart (ULift.{u} ℤ)) (by simp)

/-- The second affine chart lies over `S`. -/
@[simp]
theorem affineYChart_comp (S : Scheme.{u}) :
    affineYChart S ≫ (relativeProjectiveLine S ↘ S) = pullback.fst _ _ := by
  show affineYChart S ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The second affine chart is the base change of the chart `𝔸¹_ℤ ⟶ ℙ¹_ℤ` with coordinate `y`
along the projection of `ℙ¹_S` to `ℙ¹_ℤ`. -/
theorem isPullback_affineYChart (S : Scheme.{u}) :
    IsPullback (affineYChart S)
      (pullback.snd (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))))
      (projectiveLineYChart (ULift.{u} ℤ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ)))) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  rw [show affineYChart S ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ))) = pullback.fst _ _ from affineYChart_comp S,
    show projectiveLineYChart (ULift.{u} ℤ) ≫ terminal.from (projectiveLine (ULift.{u} ℤ)) =
      terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))) from terminal.hom_ext _ _]
  exact IsPullback.of_hasPullback _ _

/-- The second affine chart is an open immersion. -/
instance isOpenImmersion_affineYChart (S : Scheme.{u}) : IsOpenImmersion (affineYChart S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_affineYChart S).flip inferInstance

/-- A constant section of `𝔸¹_S` becomes, in the second chart, the corresponding constant
section of `ℙ¹_S`. -/
theorem affineLineConstantSection_comp_affineYChart (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))) :
    affineLineConstantSection S e ≫ affineYChart S =
      lineConstantSection S (e ≫ projectiveLineYChart (ULift.{u} ℤ)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineYChart, pullback.lift_fst, affineLineConstantSection,
      pullback.lift_fst, lineConstantSection, pullback.lift_fst]
  · rw [Category.assoc, affineYChart, pullback.lift_snd, ← Category.assoc,
      affineLineConstantSection, pullback.lift_snd, lineConstantSection, pullback.lift_snd,
      Category.assoc]

/-- The point `∞` of `ℙ¹_ℤ` is the point `0` of `𝔸¹_ℤ`, read in the second chart. -/
theorem integralAffineZeroSection_comp_projectiveLineYChart :
    integralAffineZeroSection.{u} ≫ projectiveLineYChart (ULift.{u} ℤ) =
      integralInfinitySection.{u} := by
  rw [integralAffineZeroSection, integralInfinitySection, Category.assoc]

/-- The infinity section of `ℙ¹_S` factors through the second affine chart. -/
theorem lineInfinitySection_eq (S : Scheme.{u}) :
    affineLineConstantSection S integralAffineZeroSection ≫ affineYChart S =
      lineInfinitySection S := by
  rw [affineLineConstantSection_comp_affineYChart,
    integralAffineZeroSection_comp_projectiveLineYChart]

/-! ### The local equation of `D_∞` on the second chart -/

/-- `D_∞` meets the second affine chart in the zero section of `𝔸¹_S`. -/
theorem comap_lineInfinityDivisor_affineYChart (S : Scheme.{u}) :
    (lineInfinityDivisor S).comap (affineYChart S) =
      (affineLineConstantSection S integralAffineZeroSection).ker := by
  have hpb : IsPullback (affineLineConstantSection S integralAffineZeroSection) (𝟙 S)
      (affineYChart S) (lineInfinitySection S) := by
    refine IsPullback.of_vert_isIso_mono ⟨?_⟩
    rw [Category.id_comp]
    exact lineInfinitySection_eq S
  rw [lineInfinityDivisor, ← AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hpb]

/-- **In the coordinate of the second chart, `D_∞` is cut out by the coordinate itself.** -/
theorem infinityDivisor_ideal_comap_affineYChart (S : Scheme.{u})
    (V : (affineLineOver S).affineOpens) :
    ((lineInfinityDivisor S).comap (affineYChart S)).ideal V =
      Ideal.span {(affineLineOver S).presheaf.map (homOfLE le_top).op (affineCoordinate S)} := by
  rw [comap_lineInfinityDivisor_affineYChart, ker_affineLineConstantSection,
    Stacks.IdealSheaf.ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ V le_top,
    ker_ideal_top_integralAffineZeroSection, Ideal.map_span, Set.image_singleton]
  rfl

/-- The support of `D_∞` lies in the second affine chart. -/
theorem range_lineInfinitySection_subset_range_affineYChart (S : Scheme.{u}) :
    Set.range (lineInfinitySection S) ⊆ Set.range (affineYChart S) := by
  rw [← lineInfinitySection_eq, range_comp_scheme]
  exact Set.image_subset_range _ _

/-! ### `D_∞` is an effective Cartier divisor -/

/-- **Stacks Project, Tag 02RQ part (3), the infinity divisor.** `D_∞ ⊆ ℙ¹_S` is an effective
Cartier divisor: on the second affine chart it is cut out by the coordinate `T`, which is a
nonzerodivisor on the inverse image of any affine open of `S`, and away from that chart it is
the unit ideal. -/
theorem lineInfinityDivisor_isEffectiveCartierDivisor (S : Scheme.{u}) :
    Stacks.Divisors.IsEffectiveCartierDivisor (lineInfinityDivisor S) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun p => ?_
  by_cases hp : p ∈ Set.range (affineYChart S)
  · obtain ⟨v, rfl⟩ := hp
    obtain ⟨V, hvV, hreg⟩ := exists_affineOpens_isRegular_affineCoordinate S v
    refine ⟨affineYChart S ''ᵁ V.1, V.2.image_of_isOpenImmersion _, ⟨v, hvV, rfl⟩,
      ((affineYChart S).appIso V.1).inv
        ((affineLineOver S).presheaf.map (homOfLE (le_top (a := V.1))).op
          (affineCoordinate S)), isRegular_of_iso ((affineYChart S).appIso V.1).symm hreg, ?_⟩
    have h1 := infinityDivisor_ideal_comap_affineYChart S V
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h1
    have hsurj : Function.Surjective ((affineYChart S).appIso V.1).inv.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    rw [← Ideal.map_comap_of_surjective _ hsurj
      ((lineInfinityDivisor S).ideal ⟨affineYChart S ''ᵁ V.1, V.2.image_of_isOpenImmersion _⟩),
      h1, Ideal.map_span, Set.image_singleton]
  · refine Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_notMem_support _ p
      (fun hps => hp ?_)
    exact range_lineInfinitySection_subset_range_affineYChart S
      ((coe_support_lineInfinityDivisor S).le hps)

end Stacks.Chow

end
