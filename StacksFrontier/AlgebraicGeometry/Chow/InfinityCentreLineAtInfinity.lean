module

public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSection

/-!
# The projective line of the centre inside the blowup at infinity

Let `X` be a scheme, `i : Z ⟶ X` a closed immersion with ideal sheaf `ℐ = ker i`, and let
`b : W ⟶ 𝐏¹_X` be the blowup of `𝐏¹_X` in the centre `∞(Z)`, with exceptional divisor `E`, fibre
at infinity `W_∞ = b⁻¹((𝐏¹_X)_∞)`, strict transform `X' ⊆ W` of `X`, and with the closed
immersion `𝐏¹_Z ⟶ W` of `Stacks.Chow.lineToBlowupAtInfinity`, whose composite with `b` is the
inclusion `𝐏¹_Z ⟶ 𝐏¹_X`. Assertion (8) of Stacks 0FBG, which is Stacks 0FE9, adds that the base
change of `𝐏¹_Z ⟶ W` by `∞`, that is along `W_∞ ⟶ W`, is the composite

  `Z ⟶ C_ZX ⟶ E ⟶ W_∞`

of the vertex (zero section) of the normal cone, the open immersion `C_ZX ≅ E ∖ X' ⊆ E` of
Stacks 0FBH and the inclusion `E ⊆ W_∞`. Here the fibre `(𝐏¹_Z)_∞` of `𝐏¹_Z` at infinity is `Z`
itself, through the infinity section.

## Main results

* `Stacks.Chow.comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity` and
  `Stacks.Chow.comap_fibreIdealAtInfinity_lineToBlowupAtInfinity` — `E` and `W_∞` restrict to the
  divisor at infinity of `𝐏¹_Z`.
* `Stacks.Chow.comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity` — `𝐏¹_Z` misses `X'`.
* `Stacks.Chow.comap_residualIdealAtInfinity_lineToBlowupAtInfinity` — the residual ideal `𝒟`
  (`Stacks.Chow.residualIdealAtInfinity ℐ ℐ`) vanishes on `𝐏¹_Z`.
* `Stacks.Chow.lineInfinitySection_lineToBlowupAtInfinity` — the infinity section of `𝐏¹_Z`
  followed by `𝐏¹_Z ⟶ W` is the vertex `Z ⟶ C_ZX` followed by `C_ZX ⟶ E ⟶ W`.
* `Stacks.Chow.isPullback_lineToBlowupAtInfinity_fibreIdealAtInfinity` — the base change of
  `𝐏¹_Z ⟶ W` along `W_∞ ⟶ W` is `Z ⟶ C_ZX ⟶ E ⟶ W_∞`, and
  `Stacks.Chow.isPullback_lineToBlowupAtInfinity_modificationFibreAtInfinity` — the same with
  `W_∞` the fibre at infinity of the modification `W ⟶ X ×_S 𝐏¹_S` and `C_ZX ⟶ W_∞` the open
  immersion `Stacks.Chow.normalConeToFibreAtInfinity`.
* `Stacks.Chow.lineToBlowupAtInfinity_spec` — **Stacks 0FE9**: the closed immersion
  `𝐏¹_Z ⟶ W`, its triangle over `𝐏¹_X` and its base change by `∞`.

## Implementation notes

The closed subscheme is an arbitrary closed immersion `i : Z ⟶ X`, as for the normal cone
`Stacks.Conormal.normalCone i`, and the blowup is that of the centre cut out by `ker i`. The
projective line of `Stacks.Chow.lineToBlowupAtInfinity` is that of the closed subscheme
`V(ker i)`; it is compared with `Z` through the isomorphism `Z ≅ V(ker i)` of the closed
immersion `i` (`AlgebraicGeometry.Scheme.Hom.toImage`). The base change by `∞` is stated as a
cartesian square whose top arrow is `Z ≅ V(ker i)` followed by the infinity section of
`𝐏¹_{V(ker i)}`, which identifies `Z` with the fibre `(𝐏¹_{V(ker i)})_∞`.

## References

* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-! ### The divisors of `W` restricted to `𝐏¹_Z` -/

section Restriction

/-- **`E` restricts to `(𝐏¹_Z)_∞` on `𝐏¹_Z`**: the centre `∞(Z)` pulls back to the divisor at
infinity of `𝐏¹_Z` along the inclusion `𝐏¹_Z ⟶ 𝐏¹_X`. -/
theorem comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity :
    (exceptionalIdealAtInfinity ℐ).comap (lineToBlowupAtInfinity ℐ) =
      lineInfinityDivisor ℐ.subscheme := by
  show ((infinityCentreIdeal ℐ).comap (blowupAtInfinityToLine ℐ)).comap
    (lineToBlowupAtInfinity ℐ) = _
  rw [← Scheme.IdealSheafData.comap_comp, lineToBlowupAtInfinity_comp,
    comap_infinityCentreIdeal_projectiveLineBaseChange]

/-- **`W_∞` restricts to `(𝐏¹_Z)_∞` on `𝐏¹_Z`**: the divisor at infinity of `𝐏¹_X` pulls back to
that of `𝐏¹_Z`. -/
theorem comap_fibreIdealAtInfinity_lineToBlowupAtInfinity :
    (fibreIdealAtInfinity ℐ).comap (lineToBlowupAtInfinity ℐ) =
      lineInfinityDivisor ℐ.subscheme := by
  rw [fibreIdealAtInfinity, ← Scheme.IdealSheafData.comap_comp, lineToBlowupAtInfinity_comp,
    comap_lineInfinityDivisor_projectiveLineBaseChange]

/-- **`𝐏¹_Z` misses the strict transform `X'`**: the ideal of `X'` pulls back to the unit ideal
on `𝐏¹_Z`. -/
theorem comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity :
    (strictTransformIdealAtInfinity ℐ).comap (lineToBlowupAtInfinity ℐ) = ⊤ := by
  have h := congrArg (fun J => J.comap (lineToBlowupAtInfinity ℐ))
    (fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity ℐ)
  rw [Stacks.IdealSheaf.comap_mul, comap_fibreIdealAtInfinity_lineToBlowupAtInfinity,
    comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity] at h
  refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
    (lineInfinityDivisor_isEffectiveCartierDivisor ℐ.subscheme) ?_
  rw [Scheme.IdealSheafData.mul_top]
  exact h.symm

/-- The points of `𝐏¹_Z` land in `W ∖ X'`. -/
theorem lineToBlowupAtInfinity_notMem_support_strictTransformIdealAtInfinity
    (w : relativeProjectiveLine ℐ.subscheme) :
    lineToBlowupAtInfinity ℐ w ∉ (strictTransformIdealAtInfinity ℐ).support := by
  intro hw
  have h : w ∈ ((strictTransformIdealAtInfinity ℐ).comap (lineToBlowupAtInfinity ℐ)).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  rwa [comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity,
    Scheme.IdealSheafData.support_top] at h

/-- **The residual ideal vanishes on `𝐏¹_Z`**: the residual ideal `𝒟` of `ℐ · 𝒪_W = E + 𝒟`
pulls back to the zero ideal on `𝐏¹_Z`. -/
theorem comap_residualIdealAtInfinity_lineToBlowupAtInfinity :
    (residualIdealAtInfinity ℐ ℐ).comap (lineToBlowupAtInfinity ℐ) = ⊥ := by
  have hZ : ℐ.comap ℐ.subschemeι = ⊥ := by
    have := ker_comap_self ℐ.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  have h := congrArg (fun J => J.comap (lineToBlowupAtInfinity ℐ))
    (comap_blowupAtInfinityToBase_eq_mul_residualIdealAtInfinity (le_refl ℐ))
  rw [Stacks.IdealSheaf.comap_mul, comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity,
    ← Scheme.IdealSheafData.comap_comp, blowupAtInfinityToBase, ← Category.assoc,
    lineToBlowupAtInfinity_comp, projectiveLineBaseChange_over, Scheme.IdealSheafData.comap_comp,
    hZ, Scheme.IdealSheafData.comap_bot] at h
  refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
    (lineInfinityDivisor_isEffectiveCartierDivisor ℐ.subscheme) ?_
  rw [Scheme.IdealSheafData.mul_bot]
  exact h.symm

end Restriction

/-! ### The fibre of `𝐏¹_Z ⟶ W` at infinity -/

section Fibre

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The infinity section of `𝐏¹_Z`, followed by `𝐏¹_Z ⟶ W`, is the vertex of the cone followed
by `C_ZX ⟶ E ⟶ W`.** Here `Z` is identified with `V(ker i)` through `i.toImage`. -/
theorem lineInfinitySection_lineToBlowupAtInfinity :
    i.toImage ≫ lineInfinitySection i.ker.subscheme ≫ lineToBlowupAtInfinity i.ker =
      normalConeZeroSection i ≫ normalConeToExceptionalDivisor i ≫
        (exceptionalIdealAtInfinity i.ker).subschemeι := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = i.toImage ≫ lineInfinitySection i.ker.subscheme ≫
      lineToBlowupAtInfinity i.ker := ⟨_, rfl⟩
  have hE : (exceptionalIdealAtInfinity i.ker).subschemeι.ker ≤ ψ.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, le_ker_iff_comap_eq_bot, hψ,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      comap_exceptionalIdealAtInfinity_lineToBlowupAtInfinity, lineInfinityDivisor,
      ker_comap_self, Scheme.IdealSheafData.comap_bot]
  obtain ⟨ψE, hψE⟩ : ∃ ψE, ψE = IsClosedImmersion.lift _ ψ hE := ⟨_, rfl⟩
  have hψE' : ψE ≫ (exceptionalIdealAtInfinity i.ker).subschemeι = ψ := by
    rw [hψE]
    exact IsClosedImmersion.lift_fac _ _ _
  have hR : Set.range ψE ⊆ Set.range (exceptionalCompl i.ker).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (exceptionalIdealAtInfinity i.ker).subschemeι (ψE z) ∈
      strictTransformComplAtInfinity i.ker
    rw [← Scheme.Hom.comp_apply, hψE', hψ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact lineToBlowupAtInfinity_notMem_support_strictTransformIdealAtInfinity i.ker _
  obtain ⟨ψC, hψC⟩ : ∃ ψC, ψC = IsOpenImmersion.lift (exceptionalCompl i.ker).ι ψE hR ≫
      (normalConeIsoExceptionalCompl i).inv := ⟨_, rfl⟩
  have hψC' : ψC ≫ normalConeToExceptionalDivisor i = ψE := by
    rw [hψC, normalConeToExceptionalDivisor, Category.assoc, Iso.inv_hom_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  have hO : (normalConeZeroSection i).ker ≤ ψC.ker := by
    rw [ker_normalConeZeroSection, le_ker_iff_comap_eq_bot, normalConeZeroSectionIdeal,
      ← Scheme.IdealSheafData.comap_comp, reassoc_of% hψC', hψE', hψ,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      comap_residualIdealAtInfinity_lineToBlowupAtInfinity, Scheme.IdealSheafData.comap_bot,
      Scheme.IdealSheafData.comap_bot]
  have hi : ψC ≫ normalConeToX i = i := by
    rw [← normalConeIsoExceptionalCompl_hom_toX i]
    have hC : ψC ≫ (normalConeIsoExceptionalCompl i).hom ≫ (exceptionalCompl i.ker).ι = ψE := by
      rw [← hψC', normalConeToExceptionalDivisor]
    rw [exceptionalComplToX, reassoc_of% hC, reassoc_of% hψE', hψ, blowupAtInfinityToBase,
      Category.assoc, Category.assoc, reassoc_of% (lineToBlowupAtInfinity_comp i.ker),
      projectiveLineBaseChange_over, reassoc_of% (lineInfinitySection_comp i.ker.subscheme)]
    exact Scheme.Hom.toImage_imageι i
  have hg : IsClosedImmersion.lift (normalConeZeroSection i) ψC hO = 𝟙 Z := by
    rw [← cancel_mono i, Category.id_comp]
    calc IsClosedImmersion.lift (normalConeZeroSection i) ψC hO ≫ i
        = IsClosedImmersion.lift (normalConeZeroSection i) ψC hO ≫ normalConeZeroSection i ≫
            normalConeToX i := by rw [normalConeZeroSection_toX]
      _ = i := by rw [IsClosedImmersion.lift_fac_assoc, hi]
  rw [← hψ, ← hψE', ← hψC', ← IsClosedImmersion.lift_fac (normalConeZeroSection i) ψC hO, hg,
    Category.id_comp, Category.assoc]

/-- **The base change of `𝐏¹_Z ⟶ W` by `∞` is `Z ⟶ C_ZX ⟶ E ⟶ W_∞`.** The square

  `Z ⟶ 𝐏¹_Z`, `Z ⟶ W_∞`, `𝐏¹_Z ⟶ W`, `W_∞ ⟶ W`

is cartesian, where `Z ⟶ 𝐏¹_Z` is `Z ≅ V(ker i)` followed by the infinity section (identifying `Z`
with the fibre `(𝐏¹_Z)_∞`), and `Z ⟶ W_∞` is the vertex `Z ⟶ C_ZX` of the normal cone, followed by
the open immersion `C_ZX ⟶ E` of Stacks 0FBH and the inclusion `E ⊆ W_∞`. -/
theorem isPullback_lineToBlowupAtInfinity_fibreIdealAtInfinity :
    IsPullback (i.toImage ≫ lineInfinitySection i.ker.subscheme)
      (normalConeZeroSection i ≫ normalConeToExceptionalDivisor i ≫
        Scheme.IdealSheafData.inclusion (fibreIdealAtInfinity_le_exceptionalIdealAtInfinity i.ker))
      (lineToBlowupAtInfinity i.ker) (fibreIdealAtInfinity i.ker).subschemeι := by
  refine isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι]
    exact lineInfinitySection_lineToBlowupAtInfinity i
  · rw [Scheme.IdealSheafData.ker_subschemeι, comap_fibreIdealAtInfinity_lineToBlowupAtInfinity,
      Scheme.Hom.ker_comp_of_isIso, lineInfinityDivisor]

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- **The base change of `𝐏¹_Z ⟶ W` by `∞`, with `W_∞` the fibre at infinity of the modification
`W ⟶ X ×_S 𝐏¹_S`**: it is the vertex `Z ⟶ C_ZX` followed by the open immersion
`j : C_ZX ⟶ W_∞` of Stacks 0FBH. -/
theorem isPullback_lineToBlowupAtInfinity_modificationFibreAtInfinity :
    IsPullback (i.toImage ≫ lineInfinitySection i.ker.subscheme)
      (normalConeZeroSection i ≫ normalConeToFibreAtInfinity i f)
      (lineToBlowupAtInfinity i.ker)
      (modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f)) := by
  refine isPullback_of_isClosedImmersion _ _ _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, normalConeToFibreAtInfinity_inclusion]
    exact lineInfinitySection_lineToBlowupAtInfinity i
  · rw [ker_modificationInclusionAtInfinity_blowupAtInfinity,
      comap_fibreIdealAtInfinity_lineToBlowupAtInfinity, Scheme.Hom.ker_comp_of_isIso,
      lineInfinityDivisor]

/-- Let `Z ⊆ X` be the closed subscheme of the closed immersion `i`, let `b : W ⟶ 𝐏¹_X` be the
blowup of `𝐏¹_X` in `∞(Z)`, with exceptional divisor `E` and fibre at infinity `W_∞`. Then
`lineToBlowupAtInfinity : 𝐏¹_Z ⟶ W` is a closed immersion, its composite with `b` is the
inclusion `𝐏¹_Z ⟶ 𝐏¹_X`, and its base change by `∞` (along `W_∞ ⟶ W`, with `(𝐏¹_Z)_∞ = Z`) is
the composite `Z ⟶ C_ZX ⟶ E ⟶ W_∞` of the vertex of the normal cone, the open immersion
`C_ZX ⟶ E` and the inclusion `E ⊆ W_∞`. -/
@[stacks 0FE9 "a closed immersion P¹_Z → W over P¹_X whose base change by ∞ is \
Z → C_ZX → E → W_∞, the first arrow the vertex of the cone"]
theorem lineToBlowupAtInfinity_spec :
    IsClosedImmersion (lineToBlowupAtInfinity i.ker) ∧
      lineToBlowupAtInfinity i.ker ≫ blowupAtInfinityToLine i.ker =
        projectiveLineBaseChange i.ker.subschemeι ∧
      IsPullback (i.toImage ≫ lineInfinitySection i.ker.subscheme)
        (normalConeZeroSection i ≫ normalConeToExceptionalDivisor i ≫
          Scheme.IdealSheafData.inclusion
            (fibreIdealAtInfinity_le_exceptionalIdealAtInfinity i.ker))
        (lineToBlowupAtInfinity i.ker) (fibreIdealAtInfinity i.ker).subschemeι :=
  ⟨inferInstance, lineToBlowupAtInfinity_comp i.ker,
    isPullback_lineToBlowupAtInfinity_fibreIdealAtInfinity i⟩

end Fibre

end Stacks.Chow

end
