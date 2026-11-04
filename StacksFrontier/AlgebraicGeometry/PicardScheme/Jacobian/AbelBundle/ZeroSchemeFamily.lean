module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Zero schemes of sections nonvanishing on the fibres of a relative curve

Let `π : Y ⟶ T` be smooth of relative dimension one and proper with integral fibres, `ℳ` an
invertible `𝒪_Y`-module and `s` a global section of `ℳ` which vanishes identically on no fibre.
Then the zero scheme `Z(s)` is a relative effective Cartier divisor over `T` ([Stacks, Tag 062Y]:
it is locally principal and meets every fibre in an effective Cartier divisor, the fibre being
integral), hence finite locally free over `T` since `π` is proper ([Stacks, Tag 0B9D]); its rank at
`t` is the degree of `ℳ` on the fibre over `t` ([Stacks, Tag 0AYY], rank one case).

This is the family-level half of the identification of the Hilbert scheme of a curve with a
projective bundle over its Jacobian; the rank-one case is the claim in the proof of
[Stacks, Tag 0B9X].

## Main results

* `AlgebraicGeometry.isRelativeEffectiveCartierDivisor_zeroScheme_of_ne_zero`.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_zeroScheme_of_ne_zero`.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

variable {Y T : Scheme.{u}} (π : Y ⟶ T) [SmoothOfRelativeDimension 1 π] [IsProper π]

omit [IsProper π] in
/-- **The zero scheme of a section vanishing identically on no integral fibre of a flat relative
scheme is a relative effective Cartier divisor** ([Stacks, Tag 062Y], [Stacks, Tag 0B6Y]). -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme_of_ne_zero
    (hint : ∀ t : T, IsIntegral (π.fiber t)) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (s : Γ(M, ⊤)) (hs : ∀ t : T, pullbackGlobalSections (π.fiberι t) M s ≠ 0) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor π (Stacks.Divisors.zeroScheme Y M s) := by
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  exact Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres π _
    (isLocallyPrincipal_zeroScheme _ M s) fun t =>
      have := hint t
      isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero (π.fiberι t) M s (hs t)

/-- **The zero scheme of a section vanishing identically on no fibre of a smooth proper relative
curve with integral fibres is a relative effective Cartier divisor, finite locally free over the
base, of degree the fibre degree of the module.** -/
@[sga "4 XVIII 1.3.2.1" "partial"]
theorem isFiniteLocallyFreeOfRank_zeroScheme_of_ne_zero
    (hint : ∀ t : T, IsIntegral (π.fiber t)) (hdim : ∀ t : T, topologicalKrullDim (π.fiber t) ≤ 1)
    (M : Y.Modules) (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (s : Γ(M, ⊤)) (hs : ∀ t : T, pullbackGlobalSections (π.fiberι t) M s ≠ 0) (d : ℕ)
    (hdeg : ∀ t : T, relativeInvertibleDegreeHomAt π hdim t
      (Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M hM) = d) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor π (Stacks.Divisors.zeroScheme Y M s) ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((Stacks.Divisors.zeroScheme Y M s).subschemeι ≫ π) d := by
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  set D := Stacks.Divisors.zeroScheme Y M s with hDdef
  have hfibD : ∀ t : T, Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (π.fiberι t)) :=
    fun t =>
      have := hint t
      isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero (π.fiberι t) M s (hs t)
  have hRel : Stacks.Divisors.IsRelativeEffectiveCartierDivisor π D :=
    Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres π D
      (isLocallyPrincipal_zeroScheme _ M s) hfibD
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hRel.1
  have hclD : Stacks.Divisors.picardClass D = Stacks.SheafOfModules.picardClass Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) M hM :=
    picardClass_zeroScheme M hM s
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree (D.subschemeι ≫ π) :=
    (isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper π D).2 hRel
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 hflf
  refine ⟨hRel, (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).2 ?_⟩
  intro t
  have := hfibD t
  have hr := isFiniteLocallyFreeOfRank_of_fiber π D t
  have hdeg₁ := invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank
    (T.residueField t) (π.fiberToSpecResidueField t) (hdim t) (D.comap (π.fiberι t))
    ((D.subschemeι ≫ π).finrank t)
  have : Stacks.Divisors.IsPullbackDefined (π.fiberι t) D := hfibD t
  rw [← Stacks.Divisors.schemePullbackClass_picardClass, hclD] at hdeg₁
  have h := (hdeg t).symm.trans ((relativeInvertibleDegreeHomAt_apply π hdim t _).trans hdeg₁)
  exact_mod_cast h.symm

end AlgebraicGeometry

end
