module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantNonzero

/-!
# The zero scheme of a family of sections

Let `Y ⟶ S` be flat and locally of finite presentation, with integral fibres, let `ℒ` be an
invertible `𝒪_Y`-module and `s` a global section of `ℒ` which is nonzero on every fibre. Then the
zero scheme `Z(s)` is a relative effective Cartier divisor on `Y` over `S`.

## Main results

* `Stacks.AbelMap.isLocallyPrincipal_zeroScheme`: the zero scheme of a section of an invertible
  module is locally principal.
* `Stacks.AbelMap.isRelativeEffectiveCartierDivisor_zeroScheme`: for `Y ⟶ S` flat and locally
  of finite presentation with integral fibres, the zero scheme of a section nonzero on every
  fibre is a relative effective Cartier divisor.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.AbelMap

variable {Y : Scheme.{u}} (L : Y.Modules)
  [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]

/-- **The zero scheme of a section of an invertible module is locally principal**: on an affine
open where the module is free on a generator `g`, the section is `b • g` and the zero scheme is
cut out by `b`. -/
theorem isLocallyPrincipal_zeroScheme (s : Γ(L, ⊤)) :
    Stacks.Divisors.IsLocallyPrincipal (zeroScheme Y L s) := by
  intro y
  have hL : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L).2 ‹_›
  obtain ⟨W, hyW, a, hbij⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyW W.2
  obtain ⟨b, hb⟩ := (hbij V hVW).2 (L.presheaf.map (homOfLE le_top).op s)
  refine ⟨⟨V, hV⟩, hyV, ⟨b, ?_⟩⟩
  rw [zeroScheme_ideal_eq_span_singleton_of_bijective_smul Y L s ⟨V, hV⟩ _ (hbij V hVW) b hb.symm]

/-- **The zero scheme of a family of sections nonzero on every fibre is a relative effective
Cartier divisor.** -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme {S : Scheme.{u}} (fY : Y ⟶ S) [Flat fY]
    [LocallyOfFinitePresentation fY] [∀ t : S, IsIntegral (fY.fiber t)] (s : Γ(L, ⊤))
    (hfib : ∀ t : S, AlgebraicGeometry.pullbackGlobalSections (fY.fiberι t) L s ≠ 0) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor fY (zeroScheme Y L s) := by
  refine Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres fY _
    (isLocallyPrincipal_zeroScheme L s) fun t => ?_
  rw [← Stacks.Divisors.zeroScheme_pullback]
  exact isEffectiveCartierDivisor_zeroScheme_of_ne_zero _ _ (hfib t)

end Stacks.AbelMap

end
