module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingGorenstein
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizingSupplement

/-!
# `ω_E ≅ 𝒪_E(-1)` for the blowup of a Gorenstein rational surface singularity

In Situation [Stacks, Tag 0B4W] with `A` not regular, let `X` be the blowup of `Spec(A)` in the
maximal ideal, let `i : E ⟶ X` be its exceptional curve and let `ω_X` be the dualizing module of
`X` normalized relative to a dualizing module `ω_A` of `A`. When `A` is Gorenstein, that is
`ω_A ≅ A`, and `i^*ω_X` is globally generated, the dualizing module `ω_E` of [Stacks, Tag 0B64]
is isomorphic to `𝒪_E(-1)`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwistSheaf`:
  `ω_E ≅ 𝒪_E(-1)` when `A` is Gorenstein.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

/-- In Situation [Stacks, Tag 0B4W] with `A` not regular and Gorenstein, so `ω_A ≅ A`, and with
generating sections `G` of the pullback of `ω_X` to the exceptional curve `E` of the blowup of
`Spec(A)` in the maximal ideal, the dualizing module `ω_E` is isomorphic to `𝒪_E(-1)`. -/
theorem nonempty_exceptionalDualizingModule_iso_curveTwistSheaf
    (S : RationalSingularitySituation.{u}) (hnot : ¬ IsRegularLocalRing S.A)
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : ωA ≅ ModuleCat.of S.A S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).NormalizedDualizingModule ωA ωX)
    (G : SheafOfModules.GeneratingSections
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX)) :
    Nonempty (exceptionalDualizingModule S.A ωX ≅ curveTwistSheaf S.A (-1)) := by
  obtain ⟨hG⟩ := nonempty_iso_structureModule_of_iso_self S hnot ωA hωA e ωX N G
  obtain ⟨h1⟩ := nonempty_exceptionalDualizingModule_iso_curveTwist S.A ωX
  have hpull : (Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX ≅
      Scheme.unitModule (exceptionalCurve S.A) :=
    (Scheme.Modules.pullback (exceptionalImmersion S.A)).mapIso hG ≪≫
      Scheme.Modules.pullbackUnitIso (exceptionalImmersion S.A)
  have hm : Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX)
        (curveTwistSheaf S.A (-1)) ≅
      Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        (Scheme.unitModule (exceptionalCurve S.A)) (curveTwistSheaf S.A (-1)) :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso (exceptionalCurve S.A) hpull (Iso.refl _)
  have hb : Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        (Scheme.unitModule (exceptionalCurve S.A)) (curveTwistSheaf S.A (-1)) ≅
      Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        (curveTwistSheaf S.A (-1)) (Scheme.unitModule (exceptionalCurve S.A)) :=
    Stacks.SheafOfModules.tensorSheafBraiding (exceptionalCurve S.A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve S.A)) _ _
  have hu : Stacks.RelativeVeryAmple.tensorModules (exceptionalCurve S.A)
        (curveTwistSheaf S.A (-1)) (Scheme.unitModule (exceptionalCurve S.A)) ≅
      curveTwistSheaf S.A (-1) :=
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (exceptionalCurve S.A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve S.A)) _
  exact ⟨h1 ≪≫ hm ≪≫ hb ≪≫ hu⟩

end AlgebraicGeometry.BlowUpDualizing

end
