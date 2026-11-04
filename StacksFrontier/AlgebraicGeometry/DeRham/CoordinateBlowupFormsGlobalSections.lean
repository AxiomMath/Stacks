module

public import StacksFrontier.AlgebraicGeometry.BlowUpSeparatedInput.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartMono
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# Clause (1) of Stacks 0FUR is a statement about global sections

Let `R` be a ring, `S = Spec R`, `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X` the coordinate closed immersion
and `b : L ⟶ X` the blowup of `X` along `Z`. Clause (1) of [Stacks, Tag 0FUR] asserts that the
map `Stacks.DeRham.coordinateBlowupFormsDirectImage`

`Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}`

is an isomorphism for every `a ≥ 0`.

The ideal sheaf of the centre is of finite type, so `b` is quasi-compact and quasi-separated and
`b_*Ω^a_{L/S}` is quasi-coherent ([Stacks, Tag 01LC]). Since `X` is affine, the map above is an
isomorphism as soon as the map on global sections

`Γ(X, Ω^a_{X/S}) ⟶ Γ(L, Ω^a_{L/S})`

is invertible.

## Main results

* `Stacks.DeRham.isFiniteType_coordinateIdeal`: the ideal sheaf of the centre is of finite
  type.
* `Stacks.DeRham.quasiCompact_coordinateBlowupToAmbient` and
  `Stacks.DeRham.quasiSeparated_coordinateBlowupToAmbient`: the blowing-up morphism of the
  standard coordinate blowup is quasi-compact and quasi-separated.
* `Stacks.DeRham.isQuasicoherent_pushforward_coordinateBlowupForms`: `b_*Ω^a_{L/S}` is
  quasi-coherent.
* `Stacks.DeRham.isIso_coordinateBlowupFormsDirectImage_of_isIso_appTop`: the map
  `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` is an isomorphism if it is invertible on global sections.
* `Stacks.DeRham.coordinateBlowupFormsDirectImage_eq`: the comparison map of clause (1) is the
  unit of `b^* ⊣ b_*` followed by the direct image of the first canonical map of
  [Stacks, Tag 0G5G], and
  `Stacks.DeRham.mono_pushforward_blowupFormsPullbackMap`: that second factor is a
  monomorphism.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUB](https://stacks.math.columbia.edu/tag/0FUB)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-! ### The centre is of finite type, and the blowing-up morphism is qcqs -/

/-- The ideal sheaf of the centre of the standard coordinate blowup is of finite type. -/
theorem isFiniteType_coordinateIdeal :
    (Stacks.MoreMorphisms.coordinateIdeal R m n).IsFiniteType := by
  intro U
  have hle : U ≤ Stacks.MoreMorphisms.topAffineOpen R m n :=
    (le_top : (U : (coordinateAmbient R m n).Opens) ≤ ⊤)
  rw [← (Stacks.MoreMorphisms.coordinateIdeal R m n).map_ideal hle]
  refine Ideal.FG.map ?_ _
  rw [Stacks.MoreMorphisms.coordinateIdeal_ideal_top]
  exact Ideal.FG.map (Submodule.fg_span (Set.finite_range _)) _

/-- The blowing-up morphism of the standard coordinate blowup is quasi-compact. -/
instance quasiCompact_coordinateBlowupToAmbient :
    QuasiCompact (coordinateBlowupToAmbient R m n) :=
  Stacks.Blowup.quasiCompact_blowUpToBase (isFiniteType_coordinateIdeal R m n)

/-- The blowing-up morphism of the standard coordinate blowup is separated. -/
instance isSeparated_coordinateBlowupToAmbient :
    IsSeparated (coordinateBlowupToAmbient R m n) :=
  Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase _

/-- The blowing-up morphism of the standard coordinate blowup is quasi-separated. -/
instance quasiSeparated_coordinateBlowupToAmbient :
    QuasiSeparated (coordinateBlowupToAmbient R m n) :=
  inferInstance

/-! ### Quasi-coherence of both sides of the comparison -/

/-- The sheaf `Ω^a_{X/S}` of relative differential `a`-forms of the coordinate ambient space is
quasi-coherent. -/
theorem isQuasicoherent_coordinateAmbientForms (a : ℕ) :
    (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n)
      (a : ℤ)).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a

/-- The direct image `b_*Ω^a_{L/S}` of the sheaf of relative differential `a`-forms of the
coordinate blowup is quasi-coherent. -/
theorem isQuasicoherent_pushforward_coordinateBlowupForms (a : ℕ) :
    ((Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)).obj
      (Scheme.Hom.relativeDifferentialForms
        (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n)
        (a : ℤ))).IsQuasicoherent :=
  have : (Scheme.Hom.relativeDifferentialForms
      (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n)
      (a : ℤ)).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a
  inferInstance

/-! ### The reduction of clause (1) to global sections -/

/-- The canonical map `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` of clause (1) of [Stacks, Tag 0FUR] is an
isomorphism as soon as its map on global sections

`Γ(X, Ω^a_{X/S}) ⟶ Γ(L, Ω^a_{L/S})`

is invertible. -/
theorem isIso_coordinateBlowupFormsDirectImage_of_isIso_appTop (a : ℕ)
    (h : IsIso ((coordinateBlowupFormsDirectImage R m n a).app ⊤)) :
    IsIso (coordinateBlowupFormsDirectImage R m n a) :=
  have := isQuasicoherent_coordinateAmbientForms R m n a
  have := isQuasicoherent_pushforward_coordinateBlowupForms R m n a
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ h

/-! ### The comparison map factors through the canonical map of Tag 0G5G -/

/-- The comparison map of clause (1) of [Stacks, Tag 0FUR] is the unit of `b^* ⊣ b_*` at
`Ω^a_{X/S}` followed by the direct image of the first canonical map
`Stacks.DeRham.blowupFormsPullbackMap` of [Stacks, Tag 0G5G]. -/
theorem coordinateBlowupFormsDirectImage_eq (a : ℕ) :
    coordinateBlowupFormsDirectImage R m n a =
      (Scheme.Modules.pullbackPushforwardAdjunction (coordinateBlowupToAmbient R m n)).unit.app
          (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) (a : ℤ)) ≫
        (Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)).map
          (blowupFormsPullbackMap R m n a) :=
  rfl

/-- The direct image along `b` of the first canonical map `Stacks.DeRham.blowupFormsPullbackMap`
of [Stacks, Tag 0G5G] is a monomorphism. -/
theorem mono_pushforward_blowupFormsPullbackMap (a : ℕ) :
    Mono ((Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)).map
      (blowupFormsPullbackMap R m n a)) :=
  have : CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
      (Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (coordinateBlowupToAmbient R m n)).rightAdjoint_preservesLimits).preservesLimitsOfShape
  have := mono_blowupFormsPullbackMap R m n a
  inferInstance

end Stacks.DeRham

end
