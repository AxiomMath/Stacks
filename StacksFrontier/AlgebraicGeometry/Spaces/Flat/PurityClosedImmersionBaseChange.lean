module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange

/-!
# Purity of a module supported on a closed subspace, unconditionally

`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityClosedImmersion.lean` proves Stacks 0CVH from
one input on the base changes of the situation,
`AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput`: for a closed immersion
`i : Z ⟶ X` into the source of a pre-pure situation and a morphism `T ⟶ Y` from a scheme of the
site, the restriction of `i_*𝒢` to `X_T` is the direct image along the induced closed immersion
`Z_T ⟶ X_T` of the restriction of `𝒢`.  This is affine base change for algebraic spaces (the
base change clause of Stacks 07U8), proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleAffineBaseChange.lean`, a closed immersion being
affine (Stacks 07U2).  This file discharges the input and states Stacks 0CVH without it.

## Main results

* `AlgebraicGeometry.Space.ClosedSubspaceModule.isPullback_baseChangeImmersion_spaces`: the
  square of base changes is cartesian in the category of algebraic spaces.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.baseChangeInput`: the input holds.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.isPureAbove_iff` and
  `AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_iff`: **Stacks 0CVH**.

## References

* [Stacks Project, Tag 0CVH](https://stacks.math.columbia.edu/tag/0CVH)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ClosedSubspaceModule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P : PrePureSituation.{u, u} B S hS} (c : ClosedSubspaceModule P)
  (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ P.Y)

/-- The square of base changes `Z_T ⟶ X_T` over `i : Z ⟶ X` is cartesian in the category of
algebraic spaces over `S`, fibre products of algebraic spaces being computed in presheaves. -/
theorem isPullback_baseChangeImmersion_spaces :
    IsPullback (c.situation.baseChangeToSource T g) (c.baseChangeImmersion T g) c.i
      (P.baseChangeToSource T g) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (c.baseChangeImmersion_hom_comp_snd T g).symm)
    (c.isPullback_baseChangeImmersion T g).flip

/-- **The input of `AlgebraicGeometry.Space.ClosedSubspaceModule.BaseChangeInput` holds**: the
restriction of `i_*𝒢` to `X_T` is the direct image along `Z_T ⟶ X_T` of the restriction of `𝒢`
to `Z_T`, by affine base change (Stacks 07U8), a closed immersion being affine (Stacks 07U2). -/
theorem baseChangeInput : c.BaseChangeInput where
  directImage T g :=
    nonempty_modulePullbackModulePushforwardIso_of_isAffineHom
      (c.isPullback_baseChangeImmersion_spaces T g)
      (isAffineHom_of_isClosedImmersion B S hS c.i.hom c.isClosedImmersion) c.G
      c.moduleQuasicoherent

/-- **Stacks 0CVH, purity above `y`.** In the situation of Stacks 0CV6, let `i : Z ⟶ X` be a
closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent `𝒪_Z`-module `𝒢`.
Then `𝒢` is pure above `y` if and only if `ℱ` is pure above `y`. -/
@[stacks 0CVH "pure above y"]
theorem isPureAbove_iff : IsPureAbove c.situation ↔ IsPureAbove P :=
  c.isPureAbove_situation_iff c.baseChangeInput

/-- **Stacks 0CVH, universal purity above `y`.** In the situation of Stacks 0CV6, let
`i : Z ⟶ X` be a closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent
`𝒪_Z`-module `𝒢`.  Then `𝒢` is universally pure above `y` if and only if `ℱ` is universally
pure above `y`. -/
@[stacks 0CVH "universally pure above y"]
theorem isUniversallyPureAbove_iff :
    IsUniversallyPureAbove c.situation ↔ IsUniversallyPureAbove P :=
  c.isUniversallyPureAbove_situation_iff c.baseChangeInput

end AlgebraicGeometry.Space.ClosedSubspaceModule

end
