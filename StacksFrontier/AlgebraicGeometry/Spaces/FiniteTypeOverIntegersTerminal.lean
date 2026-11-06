module

public import StacksFrontier.AlgebraicGeometry.Spaces.ViewOverIntegersTerminal
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LocallyNoetherianExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation

/-!
# Consequences of finite type over `Spec ℤ` for a space already over `Spec ℤ`

Let `F` be a presheaf on the big fppf site of `Spec ℤ`. Its view over `Spec ℤ` is relocalization
along the structure morphism of the terminal scheme, which is the identity, so the view is
isomorphic to `F` itself. This file records that isomorphism and the facts it transports: an
algebraic space over `Spec ℤ` whose view over `Spec ℤ` is quasi-compact, or locally of finite type,
over `Spec ℤ` is quasi-compact, respectively locally of finite presentation over `Spec ℤ`.

## Main definitions

* `AlgebraicGeometry.Space.viewOverIntegersIsoOfTerminal`: the view over `Spec ℤ` of a presheaf
  over `Spec ℤ` is that presheaf.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `isQuasiCompactSpace_terminal_of_isAffine`: the terminal presheaf over an affine base is
  quasi-compact.
* `isQuasiCompactSpace_of_isQuasiCompact_viewOverIntegers`: a presheaf over `Spec ℤ` whose view
  over `Spec ℤ` is quasi-compact over `Spec ℤ` is quasi-compact.
* `isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers`: an algebraic
  space over `Spec ℤ` whose view over `Spec ℤ` is locally of finite type is locally of finite
  presentation over `Spec ℤ`, the base being Noetherian (Stacks 06G4).

## References

* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})

/-- **The terminal presheaf over an affine base is quasi-compact.** It is represented by the
identity of the base, a terminal object of the site whose underlying scheme is the base. -/
theorem isQuasiCompactSpace_terminal_of_isAffine (S : Scheme.{u}) (hS : B.Contains S)
    [IsAffine S] : IsQuasiCompactSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  isQuasiCompactSpace_of_iso B S hS
    (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
      terminalIsTerminal)
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS (Over.mk (𝟙 (B.obj hS))) ‹IsAffine S›)

variable (hZ : B.Contains (⊤_ Scheme.{u}))

variable {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- **A presheaf over `Spec ℤ` whose view over `Spec ℤ` is quasi-compact over `Spec ℤ` is
quasi-compact.** The base change of the structure morphism of the view along the identity of the
terminal presheaf, which is quasi-compact, is the view, and the view is the presheaf itself. -/
theorem isQuasiCompactSpace_of_isQuasiCompact_viewOverIntegers
    (h : IsQuasiCompact B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F :=
  isQuasiCompactSpace_of_iso B _ hZ (viewOverIntegersIsoOfTerminal B hZ F)
    (isQuasiCompactSpace_of_iso B _ hZ (asIso (pullback.snd (𝟙 _) _))
      (h _ (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
        (isQuasiCompactSpace_terminal_of_isAffine B _ hZ) (𝟙 _)))

/-- The structure morphism of an algebraic space of finite type over `Spec ℤ` is quasi-compact:
over the terminal base the view over `Spec ℤ` is the space itself. -/
theorem isQuasiCompact_terminal_of_isFiniteTypeOverIntegers
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsQuasiCompact B (⊤_ Scheme.{u}) hZ (terminal.from F) := by
  rw [show terminal.from F = (viewOverIntegersIsoOfTerminal B hZ F).inv ≫ terminal.from _ from
    terminal.hom_ext _ _]
  exact isQuasiCompact_isIso_comp B (⊤_ Scheme.{u}) hZ _ h.2

/-- **An algebraic space over `Spec ℤ` whose view over `Spec ℤ` is locally of finite type is
locally of finite presentation over `Spec ℤ`.** The view is the space itself, and over the
Noetherian base `Spec ℤ` an algebraic space locally of finite type is limit preserving, hence
locally of finite presentation (Stacks 06G4). -/
theorem isLocallyOfFinitePresentation_terminal_of_isLocallyOfFiniteType_viewOverIntegers
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (h : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from F) := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian
    (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  exact (isLocallyOfFinitePresentation_terminal_iff_limitPreserving B _ hZ hF).2
    (limitPreserving_of_isLocallyOfFiniteType B _ hZ hF
      ((isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ
        (viewOverIntegersIsoOfTerminal B hZ F)).mp h))

end AlgebraicGeometry.Space

end
