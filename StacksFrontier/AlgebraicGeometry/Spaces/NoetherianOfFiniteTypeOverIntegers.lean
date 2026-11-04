module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverQuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion

/-!
# Algebraic spaces of finite type over `Spec ℤ` are Noetherian

An algebraic space `Y` over a scheme `S` which is of finite type over `Spec ℤ` is quasi-compact
and locally Noetherian; if it is also quasi-separated it is therefore Noetherian. An algebraic
space `X` with a quasi-separated morphism of finite type to a Noetherian algebraic space is
again Noetherian: it is quasi-compact over a quasi-compact space, quasi-separated over a
quasi-separated space (Stacks 04ZH), and locally Noetherian (Stacks 04ZK).

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFiniteType_viewOverIntegers`: an algebraic
  space of finite type over `Spec ℤ` is quasi-compact.
* `AlgebraicGeometry.Space.isNoetherian_of_isFiniteType_of_isQuasiSeparated`: the source of a
  quasi-separated morphism of finite type to a Noetherian algebraic space is Noetherian.

## Implementation notes

That a quasi-separated algebraic space of finite type over `Spec ℤ` is Noetherian is
`AlgebraicGeometry.Space.isNoetherian_of_isFiniteType_viewOverIntegers`.

Being of finite type over `Spec ℤ` is read, as in
`AlgebraicGeometry.Space.NoetherianApproximation`, on the view of the space over the terminal
scheme. Quasi-compactness and local Noetherianity are both unchanged by the view, so they are
proved for the view, whose structure morphism to the terminal presheaf is quasi-compact and
locally of finite type, and transported back.

Quasi-separatedness of the morphism is needed in the last statement: a morphism of finite type
need not be quasi-separated, and a Noetherian algebraic space is quasi-separated by definition.

## References

* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space of finite type over `Spec ℤ` is quasi-compact.** Its view over the
terminal scheme is the source of a quasi-compact morphism to the terminal presheaf, which is a
quasi-compact algebraic space, and quasi-compactness is reflected by the view. -/
theorem isQuasiCompactSpace_of_isFiniteType_viewOverIntegers (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ F))) :
    IsQuasiCompactSpace B S hS F := by
  let T : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
  have : IsIso (terminal.from (yoneda.obj T)) :=
    (((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso
      terminalIsTerminal).isIso_hom
  have hpb := h.2 (yoneda.obj T) (isAlgebraicSpace_yoneda B _ hZ T)
    (isQuasiCompactSpace_yoneda_of_isAffine B _ hZ T
      (IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv))
    (terminal.from _)
  exact isQuasiCompactSpace_of_relocalize B S (⊤_ Scheme.{u}) hS hZ _ F
    (isQuasiCompactSpace_of_iso B _ hZ (asIso (pullback.snd _ _)) hpb)

/-- **The source of a quasi-separated morphism of finite type to a Noetherian algebraic space
is Noetherian.** It is quasi-compact, since the morphism and its target are; quasi-separated by
Stacks 04ZH, part (2); and locally Noetherian by Stacks 04ZK. -/
theorem isNoetherian_of_isFiniteType_of_isQuasiSeparated (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFiniteType B S hS f)
    (hfqs : IsQuasiSeparated B S hS f) (hN : IsNoetherian B S hS hZ Y) :
    IsNoetherian B S hS hZ X :=
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hN.1 hf.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hN.2.1 hfqs,
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX hY f hf.1 hN.2.2⟩

end AlgebraicGeometry.Space

end
