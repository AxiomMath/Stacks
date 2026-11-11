module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquaresProof
import StacksCore.Tactic.StacksAttribute

/-!
# The spectral sequence of a smooth morphism

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
scheme `S`, with `g : Y ⟶ S` the structure morphism of the target. This file states
[Stacks, Tag 0FMM]: there is a bounded spectral sequence with first page

`E_1^{p,q} = H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`

converging to `R^{p+q}f_*Ω^•_{X/S}`.

## Main results

* `Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence_of_smooth`: the bounded spectral
  sequence with first page `H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})` converging to
  `R^{p+q}f_*Ω^•_{X/S}`.

## Implementation notes

The proof follows Stacks: the spectral sequence is that of the filtered complex `Ω^•_{X/S}` with
the filtration of Section 0FMK (`Stacks.DeRhamSmooth.deRhamSmoothFiltration`), via
`Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence`. The vanishing of the higher direct
images of its far steps is
`Stacks.DeRhamSmooth.exists_higherDirectImage_deRhamSmoothFiltration_isZero`, and the
identification of the higher direct images of its graded pieces with the first page (the graded
pieces of Section 0FMK and the projection formula of [Stacks, Tag 0FML]) is
`Stacks.DeRhamSmooth.higherDirectImageGradedPieceIsoFirstPage` at
`Stacks.DeRhamSmooth.stepSquares`. Nothing is assumed beyond the hypotheses of the statement.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
scheme `S`, with `g : Y ⟶ S` the structure morphism of the target. There is a bounded cohomological
spectral sequence of sheaves of `g^{-1}𝒪_S`-modules on `Y`, starting at its first page, with

`E_1^{p,q} = H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`,

which abuts to `R^{p+q}f_*Ω^•_{X/S}`. -/
@[stacks 0FMM "the bounded spectral sequence of a quasi-compact, quasi-separated, smooth \
morphism, with first page H^q(Ω^p_{Y/S} ⊗ᴸ Rf_*Ω^•_{X/Y}) and abutment R^{p+q}f_*Ω^•_{X/S}"]
theorem exists_boundedDeRhamSpectralSequence_of_smooth
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u} (structureSheafRing (Stacks.DeRhamDirectImage.inverseImageBase g))) 1,
      _root_.IsBounded E ∧
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ deRhamFirstPage f g p q)) ∧
      SpectralSequence.AbutsTo E (fun n => deRhamHigherDirectImage f g n) :=
  exists_boundedDeRhamSpectralSequence_of_stepSquares f g (stepSquares f g)

end Stacks.DeRhamSmooth

end
