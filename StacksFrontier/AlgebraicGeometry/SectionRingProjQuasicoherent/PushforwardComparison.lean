module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Comparison
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Isomorphism

/-!
# The comparison `M̃ ⟶ f_* ℱ` on `Proj` of the section ring

In Situation 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module, `S = Γ_*(X, L)` and
`f : X ⟶ Proj S` the canonical morphism of Stacks Tag 01PZ — let `M = Γ_*(X, L, ℱ)`. Stacks Tag
01QJ is `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison_spec`, about the comparison
`Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison : f^* M̃ ⟶ ℱ`. This file constructs
the family `M̃ ⟶ f_* ℱ` on `Proj S` it is the transpose of, and identifies the transpose
`Stacks.SectionRingProjQuasicoherent.pullbackComparison` of that family with
`pullbackTildeComparison`.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.tildeToPushforward`: `M̃ ⟶ f_* ℱ`, natural in `ℱ`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.restrictComparison_tildeToPushforward`: its transpose
  across the restriction adjunction is `gluedComparisonNatTrans`.
* `Stacks.SectionRingProjQuasicoherent.pullbackComparison_tildeToPushforward`: its transpose
  across `f^* ⊣ f_*` is `pullbackTildeComparison`.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.SectionRingProjQuasicoherent

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

/-- **The comparison `M̃ ⟶ f_* ℱ` on `Proj Γ_*(X, L)`**, natural in `ℱ`, for `M = Γ_*(X, L, ℱ)`:
the transpose of `gluedComparisonNatTrans` across the adjunction between restriction along the
open immersion `f` (Stacks Tag 01Q1) and `f_*`. -/
def tildeToPushforward : tildeFunctor L ⟶ Scheme.Modules.pushforward (projHomOfIsAmple L hL) :=
  haveI := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  Functor.whiskerLeft (tildeFunctor L)
      (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).unit ≫
    Functor.whiskerRight (gluedComparisonNatTrans L hL)
      (Scheme.Modules.pushforward (projHomOfIsAmple L hL))

/-- Transposing `tildeToPushforward` back across the restriction adjunction recovers
`gluedComparisonNatTrans`. -/
theorem restrictComparison_tildeToPushforward [IsOpenImmersion (projHomOfIsAmple L hL)] :
    restrictComparison L hL (tildeToPushforward L hL) = gluedComparisonNatTrans L hL := by
  refine NatTrans.ext (funext fun A => ?_)
  dsimp only [restrictComparison, tildeToPushforward, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have h := ((Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).homEquiv _
    _).symm_apply_apply ((gluedComparisonNatTrans L hL).app A)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  exact h

/-- **`pullbackTildeComparison` is `pullbackComparison` at the constructed family**
`tildeToPushforward : M̃ ⟶ f_* ℱ`. -/
theorem pullbackComparison_tildeToPushforward :
    pullbackComparison L hL (tildeToPushforward L hL) = pullbackTildeComparison L hL :=
  haveI := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  congrArg (fun θ => (Functor.isoWhiskerLeft (tildeFunctor L)
      (Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL))).inv ≫ θ)
    (restrictComparison_tildeToPushforward L hL)

end Stacks.SectionRingProjQuasicoherent

end
