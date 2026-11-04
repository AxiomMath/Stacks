module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneOverSiteSlotHTZ
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePsiLegOverSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteChiSlot
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHTSlot
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHcompExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHsiteExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceSiteSlotsF1

/-!
# The target square of clause (1) of Tag 0D2Z over the site of `s`

In the namespace `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`:
the target square of clause (1) of Tag 0D2Z at a scheme point `w` of `U(ψ)` over the site of `s`,
that is, the conclusion of `clauseOneTarget_square_overSite_of_slots` with its seven slot
hypotheses discharged.

## Main results

* `targetSquareOverSite_square`: the target square of clause (1) at a scheme point of `U(ψ)`, over
  the site of `s`, with no hypothesis.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- The target square of clause (1) of Tag 0D2Z at a scheme point `w` of `U(ψ)`, over the site
of `s`, with no hypothesis: the conclusion of `clauseOneTarget_square_overSite_of_slots`. -/
theorem targetSquareOverSite_square :
    (fun {α₁ α₂ α₃ α₄ α₅ α₆ α₇ γ : Prop} (_ : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → γ) => γ)
      (clauseOneTarget_square_overSite_of_slots w d) :=
  clauseOneTarget_square_overSite_of_slots w d (targetSquare_hcomp_exact w d)
    (targetSquareSite_hsite_exact w d) (targetSquareOverSite_slot_HTZ w d)
    (clauseOneTarget_square_overSite_of_slots_hτ₁ w d)
    (fibrePsiSourceIso_hom_eq_locusPoint_slot w d) (chartTargetIso_hom_eq_over_site_slot w (d : ℤ))
    (clauseOnePsiLeg_eq_overSite (f := f) (L := L) (ψ := ψ) d)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
