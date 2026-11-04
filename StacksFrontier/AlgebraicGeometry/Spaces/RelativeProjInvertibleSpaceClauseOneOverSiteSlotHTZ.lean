module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSiteHTZ

/-!
# The slot `hTZ` of the target square of clause (1) of Stacks 0D2Z over the site of `s`

The target square of clause (1) of [Stacks, Tag 0D2Z] over the site of `s`
(`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`) takes seven slot
hypotheses.  This file states its hypothesis `hTZ` with exactly the type of that binder (read
off the lemma) and proves it by the square of `ψ_d` at the scheme point `x`
(`…targetSquareSite_hTZ`), so that the instance takes it with no conversion.

## Main results

* `…InvertibleTwistingRestriction.targetSquareOverSite_slot_HTZ`: the hypothesis `hTZ`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
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

/-- **The hypothesis `hTZ` of the target square of clause (1) over the site of `s`**, with
exactly the type of the binder `hTZ` of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`: the square of `ψ_d` at
the scheme point `x` (`…targetSquareSite_hTZ`). -/
theorem targetSquareOverSite_slot_HTZ :
    (fun {α₁ α₂ α₃ α₄ α₅ α₆ α₇ γ : Prop} (_ : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → γ) => α₃)
      (clauseOneTarget_square_overSite_of_slots w d) :=
  targetSquareSite_hTZ w d

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
