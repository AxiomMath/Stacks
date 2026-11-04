module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingDefinesRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion

/-!
# Closed points of a chain of point blowups of a two-dimensional regular local base

Let `A` be a regular local ring of dimension two, `S` an affine scheme with `Γ(S, ⊤) = A`, and
`W ⟶ S` a finite sequence of blowups in closed points. Then *every* closed point of `W` has a
two-dimensional local ring.

The statement is false for an arbitrary integral regular surface: on `Spec V[y]` with `V` a
discrete valuation ring with uniformizer `x`, the maximal ideal `(xy - 1)` has height one. What
makes it true here is that the base is the spectrum of a *local* ring and the chain is proper over
it, so a closed point of `W` cannot escape to the boundary.

The argument is therefore only a matter of exhibiting the chain as a modification of `Spec A` and
quoting `AlgebraicGeometry.ringKrullDim_stalk_eq_two_of_isModification`, which is the hard half: a
chain of blowups in closed points of an integral regular surface is proper with integral source
(`isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional`) and birational
(`isBirational_of_pointBlowupChain_of_isIntegralRegularSurface`), both in the namespace
`Stacks.ResolutionOfSurfaces`, and composing with the isomorphism `S ≅ Spec Γ(S, ⊤)` preserves all
three properties. A regular local ring is a Noetherian local normal domain, which supplies the
ring-theoretic hypotheses.

## Main results

* `Stacks.BlowupTwistUnit.ringKrullDim_stalk_eq_two_of_pointBlowupChain`: the local ring at a
  closed point of a chain of blowups in closed points over the spectrum of a two-dimensional
  regular local ring has dimension two.

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.BlowupTwistUnit

/-- **Every closed point of a chain of blowups in closed points over a two-dimensional regular
local base has a two-dimensional local ring.** Here `S` is affine with `Γ(S, ⊤)` a regular local
ring of dimension two and `h : W ⟶ S` is a `Stacks.ResolutionOfSurfaces.PointBlowupChain`.

The chain is proper with integral source and birational, so `h` composed with `S.isoSpec` is a
modification of `Spec Γ(S, ⊤)`, and the conclusion is
`AlgebraicGeometry.ringKrullDim_stalk_eq_two_of_isModification`. -/
theorem ringKrullDim_stalk_eq_two_of_pointBlowupChain
    {S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
    [IsRegularLocalRing Γ(S, ⊤)] (hdimA : ringKrullDim Γ(S, ⊤) = 2)
    (hS : Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface S) {T : Set S}
    {W : Scheme.{u}} {h : W ⟶ S} (hc : Stacks.ResolutionOfSurfaces.PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) :
    ringKrullDim (W.presheaf.stalk w) = 2 := by
  have := hS.isIntegral
  have : IsNormalDomain ↑Γ(S, (⊤ : S.Opens)) := isNormalDomain_of_isRegularLocalRing _
  obtain ⟨hWsurface, hWproper⟩ :=
    ResolutionOfSurfaces.isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional
      hc hS
  have := hWsurface.isIntegral
  have hbir : IsBirational h :=
    Stacks.ResolutionOfSurfaces.isBirational_of_pointBlowupChain_of_isIntegralRegularSurface hc hS
  have hbirIso : IsBirational S.isoSpec.hom := isBirational_of_isIso_stalkMap_genericPoint _
  have hproper : IsProper (h ≫ S.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ hWproper inferInstance
  have hmod : IsModification (h ≫ S.isoSpec.hom) :=
    ⟨hbir.comp hbirIso, hproper, inferInstance⟩
  exact ringKrullDim_stalk_eq_two_of_isModification ↑Γ(S, (⊤ : S.Opens)) hdimA
    (h ≫ S.isoSpec.hom) hmod w hw

end Stacks.BlowupTwistUnit

end
