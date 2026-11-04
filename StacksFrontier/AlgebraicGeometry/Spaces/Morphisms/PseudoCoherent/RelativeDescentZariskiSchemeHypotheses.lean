module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPerfectPseudoCoherentTransport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing

/-!
# The pseudo-coherence hypothesis of Stacks 0DI7 on an affine model, from that of Stacks 0DKV

`AlgebraicGeometry.Space.RelativeDescentSituation.zariskiModelHomDescent_of_affineChart` asks
for the hypotheses of Stacks 0DI7 on the Zariski site of the scheme underlying an affine object
`U` of the site, while Stacks 0DKV supplies them on the small étale site of the represented
algebraic space `h_U`, for `ε^*K`.  This file translates the pseudo-coherence hypothesis: Stacks
08HE read on `h_U` in each degree
(`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_representedDerivedAssociatedModule`), assembled
into unbounded pseudo-coherence on the ringed space by Stacks 08CC
(`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`).

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_of_representedDerivedAssociatedModule`: if `ε^*E₀`
  is pseudo-coherent on the small étale site of `h_U`, then `E₀` is pseudo-coherent on the scheme
  underlying `U`.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **Pseudo-coherence descends along `ε^*`, unbounded** (Stacks 08HE, read on the represented
algebraic space): if `ε^*E₀` is pseudo-coherent on the small étale site of `h_U`, then `E₀` is
pseudo-coherent on the scheme underlying `U`. -/
theorem isPseudoCoherent_of_representedDerivedAssociatedModule
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherent
        ((representedDerivedAssociatedModule B S hS U).obj E₀)) :
    RingedSpace.IsPseudoCoherent (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ := by
  obtain ⟨P, hP, e⟩ := h
  exact (RingedSpace.isPseudoCoherent_iff_forall E₀).2 fun m =>
    isPseudoCoherentFrom_of_representedDerivedAssociatedModule B S hS U E₀ m ⟨P, hP m, e⟩

end AlgebraicGeometry.Space

end
