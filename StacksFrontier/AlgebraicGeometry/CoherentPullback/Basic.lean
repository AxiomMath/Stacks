module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of a coherent module to a locally Noetherian scheme

The pullback of a coherent module along an arbitrary morphism of schemes is coherent as soon as
the source is locally Noetherian. No flatness and no hypothesis on the target are needed.

## Main results

* `AlgebraicGeometry.isCoherent_pullback`: the pullback of a coherent module along a morphism
  of schemes whose source is locally Noetherian is coherent.

## Implementation notes

Coherence is not preserved by pullback in general; what is preserved unconditionally is finite
presentation, by [Stacks, Tag 01BQ]. On a locally Noetherian scheme finite presentation is
equivalent to coherence, which is implication (3) ⇒ (1) of [Stacks, Tag 01XZ]. The proof is the
composite of those two facts, so the Noetherian hypothesis is used only on the source.

The finite-presentation input is stated for a morphism of ringed spaces and the pullback functor
`RingedSpaceModuleAdjunction.modulePullback`; it is applied here to `Scheme.Modules.pullback`,
which unfolds to the same functor.

## References

* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EBF.** The pullback of a coherent module along a morphism of schemes
with locally Noetherian source is coherent. -/
@[stacks 0EBF "coherence of the pullback"]
public theorem isCoherent_pullback
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) (G : Y.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pullback f).obj G).IsCoherent := by
  have hGfp : G.IsFinitePresentation := isFinitePresentation_of_isCoherent G
  have hfp : ((Scheme.Modules.pullback f).obj G).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom G hGfp
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation _ hfp

end AlgebraicGeometry

end
