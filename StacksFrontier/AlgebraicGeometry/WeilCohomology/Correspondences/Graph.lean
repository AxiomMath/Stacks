module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute

/-!
# The graph of a morphism of schemes

Let `pX : X ⟶ S` and `pY : Y ⟶ S` be schemes over a base and let `f : Y ⟶ X` be a morphism
over `S`. Pairing `f` with the identity of `Y` gives a morphism `Y ⟶ X ×_S Y`, and the graph
`Γ_f` of `f` is the scheme-theoretic image of that morphism. When `X` is separated over `S` the
pairing morphism is already a closed immersion, so the graph is the closed subscheme of
`X ×_S Y` it cuts out.

The source introduces the graph for smooth projective schemes over a field; the construction
here needs no hypothesis on `X`, `Y` or `S`. The factors are ordered with the target first, as
`X ×_S Y`, matching the source's `Γ_f ⊆ X × Y` for `f : Y → X`.

## Main definitions

* `Stacks.WeilCohomology.graphMorphism`: the morphism `(f, 𝟙 Y) : Y ⟶ X ×_S Y`.
* `Stacks.WeilCohomology.graph`: the graph `Γ_f ⊆ X ×_S Y`, the scheme-theoretic image of
  `graphMorphism`.

## Main results

* `Stacks.WeilCohomology.graphMorphism_fst` and `Stacks.WeilCohomology.graphMorphism_snd`
  identify the two projections of the graph morphism, which characterise it.
* `Stacks.WeilCohomology.isClosedImmersion_graphMorphism`: the graph morphism is a closed
  immersion as soon as `X` is separated over `S`.

## References

* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
-/

open AlgebraicGeometry

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.WeilCohomology

variable {S X Y : Scheme.{u}}

/-- The graph morphism `(f, 𝟙 Y) : Y ⟶ X ×_S Y` of a morphism `f : Y ⟶ X` over `S`, with the
target of `f` as the first factor of the fibre product. -/
abbrev graphMorphism (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ pX = pY) :
    Y ⟶ pullback pX pY :=
  pullback.lift f (𝟙 Y) (by simpa using hf)

/-- The first projection of the graph morphism of `f` is `f`. -/
@[simp]
theorem graphMorphism_fst (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ pX = pY) :
    graphMorphism pX pY f hf ≫ pullback.fst pX pY = f :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph morphism of `f` is the identity. -/
@[simp]
theorem graphMorphism_snd (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ pX = pY) :
    graphMorphism pX pY f hf ≫ pullback.snd pX pY = 𝟙 Y :=
  pullback.lift_snd _ _ _

/-- **Stacks Project, Tag 0FG1.** The graph `Γ_f ⊆ X ×_S Y` of a morphism `f : Y ⟶ X` over `S`:
the scheme-theoretic image of `(f, 𝟙 Y) : Y ⟶ X ×_S Y`. -/
@[stacks 0FG1 "graph_of_morphism"]
abbrev graph (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ pX = pY) : Scheme.{u} :=
  (graphMorphism pX pY f hf).image

/-- **Stacks Project, Tag 0FG1.** The graph morphism of an `S`-morphism `f : Y ⟶ X` is a closed
immersion whenever `X` is separated over `S`. -/
@[stacks 0FG1 "graph_closed_immersion",
  ega "I 5.4.3",
  ega "I 10.15.4" "ordinary schemes",
  ega "I 5.3.11" "separated case", ega "I 5.4.2" "special case"]
theorem isClosedImmersion_graphMorphism (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ pX = pY) [IsSeparated pX] :
    IsClosedImmersion (graphMorphism pX pY f hf) :=
  have : IsClosedImmersion (graphMorphism pX pY f hf ≫ pullback.snd pX pY) := by
    simpa using (inferInstance : IsClosedImmersion (𝟙 Y))
  IsClosedImmersion.of_comp _ (pullback.snd pX pY)

end Stacks.WeilCohomology

end
