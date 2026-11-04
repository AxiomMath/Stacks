module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition

/-!
# Rig-smoothness is stable under composition

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCS** says that if
`f` and `g` are rig-smooth (Stacks 0GCP), then so is `g ∘ f`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.TransfersCompositionOnAffineEtaleDiagrams`: the transfer to
  formal algebraic spaces drawn in **Stacks 0GBK**.

## Implementation notes

The proof of Stacks 0GCS is the composite of two facts. At the level of topological rings,
rig-smoothness is stable under composition in the sense of Remark 0GBK; this is Stacks 0GCM,
carried by the library as `Rig.rigSmooth_isStableUnderCompositionNoetherian`, whose bundle keeps
the locality of rig-smoothness (Stacks 0GCK) as an input. Remark 0GBK then draws from such a
stability bundle the geometric transfer: condition (1) of Stacks 0ANG passes from `f` and `g` to
their composite. That transfer is not in the library — producing it means manufacturing, from a
chart of `X` and a chart of `Z`, a chart of the intermediate space `Y` through which the chart
morphism factors, and descending the property along the resulting coverings — so it is carried
here as the hypothesis `TransfersCompositionOnAffineEtaleDiagrams`, quantified over *all*
properties admitting a stability bundle; it is therefore a statement about the generic machinery
of Remark 0GBK and not a restatement of Stacks 0GCS itself. This is the same arrangement as
for the base-change variant Stacks 0GCR in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange`.

## References

* [Stacks Project, Tag 0GCS](https://stacks.math.columbia.edu/tag/0GCS)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GCM](https://stacks.math.columbia.edu/tag/0GCM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The transfer to formal algebraic spaces drawn in **Stacks 0GBK**: whenever a local property
`P` of arrows of `WAdm^{Noeth}` is stable under composition, condition (1) of Stacks 0ANG passes
from two composable morphisms with `P` to their composite. -/
abbrev TransfersCompositionOnAffineEtaleDiagrams (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop :=
  ∀ (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop),
    TopologicalRing.PropertyIsStableUnderCompositionNoetherian.{u} P →
    ∀ {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      HasPropertyOnEveryAffineEtaleDiagram B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P f →
        HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P g →
          HasPropertyOnEveryAffineEtaleDiagram B S hS
            (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R) P (f ≫ g)

end AlgebraicGeometry.FormalSpace

end
