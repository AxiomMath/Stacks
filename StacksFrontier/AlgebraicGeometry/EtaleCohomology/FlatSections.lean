module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Maps.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections under a flat quasi-compact morphism with connected fibres

Let `f : T ⟶ S` be a flat quasi-compact morphism of schemes whose geometric fibres are
connected. Then pulling back a sheaf of sets on the small étale site of `S` to the small étale
site of `T` does not change its global sections: `Γ(S, F) = Γ(T, f^{-1} F)`.

The geometric input is that such an `f` is universally submersive. Connectedness of the geometric
fibres makes `f` surjective, a surjective flat quasi-compact morphism of schemes is a quotient
map of the underlying topological spaces, and flatness, quasi-compactness and connectedness of
the geometric fibres are all stable under base change; so every base change of `f` is a quotient
map. The statement about global sections for a universally submersive morphism with connected
geometric fibres is a separate result, and is carried here as a declared hypothesis.

## Main results

* `Stacks.EtaleCohomology.universally_isQuotientMap_of_flat_quasiCompact` — a flat quasi-compact
  morphism with geometrically connected fibres is universally submersive.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_quasiCompact` — global
  sections downstairs agree, naturally in the sheaf, with global sections of the inverse image
  upstairs.

## Implementation notes

Submersivity is `(topologically Topology.IsQuotientMap).universally`, and connectedness of the
geometric fibres is Mathlib's morphism property `GeometricallyConnected`. The equality of section
sets of the source is expressed as a natural isomorphism of global-sections functors, which
records both that the comparison is the canonical one and that it is natural in the sheaf.

## References

* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- A flat quasi-compact morphism with geometrically connected fibres is universally submersive:
each of the three hypotheses is stable under base change, a flat quasi-compact surjection of
schemes is a quotient map of topological spaces, and connectedness of the geometric fibres
supplies the surjectivity. -/
@[ega "IV 15.7.8" "special case"]
public lemma universally_isQuotientMap_of_flat_quasiCompact
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f] :
    (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally f := by
  intro T' S' i₁ i₂ f' hpb
  have hflat : Flat f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance
  have hqc : QuasiCompact f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance
  have hconn : GeometricallyConnected f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip inferInstance
  exact AlgebraicGeometry.Flat.isQuotientMap_of_surjective f'

/-- **Stacks Project, Tag 0A3H.** Pullback along a flat quasi-compact morphism with
geometrically connected fibres preserves global sections of every sheaf of sets on the small
étale site, naturally in the sheaf. -/
@[stacks 0A3H "Tag 0EZK -- the same conclusion for a universally submersive morphism with
geometrically connected fibres -- is a separate cited tag and is carried as the declared
hypothesis `hEZK`, following the 08W5 convention. The content supplied here is that a flat
quasi-compact morphism with geometrically connected fibres is universally submersive, proved
unconditionally as `universally_isQuotientMap_of_flat_quasiCompact`."]
public def globalSectionsSmallEtaleInverseImageIso_of_flat_quasiCompact
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f] [GeometricallyConnected f]
    (hEZK : ∀ {X S' : Scheme.{u}} (g : X ⟶ S'), GeometricallyConnected g →
      (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally g →
      (Sheaf.Γ (smallEtaleTopology S') (Type (max (u + 1) v)) ≅
        smallEtaleInverseImage.{u, v} g ⋙
          Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v)))) :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v} f ⋙
        Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v)) :=
  hEZK f inferInstance (universally_isQuotientMap_of_flat_quasiCompact f)

end Stacks.EtaleCohomology

end
