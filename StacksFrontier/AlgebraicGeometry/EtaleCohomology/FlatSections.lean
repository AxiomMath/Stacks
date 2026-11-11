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
# Flat quasi-compact morphisms with connected fibres are universally submersive

Let `f : T ⟶ S` be a flat quasi-compact morphism of schemes whose geometric fibres are
connected. Then `f` is universally submersive; this is the geometric input to [Stacks, Tag 0A3H],
which is proved in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSectionsCanonical`.

Connectedness of the geometric fibres makes `f` surjective, a surjective flat quasi-compact
morphism of schemes is a quotient map of the underlying topological spaces, and flatness,
quasi-compactness and connectedness of the geometric fibres are all stable under base change; so
every base change of `f` is a quotient map.

## Main results

* `Stacks.EtaleCohomology.universally_isQuotientMap_of_flat_quasiCompact` — a flat quasi-compact
  morphism with geometrically connected fibres is universally submersive.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_quasiCompact` — the
  reduction of the global-sections statement to any supplier of the universally submersive
  case; the unconditional form is in `FlatSectionsCanonical`.

## Implementation notes

Submersivity is `(topologically Topology.IsQuotientMap).universally`, and connectedness of the
geometric fibres is Mathlib's morphism property `GeometricallyConnected`.

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

/-- Pullback along a flat quasi-compact morphism with geometrically connected fibres preserves
global sections of every sheaf of sets on the small étale site, naturally in the sheaf, given any
supplier `hEZK` of the same conclusion for universally submersive morphisms with geometrically
connected fibres. Tag 0EZK is proved in the library, and Tag 0A3H with no such argument is
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_of_quasiCompact`. -/
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
