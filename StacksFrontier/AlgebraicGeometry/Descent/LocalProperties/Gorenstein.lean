module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein

/-!
# Being Gorenstein is local in the syntomic topology

A scheme is Gorenstein if and only if the members of a jointly surjective family of syntomic
morphisms onto it are Gorenstein.

## Main results

* `AlgebraicGeometry.isGorenstein_isLocal_syntomic` states syntomic locality of the Gorenstein
  property of schemes.

## Implementation notes

Being Gorenstein is local Noetherianity together with Gorensteinness of every local ring, and
the two conjuncts are treated separately. Local Noetherianity is local for fppf coverings, and
a syntomic covering family is an fppf covering family, so it is local for syntomic coverings.

For the local rings, a member of a syntomic covering family is a local complete intersection
morphism, so Gorensteinness passes from the base to the member; this is the ascent. In the other
direction a syntomic covering family is jointly surjective, so every point of the base is the
image of a point of some member, and the induced map of local rings is a flat local homomorphism
of Noetherian local rings with Gorenstein target. Gorensteinness of its source is one of the two
conjuncts the flat local criterion extracts from Gorensteinness of its target.

## References

* [Stacks Project, Tag 0C01](https://stacks.math.columbia.edu/tag/0C01)
* [Stacks Project, Tag 034C](https://stacks.math.columbia.edu/tag/034C)
* [Stacks Project, Tag 0BVA](https://stacks.math.columbia.edu/tag/0BVA)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Being locally Noetherian is local for syntomic coverings, every syntomic covering family
being an fppf covering family. -/
private instance isLocallyNoetherian_isLocal_syntomic :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (Scheme.precoverage @Syntomic) :=
  ObjectProperty.IsLocal.of_le Scheme.syntomicPrecoverage_le_fppfPrecoverage

/-- For a flat morphism of schemes with Gorenstein source and locally Noetherian target, the
local ring of the target at the image of a point of the source is Gorenstein. -/
private theorem isGorensteinLocalRing_stalk_of_flat {Y X : Scheme.{u}} (g : Y ⟶ X) [Flat g]
    [IsLocallyNoetherian X] (hY : IsGorenstein Y) (y : Y) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk (g.base y)) := by
  have _ : IsLocallyNoetherian Y := hY.toIsLocallyNoetherian
  have _ := Flat.stalkMap g y
  algebraize [(g.stalkMap y).hom]
  have _ : IsLocalHom
      (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) := g.toLRSHom.prop y
  exact ((Dualizing.isGorensteinLocalRing_iff_of_flat
    (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)).mp (hY.isGorensteinLocalRing y)).1

/-- **Stacks Project, Tag 0C01.** Being Gorenstein is local for syntomic coverings. -/
@[stacks 0C01]
instance isGorenstein_isLocal_syntomic :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsGorenstein X)
      (Scheme.precoverage @Syntomic) where
  of_iso {X _Y} e hX := by
    let _ : IsGorenstein X := hX
    exact isGorenstein_of_isOpenImmersion e.inv
  component {_X _R} hR {_Y} f hf hX :=
    isGorenstein_of_isLocalCompleteIntersectionMorphism f
      (isLocalCompleteIntersectionMorphism_of_syntomic (hR.2 hf)) hX
  of_presieve {X R} hR h := by
    have hNX : IsLocallyNoetherian X :=
      ObjectProperty.IsLocal.of_presieve (P := fun T : Scheme.{u} => IsLocallyNoetherian T)
        (K := Scheme.precoverage @Syntomic) hR fun {_} {_} hf => (h hf).toIsLocallyNoetherian
    refine { toIsLocallyNoetherian := hNX, isGorensteinLocalRing := fun x => ?_ }
    obtain ⟨Y, g, hg, y, rfl⟩ := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff
      (F := Scheme.forget.{u})).mp hR.1 x
    have _ : Flat g := AlgebraicGeometry.flat (hR.2 hg)
    exact isGorensteinLocalRing_stalk_of_flat g (h hg) y

end AlgebraicGeometry

end
