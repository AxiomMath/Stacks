module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Invariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Defs

/-!
# Invariance of Gorensteinness under isomorphism

Gorensteinness of a morphism of algebraic spaces at a point of its source (Tag 0E14) is unchanged
when the source and the target of the morphism are replaced by isomorphic presheaves. Both of its
conjuncts — flatness at the point and the fibre local ring condition of Tag 0E13 — are
pointed-chart conditions of Tag 04RE, and those are invariant under such replacements.

## Main results

* `AlgebraicGeometry.Space.isGorensteinAt_iso_iff`: invariance of Gorensteinness at a point.
* `AlgebraicGeometry.Space.isGorenstein_iso_iff`: invariance of Gorensteinness of the morphism.

## Implementation notes

This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iso_iff` applied to both
conjuncts, exactly as `AlgebraicGeometry.Space.isCohenMacaulayAt_iso_iff` in the Cohen–Macaulay
case.

## References

* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G K K' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Gorensteinness at a point is invariant under isomorphisms of the source and of the target of
the morphism: both of its conjuncts are pointed-chart conditions. -/
theorem isGorensteinAt_iso_iff (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F) :
    IsGorensteinAt B S hS f x ↔ IsGorensteinAt B S hS g (pointsMap B S hS F e.hom x) :=
  and_congr (holdsOnEveryEtaleChartAtPoint_iso_iff B S hS _ e eK f g hcomm x)
    (holdsOnEveryEtaleChartAtPoint_iso_iff B S hS _ e eK f g hcomm x)

/-- Gorensteinness of a morphism of presheaves is invariant under isomorphisms of its source and
of its target: every point of the new source is the image of a point of the old one. -/
theorem isGorenstein_iso_iff (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) :
    IsGorenstein B S hS f ↔ IsGorenstein B S hS g := by
  refine ⟨fun hf y => ?_, fun hg x => (isGorensteinAt_iso_iff B S hS e eK f g hcomm x).mpr (hg _)⟩
  have hy : pointsMap B S hS F e.hom (pointsMap B S hS G e.inv y) = y := by
    rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  rw [← hy]
  exact (isGorensteinAt_iso_iff B S hS e eK f g hcomm _).mp (hf _)

end AlgebraicGeometry.Space

end
