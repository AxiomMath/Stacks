module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Invariance of pointed-chart conditions under isomorphism

A condition of Tag 04RE on a morphism of algebraic spaces at a point of its source is
unchanged when the source and the target of the morphism are replaced by isomorphic
presheaves. In particular Cohen–Macaulayness at a point (Tag 0E0V) is invariant.

## Main definitions

* `AlgebraicGeometry.Space.EtaleChartAtPoint.ofIso`: a pointed étale chart of a morphism,
  transported along isomorphisms of its source and its target.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_of_iso` and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iso_iff`: invariance of an arbitrary
  pointed-chart condition.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_of_iso` and
  `AlgebraicGeometry.Space.isCohenMacaulayAt_iso_iff`: invariance of Cohen–Macaulayness at a
  point.

## References

* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G K K' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A pointed étale chart of a morphism, transported along isomorphisms of its source and its
target: the chart morphisms are composed with the inverses of the isomorphisms, while the
chart objects, the induced morphism of charts and the field-valued representative of the point
are unchanged. -/
def EtaleChartAtPoint.ofIso (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F)
    (c : EtaleChartAtPoint B S hS g (pointsMap B S hS F e.hom x)) :
    EtaleChartAtPoint B S hS f x where
  U := c.U
  V := c.V
  a := c.a ≫ e.inv
  b := c.b ≫ eK.inv
  h := c.h
  a_etale := MorphismProperty.RespectsIso.postcomp _ e.inv c.a c.a_etale
  b_etale := MorphismProperty.RespectsIso.postcomp _ eK.inv c.b c.b_etale
  comm := by
    have hgi : g ≫ eK.inv = e.inv ≫ f := by
      rw [Iso.eq_inv_comp, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [← Category.assoc, c.comm, Category.assoc, hgi, Category.assoc]
  representative := c.representative
  point := c.point
  maps_to := by
    rw [pointsMap_comp_apply, c.maps_to, ← pointsMap_comp_apply, e.hom_inv_id, pointsMap_id,
      id_eq]

/-- A pointed-chart condition of Tag 04RE is carried along isomorphisms of the source and of
the target of the morphism. -/
theorem holdsOnEveryEtaleChartAtPoint_of_iso
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F)
    (h : HoldsOnEveryEtaleChartAtPoint B S hS Q f x) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q g (pointsMap B S hS F e.hom x) :=
  fun c => h (EtaleChartAtPoint.ofIso B S hS e eK f g hcomm x c)

/-- A pointed-chart condition of Tag 04RE is invariant under isomorphisms of the source and of
the target of the morphism. -/
theorem holdsOnEveryEtaleChartAtPoint_iso_iff
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS Q g (pointsMap B S hS F e.hom x) := by
  refine ⟨holdsOnEveryEtaleChartAtPoint_of_iso B S hS Q e eK f g hcomm x, fun h => ?_⟩
  have hcomm' : e.inv ≫ f = g ≫ eK.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h2 := holdsOnEveryEtaleChartAtPoint_of_iso B S hS Q e.symm eK.symm g f hcomm' _ h
  have h3 : pointsMap B S hS G e.symm.hom (pointsMap B S hS F e.hom x) = x := by
    rw [← pointsMap_comp_apply, Iso.symm_hom, e.hom_inv_id, pointsMap_id, id_eq]
  rwa [h3] at h2

/-- **Stacks 0E0V.** Cohen–Macaulayness at a point is carried along isomorphisms of the source
and of the target of the morphism. -/
theorem isCohenMacaulayAt_of_iso (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F)
    (h : IsCohenMacaulayAt B S hS f x) :
    IsCohenMacaulayAt B S hS g (pointsMap B S hS F e.hom x) :=
  ⟨holdsOnEveryEtaleChartAtPoint_of_iso B S hS _ e eK f g hcomm x h.1,
    holdsOnEveryEtaleChartAtPoint_of_iso B S hS _ e eK f g hcomm x h.2⟩

/-- **Stacks 0E0V.** Cohen–Macaulayness at a point is invariant under isomorphisms of the
source and of the target of the morphism. -/
theorem isCohenMacaulayAt_iso_iff (e : F ≅ G) (eK : K ≅ K') (f : F ⟶ K) (g : G ⟶ K')
    (hcomm : e.hom ≫ g = f ≫ eK.hom) (x : points B S hS F) :
    IsCohenMacaulayAt B S hS f x ↔
      IsCohenMacaulayAt B S hS g (pointsMap B S hS F e.hom x) :=
  and_congr (holdsOnEveryEtaleChartAtPoint_iso_iff B S hS _ e eK f g hcomm x)
    (holdsOnEveryEtaleChartAtPoint_iso_iff B S hS _ e eK f g hcomm x)

end AlgebraicGeometry.Space

end
