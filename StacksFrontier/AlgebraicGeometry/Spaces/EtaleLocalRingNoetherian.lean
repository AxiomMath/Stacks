module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# The étale local ring of an algebraic space at a geometric point

The étale local ring of an algebraic space at a geometric point — the stalk of its
small-étale structure sheaf (Stacks 04KG) — is a local ring, and it is Noetherian as soon as
the algebraic space is.

## Main results

* `AlgebraicGeometry.Space.exists_pointed_smallEtaleNeighborhood`: a surjective étale scheme
  atlas is the chart of a small étale neighbourhood of any prescribed geometric point.
* `AlgebraicGeometry.Space.isLocalRing_etaleLocalRing`: the étale local ring is a local ring.
* `AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing`: the étale local ring of a
  Noetherian algebraic space is Noetherian.

## Implementation notes

Both statements are read off a scheme chart. By Stacks 04KF the étale local ring at a
geometric point is the strict henselization of the ordinary local ring of any small étale
neighbourhood of that point at the induced point, which is
`AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`; a strict henselization is a
local ring by construction, and it is Noetherian exactly when the ring it henselizes is.

That comparison needs a small étale neighbourhood whose chart is a scheme the ambient big
fppf site contains, and a big étale site containing that scheme. The first is
`exists_pointed_smallEtaleNeighborhood`: a surjective étale atlas is surjective on points
(Stacks 03H5), so the geometric point lifts to it without extending its field (Stacks 05VN),
and the lift is exactly the datum of a small étale neighbourhood. The second is
`AlgebraicGeometry.bigEtaleSiteOfFppfSite`, whose size cutoff is that of the fppf site, so it
contains every chart.

For the Noetherian statement the atlas is taken from the definition of a Noetherian algebraic
space (Stacks 03EA), which supplies a locally Noetherian one; its local rings are then
Noetherian rings.

## References

* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

namespace AlgebraicGeometry.Space

/-- Transport of the value of a field-valued point along the equality of site objects induced
by an equality of its images. -/
private theorem fieldValuedPoint_map_value_eq {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS G)
    (hsite : Opposite.op p.siteObject = Opposite.op q.siteObject)
    (h : FieldValuedPoint.map B S hS F f p = q) :
    hsite ▸ f.app (Opposite.op p.siteObject) p.value = q.value := by
  have hv : HEq (f.app (Opposite.op p.siteObject) p.value) q.value := by
    cases h
    rfl
  exact eq_of_heq ((eqRec_heq hsite _).trans hv)

/-- The action of a presheaf on an `eqToHom` is transport along the underlying equality. -/
private theorem map_eqToHom_eq_cast {C : Type v} [Category.{w} C] {F : Cᵒᵖ ⥤ Type u}
    {X Y : Cᵒᵖ} (h : X = Y) (a : F.obj X) : F.map (eqToHom h) a = h ▸ a := by
  rw [eqToHom_map]
  cases h
  rfl

/-- A surjective étale scheme atlas of an algebraic space is the chart of a small étale
neighbourhood of any prescribed geometric point: the geometric point lifts to the atlas
without extending its field. -/
theorem exists_pointed_smallEtaleNeighborhood (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (hSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f)
    (hEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) :
    Nonempty { V : SmallEtaleNeighborhood x // V.chart.obj.left = U } := by
  obtain ⟨p, hp⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U f).mp hSurj x.image
  obtain ⟨xU, -, hxU⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) hF f
    ((isEtale_iff_presheaf_of_yoneda B S hS f).mpr hEtale) x p hp
  have hsite : Opposite.op xU.val.siteObject = Opposite.op x.val.siteObject :=
    congrArg (fun z : FieldValuedPoint B S hS F ↦ Opposite.op z.siteObject) hxU
  refine ⟨⟨⟨⟨CostructuredArrow.mk f, hEtale⟩,
    (yoneda.obj U).map (eqToHom hsite) xU.val.value, ?_⟩, rfl⟩⟩
  calc
    f.app (Opposite.op x.val.siteObject)
          ((yoneda.obj U).map (eqToHom hsite) xU.val.value) =
        F.map (eqToHom hsite) (f.app (Opposite.op xU.val.siteObject) xU.val.value) := by
      simpa only [types_comp_apply] using
        congrArg (fun k ↦ k xU.val.value) (f.naturality (eqToHom hsite))
    _ = x.val.value :=
      (map_eqToHom_eq_cast hsite _).trans (fieldValuedPoint_map_value_eq f xU.val x.val hsite hxU)

/-- The scheme underlying the chart of a small étale neighbourhood lies in the big étale site. -/
private theorem contains_chartScheme {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) :=
  V.chart.obj.left.left.property

/-- **Stacks 08AH.** The étale local ring of an algebraic space at a geometric point is a
local ring. -/
@[stacks 08AH "local ring"]
theorem isLocalRing_etaleLocalRing (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    IsLocalRing (etaleLocalRing B S hS F x) := by
  obtain ⟨U, f, hSurj, hEtale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x f hSurj hEtale
  exact (strictHenselizationEquivEtaleLocalRing hF V _ (contains_chartScheme V)
    (henselizationTower _
      (separableClosure (ResidueField ((neighborhoodChartScheme V).presheaf.stalk
        ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))))
        (chartGeometricPoint V).residueField))).isLocalRing

/-- **Stacks 08AH.** The étale local ring of a Noetherian algebraic space at a geometric point
is a Noetherian ring. -/
@[stacks 08AH "Noetherian ring"]
theorem isNoetherianRing_etaleLocalRing (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hNoetherian : IsNoetherian B S hS hZ F) (x : GeometricPoint B S hS F) :
    IsNoetherianRing (etaleLocalRing B S hS F x) := by
  obtain ⟨U, f, hSurj, hEtale, hUloc⟩ := hNoetherian.2.2
  obtain ⟨⟨V, hVU⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x f hSurj hEtale
  have hVnoeth : IsLocallyNoetherian (chartScheme V.chart) := by
    show IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.chart.obj.left)
    rw [hVU]
    exact hUloc
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let T := henselizationTower R
    (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)
  have hT : IsNoetherianRing T.strictHenselization :=
    (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization
      (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)).2.mp inferInstance
  exact isNoetherianRing_of_ringEquiv T.strictHenselization
    (strictHenselizationEquivEtaleLocalRing hF V _ (contains_chartScheme V) T)

end AlgebraicGeometry.Space

end
