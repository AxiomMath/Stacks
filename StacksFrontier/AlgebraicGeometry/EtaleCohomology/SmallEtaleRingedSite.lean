module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteOverStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.SitePoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily

/-!
# The small étale ringed site of a scheme

Let `B` be a big étale site containing a scheme `S`. The small étale site of `S`, together with
the sheaf of global functions `T ↦ Γ(T, 𝒪_T)`, is a ringed site, and it is *locally* ringed: the
sections `0` and `1` of the structure sheaf are nowhere equal, and every section is, on some
étale covering, either a unit or has unit complement.

## Main definitions

* `AlgebraicGeometry.SmallEtale.commRingStructureSheaf` — the structure sheaf of the small étale
  site of `S`, with values in commutative rings.
* `AlgebraicGeometry.smallEtaleRingedSite` — the small étale site of `S` with that structure
  sheaf, as a ringed site.
* `AlgebraicGeometry.commRingEtaleStalkForgetIso` — the stalk of that structure sheaf at a
  geometric point, after forgetting commutativity, is the étale local ring.

## Main results

* `AlgebraicGeometry.isLocalRing_presheafFiber_commRingStructurePresheaf` — the stalk of the
  structure sheaf at any point of the small étale site is a local ring.
* `AlgebraicGeometry.smallEtaleRingedSite_isLocallyRinged` — the small étale ringed site of a
  scheme is locally ringed.

## References

* [Stacks Project, Tag 04HZ](https://stacks.math.columbia.edu/tag/04HZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The structure sheaf of commutative rings -/

/-- The presheaf of commutative rings of global functions on the small étale site of `S`. -/
public abbrev SmallEtale.commRingStructurePresheaf :
    (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ

/-- The canonical functor from the small étale site to schemes is the inclusion into the big
étale slice followed by the forgetful functor of that slice. -/
public theorem toScheme_eq_post_comp_forget :
    SmallEtale.toScheme B S hS =
      (SmallEtale.inclusion B S hS ⋙ Over.post B.inclusion) ⋙ Over.forget S :=
  CategoryTheory.Functor.ext fun _ => rfl

/-- Forgetting the commutativity of the structure presheaf of the small étale site gives the
presheaf underlying `AlgebraicGeometry.SmallEtale.structureSheaf`. -/
public theorem commRingStructurePresheaf_comp_forget₂ :
    SmallEtale.commRingStructurePresheaf B S hS ⋙ forget₂ CommRingCat RingCat =
      (SmallEtale.structureSheaf B S hS).obj := by
  change (SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat =
    ((SmallEtale.inclusion B S hS ⋙ Over.post B.inclusion) ⋙ Over.forget S).op ⋙
      Scheme.Γ ⋙ forget₂ CommRingCat RingCat
  rw [toScheme_eq_post_comp_forget]

/-- Global functions form a sheaf of commutative rings on the small étale site of `S`. -/
public theorem SmallEtale.commRingStructure_isSheaf :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      (SmallEtale.commRingStructurePresheaf B S hS) :=
  Stacks.Sites.isSheaf_commRingCat_of_isSheaf_forget _ _
    (SmallEtale.isSheaf_globalSections B S hS)

/-- The structure sheaf of commutative rings of the small étale site of `S`. -/
public def SmallEtale.commRingStructureSheaf :
    Sheaf (SmallEtale.topology B S hS) CommRingCat.{u} :=
  ⟨SmallEtale.commRingStructurePresheaf B S hS, SmallEtale.commRingStructure_isSheaf B S hS⟩

/-- The structure sheaf of commutative rings has the presheaf of global functions as its
underlying presheaf. -/
@[simp]
public theorem SmallEtale.commRingStructureSheaf_obj :
    (SmallEtale.commRingStructureSheaf B S hS).obj =
      SmallEtale.commRingStructurePresheaf B S hS :=
  rfl

/-- The small étale site of `S`, endowed with its structure sheaf of commutative rings, as a
ringed site. -/
public abbrev smallEtaleRingedSite : RingedSite.{u + 1, u, u} where
  C := SmallEtale B S hS
  J := SmallEtale.topology B S hS
  O := SmallEtale.commRingStructureSheaf B S hS

/-! ### The stalks are local rings -/

/-- The stalk of the commutative-ring structure sheaf at a geometric point is the étale local
ring `AlgebraicGeometry.etaleLocalRing`, after forgetting commutativity. -/
public def commRingEtaleStalkForgetIso (s : GeometricPoint S) :
    (forget₂ CommRingCat RingCat).obj
        (etaleStalk B S hS s (SmallEtale.commRingStructurePresheaf B S hS)) ≅
      etaleLocalRing B S hS s := by
  let D := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
    SmallEtale.commRingStructurePresheaf B S hS
  have hD : D ⋙ forget₂ CommRingCat RingCat =
      (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj := by
    change (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.commRingStructurePresheaf B S hS ⋙ forget₂ CommRingCat RingCat) = _
    rw [commRingStructurePresheaf_comp_forget₂]
  let : IsFiltered (geometricPointFiber B S hS s).Elementsᵒᵖ := inferInstance
  let : PreservesColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ
      (forget₂ CommRingCat RingCat) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered
      (C := (geometricPointFiber B S hS s).Elementsᵒᵖ) (forget₂ CommRingCat RingCat)
  exact (preservesColimitIso (forget₂ CommRingCat RingCat) D).trans
    (HasColimit.isoOfNatIso (eqToIso hD))

/-- The stalk of the structure sheaf of the small étale site at a geometric point is a local
ring. -/
public theorem isLocalRing_etaleStalk_commRingStructurePresheaf (s : GeometricPoint S) :
    IsLocalRing ↥(etaleStalk B S hS s (SmallEtale.commRingStructurePresheaf B S hS)) := by
  have := etaleLocalRing_strictHenselian B S hS s
  exact (commRingEtaleStalkForgetIso B S hS s).ringCatIsoToRingEquiv.symm.isLocalRing

/-- The stalk of the structure sheaf of the small étale site of `S` at *any* point of the site is
a local ring. -/
public theorem isLocalRing_presheafFiber_commRingStructurePresheaf
    (p : (SmallEtale.topology B S hS).Point.{u}) :
    IsLocalRing ↥((p.presheafFiber (A := CommRingCat.{u})).obj
      (SmallEtale.commRingStructurePresheaf B S hS)) := by
  obtain ⟨s, ⟨e⟩⟩ := exists_geometricPoint_sitePoint_iso B S hS p
  let E : (geometricPointSitePoint B S hS s).presheafFiber (A := CommRingCat.{u}) ≅
      p.presheafFiber (A := CommRingCat.{u}) :=
    { hom := e.hom.presheafFiber
      inv := e.inv.presheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, e.inv_hom_id,
          GrothendieckTopology.Point.Hom.presheafFiber_id]
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.presheafFiber_comp, e.hom_inv_id,
          GrothendieckTopology.Point.Hom.presheafFiber_id] }
  have h : IsLocalRing ↥(((geometricPointSitePoint B S hS s).presheafFiber
      (A := CommRingCat.{u})).obj (SmallEtale.commRingStructurePresheaf B S hS)) :=
    isLocalRing_etaleStalk_commRingStructurePresheaf B S hS s
  exact (E.app (SmallEtale.commRingStructurePresheaf B S hS)).commRingCatIsoToRingEquiv.isLocalRing

/-- The small étale site of a scheme, endowed with its structure sheaf, is a
locally ringed site. -/
@[stacks 04HZ]
public theorem smallEtaleRingedSite_isLocallyRinged :
    RingedSite.IsLocallyRinged (smallEtaleRingedSite B S hS) := by
  obtain ⟨P, hP⟩ :=
    (GrothendieckTopology.hasConservativeFamily_iff_exists
      (SmallEtale.topology B S hS)).1 (SmallEtale.hasConservativeFamily B S hS)
  exact RingedSite.isLocallyRinged_of_local_stalks (smallEtaleRingedSite B S hS) P hP
    fun p _ => isLocalRing_presheafFiber_commRingStructurePresheaf B S hS p

end AlgebraicGeometry

end
