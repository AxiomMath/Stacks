module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The unit of the derived adjunction along a composite

Let `j : Z ⟶ W`, `i : W ⟶ V` and `c : V ⟶ T` be morphisms of ringed spaces. The unit of
`L(j ≫ i)^* ⊣ R(j ≫ i)_*` is the composite of the units along `i` and along `j`, read through the
composition isomorphisms of derived pullback (Tag 0D5S) and of derived pushforward (Tag 079W).
Consequently the map `Rc_*K ⟶ R(i ≫ c)_* Li^*K` given by `Rc_*` of the unit and the composition
isomorphism — the map underlying the pullback on derived global sections — is compatible with
composition.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp_unit_app`: the unit
  along a composite.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.map_unit_comp_derivedPushforwardCompIso_comp`:
  the pushed-forward unit is compatible with composition.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 10000] HasDerivedCategory.standard

variable {T V W Z : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V) (j : Z ⟶ W)

/-- **The unit of the derived adjunction along a composite** `j ≫ i` is the unit along `i`,
followed by `Ri_*` of the unit along `j`, of `Ri_* Rj_*` of the composition isomorphism of
Tag 0D5S and of the composition isomorphism of derived pushforward. This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp` read at the unit. -/
theorem derivedAdjunction_comp_unit_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    (derivedAdjunction (j ≫ i)).unit.app K =
      (derivedAdjunction i).unit.app K ≫
        (derivedPushforward i).map ((derivedAdjunction j).unit.app ((derivedPullback i).obj K)) ≫
        (derivedPushforward i).map ((derivedPushforward j).map
          ((derivedPullbackCompIsoCanonical j i).hom.app K)) ≫
        (derivedPushforwardCompIso j i).hom.app ((derivedPullback (j ≫ i)).obj K) := by
  rw [← derivedAdjunction_comp j i]
  simp [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft, Adjunction.comp_unit_app]

/-- The map `Rc_*K ⟶ R(i ≫ c)_* Li^*K`, named only for the proof below. -/
private abbrev pullMap (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    (derivedPushforward c).obj K ⟶ (derivedPushforward (i ≫ c)).obj ((derivedPullback i).obj K) :=
  (derivedPushforward c).map ((derivedAdjunction i).unit.app K) ≫
    (derivedPushforwardCompIso i c).hom.app _

private theorem pullMap_comp (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    pullMap c i K ≫ pullMap (i ≫ c) j ((derivedPullback i).obj K) =
      pullMap c (j ≫ i) K ≫
        (derivedPushforward ((j ≫ i) ≫ c)).map
          ((derivedPullbackCompIsoCanonical j i).inv.app K) := by
  have hassoc := congr_app (congrArg Iso.hom
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardCompIso_assoc j i c))
    ((derivedPullback j).obj ((derivedPullback i).obj K))
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] at hassoc
  simp only [pullMap, derivedAdjunction_comp_unit_app, Functor.map_comp, Category.assoc]
  have hn := (derivedPushforwardCompIso i c).hom.naturality
    ((derivedAdjunction j).unit.app ((derivedPullback i).obj K))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← reassoc_of% hn]
  simp only [hassoc]
  have n2 := (derivedPushforwardCompIso (j ≫ i) c).hom.naturality
    ((derivedPullbackCompIsoCanonical j i).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at n2
  simp only [← n2]
  have key : (derivedPushforward i).map ((derivedPushforward j).map
      ((derivedPullbackCompIsoCanonical j i).hom.app K)) ≫
      (derivedPushforwardCompIso j i).hom.app ((derivedPullback (j ≫ i)).obj K) ≫
      (derivedPushforward (j ≫ i)).map ((derivedPullbackCompIsoCanonical j i).inv.app K) =
      (derivedPushforwardCompIso j i).hom.app
        ((derivedPullback j).obj ((derivedPullback i).obj K)) := by
    have n4 := (derivedPushforwardCompIso j i).hom.naturality
      ((derivedPullbackCompIsoCanonical j i).hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at n4
    simp only [reassoc_of% n4, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj]
    simp
  have key' := (derivedPushforward c).congr_map key
  simp only [Functor.map_comp] at key'
  simp only [reassoc_of% key']
  rfl


/-- **The pushed-forward unit is compatible with composition.** The map
`Rc_*K ⟶ R(i ≫ c)_* Li^*K` given by `Rc_*` of the unit of `Li^* ⊣ Ri_*` and the composition
isomorphism, followed by the same map along `j` for `i ≫ c`, is the map along `j ≫ i` followed by
the composition isomorphism `Lj^* Li^* ≅ L(j ≫ i)^*` of Tag 0D5S. -/
theorem map_unit_comp_derivedPushforwardCompIso_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    ((derivedPushforward c).map ((derivedAdjunction i).unit.app K) ≫
        (derivedPushforwardCompIso i c).hom.app ((derivedPullback i).obj K) :
        (derivedPushforward c).obj K ⟶
          (derivedPushforward (i ≫ c)).obj ((derivedPullback i).obj K)) ≫
      ((derivedPushforward (i ≫ c)).map
          ((derivedAdjunction j).unit.app ((derivedPullback i).obj K)) ≫
        (derivedPushforwardCompIso j (i ≫ c)).hom.app
          ((derivedPullback j).obj ((derivedPullback i).obj K)) :
        (derivedPushforward (i ≫ c)).obj ((derivedPullback i).obj K) ⟶
          (derivedPushforward (j ≫ i ≫ c)).obj
            ((derivedPullback j).obj ((derivedPullback i).obj K))) =
      ((derivedPushforward c).map ((derivedAdjunction (j ≫ i)).unit.app K) ≫
        (derivedPushforwardCompIso (j ≫ i) c).hom.app ((derivedPullback (j ≫ i)).obj K) :
        (derivedPushforward c).obj K ⟶
          (derivedPushforward ((j ≫ i) ≫ c)).obj ((derivedPullback (j ≫ i)).obj K)) ≫
        ((derivedPushforward ((j ≫ i) ≫ c)).map
          ((derivedPullbackCompIsoCanonical j i).inv.app K) :
          (derivedPushforward ((j ≫ i) ≫ c)).obj ((derivedPullback (j ≫ i)).obj K) ⟶
            (derivedPushforward ((j ≫ i) ≫ c)).obj
              ((derivedPullback j).obj ((derivedPullback i).obj K))) :=
  pullMap_comp c i j K


end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
