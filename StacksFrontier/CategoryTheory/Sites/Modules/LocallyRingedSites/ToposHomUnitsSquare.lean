module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.UnitsSquareCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafInverseImage

/-!
# The units square of a morphism of ringed topoi, read on one site

Stacks 04HA calls a morphism `f : X ⟶ Y` of ringed topoi *locally ringed* when its square

```
  f⁻¹(O_Y^*) ---> O_X^*
      |             |
      v             v
  f⁻¹(O_Y)  ---> O_X
```

of units subsheaves is cartesian.  By Stacks 04KR the inverse image of the units subsheaf of
`Y` is the units subsheaf of the inverse-image structure sheaf `f⁻¹O_Y`, so that square is the
units square of the morphism `f⁻¹O_Y ⟶ O_X` of sheaves of commutative rings on the site of
`X`, and `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family` applies to it.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.unitsComparison`: the comparison of Stacks 04KR for the
  morphism of topoi underlying `f`.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj`: a morphism of ringed
  topoi is locally ringed as soon as a family of left exact functors to sets which detects
  isomorphisms reflects units for `f⁻¹O_Y ⟶ O_X`.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj_comp`: the same with the
  hypothesis asked only of `f⁻¹O_Y ⟶ O_X ⟶ O'` for one further map `q : O_X ⟶ O'` of structure
  sheaves on the site of `X`.
* `AlgebraicGeometry.RingedToposHom.isPullback_unitsSquare_of_isLocallyRinged` and
  `AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`: conversely, a locally
  ringed morphism of ringed topoi has that units square cartesian, hence has units reflected by
  every left exact functor to sets.  The second is Stacks 04H9, (1) ⇒ (3).

## Implementation notes

`AlgebraicGeometry.RingedSite.HomGeneral.isLocallyRinged_of_reflectsUnitsObj` is the same
statement for a morphism of ringed *sites*.  It does not cover a morphism of ringed topoi whose
underlying morphism of topoi is not presented by a functor of sites — the morphism attached to
a morphism of algebraic spaces is one, a morphism of algebraic spaces not pulling étale charts
of the target back to étale charts of the source — so the argument is run here directly on
`AlgebraicGeometry.RingedToposHom`.  It is the same argument: the three inputs it uses,
`AlgebraicGeometry.inverseImageUnitsIso`,
`AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family` and the identification of
`AlgebraicGeometry.RingedToposHom.fSharpSet` with the forgetful image of
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`, are all available at this generality.

The two structure sheaves are required to take their sections in one universe, which is what
lets the units square of the target be compared with a square on the site of the source at all.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe t w v u v' u'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  (f : RingedToposHom X Y)

/-- **Stacks 04KR for a morphism of ringed topoi.** The comparison of the inverse image of the
units subsheaf of the target with the units subsheaf of the inverse-image structure sheaf. -/
noncomputable abbrev unitsComparison :
    f.toToposHom.inverseImage.obj (RingedTopos.units Y) ≅
      RingedTopos.units (inverseImageRingedTopos X.C X.J Y f.toToposHom) :=
  inverseImageUnitsIso X.J Y f.toToposHom

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The comparison of units subsheaves is compatible with the two inclusions into the structure
sheaves. -/
theorem unitsComparison_inv_comp :
    f.unitsComparison.inv ≫ f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) =
      RingedTopos.unitsι (inverseImageRingedTopos X.C X.J Y f.toToposHom) := by
  refine (Iso.inv_comp_eq _).2 ?_
  exact ((inverseImageUnitsIso_hom_comp_unitsι X.J Y f.toToposHom).trans
    (Category.comp_id _)).symm

/-- Forgetting the ring operations of the inverse-image structure map gives the structure map on
underlying sheaves of sets. -/
theorem forgetRing_map_fSharpInverseImage_eq_fSharpSet :
    (sheafCompose X.J (forget CommRingCat.{w})).map f.fSharpInverseImage = f.fSharpSet :=
  forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget f

/-- **A morphism of ringed topoi is locally ringed as soon as units are reflected at a family of
left exact functors to sets which detects isomorphisms.**

By Stacks 04KR the units square of `f` is the units square of the morphism `f⁻¹O_Y ⟶ O_X` of
sheaves of commutative rings on the site of `X`, and
`AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family` makes the latter cartesian.
For the family of stalk functors at a conservative family of points of the site of `X`, the
hypothesis is that each induced map of stalk rings reflects units, which for locally ringed
structure sheaves is condition (3) of Stacks 04H9. -/
theorem isLocallyRinged_of_reflectsUnitsObj {ι : Type*}
    (P : ι → Sheaf X.J (Type w) ⥤ Type t) (hP : ∀ i, PreservesFiniteLimits (P i))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (ψ : F ⟶ G), (∀ i, IsIso ((P i).map ψ)) → IsIso ψ)
    (h : ∀ i, RingedTopos.ReflectsUnitsObj (P i) f.fSharpInverseImage) :
    f.IsLocallyRinged := by
  have hsq := RingedTopos.isPullback_unitsSquare_of_family f.fSharpInverseImage P hP hcons h
  refine ⟨f.unitsComparison.hom ≫ RingedTopos.unitsMapOf f.fSharpInverseImage, ?_⟩
  refine hsq.of_iso f.unitsComparison.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm
  · exact (Category.comp_id _).trans (unitsComparison_inv_comp f).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((forgetRing_map_fSharpInverseImage_eq_fSharpSet f).trans (Category.id_comp _).symm)

/-- **A morphism of ringed topoi whose structure map reflects units after one further map of
structure sheaves is locally ringed.**

Given `q : O_X ⟶ O'` on the site of `X`, reflection of units at each `P i` for the composite
`f⁻¹O_Y ⟶ O_X ⟶ O'` already forces reflection for `f⁻¹O_Y ⟶ O_X`
(`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_of_comp`), so the units square of `f` is
cartesian by `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj`.

This is the shape the [Stacks, Tag 05ZT] route needs, where `O_X` is a sheaf of rings `𝒜` that
is a square-zero extension of the structure sheaf `O'` of an algebraic space and `q` is that
surjection: the composite is the structure map of the morphism of algebraic spaces, whose
morphism of small étale ringed topoi is locally ringed
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged`), so the hypothesis comes
from `AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` once the composite
has been identified with that structure map.  Nothing is assumed of `q` here: the square-zero
hypothesis of Tag 05ZT enters in producing that identification and in making the source a
locally ringed site, not in this step. -/
theorem isLocallyRinged_of_reflectsUnitsObj_comp {O' : Sheaf X.J CommRingCat.{w}}
    (q : X.O ⟶ O') {ι : Type*} (P : ι → Sheaf X.J (Type w) ⥤ Type t)
    (hP : ∀ i, PreservesFiniteLimits (P i))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpInverseImage)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (ψ : F ⟶ G), (∀ i, IsIso ((P i).map ψ)) → IsIso ψ)
    (h : ∀ i, RingedTopos.ReflectsUnitsObj (P i) (f.fSharpInverseImage ≫ q)) :
    f.IsLocallyRinged :=
  f.isLocallyRinged_of_reflectsUnitsObj P hP hcons fun i ↦
    RingedTopos.reflectsUnitsObj_of_comp (P i) f.fSharpInverseImage q (h i)

/-- **The units square of a locally ringed morphism of ringed topoi, read on one site.** By
Stacks 04KR the cartesian square of Stacks 04HA is the units square of the morphism
`f⁻¹O_Y ⟶ O_X` of sheaves of commutative rings on the site of `X`. -/
theorem isPullback_unitsSquare_of_isLocallyRinged (hf : f.IsLocallyRinged) :
    IsPullback (RingedTopos.unitsMapOf f.fSharpInverseImage)
      (RingedTopos.unitsιOf ((inverseImageCommRingFunctor f.toToposHom).obj Y.O))
      (RingedTopos.unitsιOf X.O) (RingedTopos.forgetRingMap f.fSharpInverseImage) := by
  obtain ⟨t, ht⟩ := hf
  have hcomp : f.unitsComparison.hom ≫
      RingedTopos.unitsιOf ((inverseImageCommRingFunctor f.toToposHom).obj Y.O) =
      f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) :=
    ((Iso.inv_comp_eq f.unitsComparison).1 (unitsComparison_inv_comp f)).symm
  have hbot : f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) ≫ f.fSharpSet =
      f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) ≫
        RingedTopos.forgetRingMap f.fSharpInverseImage :=
    congrArg (fun k ↦ f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) ≫ k)
      (forgetRing_map_fSharpInverseImage_eq_fSharpSet f).symm
  have hmono : Mono (RingedTopos.unitsιOf X.O) :=
    RingedTopos.unitsι_mono (RingedTopos.ofStructureSheaf X.J X.O)
  have htop : t = f.unitsComparison.hom ≫ RingedTopos.unitsMapOf f.fSharpInverseImage := by
    refine (cancel_mono (RingedTopos.unitsιOf X.O)).1 ?_
    rw [Category.assoc, RingedTopos.unitsMapOf_comp_unitsιOf, ← Category.assoc, hcomp]
    exact ht.w.trans hbot
  refine ht.of_iso f.unitsComparison (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans htop
  · exact (Category.comp_id _).trans hcomp.symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((forgetRing_map_fSharpInverseImage_eq_fSharpSet f).symm.trans (Category.id_comp _).symm)

/-- **Stacks 04H9, (1) ⇒ (3), for a morphism of ringed topoi.** If a morphism of ringed topoi is
locally ringed, then every left exact functor to sets reflects units for the induced morphism
`f⁻¹O_Y ⟶ O_X`; at a stalk functor this is locality of the induced map of stalk rings. -/
theorem reflectsUnitsObj_of_isLocallyRinged (hf : f.IsLocallyRinged)
    (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P] :
    RingedTopos.ReflectsUnitsObj P f.fSharpInverseImage :=
  RingedTopos.reflectsUnitsObj_of_isPullback P f.fSharpInverseImage
    (f.isPullback_unitsSquare_of_isLocallyRinged hf)

end AlgebraicGeometry.RingedToposHom

end
