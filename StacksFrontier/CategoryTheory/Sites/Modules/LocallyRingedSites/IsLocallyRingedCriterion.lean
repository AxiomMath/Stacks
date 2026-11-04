module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.UnitsSquareCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
import StacksCore.Tactic.StacksAttribute

/-!
# A criterion for a morphism of ringed sites to be locally ringed

Let `f : X ⟶ Y` be a morphism of ringed sites at independent universes,
`AlgebraicGeometry.RingedSite.HomGeneral`.  Stacks 04HA asks for its square

```
  f⁻¹(O_Y^*) ---> O_X^*
      |             |
      v             v
  f⁻¹(O_Y)  ---> O_X
```

of units subsheaves to be cartesian.  Two results turn that into a question about one site.
Stacks 04KR, `AlgebraicGeometry.inverseImageUnitsIso`, identifies the inverse image of the units
subsheaf of `Y` with the units subsheaf of the inverse-image structure sheaf `f⁻¹O_Y`, compatibly
with the two inclusions; and the structure map of `f` is, on underlying sheaves of sets, the
forgetful image of a morphism `f⁻¹O_Y ⟶ O_X` of sheaves of *commutative rings* on the site of `X`.
So the square of `f` is, up to that identification, the units square of a morphism of sheaves of
commutative rings on one site, and `AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family`
applies to it.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom`: the morphism of ringed topoi
  associated to a morphism of ringed sites, as a construction rather than an existential.
* `AlgebraicGeometry.RingedSite.HomGeneral.fSharpRingMap`: its structure map read as a morphism
  `f⁻¹O_Y ⟶ O_X` of sheaves of commutative rings on the site of `X`.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.forgetRing_map_fSharpRingMap`: forgetting the ring
  operations of `fSharpRingMap` gives the structure map on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.HomGeneral.isLocallyRinged_of_reflectsUnitsObj`: a morphism of
  ringed sites is locally ringed as soon as a family of left exact functors to sets which
  detects isomorphisms reflects units for `fSharpRingMap`.
* `AlgebraicGeometry.RingedSite.HomGeneral.reflectsUnitsObj_of_isLocallyRinged`: conversely, a
  locally ringed morphism of ringed sites has its units for `fSharpRingMap` reflected by every
  left exact functor to sets.  This is Stacks 04H9 (1) ⇒ (3).
* `AlgebraicGeometry.RingedSite.HomGeneral.isLocallyRinged_iff_reflectsUnitsObj`: the two
  together, for a family of left exact functors to sets which detects isomorphisms.

## Implementation notes

`toRingedToposHom` is a construction of the morphism of ringed topoi whose existence is
`AlgebraicGeometry.RingedSite.HomGeneral.exists_associatedRingedToposHom`.  That existential has
a `HEq` as its second clause, and the morphism of ringed topoi has to be named before its
inverse-image structure map can be.

The identification of the inverse image of the underlying sheaf of sets of `O_Y` with the
underlying sheaf of sets of `f⁻¹O_Y` is `AlgebraicGeometry.inverseImageForgetIso`, which is
`Iso.refl`.  So the endpoints of `forgetRing_map_fSharpRingMap` are literally the endpoints of
`HomGeneral.fSharpSet` and no transport is needed; only the *statement* has to name them in the
spelling each side was built in.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe t w uX vX uY vY

namespace AlgebraicGeometry.RingedSite.HomGeneral

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  (f : HomGeneral X Y)

/-- **Stacks 04HA.** The morphism of ringed topoi associated to a morphism of ringed sites: the
underlying morphism of topoi is `HomGeneral.toposHom`, and the structure map is the one of `f`,
read in the direct image along that morphism of topoi rather than in the restriction along the
site functor.

The two differ by `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which is the identity
on underlying sheaves of sets. -/
noncomputable def toRingedToposHom :
    RingedToposHom (toRingedTopos X) (toRingedTopos Y) where
  toToposHom := f.toposHom
  fSharp := f.fsharp ≫ (restrictionCommRingIso Y.J X.J f.u X.O).inv

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The associated morphism of ringed topoi has the given underlying morphism of topoi. -/
@[simp]
theorem toRingedToposHom_toToposHom : f.toRingedToposHom.toToposHom = f.toposHom := rfl

/-- The structure map of a morphism of ringed sites, read as a morphism `f⁻¹O_Y ⟶ O_X` of
sheaves of commutative rings on the site of the source. -/
noncomputable abbrev fSharpRingMap :
    (inverseImageCommRingFunctor f.toposHom).obj Y.O ⟶ X.O :=
  f.toRingedToposHom.fSharpInverseImage

/-- **Forgetting the ring operations of the inverse-image structure map gives the structure map
on underlying sheaves of sets.** -/
theorem forgetRing_map_fSharpRingMap :
    (sheafCompose X.J (forget CommRingCat.{w})).map f.fSharpRingMap = f.fSharpSet := by
  have h := RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    f.toRingedToposHom
  refine h.trans ?_
  have he : (RingedTopos.forgetRing (toRingedTopos Y)).map
      (restrictionCommRingIso Y.J X.J f.u X.O).inv =
      𝟙 ((RingedTopos.forgetRing (toRingedTopos Y)).obj
        ((pushforwardCommRingFunctor f.toposHom).obj X.O)) :=
    restrictionCommRingIso_inv_forget Y.J X.J f.u X.O
  have hmap : (RingedTopos.forgetRing (toRingedTopos Y)).map
        (f.fsharp ≫ (restrictionCommRingIso Y.J X.J f.u X.O).inv) =
      (RingedTopos.forgetRing (toRingedTopos Y)).map f.fsharp :=
    (CategoryTheory.Functor.map_comp _ _ _).trans
      ((congrArg (fun k ↦
        (RingedTopos.forgetRing (toRingedTopos Y)).map f.fsharp ≫ k) he).trans
        (Category.comp_id _))
  rw [RingedToposHom.fSharpInverseImageForget, HomGeneral.fSharpSet]
  exact congrArg (f.toposHom.adj.homEquiv _ _).symm hmap

/-- The comparison of the inverse image of the units subsheaf of the target with the units
subsheaf of the inverse-image structure sheaf, for the morphism of topoi underlying `f`. This is
Stacks 04KR. -/
noncomputable abbrev unitsComparison :
    f.inverseImage.obj (RingedTopos.units (toRingedTopos Y)) ≅
      RingedTopos.units (inverseImageRingedTopos X.C X.J (toRingedTopos Y) f.toposHom) :=
  inverseImageUnitsIso X.J (toRingedTopos Y) f.toposHom

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The comparison of units subsheaves is compatible with the two inclusions into the structure
sheaves. -/
theorem unitsComparison_inv_comp :
    f.unitsComparison.inv ≫ f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) =
      RingedTopos.unitsι
        (inverseImageRingedTopos X.C X.J (toRingedTopos Y) f.toposHom) :=
  (Iso.inv_comp_eq _).2 ((inverseImageUnitsIso_hom_comp_unitsι X.J (toRingedTopos Y)
    f.toposHom).trans (Category.comp_id _)).symm

/-- **A morphism of ringed sites is locally ringed as soon as units are reflected at a family of
left exact functors to sets which detects isomorphisms.**  For the family of stalk functors at a
conservative family of points of the site of `X`, the hypothesis is that each induced map of stalk
rings reflects units, which for locally ringed structure sheaves is condition (3) of Stacks 04H9. -/
@[sga "4 IV 13.9" "more general"]
theorem isLocallyRinged_of_reflectsUnitsObj {ι : Type*}
    (P : ι → Sheaf X.J (Type w) ⥤ Type t) (hP : ∀ i, PreservesFiniteLimits (P i))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpRingMap)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (ψ : F ⟶ G), (∀ i, IsIso ((P i).map ψ)) → IsIso ψ)
    (h : ∀ i, RingedTopos.ReflectsUnitsObj (P i) f.fSharpRingMap) :
    f.IsLocallyRinged := by
  have hsq := RingedTopos.isPullback_unitsSquare_of_family f.fSharpRingMap P hP hcons h
  refine ⟨f.unitsComparison.hom ≫ RingedTopos.unitsMapOf f.fSharpRingMap, ?_⟩
  refine hsq.of_iso f.unitsComparison.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm
  · exact (Category.comp_id _).trans (unitsComparison_inv_comp f).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((forgetRing_map_fSharpRingMap f).trans (Category.id_comp _).symm)

/-- **The units square of a locally ringed morphism of ringed sites, read on one site.** By
Stacks 04KR the cartesian square of Stacks 04HA is the units square of the morphism
`f⁻¹O_Y ⟶ O_X` of sheaves of commutative rings on the site of `X`. -/
theorem isPullback_unitsSquare_of_isLocallyRinged (hf : f.IsLocallyRinged) :
    IsPullback (RingedTopos.unitsMapOf f.fSharpRingMap)
      (RingedTopos.unitsιOf ((inverseImageCommRingFunctor f.toposHom).obj Y.O))
      (RingedTopos.unitsιOf X.O) (RingedTopos.forgetRingMap f.fSharpRingMap) := by
  obtain ⟨t, ht⟩ := hf
  have hcomp : f.unitsComparison.hom ≫
      RingedTopos.unitsιOf ((inverseImageCommRingFunctor f.toposHom).obj Y.O) =
      f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) :=
    ((Iso.inv_comp_eq f.unitsComparison).1 (unitsComparison_inv_comp f)).symm
  have hbot : f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) ≫ f.fSharpSet =
      f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) ≫
        RingedTopos.forgetRingMap f.fSharpRingMap :=
    congrArg (fun k ↦ f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) ≫ k)
      (forgetRing_map_fSharpRingMap f).symm
  have hmono : Mono (RingedTopos.unitsιOf X.O) :=
    RingedTopos.unitsι_mono (RingedTopos.ofStructureSheaf X.J X.O)
  have htop : t = f.unitsComparison.hom ≫ RingedTopos.unitsMapOf f.fSharpRingMap := by
    refine (cancel_mono (RingedTopos.unitsιOf X.O)).1 ?_
    rw [Category.assoc, RingedTopos.unitsMapOf_comp_unitsιOf, ← Category.assoc, hcomp]
    exact ht.w.trans hbot
  refine ht.of_iso f.unitsComparison (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans htop
  · exact (Category.comp_id _).trans hcomp.symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((forgetRing_map_fSharpRingMap f).symm.trans (Category.id_comp _).symm)

/-- **Stacks 04H9, (1) ⇒ (3) at independent universes.** If a morphism of ringed sites is
locally ringed, then every left exact functor to sets reflects units for the induced morphism
`f⁻¹O_Y ⟶ O_X`; at a stalk functor this is locality of the induced map of stalk rings. -/
@[stacks 04H9 "(1)⇒(3), independent universes", sga "4 IV 13.9" "c) (i) ⇒ (ii)"]
theorem reflectsUnitsObj_of_isLocallyRinged (hf : f.IsLocallyRinged)
    (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P] :
    RingedTopos.ReflectsUnitsObj P f.fSharpRingMap :=
  RingedTopos.reflectsUnitsObj_of_isPullback P f.fSharpRingMap
    (f.isPullback_unitsSquare_of_isLocallyRinged hf)

/-- **Stacks 04H9, (1) ⇔ (3) at independent universes.** For a family of left exact functors to
sets which detects isomorphisms — in practice the stalk functors at a conservative family of
points — a morphism of ringed sites is locally ringed exactly when each member reflects units
for `f⁻¹O_Y ⟶ O_X`. -/
@[stacks 04H9 "(1)⇔(3) at a conservative family, independent universes",
  sga "4 IV 13.9" "c) (i)⇔(ii) enough pts"]
theorem isLocallyRinged_iff_reflectsUnitsObj {ι : Type*}
    (P : ι → Sheaf X.J (Type w) ⥤ Type t) (hP : ∀ i, PreservesFiniteLimits (P i))
    [HasPullback (RingedTopos.unitsιOf X.O)
      (RingedTopos.forgetRingMap f.fSharpRingMap)]
    (hcons : ∀ {F G : Sheaf X.J (Type w)} (ψ : F ⟶ G), (∀ i, IsIso ((P i).map ψ)) → IsIso ψ) :
    f.IsLocallyRinged ↔ ∀ i, RingedTopos.ReflectsUnitsObj (P i) f.fSharpRingMap :=
  ⟨fun hf i ↦ have := hP i; f.reflectsUnitsObj_of_isLocallyRinged hf (P i),
    fun h ↦ f.isLocallyRinged_of_reflectsUnitsObj P hP hcons h⟩

end AlgebraicGeometry.RingedSite.HomGeneral

end
