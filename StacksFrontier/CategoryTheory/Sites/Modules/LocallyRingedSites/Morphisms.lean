module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedTopos
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of locally ringed topoi and of locally ringed sites

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is *locally ringed* when the
square

```
  f⁻¹(O_D^*) ---> O_C^*
      |             |
      v             v
  f⁻¹(O_D)  ---> O_C
```

comparing the inverse image of the units subsheaf of the target with the units subsheaf of the
source is cartesian, the bottom arrow being the structure map on underlying sheaves of sets. A
morphism of ringed sites is locally ringed when the morphism of ringed topoi it induces is. Since
the inclusion of units is a monomorphism, an arrow making the square commute is unique if it
exists.

## Main definitions

* `AlgebraicGeometry.RingedTopos.units` and `.unitsι`: the units subsheaf of the structure sheaf
  of a ringed topos and its inclusion.
* `AlgebraicGeometry.RingedToposHom.fSharpSet`: the structure map of a morphism of ringed topoi
  on underlying sheaves of sets, in inverse-image form.
* `AlgebraicGeometry.RingedToposHom.IsLocallyRinged`: the cartesian units-square condition.
* `AlgebraicGeometry.RingedSite.Hom.IsLocallyRinged`: the same condition for a morphism of
  ringed sites.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_iff_existsUnique`: a morphism of ringed
  topoi is locally ringed if and only if a unique top arrow makes its units square cartesian.
* `AlgebraicGeometry.RingedSite.Hom.exists_associatedRingedToposHom`: a morphism of ringed sites
  induces a morphism of ringed topoi whose underlying morphism of topoi and whose structure map
  on underlying sheaves of sets are the given ones.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w'

namespace AlgebraicGeometry




namespace RingedTopos

/-- Regard the site presenting a ringed topos as a ringed site. -/
abbrev toRingedSite (X : RingedTopos.{v, u, w}) : RingedSite.{u, v, w} :=
  { C := X.C, J := X.J, O := X.O }

/-- The units subsheaf of the underlying sheaf of sets of a ringed topos. -/
noncomputable abbrev units (X : RingedTopos.{v, u, w}) : X.Topos :=
  (sheafCompose X.J (forget CommGrpCat.{w})).obj (RingedSite.unitsSheaf (toRingedSite X))

/-- Inclusion of the units subsheaf in the structure sheaf. -/
noncomputable abbrev unitsι (X : RingedTopos.{v, u, w}) :
    units X ⟶ X.forgetRing.obj X.O :=
  RingedSite.unitsSheafι (toRingedSite X)

/-- The inclusion of units is a monomorphism. -/
instance unitsι_mono (X : RingedTopos.{v, u, w}) : Mono (unitsι X) :=
  RingedSite.unitsSheafι_mono (toRingedSite X)

end RingedTopos

namespace RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- The structure map on underlying sheaves of sets, in inverse-image form. -/
noncomputable abbrev fSharpSet (f : RingedToposHom X Y) :
    f.toToposHom.inverseImage.obj (Y.forgetRing.obj Y.O) ⟶ X.forgetRing.obj X.O :=
  (f.toToposHom.adj.homEquiv _ _).symm (Y.forgetRing.map f.fSharp)

/-- A morphism of ringed topoi is locally ringed when its square of units subsheaves, over the
structure map `fSharpSet f`, is cartesian. -/
@[stacks 04HA "morphisms of locally ringed topoi"]
abbrev IsLocallyRinged (f : RingedToposHom X Y) : Prop :=
  ∃ t : f.toToposHom.inverseImage.obj (RingedTopos.units Y) ⟶ RingedTopos.units X,
    IsPullback t (f.toToposHom.inverseImage.map (RingedTopos.unitsι Y))
      (RingedTopos.unitsι X) (fSharpSet f)

/-- A map into the units subsheaf is determined by its composite with the inclusion. -/
theorem unitsMap_unique (f : RingedToposHom X Y)
    (t₁ t₂ : f.toToposHom.inverseImage.obj (RingedTopos.units Y) ⟶ RingedTopos.units X)
    (h₁ : t₁ ≫ RingedTopos.unitsι X =
      f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) ≫ fSharpSet f)
    (h₂ : t₂ ≫ RingedTopos.unitsι X =
      f.toToposHom.inverseImage.map (RingedTopos.unitsι Y) ≫ fSharpSet f) :
    t₁ = t₂ :=
  (cancel_mono (RingedTopos.unitsι X)).mp (h₁.trans h₂.symm)

/-- A morphism of ringed topoi is locally ringed if and only if a unique top arrow makes its square
of units subsheaves cartesian. -/
theorem isLocallyRinged_iff_existsUnique (f : RingedToposHom X Y) :
    IsLocallyRinged f ↔
      ∃! t : f.toToposHom.inverseImage.obj (RingedTopos.units Y) ⟶ RingedTopos.units X,
        IsPullback t (f.toToposHom.inverseImage.map (RingedTopos.unitsι Y))
          (RingedTopos.unitsι X) (fSharpSet f) :=
  ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht, fun s hs ↦ unitsMap_unique f s t hs.w ht.w⟩, fun ⟨t, ht, _⟩ ↦ ⟨t, ht⟩⟩

end RingedToposHom

namespace RingedSite

/-- The ringed topos presented by a ringed site. -/
@[sga "4 IV 11.1.1" "special case"]
abbrev toRingedTopos (X : RingedSite.{u, v, w}) : RingedTopos.{v, u, w} :=
  { C := X.C, J := X.J, O := X.O }

namespace Hom

variable {X Y : RingedSite.{u, u, u}}

/-- The structure map on underlying sheaves of sets, in inverse-image form. -/
noncomputable abbrev fSharpSet (f : RingedSite.Hom X Y) :
    (f.u.sheafPullback (Type u) Y.J X.J).obj
      ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ⟶
        (sheafCompose X.J (forget CommRingCat.{u})).obj X.O :=
  ((f.u.sheafAdjunctionContinuous (Type u) Y.J X.J).homEquiv _ _).symm
    ((sheafCompose Y.J (forget CommRingCat.{u})).map f.fsharp)

variable [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]

/-- A morphism of ringed sites induces a morphism of ringed topoi whose underlying morphism of
topoi and whose structure map on underlying sheaves of sets are the given ones. -/
@[stacks 04HA "associated ringed-topos morphism of a ringed-site morphism",
  sga "4 IV 13.3.1" "site ⇒ topos morphism"]
theorem exists_associatedRingedToposHom (f : RingedSite.Hom X Y) :
    ∃ g : RingedToposHom (toRingedTopos X) (toRingedTopos Y),
      (g.toToposHom = f.isMorphismOfSites.morphismOfTopoi) ∧
      HEq (RingedToposHom.fSharpSet g) (fSharpSet f) := by
  let φ := f.isMorphismOfSites.morphismOfTopoi
  let e : (pushforwardCommRingFunctor φ).obj X.O ≅
      (f.u.sheafPushforwardContinuous CommRingCat.{u} Y.J X.J).obj X.O :=
    restrictionCommRingIso Y.J X.J f.u X.O
  have he : (RingedTopos.forgetRing (toRingedTopos Y)).map e.inv =
      𝟙 ((RingedTopos.forgetRing (toRingedTopos Y)).obj
        ((pushforwardCommRingFunctor φ).obj X.O)) :=
    restrictionCommRingIso_inv_forget Y.J X.J f.u X.O
  refine ⟨⟨φ, f.fsharp ≫ e.inv⟩, rfl, ?_⟩
  have hmap :
      (RingedTopos.forgetRing (toRingedTopos Y)).map (f.fsharp ≫ e.inv) =
      (RingedTopos.forgetRing (toRingedTopos Y)).map f.fsharp :=
    (CategoryTheory.Functor.map_comp _ _ _).trans
      ((congrArg (fun k ↦
        (RingedTopos.forgetRing (toRingedTopos Y)).map f.fsharp ≫ k)
          he).trans (Category.comp_id _))
  rw [RingedToposHom.fSharpSet, fSharpSet, hmap]
  dsimp [φ, CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi]
  rfl

/-- The specified ringed-topos morphism associated to a morphism of ringed sites. -/
noncomputable def associatedRingedToposHom (f : RingedSite.Hom X Y) :
    { g : RingedToposHom (toRingedTopos X) (toRingedTopos Y) //
      (g.toToposHom = f.isMorphismOfSites.morphismOfTopoi) ∧
      HEq (RingedToposHom.fSharpSet g) (fSharpSet f) } :=
  ⟨Classical.choose (exists_associatedRingedToposHom f),
    Classical.choose_spec (exists_associatedRingedToposHom f)⟩

/-- A morphism of ringed sites is locally ringed when the units square for its associated morphism
of ringed topoi is cartesian. -/
@[stacks 04HA "morphisms of locally ringed sites"]
abbrev IsLocallyRinged (f : RingedSite.Hom X Y) : Prop :=
  RingedToposHom.IsLocallyRinged (associatedRingedToposHom f).1

end Hom
end RingedSite


end AlgebraicGeometry
