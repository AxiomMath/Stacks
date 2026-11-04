module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of locally ringed sites at independent universes

`AlgebraicGeometry.RingedSite.Hom` takes both of its endpoints in `RingedSite.{u, u, u}`, so the
objects and the morphisms of a ringed site are forced into one universe.  Every site of schemes
in this development has objects in `Type (u + 1)` and morphisms in `Type u` — for instance
`AlgebraicGeometry.smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}` — so none of them can be
an endpoint of an `AlgebraicGeometry.RingedSite.Hom`, and a statement about a morphism of such
ringed sites cannot be written down at all.

This file adds, alongside `AlgebraicGeometry.RingedSite.Hom` and without touching it, the same
notion with the object and morphism universes of the source independent of those of the target:
`AlgebraicGeometry.RingedSite.HomGeneral`.  The site condition is taken at the unrestricted
`IsMorphismOfSites`, which asks only that the direct image on sheaves of sets admit a left exact
left adjoint and places no constraint on the universes, instead of
`CategoryTheory.Functor.IsMorphismOfSites`, which is stated for small sites only.  The universe
of the sheaves of sets is the universe of the sections of the two structure sheaves, because that
is the universe at which an `AlgebraicGeometry.RingedTopos` declares its underlying topos.

## Main definitions

* `IsMorphismOfSites.morphismOfTopoi`: the morphism of topoi of a morphism of sites, at
  independent universes.  This is Stacks 00XC with the smallness hypothesis of
  `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi` removed.
* `AlgebraicGeometry.RingedSite.HomGeneral`: a morphism of ringed sites whose source and target
  may have different object and morphism universes.
* `AlgebraicGeometry.RingedSite.HomGeneral.fSharpSet`: its structure map on underlying sheaves of
  sets, in inverse-image form.
* `AlgebraicGeometry.RingedSite.HomGeneral.IsLocallyRinged`: the cartesian units-square condition
  of Stacks 04HA, at those universes.
* `AlgebraicGeometry.RingedSite.Hom.toHomGeneral`: the embedding of the existing notion.

## Main results

* `IsMorphismOfSites.preservesFiniteLimits_sheafPullback`: the canonical inverse image of a
  morphism of sites is left exact, at independent universes.
* `AlgebraicGeometry.RingedSite.HomGeneral.isLocallyRinged_iff_existsUnique`: the cartesian
  units square has a unique top arrow.
* `AlgebraicGeometry.RingedSite.HomGeneral.exists_associatedRingedToposHom`: a morphism of
  ringed sites at independent universes induces a morphism of ringed topoi whose underlying
  morphism of topoi and whose structure map on underlying sheaves of sets are the given ones.
* `CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites`: on a small site the
  small-site condition gives the unrestricted one, which is what makes
  `AlgebraicGeometry.RingedSite.Hom.toHomGeneral` available.

## Implementation notes

**This is a widening, not a second notion.**  `HomGeneral` duplicates `Hom` on the range where
`Hom` is defined, and `Hom.toHomGeneral` together with `Hom.toHomGeneral_u` and
`Hom.toHomGeneral_fsharp` exhibits every morphism of ringed sites as a `HomGeneral` with the same
underlying functor and the same structure map.  The right fix is to widen the universes of `Hom`
itself in `StacksFrontier/CategoryTheory/Sites/Modules/RingedSite.lean`; `HomGeneral` exists because
that file's interface may not change, so the generalisation is introduced additively here and
nothing that already exists is touched.  Once `Hom` is widened, `HomGeneral` is to be deleted and
its uses renamed.

The inverse image is *canonical* and not a choice.  `IsMorphismOfSites` asserts the existence of
a left exact left adjoint of the direct image; that existence is exactly
`CategoryTheory.Functor.IsRightAdjoint` for the direct image
(`IsMorphismOfSites.isRightAdjoint_sheafPushforwardContinuous`), which is a `Prop`, so Mathlib's
`CategoryTheory.Functor.sheafPullback` — the left adjoint extracted from it — does not depend on
which proof is supplied, and `IsMorphismOfSites.preservesFiniteLimits_sheafPullback` transfers
left exactness to it by uniqueness of left adjoints.  So `HomGeneral.fSharpSet` and
`HomGeneral.IsLocallyRinged` are stated with no `Classical.choose` anywhere in them, unlike
`AlgebraicGeometry.RingedSite.Hom.IsLocallyRinged`, which is defined through a chosen associated
morphism of ringed topoi.

`HomGeneral.IsLocallyRinged` is therefore the cartesian units square *itself*, written with the
canonical inverse image, rather than `AlgebraicGeometry.RingedToposHom.IsLocallyRinged` of an
associated morphism of ringed topoi.  The two are the same square:
`HomGeneral.exists_associatedRingedToposHom` produces a morphism of ringed topoi whose underlying
morphism of topoi is `HomGeneral.toposHom` on the nose and whose set-level structure map is
`HomGeneral.fSharpSet`, and the predicate mentions nothing else about it.  An `Iff` between the
two is not stated: `AlgebraicGeometry.RingedSite.Hom.IsLocallyRinged` quantifies over a
`Classical.choose` of that existential, and relating the two propositions means transporting the
square along an equation between the two `AlgebraicGeometry.MorphismOfTopoi` values, which is
work with no mathematical content.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe w v₁ u₁ v₂ u₂ uX vX uY vY u

section MorphismOfSitesGeneral

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}

/-- The direct image of a morphism of sites on sheaves of sets is a right adjoint.  This is the
existence clause of `IsMorphismOfSites` read as `CategoryTheory.Functor.IsRightAdjoint`; being a
`Prop`, it pins Mathlib's `CategoryTheory.Functor.sheafPullback` without any choice. -/
theorem IsMorphismOfSites.isRightAdjoint_sheafPushforwardContinuous
    (h : IsMorphismOfSites.{w} F J K) :
    (F.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint := by
  obtain ⟨L, hL, -⟩ := h.hasExactLeftAdjoint
  exact ⟨L, hL⟩

/-- The canonical inverse image of a morphism of sites is left exact, at independent universes:
any left exact left adjoint of the direct image is isomorphic to it, by uniqueness of left
adjoints. -/
theorem IsMorphismOfSites.preservesFiniteLimits_sheafPullback
    (h : IsMorphismOfSites.{w} F J K) :
    haveI := h.isRightAdjoint_sheafPushforwardContinuous
    PreservesFiniteLimits (F.sheafPullback (Type w) J K) := by
  have := h.isRightAdjoint_sheafPushforwardContinuous
  obtain ⟨L, ⟨adj⟩, hL⟩ := h.hasExactLeftAdjoint
  have := hL
  exact preservesFiniteLimits_of_natIso
    (Adjunction.leftAdjointUniq adj (F.sheafAdjunctionContinuous (Type w) J K))

/-- **Stacks 00XC** at independent universes.  A morphism of sites `f : D → C`, given by a
functor `F : C ⥤ D` in the opposite direction whose direct image on sheaves of sets has a left
exact left adjoint, induces a morphism of topoi `Sh(D) → Sh(C)`.

This is `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi` with the hypothesis that the
two sites be small removed; the pushforward is the same canonical direct image, so a construction
stated for the one applies verbatim to the other. -/
@[sga "4 IV 4.9.1"]
noncomputable def IsMorphismOfSites.morphismOfTopoi (h : IsMorphismOfSites.{w} F J K) :
    MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)) :=
  haveI := h.isRightAdjoint_sheafPushforwardContinuous
  { pushforward := F.sheafPushforwardContinuous (Type w) J K
    inverseImage := F.sheafPullback (Type w) J K
    adj := F.sheafAdjunctionContinuous (Type w) J K
    preservesFiniteLimits := h.preservesFiniteLimits_sheafPullback }

/-- The direct image of the induced morphism of topoi is the canonical direct image. -/
@[simp]
theorem IsMorphismOfSites.morphismOfTopoi_pushforward (h : IsMorphismOfSites.{w} F J K) :
    h.morphismOfTopoi.pushforward = F.sheafPushforwardContinuous (Type w) J K := rfl

/-- The inverse image of the induced morphism of topoi is the canonical inverse image. -/
@[simp]
theorem IsMorphismOfSites.morphismOfTopoi_inverseImage (h : IsMorphismOfSites.{w} F J K) :
    haveI := h.isRightAdjoint_sheafPushforwardContinuous
    h.morphismOfTopoi.inverseImage = F.sheafPullback (Type w) J K := rfl

/-- On a site whose objects and morphisms share a universe, the small-site condition of
Stacks 00X1 gives the unrestricted one at that universe: the chosen sheaf pullback is itself a
left exact left adjoint of the direct image. -/
theorem CategoryTheory.Functor.IsMorphismOfSites.toIsMorphismOfSites
    {C' : Type w} [SmallCategory C'] {D' : Type w} [SmallCategory D'] {F' : C' ⥤ D'}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    (h : F'.IsMorphismOfSites J' K') : _root_.IsMorphismOfSites.{w} F' J' K' :=
  have := h.isContinuous
  { __ := h.isContinuous
    hasExactLeftAdjoint :=
      ⟨F'.sheafPullback (Type w) J' K', ⟨F'.sheafAdjunctionContinuous (Type w) J' K'⟩,
        h.preservesFiniteLimits⟩ }

end MorphismOfSitesGeneral

namespace AlgebraicGeometry

namespace RingedSite

/-- A morphism of ringed sites, with the object and morphism universes of the source independent
of those of the target.  The functor `u : Y.C ⥤ X.C` represents the underlying morphism of sites
`X ⟶ Y`, and `fsharp` is its structure map in direct-image form `O_Y ⟶ f_* O_X`.

The universe of the sheaves of sets in the site condition is the universe of the sections of the
two structure sheaves: that is the universe at which the underlying topos of a ringed topos is
declared, so it is the one in which the units square of Stacks 04HA can be read. -/
structure HomGeneral.{w', uX', vX', uY', vY'}
    (X : RingedSite.{uX', vX', w'}) (Y : RingedSite.{uY', vY', w'}) where
  /-- The functor, in the direction opposite to the represented morphism of sites. -/
  u : Y.C ⥤ X.C
  /-- The assertion that `u` defines a morphism of sites. -/
  isMorphismOfSites : IsMorphismOfSites.{w'} u Y.J X.J
  /-- The structure map `O_Y ⟶ f_* O_X`. -/
  fsharp :
    letI : u.IsContinuous Y.J X.J := isMorphismOfSites.toIsContinuous
    Y.O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w'} Y.J X.J).obj X.O

namespace HomGeneral

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The functor underlying a morphism of ringed sites is continuous. -/
instance isContinuous (f : HomGeneral X Y) : f.u.IsContinuous Y.J X.J :=
  f.isMorphismOfSites.toIsContinuous

/-- The morphism of topoi `Sh(X) ⟶ Sh(Y)` underlying a morphism of ringed sites, by
Stacks 00XC. -/
noncomputable abbrev toposHom (f : HomGeneral X Y) :
    MorphismOfTopoi (Sheaf X.J (Type w)) (Sheaf Y.J (Type w)) :=
  f.isMorphismOfSites.morphismOfTopoi

/-- The inverse image `f⁻¹ : Sh(Y) ⥤ Sh(X)` on sheaves of sets. -/
noncomputable abbrev inverseImage (f : HomGeneral X Y) :
    Sheaf Y.J (Type w) ⥤ Sheaf X.J (Type w) :=
  f.toposHom.inverseImage

/-- The direct image `f_* : Sh(X) ⥤ Sh(Y)` on sheaves of sets is the canonical one. -/
@[simp]
theorem toposHom_pushforward (f : HomGeneral X Y) :
    f.toposHom.pushforward = f.u.sheafPushforwardContinuous (Type w) Y.J X.J := rfl

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]

/-- The structure map on underlying sheaves of sets, in inverse-image form `f⁻¹ O_Y ⟶ O_X`. -/
noncomputable abbrev fSharpSet (f : HomGeneral X Y) :
    f.inverseImage.obj ((sheafCompose Y.J (forget CommRingCat.{w})).obj Y.O) ⟶
      (sheafCompose X.J (forget CommRingCat.{w})).obj X.O :=
  (f.toposHom.adj.homEquiv _ _).symm
    ((sheafCompose Y.J (forget CommRingCat.{w})).map f.fsharp)

/-- **Stacks 04HA** at independent universes.  A morphism of ringed sites is *locally ringed*
when its square

```
  f⁻¹(O_Y^*) ---> O_X^*
      |             |
      v             v
  f⁻¹(O_Y)  ---> O_X
```

of units subsheaves is cartesian, the bottom arrow being the structure map on underlying sheaves
of sets.  The top arrow is not part of the data: the inclusion of units is a monomorphism, so an
arrow making the square commute is unique if it exists, which is
`AlgebraicGeometry.RingedSite.HomGeneral.isLocallyRinged_iff_existsUnique`. -/
@[stacks 04HA "morphisms of locally ringed sites, independent universes"]
abbrev IsLocallyRinged (f : HomGeneral X Y) : Prop :=
  ∃ t : f.inverseImage.obj (RingedTopos.units (toRingedTopos Y)) ⟶
      RingedTopos.units (toRingedTopos X),
    IsPullback t (f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)))
      (RingedTopos.unitsι (toRingedTopos X)) f.fSharpSet

/-- A map into the units subsheaf is determined by its composite with the inclusion. -/
theorem unitsMap_unique (f : HomGeneral X Y)
    (t₁ t₂ : f.inverseImage.obj (RingedTopos.units (toRingedTopos Y)) ⟶
      RingedTopos.units (toRingedTopos X))
    (h₁ : t₁ ≫ RingedTopos.unitsι (toRingedTopos X) =
      f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) ≫ f.fSharpSet)
    (h₂ : t₂ ≫ RingedTopos.unitsι (toRingedTopos X) =
      f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)) ≫ f.fSharpSet) :
    t₁ = t₂ :=
  (cancel_mono (RingedTopos.unitsι (toRingedTopos X))).mp (h₁.trans h₂.symm)

/-- The cartesian units square has a unique top arrow. -/
theorem isLocallyRinged_iff_existsUnique (f : HomGeneral X Y) :
    IsLocallyRinged f ↔
      ∃! t : f.inverseImage.obj (RingedTopos.units (toRingedTopos Y)) ⟶
          RingedTopos.units (toRingedTopos X),
        IsPullback t (f.inverseImage.map (RingedTopos.unitsι (toRingedTopos Y)))
          (RingedTopos.unitsι (toRingedTopos X)) f.fSharpSet := by
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, ht, fun s hs => unitsMap_unique f s t hs.w ht.w⟩
  · rintro ⟨t, ht, -⟩; exact ⟨t, ht⟩

end HomGeneral

section Associated

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})]

/-- **Stacks 04HA** at independent universes.  A morphism of ringed sites induces a morphism of
ringed topoi whose underlying morphism of topoi is `HomGeneral.toposHom` and whose structure map
on underlying sheaves of sets is `HomGeneral.fSharpSet`.

As in `AlgebraicGeometry.RingedSite.Hom.exists_associatedRingedToposHom`, the statement is
existential rather than a construction: the structure map of a morphism of ringed sites lands in
the *restriction* `u^s O_X` along the site functor, whereas a morphism of ringed topoi needs it
in the direct image `f_* O_X` along the induced morphism of topoi, and those agree only up to
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which is the identity on underlying
sheaves of sets but not the identity map of sheaves of commutative rings. -/
@[stacks 04HA "associated ringed-topos morphism, independent universes",
  sga "4 IV 13.3.1" "special case"]
theorem HomGeneral.exists_associatedRingedToposHom (f : HomGeneral X Y) :
    ∃ g : RingedToposHom (toRingedTopos X) (toRingedTopos Y),
      (g.toToposHom = f.toposHom) ∧ HEq (RingedToposHom.fSharpSet g) f.fSharpSet := by
  let φ := f.toposHom
  let e : (pushforwardCommRingFunctor φ).obj X.O ≅
      (f.u.sheafPushforwardContinuous CommRingCat.{w} Y.J X.J).obj X.O :=
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
      ((congrArg (fun k =>
        (RingedTopos.forgetRing (toRingedTopos Y)).map f.fsharp ≫ k)
          he).trans (Category.comp_id _))
  rw [RingedToposHom.fSharpSet, HomGeneral.fSharpSet, hmap]

end Associated

namespace Hom

variable {X Y : RingedSite.{u, u, u}}

/-- Every morphism of ringed sites is a morphism of ringed sites at independent universes, with
the same underlying functor and the same structure map. -/
def toHomGeneral (f : Hom X Y) : HomGeneral X Y where
  u := f.u
  isMorphismOfSites := f.isMorphismOfSites.toIsMorphismOfSites
  fsharp := f.fsharp

/-- The widening leaves the underlying functor unchanged. -/
@[simp]
theorem toHomGeneral_u (f : Hom X Y) : f.toHomGeneral.u = f.u := rfl

/-- The widening leaves the structure map unchanged. -/
@[simp]
theorem toHomGeneral_fsharp (f : Hom X Y) : f.toHomGeneral.fsharp = f.fsharp := rfl

/-- The widening leaves the direct image on sheaves of sets unchanged. -/
@[simp]
theorem toHomGeneral_toposHom_pushforward (f : Hom X Y) :
    f.toHomGeneral.toposHom.pushforward =
      f.isMorphismOfSites.morphismOfTopoi.pushforward := rfl

/-- The widening leaves the inverse image on sheaves of sets unchanged. -/
@[simp]
theorem toHomGeneral_toposHom_inverseImage (f : Hom X Y) :
    f.toHomGeneral.toposHom.inverseImage =
      f.isMorphismOfSites.morphismOfTopoi.inverseImage := rfl

end Hom

end RingedSite

end AlgebraicGeometry

end
