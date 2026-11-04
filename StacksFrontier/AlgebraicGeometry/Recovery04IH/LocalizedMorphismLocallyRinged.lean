module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedMateInvertible
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Localization
import StacksCore.Tactic.StacksAttribute

/-!
# The localization of a morphism of locally ringed sites

Let `(f, f^#) : (C, O) ⟶ (D, O')` be a morphism of ringed sites with underlying continuous
functor `u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Its localization
`(f', (f')^#) : (C/U, O_U) ⟶ (D/V, O'_V)` (Stacks 04J0) is
`AlgebraicGeometry.RingedSite.Hom.localized`. If `(f, f^#)` is a morphism of locally ringed sites,
then so is `(f', (f')^#)`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isLocallyRinged_of_isPullback` and
  `AlgebraicGeometry.RingedSite.Hom.exists_isPullback_of_isLocallyRinged`: the locality condition
  of Stacks 04HA for a morphism of ringed sites, read as a cartesian square written with the
  canonical inverse image and `AlgebraicGeometry.RingedSite.Hom.fSharpSet`.
* `AlgebraicGeometry.RingedSite.Hom.isPullback_localizedUnitsSquare`: if the units square of `f`
  is cartesian, so is the units square of the localized morphism.
* `AlgebraicGeometry.RingedSite.Hom.isLocallyRinged_localized`: the localization of a locally
  ringed morphism of ringed sites is a locally ringed morphism.
* `AlgebraicGeometry.RingedSite.Hom.localized_isLocallyRinged_sites`: for a morphism of locally
  ringed sites, the two localized sites are locally ringed and the localized morphism is a locally
  ringed morphism.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace RingedSite

/-- The units subsheaf of a localized ringed site is the restriction along the slice projection
of the units subsheaf. -/
theorem units_over (Z : RingedSite.{u, u, u}) (U : Z.C) :
    RingedTopos.units (toRingedTopos (Z.over U)) =
      (Z.J.overPullback (Type u) U).obj (RingedTopos.units (toRingedTopos Z)) := rfl

/-- The inclusion of the units subsheaf of a localized ringed site is the restriction along the
slice projection of the inclusion. -/
theorem unitsι_over (Z : RingedSite.{u, u, u}) (U : Z.C) :
    RingedTopos.unitsι (toRingedTopos (Z.over U)) =
      (Z.J.overPullback (Type u) U).map (RingedTopos.unitsι (toRingedTopos Z)) := rfl

end RingedSite

section Bridge

variable {X Y : RingedSite.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]

/-- The cartesian units square of Stacks 04HA depends on a morphism of ringed topoi only through
its underlying morphism of topoi and its structure map on underlying sheaves of sets: given a
cartesian square for those, the morphism is locally ringed. -/
theorem RingedToposHom.isLocallyRinged_of_eq
    (φ : MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)))
    (fs : φ.inverseImage.obj ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ⟶
      (sheafCompose X.J (forget CommRingCat.{u})).obj X.O)
    (t : φ.inverseImage.obj (RingedTopos.units (RingedSite.toRingedTopos Y)) ⟶
      RingedTopos.units (RingedSite.toRingedTopos X))
    (h : IsPullback t (φ.inverseImage.map (RingedTopos.unitsι (RingedSite.toRingedTopos Y)))
      (RingedTopos.unitsι (RingedSite.toRingedTopos X)) fs)
    (g : RingedToposHom (RingedSite.toRingedTopos X) (RingedSite.toRingedTopos Y))
    (hg : g.toToposHom = φ) (hfs : HEq (RingedToposHom.fSharpSet g) fs) :
    RingedToposHom.IsLocallyRinged g := by
  subst hg
  exact ⟨t, (eq_of_heq hfs).symm ▸ h⟩

/-- The converse reading of `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_eq`: a locally
ringed morphism of ringed topoi has a cartesian units square for any morphism of topoi and any
set-level structure map it is presented by. -/
theorem RingedToposHom.exists_isPullback_of_eq
    (φ : MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)))
    (fs : φ.inverseImage.obj ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ⟶
      (sheafCompose X.J (forget CommRingCat.{u})).obj X.O)
    (g : RingedToposHom (RingedSite.toRingedTopos X) (RingedSite.toRingedTopos Y))
    (hg : g.toToposHom = φ) (hfs : HEq (RingedToposHom.fSharpSet g) fs)
    (hloc : RingedToposHom.IsLocallyRinged g) :
    ∃ t : φ.inverseImage.obj (RingedTopos.units (RingedSite.toRingedTopos Y)) ⟶
      RingedTopos.units (RingedSite.toRingedTopos X),
      IsPullback t (φ.inverseImage.map (RingedTopos.unitsι (RingedSite.toRingedTopos Y)))
        (RingedTopos.unitsι (RingedSite.toRingedTopos X)) fs := by
  subst hg
  obtain ⟨t, ht⟩ := hloc
  exact ⟨t, (eq_of_heq hfs) ▸ ht⟩

/-- A morphism of ringed sites is locally ringed (Stacks 04HA) as soon as its units square,
written with the canonical inverse image and any `fs` equal to
`AlgebraicGeometry.RingedSite.Hom.fSharpSet`, is cartesian. -/
theorem RingedSite.Hom.isLocallyRinged_of_isPullback (f : RingedSite.Hom X Y)
    (fs : (f.u.sheafPullback (Type u) Y.J X.J).obj
        ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ⟶
      (sheafCompose X.J (forget CommRingCat.{u})).obj X.O)
    (hfs : RingedSite.Hom.fSharpSet f = fs)
    (t : (f.u.sheafPullback (Type u) Y.J X.J).obj
        (RingedTopos.units (RingedSite.toRingedTopos Y)) ⟶
      RingedTopos.units (RingedSite.toRingedTopos X))
    (h : IsPullback t ((f.u.sheafPullback (Type u) Y.J X.J).map
        (RingedTopos.unitsι (RingedSite.toRingedTopos Y)))
      (RingedTopos.unitsι (RingedSite.toRingedTopos X)) fs) :
    f.IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_eq f.isMorphismOfSites.morphismOfTopoi fs t h _
    (RingedSite.Hom.associatedRingedToposHom f).2.1
    ((RingedSite.Hom.associatedRingedToposHom f).2.2.trans (heq_of_eq hfs))

/-- A locally ringed morphism of ringed sites (Stacks 04HA) has a cartesian units square, written
with the canonical inverse image and `AlgebraicGeometry.RingedSite.Hom.fSharpSet`. -/
theorem RingedSite.Hom.exists_isPullback_of_isLocallyRinged (f : RingedSite.Hom X Y)
    (hf : f.IsLocallyRinged) :
    ∃ t : (f.u.sheafPullback (Type u) Y.J X.J).obj
        (RingedTopos.units (RingedSite.toRingedTopos Y)) ⟶
      RingedTopos.units (RingedSite.toRingedTopos X),
      IsPullback t ((f.u.sheafPullback (Type u) Y.J X.J).map
          (RingedTopos.unitsι (RingedSite.toRingedTopos Y)))
        (RingedTopos.unitsι (RingedSite.toRingedTopos X)) (RingedSite.Hom.fSharpSet f) :=
  RingedToposHom.exists_isPullback_of_eq f.isMorphismOfSites.morphismOfTopoi
    (RingedSite.Hom.fSharpSet f) _
    (RingedSite.Hom.associatedRingedToposHom f).2.1
    (RingedSite.Hom.associatedRingedToposHom f).2.2 hf

end Bridge

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, u, u}}

attribute [local instance] isContinuous_overPost

variable (f : RingedSite.Hom X Y) (V : Y.C)

/-- If the units square of `f` is cartesian, then so is the units square of the localized morphism
at `V`, with both columns written as restrictions along the slice projections. -/
theorem isPullback_localizedUnitsSquare
    (t : (f.u.sheafPullback (Type u) Y.J X.J).obj
        (RingedTopos.units (toRingedTopos Y)) ⟶ RingedTopos.units (toRingedTopos X))
    (h : IsPullback t ((f.u.sheafPullback (Type u) Y.J X.J).map
        (RingedTopos.unitsι (toRingedTopos Y)))
      (RingedTopos.unitsι (toRingedTopos X)) (fSharpSet f)) :
    IsPullback
      ((SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app
          (RingedTopos.units (toRingedTopos Y)) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map t)
      (((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))).map
        ((Y.J.overPullback (Type u) V).map (RingedTopos.unitsι (toRingedTopos Y))))
      ((X.J.overPullback (Type u) (f.u.obj V)).map (RingedTopos.unitsι (toRingedTopos X)))
      ((SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app
          ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map (fSharpSet f)) := by
  have : ∀ F, IsIso ((SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app F) := fun F =>
    SliceTopos.isIso_localizedInverseImageMate_app Y.J X.J f.u V f.isMorphismOfSites F
  have hnat := (SliceTopos.localizedInverseImageMate Y.J X.J f.u V).naturality
    (RingedTopos.unitsι (toRingedTopos Y))
  simp only [Functor.comp_map] at hnat
  refine (h.map (X.J.overPullback (Type u) (f.u.obj V))).of_iso
    (asIso ((SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app
      (RingedTopos.units (toRingedTopos Y)))).symm (Iso.refl _)
    (asIso ((SliceTopos.localizedInverseImageMate Y.J X.J f.u V).app
      ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O))).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp only [Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, Category.assoc, hnat]
    simp
  · simp
  · simp

/-- The localization of a locally ringed morphism of ringed sites at an object of the target is a
locally ringed morphism. -/
theorem isLocallyRinged_localized (hf : f.IsLocallyRinged) :
    (f.localized V).IsLocallyRinged := by
  obtain ⟨t, h⟩ := f.exists_isPullback_of_isLocallyRinged hf
  exact (f.localized V).isLocallyRinged_of_isPullback _ (f.fSharpSet_localized V) _
    (f.isPullback_localizedUnitsSquare V t h)

/-- For a morphism of *locally ringed* sites `(f, f^#)` and an
object `V` of the target, the two localized sites `(C/U, O_U)` and `(D/V, O'_V)` are locally
ringed sites and the localized morphism `(f', (f')^#)` of Stacks 04J0 is a locally ringed
morphism. -/
@[stacks 04IH "part (3): the localization of a morphism of locally ringed sites"]
theorem localized_isLocallyRinged_sites (hX : RingedSite.IsLocallyRinged X)
    (hY : RingedSite.IsLocallyRinged Y) (hf : f.IsLocallyRinged) :
    RingedSite.IsLocallyRinged (X.over (f.u.obj V)) ∧
      RingedSite.IsLocallyRinged (Y.over V) ∧ (f.localized V).IsLocallyRinged :=
  ⟨RingedSite.isLocallyRinged_over X (f.u.obj V) hX,
    RingedSite.isLocallyRinged_over Y V hY, f.isLocallyRinged_localized V hf⟩

end RingedSite.Hom

end AlgebraicGeometry

end
