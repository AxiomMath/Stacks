module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a 2-isomorphism of ringed topoi to a localization

Let `f, g : (Sh(C), O) ⟶ (Sh(D), O')` be morphisms of ringed topoi, let `t : f_* ≅ g_*` be a
2-isomorphism between them and let `G` be a sheaf of sets on `D`. Localizing the target at `G`
and the source at the inverse image of `G` turns `f` and `g` into the morphisms `f'` and `g'` of
Stacks 04IF, and `t` restricts to a comparison of *their* direct images, compatible with the
restrictions of the two structure maps.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.localized`: the **restriction of a 2-isomorphism along
  a localization of both ringed topoi**, as an isomorphism
  `j_{f⁻¹G}⁻¹ ⋙ f'_* ≅ j_{g⁻¹G}⁻¹ ⋙ g'_*` of functors `Sh(C) ⥤ Sh(D)/G`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.localized_conjugate`: read through Stacks 04IF's
  identity `f'_* j_F⁻¹ = j_G⁻¹ f_*`, the restriction is `t` whiskered by `j_G⁻¹`; this is what
  says that `localized` is the restriction of `t` and nothing else.
* `AlgebraicGeometry.RingedToposHom.TwoIso.localized_commutes`: the structure-map half, i.e. the
  `commutes` field of `t` restricted to the localization.
* `AlgebraicGeometry.RingedToposHom.TwoIso.localized_refl`, `.localized_symm` and
  `.localized_trans`: restriction respects the calculus of 2-isomorphisms, which is what lets a
  chartwise family of restrictions satisfy a cocycle condition.
* `AlgebraicGeometry.RingedToposHom.TwoIso.eq_of_forall_localized_eq`: **separatedness**, reduced
  to joint faithfulness of the localization inverse images of the covering family.

## Implementation notes

**Why the restriction is not a `TwoIso`.** The localized morphism
`AlgebraicGeometry.RingedToposHom.localized` of Stacks 04IF localizes the *source* at `f⁻¹G`,
the inverse image of `G` under the morphism being localized:

```
f.localized G : RingedToposHom (X.localizedRingedTopos (f⁻¹G)) (Y.localizedRingedTopos G) .
```

So `f.localized G` and `g.localized G` are morphisms out of *different* ringed topoi, and
`TwoIso (f.localized G) (g.localized G)` is not a type — Lean rejects it with an application
type mismatch at the second argument. This is not an artefact of the formalization: a
2-isomorphism `t : f_* ≅ g_*` conjugates to an isomorphism `g⁻¹ ≅ f⁻¹`, hence to an
*isomorphism* `f⁻¹G ≅ g⁻¹G` of sheaves, never an equality, and `localizedRingedTopos` of two
isomorphic sheaves are two different ringed topoi with equivalent, not equal, sites.

Identifying the two localizations along that isomorphism is `Stacks 04J4`'s relocalization, and
would give a bona fide `TwoIso` between `f.localized G` and the composite of `g.localized G`
with it. That is unavailable here for a universe reason, not a mathematical one:
`AlgebraicGeometry.RingedTopos.relocalizationMorphism` factors through
`AlgebraicGeometry.RingedTopos.toStacks04H9` and so exists only for a `RingedTopos.{u, u, u}`,
whereas Stacks 04I7's small étale ringed topoi are `RingedTopos.{u, u + 1, u}` — exactly the
generality at which `localized` was made available and `relocalizationMorphism` was not. The
blocking piece is `Stacks.Sheaves.LocalizedRingedTopos.elementPostcomp` together with its
continuity and cocontinuity, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardRightExact.lean`, stated at a single
universe.

**What is restricted instead.** Both `j_{f⁻¹G}⁻¹ ⋙ f'_*` and `j_{g⁻¹G}⁻¹ ⋙ g'_*` are functors
`Sh(C) ⥤ Sh(D)/G`, so they *can* be compared, and Stacks 04IF's identity
`AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso` identifies each with
`f_* ⋙ j_G⁻¹` and `g_* ⋙ j_G⁻¹`. The restriction of `t` is `t` whiskered by `j_G⁻¹`, read
through those two identifications; `localized_conjugate` is that statement, and it is what makes
`localized` a restriction operation rather than an arbitrary comparison. Both sides mention the
localized morphisms of Stacks 04IF, so this is the restriction of the 2-isomorphism *along a
localization of both ringed topoi*, as the source asks; what it is not is a `TwoIso`, for the
reason above.

The structure-map half costs nothing: `t.commutes` is an equation between morphisms of sheaves on
`D`, and `j_G⁻¹` is a functor, so applying it gives `localized_commutes` by functoriality alone.
Tying that to the structure map of `f.localized G` itself would need the compatibility of
Stacks 04IF's square with the three structure maps, which this repository does not carry; see the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`,
where the same equation appears as the hypothesis `hIF`.

**Separatedness, and what gluing still needs.** A 2-isomorphism is its isomorphism of direct
images, and by `localized_conjugate` its restrictions to a family `G i` determine the
`j_{G i}⁻¹`-images of every component of that isomorphism. So separatedness is exactly joint
faithfulness of the functors `j_{G i}⁻¹`, and `eq_of_forall_localized_eq` takes that as the
hypothesis `CategoryTheory.JointlyFaithful`. The hypothesis is not vacuous: its small étale
analogue, joint faithfulness of the inverse images along a jointly surjective finite family, is
`AlgebraicGeometry.jointlyFaithful_smallEtaleSetPullback` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/JointlySurjectiveFamilyFaithful.lean`. What is
missing is the bridge: that the localization of a small étale ringed topos at the sheaf of an
étale neighbourhood is the small étale ringed topos of that neighbourhood, with `j⁻¹` the small
étale inverse image.

**Gluing is not provided, and is not assembly.** Going the other way — from a compatible family
of restrictions to a global 2-isomorphism — is not reachable from the sheaf-gluing machinery of
`StacksFrontier/CategoryTheory/Sites/Glueing/`. `Stacks.SheafMapGluing.maps_of_sheaves_glue` and
`Stacks.SheafMapGluing.iso_of_sheaves_glue` glue a `Stacks.SheafMapGluing.RestrictedHom` between
two *fixed* sheaves over a covering of an object of the site; the thing to be glued here is an
isomorphism of *functors* on the whole topos, so each component could be glued separately but
naturality in the sheaf argument would remain, and the covering is indexed by sheaves on `D`
rather than by objects of `D`'s site. Nothing in this repository connects the two; that is the
descent recorded as missing in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineCase` and
`...RecoveringMorphisms.ExistenceClause`.

**Universes.** As for `localized`: the morphisms of the two sites and the sections of their
structure sheaves lie in one universe `v`, their objects in an independent universe `u`, and both
sites are essentially `v`-small. At `RingedTopos.{u, u + 1, u}` the smallness instances are
discharged by `AlgebraicGeometry.SmallEtale.essentiallySmall`, so `localized` applies verbatim to
a 2-isomorphism of the morphisms of small étale ringed topoi of two morphisms of schemes, which
is the generality Stacks 04I7 needs.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C]
  [X.J.HasSheafCompose (forget RingCat.{v})]
  [Y.J.HasSheafCompose (forget RingCat.{v})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]

/-- **The restriction of a 2-isomorphism of ringed topoi along a localization of both ringed
topoi.** Let `t : f_* ≅ g_*` be a 2-isomorphism of morphisms of ringed topoi
`f, g : (Sh(C), O) ⟶ (Sh(D), O')` and let `G` be a sheaf of sets on `D`. Localizing the target at
`G` and each source at its own inverse image of `G` gives the two morphisms `f'` and `g'` of
Stacks 04IF, and `t` restricts to a comparison

```
  j_{f⁻¹G}⁻¹ ⋙ f'_*  ≅  j_{g⁻¹G}⁻¹ ⋙ g'_*
```

of their direct images, read on sheaves pulled back from `Sh(C)`. It is `t` whiskered by `j_G⁻¹`
conjugated by the two instances of Stacks 04IF's identity `f'_* j_F⁻¹ = j_G⁻¹ f_*`; see
`TwoIso.localized_conjugate`.

The two localized morphisms have *different* sources — `f.localized G` starts at the
localization of `X` at `f⁻¹G` — so `TwoIso (f.localized G) (g.localized G)` is not a type; the
implementation notes of this file explain why, and why the identification needed to make it one
is unavailable at these universes. -/
noncomputable def TwoIso.localized {f g : RingedToposHom X Y} (t : TwoIso f g) (G : Y.Topos) :
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
        (f.localized G).toToposHom.pushforward ≅
      (X.localizationMorphism (g.toToposHom.inverseImage.obj G)).toToposHom.inverseImage ⋙
        (g.localized G).toToposHom.pushforward :=
  f.localizationCompPushforwardIso G ≪≫
    Functor.isoWhiskerRight t.e (Y.localizationMorphism G).toToposHom.inverseImage ≪≫
    (g.localizationCompPushforwardIso G).symm

namespace TwoIso

/-- The components of the restriction of a 2-isomorphism: the component of `t` at a sheaf,
restricted to the localization of the target and conjugated by Stacks 04IF's identity at the
source and at the target. -/
theorem localized_hom_app {f g : RingedToposHom X Y} (t : TwoIso f g) (G : Y.Topos)
    (H : X.Topos) :
    (t.localized G).hom.app H =
      (f.localizationCompPushforwardIso G).hom.app H ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map (t.e.hom.app H) ≫
        (g.localizationCompPushforwardIso G).inv.app H :=
  rfl

/-- The components of the inverse of the restriction of a 2-isomorphism. -/
theorem localized_inv_app {f g : RingedToposHom X Y} (t : TwoIso f g) (G : Y.Topos)
    (H : X.Topos) :
    (t.localized G).inv.app H =
      (g.localizationCompPushforwardIso G).hom.app H ≫
        (Y.localizationMorphism G).toToposHom.inverseImage.map (t.e.inv.app H) ≫
        (f.localizationCompPushforwardIso G).inv.app H := by
  change ((g.localizationCompPushforwardIso G).hom.app H ≫
      (Y.localizationMorphism G).toToposHom.inverseImage.map (t.e.inv.app H)) ≫
    (f.localizationCompPushforwardIso G).inv.app H = _
  rw [Category.assoc]

/-- **The restriction of a 2-isomorphism is the 2-isomorphism restricted.** Conjugating
`TwoIso.localized` back along the two instances of Stacks 04IF's identity
`f'_* j_F⁻¹ = j_G⁻¹ f_*` leaves `t` whiskered by the inverse image of the localization morphism
of the target. This is the statement that `localized` carries no information beyond `t`. -/
theorem localized_conjugate {f g : RingedToposHom X Y} (t : TwoIso f g) (G : Y.Topos) :
    (f.localizationCompPushforwardIso G).inv ≫ (t.localized G).hom ≫
        (g.localizationCompPushforwardIso G).hom =
      Functor.whiskerRight t.e.hom (Y.localizationMorphism G).toToposHom.inverseImage := by
  refine NatTrans.ext (funext fun H => ?_)
  change (f.localizationCompPushforwardIso G).inv.app H ≫
      (t.localized G).hom.app H ≫ (g.localizationCompPushforwardIso G).hom.app H =
    (Y.localizationMorphism G).toToposHom.inverseImage.map (t.e.hom.app H)
  rw [localized_hom_app]
  simp

omit [EssentiallySmall.{v} X.C] in
/-- **The structure-map half of the restriction.** The compatibility of `t` with the two
structure maps, restricted to the localization of the target: `t.commutes` is an equation of
morphisms of sheaves on `D`, so applying the inverse image of the localization morphism to it is
all there is to do.

This is the compatibility in the form the restricted comparison of `localized_conjugate` has it.
Reading it against the structure map of `f.localized G` itself needs the compatibility of
Stacks 04IF's square with the three structure maps, which this repository does not carry. -/
theorem localized_commutes {f g : RingedToposHom X Y} (t : TwoIso f g) (G : Y.Topos) :
    (Y.localizationMorphism G).toToposHom.inverseImage.map (forgetFSharp f) ≫
        (Functor.whiskerRight t.e.hom
          (Y.localizationMorphism G).toToposHom.inverseImage).app (X.forgetRing.obj X.O) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (forgetFSharp g) :=
  ((Y.localizationMorphism G).toToposHom.inverseImage.map_comp _ _).symm.trans
    (congrArg (Y.localizationMorphism G).toToposHom.inverseImage.map t.commutes)

/-- Restriction takes the identity 2-isomorphism to the identity. -/
theorem localized_refl (f : RingedToposHom X Y) (G : Y.Topos) :
    (TwoIso.refl f).localized G = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun H => ?_))
  rw [localized_hom_app]
  simp [TwoIso.refl]

/-- Restriction takes a vertical composite of 2-isomorphisms to the composite of the
restrictions: the two middle copies of Stacks 04IF's identity cancel. -/
theorem localized_trans {p q r : RingedToposHom X Y} (s : TwoIso p q) (s' : TwoIso q r)
    (G : Y.Topos) :
    (s.trans s').localized G = s.localized G ≪≫ s'.localized G := by
  refine Iso.ext (NatTrans.ext (funext fun H => ?_))
  rw [Iso.trans_hom, NatTrans.comp_app, localized_hom_app, localized_hom_app, localized_hom_app]
  simp [TwoIso.trans]

/-- Restriction takes the inverse of a 2-isomorphism to the inverse of the restriction. -/
theorem localized_symm {p q : RingedToposHom X Y} (s : TwoIso p q) (G : Y.Topos) :
    s.symm.localized G = (s.localized G).symm := by
  refine Iso.ext (NatTrans.ext (funext fun H => ?_))
  rw [localized_hom_app, Iso.symm_hom, localized_inv_app]
  rfl

/-- **Separatedness of 2-isomorphisms of ringed topoi under restriction.** Two 2-isomorphisms
between the same pair of morphisms of ringed topoi whose restrictions to a family `G i` of
sheaves on the target agree are equal, provided the inverse images of the localization morphisms
of that family are jointly faithful.

A 2-isomorphism is its isomorphism of direct images, and by `localized_conjugate` the
restriction to `G i` recovers the `j_{G i}⁻¹`-image of each of its components; so this is the
whole of separatedness, with the local nature of the covering isolated in the hypothesis. The
hypothesis is the sheaf-theoretic statement that the family covers, and holds in the small étale
setting for a jointly surjective family — see the implementation notes of this file. -/
theorem eq_of_forall_localized_eq {f g : RingedToposHom X Y} {ι : Type*} (Gi : ι → Y.Topos)
    (hfaithful : JointlyFaithful
      (fun i => (Y.localizationMorphism (Gi i)).toToposHom.inverseImage))
    {t t' : TwoIso f g} (h : ∀ i, t.localized (Gi i) = t'.localized (Gi i)) :
    t = t' := by
  suffices he : t.e = t'.e by
    cases t
    cases t'
    cases he
    rfl
  refine Iso.ext (NatTrans.ext (funext fun H => ?_))
  refine hfaithful.map_injective fun i => ?_
  have hc := (localized_conjugate t (Gi i)).symm.trans
    ((congrArg (fun z : _ ≅ _ => (f.localizationCompPushforwardIso (Gi i)).inv ≫ z.hom ≫
        (g.localizationCompPushforwardIso (Gi i)).hom) (h i)).trans
      (localized_conjugate t' (Gi i)))
  exact congrFun (congrArg NatTrans.app hc) H

end TwoIso

end AlgebraicGeometry.RingedToposHom

end
