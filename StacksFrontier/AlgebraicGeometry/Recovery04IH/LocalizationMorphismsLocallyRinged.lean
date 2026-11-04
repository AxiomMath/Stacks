module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization
import StacksCore.Tactic.StacksAttribute

/-!
# Localization and relocalization morphisms are locally ringed

Stacks 04IH asserts that the localization of a locally ringed site is locally ringed, and that
the canonical morphisms attached to a localization — localization of a ringed site at an object,
relocalization of a ringed site along a morphism of objects, and the corresponding morphisms of
a ringed topos localized at a sheaf — are *locally ringed morphisms*, i.e. satisfy the cartesian
units-square condition `AlgebraicGeometry.RingedToposHom.IsLocallyRinged` of Stacks 04HA.

This file proves locality for the two morphisms of a ringed site and for the localization
morphism of a ringed topos; the relocalization morphism of a ringed topos is in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/ToposRelocalization.lean`.

## Main results

* `AlgebraicGeometry.RingedSite.localizationRingedToposHom_isLocallyRinged`: **Stacks 04IH (1),
  second assertion**, the localization morphism at an object of a ringed site is locally ringed.
* `AlgebraicGeometry.RingedSite.relocalizationRingedToposHom_isLocallyRinged`: **Stacks 04IH
  (2)**, the relocalization morphism of Stacks 04IY along a morphism of objects of a ringed site
  is locally ringed.
* `AlgebraicGeometry.RingedTopos.localizationMorphism_isLocallyRinged`: **Stacks 04IH (5),
  second assertion**, the localization of a ringed topos at a sheaf is locally ringed.

## Implementation notes

One observation does all three, and it replaces the units computation one would expect. For each
of these morphisms the inverse image is *restriction* along a continuous functor of sites, and
the structure sheaf of the source is the restriction of the structure sheaf of the target.
Restriction is computed objectwise and commutes with `CategoryTheory.sheafCompose` on the nose,
and the units subsheaf `AlgebraicGeometry.RingedSite.unitsSheaf` is a composite of
`sheafCompose`s; so the inverse image of the units subsheaf of the target *is* the units subsheaf
of the source, and the inverse image of its inclusion *is* the inclusion, both on the nose.
Meanwhile the structure map in inverse-image form is a comparison with restriction, hence the
identity on underlying sheaves of sets. The units square is therefore a square of identities and
is cartesian by `CategoryTheory.IsPullback.of_id_fst`. No comparison map
`f⁻¹(O_D^*) ≅ (f⁻¹O_D)^*` — the content of Stacks 04KR — is needed.

Getting from the structure map in direct-image form, which is what
`AlgebraicGeometry.RingedToposHom` stores, to the inverse-image form is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`.

The morphisms of a ringed site are taken in their two-field form,
`AlgebraicGeometry.RingedSite.localizationRingedToposHom` and `.relocalizationRingedToposHom`,
because `AlgebraicGeometry.RingedToposHom` is the structure Stacks 04HA quantifies over;
`AlgebraicGeometry.RingedSite.localizationMorphism` and `.relocalizationMorphism` are the same
two morphisms recorded in the richer four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, which is not the type the locality condition
takes.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w})

/-- The structure map of the localization morphism of a ringed site is the identity on
underlying sheaves of sets. -/
theorem fSharpSet_localizationRingedToposHom (U : X.C) :
    RingedToposHom.fSharpSet (X.localizationRingedToposHom U) =
      𝟙 ((X.localizationRingedToposHom U).toToposHom.inverseImage.obj
        ((ringedTopos X).forgetRing.obj X.O)) :=
  (RingedToposHom.fSharpInverseImage_forget_homEquiv
    (X.localizationRingedToposHom U)).symm.trans
      (X.forgetRing_localizationRingedToposHom_fSharpInverseImage U)

/-- **Stacks 04IH (1), second assertion.** The localization morphism `(j_U, j_U♯)` of a ringed
site at an object `U` is a morphism of locally ringed topoi: its structure map is the identity
on underlying sheaves of sets, and the inverse image of the units subsheaf is the units
subsheaf, so the units square is a square of identities. -/
@[stacks 04IH "(1), second assertion: the localization morphism `(j_U, j_U♯)` is a morphism of
locally ringed topoi"]
theorem localizationRingedToposHom_isLocallyRinged (U : X.C) :
    (X.localizationRingedToposHom U).IsLocallyRinged :=
  ⟨𝟙 _, X.fSharpSet_localizationRingedToposHom U ▸ .of_id_fst⟩

variable {U V : X.C}

/-- The structure map of the relocalization morphism of a ringed site is the identity on
underlying sheaves of sets: it is a comparison of an inverse image with a restriction followed
by a change of slice, and both are objectwise the identity. -/
theorem fSharpSet_relocalizationRingedToposHom (f : V ⟶ U) :
    RingedToposHom.fSharpSet (X.relocalizationRingedToposHom f) =
      𝟙 ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.obj
        ((ringedTopos (X.over U)).forgetRing.obj (X.over U).O)) :=
  (RingedToposHom.fSharpInverseImage_forget_homEquiv
    (X.relocalizationRingedToposHom f)).symm.trans
      (X.forgetRing_relocalizationRingedToposHom_fSharpInverseImage f)

/-- **Stacks 04IH (2).** The morphism `(j, j♯) : (Sh(C/V), O_V) → (Sh(C/U), O_U)` of Stacks 04IY,
the relocalization of a ringed site along a morphism `f : V ⟶ U` of its underlying category, is
a morphism of locally ringed topoi. As for the localization morphism, the units square is a
square of identities. -/
@[stacks 04IH "(2): the morphism `(j, j♯)` of 04IY is a morphism of locally ringed topoi"]
theorem relocalizationRingedToposHom_isLocallyRinged (f : V ⟶ U) :
    (X.relocalizationRingedToposHom f).IsLocallyRinged :=
  ⟨𝟙 _, X.fSharpSet_relocalizationRingedToposHom f ▸ .of_id_fst⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- The structure map of the localization of a ringed topos at a sheaf is the identity on
underlying sheaves of sets. -/
theorem fSharpSet_localizationMorphism :
    RingedToposHom.fSharpSet (localizationMorphism X F) =
      𝟙 ((localizationMorphism X F).toToposHom.inverseImage.obj (X.forgetRing.obj X.O)) :=
  (RingedToposHom.fSharpInverseImage_forget_homEquiv
    (localizationMorphism X F)).symm.trans
      ((congrArg (localizedRingedTopos X F).forgetRing.map
        (localization_fSharp_inverseImage X F)).trans rfl)

/-- **Stacks 04IH (5), second assertion.** The localization morphism
`(j_F, j_F♯) : (Sh(C)/F, O_F) → (Sh(C), O)` of a ringed topos at a sheaf is a morphism of
locally ringed topoi: the site of elements carries the restriction of the structure sheaf, so
the structure map is the identity on underlying sheaves of sets and the units square is a
square of identities. -/
@[stacks 04IH "(5), second assertion: the localization morphism `(j_F, j_F♯)` is a morphism of
locally ringed topoi"]
theorem localizationMorphism_isLocallyRinged :
    (localizationMorphism X F).IsLocallyRinged :=
  ⟨𝟙 _, fSharpSet_localizationMorphism X F ▸ .of_id_fst⟩

end AlgebraicGeometry.RingedTopos

end
