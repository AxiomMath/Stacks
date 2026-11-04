module

public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting

/-!
# Morphisms out of the universe-lifted unit sheaf of modules

`SheafOfModules.uliftForPresentation` raises the universe of the sections of a sheaf of modules
without moving its coefficient ring sheaf, and `SheafOfModules.HasGlobalPresentation` — the
global condition of Stacks 03DE(6) underlying quasi-coherence on an arbitrary site — builds its
free objects out of `SheafOfModules.uliftForPresentation (SheafOfModules.unit R)`.  That lift is
still free of rank one, generated over every object `X` by `ULift.up (1 : R(X))`, so a morphism
out of it is the same data as a *global section* of the target, exactly as for the unit object
itself (`SheafOfModules.unitHomEquiv`).

This file states that bijection for morphisms of **sheaves** of modules, together with its
naturality in the target and the resulting extensionality principle.  The analogous statement
for morphisms of the underlying *presheaves* of modules is
`Stacks.SheafOfModules.uliftUnitHomEquiv` of
`StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase`, and the equivalence here is that
one transported along the full faithfulness of `SheafOfModules.forget`, in the same way as
Mathlib's `SheafOfModules.unitHomEquiv` is built from `PresheafOfModules.unitHomEquiv`.

## Main definitions

* `Stacks.SheafOfModules.uliftUnitSheafHomEquiv`: morphisms of sheaves of modules out of the
  universe lift of the free module of rank one are the global sections of the target,
  `(SheafOfModules.uliftForPresentation (SheafOfModules.unit R) ⟶ M) ≃ M.sections`.

## Main results

* `Stacks.SheafOfModules.uliftUnitSheafHomEquiv_apply_coe`: the section attached to a morphism is
  the image of the generator `ULift.up 1`, by definition.
* `Stacks.SheafOfModules.uliftUnitSheafHomEquiv_comp_apply` and
  `Stacks.SheafOfModules.uliftUnitSheafHomEquiv_symm_comp`: **naturality in the target**, in the
  two directions of the equivalence.
* `Stacks.SheafOfModules.eq_of_sections_eq` and
  `Stacks.SheafOfModules.hom_ext_val_app_one`: two morphisms out of the lift agree as soon as
  their sections do, hence as soon as they agree on the generator `ULift.up 1` over every object.
* `Stacks.SheafOfModules.sectionsEquivObjOfIsTerminal_uliftUnitSheafHomEquiv`: **on a site with a
  terminal object this equivalence refines the one already available there.**  Evaluating the
  section attached to a morphism at a terminal object `Z` gives back
  `SheafOfModules.uliftUnitHomEquiv`, the bijection onto the sections over `Z`.

## Implementation notes

The module universe of the target is `max t r`, with `t` the amount by which the universe is
raised and `r` the universe of the coefficient rings.  That shape is forced by the universe lift
itself and is not an artifact: the sections of the lift over `X` are `ULift.{t} (R(X))`, which
lives in `Type (max t r)` whatever `t` is.  It is also the shape in which
`SheafOfModules.HasGlobalPresentation` uses the lift, so no further universe bound appears here.

Nothing is re-proved.  The content of the equivalence — that the sections of the lift over `X`
form the free `R(X)`-module on `ULift.up 1`, and that compatibility of the image of that element
with restriction is exactly the condition for a global section — is
`Stacks.SheafOfModules.uliftUnitHomEquiv`; what this file adds is the passage to morphisms of
sheaves, which is `SheafOfModules.fullyFaithfulForget`, and the naturality statements, which that
declaration does not record.  All three computations with the equivalence hold by `rfl`.

For the same reason there is no `SheafOfModules`-level restatement of "global sections of a
presheaf on a site with a terminal object are the sections over that object":
`SheafOfModules.sections` is an abbreviation for the sections of the underlying presheaf, so
`PresheafOfModules.sectionsEquivObjOfIsTerminal` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting` already
*is* that statement, at an arbitrary module universe.  It is used here as it stands, in
`Stacks.SheafOfModules.sectionsEquivObjOfIsTerminal_uliftUnitSheafHomEquiv`.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r t

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Morphisms of sheaves of modules out of the universe lift of the free module of rank one are
the global sections.**  For a sheaf of rings `R` on a site and a sheaf of `R`-modules `M` whose
module universe is a universe lift of that of `R`,

`(SheafOfModules.uliftForPresentation (SheafOfModules.unit R) ⟶ M) ≃ M.sections`,

the morphism `f` going to the section `X ↦ f.val.app X (ULift.up 1)` and a section `s` going to
the morphism whose component at `X` sends `ULift.up a` to `a • s.val X`.

This is `Stacks.SheafOfModules.uliftUnitHomEquiv`, the same bijection for morphisms of the
underlying presheaves of modules, composed with the full faithfulness of
`SheafOfModules.forget` — exactly how Mathlib's `SheafOfModules.unitHomEquiv` is obtained from
`PresheafOfModules.unitHomEquiv`.  The universe lift is what makes the statement usable where a
presentation is taken: `SheafOfModules.unitHomEquiv` pins the module universe of `M` to the
universe of the coefficient rings, whereas `SheafOfModules.HasGlobalPresentation` lifts the free
modules into a larger common universe first. -/
noncomputable def uliftUnitSheafHomEquiv (M : _root_.SheafOfModules.{max t r} R) :
    (_root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M) ≃ M.sections :=
  (_root_.SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (Stacks.SheafOfModules.uliftUnitHomEquiv.{u, v, r, t} M)

/-- The global section attached to a morphism out of the universe lift of the free module of rank
one is the image of the canonical generator `ULift.up 1`, over every object of the site. -/
lemma uliftUnitSheafHomEquiv_apply_coe (M : _root_.SheafOfModules.{max t r} R)
    (f : _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M) (X : Cᵒᵖ) :
    (uliftUnitSheafHomEquiv.{u, v, r, t} M f).val X =
      f.val.app X (ULift.up (1 : (R.obj.obj X : Type r))) :=
  rfl

/-- **`Stacks.SheafOfModules.uliftUnitSheafHomEquiv` is natural in the target.**  Postcomposing a
morphism out of the universe lift with `p : M ⟶ N` transports its section along `p`. -/
lemma uliftUnitSheafHomEquiv_comp_apply {M N : _root_.SheafOfModules.{max t r} R}
    (f : _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M) (p : M ⟶ N) :
    uliftUnitSheafHomEquiv.{u, v, r, t} N (f ≫ p) =
      PresheafOfModules.sectionsMap p.val (uliftUnitSheafHomEquiv.{u, v, r, t} M f) :=
  rfl

/-- **Naturality in the target, read through the inverse of
`Stacks.SheafOfModules.uliftUnitSheafHomEquiv`.**  The morphism attached to a section `s`,
followed by `p : M ⟶ N`, is the morphism attached to the transport of `s` along `p`. -/
lemma uliftUnitSheafHomEquiv_symm_comp {M N : _root_.SheafOfModules.{max t r} R}
    (s : M.sections) (p : M ⟶ N) :
    (uliftUnitSheafHomEquiv.{u, v, r, t} M).symm s ≫ p =
      (uliftUnitSheafHomEquiv.{u, v, r, t} N).symm (PresheafOfModules.sectionsMap p.val s) :=
  (uliftUnitSheafHomEquiv.{u, v, r, t} N).injective (by
    rw [uliftUnitSheafHomEquiv_comp_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- Two morphisms out of the universe lift of the free module of rank one with the same global
section are equal, `Stacks.SheafOfModules.uliftUnitSheafHomEquiv` being a bijection. -/
theorem eq_of_sections_eq {M : _root_.SheafOfModules.{max t r} R}
    {f g : _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M}
    (h : uliftUnitSheafHomEquiv.{u, v, r, t} M f = uliftUnitSheafHomEquiv.{u, v, r, t} M g) :
    f = g :=
  (uliftUnitSheafHomEquiv.{u, v, r, t} M).injective h

/-- **Two morphisms out of the universe lift of the free module of rank one agreeing on the
canonical generator `ULift.up 1` over every object are equal**, the sections of the lift over `X`
being the free `R(X)`-module on that element. -/
theorem hom_ext_val_app_one {M : _root_.SheafOfModules.{max t r} R}
    {f g : _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M}
    (h : ∀ X : Cᵒᵖ, f.val.app X (ULift.up (1 : (R.obj.obj X : Type r))) =
      g.val.app X (ULift.up (1 : (R.obj.obj X : Type r)))) :
    f = g :=
  eq_of_sections_eq.{u, v, r, t} (PresheafOfModules.sections_ext _ _ h)

/-- **On a site with a terminal object `Z`, `Stacks.SheafOfModules.uliftUnitSheafHomEquiv`
refines the bijection onto the sections over `Z`.**  Evaluating at `Z` the global section
attached to a morphism out of the universe lift gives back
`SheafOfModules.uliftUnitHomEquiv`, which identifies those morphisms with the sections over `Z`
directly.

Global sections of a presheaf of modules on such a site are its sections over `Z` by
`PresheafOfModules.sectionsEquivObjOfIsTerminal`, and the sections of a sheaf of modules are
those of its underlying presheaf, so that declaration serves unchanged and no sheaf-level
restatement of it is needed. -/
lemma sectionsEquivObjOfIsTerminal_uliftUnitSheafHomEquiv
    (M : _root_.SheafOfModules.{max t r} R) {Z : C} (hZ : IsTerminal Z)
    (f : _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, t}
      (_root_.SheafOfModules.unit R) ⟶ M) :
    PresheafOfModules.sectionsEquivObjOfIsTerminal M.val hZ
        (uliftUnitSheafHomEquiv.{u, v, r, t} M f) =
      _root_.SheafOfModules.uliftUnitHomEquiv.{u, v, r, t} hZ M f :=
  rfl

end Stacks.SheafOfModules

end
