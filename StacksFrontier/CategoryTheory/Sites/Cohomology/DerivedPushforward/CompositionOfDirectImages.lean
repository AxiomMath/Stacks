module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of direct images of sheaves of modules on ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi. Stacks 0D6E asserts that `Rg_* ∘ Rf_* = R(g ∘ f)_*` on unbounded derived
categories of modules. The underived input to that statement is the canonical identification
`(g ∘ f)_* = f_* ⋙ g_*` on sheaves of modules, together with the fact that it is the identity
on underlying sections and so not an arbitrarily chosen isomorphism. That is what this file
supplies, for the presentation of a morphism of ringed topoi that the derived pushforward of
Stacks 07A6 is actually built on.

The measurement that fixed the shape of this file: Stacks 07A6 is in the tree, axiom-clean, as
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunction`,
and its `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward` is formed
from
`AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos` — the direct image for a morphism of
ringed topoi *presented by a continuous functor of the underlying sites*. The repository also
carries a second, topos-morphism presentation,
`Stacks.Sheaves.RingedToposModules.pushforwardModules`, which is a different declaration over a
different four-field structure and has **no composition operation at all**. Only
`RingedToposSiteHom` has one: `AlgebraicGeometry.RingedToposSiteHom.comp`, the site-level
form of the composition rule of Stacks 01D3 (3). So the composition law
is stated here for the presentation that both has a composition and feeds 07A6.

With that presentation the whole statement reduces to Mathlib. `pushforwardTopos f` is
`SheafOfModules.pushforward f.fSharpRing`, Mathlib's `SheafOfModules.pushforwardComp` already
identifies a composite of two such pushforwards with the pushforward for the composite
continuous functor, and it is `Iso.refl`. What remains is the one equation
`fSharpRing_comp` — that `RingedToposSiteHom.comp`'s structure map, which is built with the
comparison `Functor.sheafPushforwardContinuousComp` at the `CommRingCat` level, becomes the
plain composite `g♯ ≫ g_*(f♯)` once commutativity is forgotten. That equation is
`rfl`, so the comparison contributes nothing at the `RingCat` level and no transport has to be
carried through the isomorphism below.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso`: the canonical isomorphism
  `(g ∘ f)_* ≅ f_* ⋙ g_*` on sheaves of modules.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.fSharpRing_comp`: the structure map of a composite,
  read on sheaves of not necessarily commutative rings, is the composite of the two structure
  maps.
* `AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso_hom_app_val_app` and
  `…_inv_app_val_app`: the comparison is the identity on sections in both directions. This is
  what makes `pushforwardToposCompIso` *the* canonical identification rather than some
  isomorphism: a natural isomorphism of these two functors is pinned by its effect on sections,
  and this one has none.

## Implementation notes

The section universe `w` is shared by the three ringed topoi, while their site universes
`(v, u)`, `(v', u')`, `(v'', u'')` stay independent. That narrowing is **not** a local decision
here: it comes down the chain from the declaration of `AlgebraicGeometry.RingedToposSiteHom`
itself, which already identifies the section universes of its source and target, and from
`RingedToposSiteHom.comp`, which is declared at a single `w` for all three. Stacks 0D6E's own
statement has independent section universes, so this is recorded rather than decided, following
the chain's precedent.

No tag is placed. Stacks 0D6E's single assertion is the invertibility of the *derived*
comparison, and nothing here is that statement; the two tags nearest this material —
01D3 part (3) and 03D6 part (1) — are already on
`RingedToposSiteHom.comp` and `RingedToposSiteHom.pushforwardTopos`, and the composition law is
a clause of neither.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposSiteHom

universe v u v' u' v'' u'' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The structure map of a composite of morphisms of ringed topoi, read as a map of sheaves of
not necessarily commutative rings, is `g♯ ≫ g_*(f♯)`.

`RingedToposSiteHom.comp` defines its structure map with the comparison
`Functor.sheafPushforwardContinuousComp` at the end, because at the `CommRingCat` level the two
spellings of the iterated direct image are compared along it. After forgetting commutativity
the comparison is the identity, so no transport survives: this equation is `rfl`. It is the
only thing standing between `pushforwardToposCompIso` below and
`SheafOfModules.pushforwardComp`. -/
lemma fSharpRing_comp :
    (g.comp f).fSharpRing =
      g.fSharpRing ≫ (g.u.sheafPushforwardContinuous RingCat.{w} Z.J Y.J).map f.fSharpRing :=
  rfl

/-- **The underived half of Stacks 0D6E.** The direct image of sheaves of modules along a
composite of morphisms of ringed topoi is canonically isomorphic to the composite of the two
direct images.

The underlying sheaf of abelian groups of `(g ∘ f)_* M` is `M` precomposed with
`(g.u ⋙ f.u).op`, and that of `g_*(f_* M)` is `M` precomposed with `f.u.op` and then with
`g.u.op`; these agree on the nose, and by `fSharpRing_comp` so do the two module structures.
The isomorphism is therefore Mathlib's `SheafOfModules.pushforwardComp`, transported along that
one equation. -/
noncomputable def pushforwardToposCompIso :
    (g.comp f).pushforwardTopos ≅ f.pushforwardTopos ⋙ g.pushforwardTopos :=
  SheafOfModules.pushforwardCongr (fSharpRing_comp f g) ≪≫
    (SheafOfModules.pushforwardComp g.fSharpRing f.fSharpRing).symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The composition comparison is the identity on sections. Together with
`pushforwardToposCompIso_inv_app_val_app` this is the normalization of
`pushforwardToposCompIso`: it records which isomorphism it is, not merely that the two functors
are isomorphic. -/
lemma pushforwardToposCompIso_hom_app_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : Z.Cᵒᵖ)
    (x : ((g.comp f).pushforwardTopos.obj M).val.obj U) :
    ((pushforwardToposCompIso f g).hom.app M).val.app U x = x := rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The inverse of the composition comparison is the identity on sections. -/
lemma pushforwardToposCompIso_inv_app_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : Z.Cᵒᵖ)
    (x : ((f.pushforwardTopos ⋙ g.pushforwardTopos).obj M).val.obj U) :
    ((pushforwardToposCompIso f g).inv.app M).val.app U x = x := rfl

end AlgebraicGeometry.RingedToposSiteHom

end
