module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of sheafifications, of the sheaf inverse image, and of the pullback of modules

Sheafification does not change stalks.  For `Type`-valued presheaves on a topological space
this is Mathlib's `TopCat.Presheaf.sheafifyStalkIso`, about the *concrete* sheafification
built out of germs.  The same statement for the *categorical* sheafification
`CategoryTheory.presheafToSheaf`, with values in an arbitrary category that has
sheafification, is Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`: the
unit `P ⟶ P^#` induces an isomorphism on every stalk, because the stalk functor is a left
adjoint (the skyscraper sheaf is its right adjoint) and therefore so is its composite with
sheafification.  That theorem needs nothing of the value category beyond colimits, a terminal
object, and the existence of sheafification, so it applies verbatim to `CommRingCat` and to
`Ab`.  The resulting isomorphism is `TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso`.

This file draws the consequences for the three inverse-image constructions that proceed by
sheafifying a presheaf-level inverse image.

## Main results

* `Stacks.SheafifyStalk.stalkPushforward_naturality` and
  `Stacks.SheafifyStalk.stalkPullbackHom_naturality`: the direct-image and presheaf
  inverse-image stalk comparisons are natural in the presheaf.  Mathlib defines both
  morphisms and computes them on germs but states no naturality for either.
* `Stacks.SheafifyStalk.stalkSheafifyIso_naturality`: the sheafification stalk comparison is
  natural in the presheaf.
* `Stacks.SheafifyStalk.stalkSheafPullbackIso`: for a sheaf `F` with values in a suitable
  concrete category on a space `Y` and a continuous `f : X ⟶ Y`, the stalk of the *sheaf*
  inverse image is the stalk of `F` at the image point, `(f⁻¹F)_x ≅ F_{f(x)}`.  Mathlib has
  this for the presheaf inverse image only (`TopCat.Presheaf.stalkPullbackIso`).
  `Stacks.SheafifyStalk.stalkSheafPullbackIso_inv` writes its inverse out as the composite of
  the three comparisons it is built from.
* `Stacks.SheafifyStalk.stalkInverseImageIso`: the same for a sheaf of commutative rings along
  a morphism of schemes, `(g⁻¹A)_t ≅ A_{g(t)}`, in the spelling the base-change clauses of
  Stacks Tag 01SA are stated in.
* `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`: its instance at the structure
  sheaf, `(g⁻¹𝒪_S)_t ≅ 𝒪_{S,g(t)}`.
* `Stacks.SheafifyStalk.stalkModulesPullbackIso`: the stalk of the underlying presheaf of
  abelian groups of `AlgebraicGeometry.Scheme.Modules.pullback` is the stalk of the underlying
  presheaf of abelian groups of `PresheafOfModules.pullback`, so computing the former is
  reduced to a presheaf-level question with no sheafification left in it.
* `Stacks.SheafifyStalk.isRightAdjoint_presheafOfModules_pushforward`: the adjointness
  instance that reduction needs, re-spelled so that instance search can find it.

## Route and why

`TopCat.Sheaf.pullback` is, by `TopCat.Sheaf.pullbackIso`, the presheaf inverse image followed
by categorical sheafification.  So the stalk of the sheaf inverse image is the stalk of the
sheafification of the presheaf inverse image, which by the discussion above is the stalk of
the presheaf inverse image, which by `TopCat.Presheaf.stalkPullbackIso` is the stalk of `F` at
the image point.  Three isomorphisms composed; no new mathematics.

`AlgebraicGeometry.Scheme.Modules.pullback` is handled the same way.  Its underlying presheaf
of abelian groups is computed by `SheafOfModules.pullbackIso` followed by
`PresheafOfModules.sheafificationCompForgetCompToPresheaf`, which is `Iso.refl`: the
underlying presheaf of abelian groups of the sheafification of a presheaf of modules *is* the
`Ab`-valued sheafification of the underlying presheaf.  Hence sheafification drops out of the
stalk here too, and what remains is the stalk of the presheaf-level extension of scalars.

## Universe situation

Everything runs in a single universe: the value category has hom universe equal to the
universe of the underlying topological space, which is what `TopCat.Presheaf.stalkFunctor`
and `TopCat.Sheaf.pullback` both require.  For schemes this is the carrier universe `u`.  No
universe obstruction arises, and the general statements are polymorphic in the value category's
object universe.

## Transparency notes

Instance search is keyed syntactically, and the places where that bites here are all about the
underlying presheaf of a sheaf:

* The component `φ.hom` of a morphism of sheaves of rings
  `φ : S ⟶ (F.sheafPushforwardContinuous ..).obj R` has type `S.obj ⟶ ((..).obj R).obj`,
  which is definitionally but not syntactically `S.obj ⟶ F.op ⋙ R.obj`.  Mathlib's instance
  producing `(PresheafOfModules.pushforward φ.hom).IsRightAdjoint` is stated at the second
  spelling and so is *not* found at the first.  Writing the composite out with a `show` makes
  it synthesize; `isRightAdjoint_presheafOfModules_pushforward` does exactly that, and is
  registered as a local instance for the use of `SheafOfModules.pullbackIso` below.
* `AlgebraicGeometry.Scheme.Modules` is a `def` wrapping `SheafOfModules` with its own
  `Category` instance, so the scheme-level statements are obtained by applying the
  `SheafOfModules`-level ones at `f.toRingCatSheafHom`, not by instance search through the
  wrapper.
* `TopCat.Presheaf.stalk` is a `def`, so `F.stalk x` and `(stalkFunctor C x).obj F` are
  definitionally equal but not interchangeable at the transparency `rw` and `simp` use when
  they build a rewrite motive, and Mathlib's germ lemmas are stated at the first spelling
  while the stalk of a functorial construction appears at the second.  Every rewrite in the
  naturality proofs needs `TopCat.Presheaf.stalk` made implicitly reducible for the section;
  without it the germ lemmas silently fail to fire.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v u

noncomputable section

namespace Stacks.SheafifyStalk

section Naturality

open TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (C : Type u) [Category.{v} C] [HasColimits.{v} C] {X Y : TopCat.{v}}

/-- **The direct-image stalk comparison is natural in the presheaf.**  For `β : P ⟶ Q` on `X`
the square relating `(f_*P)_{f(x)} ⟶ P_x` and `(f_*Q)_{f(x)} ⟶ Q_x` commutes.

Mathlib has `TopCat.Presheaf.stalkPushforward` and computes it on germs, but states no
naturality in the presheaf. -/
@[ega "0 3.4.4"]
public theorem stalkPushforward_naturality (f : X ⟶ Y) {P Q : X.Presheaf C} (β : P ⟶ Q)
    (x : X) :
    (stalkFunctor C (f x)).map ((TopCat.Presheaf.pushforward C f).map β) ≫
        stalkPushforward C f Q x =
      stalkPushforward C f P x ≫ (stalkFunctor C x).map β := by
  refine stalk_hom_ext _ fun U hU => ?_
  simpa using (stalkFunctor_map_germ ((Opens.map f).obj U) x hU β).symm

/-- **The presheaf inverse-image stalk comparison is natural in the presheaf.**  For
`α : F ⟶ G` on `Y` the square relating `F_{f(x)} ⟶ (f⁻¹F)_x` and `G_{f(x)} ⟶ (f⁻¹G)_x`
commutes.

`TopCat.Presheaf.stalkPullbackHom` is the unit of the inverse-image/direct-image adjunction
on stalks followed by `TopCat.Presheaf.stalkPushforward`; the first factor is natural because
the unit is and the stalk is a functor, and the second by
`Stacks.SheafifyStalk.stalkPushforward_naturality`.  Mathlib states no naturality for it. -/
public theorem stalkPullbackHom_naturality (f : X ⟶ Y) {F G : Y.Presheaf C} (α : F ⟶ G)
    (x : X) :
    stalkPullbackHom C f F x ≫ (stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map α) =
      (stalkFunctor C (f x)).map α ≫ stalkPullbackHom C f G x := by
  have h : (TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app F ≫
      (TopCat.Presheaf.pushforward C f).map ((TopCat.Presheaf.pullback C f).map α) =
        α ≫ (TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app G :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.naturality α).symm
  rw [stalkPullbackHom, stalkPullbackHom, Category.assoc,
    ← stalkPushforward_naturality C f ((TopCat.Presheaf.pullback C f).map α) x]
  simp only [← Category.assoc, ← Functor.map_comp, h]

variable [HasTerminal C] [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- **The sheafification stalk comparison is natural in the presheaf.**  The components of
`TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso` are the stalks of the sheafification
unit, so this is the stalk functor applied to the naturality of that unit. -/
public theorem stalkSheafifyIso_naturality {P Q : X.Presheaf C} (β : P ⟶ Q) (x : X) :
    (ExtensionByInitial.stalkSheafifyIso P x).hom ≫ (stalkFunctor C x).map
        (sheafifyMap (Opens.grothendieckTopology X) β) =
      (stalkFunctor C x).map β ≫ (ExtensionByInitial.stalkSheafifyIso Q x).hom := by
  simp only [ExtensionByInitial.stalkSheafifyIso, asIso_hom, ← Functor.map_comp]
  exact congrArg _
    ((sheafificationAdjunction (Opens.grothendieckTopology X) C).unit.naturality β).symm

end Naturality

section SheafPullback

variable {X Y : TopCat.{v}} (A : Type u) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
variable [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{v} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- **The stalk of the sheaf inverse image is the stalk at the image point**:
`(f⁻¹F)_x ≅ F_{f(x)}` for a sheaf `F` on `Y` and a continuous map `f : X ⟶ Y`.

Mathlib's `TopCat.Presheaf.stalkPullbackIso` is the presheaf-level statement; the sheaf
inverse image is that followed by categorical sheafification, which by
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` does not change stalks. -/
@[ega "0 3.7.2" "more general"]
public def stalkSheafPullbackIso (f : X ⟶ Y) (F : TopCat.Sheaf A Y) (x : X) :
    ((TopCat.Sheaf.pullback A f).obj F).presheaf.stalk x ≅ F.presheaf.stalk (f x) :=
  (TopCat.Presheaf.stalkFunctor A x).mapIso
      ((TopCat.Sheaf.forget A X).mapIso ((TopCat.Sheaf.pullbackIso A f).app F)) ≪≫
    (TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso
      ((TopCat.Presheaf.pullback A f).obj F.presheaf) x).symm ≪≫
    (TopCat.Presheaf.stalkPullbackIso A f F.presheaf x).symm

section

attribute [local implicit_reducible] TopCat.Presheaf.stalk

/-- The inverse of `Stacks.SheafifyStalk.stalkSheafPullbackIso` written out: the presheaf-level
comparison `F_{f(x)} ⟶ (f⁻¹F)_x`, then the stalk of the sheafification unit, then the stalk of
the identification of the sheaf inverse image with the sheafified presheaf inverse image. -/
public theorem stalkSheafPullbackIso_inv (f : X ⟶ Y) (F : TopCat.Sheaf A Y) (x : X) :
    (stalkSheafPullbackIso A f F x).inv =
      (TopCat.Presheaf.stalkPullbackHom A f F.presheaf x ≫
          (TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso
            ((TopCat.Presheaf.pullback A f).obj F.presheaf) x).hom) ≫
        (TopCat.Presheaf.stalkFunctor A x).map ((TopCat.Sheaf.pullbackIso A f).inv.app F).hom :=
  rfl

end

end SheafPullback

section Schemes

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- **The stalk of the inverse image of a sheaf of commutative rings on a scheme**:
`(g⁻¹A)_t ≅ A_{g(t)}`.  This is `Stacks.SheafifyStalk.stalkSheafPullbackIso` at
`CommRingCat`, written in the vocabulary the base-change clauses of Stacks Tag 01SA use. -/
public def stalkInverseImageIso (A : TopCat.Sheaf CommRingCat.{u} S.toTopCat) (t : T) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj A).presheaf.stalk t ≅
      A.presheaf.stalk (g.base t) :=
  stalkSheafPullbackIso CommRingCat.{u} g.base A t

/-- **The stalk of `g⁻¹𝒪_S` is `𝒪_{S,g(t)}`.**  The instance of
`Stacks.SheafifyStalk.stalkInverseImageIso` at the structure sheaf, which is the ring that the
stalk of a pullback algebra is an algebra over. -/
public def stalkInverseImageStructureSheafIso (t : T) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj S.sheaf).presheaf.stalk t ≅
      S.presheaf.stalk (g.base t) :=
  stalkInverseImageIso g S.sheaf t

end Schemes

section Modules

/-- The adjointness of presheaf-level pushforward of modules, re-spelled at the composite
`F.op ⋙ R.obj` so that instance search matches it.

Mathlib proves this instance for a morphism of *presheaves* of rings written as
`S ⟶ F.op ⋙ R`.  The comorphism of a morphism of sheaves of rings is a morphism of presheaves
of rings whose target is spelled `((F.sheafPushforwardContinuous ..).obj R).obj` instead;
the two are definitionally equal, but instance search is syntactic and does not see it. -/
public theorem isRightAdjoint_presheafOfModules_pushforward {X Y : TopCat.{u}} {f : X ⟶ Y}
    {R : TopCat.Sheaf RingCat.{u} X} {S : TopCat.Sheaf RingCat.{u} Y}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↑Y) (Opens.grothendieckTopology ↑X)).obj R) :
    (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{u}
    (show S.obj ⟶ (Opens.map f).op ⋙ R.obj from φ.hom)).IsRightAdjoint

attribute [local instance] isRightAdjoint_presheafOfModules_pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The stalk of the pullback of a sheaf of modules carries no sheafification.**  On
underlying presheaves of abelian groups, the stalk at `x` of `f^*M` is the stalk at `x` of the
*presheaf*-level pullback of `M`, that is of the presheaf-level extension of scalars
`M ⊗_{f^{-1}𝒪_Y} 𝒪_X`.

`SheafOfModules.pullbackIso` writes `f^*` as the presheaf-level pullback followed by
sheafification of presheaves of modules, and the underlying presheaf of abelian groups of that
sheafification is the `Ab`-valued sheafification of the underlying presheaf
(`PresheafOfModules.sheafificationCompForgetCompToPresheaf` is `Iso.refl`).  So the
sheafification contributes nothing to the stalk. -/
public def stalkModulesPullbackIso (M : Y.Modules) (x : X) :
    ((Scheme.Modules.pullback f).obj M).presheaf.stalk x ≅
      (TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
        ((PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom).obj
          ((SheafOfModules.forget _).obj M)).presheaf :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
        ((SheafOfModules.pullbackIso f.toRingCatSheafHom).app M)) ≪≫
    (TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso _ x).symm

end Modules

end Stacks.SheafifyStalk

end

end
