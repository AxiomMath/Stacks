module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PushforwardIndexIso
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportRestrictRingSheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportRestrictSections

/-!
# Descent along a closed quotient morphism commutes with restriction to an open subspace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and let `U ⊆ X` be open. Descent
`ClosedQuotientMorphismOfRingedSpaces.moduleDescend` reads an `i_* 𝒪_Z`-module `𝓜` on `X` as an
`𝒪_Z`-module on `Z`, its sections over an open `V` of `Z` being `𝓜(i_! V)`. This file proves that
descent commutes with restriction to `U`,

`(moduleDescend 𝓜)|_{i⁻¹U} ≅ moduleDescend_{i|_{i⁻¹U}}(𝓜|_U)`,

as an isomorphism of **functors** `Mod(i_* 𝒪_Z) ⥤ Mod(𝒪_{Z|_{i⁻¹U}})`, with no hypothesis.

Two inputs make the statement sayable and true. The restricted module `𝓜|_U` is a module over
`(i_* 𝒪_Z)|_U`, while the descent of the restricted situation
`ClosedQuotientMorphismOfRingedSpaces.restrict` is taken over
`(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}`; the two sheaves of rings are identified, as algebras over
`𝒪_{X|_U}`, by `ClosedQuotientMorphismOfRingedSpaces.pushedRingSheafRestrictIso`, and that
identification is what `ClosedQuotientMorphismOfRingedSpaces.moduleRestrictionPushedRing` below
restricts scalars along. On sections both sides are sections of `𝓜` — over `i_! V` on the left
and over `i_! V ⊓ U` on the right — and the restriction between those two opens is bijective
because their difference misses the image of `Z`, which is
`ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_opensFunctor_restrict`.

## Main definitions

* `ClosedQuotientMorphismOfRingedSpaces.moduleRestrictionPushedRing`: restriction to `U` of an
  `i_* 𝒪_Z`-module, read as a module over the pushed structure sheaf of the restricted situation.
* `ClosedQuotientMorphismOfRingedSpaces.descendRestrictIndexLeft` and
  `descendRestrictIndexRight`: the two functors `Opens (i⁻¹U) ⥤ Opens X` along which the two
  composites reindex `𝓜`, namely `V ↦ i_! V` and `V ↦ i_! V ⊓ U`, and
  `descendRestrictOpensHom`: the inclusion between them.
* `ClosedQuotientMorphismOfRingedSpaces.descendRestrictScalarsLeft` and
  `descendRestrictScalarsRight`: the scalar morphisms of the two composites, read as
  pushforwards of presheaves of modules.
* `ClosedQuotientMorphismOfRingedSpaces.descendRestrictPresheafMap`: **the comparison**, as a
  natural transformation of pushforwards of presheaves of modules.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso`: **descent commutes with
  restriction to an open subspace**, as an isomorphism of functors.
* `ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso_hom_app_val_app`: on sections
  the isomorphism is the restriction map of `𝓜` from `i_! V` to `i_! V ⊓ U`. This pins the
  comparison down and rules out composing it with an automorphism.
* `ClosedQuotientMorphismOfRingedSpaces.descendRestrictScalars_compat`: the compatibility of the
  two scalar morphisms with the inclusion of index functors, which is what makes the comparison
  semilinear and hence exist at all.
* `ClosedQuotientMorphismOfRingedSpaces.bijective_descendRestrictPresheafMap_app_app` and
  `isIso_descendRestrictPresheafMap_app_app`: every component of the comparison is bijective.

## What this is for, and what it is not

This is one of the identifications the affine reduction of [Stacks, Tag 0E2N] is made of. That
reduction replaces `X` by an affine open and reads every functor in the canonical map of the tag
on the smaller space; `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupport` is the internal
Hom `ℰom_{𝒪_X}(i_* 𝒪_Z, -)` followed by descent, and before this file **neither** factor had been
compared with restriction to an open as a functor. The descent factor is now compared. It does
**not** follow that
`ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison` is an isomorphism:
that needs the same statement for the internal Hom factor, and then the identification of the
mate with the composite of the two. Neither is here.

For the internal Hom factor the restriction isomorphism **is** available for the internal Hom of
two sheaves of modules on an arbitrary ringed site — that is [Stacks, Tag 0E8H],
`Stacks.SheafOfModules.InternalHom.internalHomOverIso`, the underived counterpart of
[Stacks, Tag 08DL]. It is stated for the internal Hom
`Stacks.PresheafOfModules.internalHom` of two modules over a presheaf of *commutative* rings and
for restriction to the *slice site* `Opens X / U`. The factor occurring in
`sheafHomExactSupport` is `RingedSpaceModuleAdjunction.homSheaf`, whose underlying presheaf is
`Stacks.PresheafOfModules.CoextendScalars.coextObj` — the internal Hom out of a sheaf of rings,
over a sheaf of rings that is not required to be commutative — and the restriction occurring in
the comparison is to the *open subspace* `U`. So 0E8H does not apply to it as it stands, and
those two gaps, not the absence of an underived statement, are what the internal Hom factor is
waiting on.

## Implementation notes

*The two composites are pushforwards of presheaves of modules, definitionally.* Descent is
`PresheafOfModules.pushforward` along `i_!` (`descendPresheaf`), restriction to an open subspace
is `PresheafOfModules.pushforward` along the inclusion of opens (`restMod`, hence
`moduleRestriction`), and `PresheafOfModules.pushforwardComp` is `Iso.refl`. So each composite
is, on underlying presheaves of modules, a single pushforward along the composite index functor,
and `moduleDescend_comp_moduleRestriction_val` and
`moduleRestrictionPushedRing_comp_moduleDescend_val` record that by `rfl`. This is the only reason
the comparison can be taken from the generic `Stacks.PresheafOfModules.pushforwardIndexMap` rather
than built by hand with its semilinearity.

*The index functors are not isomorphic.* `i_! V` and `i_! V ⊓ U` are different opens of `X`, so
`Stacks.PresheafOfModules.pushforwardIsoOfIndexIso` does not apply: only the *map* comes from the
generic machinery, and invertibility comes from the gluing argument of
`ExactSupportRestrictSections.lean`. This is also why descent is not an instance of
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, which identifies two
pushforwards along isomorphic index functors and is the identity on sections; the comparison here
is a restriction map between two genuinely different opens, which happens to be bijective.

*The compatibility of the two scalar morphisms is a statement about a poset.* Both sides of
`descendRestrictScalars_compat` are composites of two restriction maps of `𝒪_Z` between one and
the same pair of opens of `Z`, so they agree because the hom types of `Opens Z` are
subsingletons. The two composites are reached by `rfl` — the one through the identity
`phiSh`, the counit of `i⁻¹ ⊣ i_!` and the comorphism of `i`; the other through the counit of the
restricted situation and the inverse of `pushedRingSheafRestrictIso`, whose component is
`ringSheafPushforwardRestrictIso_inv_app_hom_app`. Folding the composite on the left-hand side
with `rw [← Functor.map_comp]` fails on the two spellings of `i_!` that the index functors carry,
so that one fold is done by `exact` against the goal, which takes its instances from the goal.

## References

* [Stacks Project, Tag 0A74](https://stacks.math.columbia.edu/tag/0A74)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)

/-! ### Restriction of an `i_* 𝒪_Z`-module to `U` -/

/-- **Restriction to `U` of a module over `i_* 𝒪_Z`**, read as a module over the pushed-forward
structure sheaf `(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` of the restricted situation.

Restricting sections to the opens contained in `U` gives a module over `(i_* 𝒪_Z)|_U`; the
identification of that sheaf of rings with `(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` is
`ClosedQuotientMorphismOfRingedSpaces.pushedRingSheafRestrictIso`, and this is the restriction
with scalars taken along its inverse. By
`ClosedQuotientMorphismOfRingedSpaces.pushedRingHom_comp_pushedRingSheafRestrictIso_inv` that
identification is one of algebras over `𝒪_{X|_U}`, so no choice is made here. -/
def moduleRestrictionPushedRing :
    SheafOfModules.{u} S.pushedRingSheaf ⥤ SheafOfModules.{u} (S.restrict U).pushedRingSheaf :=
  SheafOfModules.pushforward (S.pushedRingSheafRestrictIso U).inv

/-! ### The two index functors and the inclusion between them -/

/-- The index functor of the left-hand composite `V ↦ i_! V`: an open `V` of `Z|_{i⁻¹U}` is read
as an open of `Z` and then sent to the largest open of `X` with that inverse image. These are the
opens whose sections of `𝓜` the restriction to `i⁻¹U` of the descent of `𝓜` has. -/
def descendRestrictIndexLeft : Opens (S.restrict U).Z ⥤ Opens S.X :=
  jFun (asRingSheafedSpace S.Z) (preimageOpen S.i U) ⋙ S.opensFunctor

/-- The index functor of the right-hand composite `V ↦ i_! V ⊓ U`: an open `V` of `Z|_{i⁻¹U}` is
sent to the `i_!` of the restricted situation and then read as an open of `X`. That this is
`i_! V ⊓ U` is `ClosedQuotientMorphismOfRingedSpaces.opensFunctor_inf_eq`. These are the opens
whose sections of `𝓜` the descent of `𝓜|_U` to `Z|_{i⁻¹U}` has. -/
def descendRestrictIndexRight : Opens (S.restrict U).Z ⥤ Opens S.X :=
  (S.restrict U).opensFunctor ⋙ jFun (asRingSheafedSpace S.X) U

/-- **The inclusion of the two index functors**, `i_! V ⊓ U ≤ i_! V`. Naturality is automatic,
the opens of `X` forming a poset. -/
def descendRestrictOpensHom :
    S.descendRestrictIndexRight U ⟶ S.descendRestrictIndexLeft U where
  app V := homOfLE ((S.opensFunctor_inf_eq U V).le.trans inf_le_left)
  naturality _ _ _ := Subsingleton.elim _ _

/-! ### The two composites as single pushforwards -/

/-- The scalars of the left-hand composite: the identity comparison of the structure sheaf of the
open subspace `i⁻¹U` of `Z`, followed by the ring datum `𝒪_Z ⟶ (i_* 𝒪_Z) ∘ i_!` of descent. -/
def descendRestrictScalarsLeft :
    (structureSheafRing (S.restrict U).Z).obj ⟶
      (S.descendRestrictIndexLeft U).op ⋙ S.pushedRingSheaf.obj :=
  (phiSh (asRingSheafedSpace S.Z) (preimageOpen S.i U)).hom ≫
    Functor.whiskerLeft (jFun (asRingSheafedSpace S.Z) (preimageOpen S.i U)).op S.descendRingHom

/-- The scalars of the right-hand composite: the ring datum of the descent of the restricted
situation, followed by the identification of the two sheaves of rings. -/
def descendRestrictScalarsRight :
    (structureSheafRing (S.restrict U).Z).obj ⟶
      (S.descendRestrictIndexRight U).op ⋙ S.pushedRingSheaf.obj :=
  (S.restrict U).descendRingHom ≫
    Functor.whiskerLeft ((S.restrict U).opensFunctor).op
      ((S.pushedRingSheafRestrictIso U).inv).hom

/-- **Descending and then restricting to `i⁻¹U` is, on underlying presheaves of modules, a single
pushforward**, along `V ↦ i_! V` with scalars `descendRestrictScalarsLeft`. Both descent and
restriction to an open subspace are pushforwards of presheaves of modules, and
`PresheafOfModules.pushforwardComp` is the identity, so this holds by `rfl`. -/
theorem moduleDescend_comp_moduleRestriction_val (M : SheafOfModules.{u} S.pushedRingSheaf) :
    ((S.moduleDescend ⋙ moduleRestriction S.Z (preimageOpen S.i U)).obj M).val =
      (PresheafOfModules.pushforward (S.descendRestrictScalarsLeft U)).obj M.val :=
  rfl

/-- **Restricting to `U` and then descending in the restricted situation is, on underlying
presheaves of modules, a single pushforward**, along `V ↦ i_! V ⊓ U` with scalars
`descendRestrictScalarsRight`. -/
theorem moduleRestrictionPushedRing_comp_moduleDescend_val
    (M : SheafOfModules.{u} S.pushedRingSheaf) :
    ((S.moduleRestrictionPushedRing U ⋙ (S.restrict U).moduleDescend).obj M).val =
      (PresheafOfModules.pushforward (S.descendRestrictScalarsRight U)).obj M.val :=
  rfl

/-! ### The comparison -/

/-- Two restriction maps of the structure sheaf of `Z` between one and the same pair of opens
agree, the opens of a space forming a poset. -/
private lemma mapZ_eq_mapZ {A B : (Opens S.Z)ᵒᵖ} (f g : A ⟶ B) :
    (structureSheafRing S.Z).obj.map f = (structureSheafRing S.Z).obj.map g := by
  rw [Subsingleton.elim f g]

/-- **The two scalar morphisms are compatible with the inclusion of index functors.** This is the
hypothesis of `Stacks.PresheafOfModules.pushforwardIndexMap`, and it is what makes the
restriction map of `𝓜` from `i_! V` to `i_! V ⊓ U` semilinear over `𝒪_{Z|_{i⁻¹U}}(V)`; without
it the comparison does not exist as a morphism of presheaves of modules.

Both sides are, at an open `V`, a composite of two restriction maps of `𝒪_Z` from `i⁻¹ V`, read
as an open of `Z`, to `i⁻¹(i_! V ⊓ U)`. They therefore agree because the hom types of `Opens Z`
are subsingletons. -/
theorem descendRestrictScalars_compat :
    S.descendRestrictScalarsLeft U ≫
        Functor.whiskerRight (NatTrans.op (S.descendRestrictOpensHom U))
          S.pushedRingSheaf.obj =
      S.descendRestrictScalarsRight U := by
  refine NatTrans.ext (funext fun V => ?_)
  have e1 : (S.descendRestrictScalarsLeft U ≫
        Functor.whiskerRight (NatTrans.op (S.descendRestrictOpensHom U))
          S.pushedRingSheaf.obj).app V =
      (structureSheafRing S.Z).obj.map
          (S.opensAdjunction.counit.app
            ((jFun (asRingSheafedSpace S.Z) (preimageOpen S.i U)).obj V.unop)).op ≫
        (structureSheafRing S.Z).obj.map
          ((opensMap S.i).map ((S.descendRestrictOpensHom U).app V.unop)).op := rfl
  have e2 : (S.descendRestrictScalarsRight U).app V =
      (structureSheafRing S.Z).obj.map
          ((jFun (asRingSheafedSpace S.Z) (preimageOpen S.i U)).map
            ((S.restrict U).opensAdjunction.counit.app V.unop)).op ≫
        (structureSheafRing S.Z).obj.map
          ((restrictOpensIso S.i U).hom.app
            ((S.restrict U).opensFunctor.obj V.unop)).op := rfl
  rw [e1, e2, ← Functor.map_comp]
  exact ((structureSheafRing S.Z).obj.map_comp _ _).symm.trans (mapZ_eq_mapZ S _ _)

/-- **The comparison of descent-then-restrict with restrict-then-descend**, as a natural
transformation of pushforwards of presheaves of modules. Its component at `𝓜` and an open `V` of
`Z|_{i⁻¹U}` is the restriction map of `𝓜` from `i_! V` to `i_! V ⊓ U`, by
`Stacks.PresheafOfModules.pushforwardIndexMap_app_app_apply`. -/
def descendRestrictPresheafMap :
    PresheafOfModules.pushforward.{u} (S.descendRestrictScalarsLeft U) ⟶
      PresheafOfModules.pushforward.{u} (S.descendRestrictScalarsRight U) :=
  Stacks.PresheafOfModules.pushforwardIndexMap
    (NatTrans.op (S.descendRestrictOpensHom U)) (S.descendRestrictScalars_compat U)

/-- **Every component of the comparison is bijective.** The component at `𝓜` and `V` is the
restriction map of `𝓜` between the two opens `i_! V` and `i_! V ⊓ U`, whose difference misses the
image of `Z`, so this is
`ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_opensFunctor_restrict`. -/
theorem bijective_descendRestrictPresheafMap_app_app
    (M : SheafOfModules.{u} S.pushedRingSheaf) (V : (Opens (S.restrict U).Z)ᵒᵖ) :
    Function.Bijective (ConcreteCategory.hom
      (((S.descendRestrictPresheafMap U).app M.val).app V)) :=
  S.bijective_presheaf_map_opensFunctor_restrict M U V.unop

/-- Every component of the comparison is invertible: a morphism of modules is an isomorphism as
soon as it is bijective on the underlying sets. -/
theorem isIso_descendRestrictPresheafMap_app_app
    (M : SheafOfModules.{u} S.pushedRingSheaf) (V : (Opens (S.restrict U).Z)ᵒᵖ) :
    IsIso (((S.descendRestrictPresheafMap U).app M.val).app V) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (S.bijective_descendRestrictPresheafMap_app_app U M V)

/-! ### Descent commutes with restriction to an open subspace -/

/-- **Descent along a closed quotient morphism commutes with restriction to an open subspace.**
For an open `U ⊆ X`, restricting the descent of an `i_* 𝒪_Z`-module `𝓜` to `i⁻¹U` is the descent,
in the restricted situation `ClosedQuotientMorphismOfRingedSpaces.restrict`, of the restriction of
`𝓜` to `U`, naturally in `𝓜` and with no hypothesis.

On sections over an open `V` of `Z|_{i⁻¹U}` the left side is `𝓜(i_! V)` and the right side is
`𝓜(i_! V ⊓ U)`, by `ClosedQuotientMorphismOfRingedSpaces.opensFunctor_inf_eq`; the restriction
between them is bijective because `i_! V ∖ U` misses the image of `Z`, where `𝓜` vanishes.

This is the statement that
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictSections.lean` recorded as not
proved, and `ExactSupportRestrictRingSheaf.lean` as waiting only on the comparison of the two
sheaves of rings. -/
def moduleDescendRestrictIso :
    S.moduleDescend ⋙ moduleRestriction S.Z (preimageOpen S.i U) ≅
      S.moduleRestrictionPushedRing U ⋙ (S.restrict U).moduleDescend :=
  NatIso.ofComponents
    (fun M =>
      (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk
          (fun V => @asIso _ _ _ _ _ (S.isIso_descendRestrictPresheafMap_app_app U M V))
          (fun {_ _} f => ((S.descendRestrictPresheafMap U).app M.val).naturality f)))
    (fun {_ _} f => by
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
      exact congrArg (fun g => PresheafOfModules.Hom.app g V)
        ((S.descendRestrictPresheafMap U).naturality f.val))

/-- **On sections the comparison is the restriction map of `𝓜`** from `i_! V` to `i_! V ⊓ U`.
This pins the isomorphism down: it is that restriction map and not that map composed with an
automorphism. -/
theorem moduleDescendRestrictIso_hom_app_val_app
    (M : SheafOfModules.{u} S.pushedRingSheaf) (V : (Opens (S.restrict U).Z)ᵒᵖ)
    (x : ((S.moduleDescend ⋙ moduleRestriction S.Z (preimageOpen S.i U)).obj M).val.obj V) :
    ((S.moduleDescendRestrictIso U).hom.app M).val.app V x =
      M.val.map (homOfLE ((S.opensFunctor_inf_eq U V.unop).le.trans inf_le_left)).op x :=
  rfl

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
