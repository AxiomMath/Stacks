module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous

/-!
# Étale base change for the direct image of modules

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Stacks 03LX asserts that for every `𝒪_X`-module `F`

`f'_*(F|_{X'}) = (f_*F)|_{Y'}`   and   `R^i f'_*(F|_{X'}) = (R^i f_*F)|_{Y'}`

in `Mod(𝒪_{Y'})`, and in a footnote the inverse-image counterpart
`(f')^*(G|_{Y'}) = (f^*G)|_{X'}` around the square.  The source proves the two displayed
identities by "a restatement of Stacks 03LR applied to modules".

This file supplies the footnote outright, carries out that restatement for the **ordinary**
direct image down to a single ring-theoretic compatibility of the structure maps of
Stacks 03G8, and proves the exactness properties of étale restriction that the higher statement
consumes.  The higher direct images themselves are not treated: right-derived functors of
`AlgebraicGeometry.Space.modulePushforward` need enough injectives in
`AlgebraicGeometry.Space.Modules`, which this development does not have.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorRestrictScalarsIso`: restriction of scalars
  commutes with the transport of sheaves of modules along a finite-product-preserving functor of
  sheaves of sets.
* `AlgebraicGeometry.Space.smallEtaleSetRestriction`,
  `AlgebraicGeometry.Space.spacesEtaleSetRestriction` and
  `AlgebraicGeometry.Space.spacesSetBaseChange`: the three restriction functors on sheaves of
  sets, at the universe of the structure rings.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`: small étale restriction as the
  conjugate by the comparison equivalences of Stacks 03G1 of spaces-étale restriction.
* `AlgebraicGeometry.Space.baseChangeStructureSharp` and
  `AlgebraicGeometry.Space.baseChangeRingMap`: the structure map of `f'` and the comparison of
  the two transported structure sheaves, over which the two sides of base change are modules.

## Main results

* `AlgebraicGeometry.Space.modulePullbackSquareIso` is **the footnote of Stacks 03LX**,
  unconditionally, with both of its restrictions read as the inverse image of modules; see its
  docstring for why that reading, and not the restriction reading, is what is proved.
* `AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso` and
  `AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso` are **Stacks 03LR, part (1)**
  at the universe of the structure rings, on the spaces-étale and on the small étale sites.
* `AlgebraicGeometry.Space.modulePushforward_comp_etaleModulePullback_eq` and
  `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeLeftIso` exhibit the two sides of
  the ordinary statement of Stacks 03LX as transports of `𝒪_X`-modules along the two composite
  functors of sheaves of sets, with explicit structure maps.
* `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp` is the ordinary
  statement of Stacks 03LX, conditional on the one named hypothesis `hsharp`.
* `AlgebraicGeometry.Space.etaleModulePullback_additive`,
  `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModulePullback`,
  `AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback` and
  `AlgebraicGeometry.Space.etaleModulePullback_shortExact`: étale restriction of modules is
  additive and exact, hence preserves short exact sequences.

## Implementation notes

**Stacks 03LR at the universe of the structure rings.**
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso` is Stacks 03LR, part (1) for the
morphisms of small étale *topoi* of Stacks 03G2, part (3), which exist only at
`Type (u + 1)`.  The direct image of modules applies the direct image of sheaves of *sets* to
the sheaf underlying a module, and on the small étale site of an algebraic space that direct
image — `AlgebraicGeometry.Space.smallEtaleDirectImage` — is available only at `Type u`.  So the
statement had to be redone one universe down.  It is literally the same proof: the Beck–Chevalley
isomorphism `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` of the cartesian square is
universe-independent, and all four functors are again conjugates, by the comparison equivalence
of Stacks 03G1 at `Type u`, of restriction functors on the spaces-étale sites.  The only
difference is that the conjugating equivalence is `CategoryTheory.Functor.asEquivalence` of
`AlgebraicGeometry.Space.smallEtaleComparisonRestriction` rather than the named
`AlgebraicGeometry.Space.smallEtaleToposEquiv`.  Generalizing the value category of
`AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso` would make this file's two spaces-étale
declarations redundant.

**From sheaves of sets to modules.**  Both sides of the ordinary statement are transports of
`𝒪_X`-modules along a composite functor of sheaves of sets, followed by one restriction of
scalars; the comparison of the two is then
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` applied to the isomorphism of
those composites.  The right-hand side is such a transport by `rfl`, exactly as in Stacks 04CF
(`AlgebraicGeometry.Space.modulePushforward_comp_overFunctor_eq`): étale restriction only
reindexes sections.  The left-hand side is not, because there the restriction comes *first*: it
needs `Stacks.Sheaves.ToposPullback.restrictionModuleIso` to read étale restriction of modules
as a transport, this file's
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorRestrictScalarsIso` to move the resulting
restriction of scalars past the direct image, and
`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` to merge the two transports.

**What is left open, and why it is a hypothesis and not a `sorry`.**  After that reduction the
two sides are transports along isomorphic functors of sheaves of sets, and the *only* thing
missing is that the two structure maps agree: that `(f')^♯` corresponds, under the sheaf-of-sets
base-change isomorphism, to the étale restriction of `f^♯`.  That is a compatibility of the
family of structure maps of Stacks 03G8, and
`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean` proves none — it constructs `f^♯`
one morphism at a time and explicitly leaves even the composition law `(g ≫ f)^♯` unproved.  It
is therefore carried as the explicit named hypothesis `hsharp` of
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIsoOfStructureSharp`, which for that
reason carries **no** `@[stacks 03LX]` attribute.  Only the footnote does.

**Elaboration.**  Every intermediate isomorphism and every restriction-of-scalars functor is
named with its type written out, and every reassociation is explicit.  That is not cosmetic: a
metavariable in a `CategoryTheory.Functor.comp` position here either leaves the `Category`
instance of a `SheafOfModules` unsynthesizable — the module universe of
`SheafOfModules.restrictScalars` is not determined by its argument — or hands the unifier
`?F ⋙ ?G ≟ (P ⋙ A) ⋙ B`, whose first-order match fails, after which the fallback unfolds
`AlgebraicGeometry.Space.smallEtaleDirectImage` and the comparison equivalence of Stacks 03G1,
whose quasi-inverse is a `CategoryTheory.Functor.objPreimage`, i.e. a `Classical.choose`, and
does not terminate.  The universes of `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` are given
explicitly for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`: elaboration of an expected type
mentioning it defaults the universes of the source site before the functor argument is
elaborated.  No `set_option` appears in this file.

**Universes.**  The module universe is the universe `u` of the structure rings wherever
`AlgebraicGeometry.Space.modulePushforward` or `AlgebraicGeometry.Space.modulePullback` occurs,
since neither exists at any other.  `AlgebraicGeometry.Space.etaleModulePullback_additive` is at
a free module universe.  `AlgebraicGeometry.Space.etaleModulePullback_shortExact` is at `u`
because `Stacks.SheafOfModules.pushforward_preservesColimits` states the preservation of
colimits with the universe of the module sections equal to that of the sheaves of rings;
generalizing it would free that universe.

The declarations in the namespace `Stacks.Sheaves.ToposPullback` are general facts about the
transport of sheaves of modules and belong with that notion; they are here only to keep the
files they would belong to untouched.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u m

/-! ### Restriction of scalars and the transport of modules -/

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [Limits.PreservesFiniteProducts Φ]
  {O O' : Sheaf K RingCat.{ww'}}

/-- The transported module structure of a sheaf of modules read through restriction of scalars
along `a` is the restriction along the transport of `a` of the transported module structure: the
identity map on sections is linear.

The addition is unchanged by restriction of scalars, and the scalar actions are compared by
`Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars`. -/
noncomputable def pullbackModuleRestrictScalarsHom (a : O ⟶ O')
    (M : SheafOfModules.{ww'} O') (X : Cᵒᵖ) :
    (pullbackModuleObj J Φ O ((SheafOfModules.restrictScalars a).obj M)).val.obj X ⟶
      ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ a)).obj
        (pullbackModuleObj J Φ O' M)).val.obj X :=
  letI : Module ((pullbackRingSheaf J Φ O).obj.obj X)
      ((pullbackModuleAb J Φ O ((SheafOfModules.restrictScalars a).obj M)).obj X) :=
    Sheaf.moduleObjModule O ((SheafOfModules.restrictScalars a).obj M)
      (Φ ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (X := ModuleCat.of ((pullbackRingSheaf J Φ O).obj.obj X)
      ((pullbackModuleAb J Φ O ((SheafOfModules.restrictScalars a).obj M)).obj X))
    (Y := (ModuleCat.restrictScalars ((pullbackRingSheafMap J Φ a).hom.app X).hom).obj
      ((pullbackModuleObj J Φ O' M).val.obj X))
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦
        Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars a M
          (Φ ⋙ Sheaf.sectionsFunctor J X) r x }

/-- The same identity map on sections, read as a linear map in the other direction. -/
noncomputable def pullbackModuleRestrictScalarsHomInv (a : O ⟶ O')
    (M : SheafOfModules.{ww'} O') (X : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ a)).obj
        (pullbackModuleObj J Φ O' M)).val.obj X ⟶
      (pullbackModuleObj J Φ O ((SheafOfModules.restrictScalars a).obj M)).val.obj X :=
  letI : Module ((pullbackRingSheaf J Φ O).obj.obj X)
      ((pullbackModuleAb J Φ O ((SheafOfModules.restrictScalars a).obj M)).obj X) :=
    Sheaf.moduleObjModule O ((SheafOfModules.restrictScalars a).obj M)
      (Φ ⋙ Sheaf.sectionsFunctor J X)
  ModuleCat.ofHom
    (Y := ModuleCat.of ((pullbackRingSheaf J Φ O).obj.obj X)
      ((pullbackModuleAb J Φ O ((SheafOfModules.restrictScalars a).obj M)).obj X))
    (X := (ModuleCat.restrictScalars ((pullbackRingSheafMap J Φ a).hom.app X).hom).obj
      ((pullbackModuleObj J Φ O' M).val.obj X))
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦
        (Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars a M
          (Φ ⋙ Sheaf.sectionsFunctor J X) r x).symm }

/-- The comparison of the two readings on the sections over one object. -/
noncomputable def pullbackModuleRestrictScalarsObjIso (a : O ⟶ O')
    (M : SheafOfModules.{ww'} O') (X : Cᵒᵖ) :
    (pullbackModuleObj J Φ O ((SheafOfModules.restrictScalars a).obj M)).val.obj X ≅
      ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ a)).obj
        (pullbackModuleObj J Φ O' M)).val.obj X where
  hom := pullbackModuleRestrictScalarsHom J Φ a M X
  inv := pullbackModuleRestrictScalarsHomInv J Φ a M X
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison of the two readings on one sheaf of modules. -/
noncomputable def pullbackModuleRestrictScalarsSheafIso (a : O ⟶ O')
    (M : SheafOfModules.{ww'} O') :
    pullbackModuleObj J Φ O ((SheafOfModules.restrictScalars a).obj M) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ a)).obj
        (pullbackModuleObj J Φ O' M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (pullbackModuleRestrictScalarsObjIso J Φ a M) (fun _ _ _ ↦ rfl))

/-- **Restriction of scalars commutes with the transport of sheaves of modules.** Transporting
a sheaf of `O'`-modules read as a sheaf of `O`-modules along `a : O ⟶ O'` is the transport of
the sheaf of `O'`-modules, read through the transport
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMap` of `a`.

The comparison is the identity on sections; the content is that the transported addition and
scalar action are unaffected. -/
noncomputable def pullbackModuleFunctorRestrictScalarsIso (a : O ⟶ O') :
    SheafOfModules.restrictScalars a ⋙ pullbackModuleFunctor J Φ O ≅
      pullbackModuleFunctor J Φ O' ⋙
        SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ a) :=
  NatIso.ofComponents (pullbackModuleRestrictScalarsSheafIso J Φ a) (fun _ ↦ rfl)

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-! ### Restriction functors at the universe of the structure rings -/

/-- Restriction of sheaves of sets along small étale postcomposition with an étale morphism
`h : U ⟶ V`, at the universe of the structure rings. -/
noncomputable abbrev smallEtaleSetRestriction {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Sheaf (SmallEtale.topology B S hS V.1) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS U.1) (Type u) :=
  (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)

/-- Restriction of sheaves of sets along spaces-étale postcomposition with an étale morphism
`h : U ⟶ V`, at the universe of the structure rings. -/
noncomputable abbrev spacesEtaleSetRestriction {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Sheaf (SpacesEtale.topology B S hS V) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS U) (Type u) :=
  (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V)

/-- Restriction of sheaves of sets along spaces-étale base change, at the universe of the
structure rings: the second factor of `AlgebraicGeometry.Space.smallEtaleDirectImage`. -/
noncomputable abbrev spacesSetBaseChange {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) :
    Sheaf (SpacesEtale.topology B S hS U) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS V) (Type u) :=
  (spacesBaseChange B S hS h).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U)

/-- **The comparison square of Stacks 03G1 for postcomposition, on sheaves of sets.**
Restricting along spaces-étale postcomposition and then along the comparison functor of
Stacks 03G1 is restricting along the comparison functor and then along small étale
postcomposition.

The two composites of functors of sites are equal by
`AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`, and restriction along a
composite is the composite of the restrictions on the nose, so this is `rfl`. -/
theorem spacesEtaleSetRestriction_comp_comparisonRestriction
    {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    spacesEtaleSetRestriction B S hS h hh ⋙ smallEtaleComparisonRestriction B S hS U =
      smallEtaleComparisonRestriction B S hS V ⋙ smallEtaleSetRestriction B S hS h hh :=
  rfl

/-- Small étale restriction along an étale morphism, written as the conjugate by the comparison
equivalences of Stacks 03G1 of spaces-étale restriction.

This is the shape in which the base-change comparison below consumes it; the content is
`AlgebraicGeometry.Space.spacesEtaleSetRestriction_comp_comparisonRestriction` together with the
counit of the comparison equivalence. -/
noncomputable def smallEtaleSetRestrictionConjIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    smallEtaleSetRestriction B S hS h hh ≅
      (smallEtaleComparisonRestriction B S hS V).asEquivalence.inverse ⋙
        spacesEtaleSetRestriction B S hS h hh ⋙ smallEtaleComparisonRestriction B S hS U :=
  let e : Sheaf (SpacesEtale.topology B S hS V) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS V.1) (Type u) :=
    (smallEtaleComparisonRestriction B S hS V).asEquivalence
  let b₁ : smallEtaleSetRestriction B S hS h hh ≅
      𝟭 (Sheaf (SmallEtale.topology B S hS V.1) (Type u)) ⋙
        smallEtaleSetRestriction B S hS h hh :=
    (Functor.leftUnitor (smallEtaleSetRestriction B S hS h hh)).symm
  let b₂ : 𝟭 (Sheaf (SmallEtale.topology B S hS V.1) (Type u)) ⋙
        smallEtaleSetRestriction B S hS h hh ≅
      (e.inverse ⋙ e.functor) ⋙ smallEtaleSetRestriction B S hS h hh :=
    Functor.isoWhiskerRight e.counitIso.symm (smallEtaleSetRestriction B S hS h hh)
  let b₃ : (e.inverse ⋙ e.functor) ⋙ smallEtaleSetRestriction B S hS h hh ≅
      e.inverse ⋙ (e.functor ⋙ smallEtaleSetRestriction B S hS h hh) :=
    Functor.associator e.inverse e.functor (smallEtaleSetRestriction B S hS h hh)
  let b₄ : e.inverse ⋙ (smallEtaleComparisonRestriction B S hS V ⋙
        smallEtaleSetRestriction B S hS h hh) ≅
      e.inverse ⋙ (spacesEtaleSetRestriction B S hS h hh ⋙
        smallEtaleComparisonRestriction B S hS U) :=
    eqToIso (congrArg (fun F ↦ e.inverse ⋙ F)
      (spacesEtaleSetRestriction_comp_comparisonRestriction B S hS h hh).symm)
  b₁ ≪≫ b₂ ≪≫ b₃ ≪≫ b₄ ≪≫
    (Functor.associator e.inverse (spacesEtaleSetRestriction B S hS h hh)
      (smallEtaleComparisonRestriction B S hS U)).symm

/-! ### Base change on the spaces-étale sites, at the universe of the structure rings -/

/-- **Stacks 03LR, part (1), on the spaces-étale topoi, at the universe of the structure
rings.** Restriction along postcomposition with `i` followed by restriction along base change
along `f'` is restriction along base change along `f` followed by restriction along
postcomposition with `g`.

This is `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` — the Beck–Chevalley isomorphism
of the cartesian square, lifted to the étale objects — transported by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`.  It is the same two lines as
`AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso`, whose statement fixes the value
category to `Type (u + 1)`; the modules of the small étale sites live at the universe of the
structure rings, so this instance of the square is the one they consume. -/
noncomputable def spacesSetPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    spacesEtaleSetRestriction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        spacesSetBaseChange B S hS f' ≅
      spacesSetBaseChange B S hS f ⋙ spacesEtaleSetRestriction B S hS g hg :=
  haveI := Functor.isContinuous_comp (spacesEtalePostcomp B S hS g hg)
    (spacesBaseChange B S hS f).functor (SpacesEtale.topology B S hS Y')
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.sheafPushforwardContinuousComp'
      (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg) (Type u)
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')
      (SpacesEtale.topology B S hS X) ≪≫
    (Functor.sheafPushforwardContinuousComp (spacesEtalePostcomp B S hS g hg)
      (spacesBaseChange B S hS f).functor (Type u)
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X)).symm

/-! ### Base change for the direct image of sheaves of sets on the small étale sites -/

/-- **Stacks 03LR, part (1), for the direct image at the universe of the structure rings.**
For a cartesian square of algebraic spaces whose bottom arrow `g` is étale, the direct image of
sheaves of sets on the small étale sites commutes with étale restriction:
`f'_*(F|_{X'}) = (f_*F)|_{Y'}`, naturally in `F`.

Each of the four functors is the conjugate by the comparison equivalences of Stacks 03G1 of a
restriction functor on the spaces-étale sites, where the statement is
`AlgebraicGeometry.Space.spacesSetPushforwardBaseChangeIso`, and
`CategoryTheory.Equivalence.conjugateCompIso` collapses the composites of conjugates to the
conjugates of the composites.

`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso` is the same assertion for the
morphisms of small étale *topoi* of Stacks 03G2, part (3), which exist only at
`Type (u + 1)`.  The direct image of modules applies the direct image of sheaves of sets to the
sheaf underlying a module, so it is this instance, at the universe of the structure rings, that
the module statement of Stacks 03LX needs. -/
noncomputable def smallEtaleSetPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    smallEtaleSetRestriction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        smallEtaleDirectImage B S hS f' ≅
      smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg :=
  let eX : Sheaf (SpacesEtale.topology B S hS X) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
    (smallEtaleComparisonRestriction B S hS X).asEquivalence
  let eX' : Sheaf (SpacesEtale.topology B S hS X') (Type u) ≌
      Sheaf (SmallEtale.topology B S hS X'.1) (Type u) :=
    (smallEtaleComparisonRestriction B S hS X').asEquivalence
  let eY : Sheaf (SpacesEtale.topology B S hS Y) (Type u) ≌
      Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence
  let eY' : Sheaf (SpacesEtale.topology B S hS Y') (Type u) ≌
      Sheaf (SmallEtale.topology B S hS Y'.1) (Type u) :=
    (smallEtaleComparisonRestriction B S hS Y').asEquivalence
  let Pi : Sheaf (SpacesEtale.topology B S hS X) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS X') (Type u) :=
    spacesEtaleSetRestriction B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  let Pg : Sheaf (SpacesEtale.topology B S hS Y) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS Y') (Type u) :=
    spacesEtaleSetRestriction B S hS g hg
  let Rf' : Sheaf (SpacesEtale.topology B S hS X') (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS Y') (Type u) := spacesSetBaseChange B S hS f'
  let Rf : Sheaf (SpacesEtale.topology B S hS X) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS Y) (Type u) := spacesSetBaseChange B S hS f
  let a₁ : smallEtaleSetRestriction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        smallEtaleDirectImage B S hS f' ≅
      (eX.inverse ⋙ Pi ⋙ eX'.functor) ⋙ smallEtaleDirectImage B S hS f' :=
    Functor.isoWhiskerRight
      (smallEtaleSetRestrictionConjIso B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (smallEtaleDirectImage B S hS f')
  let a₂ : (eX.inverse ⋙ Pi ⋙ eX'.functor) ⋙ (eX'.inverse ⋙ Rf' ⋙ eY'.functor) ≅
      eX.inverse ⋙ (Pi ⋙ Rf') ⋙ eY'.functor :=
    Equivalence.conjugateCompIso eX eX' eY' Pi Rf'
  let a₃ : eX.inverse ⋙ (Pi ⋙ Rf') ⋙ eY'.functor ≅
      eX.inverse ⋙ (Rf ⋙ Pg) ⋙ eY'.functor :=
    Functor.isoWhiskerLeft eX.inverse
      (Functor.isoWhiskerRight (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg)
        eY'.functor)
  let a₄ : eX.inverse ⋙ (Rf ⋙ Pg) ⋙ eY'.functor ≅
      (eX.inverse ⋙ Rf ⋙ eY.functor) ⋙ (eY.inverse ⋙ Pg ⋙ eY'.functor) :=
    (Equivalence.conjugateCompIso eX eY eY' Rf Pg).symm
  let a₅ : smallEtaleDirectImage B S hS f ⋙ (eY.inverse ⋙ Pg ⋙ eY'.functor) ≅
      smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg :=
    Functor.isoWhiskerLeft (smallEtaleDirectImage B S hS f)
      (smallEtaleSetRestrictionConjIso B S hS g hg).symm
  a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅


/-! ### Modules: the two sides as transports along the composite -/

/-- Restriction of sheaves of rings along small étale postcomposition with an étale morphism. -/
noncomputable abbrev smallEtaleRingRestriction {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Sheaf (SmallEtale.topology B S hS V.1) RingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS U.1) RingCat.{u} :=
  (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous RingCat.{u}
    (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)

/-- Pullback of modules along an étale morphism is the restriction of modules of Stacks 03D1
along the continuous functor of small étale postcomposition. -/
theorem etaleModulePullback_eq_restrictionModules {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    etaleModulePullback.{u, u} B S hS h hh =
      restrictionModules (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)
        (smallEtalePostcomp B S hS h hh) (structureRingSheaf B S hS V) :=
  rfl

/-- The structure sheaf of `U`, read as the transport of the structure sheaf of `V` along étale
restriction of sheaves of sets. -/
noncomputable abbrev etaleRestrictionRingSheaf {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) : Sheaf (SmallEtale.topology B S hS U.1) RingCat.{u} :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS U.1)
    (smallEtaleSetRestriction B S hS h hh) (structureRingSheaf B S hS V)

/-- The transport of the structure sheaf of `V` along étale restriction *is* the structure
sheaf of `U`: the sections agree on the nose and the transported ring operations agree with the
original ones.  This is `Stacks.Sheaves.ToposPullback.restrictionRingIso`. -/
noncomputable abbrev etaleStructureRingIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    etaleRestrictionRingSheaf B S hS h hh ≅ structureRingSheaf B S hS U :=
  restrictionRingIso (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)
    (smallEtalePostcomp B S hS h hh) (structureRingSheaf B S hS V)

/-- The iterated transport of `𝒪_X`, first along étale restriction to `X'` and then along the
direct image of `f'`. -/
noncomputable abbrev baseChangeIteratedRingSheaf (hi : IsEtale B S hS i.hom) :
    Sheaf (SmallEtale.topology B S hS Y'.1) RingCat.{u} :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
    (smallEtaleDirectImage B S hS f') (etaleRestrictionRingSheaf B S hS i hi)

/-- The transport of `𝒪_X` along the composite `(-)|_{X'} ⋙ f'_*`: the sheaf of rings over
which the left-hand side of Stacks 03LX is a module before restriction of scalars. -/
noncomputable abbrev baseChangeLeftRingSheaf (hi : IsEtale B S hS i.hom) :
    Sheaf (SmallEtale.topology B S hS Y'.1) RingCat.{u} :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
    (smallEtaleSetRestriction B S hS i hi ⋙ smallEtaleDirectImage B S hS f')
    (structureRingSheaf B S hS X)

/-- The transport of `𝒪_X` along the composite `f_* ⋙ (-)|_{Y'}`: the sheaf of rings over
which the right-hand side of Stacks 03LX is a module before restriction of scalars. -/
noncomputable abbrev baseChangeRightRingSheaf (hg : IsEtale B S hS g.hom) :
    Sheaf (SmallEtale.topology B S hS Y'.1) RingCat.{u} :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS Y'.1)
    (smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg)
    (structureRingSheaf B S hS X)

/-- The transport of `𝒪_X`-modules along `(-)|_{X'} ⋙ f'_*`. -/
noncomputable abbrev baseChangeLeftTransport (hi : IsEtale B S hS i.hom) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) :=
  pullbackModuleFunctor (SmallEtale.topology B S hS Y'.1)
    (smallEtaleSetRestriction B S hS i hi ⋙ smallEtaleDirectImage B S hS f')
    (structureRingSheaf B S hS X)

/-- The transport of `𝒪_X`-modules along `f_* ⋙ (-)|_{Y'}`. -/
noncomputable abbrev baseChangeRightTransport (hg : IsEtale B S hS g.hom) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u} (baseChangeRightRingSheaf B S hS f g hg) :=
  pullbackModuleFunctor (SmallEtale.topology B S hS Y'.1)
    (smallEtaleDirectImage B S hS f ⋙ smallEtaleSetRestriction B S hS g hg)
    (structureRingSheaf B S hS X)

/-- **The right-hand side of Stacks 03LX, as a transport of modules.** Restricting the direct
image of modules along `f` to the small étale site of `Y'` is the transport of `𝒪_X`-modules
along the composite `f_* ⋙ (-)|_{Y'}` of functors of sheaves of sets, with the restriction of
the structure map `f^♯` of Stacks 03G8 as its structure map.

This holds by `rfl`: étale restriction only reindexes sections, so it commutes both with the
transport of modules along a finite-product-preserving functor of sheaves of sets and with
restriction of scalars. -/
theorem modulePushforward_comp_etaleModulePullback_eq (hg : IsEtale B S hS g.hom) :
    modulePushforward B S hS f ⋙ etaleModulePullback B S hS g hg =
      baseChangeRightTransport B S hS f g hg ⋙
        SheafOfModules.restrictScalars.{u}
          ((smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f)) :=
  rfl

/-- The comparison of `f'_*𝒪_{X'}` with the iterated transport of `𝒪_X`: the image under
transport along `f'_*` of `AlgebraicGeometry.Space.etaleStructureRingIso`. -/
noncomputable abbrev etaleBaseChangeRingComparison (hi : IsEtale B S hS i.hom) :
    baseChangeIteratedRingSheaf B S hS i f' hi ≅ structureRingSheafDirectImage B S hS f' :=
  (pullbackRingSheafFunctor (SmallEtale.topology B S hS Y'.1)
    (smallEtaleDirectImage B S hS f')).mapIso (etaleStructureRingIso B S hS i hi)

/-- The comparison of the iterated transport of `𝒪_X` with its transport along the composite
functor in one step. -/
noncomputable abbrev etaleBaseChangeRingCompIso (hi : IsEtale B S hS i.hom) :
    baseChangeIteratedRingSheaf B S hS i f' hi ≅ baseChangeLeftRingSheaf B S hS i f' hi :=
  pullbackRingSheafCompIso (SmallEtale.topology B S hS Y'.1)
    (SmallEtale.topology B S hS X'.1) (smallEtaleDirectImage B S hS f')
    (smallEtaleSetRestriction B S hS i hi) (structureRingSheaf B S hS X)

/-- The structure map `(f')^♯ : 𝒪_{Y'} ⟶ f'_*𝒪_{X'}` of Stacks 03G8, read as a structure map
for the transport of `𝒪_X` along the composite `(-)|_{X'} ⋙ f'_*` through the two ring
comparisons above. -/
noncomputable def baseChangeStructureSharp (hi : IsEtale B S hS i.hom) :
    structureRingSheaf B S hS Y' ⟶ baseChangeLeftRingSheaf B S hS i f' hi :=
  (structureSharp B S hS f' ≫ (etaleBaseChangeRingComparison B S hS i f' hi).inv) ≫
    (etaleBaseChangeRingCompIso B S hS i f' hi).hom

/-- The comparison of the sheaves of rings transported along the two sides of base change,
induced by `AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso`.  It is the identity
on underlying sheaves of sets. -/
noncomputable def baseChangeRingMap (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    baseChangeLeftRingSheaf B S hS i f'
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⟶
      baseChangeRightRingSheaf B S hS f g hg :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y'.1)
    (structureRingSheaf B S hS X)
    (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom

/-- **The left-hand side of Stacks 03LX, as a transport of modules.** The direct image along
`f'` of the étale restriction to `X'` of an `𝒪_X`-module is the transport of `𝒪_X`-modules
along the composite `(-)|_{X'} ⋙ f'_*` of functors of sheaves of sets, with
`AlgebraicGeometry.Space.baseChangeStructureSharp` as its structure map.

Three general facts do the work: étale restriction of modules is the transport of
modules along the restriction functor (`Stacks.Sheaves.ToposPullback.restrictionModuleIso`),
restriction of scalars commutes with the transport of modules
(`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorRestrictScalarsIso`), and an iterated
transport is the transport along the composite
(`Stacks.Sheaves.ToposPullback.pullbackModuleCompIso`).  Each intermediate isomorphism and each
restriction-of-scalars functor is named with its type written out and every reassociation is
explicit: a metavariable in a functor-composition position here either leaves the category
instance of a `SheafOfModules` unsynthesizable or drives the unifier through
`CategoryTheory.Functor.objPreimage` and `Classical.choose`. -/
noncomputable def modulePushforwardEtaleBaseChangeLeftIso (hi : IsEtale B S hS i.hom) :
    etaleModulePullback B S hS i hi ⋙ modulePushforward B S hS f' ≅
      baseChangeLeftTransport B S hS i f' hi ⋙
        SheafOfModules.restrictScalars (baseChangeStructureSharp B S hS i f' hi) :=
  let rho : etaleRestrictionRingSheaf B S hS i hi ⟶ structureRingSheaf B S hS X' :=
    (etaleStructureRingIso B S hS i hi).hom
  let bet : baseChangeIteratedRingSheaf B S hS i f' hi ≅
      structureRingSheafDirectImage B S hS f' := etaleBaseChangeRingComparison B S hS i f' hi
  let cI : baseChangeIteratedRingSheaf B S hS i f' hi ≅
      baseChangeLeftRingSheaf B S hS i f' hi := etaleBaseChangeRingCompIso B S hS i f' hi
  let c : structureRingSheaf B S hS Y' ⟶ baseChangeIteratedRingSheaf B S hS i f' hi :=
    structureSharp B S hS f' ≫ bet.inv
  let RM : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X'.1 X'.2 :=
    restrictionModules (SmallEtale.topology B S hS X'.1) (SmallEtale.topology B S hS X.1)
      (smallEtalePostcomp B S hS i hi) (structureRingSheaf B S hS X)
  let T' : Modules.{u, u} B S hS X'.1 X'.2 ⥤
      SheafOfModules.{u} (structureRingSheafDirectImage B S hS f') :=
    pullbackModuleFunctor (SmallEtale.topology B S hS Y'.1) (smallEtaleDirectImage B S hS f')
      (structureRingSheaf B S hS X')
  let TP : SheafOfModules.{u} (etaleRestrictionRingSheaf B S hS i hi) ⥤
      SheafOfModules.{u} (baseChangeIteratedRingSheaf B S hS i f' hi) :=
    pullbackModuleFunctor (SmallEtale.topology B S hS Y'.1) (smallEtaleDirectImage B S hS f')
      (etaleRestrictionRingSheaf B S hS i hi)
  let PL : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (etaleRestrictionRingSheaf B S hS i hi) :=
    pullbackModuleFunctor (SmallEtale.topology B S hS X'.1)
      (smallEtaleSetRestriction B S hS i hi) (structureRingSheaf B S hS X)
  let TC : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) :=
    baseChangeLeftTransport B S hS i f' hi
  let RSrho : Modules.{u, u} B S hS X'.1 X'.2 ⥤
      SheafOfModules.{u} (etaleRestrictionRingSheaf B S hS i hi) :=
    SheafOfModules.restrictScalars rho
  let RSbet : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f') ⥤
      SheafOfModules.{u} (baseChangeIteratedRingSheaf B S hS i f' hi) :=
    SheafOfModules.restrictScalars bet.hom
  let RScI : SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) ⥤
      SheafOfModules.{u} (baseChangeIteratedRingSheaf B S hS i f' hi) :=
    SheafOfModules.restrictScalars cI.hom
  let RSc : SheafOfModules.{u} (baseChangeIteratedRingSheaf B S hS i f' hi) ⥤
      Modules.{u, u} B S hS Y'.1 Y'.2 := SheafOfModules.restrictScalars c
  let RSsharp : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f') ⥤
      Modules.{u, u} B S hS Y'.1 Y'.2 :=
    SheafOfModules.restrictScalars (structureSharp B S hS f')
  let RSaL : SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) ⥤
      Modules.{u, u} B S hS Y'.1 Y'.2 :=
    SheafOfModules.restrictScalars (baseChangeStructureSharp B S hS i f' hi)
  let m₁ : RM ⋙ (T' ⋙ RSbet) ≅ RM ⋙ (RSrho ⋙ TP) :=
    Functor.isoWhiskerLeft RM
      (pullbackModuleFunctorRestrictScalarsIso (SmallEtale.topology B S hS Y'.1)
        (smallEtaleDirectImage B S hS f') rho).symm
  let m₂ : RM ⋙ (RSrho ⋙ TP) ≅ (RM ⋙ RSrho) ⋙ TP :=
    (Functor.associator RM RSrho TP).symm
  let m₃ : (RM ⋙ RSrho) ⋙ TP ≅ PL ⋙ TP :=
    Functor.isoWhiskerRight
      (restrictionModuleIso (SmallEtale.topology B S hS X'.1)
        (SmallEtale.topology B S hS X.1) (smallEtalePostcomp B S hS i hi)
        (structureRingSheaf B S hS X)).symm TP
  let m₄ : PL ⋙ TP ≅ TC ⋙ RScI :=
    pullbackModuleCompIso (SmallEtale.topology B S hS Y'.1)
      (SmallEtale.topology B S hS X'.1) (smallEtaleDirectImage B S hS f')
      (smallEtaleSetRestriction B S hS i hi) (structureRingSheaf B S hS X)
  let L1 : RM ⋙ (T' ⋙ RSbet) ≅ TC ⋙ RScI := m₁ ≪≫ m₂ ≪≫ m₃ ≪≫ m₄
  let hc : c ≫ bet.hom = structureSharp B S hS f' :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun φ ↦ structureSharp B S hS f' ≫ φ) bet.inv_hom_id).trans
        (Category.comp_id _))
  let n₁ : RM ⋙ T' ⋙ RSsharp ≅ RM ⋙ T' ⋙ (RSbet ⋙ RSc) :=
    eqToIso (congrArg (fun F ↦ RM ⋙ T' ⋙ F)
      ((congrArg SheafOfModules.restrictScalars.{u} hc).symm.trans
        (SheafOfModules.restrictScalars_comp c bet.hom).symm))
  let n₂ : RM ⋙ T' ⋙ (RSbet ⋙ RSc) ≅ RM ⋙ ((T' ⋙ RSbet) ⋙ RSc) :=
    Functor.isoWhiskerLeft RM (Functor.associator T' RSbet RSc).symm
  let n₃ : RM ⋙ ((T' ⋙ RSbet) ⋙ RSc) ≅ (RM ⋙ (T' ⋙ RSbet)) ⋙ RSc :=
    (Functor.associator RM (T' ⋙ RSbet) RSc).symm
  let n₄ : (RM ⋙ (T' ⋙ RSbet)) ⋙ RSc ≅ (TC ⋙ RScI) ⋙ RSc :=
    Functor.isoWhiskerRight L1 RSc
  let n₅ : (TC ⋙ RScI) ⋙ RSc ≅ TC ⋙ (RScI ⋙ RSc) := Functor.associator TC RScI RSc
  let n₆ : TC ⋙ (RScI ⋙ RSc) ≅ TC ⋙ RSaL :=
    eqToIso (congrArg (fun F ↦ TC ⋙ F) (SheafOfModules.restrictScalars_comp c cI.hom))
  n₁ ≪≫ n₂ ≪≫ n₃ ≪≫ n₄ ≪≫ n₅ ≪≫ n₆

/-! ### Étale base change for the direct image of modules -/

/-- Étale restriction of modules is additive: it only reindexes sections, so it is the identity
on the addition of module morphisms. -/
theorem etaleModulePullback_additive {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (etaleModulePullback.{u, m} B S hS h hh).Additive where
  map_add := rfl

/-- **Stacks 03LX, ordinary direct image, conditional on the base-change compatibility of the
structure maps of Stacks 03G8.**  Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Then for every `𝒪_X`-module `F`

`f'_*(F|_{X'}) = (f_*F)|_{Y'}`

in `Mod(𝒪_{Y'})`, naturally in `F`.

The underlying isomorphism of sheaves of sets is
`AlgebraicGeometry.Space.smallEtaleSetPushforwardBaseChangeIso`, Stacks 03LR, part (1).  What
the hypothesis `hsharp` adds is that this isomorphism is `𝒪_{Y'}`-linear, that is that the
structure map `(f')^♯` of the base-changed morphism corresponds under it to the étale
restriction of the structure map `f^♯`.  That compatibility is a statement about Stacks 03G8
and is **not** proved in this development:
`StacksFrontier/AlgebraicGeometry/Spaces/StructureMapSharp.lean` constructs `f^♯` for one morphism
at a time and proves no compatibility of the family, not even the composition law `(g ≫ f)^♯`.
It is therefore carried here as an explicit named hypothesis rather than assumed silently, and
this declaration does **not** carry the Stacks 03LX attribute:
the unconditional form is exactly this isomorphism with `hsharp` discharged. -/
noncomputable def modulePushforwardEtaleBaseChangeIsoOfStructureSharp
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom)
    (hsharp : baseChangeStructureSharp B S hS i f'
            (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ≫
          baseChangeRingMap B S hS i f' f g sq hg =
        (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f)) :
    etaleModulePullback B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ⋙
        modulePushforward B S hS f' ≅
      modulePushforward B S hS f ⋙ etaleModulePullback B S hS g hg :=
  let hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  let aL : structureRingSheaf B S hS Y' ⟶ baseChangeLeftRingSheaf B S hS i f' hi :=
    baseChangeStructureSharp B S hS i f' hi
  let gam : baseChangeLeftRingSheaf B S hS i f' hi ⟶ baseChangeRightRingSheaf B S hS f g hg :=
    baseChangeRingMap B S hS i f' f g sq hg
  let aR : structureRingSheaf B S hS Y' ⟶ baseChangeRightRingSheaf B S hS f g hg :=
    (smallEtaleRingRestriction B S hS g hg).map (structureSharp B S hS f)
  let TC : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) :=
    baseChangeLeftTransport B S hS i f' hi
  let TR : Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (baseChangeRightRingSheaf B S hS f g hg) :=
    baseChangeRightTransport B S hS f g hg
  let RSgam : SheafOfModules.{u} (baseChangeRightRingSheaf B S hS f g hg) ⥤
      SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) :=
    SheafOfModules.restrictScalars gam
  let RSaL : SheafOfModules.{u} (baseChangeLeftRingSheaf B S hS i f' hi) ⥤
      Modules.{u, u} B S hS Y'.1 Y'.2 := SheafOfModules.restrictScalars aL
  let RSaR : SheafOfModules.{u} (baseChangeRightRingSheaf B S hS f g hg) ⥤
      Modules.{u, u} B S hS Y'.1 Y'.2 := SheafOfModules.restrictScalars aR
  let p₂ : TC ≅ TR ⋙ RSgam :=
    pullbackModuleFunctorIsoOfNatIso (SmallEtale.topology B S hS Y'.1)
      (structureRingSheaf B S hS X)
      (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg) gam
      (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y'.1)
        (structureRingSheaf B S hS X)
        (smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom)
  let p₃ : TC ⋙ RSaL ≅ (TR ⋙ RSgam) ⋙ RSaL := Functor.isoWhiskerRight p₂ RSaL
  let p₄ : (TR ⋙ RSgam) ⋙ RSaL ≅ TR ⋙ (RSgam ⋙ RSaL) := Functor.associator TR RSgam RSaL
  let p₅ : TR ⋙ (RSgam ⋙ RSaL) ≅ TR ⋙ RSaR :=
    eqToIso (congrArg (fun F ↦ TR ⋙ F)
      ((SheafOfModules.restrictScalars_comp aL gam).trans
        (congrArg SheafOfModules.restrictScalars.{u} hsharp)))
  modulePushforwardEtaleBaseChangeLeftIso B S hS i f' hi ≪≫ p₃ ≪≫ p₄ ≪≫ p₅ ≪≫
    eqToIso (modulePushforward_comp_etaleModulePullback_eq B S hS f g hg).symm

/-- Étale restriction of modules preserves finite limits: it is
`SheafOfModules.pushforward` for a continuous functor of sites, and the direct image of sheaves
of modules along such a functor is left exact (Stacks 04BD, part (2), left exact half). -/
theorem preservesFiniteLimits_etaleModulePullback {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Limits.PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS h hh) :=
  show Limits.PreservesFiniteLimits
    (restrictionModules (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)
      (smallEtalePostcomp B S hS h hh) (structureRingSheaf B S hS V)) from inferInstance

/-- Étale restriction of modules preserves finite colimits: small étale postcomposition is both
continuous and cocontinuous, so restriction of modules along it preserves every colimit indexed
in the universe of the structure rings.

The module universe here is the universe `u` of the structure rings and not the free universe of
`AlgebraicGeometry.Space.etaleModulePullback`, because
`Stacks.SheafOfModules.pushforward_preservesColimits` states the preservation of colimits with
the universe of the module sections *equal* to the universe of the sheaves of rings. -/
theorem preservesFiniteColimits_etaleModulePullback {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    Limits.PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS h hh) :=
  have : Limits.PreservesColimitsOfSize.{u, u} (etaleModulePullback.{u, u} B S hS h hh) :=
    Stacks.SheafOfModules.pushforward_preservesColimits.{u + 1, u, u, u + 1, u, u}
      (J := SmallEtale.topology B S hS U.1) (K := SmallEtale.topology B S hS V.1)
      (R := structureRingSheaf B S hS V)
      (smallEtalePostcomp B S hS h hh) (𝟙 (structureRingSheaf B S hS U))
  Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- Étale restriction of module sheaves preserves short exact sequences: it is exact, being
left exact by `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModulePullback` and right
exact by `AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback`.

The module universe is `u`, for the reason recorded in the implementation notes of this file. -/
theorem etaleModulePullback_shortExact {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom)
    (T : ShortComplex (Modules.{u, u} B S hS V.1 V.2)) (hT : T.ShortExact) :
    letI : (etaleModulePullback.{u, u} B S hS h hh).Additive :=
      etaleModulePullback_additive B S hS h hh
    (T.map (etaleModulePullback.{u, u} B S hS h hh)).ShortExact :=
  let : (etaleModulePullback.{u, u} B S hS h hh).Additive :=
    etaleModulePullback_additive B S hS h hh
  have := preservesFiniteLimits_etaleModulePullback B S hS h hh
  have := preservesFiniteColimits_etaleModulePullback B S hS h hh
  hT.map_of_exact _

/-! ### The footnote: the pullback-square comparison -/

/-- **Stacks 03LX, the footnote.** For a commutative — in particular a cartesian — square

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

of algebraic spaces, the inverse image of modules around the square agrees:
`(f')^*(G|_{Y'}) = (f^*G)|_{X'}` for every `𝒪_Y`-module `G`, naturally in `G`.

**Both restrictions are read as the inverse image of modules**, so all four functors in the
statement are `AlgebraicGeometry.Space.modulePullback` — the source's `G|_{Y'}` is `g^*G` and
its `(-)|_{X'}` is `i^*`.  That is the reading of Stacks 03LW, which the source's own footnote
invokes to derive this identity, and which this development does **not** supply: no comparison
of `AlgebraicGeometry.Space.modulePullback` with the étale restriction
`AlgebraicGeometry.Space.etaleModulePullback` used elsewhere in this file is proved anywhere,
and the two are different functors (the tensor inverse image of Stacks 03D6, part (2) against
restriction along `AlgebraicGeometry.Space.smallEtalePostcomp`).  So what is proved here is the
footnote in the inverse-image reading, not in the restriction reading, and the attribute says so.

No étaleness is used: as in the source, the comparison is the Stacks 03LU composition
isomorphism `AlgebraicGeometry.Space.modulePullbackCompIso` for the two factorizations of the
diagonal `X' ⟶ Y` of the square, glued by the commutativity `sq.w` of the square; only `sq.w`
is consumed, so the cartesian hypothesis is stronger than the proof needs.  The module universe
is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePullback` exists. -/
@[stacks 03LX "the footnote, with both restrictions read as the inverse image of modules
  (Stacks 03LW)"]
noncomputable def modulePullbackSquareIso (sq : IsPullback i f' f g) :
    modulePullback B S hS g ⋙ modulePullback B S hS f' ≅
      modulePullback B S hS f ⋙ modulePullback B S hS i :=
  modulePullbackCompIso B S hS f' g ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y => modulePullback B S hS h) sq.w.symm) ≪≫
    (modulePullbackCompIso B S hS i f).symm

end AlgebraicGeometry.Space

end
