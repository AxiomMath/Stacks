module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChangeDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeSquareComparison

/-!
# The square of Stacks 05ZC and Stacks 05ZD commutes

Let `k : U' ⟶ U`, `r : U ⟶ V`, `r' : U' ⟶ V'`, `l : V' ⟶ V` be morphisms of schemes of the big
fppf site over `S` forming a commutative square, and let `C` be an `𝒪`-module on the small étale
site of the represented algebraic space `yoneda.obj U'`.  The input of Stacks 05ZC and
Stacks 05ZD is that restriction of derivations along `k`,
`AlgebraicGeometry.Space.restrictDerivation`, is bijective; the route to it recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeZariskiDerivation.lean` factors
that map through the square

```
Derivation'_{yoneda.obj V}(k_*C)  ←--- restrictDerivation ---  (Ω_{U'/V'} ⟶ C)
          |                                                        |
schemeZariskiDerivationEquiv r                            schemeZariskiHomEquiv r'
          v                                                        v
SheafDerivation(restrictModule_U(Ψ_U(k_*C))) -Φ→ (Ω_{U/V} ⟶ (k_s)_*(restrictModule_{U'}(Ψ_{U'}C)))
```

whose horizontal on the right is restriction of derivations of *schemes* along the morphism of
schemes underlying `k`, `AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation` — Morphisms,
Lemma 01V0 in derivation form — and whose comparison `Φ` is
`AlgebraicGeometry.Space.representedSquareComparison`.

**This file proves that square commutes**:
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation`.

## How it is proved

By `PresheafOfModules.Derivation.ext` the identity is one of values over the Zariski opens `W` of
the scheme `U`, and both sides are then read by existing lemmas:

* the left-hand side is `Φ` on sections over `W`,
  `AlgebraicGeometry.Space.representedSquareComparison_app_apply`, composed with the value
  description of the bottom horizontal,
  `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_d`, and with the chart formula
  `AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` for
  `AlgebraicGeometry.Space.restrictDerivation` — which the named chart comparison
  `AlgebraicGeometry.Space.representedSquareChartComparison` is identified with by
  `AlgebraicGeometry.Space.representedSquareChartComparison_eq`.  It comes out as `g` of the
  universal differential of the pullback of `a ∈ Γ(U, W)` along the cartesian projection
  `W ×_U U' ⟶ W`, restricted along
  `AlgebraicGeometry.Space.representedSquareOpensNat`;
* the right-hand side is `AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d` followed by
  the *characterising equation* of `AlgebraicGeometry.Space.schemeZariskiHomEquiv`,
  `AlgebraicGeometry.Space.postcomp_schemeZariskiHomEquiv`.  It comes out as `g` of the universal
  differential of `k♯a`, read on the preimage open.

What is left is one identity about regular functions,
`AlgebraicGeometry.Space.representedSquareOpensNat_chartPullback`: the pullback of `a` along
`W ×_U U' ⟶ W`, restricted along `AlgebraicGeometry.Space.representedSquareOpensNat`, is `k♯a` on
the preimage open.  It is proved by identifying the two chart comparisons involved —
`AlgebraicGeometry.Space.functor_map_representedSquareOpensNat_comp` — and then quoting
`AlgebraicGeometry.SmallEtale.map_structureSharp_opens_eq_pullbackSection`, the same identity on
the small étale site of the scheme `U'`.  The identification of the chart comparisons needs no
computation at all: both sides are morphisms into the base change of an *open*, whose structure
morphism is a monomorphism, so there is at most one
(`AlgebraicGeometry.SmallEtale.subsingleton_hom_baseChangeOpens`).

## Main results

* `AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation`: **the square
  commutes**, and
  `AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_schemeSpace`
  the same with the top edge spelled `AlgebraicGeometry.schemeSpaceMap`, which is what
  `AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` quantifies over.
* `AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_d`: the same
  on sections over an open of the scheme `U`.
* `AlgebraicGeometry.Space.representedSquareComparison_postcomp_d`: **the left-hand vertical
  followed by `Φ`, on sections**, and
  `AlgebraicGeometry.Space.restrictRelativeDerivation_schemeZariskiHomEquiv_d` **the right-hand
  vertical after the top horizontal, on sections**.
* `AlgebraicGeometry.Space.representedSquareOpensNat_chartPullback`: **the one identity about
  regular functions the square comes down to**, and
  `AlgebraicGeometry.Space.representedSquareOpensNat_gammaPullback` the same with the pullback
  written as pullback of global functions.
* `AlgebraicGeometry.Space.functor_map_representedSquareOpensNat_comp`: the restriction along
  which `Φ` acts on sections, read on the scheme's small étale site, **is** the identification of
  the base change of an open with the preimage open.
* `AlgebraicGeometry.Space.postcomp_schemeZariskiHomEquiv`: the characterising equation of
  `AlgebraicGeometry.Space.schemeZariskiHomEquiv`.

## Implementation notes

**`θ = schemeZariskiHomEquiv r' C D` is used only through its characterising equation and is
never computed.**  `AlgebraicGeometry.Space.schemeZariskiHomEquiv` is
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` followed by the `.symm` of an
`Equiv.ofBijective`, so its value is a `Function.surjInv`: a bijection assembled from a universal
property cannot describe its own values.  What is available instead is `Equiv.apply_symm_apply`
for that bijection, which says that postcomposing the universal relative derivation of `U'/V'`
with `θ` returns the derivation `θ` was built from; that is
`AlgebraicGeometry.Space.postcomp_schemeZariskiHomEquiv`, and both of its sides are computable.

**Every reading is stated at a variable section over a variable open.**  Reconciling
`Γ(𝒪_{U'_étale}, inverse_{U'}(W'))` with `Γ(𝒪_{U'}, W')` — the structure sheaf of the small étale
site of `yoneda.obj U'` against the structure sheaf of the small étale site of the scheme `U'`,
across `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` — is the expensive type check
here, and it has to happen once rather than once per factor.  Composing
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_d` with
`PresheafOfModules.Derivation.postcomp_d_apply` *at the concrete open and section of the square*
exhausts the 200000-heartbeat budget at `whnf`; the same composition at a variable open and a
variable section (`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_postcomp_d`) costs a
fraction of it, and the concrete instance is then an instantiation rather than a unification.
The same discipline, for the same reason, is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareComparison.lean` record for
the factors of `Φ`.

`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` cannot be made `local irreducible`
here, unlike in that file: the statements below *do* need the identification of the two structure
sheaves, which is exactly the defeq it hides, and with it opaque they do not typecheck.

**The heartbeat budget is per declaration, and that is the whole difficulty of this file.**  Four
arrangements of exactly the steps below died at `whnf` or `isDefEq` for no other reason than that
the statement of one declaration plus three of its steps already accounted for most of 200000,
leaving nothing for the fourth.  Hence the shape of the file: the left-hand reading stops at the
pullback along the cartesian projection
(`AlgebraicGeometry.Space.representedSquareComparison_postcomp_d`), the identification of that
regular function with `k♯a` is a declaration of its own
(`AlgebraicGeometry.Space.universalDerivation_d_representedSquareOpensNat`), and the composition
of the two readings is a third
(`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_d`).  Splitting
a declaration is the first thing to try when one of these statements does not fit; nothing here
needed a different proof.

**Never let the two spellings of the top edge meet underneath a chart comparison.**
`AlgebraicGeometry.Space.representedSpaceMap B S hS k` and `AlgebraicGeometry.schemeSpaceMap k`
are the same term up to two delta steps, but unifying
`AlgebraicGeometry.Space.modulePushforwardChartIso B S hS f hk` at the two spellings of `f`
exhausts the budget.  Everything on the chart side of this file is therefore written at
`representedSpaceMap` — the spelling `AlgebraicGeometry.Space.representedSquareChartComparison_eq`,
`AlgebraicGeometry.Space.representedSquareOpensNat` and
`AlgebraicGeometry.Space.representedSquareComparison` already use — and the two spellings are
reconciled once, in
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_schemeSpace`,
where no chart comparison is in the way; there it costs a second.

**Write the action of a morphism of modules on sections the way the lemma you will compose with
writes it.**  `AlgebraicGeometry.Space.representedSquareComparison_app_apply` applies the
comparison to a section by plain application, which elaborates to `ConcreteCategory.hom`, while
`.hom` elaborates to `ModuleCat.Hom.hom`; the two are definitionally equal and bridging them at a
concrete object of the small étale site is unaffordable.  So
`AlgebraicGeometry.Space.representedSquareChartComparison_restrictDerivation_d` is stated with the
chart comparison applied plainly, and the `g`-side with `.hom`, which is how
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` states it.

**The orientation of an equation between two spellings of one section matters.**
`AlgebraicGeometry.Space.representedSquareOpensNat_gammaPullback` is stated with
`AlgebraicGeometry.SmallEtale.pullbackSection` on the *left*, so that the equation carries the
scheme-level section type.  Written the other way round it carries the type of a section of the
structure sheaf of the small étale site of `yoneda.obj U'`, and a consumer then pays for the
reconciliation of the two at a concrete object of the site.

## References

* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZD](https://stacks.math.columbia.edu/tag/05ZD)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0), the scheme-level
  restriction of derivations which is the right-hand vertical.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4), base change
  of étale scheme charts.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the passage to the small
  Zariski site which the two verticals are built from.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.SectionsComponents

universe v₁ u₁

/-- Restriction along a composite, on sections of a presheaf of commutative rings.  Stated with
the two morphisms variables, so that a use site does not have to weak-head-normalise a concrete
one. -/
theorem commRingPresheaf_map_comp_apply {C : Type u₁} [Category.{v₁} C]
    (F : Cᵒᵖ ⥤ CommRingCat.{u}) {A₁ A₂ A₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (x : F.obj (op A₃)) :
    (F.map (f ≫ g).op).hom x = (F.map f.op).hom ((F.map g.op).hom x) := by
  rw [op_comp, F.map_comp]
  rfl

end Stacks.SectionsComponents

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} (k : U' ⟶ U)

/-- **The restriction along which `Φ` acts on sections, read on the small étale site of the
scheme `U'`, is the identification of the base change of an open with the preimage open.**

Both sides are morphisms into the base change along `k` of the object of the small étale site of
the scheme `U` which the open `W` names, and the structure morphism of such a base change is a
monomorphism — the base change of an open immersion — so there is at most one such morphism. -/
theorem functor_map_representedSquareOpensNat_comp
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (representedSmallEtaleEquivalence B S hS U').functor.map
          (representedSquareOpensNat B S hS k
            (relativelyRepresentable_yoneda_map B S hS k) W) ≫
        (representedSmallEtaleBaseChangeComponent B S hS k
            (relativelyRepresentable_yoneda_map B S hS k)
          ((representedSmallEtaleEquivalence B S hS U).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))).hom =
      (_root_.AlgebraicGeometry.SmallEtale.baseChangeOpensObjIso (associatedBigEtaleSite B)
        k.left W).hom :=
  (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_baseChangeOpens
    (associatedBigEtaleSite B) k.left W _).allEq _ _

/-- **The one identity about regular functions that the square of Stacks 05ZC and Stacks 05ZD
comes down to.**  Let `a` be a regular function on an open `W` of the scheme `U`.  Pulling `a`
back along the cartesian projection `W ×_U U' ⟶ W` — which is what the chart formula
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` produces — and then
restricting along `AlgebraicGeometry.Space.representedSquareOpensNat` gives the image of `a`
under `k♯`, read as a global function on the preimage open, which is what
`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d` produces.

By `AlgebraicGeometry.Space.chartPullback_chartBaseChangeArrow` the pullback along the projection
is the structure map of the morphism of small étale ringed sites of `k.left`, restricted along the
comparison of the two base changes of the chart; the two restrictions then compose into the
restriction along
`AlgebraicGeometry.Space.functor_map_representedSquareOpensNat_comp`, and
`AlgebraicGeometry.SmallEtale.map_structureSharp_opens_eq_pullbackSection` is the identity that
remains, on the small étale site of the scheme `U'`. -/
theorem representedSquareOpensNat_chartPullback
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    ((structurePresheaf B S hS (yoneda.obj U')).map
          (representedSquareOpensNat B S hS k
            (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
        (chartPullback B S hS (schemeSpaceMap k)
          ((representedSmallEtaleEquivalence B S hS U).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))
          (chartBaseChangeArrow B S hS (schemeSpaceMap k)
            (relativelyRepresentable_yoneda_map B S hS k)
            ((representedSmallEtaleEquivalence B S hS U).inverse.obj
              ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)) =
      _root_.AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
        U'.left.property
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left) W a := by
  refine Eq.trans (congrArg ((structurePresheaf B S hS (yoneda.obj U')).map
      (representedSquareOpensNat B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
    (chartPullback_chartBaseChangeArrow B S hS k
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)) _)) ?_
  refine Eq.trans (Stacks.SectionsComponents.commRingPresheaf_map_comp_apply
    (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
    ((representedSmallEtaleEquivalence B S hS U').functor.map
      (representedSquareOpensNat B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) W))
    (representedSmallEtaleBaseChangeComponent B S hS k
        (relativelyRepresentable_yoneda_map B S hS k)
      ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))).hom _).symm ?_
  refine Eq.trans (commRingStructureSheaf_map_congr_apply
    B ((BigFppfOver.toScheme B S hS).obj U') U'.left.property
    (functor_map_representedSquareOpensNat_comp B S hS k W) _) ?_
  exact _root_.AlgebraicGeometry.SmallEtale.map_structureSharp_opens_eq_pullbackSection
    (associatedBigEtaleSite B) k.left W a

/-- **The characterising equation of `AlgebraicGeometry.Space.schemeZariskiHomEquiv`**:
postcomposing the universal relative derivation of the morphism of schemes underlying `α` with
the morphism `θ` attached to a derivation `D` returns the Zariski derivation `D` restricts to.

This is `Equiv.apply_symm_apply` for the `Equiv.ofBijective` built from the universal property of
`Ω_{U/V}`, and it is the *only* way `θ` is used: `schemeZariskiHomEquiv` is
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` followed by the `.symm` of that
`Equiv.ofBijective`, so its value is a `Function.surjInv` and nothing reduces through it. -/
theorem postcomp_schemeZariskiHomEquiv {T T' : BigFppfOver B S hS} (α : T ⟶ T')
    (G : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (D : G.val.Derivation' (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom) :
    (Scheme.Hom.universalRelativeDerivation
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            α.left)).postcomp (schemeZariskiHomEquiv B S hS α G D).val =
      schemeZariskiDerivationEquiv B S hS α G D :=
  (Equiv.ofBijective _
    (_root_.AlgebraicGeometry.SmallEtale.bijective_universalRelativeDerivation_postcomp
      (associatedBigEtaleSite B) α.left _)).apply_symm_apply _

variable {V V' : BigFppfOver B S hS} (r : U ⟶ V) (r' : U' ⟶ V') (l : V' ⟶ V)

/-- **The bottom horizontal at a derivation which is itself a postcomposition.**  Over an open
`W` of the scheme `U'`, the Zariski derivation attached to `d_{U'/V'}` followed by
`g : Ω_{U'/V'} ⟶ C` takes the value `g` takes on the universal differential of the global
functions of the open subscheme `W`.

This is `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_d` and
`PresheafOfModules.Derivation.postcomp_d_apply` composed, and it is kept in a declaration of its
own **at a variable open and a variable section**: that is where the sections of the structure
sheaf of the small étale site of `yoneda.obj U'` over `inverse_{U'}(W)` are reconciled with the
sections of the structure sheaf of the small étale site of the scheme `U'` over `W`, and the same
composition carried out at the concrete open and section of the square exhausts the heartbeat
budget. -/
theorem schemeZariskiDerivationEquiv_postcomp_d
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (W : ((BigFppfOver.toScheme B S hS).obj U').Opens)
    (b : Γ((BigFppfOver.toScheme B S hS).obj U', W)) :
    (schemeZariskiDerivationEquiv B S hS r' C
        ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val)).d b =
      (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj W)))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).hom.app (op W)).hom b)) := by
  refine Eq.trans (schemeZariskiDerivationEquiv_d B S hS r' C
    ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val) b) ?_
  exact PresheafOfModules.Derivation.postcomp_d_apply
    (universalDerivation B S hS (schemeSpaceMap r')) g.val _

/-- **The right-hand vertical and the top horizontal of the square, on sections over an open `W`
of the scheme `U`.**  The scheme-level restriction of derivations along the morphism of schemes
underlying `k`, applied to the morphism `θ` attached to `d_{U'/V'}` followed by `g`, sends a
regular function `a` on `W` to `g` of the universal differential of `k♯a`, read as a global
function on the preimage open.

It is `AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d`, the characterising equation
`AlgebraicGeometry.Space.postcomp_schemeZariskiHomEquiv` of `θ`, and
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_postcomp_d` at the preimage open. -/
theorem restrictRelativeDerivation_schemeZariskiHomEquiv_d
    (hs : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    (Scheme.Hom.restrictRelativeDerivation
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left) hs
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            ((representedModuleRestriction B S hS U').obj C))
          (schemeZariskiHomEquiv B S hS r' C
            ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val))).d a =
      (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              k.left ⁻¹ᵁ W))))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          (_root_.AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
            U'.left.property
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
            W a)) := by
  refine Eq.trans (Scheme.Hom.restrictRelativeDerivation_d
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left) _ _ _ hs
    _ _ W a) ?_
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
    (Scheme.Hom.universalRelativeDerivation
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left))
    (schemeZariskiHomEquiv B S hS r' C
      ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val)).val _).symm ?_
  refine Eq.trans (PresheafOfModules.Derivation.congr_d
    (postcomp_schemeZariskiHomEquiv B S hS r' C
      ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val)) _) ?_
  exact schemeZariskiDerivationEquiv_postcomp_d B S hS r' C g
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left ⁻¹ᵁ W)
    ((Scheme.Hom.app (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      k.left) W).hom a)

/-- **The bottom horizontal followed by a morphism of `𝒪_U`-modules, on sections over an open.**
Stated with the morphism, the module and the derivation all variables, which is what makes it
affordable where the morphism is `Φ`. -/
theorem schemeZariskiDerivationEquiv_postcomp_val_d {T T' : BigFppfOver B S hS} (α : T ⟶ T')
    (G : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (D : G.val.Derivation' (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom)
    {N : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (ψ : (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
        ((representedModuleRestriction B S hS T).obj G) ⟶ N)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, W)) :
    ((schemeZariskiDerivationEquiv B S hS α G D).postcomp ψ.val).d a =
      Scheme.Modules.Hom.app ψ W
        (D.d (X := op ((representedSmallEtaleEquivalence B S hS T).inverse.obj
            ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj W)))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).hom.app (op W)).hom a)) := by
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
    (schemeZariskiDerivationEquiv B S hS α G D) ψ.val a) ?_
  exact congrArg _ (schemeZariskiDerivationEquiv_d B S hS α G D a)

/-- **Restriction past a morphism out of the sheaf of differentials and past the universal
derivation.**  Naturality of the morphism moves the restriction inside, and a derivation commutes
with restriction (`PresheafOfModules.Derivation.d_map`), so the restriction lands on the regular
function.  Stated with the morphism of the small étale site and the section variables. -/
theorem map_hom_app_universalDerivation_d {X Y : AlgebraicSpaces B S hS} (p' : X ⟶ Y)
    (C : Modules.{u, u} B S hS X.1 X.2) (g : sheafOfDifferentials B S hS p' ⟶ C)
    {A₁ A₂ : SmallEtale B S hS X.1} (m : A₁ ⟶ A₂)
    (x : (structurePresheaf B S hS X.1).obj (op A₂)) :
    (C.val.map m.op).hom ((g.val.app (op A₂)).hom
        ((universalDerivation B S hS p').d x)) =
      (g.val.app (op A₁)).hom ((universalDerivation B S hS p').d
        (((structurePresheaf B S hS X.1).map m.op).hom x)) := by
  refine Eq.trans (PresheafOfModules.naturality_apply g.val m.op
    ((universalDerivation B S hS p').d x)).symm ?_
  exact congrArg (g.val.app (op A₁)).hom
    ((universalDerivation B S hS p').d_map m.op x).symm

/-- The chartwise pullback at the base-changed chart is pullback of global regular functions
along the cartesian projection, which is the form
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` produces. -/
theorem chartPullback_chartBaseChangeArrow_apply {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (t : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartPullback B S hS f V (chartBaseChangeArrow B S hS f hf V) t =
      (forget CommRingCat.{u}).map (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) t := by
  rw [chartPullback, chartBaseChangeMap_chartBaseChangeArrow]
  rfl


/-- `AlgebraicGeometry.Space.representedSquareOpensNat_chartPullback` read backwards, with the
pullback along the cartesian projection written as pullback of global regular functions — the form
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` produces.

The orientation matters: the equation is stated **at the type the scheme-level section has**, so
that a consumer instantiating a lemma whose sections are declared at that type matches it
syntactically.  Written the other way round, its type is the sections of the structure sheaf of
the small étale site of `yoneda.obj U'`, and the consumer then pays for the reconciliation of the
two at a concrete object of the site, which exceeds the heartbeat budget. -/
theorem representedSquareOpensNat_gammaPullback
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    _root_.AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
        U'.left.property
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left) W a =
      ((structurePresheaf B S hS (schemeSpace U').1).map
        (representedSquareOpensNat B S hS k (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
        ((forget CommRingCat.{u}).map (Scheme.Γ.map
          ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_yoneda_map B S hS k).snd
              ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).1.hom)).op)
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)) :=
  Eq.trans (representedSquareOpensNat_chartPullback B S hS k W a).symm
    (congrArg ((structurePresheaf B S hS (schemeSpace U').1).map
      (representedSquareOpensNat B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
      (chartPullback_chartBaseChangeArrow_apply B S hS (schemeSpaceMap k)
        (relativelyRepresentable_yoneda_map B S hS k)
          ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)))

/-- **The first factor of `Φ` at a module, on sections over an object of the small étale site of
`yoneda.obj U`, applied to the restriction of derivations.**  The named chart comparison is
`AlgebraicGeometry.Space.modulePushforwardChartIso` by
`AlgebraicGeometry.Space.representedSquareChartComparison_eq`, so the chart formula
`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d` applies: the value is `g`
of the universal differential of the pullback of the regular function along the cartesian
projection.

Stated with the object `V` and the section `t` variables, which is what keeps the elaborator from
normalising a concrete object of the small étale site here. -/
theorem representedSquareChartComparison_restrictDerivation_d
    {V V' : BigFppfOver B S hS} (r : U ⟶ V) (r' : U' ⟶ V') (l : V' ⟶ V)
    (hkr : representedSpaceMap B S hS k ≫ schemeSpaceMap r =
      schemeSpaceMap r' ≫ schemeSpaceMap l)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (T : SmallEtale B S hS (schemeSpace U).1)
    (t : (structurePresheaf B S hS (schemeSpace U).1).obj (op T)) :
    (representedSquareChartComparison B S hS k
          (relativelyRepresentable_yoneda_map B S hS k) C).val.app (op T)
        ((restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
          (schemeSpaceMap r') (schemeSpaceMap l) hkr C g).d t) =
      (g.val.app (op ((smallBaseChange B S hS (representedSpaceMap B S hS k)
          (relativelyRepresentable_yoneda_map B S hS k)).obj T))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          ((forget CommRingCat.{u}).map (Scheme.Γ.map
            ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_yoneda_map B S hS k).snd T.1.hom)).op) t)) := by
  refine Eq.trans (congrArg (fun m ↦ m.val.app (op T)
      ((restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
        (schemeSpaceMap r') (schemeSpaceMap l) hkr C g).d t))
    (representedSquareChartComparison_eq B S hS k
      (relativelyRepresentable_yoneda_map B S hS k) C)) ?_
  exact modulePushforwardChartIso_restrictDerivation_d B S hS
    (representedSpaceMap B S hS k) (relativelyRepresentable_yoneda_map B S hS k)
    (schemeSpaceMap r) (schemeSpaceMap r') (schemeSpaceMap l) hkr C g T t


/-- **The first factor of `Φ` on sections, followed by the restriction the other two factors
contribute.**  This is
`AlgebraicGeometry.Space.representedSquareChartComparison_restrictDerivation_d` with the
restriction moved past `g` and past the universal derivation by
`AlgebraicGeometry.Space.map_hom_app_universalDerivation_d`.

The three are read together, at a variable object `T` of the small étale site, a variable
restriction `m` and a variable regular function `t`: that is what keeps the cost of the
reconciliations here off the concrete instance of the square. -/
theorem representedSquareChartComparison_restrict_restrictDerivation_d
    (hkr : representedSpaceMap B S hS k ≫ schemeSpaceMap r =
      schemeSpaceMap r' ≫ schemeSpaceMap l)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (T : SmallEtale B S hS (schemeSpace U).1)
    {A : SmallEtale B S hS (schemeSpace U').1}
    (m : A ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS k)
      (relativelyRepresentable_yoneda_map B S hS k)).obj T)
    (t : (structurePresheaf B S hS (schemeSpace U).1).obj (op T)) :
    C.val.map m.op
        ((representedSquareChartComparison B S hS k
            (relativelyRepresentable_yoneda_map B S hS k) C).val.app (op T)
          ((restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
            (schemeSpaceMap r') (schemeSpaceMap l) hkr C g).d t)) =
      (g.val.app (op A)).hom ((universalDerivation B S hS (schemeSpaceMap r')).d
        (((structurePresheaf B S hS (schemeSpace U').1).map m.op).hom
          ((forget CommRingCat.{u}).map (Scheme.Γ.map
            ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_yoneda_map B S hS k).snd T.1.hom)).op) t))) := by
  refine Eq.trans (congrArg (fun y ↦ C.val.map m.op y)
    (representedSquareChartComparison_restrictDerivation_d B S hS k r r' l hkr C g T t)) ?_
  exact map_hom_app_universalDerivation_d B S hS (schemeSpaceMap r') C g m _

/-- **The left-hand vertical and the bottom horizontal of the square, on sections over an open
`W` of the scheme `U`.**  The restriction of derivations along the represented morphism `k`, read
on the small Zariski site of `U` and then carried across `Φ`, sends a regular function `a` on `W`
to `g` of the universal differential of the pullback of `a` along the cartesian projection
`W ×_U U' ⟶ W`, restricted along `AlgebraicGeometry.Space.representedSquareOpensNat`.

The route is: `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv_postcomp_val_d` for the
bottom horizontal followed by `Φ`; `AlgebraicGeometry.Space.representedSquareComparison_app_apply`
for `Φ` on sections over `W`; and
`AlgebraicGeometry.Space.representedSquareChartComparison_restrict_restrictDerivation_d` for the
chart formula together with the restriction the other two factors contribute.

The identification of that regular function with `k♯a` is the *next* declaration, not this one:
the heartbeat budget is per declaration, and the statement here together with its three steps
already accounts for most of it. -/
theorem representedSquareComparison_postcomp_d
    (hkr : representedSpaceMap B S hS k ≫ schemeSpaceMap r =
      schemeSpaceMap r' ≫ schemeSpaceMap l)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    ((schemeZariskiDerivationEquiv B S hS r
            ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)
            (restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
              (schemeSpaceMap r') (schemeSpaceMap l) hkr C g)).postcomp
        (representedSquareComparison B S hS k
          (relativelyRepresentable_yoneda_map B S hS k) C).val).d a =
      (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              k.left ⁻¹ᵁ W))))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          (((structurePresheaf B S hS (schemeSpace U').1).map
            (representedSquareOpensNat B S hS k
              (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
            ((forget CommRingCat.{u}).map (Scheme.Γ.map
            ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_yoneda_map B S hS k).snd
                ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).1.hom)).op)
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)))) := by
  refine Eq.trans (schemeZariskiDerivationEquiv_postcomp_val_d B S hS r
    ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)
    (restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
      (schemeSpaceMap r') (schemeSpaceMap l) hkr C g)
    (representedSquareComparison B S hS k (relativelyRepresentable_yoneda_map B S hS k) C) W a) ?_
  refine Eq.trans (representedSquareComparison_app_apply B S hS k
    (relativelyRepresentable_yoneda_map B S hS k) C W
    ((restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
      (schemeSpaceMap r') (schemeSpaceMap l) hkr C g).d
        (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)))
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a))) ?_
  exact representedSquareChartComparison_restrict_restrictDerivation_d B S hS k r r' l hkr C g
    ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W))
          (representedSquareOpensNat B S hS k (relativelyRepresentable_yoneda_map B S hS k) W)
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)

/-- **The regular function the left-hand vertical produces is `k♯a`.**  This is
`AlgebraicGeometry.Space.representedSquareOpensNat_gammaPullback` read under `g` and the universal
derivation.

It is a declaration of its own because the heartbeat budget is per declaration: the
reconciliation of the sections of the structure sheaf of the small étale site of `yoneda.obj U'`
over `inverse_{U'}(k⁻¹W)` with the sections of the structure sheaf of the small étale site of the
scheme `U'` over `k⁻¹W` costs a sizeable fraction of it at this concrete object, and
`AlgebraicGeometry.Space.representedSquareComparison_postcomp_d` has already spent the rest. -/
theorem universalDerivation_d_representedSquareOpensNat (r' : U' ⟶ V')
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              k.left ⁻¹ᵁ W))))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          (((structurePresheaf B S hS (schemeSpace U').1).map
            (representedSquareOpensNat B S hS k
              (relativelyRepresentable_yoneda_map B S hS k) W).op).hom
            ((forget CommRingCat.{u}).map (Scheme.Γ.map
            ((BigFppfOver.toScheme B S hS).map
              ((relativelyRepresentable_yoneda_map B S hS k).snd
                ((representedSmallEtaleEquivalence B S hS U).inverse.obj
      ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj W)).1.hom)).op)
          (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op W)).hom a)))) =
      (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              k.left ⁻¹ᵁ W))))).hom
        ((universalDerivation B S hS (schemeSpaceMap r')).d
          (_root_.AlgebraicGeometry.SmallEtale.pullbackSection (associatedBigEtaleSite B)
            U'.left.property
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
            W a)) :=
  congrArg (fun z ↦ (g.val.app (op ((representedSmallEtaleEquivalence B S hS U').inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              k.left ⁻¹ᵁ W))))).hom
      ((universalDerivation B S hS (schemeSpaceMap r')).d z))
    (representedSquareOpensNat_gammaPullback B S hS k W a).symm


/-- **The square of Stacks 05ZC and Stacks 05ZD commutes, on sections over an open `W` of the
scheme `U`.**  Both sides are `g` of the universal differential of `k♯a`, read on the preimage
open: the left-hand route by
`AlgebraicGeometry.Space.representedSquareComparison_postcomp_d` and
`AlgebraicGeometry.Space.universalDerivation_d_representedSquareOpensNat`, the right-hand route
by `AlgebraicGeometry.Space.restrictRelativeDerivation_schemeZariskiHomEquiv_d`. -/
theorem representedSquareDerivation_restrictRelativeDerivation_d
    (hkr : representedSpaceMap B S hS k ≫ schemeSpaceMap r =
      schemeSpaceMap r' ≫ schemeSpaceMap l)
    (hs : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, W)) :
    ((schemeZariskiDerivationEquiv B S hS r
            ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)
            (restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
              (schemeSpaceMap r') (schemeSpaceMap l) hkr C g)).postcomp
        (representedSquareComparison B S hS k
          (relativelyRepresentable_yoneda_map B S hS k) C).val).d a =
      (Scheme.Hom.restrictRelativeDerivation
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left) hs
          ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
            ((representedModuleRestriction B S hS U').obj C))
          (schemeZariskiHomEquiv B S hS r' C
            ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val))).d a :=
  ((representedSquareComparison_postcomp_d B S hS k r r' l hkr C g W a).trans
      (universalDerivation_d_representedSquareOpensNat B S hS k r' C g W a)).trans
    (restrictRelativeDerivation_schemeZariskiHomEquiv_d B S hS k r r' l hs C g W a).symm

/-- **The square of Stacks 05ZC and Stacks 05ZD commutes.**  For a commutative square of schemes
of the big fppf site over `S` and an `𝒪`-module `C` on the small étale site of `yoneda.obj U'`,
the restriction of derivations along `k` of `AlgebraicGeometry.Space.restrictDerivation`, read on
the small Zariski site of `U` by `AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` and then
carried across the comparison `Φ` of the two tags, is the *scheme-level* restriction of
derivations along the morphism of schemes underlying `k` — Morphisms, Lemma 01V0 in derivation
form — applied to the morphism out of `Ω_{U'/V'}` attached to `g` by
`AlgebraicGeometry.Space.schemeZariskiHomEquiv`.

By `PresheafOfModules.Derivation.ext` this is the identity of values
`AlgebraicGeometry.Space.representedSquareDerivation_restrictRelativeDerivation_d` over the
Zariski opens of `U`.

This is the commutativity half of the reduction of
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` to Morphisms, Lemma 01V0.  The
other half — that the three other maps of the square are bijections, hence so is this one — is
`AlgebraicGeometry.Space.bijective_restrictDerivation_schemeSquare` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareBijective.lean`. -/
theorem representedSquareDerivation_restrictRelativeDerivation
    (hkr : representedSpaceMap B S hS k ≫ schemeSpaceMap r =
      schemeSpaceMap r' ≫ schemeSpaceMap l)
    (hs : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C) :
    (schemeZariskiDerivationEquiv B S hS r
            ((modulePushforward B S hS (representedSpaceMap B S hS k)).obj C)
            (restrictDerivation B S hS (representedSpaceMap B S hS k) (schemeSpaceMap r)
              (schemeSpaceMap r') (schemeSpaceMap l) hkr C g)).postcomp
        (representedSquareComparison B S hS k (relativelyRepresentable_yoneda_map B S hS k) C).val =
      Scheme.Hom.restrictRelativeDerivation
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left) hs
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((representedModuleRestriction B S hS U').obj C))
        (schemeZariskiHomEquiv B S hS r' C
          ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val)) :=
  PresheafOfModules.Derivation.ext (funext fun W ↦ AddMonoidHom.ext fun a ↦
    representedSquareDerivation_restrictRelativeDerivation_d B S hS k r r' l hkr hs C g W.unop a)


/-- **The square of Stacks 05ZC and Stacks 05ZD commutes**, with the top edge written as
`AlgebraicGeometry.schemeSpaceMap` rather than as
`AlgebraicGeometry.Space.representedSpaceMap`.  The two are the same morphism — `schemeSpaceMap`
is a `def` and `representedSpaceMap` an `abbrev` with the same body — and this is the spelling
`AlgebraicGeometry.Space.IsSchemeSquareDerivationRestriction` quantifies over, so it is the one a
consumer of the square wants.

The conversion is kept in a declaration of its own: unifying the two spellings underneath
`AlgebraicGeometry.Space.modulePushforwardChartIso` exhausts the heartbeat budget, so every
reading above is carried out at `representedSpaceMap` and the spellings are reconciled once,
here, where no chart comparison is in the way. -/
theorem representedSquareDerivation_restrictRelativeDerivation_schemeSpace
    (hkr : schemeSpaceMap k ≫ schemeSpaceMap r = schemeSpaceMap r' ≫ schemeSpaceMap l)
    (hs : _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left =
      _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left ≫
        _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left)
    (C : Modules.{u, u} B S hS (schemeSpace U').1 (schemeSpace U').2)
    (g : sheafOfDifferentials B S hS (schemeSpaceMap r') ⟶ C) :
    (schemeZariskiDerivationEquiv B S hS r
            ((modulePushforward B S hS (schemeSpaceMap k)).obj C)
            (restrictDerivation B S hS (schemeSpaceMap k) (schemeSpaceMap r)
              (schemeSpaceMap r') (schemeSpaceMap l) hkr C g)).postcomp
        (representedSquareComparison B S hS k (relativelyRepresentable_yoneda_map B S hS k) C).val =
      Scheme.Hom.restrictRelativeDerivation
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) r'.left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) l.left) hs
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U') U'.left.property).obj
          ((representedModuleRestriction B S hS U').obj C))
        (schemeZariskiHomEquiv B S hS r' C
          ((universalDerivation B S hS (schemeSpaceMap r')).postcomp g.val)) :=
  representedSquareDerivation_restrictRelativeDerivation B S hS k r r' l hkr hs C g


end AlgebraicGeometry.Space

end
