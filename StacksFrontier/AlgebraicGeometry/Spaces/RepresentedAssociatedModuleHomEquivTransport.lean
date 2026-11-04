module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleHomEquivTransport

/-!
# The transposition of Stacks 03LU and the Zariski transposition correspond, in one square

`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleHomEquivTransport.lean` proves that the
hom-set bijections of the Zariski adjunction, the small-étale adjunction of the two *schemes* and
the spaces-level adjunction of Stacks 03LU correspond, **in two links** which meet on the small
étale site of the representing scheme.  A consumer that compares a spaces-level adjoint transpose
with a Zariski one — the identification of the first arrow of Stacks 05ZA with the first arrow of
Stacks 01UZ, which the proof of Stacks 05ZB needs — has to compose the two.

**This file composes them**, and it does so by assembling the two squares into one rather than
by chaining the two statements.  A square of adjunctions stacked on a second square whose two
vertical functors are the two halves of an equivalence is again a square of adjunctions, whose
two vertical left adjoints are `AlgebraicGeometry.Space.representedAssociatedModule` upstairs and
downstairs; so `Stacks.CategoryTheory.homEquiv_transport`, which is stated for an arbitrary
square, applies to it directly, and no identification of two separately transported transposes is
needed.

The comparison of the two composite left adjoints round the stacked square is
`AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso`, built from the two
squares' own comparisons — `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.Space.representedModulePullbackFunctorIso`.  The second of those is the step
that was missing until the first link was read in the forward direction: the two squares are
traversed in opposite directions, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleHomEquivTransport.lean` explain, and
turning the second one round is what
`AlgebraicGeometry.Space.isIso_representedModulePullbackMate` is for.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleAssociatedModuleAdjunction`: reading a Zariski
  module on a scheme of the site as an `𝒪`-module on the small étale site of the represented
  algebraic space is a left adjoint — the associated-module adjunction of Stacks 03DU (4)
  composed with the identification of the two small étale sites by
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` (the base's
  `AlgebraicGeometry.Space.representedAssociatedModuleAdjunction` composes with
  `AlgebraicGeometry.Space.representedModuleSiteEquivalence` instead).  Its left adjoint is
  `AlgebraicGeometry.Space.representedAssociatedModule`
  (`AlgebraicGeometry.Space.representedAssociatedModule_eq_comp`).
* `AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso`: **the comparison of
  the two composite left adjoints round the stacked square**, that is
  `(α^*𝓕)^a ≅ φ^*(𝓕^a)` naturally in `𝓕`, with `(-)^a` read on the small étale site of the
  represented algebraic space.  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`
  is the same comparison at one module, with no naturality.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate`: the comparison of right
  adjoints it determines, with
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_eq` for its definition.

## Main results

* `AlgebraicGeometry.Space.homEquiv_representedAssociatedModulePullback` and
  `AlgebraicGeometry.Space.homEquiv_symm_representedAssociatedModulePullback`: **the Zariski
  transposition and the spaces-level transposition of Stacks 03LU correspond** under
  `AlgebraicGeometry.Space.representedAssociatedModule`, in one statement.  The second is the
  form consumed by an arrow *defined* as an adjoint transpose, which is what the first arrow of
  the conormal sequence is at both ends.
* `AlgebraicGeometry.Space.unit_representedAssociatedModulePullback`: **the two units
  correspond**, the same correspondence read at the identity.  This is the form consumed by an
  arrow built as the adjoint transpose of a derivation *followed by the unit*, which is what the
  first arrow of the conormal sequence is at both ends: the derivation is compared by the
  universal property of the module of differentials and this compares what follows it.

## Implementation notes

**Three spellings matter, two of them for elaboration cost.**

* The two vertical adjunctions are **named as definitions**, not written out as
  `CategoryTheory.Adjunction.comp` of two others and not introduced as reducible abbreviations.
  With the composite written out underneath the hom-set bijection the statement below does not
  fit in the default heartbeat budget; this is the same phenomenon the implementation notes of
  `AlgebraicGeometry.Space.representedSmallEtaleModuleRestrictionAdjunction` record for the
  spelling of an equivalence's inverse.
* The comparison of right adjoints is **written out** in the three statements rather than named
  by `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate`.  Naming it does not merely
  cost: it exhausts the *recursion depth*, not the heartbeat budget, and this development raises
  neither limit.  `representedAssociatedModulePullbackMate_eq` moves between the two spellings
  and is `rfl`.
* The two vertical left adjoints are written as the composite
  `(-)^a ⋙ (representedSmallEtaleModuleEquivalence …).functor`, which is the spelling
  `CategoryTheory.Adjunction.comp` produces, and not as
  `AlgebraicGeometry.Space.representedAssociatedModule`, which is the same functor by `rfl`
  (`AlgebraicGeometry.Space.representedAssociatedModule_eq_comp`).

The vertical adjunctions of the stacked square are **not** adjoint equivalences — the
associated-module functor of Stacks 03DU (4) is a left adjoint with no left adjoint of its own —
so `Stacks.CategoryTheory.isIso_transportMate` does not apply and there is no counterpart here of
`AlgebraicGeometry.Space.isIso_representedModulePullbackMate`.  That is not needed: the
correspondence of the transpositions is an equality of two morphisms and is read in either
direction already.

No declaration here carries a `stacks` tag.  The correspondence of two transpositions is a step
of the identification of the two first arrows of the conormal sequence, not an assertion of
Stacks 03LU, 03DU or 05ZB.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the spaces-level
  adjunction.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  associated module on the small étale site, and its right adjoint.
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC), part (1), the
  compatibility of the associated module with pullback, which is the upper square's comparison.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA) and
  [Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the two conormal sequences whose first
  arrows this correspondence compares, and
  [Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the tag that comparison serves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Reading a Zariski module on a scheme of the site as an `𝒪`-module on the small étale site
of the represented algebraic space is a left adjoint.**  It is the associated-module functor of
Stacks 03DU (4) for the small étale site of the representing scheme, followed by the
identification of that site with the small étale site of `yoneda.obj W`, so the adjunction is the
associated-module adjunction composed with that equivalence.

The left adjoint is `AlgebraicGeometry.Space.representedAssociatedModule`, by
`AlgebraicGeometry.Space.representedAssociatedModule_eq_comp`; it is written here as the
composite because that is the spelling `CategoryTheory.Adjunction.comp` produces, and the
statements below are read at it. -/
noncomputable def representedSmallEtaleAssociatedModuleAdjunction (W : BigFppfOver B S hS) :
    _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS W).functor ⊣
      (representedSmallEtaleModuleEquivalence B S hS W).inverse ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj W) W.left.property :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj W) W.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS W).toAdjunction

/-- The left adjoint of `AlgebraicGeometry.Space.representedSmallEtaleAssociatedModuleAdjunction`
is `AlgebraicGeometry.Space.representedAssociatedModule`: the two spellings of that functor are
the same, the equivalence's functor being transport of modules along the identification of the
two small étale sites on the nose. -/
theorem representedAssociatedModule_eq_comp (W : BigFppfOver B S hS) :
    representedAssociatedModule B S hS W (schemeSpace W).property =
      _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj W) W.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS W).functor :=
  rfl

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The comparison of the two composite left adjoints round the stacked square**: the
associated module, read on the small étale site of the represented algebraic space, of the Zariski
inverse image of `𝓕` along the underlying morphism of schemes is the inverse image of
Stacks 03LU of the associated module of `𝓕`, naturally in `𝓕`.

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is this comparison at one
module, with no naturality.  It is assembled from the two squares' own comparisons:
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` for the upper square, which is
Stacks 03LC (1), and `AlgebraicGeometry.Space.representedModulePullbackFunctorIso` for the lower
one. -/
noncomputable def schemePullbackRepresentedAssociatedModuleSquareIso :
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').functor) ≅
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor) ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
          (associatedBigEtaleSite B) g.left) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (representedModulePullbackFunctorIso B S hS g hg) ≪≫
          (Functor.associator _ _ _).symm

/-- **The comparison of right adjoints attached to it.**  Its component at an `𝒪_{T'}`-module
`𝓖` carries the associated module of the Zariski direct image of `𝓖` to the direct image of
Stacks 03LU of the associated module of `𝓖`, both read on the small étale site of
`yoneda.obj T`.

It is `Stacks.CategoryTheory.transportMate` of
`AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso`,
hence determined by it;
it is the unique correction under which the two transpositions correspond. -/
noncomputable def representedAssociatedModulePullbackMate :
    Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g) ⋙
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T).functor) ⟶
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').functor) ⋙
        modulePushforward B S hS (representedSpaceMap B S hS g) :=
  Stacks.CategoryTheory.transportMate
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg)

/-- `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate` is
`Stacks.CategoryTheory.transportMate` of
`AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso`,
which is its definition,
stated so that the three statements below — which write the comparison out — can be read at the
shorter name.

They write it out because naming it exhausts the recursion depth of the elaborator underneath
`CategoryTheory.NatTrans.app`, while the comparison of the two natural transformations themselves
is this `rfl`. -/
theorem representedAssociatedModulePullbackMate_eq :
    representedAssociatedModulePullbackMate B S hS g hg =
      Stacks.CategoryTheory.transportMate
        (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
        (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
        (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
        (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
        (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg) :=
  rfl

/-- **The Zariski transposition and the spaces-level transposition of Stacks 03LU correspond.**
Let `𝓕` be an `𝒪_T`-module, `𝓖` an `𝒪_{T'}`-module and `u : α^*𝓕 ⟶ 𝓖` a morphism of
`𝒪_{T'}`-modules, for `α` the morphism of schemes underlying `g`.  Transporting the associated
module of `u` by
`AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso` and transposing along
`φ^* ⊣ φ_*` gives the associated module of the Zariski transpose of `u`, followed by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMate`.

This is `Stacks.CategoryTheory.homEquiv_transport` at the stacked square, so it is the two links
of `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleHomEquivTransport.lean` composed. -/
theorem homEquiv_representedAssociatedModulePullback
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (𝓖 : ((BigFppfOver.toScheme B S hS).obj T').Modules)
    (u : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj 𝓕 ⟶ 𝓖) :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T).functor).obj 𝓕)
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T').functor).obj 𝓖)
        ((schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg).inv.app 𝓕 ≫
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
              (representedSmallEtaleModuleEquivalence B S hS T').functor).map u) =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T).functor).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((BigFppfOver.toScheme B S hS).map g)).homEquiv 𝓕 𝓖 u) ≫
        (Stacks.CategoryTheory.transportMate
          (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
          (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
          (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
          (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg)).app 𝓖 :=
  Stacks.CategoryTheory.homEquiv_transport
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg) u

/-- **The same correspondence read through the inverse transpositions.**  For a morphism
`v : 𝓕 ⟶ α_*𝓖` of `𝒪_T`-modules, the spaces-level transpose of the associated module of `v`
corrected by `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate` is the transport
along `AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso` of the
associated module of the Zariski transpose of `v`. -/
theorem homEquiv_symm_representedAssociatedModulePullback
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (𝓖 : ((BigFppfOver.toScheme B S hS).obj T').Modules)
    (v : 𝓕 ⟶ (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).obj 𝓖) :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).homEquiv
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
              (representedSmallEtaleModuleEquivalence B S hS T).functor).obj 𝓕)
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
              (representedSmallEtaleModuleEquivalence B S hS T').functor).obj 𝓖)).symm
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
              (representedSmallEtaleModuleEquivalence B S hS T).functor).map v ≫
          (Stacks.CategoryTheory.transportMate
            (Scheme.Modules.pullbackPushforwardAdjunction
              ((BigFppfOver.toScheme B S hS).map g))
            (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
            (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
            (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
            (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg)).app 𝓖) =
      (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg).inv.app 𝓕 ≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T').functor).map
          (((Scheme.Modules.pullbackPushforwardAdjunction
            ((BigFppfOver.toScheme B S hS).map g)).homEquiv 𝓕 𝓖).symm v) :=
  Stacks.CategoryTheory.homEquiv_symm_transport
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg) v

/-- **The unit of the Zariski adjunction and the unit of Stacks 03LU correspond.**  This is
`AlgebraicGeometry.Space.homEquiv_representedAssociatedModulePullback` at the identity.

It is the form in which a morphism built as the adjoint transpose of a *derivation followed by
the unit* consumes the comparison — which is what the first arrow of the conormal sequence is at
both ends, `AlgebraicGeometry.Space.pullbackUnitDerivation` spaces-side and
`Stacks.ConormalSequenceRight.conormalDerivation` scheme-side.  The derivation itself is compared
by the universal property of the module of differentials; this compares what follows it. -/
theorem unit_representedAssociatedModulePullback
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).unit.app
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
              (representedSmallEtaleModuleEquivalence B S hS T).functor).obj 𝓕) ≫
        (modulePushforward B S hS (representedSpaceMap B S hS g)).map
          ((schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg).inv.app 𝓕) =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
            (representedSmallEtaleModuleEquivalence B S hS T).functor).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((BigFppfOver.toScheme B S hS).map g)).unit.app 𝓕) ≫
        (Stacks.CategoryTheory.transportMate
          (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
          (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
          (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
          (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg)).app
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj 𝓕) :=
  Stacks.CategoryTheory.unit_transport
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g))
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T')
    (representedSmallEtaleAssociatedModuleAdjunction B S hS T)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
    (schemePullbackRepresentedAssociatedModuleSquareIso B S hS g hg) 𝓕

end AlgebraicGeometry.Space

end
