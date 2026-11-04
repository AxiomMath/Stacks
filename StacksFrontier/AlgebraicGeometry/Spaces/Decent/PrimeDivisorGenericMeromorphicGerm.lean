module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianSpecMorphismFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericMeromorphicStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullback

/-!
# When a meromorphic section lies in `ℒ_ξ`

Let `X` be a decent algebraic space over `S`, let `Z ⊆ X` be a prime divisor with generic point
`ξ`, let `ℒ` be an `𝒪_X`-module and let `s` be a meromorphic section of `ℒ`.  The canonical
morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` is flat, so `s` pulls back to a meromorphic section of
`ℒ_ξ = c_ξ^*ℒ` on `Spec(𝒪^h_{X, ξ})`; its value over the identity étale chart is the *germ of
`s` at `ξ`*, an element of `𝒦_X(ℒ)_ξ`.

The first of the two collections of Stacks 0EPS is

`{Z ⊂ X | Z a prime divisor with generic point ξ and s not in ℒ_ξ}`,

and this file is what makes that condition expressible: `s` *lies in* `ℒ_ξ` when its germ at `ξ`
is in the image of the comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ` of
`AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalkToMeromorphic`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicGerm` is the germ of a meromorphic
  section of `ℒ` at the generic point of a prime divisor, as an element of `𝒦_X(ℒ)_ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.MemGenericModuleStalk` is the predicate "`s` lies in
  `ℒ_ξ`" of the first collection of Stacks 0EPS.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_iff`: `s` lies in `ℒ_ξ` exactly
  when its germ at `ξ` is the image of a section of `ℒ_ξ`.

## Implementation notes

The germ is the composite of the global pullback of meromorphic sections of Stacks 0ENC, part
(1) — available for `c_ξ` by
`AlgebraicGeometry.Space.PrimeDivisor.pullbacksMeromorphicSections_genericHenselianMorphism` —
with evaluation over the identity étale chart of `Spec(𝒪^h_{X, ξ})`.  Both are maps of
underlying sets, so the germ is a function and not a module map; it is nevertheless additive,
`AlgebraicGeometry.Space.pullbackMeromorphicSectionAddHom`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullbackAdditive.lean`) bundling
the global pullback of Stacks 0ENC with its additivity, which this module does not import.

The module `ℒ` ranges over `Modules.{u, u}`, as for
`AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicModuleStalk`: both the pullback of
modules and the global pullback of meromorphic sections exist only at the module universe of
the structure rings.

That sentence has been *checked* rather than assumed, and it holds; what follows is the chain
and where it bottoms out, so that the next reader need not re-derive it.  The germ needs
`AlgebraicGeometry.Space.PrimeDivisor.genericHenselianPullback`, which is
`(AlgebraicGeometry.Space.modulePullback …).obj ℒ`, and `modulePullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`) is
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the morphism of small étale ringed topoi
of Stacks 03G8.

**The decisive restriction is structural, and it is in `RingedToposModules` itself: that
development identifies the module universe with the ring universe.**  `pullbackModules` is a
functor `SheafOfModules.{w'} (structureRingSheaf Y) ⥤ SheafOfModules.{w} (structureRingSheaf X)`
for ringed topoi `RingedTopos.{v, u, w}` and `RingedTopos.{v', u', w'}`, the sections of the
module being forced into the universe `w` of the structure *rings*, which is in turn the
universe of the sheaves of sets of the underlying topos — the geometric factor
`Stacks.Sheaves.RingedToposModules.inverseImageModules` consumes a
`CategoryTheory.MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))`.  So this route cannot
produce `Modules.{u, max u z}` at all, however the universes of the topos machinery are
relaxed: asking it for modules with sections in `Type (max u z)` is asking for a ringed topos
whose *structure sheaf* is a `CommRingCat.{max u z}`, that is for a lift of `𝒪_X`, and the
modules it then returns are modules over the lifted ring sheaf rather than over the `Type
u`-valued one that `AlgebraicGeometry.Space.Modules` is taken over.

Two further things block the morphism of small étale topoi at `Type (max u z)`, and they are
worth separating because only the first is an obstruction.

* *The comparison equivalence of Stacks 03G1 is not available there.*  The restriction functor
  `(AlgebraicGeometry.Space.comparisonFunctor …).sheafPushforwardContinuous (Type (max u z)) …`
  does elaborate, but it is not known to be an equivalence; the instances that make it one at
  `Type u` are those of `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse`,
  each routed through essential smallness of the small étale site *at `u`*.  Since
  `AlgebraicGeometry.Space.smallEtaleDirectImage` takes the inverse of that equivalence, the
  restriction already bites on the *direct* image — hence on
  `AlgebraicGeometry.Space.moduleDirectImage` and `AlgebraicGeometry.Space.modulePushforward`,
  and not only on the pullback.
* *Left exactness of the inverse image is not the obstruction it looks like.*
  `AlgebraicGeometry.Space.preservesFiniteLimits_sheafPullback_spacesBaseChange`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleEssentiallySmall.lean`) obtains it at
  `Type u` by replacing the spaces-étale site with a small model at `Type u` and applying
  Stacks 00X5 there, and Mathlib's Stacks 00X5 rests on
  `CategoryTheory.lan_preservesFiniteLimits_of_flat`, whose binders force the coefficient
  category's morphism universe to equal the universe of the site — with the site at its `Type u`
  small model that pins the sheaves of sets to `Type u` exactly.  That is a limitation of the
  available statement and not of the mathematics: exactness of the inverse image of a morphism
  of sites between genuinely small sites is independent of the universe of values of the
  sheaves.

What the restriction is therefore *not* is a universe bound on the pullback of modules in
principle.  Mathlib's `SheafOfModules.pullback.{v} φ` is stated at a module universe `v` wholly
independent of the ring universe, for a *site* functor together with a morphism of sheaves of
rings, with no morphism of topoi and no left exactness anywhere in it.  The route through it has
been traced declaration by declaration, and what follows is what each of its steps costs, so
that the next reader need not re-derive the map.  **Only the last two steps are open; the site
functor is not one of them.**

* *The site functor exists.*  `AlgebraicGeometry.Space.smallBaseChange`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChange.lean`) is
  `SmallEtale … Y.1 ⥤ SmallEtale … X.1` for a **relatively representable** morphism, with
  `AlgebraicGeometry.Space.smallBaseChange_isMorphismOfSites` for its site condition and
  `AlgebraicGeometry.Space.isContinuous_smallBaseChange` for its continuity, and
  `AlgebraicGeometry.Space.smallBaseChangeSharp`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleBaseChangeRestriction.lean`) is the morphism
  of sheaves of rings it needs, at `RingCat.{u}`.  Neither mentions a module universe.
* *The adjointness at a module universe above the ring universe is available at presheaf
  level.*  `PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE` is that
  instance, its ring universe being independent of its module universe, the rings being asked
  only to take `v`-small values; the sheaf-level instance is then
  `(SheafOfModules.PullbackConstruction.adjunction.{v} φ).isRightAdjoint`, once the presheaf-level
  instance is restated at the spelling of `φ.hom` as
  `SheafOfModules.presheafPushforward_isRightAdjoint_of_essentiallySmall` restates its
  equal-universe form.  That sheaf-level form is not in the library yet — it has no consumer
  until the route below is unblocked — and
  `SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` does not supply it, its ring
  universe being the module universe.  The other ring-universe-free form in the library,
  `SheafOfModules.pushforward_isRightAdjoint_of_univLE`, asks `UnivLE` of the universe
  of the *objects* of the source site, and the small étale site has its objects in
  `Type (u + 1)`, so that form fails at every module universe `max u z` with `z ≤ u`.
* *Three instances about the small étale site are still stated too narrowly, and each narrowing
  is in the statement rather than in the mathematics.*  At the module universe `max u z` the
  pullback needs `EssentiallySmall.{max u z} (SmallEtale …)`, which holds —
  `CategoryTheory.EssentiallySmall.mk'` of `equivSmallModel` followed by
  `CategoryTheory.AsSmall.equiv` raises the universe of essential smallness — but is not an
  instance; and it needs `HasWeakSheafify` and `WEqualsLocallyBijective` for
  `AddCommGrpCat.{max u z}`, which `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` and
  `AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSite.lean`) supply only for a coefficient
  category with morphisms in `Type u`, because that is the binder they are stated at.  Mathlib's
  `CategoryTheory.hasSheafifyEssentiallySmallSite` and
  `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, through which
  both are obtained, leave the coefficient category's morphism universe free of the site's, so
  restating them at a free coefficient universe is a relaxation of binders.
  `LocallySmall.{max u z} (SmallEtale …)`, the fourth hypothesis, already holds.
* *`c_ξ` is not known to be a relatively representable morphism, and that is the first real
  gap.*  `smallBaseChange` asks `yoneda.relativelyRepresentable f.hom` — representability of the
  *morphism*, i.e. that every base change of it along a scheme is a scheme — and nothing in the
  library establishes it for
  `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianMorphism`.  That the *source* of `c_ξ` is
  representable is a strictly weaker statement and does not give it: for a morphism `T ⟶ X` from
  a scheme to an algebraic space, `T ×_X T` is a monomorphism of algebraic spaces into a scheme,
  which need not be a scheme.
* *And Stacks 0ENC would have to be re-derived over the new pullback, which is the bulk.*
  `AlgebraicGeometry.Space.pullbackMeromorphicSection`
  (`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullback.lean`) together with
  its value theory (`…MeromorphicSectionGlobalPullbackValue`) and its additivity
  (`…MeromorphicSectionGlobalPullbackAdditive`) is built on `modulePullback` throughout.

So the wall is real and its cause is `AlgebraicGeometry.Space.modulePullback`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`), whose signature is
`Modules.{u, u} ⥤ Modules.{u, u}` outright; dissolving it is a development of its own, and it is
blocked on representability of `c_ξ` rather than on the existence of a site functor.

This does **not** yet suffice to restate Stacks 0EPS without its open-subspace hypothesis, but
only one statement is missing.  The germ is computable: `pullbackMeromorphicSection` has the
evaluation lemma `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullbackValue.lean`), and with
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul` it carries a
representation of `s` as `1 ⊗ e` over a chart to the conclusion that the germ at `ξ` is the
image of a section of `ℒ_ξ`, that is to `MemGenericModuleStalk`.  What no theorem in the library
provides is that representation: a nonempty open subspace of `X` over which `s` is an honest
section of `ℒ`.  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` say what reaching it needs.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENV](https://stacks.math.columbia.edu/tag/0ENV)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- **The germ at `ξ` of a meromorphic section of `ℒ`**, an element of `𝒦_X(ℒ)_ξ`: the
meromorphic section is pulled back along the flat morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` by
Stacks 0ENC, part (1), and the result is read over the identity étale chart of
`Spec(𝒪^h_{X, ξ})`.

This is the element of which Stacks 0EPS asks whether it lies in `ℒ_ξ`, and against which the
ratio `s / s_ξ` of Stacks 0EPR is taken. -/
def PrimeDivisor.genericMeromorphicGerm (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    Z.genericMeromorphicModuleStalk B S hS hX hdec R hR L :=
  (pullbackMeromorphicSection B S hS (Z.genericHenselianMorphism B S hS hX hdec R hR) L
      (Z.pullbacksMeromorphicSections_genericHenselianMorphism B S hS hX hdec R hR) s).eval
    (op (Z.genericHenselianChart B S hS hX hdec R hR))

/-- **`s` lies in `ℒ_ξ`**: the germ at the generic point `ξ` of a prime divisor of a meromorphic
section `s` of `ℒ` is the image, under the comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ`, of a section of
`ℒ_ξ = c_ξ^*ℒ`.

The negation of this is the condition defining the first of the two collections of prime
divisors of Stacks 0EPS. -/
def PrimeDivisor.MemGenericModuleStalk (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) : Prop :=
  Z.genericMeromorphicGerm B S hS hX hdec R hR L s ∈
    Set.range (Z.genericModuleStalkToMeromorphic B S hS hX hdec R hR L)

/-- `s` lies in `ℒ_ξ` exactly when its germ at `ξ` is the image of a section of `ℒ_ξ` under the
canonical map into the meromorphic sections. -/
theorem PrimeDivisor.memGenericModuleStalk_iff (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L) :
    Z.MemGenericModuleStalk B S hS hX hdec R hR L s ↔
      ∃ m : Z.genericModuleStalk B S hS hX hdec R hR L,
        Z.genericModuleStalkToMeromorphic B S hS hX hdec R hR L m =
          Z.genericMeromorphicGerm B S hS hX hdec R hR L s :=
  Iff.rfl

end Generic

end AlgebraicGeometry.Space

end
