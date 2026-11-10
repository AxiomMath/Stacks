module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportRestrictToAnOpen

/-!
# Sheaf Hom with exact support and restriction to an open subspace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and let `U ⊆ X` be open. The
morphism restricts to a closed quotient morphism `i|_{i⁻¹U} : Z|_{i⁻¹U} ⟶ X|_U`, by
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.restrict`, so both `i` and its
restriction carry the adjunction of [Stacks, Tag 0A75] and, on unbounded derived categories, the
adjunction of [Stacks, Tag 0A76]. This file builds the comparison

`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ⟶ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)`

between the restriction of sheaf Hom with exact support and sheaf Hom with exact support of the
restricted situation, together with the underived comparison it is built from.

Both are **mates**. Pushforward commutes with restriction already before deriving:

`(i|_{i⁻¹U})_*(F|_{i⁻¹U}) ≅ (i_*F)|_U`,

which is `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, and both functors
in it are exact, so the square survives to derived categories. Read as a 2-square over the left
adjoints of the two adjunctions it has a mate over their right adjoints, and that mate is the
comparison. No hypothesis is carried and nothing is assumed about `K`.

## Main definitions

* `ClosedQuotientMorphismOfRingedSpaces.pushforwardRestrictSquare` and
  `ClosedQuotientMorphismOfRingedSpaces.derivedPushforwardRestrictSquare`: the commuting square
  of pushforward and restriction, before and after deriving, read as a 2-square.
* `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison`: **the underived
  comparison**, the mate of that square under the two adjunctions of [Stacks, Tag 0A75].
* `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison`: **the
  comparison**, the mate of the derived square under the two adjunctions of
  [Stacks, Tag 0A76].

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.unit_sheafHomExactSupportRestrictComparison` and
  `ClosedQuotientMorphismOfRingedSpaces.unit_derivedSheafHomExactSupportRestrictComparison`: the
  unit equation each comparison satisfies, and
  `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison_unique`,
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison_unique`:
  that equation determines the comparison, so nothing else inhabits the type and satisfies the
  characterization — in particular neither the zero map nor the negative of the comparison.
* `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison_counit` and
  `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison_counit`:
  the counit equation, which is the form the comparison enters an adjunction computation in.

## What is not proved here

Invertibility is not proved in this file. The underived comparison is proved to be an
isomorphism in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportRestrictComparisonIso.lean`
(`ClosedQuotientMorphismOfRingedSpaces.isIso_sheafHomExactSupportRestrictComparison`), through
evaluation at one rather than through the internal-Hom route described below, and an isomorphism
`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ≅ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)` is constructed in
`ExactSupportRestrictDerivedIso.lean`; that the derived comparison itself is invertible is not
proved. The rest of this section records the internal-Hom route. Invertibility is real work and not
bookkeeping: `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupport` is the internal Hom
`SheafHom_{𝒪_X}(i_*𝒪_Z, -)` followed by the descent equivalence
`ClosedQuotientMorphismOfRingedSpaces.moduleDescend`.

What is available towards it, and is not in this file:

* the reduction "it suffices after `(i|_{i⁻¹U})_*`", respectively "after `R(i|_{i⁻¹U})_*`", in
  `ExactSupportRestrictComparisonIso.lean`, beside this file
  (`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/`)
  — the restricted morphism is again a closed quotient morphism, so its pushforward reflects
  isomorphisms on both sides, by [Stacks, Tag 08KS];
* the descent factor compared with restriction **as a functor**, in
  `StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictDescend.lean`:
  `ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso`, unconditionally, over the
  sections statement of
  `StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictSections.lean` — an
  `i_*𝒪_Z`-module has the same sections over `i_! V` as over `i_! V ⊓ U`, and `i_! V ⊓ U` is the
  `i_!` of the restricted situation — and the ring comparison of
  `StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictRingSheaf.lean`;
* for the internal Hom factor, both the **derived** statement, [Stacks, Tag 08DL], proved as
  `Stacks.SheafOfModules.derivedSheafHomRestrictionIso`, and the **underived** one,
  [Stacks, Tag 08DL]'s underived counterpart [Stacks, Tag 0E8H], proved as
  `Stacks.SheafOfModules.InternalHom.internalHomOverIso` with its section-level
  characterization `internalHomOverIso_hom_app` (the section-level comparison is
  `Stacks.SheafOfModules.sheafHomOverEquiv`); 0E8H is the sheaf-level
  statement, for the internal Hom of two sheaves of modules on an arbitrary ringed site.
  What 0E8H does **not** cover, and what the internal Hom factor of `sheafHomExactSupport` is
  actually waiting on, is two changes of model: its internal Hom is
  `Stacks.PresheafOfModules.internalHom` of two modules over a presheaf of *commutative* rings,
  whereas `RingedSpaceModuleAdjunction.homSheaf` is the internal Hom *out of a sheaf of rings*,
  `Stacks.PresheafOfModules.CoextendScalars.coextObj`; and its restriction is to the *slice
  site* `Opens X / U`, whereas the comparison below restricts to the *open subspace* `U`.

What no declaration supplies is the identification of the pushed-forward comparison with those
maps: by the internal Hom identification of [Stacks, Tag 0A75]
(`ClosedQuotientMorphismOfRingedSpaces.modulePushforwardSheafHomExactSupportIsoHomSheaf`) and
the square below, `(i|_{i⁻¹U})_*` of the underived comparison is a map
`ℰom_{𝒪_X}(i_*𝒪_Z, F)|_U ⟶ ℰom_{𝒪_U}((i_*𝒪_Z)|_U, F|_U)`, and by [Stacks, Tag 0A77]
(`ClosedQuotientMorphismOfRingedSpaces.derivedModulePushforwardDerivedSheafHomExactSupportIso`)
the derived one is the corresponding map of derived internal Homs; that those are the maps just
listed is the step that is missing.

Nothing here carries a Stacks attribute. The source states no comparison of this shape; it
replaces `X` by an affine open and reads every functor in sight on the smaller space, and this
is one of the identifications that step is made of.

## Implementation notes

*Two spellings of the restricted morphism.* The morphism of the restricted situation,
`(S.restrict U).i`, and the written-out restriction
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, are the same term by
`ClosedQuotientMorphismOfRingedSpaces.restrict_i`, and `restrict` is reducible, but instance
search still does not cross between them: discovering the bundled morphism from the written-out
one means solving `?S.i ≟ restrictedMorphism S.i U` for `?S` under a projection, which instance
search does not do, and reducibility of `restrict` does not change that. The instance
`ClosedQuotientMorphismOfRingedSpaces.preservesFiniteColimits_modulePushforward_restrictedMorphism`
below is needed: without it, four
`PreservesFiniteColimits (modulePushforward (restrictedMorphism S.i U))` instance problems fail.
So the exactness of `(i|_{i⁻¹U})_*` is found at the first spelling and the base-change
isomorphism is stated at the second. Everything below is stated at
the second, and the crossing is paid once, in
`ClosedQuotientMorphismOfRingedSpaces.restrictPushforwardSheafHomExactSupportAdjunction` and its
derived counterpart, which are the adjunctions of the restricted situation read at that
spelling. Paying it instead inside each statement that mentions the left adjoint — which the
counit equations do — makes the kernel compare the two adjunctions themselves, and that does not
terminate within the default heartbeat budget.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)

/-! ### The restricted situation, read at the written-out restriction of `i` -/

/-- **Pushforward along the restriction of a closed quotient morphism is exact.** The
restriction `i|_{i⁻¹U}` is again a closed quotient morphism, by
`ClosedQuotientMorphismOfRingedSpaces.restrict`, so [Stacks, Tag 08KS] applies to it; this is
that instance at the written-out restriction
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`. -/
instance preservesFiniteColimits_modulePushforward_restrictedMorphism :
    PreservesFiniteColimits (modulePushforward (restrictedMorphism S.i U)) :=
  preservesFiniteColimits_modulePushforward (S.restrict U)

/-- **[Stacks, Tag 0A75] for the restricted situation**, with its left adjoint written as
pushforward along `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`. -/
def restrictPushforwardSheafHomExactSupportAdjunction :
    modulePushforward (restrictedMorphism S.i U) ⊣ (S.restrict U).sheafHomExactSupport :=
  (S.restrict U).modulePushforwardSheafHomExactSupportAdjunction

/-- **[Stacks, Tag 0A76] for the restricted situation**, with its left adjoint written as
pushforward along `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`. -/
def restrictDerivedPushforwardSheafHomExactSupportAdjunction :
    (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory ⊣
      (S.restrict U).derivedSheafHomExactSupport :=
  (S.restrict U).derivedModulePushforwardSheafHomExactSupportAdjunction

/-! ### The underived comparison -/

/-- **Pushforward commutes with restriction to an open subspace**, read as a 2-square over the
two left adjoints of [Stacks, Tag 0A75]: restricting an `𝒪_Z`-module to `i⁻¹U` and pushing
forward along `i|_{i⁻¹U}` is pushing forward along `i` and restricting to `U`.

This is `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`. -/
def pushforwardRestrictSquare :
    TwoSquare (moduleRestriction S.Z (preimageOpen S.i U)) (modulePushforward S.i)
      (modulePushforward (restrictedMorphism S.i U)) (moduleRestriction S.X U) :=
  TwoSquare.mk _ _ _ _ (modulePushforwardRestrictIso S.i U).hom

/-- **The comparison of sheaf Hom with exact support with restriction to an open subspace**,
before deriving:

`ℰom(𝒪_Z, F)|_{i⁻¹U} ⟶ ℰom(𝒪_{Z|_{i⁻¹U}}, F|_U)`,

natural in the `𝒪_X`-module `F`. It is the mate of
`ClosedQuotientMorphismOfRingedSpaces.pushforwardRestrictSquare` under the adjunction of
[Stacks, Tag 0A75] for `i` and the one for its restriction. No hypothesis enters, and it is not
proved to be an isomorphism. -/
def sheafHomExactSupportRestrictComparison :
    TwoSquare S.sheafHomExactSupport (moduleRestriction S.X U)
      (moduleRestriction S.Z (preimageOpen S.i U)) (S.restrict U).sheafHomExactSupport :=
  mateEquiv S.modulePushforwardSheafHomExactSupportAdjunction
    (S.restrictPushforwardSheafHomExactSupportAdjunction U)
    (S.pushforwardRestrictSquare U)

/-- **The unit equation characterizing the underived comparison.** For an `𝒪_Z`-module `G`, the
unit of [Stacks, Tag 0A75] for the restricted situation at `G|_{i⁻¹U}`, followed by
`ℰom(𝒪_{Z|_{i⁻¹U}}, -)` of the square, is the restriction of the unit for `i` followed by the
comparison. -/
theorem unit_sheafHomExactSupportRestrictComparison
    (G : SheafOfModules.{u} (structureSheafRing S.Z)) :
    (S.restrictPushforwardSheafHomExactSupportAdjunction U).unit.app
          ((moduleRestriction S.Z (preimageOpen S.i U)).obj G) ≫
        (S.restrict U).sheafHomExactSupport.map ((S.pushforwardRestrictSquare U).app G) =
      (moduleRestriction S.Z (preimageOpen S.i U)).map
          (S.modulePushforwardSheafHomExactSupportAdjunction.unit.app G) ≫
        (S.sheafHomExactSupportRestrictComparison U).app ((modulePushforward S.i).obj G) :=
  (unit_mateEquiv S.modulePushforwardSheafHomExactSupportAdjunction
    (S.restrictPushforwardSheafHomExactSupportAdjunction U)
    (S.pushforwardRestrictSquare U) G).symm

/-- **The unit equation determines the underived comparison.** A 2-square of the same shape
satisfying `unit_sheafHomExactSupportRestrictComparison` is that comparison, so neither the zero
map nor any other candidate satisfies the equation. -/
theorem sheafHomExactSupportRestrictComparison_unique
    (β : TwoSquare S.sheafHomExactSupport (moduleRestriction S.X U)
      (moduleRestriction S.Z (preimageOpen S.i U)) (S.restrict U).sheafHomExactSupport)
    (h : ∀ G : SheafOfModules.{u} (structureSheafRing S.Z),
      (S.restrictPushforwardSheafHomExactSupportAdjunction U).unit.app
            ((moduleRestriction S.Z (preimageOpen S.i U)).obj G) ≫
          (S.restrict U).sheafHomExactSupport.map ((S.pushforwardRestrictSquare U).app G) =
        (moduleRestriction S.Z (preimageOpen S.i U)).map
            (S.modulePushforwardSheafHomExactSupportAdjunction.unit.app G) ≫
          β.app ((modulePushforward S.i).obj G)) :
    S.sheafHomExactSupportRestrictComparison U = β :=
  mateEquiv_eq_of_unit S.modulePushforwardSheafHomExactSupportAdjunction
    (S.restrictPushforwardSheafHomExactSupportAdjunction U)
    (S.pushforwardRestrictSquare U) β h

/-- **The counit equation satisfied by the underived comparison.** Pushing the comparison at an
`𝒪_X`-module `F` forward along `i|_{i⁻¹U}` and composing with the counit of [Stacks, Tag 0A75]
for the restricted situation is the square at `ℰom(𝒪_Z, F)` followed by the restriction to `U`
of the counit for `i`. -/
theorem sheafHomExactSupportRestrictComparison_counit
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (modulePushforward (restrictedMorphism S.i U)).map
          ((S.sheafHomExactSupportRestrictComparison U).app F) ≫
        (S.restrictPushforwardSheafHomExactSupportAdjunction U).counit.app
          ((moduleRestriction S.X U).obj F) =
      (S.pushforwardRestrictSquare U).app (S.sheafHomExactSupport.obj F) ≫
        (moduleRestriction S.X U).map
          (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F) :=
  mateEquiv_counit S.modulePushforwardSheafHomExactSupportAdjunction
    (S.restrictPushforwardSheafHomExactSupportAdjunction U)
    (S.pushforwardRestrictSquare U) F

/-! ### The comparison on derived categories -/

/-- **Derived pushforward commutes with restriction to an open subspace**, read as a 2-square
over the two left adjoints of [Stacks, Tag 0A76].

Both `i_*` and restriction to an open are exact, so the derived functors are the ones induced
termwise and `ClosedQuotientMorphismOfRingedSpaces.pushforwardRestrictSquare` passes to derived
categories by `CategoryTheory.Functor.mapDerivedCategorySquareIso`. -/
def derivedPushforwardRestrictSquare :
    TwoSquare (moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory
      (modulePushforward S.i).mapDerivedCategory
      (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory
      (moduleRestriction S.X U).mapDerivedCategory :=
  TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (modulePushforwardRestrictIso S.i U)).hom

/-- **The comparison of derived sheaf Hom with exact support with restriction to an open
subspace**:

`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ⟶ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)`,

natural in `K` in `D(𝒪_X)`. It is the mate of
`ClosedQuotientMorphismOfRingedSpaces.derivedPushforwardRestrictSquare` under the adjunction
`Ri_* ⊣ R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] for `i` and the one for its restriction
`i|_{i⁻¹U}`.

This is the identification an argument replacing `X` by an open subspace needs in order to
carry `R ℰom(𝒪_Z, -)` along; the two other functors occurring in the map of
[Stacks, Tag 0E2N] already restrict, by
`Stacks.Cohomology.DerivedRestrictionPullback.derivedRestrictPullbackIso` and
`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`. **It is not proved to be
an isomorphism**, and no hypothesis is carried. -/
def derivedSheafHomExactSupportRestrictComparison :
    TwoSquare S.derivedSheafHomExactSupport (moduleRestriction S.X U).mapDerivedCategory
      (moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory
      (S.restrict U).derivedSheafHomExactSupport :=
  mateEquiv S.derivedModulePushforwardSheafHomExactSupportAdjunction
    (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U)
    (S.derivedPushforwardRestrictSquare U)

/-- **The unit equation characterizing the comparison.** For `L` in `D(𝒪_Z)`, the unit of
[Stacks, Tag 0A76] for the restricted situation at `L|_{i⁻¹U}`, followed by
`R ℰom(𝒪_{Z|_{i⁻¹U}}, -)` of the derived square, is the restriction of the unit for `i`
followed by the comparison. -/
theorem unit_derivedSheafHomExactSupportRestrictComparison
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :
    (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U).unit.app
          ((moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory.obj L) ≫
        (S.restrict U).derivedSheafHomExactSupport.map
          ((S.derivedPushforwardRestrictSquare U).app L) =
      (moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory.map
          (S.derivedModulePushforwardSheafHomExactSupportAdjunction.unit.app L) ≫
        (S.derivedSheafHomExactSupportRestrictComparison U).app
          ((modulePushforward S.i).mapDerivedCategory.obj L) :=
  (unit_mateEquiv S.derivedModulePushforwardSheafHomExactSupportAdjunction
    (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U)
    (S.derivedPushforwardRestrictSquare U) L).symm

/-- **The unit equation determines the comparison.** A 2-square of the same shape satisfying
`unit_derivedSheafHomExactSupportRestrictComparison` is that comparison. -/
theorem derivedSheafHomExactSupportRestrictComparison_unique
    (β : TwoSquare S.derivedSheafHomExactSupport (moduleRestriction S.X U).mapDerivedCategory
      (moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory
      (S.restrict U).derivedSheafHomExactSupport)
    (h : ∀ L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)),
      (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U).unit.app
            ((moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory.obj L) ≫
          (S.restrict U).derivedSheafHomExactSupport.map
            ((S.derivedPushforwardRestrictSquare U).app L) =
        (moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory.map
            (S.derivedModulePushforwardSheafHomExactSupportAdjunction.unit.app L) ≫
          β.app ((modulePushforward S.i).mapDerivedCategory.obj L)) :
    S.derivedSheafHomExactSupportRestrictComparison U = β :=
  mateEquiv_eq_of_unit S.derivedModulePushforwardSheafHomExactSupportAdjunction
    (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U)
    (S.derivedPushforwardRestrictSquare U) β h

/-- **The counit equation satisfied by the comparison.** Pushing the comparison at `K` in
`D(𝒪_X)` forward along `i|_{i⁻¹U}` and composing with the counit of [Stacks, Tag 0A76] for the
restricted situation is the derived square at `R ℰom(𝒪_Z, K)` followed by the restriction to
`U` of the counit for `i`. -/
theorem derivedSheafHomExactSupportRestrictComparison_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory.map
          ((S.derivedSheafHomExactSupportRestrictComparison U).app K) ≫
        (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U).counit.app
          ((moduleRestriction S.X U).mapDerivedCategory.obj K) =
      (S.derivedPushforwardRestrictSquare U).app (S.derivedSheafHomExactSupport.obj K) ≫
        (moduleRestriction S.X U).mapDerivedCategory.map
          (S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K) :=
  mateEquiv_counit S.derivedModulePushforwardSheafHomExactSupportAdjunction
    (S.restrictDerivedPushforwardSheafHomExactSupportAdjunction U)
    (S.derivedPushforwardRestrictSquare U) K

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
