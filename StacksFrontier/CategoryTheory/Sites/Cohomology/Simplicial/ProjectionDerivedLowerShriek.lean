module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AcyclicityUnconditional
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedCoveringPullbacks
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` for the projection `Δ × C ⥤ C`, instantiated

Let `C` be a small site with fibre products and let `O` be a sheaf of rings on it; let
`π : Δ × C ⥤ C` be the projection of Stacks 09D0, with `Δ × C` carrying the topology inherited
from `J` along `π`. This file instantiates the unconditional derived lower shriek of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AcyclicityUnconditional.lean` at `π`,
producing the functor

`Lπ_! : D(π^{-1}O) ⟶ D(O)`

of Stacks 09CY together with its adjunction, its `CommShift ℤ` and its `IsTriangulated` — that
is, the `proj` parameter of `Stacks.SimplicialModules.augmentedLowerShriek` (Stacks 09D3).

## Main definitions

* `Stacks.SimplicialModules.projection`: the projection `π : Δ × C ⥤ C`.
* `Stacks.SimplicialModules.projectionTopology`: the topology `Δ × C` inherits along it.
* `Stacks.SimplicialModules.projectionRing`: `π^{-1}O`, the restriction of the structure sheaf.
* `Stacks.SimplicialModules.derivedProjectionLowerShriek`: **`Lπ_!`**, with
  `derivedProjectionLowerShriekAdjunction`.

## Main results

* `Lπ_!` is exact as a functor of triangulated categories and commutes with the shift: these are
  the instances `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek_isTriangulated` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek_commShift`, found by instance search
  since `derivedProjectionLowerShriek` is an abbreviation of `derivedLowerShriek`.

Continuity and cocontinuity of `π` for the inherited topology — Stacks 06NW, without which the
lower-shriek development cannot be read at `π` at all — are
`CategoryTheory.Functor.isContinuous_inheritedTopology` and
`CategoryTheory.Functor.isCocontinuous_inheritedTopology` in
`StacksFrontier/CategoryTheory/Sites/Stack/InheritedCoveringPullbacks.lean`, stated for an
arbitrary fibred category and found here by instance search through
`CategoryTheory.Prod.snd_isFibered`.

## Why there is no `HasPullbacks C` hypothesis, and what is left in its place

This file does not assume `[HasPullbacks C]`, because that is a
*sufficient* condition and not the one the chain uses; what the chain uses is carried instead —
continuity and cocontinuity of `π` and the covering-pullback clause for `π`. The difference
matters for a consumer: a tag stated as "for a small site **with fibre products**" reads as
conditional, whereas these three are standing hypotheses of the source.

The fibre products themselves are **not** removable, and it is worth recording why, because the
question will be asked again.

* Deleting `[HasPullbacks 𝒮]` from
  `StacksFrontier/CategoryTheory/Sites/Stack/InheritedCoveringPullbacks.lean` fails in five places,
  all of the same shape: `CategoryTheory.Functor.IsFibered.hasPullback_of_isStronglyCartesian`
  produces the pullback of a strongly cartesian arrow along an arbitrary arrow only from the
  pullback of their images in the base. It is used in the `pullback` case of the cofinality
  induction and twice in the covering-pullback instance, and the two continuity instances go
  through an upstream lemma carrying the same hypothesis.
* It cannot be dodged by arguing in `Δ × C`. A pullback in a product category restricts to a
  pullback in each factor, so `Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J)
  (projection C)` *implies* that the members of a cofinal family of coverings of `C` have
  pullbacks along arbitrary morphisms. The `Δ` coordinate contributes nothing precisely because
  the first components are invertible
  (`CategoryTheory.Prod.isStronglyCartesian_snd_iff_isIso_fst`); the base coordinate is where
  the content is.
* And it should not be dodged by weakening the clause to "for the fibre products that exist".
  Stacks' own Definition 00VH, axiom (3) of a site, *asserts* that `U_i ×_U V` exists for every
  covering `{U_i → U}` and every `V → U`. So the existence is part of what "let `𝒞` be a site"
  means in the source, not an addition to it; and the Čech computation behind Stacks 0D6X needs
  the iterated fibre products of a covering to exist in order to form its complex at all, so a
  conditional clause would not support the consumer either.

What is left, `Stacks.Sites.PreservesCoveringPullbacks`, is clause (2) of Sites
Definition 00WV together with the existence that 00VH (3) supplies — the source's standing
hypothesis on a site, transcribed. On a site that does have all pullbacks it is discharged by
instance search, which the three `example`s at the end of this file check, so nothing regresses
for a consumer that previously wrote `[HasPullbacks C]`.

## The typing recommendation for Stacks 09DH

`Stacks.SimplicialModules.augmentedLowerShriek` takes its `proj` parameter out of
`DerivedCategory (SimplicialModule J (constantRing J O))`, whereas `Lπ_!` here is built on
`SheafOfModules (projectionRing C J O)`. The two module categories are equivalent — compose
`Stacks.SimplicialModules.equivSheafOfModules` with the identification of
`ringSheaf J (constantRing J O)` with `projectionRing C J O`, both being `U ↦ O(U)` on
`Δ × C`.

**Either spelling works.** `CategoryTheory.Functor.mapDerivedCategory` transports an exact
functor to the derived categories, and Mathlib supplies its `CommShift ℤ` and `IsTriangulated`
instances (`Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`), so the equivalence
above does carry `Lπ_!` over to the `SimplicialModule` spelling; that is the route
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/AugmentationDerivedBaseChange.lean`
takes for the `base` parameter, which exists in both spellings. The recommendation below is
therefore a preference and not a constraint.

**The preference: state Stacks 09DH against `SheafOfModules (projectionRing C J O)`**, because
that is where every instance it needs is already supplied — the abelian structure, the
Grothendieck abelianness and the derived category — so a consumer writes no ascriptions. The
`SimplicialModule` spelling is workable but has a sharp edge, and it is worth stating exactly,
because it is **not** a limit of the mathematics and **not** a heartbeat budget:

`Abelian` and `HasDerivedCategory` are arguments of `DerivedCategory`, so two sheaves of rings
that are definitionally equal but differently *spelled* give two definitionally equal but
differently spelled derived categories. Composition with `⋙` typechecks across that difference,
because it elaborates at default transparency; instance search does not, because it unfolds only
reducible definitions, so it cannot see that an instance registered for one spelling applies to
the other. The symptoms are the ones previously reported here as hard constraints — that
`CategoryTheory.Preadditive.fullSubcategory`'s `HasZeroMorphisms` is not the one an assumed
`[Abelian (SimplicialModule J A)]` resolves to, and that unfolding
`Stacks.SimplicialModules.abelian` through `abelianOfEquivalence (equivSheafOfModules …)`
exhausts the heartbeat limit. Neither is a constraint. The fix is to write every intermediate
category in exactly one spelling and ascribe the equivalence's target to it;
`equivSheafOfModulesPinned` and `constantEquivSheafOfModulesPinned` in
`AugmentationDerivedBaseChange.lean` are that ascription and nothing more, and with them
`attribute [local instance] abelian` together with `HasDerivedCategory.standard` needs no
elaboration option to be set whatsoever.

Nothing in Stacks 09DH depends on which of the two equivalent categories is used: the tag is a
distinguished triangle, and the triangle can be formed wherever `base` and `proj` are
composable. What 09D3 contributes — that the composite is exact — is proved there for arbitrary
parameters, so a consumer at either spelling loses nothing.

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.SimplicialModules

open Stacks.Cohomology.DerivedLowerShriek

attribute [local instance] HasDerivedCategory.standard

variable (C : Type w) [SmallCategory C]

/-- The projection `π : Δ × C ⥤ C` of Stacks 09D0. -/
abbrev projection : SimplexCategory × C ⥤ C := CategoryTheory.Prod.snd SimplexCategory C

variable (J : GrothendieckTopology C)

/-- The topology `Δ × C` inherits from `(C, J)` along the projection, which is the topology in
which Stacks 09D1 takes the sheaf condition on a simplicial module. -/
abbrev projectionTopology : GrothendieckTopology (SimplexCategory × C) :=
  (projection C).inheritedTopology J

variable [(projection C).IsContinuous (projectionTopology C J) J]
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]

variable (O : Sheaf J RingCat.{w})

/-- `π^{-1}O`, the restriction of the structure sheaf along the projection. Its sheaves of
modules are the simplicial modules over the constant simplicial sheaf of rings `O`. -/
abbrev projectionRing : Sheaf (projectionTopology C J) RingCat.{w} :=
  inverseImageRing (projectionTopology C J) J (projection C) O

variable [HasSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf (projectionTopology C J) AddCommGrpCat.{w})]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (idRingMap (projectionTopology C J) J (projection C) O)).IsRightAdjoint]
  [∀ V : SimplexCategory × C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((projectionRing C J O).over V) :
      (projectionRing C J O).over V ⟶ (projectionRing C J O).over V)).IsRightAdjoint]
  [EnoughInjectives (SheafOfModules.{w} (projectionRing C J O))]
  [EnoughInjectives (SheafOfModules.{w} O)]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} O)]

/-- **Stacks 09CY.** `Lπ_! : D(π^{-1}O) ⟶ D(O)`, derived lower shriek along the projection
`π : Δ × C ⥤ C` on sheaves of modules. This is the `proj` parameter of
`Stacks.SimplicialModules.augmentedLowerShriek`, now a constructed functor rather than a
hypothesis. -/
abbrev derivedProjectionLowerShriek :
    DerivedCategory (SheafOfModules.{w} (projectionRing C J O)) ⥤
      DerivedCategory (SheafOfModules.{w} O) :=
  derivedLowerShriek (projectionTopology C J) J (projection C) O

/-- **Stacks 09CY.** `Lπ_!` is left adjoint to derived restriction along `π`. -/
abbrev derivedProjectionLowerShriekAdjunction :
    derivedProjectionLowerShriek C J O ⊣
      derivedRestriction (projectionTopology C J) J (projection C) O :=
  derivedModuleLowerShriekAdjunction (projectionTopology C J) J O (projection C)

/-- **Stacks 09CY.** `Lπ_!` commutes with the shift. Recorded as an `example` rather than a
declaration: the instance is `derivedLowerShriek_commShift` and is found by search here, which
is what this checks. -/
example : (derivedProjectionLowerShriek C J O).CommShift ℤ := inferInstance

/-! ### Nothing regresses on a site with fibre products -/

section HasPullbacks

variable (C : Type w) [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)

/-- On a site with fibre products, continuity of `π` is found by instance search. -/
example : (projection C).IsContinuous (projectionTopology C J) J := inferInstance

/-- On a site with fibre products, cocontinuity of `π` is found by instance search. -/
example : (projection C).IsCocontinuous (projectionTopology C J) J := inferInstance

/-- On a site with fibre products, the covering-pullback clause for `π` is found by instance
search. So a consumer that used to supply `[HasPullbacks C]` keeps all three hypotheses of the
section above for free, and dropping that hypothesis from the statements costs nothing. -/
example : Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C) :=
  inferInstance

end HasPullbacks

end Stacks.SimplicialModules

end
