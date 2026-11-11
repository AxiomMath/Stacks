module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.ClosedAffineBases
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# Compatible systems of pseudo-coherent complexes on an algebraic space over an inverse limit

Let `(Aₙ)` be an inverse system of rings whose transition maps are surjective with locally
nilpotent kernels, let `A = lim Aₙ`, and fix a big fppf site containing `Spec A` and every
`Spec Aₙ`. Over `Spec A`, read as an algebraic space, fix an algebraic space `X` which is
proper, flat and of finite presentation, and write `Xₙ = X ×_{Spec A} Spec Aₙ` for its
infinitesimal base changes, each a closed subspace of `X`. Grothendieck's existence theorem in
its derived form for algebraic spaces starts from a compatible system `(Kₙ, φₙ)` of
pseudo-coherent objects of `D(𝒪_{Xₙ})`, where `φₙ` exhibits `Kₙ` as the derived restriction of
`Kₙ₊₁`, and produces a pseudo-coherent object of `D(𝒪_X)` restricting to all of them. This
module records the standing data of that theorem.

It is the algebraic-space form of
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation` (Tag 0DIB) and shares its
affine base vocabulary: the inverse-limit base, the affine base at a level and the two
structural morphisms between those bases are imported from that module rather than restated.

## Main definitions

* `AlgebraicGeometry.Space.limitBaseObject` and `AlgebraicGeometry.Space.baseObjectAt`: the
  inverse-limit base and the affine base at a level, as objects of the big fppf category over
  the inverse-limit base, with structure morphism
  `AlgebraicGeometry.Space.baseObjectProjection` and transition morphism
  `AlgebraicGeometry.Space.baseObjectTransition`.
* `AlgebraicGeometry.Space.baseSpaceProjection` and
  `AlgebraicGeometry.Space.baseSpaceTransition`: those two morphisms, read as morphisms of
  algebraic spaces.
* `AlgebraicGeometry.Space.spaceAt`: the base change of an algebraic space over the
  inverse-limit base to the affine base at a level, with its two projections
  `AlgebraicGeometry.Space.spaceProjection` and
  `AlgebraicGeometry.Space.spaceBaseProjection` and transition morphism
  `AlgebraicGeometry.Space.transitionSpace`.
* `AlgebraicGeometry.Space.ringedSiteAt` and
  `AlgebraicGeometry.Space.derivedCategoryAt`: the small étale ringed site of that base change
  and the derived category of modules over its structure sheaf, in which the objects of the
  theorem live; `AlgebraicGeometry.Space.IsPseudoCoherentOn` is pseudo-coherence there and
  `AlgebraicGeometry.Space.DerivedPullbackAt` is the derived pullback along the transition
  morphism.
* `AlgebraicGeometry.Space.DerivedExistenceSituation`: the rings, the algebraic space and the
  compatible family of pseudo-coherent derived objects of Stacks 0DIK, compared through a derived
  pullback carried as a field; Situation 0DIK itself, with the derived pullback constructed, is
  `AlgebraicGeometry.Space.DerivedExistenceSystem`, which maps to it.
* `AlgebraicGeometry.Space.DerivedExistenceSituation.stageProjection`: the structure morphism
  `Xₙ → Spec Aₙ` of the base change at level `n`, the morphism over which the objects `Kₙ` of
  the situation are studied.

## Main results

* `AlgebraicGeometry.Space.baseObjectTransition_baseObjectProjection` and
  `AlgebraicGeometry.Space.baseSpaceTransition_baseSpaceProjection`: the transitions of affine
  bases are morphisms over the inverse-limit base.
* `AlgebraicGeometry.Space.isPullback_spaceAt`: the base change at a level is cartesian in the
  category of algebraic spaces over the inverse-limit base.
* `AlgebraicGeometry.Space.transitionSpace_spaceProjection` and
  `AlgebraicGeometry.Space.transitionSpace_spaceBaseProjection`: the transition morphism
  between consecutive base changes lies over `X` and over the transition of affine bases.
  Together these say that the base changes form a compatible system over the affine bases, and
  by the universal property of the fibre product they characterize the transition morphism.
* `AlgebraicGeometry.Space.ringedSiteAt_eq_smallEtaleRingedSite`: the ringed site used here is
  the small étale ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` of the base
  change.
* `AlgebraicGeometry.Space.isProper_spaceBaseProjection`,
  `AlgebraicGeometry.Space.isFlat_spaceBaseProjection`,
  `AlgebraicGeometry.Space.isFinitePresentation_spaceBaseProjection` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_spaceBaseProjection`: properness, flatness,
  finite presentation and local finiteness of type pass from `X → Spec A` to the structure
  morphism `Xₙ → Spec Aₙ` of each infinitesimal base change, since that morphism is the base
  change of `X → Spec A` along `Spec Aₙ → Spec A`.
* `AlgebraicGeometry.Space.DerivedExistenceSituation.isProper_stageProjection`,
  `AlgebraicGeometry.Space.DerivedExistenceSituation.isFlat_stageProjection`,
  `AlgebraicGeometry.Space.DerivedExistenceSituation.isFinitePresentation_stageProjection` and
  `AlgebraicGeometry.Space.DerivedExistenceSituation.isLocallyOfFiniteType_stageProjection`:
  the same four properties of `Xₙ → Spec Aₙ` in a situation of Stacks 0DIK, where the
  hypotheses on `X → Spec A` are part of the data.
* `AlgebraicGeometry.Space.isClosedImmersion_baseSpaceProjection` and
  `AlgebraicGeometry.Space.isClosedImmersion_baseSpaceTransition`: when the transition maps of
  the inverse system are surjective, the affine base at a level is a closed subspace of the
  inverse-limit base and of the affine base at the next level.
* `AlgebraicGeometry.Space.isPullback_transitionSpace`: the transition morphism between
  consecutive base changes is cartesian over the transition of affine bases.
* `AlgebraicGeometry.Space.isClosedImmersion_spaceProjection`,
  `AlgebraicGeometry.Space.isClosedImmersion_transitionSpace` and their forms
  `AlgebraicGeometry.Space.DerivedExistenceSituation.closedSpaceProjection`,
  `AlgebraicGeometry.Space.DerivedExistenceSituation.closedTransitionSpace` in a situation of
  Stacks 0DIK: each infinitesimal base change is a closed subspace of the algebraic space and
  of the next infinitesimal base change, these being base changes of the two closed immersions
  of affine bases.

## Implementation notes

The index `n : ℕ` stands for the level `n + 1` of the source, as for Tag 0DIB, so that the
inverse system is a functor out of `ℕᵒᵖ` and its transitions are the images of
`homOfLE (Nat.le_succ n)`.

The transitions between the affine bases and between the infinitesimal base changes are
*defined* here rather than carried as data. The source presents `Xₙ ⊂ Xₙ₊₁` as a closed
subspace, and the two equations saying that such a morphism lies over `X` and over the
transition of affine bases determine it uniquely, by the universal property of the fibre
product; `transitionSpace` is that unique morphism, and `transitionSpace_spaceProjection`,
`transitionSpace_spaceBaseProjection` are the two equations. Likewise the transition of affine
bases is the morphism of the site induced by the ring transition, available because the
inclusion of a big fppf site into schemes is full and faithful. So `DerivedExistenceSituation`
records neither of these two morphisms.

Nor does it record that they are closed immersions. That `Xₙ` is a closed subspace of `X` and
of `Xₙ₊₁` is a consequence of the hypotheses the source does state, not a further assumption:
the transition maps `Aₙ₊₁ → Aₙ` are surjective, hence so is every projection `A → Aₙ` out of
the inverse limit, hence `Spec Aₙ → Spec A` and `Spec Aₙ → Spec Aₙ₊₁` are closed immersions,
and both `Xₙ → X` and `Xₙ → Xₙ₊₁` are base changes of those. This is
`AlgebraicGeometry.Space.DerivedExistenceSituation.closedSpaceProjection` and
`AlgebraicGeometry.Space.DerivedExistenceSituation.closedTransitionSpace`.

Membership of the affine bases in the chosen big fppf site is recorded as the fields
`containsLimitBase` and `containsBaseAt`, because `AlgebraicGeometry.BigFppfSite.Contains` is
a size condition that no geometric hypothesis supplies; it is not a restriction on the inverse
system.

`ringedSiteAt` is phrased as `AlgebraicGeometry.RingedTopos.toRingedSite` of the small étale
ringed *topos*, and not directly as `AlgebraicGeometry.Space.smallEtaleRingedSite`, although
`ringedSiteAt_eq_smallEtaleRingedSite` says the two are the same site. Both spellings are
needed and only this one makes the sheafification instances of the slices of the small étale
site available: `smallEtaleRingedSite` is a `def`, so instance search does not unfold its
projections, whereas the two abbreviations composed here are reducible. The ringed *topos* is
what the derived pullback of the comparison maps is taken along, so the reducible spelling is
also the one that keeps the two sides of `φ` on the same site.

The derived objects live over the structure sheaf of the ringed site, since
`AlgebraicGeometry.RingedSite.IsPseudoCoherent` is stated for a ringed site, while the derived
pullback along the transition morphism is taken for the corresponding morphism of ringed topoi;
the two carry the same data and `AlgebraicGeometry.RingedTopos.toRingedSite` is the
reassociation between them.

The comparison `φₙ` is stated in its adjoint form, as for Tag 0DIB: the source gives a map
`Kₙ₊₁ ⟶ Riₙ,* Kₙ` and asks that the adjoint `Liₙ^* Kₙ₊₁ ⟶ Kₙ` be an isomorphism, so recording
the adjoint together with its invertibility is exactly the derived base-change requirement. The
derived pullback itself is recorded as a
`Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback`, the library's form of the Tag 06YY
input: a total left derived functor of degreewise pullback *computed by a resolving class*,
hence a left derived functor by
`Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback.isLeftDerivedFunctor`. Any two left
derived functors of one functor are canonically isomorphic, so the invertibility of `φₙ` does
not depend on which one is recorded; Tag 06YY supplies one for every morphism of ringed topoi,
through `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback.ofResolving`.

`derivedCategoryAt`, `IsPseudoCoherentOn` and `DerivedPullbackAt` are abbreviations for the
three types the last four fields of the situation are phrased with. They are separated out
because each of the three carries a long list of sheafification and sheaf-composition instance
arguments for the small étale site, which are then resolved once in their own declarations
rather than all over again inside the structure.

A scheme of the site read as an algebraic space is `AlgebraicGeometry.schemeSpace` of
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeAsSpace.lean`, which takes the site, the base
scheme and the containment implicitly; it comes with the functor
`AlgebraicGeometry.schemeSpaceFunctor`, whose functoriality is what
`baseSpaceTransition_baseSpaceProjection` consumes.

### The generalization proposed in Tag 0DIR

Tag 0DIR proposes a generalization of the derived existence theorem of Tag 0DIQ in which
`X → Spec A` is assumed only separated and of finite presentation, each `Kₙ` is assumed only
pseudo-coherent relative to `Aₙ` and supported on a closed subset of `Xₙ` proper over `Aₙ`, and
the complex `K` produced is correspondingly only pseudo-coherent relative to `A` and supported
on a closed subset of `X` proper over `A`. That generalization is asserted there to be probable
and no precise statement of it is given, so it is not stated or proved anywhere in this library.

What *is* proved is the comparison of hypotheses on the geometry, in
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/DerivedExistenceHypotheses.lean`: in the
situation of Tag 0DIK the morphism `X → Spec A` is proper, hence separated, and is of finite
presentation, so the two conditions the generalization places on `X` hold, and each
`Xₙ → Spec Aₙ` is proper, flat and of finite presentation by the base-change results above, so
every closed subset of `Xₙ` is proper over `Aₙ` and the support condition the generalization
places on `Kₙ` holds for every `Kₙ`. The comparison of the pseudo-coherence conditions is not
carried out here; its two ingredients are in the library: relative pseudo-coherence for a
morphism of algebraic spaces (Tag 0CSY) is `AlgebraicGeometry.Space.IsRelativelyPseudoCoherent`,
and its identification with pseudo-coherence on the source for a flat morphism locally of finite
presentation (Tag 0DII) is
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection baseTransition)
open Stacks.Cohomology.DerivedPushforward (LeftDerivedPullback)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))

/-! ### The affine bases as objects of the big fppf category over the inverse-limit base -/

/-- The inverse-limit base, viewed as the terminal object of the big fppf category over
itself. -/
abbrev limitBaseObject : BigFppfOver B (limitBase F) hS := Over.mk (𝟙 (B.obj hS))

/-- The affine base at level `n`, viewed as an object of the big fppf category over the
inverse-limit base. -/
def baseObjectAt (n : ℕ) : BigFppfOver B (limitBase F) hS :=
  Over.mk (ObjectProperty.homMk (baseProjection F n) : B.obj (hSn n) ⟶ B.obj hS)

/-- The structure morphism of the affine base at level `n` to the inverse-limit base, in the
big fppf category over the inverse-limit base. -/
def baseObjectProjection (n : ℕ) :
    baseObjectAt F B hS hSn n ⟶ limitBaseObject F B hS :=
  Over.homMk (baseObjectAt F B hS hSn n).hom (by simp)

/-- The transition morphism from the affine base at level `n` to the one at level `n + 1`, in
the big fppf category over the inverse-limit base: the morphism of the site induced by the
transition of rings, which lies over the inverse-limit base because the projection out of the
inverse limit factors through the next level. -/
def baseObjectTransition (n : ℕ) :
    baseObjectAt F B hS hSn n ⟶ baseObjectAt F B hS hSn (n + 1) :=
  Over.homMk (ObjectProperty.homMk (baseTransition F n) :
      B.obj (hSn n) ⟶ B.obj (hSn (n + 1)))
    (ObjectProperty.hom_ext _
      (show baseTransition F n ≫ baseProjection F (n + 1) = baseProjection F n by
        rw [← Spec.map_comp, limit.w]))

/-- The transition morphisms between consecutive affine bases are morphisms over the
inverse-limit base. -/
@[reassoc (attr := simp)]
lemma baseObjectTransition_baseObjectProjection (n : ℕ) :
    baseObjectTransition F B hS hSn n ≫ baseObjectProjection F B hS hSn (n + 1) =
      baseObjectProjection F B hS hSn n :=
  Over.OverMorphism.ext (Over.w (baseObjectTransition F B hS hSn n))

/-- The structure morphism of the affine base at level `n`, read as a morphism of algebraic
spaces over the inverse-limit base. -/
def baseSpaceProjection (n : ℕ) :
    schemeSpace (baseObjectAt F B hS hSn n) ⟶
      schemeSpace (limitBaseObject F B hS) :=
  (schemeSpaceFunctor B (limitBase F) hS).map (baseObjectProjection F B hS hSn n)

/-- The transition morphism between consecutive affine bases, read as a morphism of algebraic
spaces over the inverse-limit base. -/
def baseSpaceTransition (n : ℕ) :
    schemeSpace (baseObjectAt F B hS hSn n) ⟶
      schemeSpace (baseObjectAt F B hS hSn (n + 1)) :=
  (schemeSpaceFunctor B (limitBase F) hS).map (baseObjectTransition F B hS hSn n)

/-- The transition morphisms between consecutive affine bases are morphisms over the
inverse-limit base, as morphisms of algebraic spaces. -/
@[reassoc (attr := simp)]
lemma baseSpaceTransition_baseSpaceProjection (n : ℕ) :
    baseSpaceTransition F B hS hSn n ≫ baseSpaceProjection F B hS hSn (n + 1) =
      baseSpaceProjection F B hS hSn n :=
  ((schemeSpaceFunctor B (limitBase F) hS).map_comp
      (baseObjectTransition F B hS hSn n)
      (baseObjectProjection F B hS hSn (n + 1))).symm.trans
    (congrArg (fun g => (schemeSpaceFunctor B (limitBase F) hS).map g)
      (baseObjectTransition_baseObjectProjection F B hS hSn n))

/-! ### Infinitesimal base changes of an algebraic space over the inverse-limit base -/

variable (X : Over (schemeSpace (limitBaseObject F B hS)))

/-- The infinitesimal base change at level `n` of an algebraic space over the inverse-limit
base: its fibre product with the affine base at level `n`. -/
abbrev spaceAt (n : ℕ) : AlgebraicSpaces B (limitBase F) hS :=
  AlgebraicSpaces.fiberProduct B (limitBase F) hS (baseSpaceProjection F B hS hSn n) X.hom

/-- The projection of the base change at level `n` to the algebraic space itself. As soon as
the transition maps of the inverse system are surjective it is a closed immersion, by
`AlgebraicGeometry.Space.isClosedImmersion_spaceProjection`, so it presents the base change as
a closed subspace. -/
def spaceProjection (n : ℕ) : spaceAt F B hS hSn X n ⟶ X.left :=
  ObjectProperty.homMk (pullback.snd (baseSpaceProjection F B hS hSn n).hom X.hom.hom)

/-- The projection of the base change at level `n` to the affine base at level `n`. -/
def spaceBaseProjection (n : ℕ) :
    spaceAt F B hS hSn X n ⟶ schemeSpace (baseObjectAt F B hS hSn n) :=
  ObjectProperty.homMk (pullback.fst (baseSpaceProjection F B hS hSn n).hom X.hom.hom)

/-- The base change at level `n` is a fibre product of the affine base at level `n` and the
algebraic space, in the category of algebraic spaces over the inverse-limit base. -/
lemma isPullback_spaceAt (n : ℕ) :
    IsPullback (spaceBaseProjection F B hS hSn X n) (spaceProjection F B hS hSn X n)
      (baseSpaceProjection F B hS hSn n) X.hom :=
  AlgebraicSpaces.isPullback_fiberProduct B (limitBase F) hS
    (baseSpaceProjection F B hS hSn n) X.hom

/-- The canonical morphism from the base change at level `n` to the one at level `n + 1`: the
unique morphism lying over the algebraic space and over the transition of affine bases. -/
def transitionSpace (n : ℕ) : spaceAt F B hS hSn X n ⟶ spaceAt F B hS hSn X (n + 1) :=
  (isPullback_spaceAt F B hS hSn X (n + 1)).lift
    (spaceBaseProjection F B hS hSn X n ≫ baseSpaceTransition F B hS hSn n)
    (spaceProjection F B hS hSn X n) (by
      rw [Category.assoc, baseSpaceTransition_baseSpaceProjection]
      exact (isPullback_spaceAt F B hS hSn X n).w)

/-- The transition morphism between consecutive base changes lies over the algebraic space. -/
@[reassoc (attr := simp)]
lemma transitionSpace_spaceProjection (n : ℕ) :
    transitionSpace F B hS hSn X n ≫ spaceProjection F B hS hSn X (n + 1) =
      spaceProjection F B hS hSn X n :=
  IsPullback.lift_snd _ _ _ _

/-- The transition morphism between consecutive base changes lies over the transition of
affine bases. -/
@[reassoc (attr := simp)]
lemma transitionSpace_spaceBaseProjection (n : ℕ) :
    transitionSpace F B hS hSn X n ≫ spaceBaseProjection F B hS hSn X (n + 1) =
      spaceBaseProjection F B hS hSn X n ≫ baseSpaceTransition F B hS hSn n :=
  IsPullback.lift_fst _ _ _ _

/-! ### Properties inherited by the infinitesimal base changes -/

/-- A property of morphisms of algebraic spaces stable under base change passes from the
algebraic space to its base change at level `n`, over the affine base at level `n`. -/
private theorem spaceBaseProjection_of_isStableUnderBaseChange
    (P : MorphismProperty (AlgebraicSpaces B (limitBase F) hS)) [P.IsStableUnderBaseChange]
    (hX : P X.hom) (n : ℕ) : P (spaceBaseProjection F B hS hSn X n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_spaceAt F B hS hSn X n).flip hX

/-- If the algebraic space is proper over the inverse-limit base, then the base change at
level `n` is proper over the affine base at level `n`. -/
theorem isProper_spaceBaseProjection (hX : IsProper B (limitBase F) hS X.hom.hom) (n : ℕ) :
    IsProper B (limitBase F) hS (spaceBaseProjection F B hS hSn X n).hom :=
  spaceBaseProjection_of_isStableUnderBaseChange F B hS hSn X
    (fun ⦃_ _⦄ f => IsProper B (limitBase F) hS f.hom) hX n

/-- If the algebraic space is flat over the inverse-limit base, then the base change at
level `n` is flat over the affine base at level `n`. -/
theorem isFlat_spaceBaseProjection (hX : IsFlat B (limitBase F) hS X.hom.hom) (n : ℕ) :
    IsFlat B (limitBase F) hS (spaceBaseProjection F B hS hSn X n).hom :=
  have := isFlat_isStableUnderBaseChange B (limitBase F) hS
  spaceBaseProjection_of_isStableUnderBaseChange F B hS hSn X
    (fun ⦃_ _⦄ f => IsFlat B (limitBase F) hS f.hom) hX n

/-- If the algebraic space is of finite presentation over the inverse-limit base, then the base
change at level `n` is of finite presentation over the affine base at level `n`. -/
theorem isFinitePresentation_spaceBaseProjection
    (hX : IsFinitePresentation B (limitBase F) hS X.hom.hom) (n : ℕ) :
    IsFinitePresentation B (limitBase F) hS (spaceBaseProjection F B hS hSn X n).hom :=
  spaceBaseProjection_of_isStableUnderBaseChange F B hS hSn X
    (fun ⦃_ _⦄ f => IsFinitePresentation B (limitBase F) hS f.hom) hX n

/-- If the algebraic space is locally of finite type over the inverse-limit base, then the base
change at level `n` is locally of finite type over the affine base at level `n`. -/
theorem isLocallyOfFiniteType_spaceBaseProjection
    (hX : IsLocallyOfFiniteType B (limitBase F) hS X.hom.hom) (n : ℕ) :
    IsLocallyOfFiniteType B (limitBase F) hS (spaceBaseProjection F B hS hSn X n).hom :=
  have := isLocallyOfFiniteType_isStableUnderBaseChange B (limitBase F) hS
  spaceBaseProjection_of_isStableUnderBaseChange F B hS hSn X
    (fun ⦃_ _⦄ f => IsLocallyOfFiniteType B (limitBase F) hS f.hom) hX n

/-! ### The infinitesimal base changes are closed subspaces -/

/-- The affine base at level `n` is a closed subspace of the inverse-limit base: the projection
`A → Aₙ` out of an inverse limit with surjective transition maps is surjective, so
`Spec Aₙ → Spec A` is a closed immersion of schemes. -/
theorem isClosedImmersion_baseSpaceProjection
    (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    IsClosedImmersion B (limitBase F) hS (baseSpaceProjection F B hS hSn n).hom :=
  (presheaf_yoneda_map_iff B (limitBase F) hS
      AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
      (baseObjectProjection F B hS hSn n)).2
    (GrothendieckExistence.isClosedImmersion_baseProjection F hFs n)

/-- The affine base at level `n` is a closed subspace of the affine base at level `n + 1`: the
transition map `Aₙ₊₁ → Aₙ` is surjective. -/
theorem isClosedImmersion_baseSpaceTransition
    (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    IsClosedImmersion B (limitBase F) hS (baseSpaceTransition F B hS hSn n).hom :=
  (presheaf_yoneda_map_iff B (limitBase F) hS
      AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
      (baseObjectTransition F B hS hSn n)).2
    (GrothendieckExistence.isClosedImmersion_baseTransition F hFs n)

/-- The base change at level `n` is the base change along the structure morphism of the base
change at level `n + 1` of the transition of affine bases.

Pasting this square with the cartesian square of the base change at level `n + 1` gives the
cartesian square of the base change at level `n`, so the pasting law for pullbacks gives the
claim. -/
lemma isPullback_transitionSpace (n : ℕ) :
    IsPullback (spaceBaseProjection F B hS hSn X n) (transitionSpace F B hS hSn X n)
      (baseSpaceTransition F B hS hSn n) (spaceBaseProjection F B hS hSn X (n + 1)) :=
  IsPullback.of_bot
    (by
      rw [transitionSpace_spaceProjection, baseSpaceTransition_baseSpaceProjection]
      exact isPullback_spaceAt F B hS hSn X n)
    (transitionSpace_spaceBaseProjection F B hS hSn X n).symm
    (isPullback_spaceAt F B hS hSn X (n + 1))

/-- The infinitesimal base change at level `n` is a closed subspace of the algebraic space: it
is the base change of the closed immersion `Spec Aₙ → Spec A` along `X → Spec A`. -/
theorem isClosedImmersion_spaceProjection
    (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    IsClosedImmersion B (limitBase F) hS (spaceProjection F B hS hSn X n).hom :=
  (isClosedImmersion_isStableUnderBaseChange B (limitBase F) hS).of_isPullback
    (AlgebraicSpaces.isPullback_hom B (limitBase F) hS (isPullback_spaceAt F B hS hSn X n))
    (isClosedImmersion_baseSpaceProjection F B hS hSn hFs n)

/-- The infinitesimal base change at level `n` is a closed subspace of the one at level
`n + 1`: it is the base change of the closed immersion `Spec Aₙ → Spec Aₙ₊₁` along
`Xₙ₊₁ → Spec Aₙ₊₁`. -/
theorem isClosedImmersion_transitionSpace
    (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    IsClosedImmersion B (limitBase F) hS (transitionSpace F B hS hSn X n).hom :=
  (isClosedImmersion_isStableUnderBaseChange B (limitBase F) hS).of_isPullback
    (AlgebraicSpaces.isPullback_hom B (limitBase F) hS
      (isPullback_transitionSpace F B hS hSn X n))
    (isClosedImmersion_baseSpaceTransition F B hS hSn hFs n)

/-! ### Derived objects on the infinitesimal base changes -/

/-- The small étale ringed site of the base change at level `n`. -/
abbrev ringedSiteAt (n : ℕ) : RingedSite.{u + 1, u, u} :=
  RingedTopos.toRingedSite (smallEtaleRingedTopos B (limitBase F) hS (spaceAt F B hS hSn X n))

/-- The ringed site of the base change at level `n` is its small étale ringed site. -/
lemma ringedSiteAt_eq_smallEtaleRingedSite (n : ℕ) :
    ringedSiteAt F B hS hSn X n =
      smallEtaleRingedSite B (limitBase F) hS (spaceAt F B hS hSn X n).1
        (spaceAt F B hS hSn X n).2 :=
  rfl

/-- The derived category of `𝒪`-modules on the base change at level `n`. -/
abbrev derivedCategoryAt (n : ℕ) :=
  DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteAt F B hS hSn X n).O))

/-- Pseudo-coherence, in the sense of Stacks 08FT, of a derived object on the base change at
level `n`. -/
abbrev IsPseudoCoherentOn (n : ℕ) (E : derivedCategoryAt F B hS hSn X n) : Prop :=
  RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1} (ringedSiteAt F B hS hSn X n) E

/-- The derived pullback along the transition morphism from level `n` to level `n + 1`, in the
form Stacks 06YY supplies it: a total left derived functor of degreewise pullback computed by a
resolving class. -/
abbrev DerivedPullbackAt (n : ℕ) :=
  LeftDerivedPullback.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B (limitBase F) hS (transitionSpace F B hS hSn X n))

/-! ### The standing situation -/

/-- The standing data of Grothendieck's existence theorem for algebraic spaces in its derived
form: an inverse system of rings with surjective, locally nilpotent transitions, a proper flat
algebraic space of finite presentation over the inverse-limit ring, and a compatible system of
pseudo-coherent objects on its infinitesimal base changes, compared through a total left derived
pullback `derivedPullback n` along each transition morphism carried as a field. Situation 0DIK of
the Stacks project, in which that derived pullback is the one constructed by Stacks 06YY, is
`AlgebraicGeometry.Space.DerivedExistenceSystem`; its
`AlgebraicGeometry.Space.DerivedExistenceSystem.toDerivedExistenceSituation` gives an object of
this structure. -/
structure DerivedExistenceSituation where
  /-- The inverse system of rings. -/
  system : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- Its consecutive transition maps are surjective. -/
  transition_surjective (n : ℕ) :
    Function.Surjective (system.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of those transition maps are locally nilpotent. -/
  transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (system.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent
  /-- The big fppf site in which the algebraic spaces are taken. -/
  B : BigFppfSite.{u}
  /-- The inverse-limit base belongs to the site. -/
  containsLimitBase : B.Contains (limitBase system)
  /-- Every affine base belongs to the site. -/
  containsBaseAt (n : ℕ) : B.Contains (baseAt system n)
  /-- The algebraic space over the inverse-limit base. -/
  X : Over (schemeSpace
    (limitBaseObject system B containsLimitBase))
  /-- The algebraic space is proper over the inverse-limit base. -/
  proper : IsProper B (limitBase system) containsLimitBase X.hom.hom
  /-- The algebraic space is flat over the inverse-limit base. -/
  flat : IsFlat B (limitBase system) containsLimitBase X.hom.hom
  /-- The algebraic space is of finite presentation over the inverse-limit base. -/
  finitePresentation :
    IsFinitePresentation B (limitBase system) containsLimitBase X.hom.hom
  /-- The derived object on the base change at level `n`. -/
  K (n : ℕ) : derivedCategoryAt system B containsLimitBase containsBaseAt X n
  /-- Each derived object is pseudo-coherent. -/
  pseudoCoherent (n : ℕ) :
    IsPseudoCoherentOn system B containsLimitBase containsBaseAt X n (K n)
  /-- The derived pullback along the transition morphism at level `n`. -/
  derivedPullback (n : ℕ) :
    DerivedPullbackAt system B containsLimitBase containsBaseAt X n
  /-- The comparison map, the adjoint of the transition map into the derived pushforward. -/
  φ (n : ℕ) : (derivedPullback n).functor.obj (K (n + 1)) ⟶ K n
  /-- The comparison map is an isomorphism: the derived restriction of the object at level
  `n + 1` is the object at level `n`. -/
  φ_isIso (n : ℕ) : IsIso (φ n)

namespace DerivedExistenceSituation

variable (D : DerivedExistenceSituation.{u})

/-- The structure morphism `Xₙ → Spec Aₙ` of the infinitesimal base change at level `n`. -/
abbrev stageProjection (n : ℕ) :
    spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n ⟶
      schemeSpace
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- Each infinitesimal base change is a closed subspace of the algebraic space, as Stacks 0DIK
views it: the projections `A → Aₙ` out of the inverse limit are surjective, so `Xₙ → X` is the
base change of a closed immersion of affine schemes. -/
theorem closedSpaceProjection (n : ℕ) :
    IsClosedImmersion D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom :=
  isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
    D.transition_surjective n

/-- Consecutive infinitesimal base changes are related by a closed immersion: `Xₙ → Xₙ₊₁` is
the base change of the closed immersion `Spec Aₙ → Spec Aₙ₊₁`. -/
theorem closedTransitionSpace (n : ℕ) :
    IsClosedImmersion D.B (limitBase D.system) D.containsLimitBase
      (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom :=
  isClosedImmersion_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X
    D.transition_surjective n

/-- Each infinitesimal base change is proper over its affine base. -/
theorem isProper_stageProjection (n : ℕ) :
    IsProper D.B (limitBase D.system) D.containsLimitBase (D.stageProjection n).hom :=
  isProper_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X D.proper n

/-- Each infinitesimal base change is flat over its affine base. -/
theorem isFlat_stageProjection (n : ℕ) :
    IsFlat D.B (limitBase D.system) D.containsLimitBase (D.stageProjection n).hom :=
  isFlat_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X D.flat n

/-- Each infinitesimal base change is of finite presentation over its affine base. -/
theorem isFinitePresentation_stageProjection (n : ℕ) :
    IsFinitePresentation D.B (limitBase D.system) D.containsLimitBase
      (D.stageProjection n).hom :=
  isFinitePresentation_spaceBaseProjection D.system D.B D.containsLimitBase
    D.containsBaseAt D.X D.finitePresentation n

/-- Each infinitesimal base change is locally of finite type over its affine base. -/
theorem isLocallyOfFiniteType_stageProjection (n : ℕ) :
    IsLocallyOfFiniteType D.B (limitBase D.system) D.containsLimitBase
      (D.stageProjection n).hom :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
    D.containsLimitBase (D.isFinitePresentation_stageProjection n).1

end DerivedExistenceSituation

end AlgebraicGeometry.Space

end
