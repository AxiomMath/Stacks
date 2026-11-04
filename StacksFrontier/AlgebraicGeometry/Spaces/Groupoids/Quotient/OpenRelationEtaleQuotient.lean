module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.FlatDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackModuliSpace

/-!
# Groupoids whose relation is an open subspace of the relative square (Stacks 0DU1)

Let `Y` be an algebraic space over a scheme `S` of a big fppf site and let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `Y` whose object space is flat and
locally of finite presentation over `Y` and whose pre-relation `(t, s) : R ⟶ U ×_Y U` is an
open immersion.  **Stacks 0DU1** says that `X = [U/R] = U/R` is then an algebraic space and
that `X ⟶ Y` is étale.  This file proves the two assertions about `U/R` and constructs the
canonical comparison `[U/R] ⟶ U/R`.

The open immersion is what makes the pre-relation a monomorphism, hence an equivalence
relation, and it is also what makes `s` and `t` flat and locally of finite presentation: both
projections of `U ×_Y U` are base changes of `U ⟶ Y`, and `(t, s)` is an open immersion, so
each of `s` and `t` is a composite of an open immersion with a flat, locally finitely
presented morphism.  Étaleness of `X ⟶ Y` is then flatness and local finite presentation
descended along the fppf covering `U ⟶ X` of **Stacks 06PG**, together with unramifiedness:
the relative diagonal `X ⟶ X ×_Y X` pulls back along the surjective, flat and locally
finitely presented `U ×_Y U ⟶ X ×_Y X` to `R ⟶ U ×_Y U`, which is an open immersion by
hypothesis, and being an open immersion is fpqc local on the base.

## Main definitions

* `AlgebraicGeometry.Space.groupoidRelativeSquare` and
  `AlgebraicGeometry.Space.groupoidRelativeSquareSpace`: the relative square `U ×_Y U`, read in
  the slice of presheaves over the base and as an object of the category of algebraic spaces.
* `AlgebraicGeometry.Space.Theorem04S6Quotient`: **Stacks 04S6 as a hypothesis** — the quotient
  sheaf of a groupoid in algebraic spaces cutting out an equivalence relation with flat,
  locally finitely presented source and target is an algebraic space.
* `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf`: **Stacks 0DU1**, the canonical
  comparison `[U/R] ⟶ U/R`, constructed as the descent of the quotient projection along the
  projection of Stacks 044R.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_groupoidPreRelation_of_isOpenImmersion`: an
  open pre-relation of a groupoid in algebraic spaces is an equivalence relation.
* `AlgebraicGeometry.Space.isFlat_source_of_isOpenImmersion`,
  `AlgebraicGeometry.Space.isFlat_target_of_isOpenImmersion`,
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_source_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_target_of_isOpenImmersion`: the source
  and target of such a groupoid are flat and locally of finite presentation as soon as the
  object space is flat and locally of finite presentation over the base.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`: **Stacks 0DU1**,
  the quotient `U/R` is an algebraic space.
* `AlgebraicGeometry.Space.isEtale_quotientSheafToBase_of_isOpenImmersion_of_isAlgebraicSpace`
  and `AlgebraicGeometry.Space.isEtale_quotientSheafToBase_of_isOpenImmersion`:
  **Stacks 0DU1**, the structural morphism `U/R ⟶ Y` is étale.
* `AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackToQuotientSheaf` and
  `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf_comp_toBase`: **Stacks 0DU1**, the two
  characterizations of the comparison — its composite with the projection `U ⟶ [U/R]` is the
  1-morphism Stacks 0458 attaches to the quotient map, and it is a morphism over the base.
* `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf_unique`: the comparison is the only
  1-morphism `[U/R] ⟶ U/R` with that restriction, by Stacks 0DUH.

## Implementation notes

Algebraicity of the quotient is **Stacks 04S6**, Theorem 10.1 of the Bootstrap chapter, in its
condition (1), `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf`, applied to the pre-relation
`(t, s)` of the groupoid.  Its inputs are that the pre-relation is an equivalence relation and
that `s` and `t` are flat and locally of finite presentation, and those are proved here from the
hypotheses of Stacks 0DU1.

The rest of the source proof uses Stacks 043C and Stacks 043X for
the equivalence relation, Stacks 03MO/03MN and Stacks 03XR/03XQ for the two properties of `s`
and `t`, Stacks 06PG for the covering map, Stacks 06NR and Stacks 0AHC for the descent of
flatness and local finite presentation, Stacks 041X for the fpqc locality of open immersions,
Stacks 05W1 for unramifiedness from the diagonal, and Stacks 06LU for étaleness.

The comparison `[U/R] ⟶ U/R` of the source statement — the forward half of the assertion
`X = [U/R] = U/R` — is a real construction and not a choice out of an existence statement: once
`U/R` is known to be an algebraic space — by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion` — the quotient
projection `U ⟶ U/R` is an invariant
morphism into an algebraic space, so `AlgebraicGeometry.Stack.quotientStackOfInvariant` descends
it, and Stacks 0DUH makes the descent the unique 1-morphism with that restriction.  What is
**not** proved here is that the comparison is an equivalence: that is the remaining half of
`[U/R] = U/R`, and it needs full faithfulness and essential surjectivity of the comparison over
the site, which this file does not address.

## References

* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 044L](https://stacks.math.columbia.edu/tag/044L)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06LU](https://stacks.math.columbia.edu/tag/06LU)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PG](https://stacks.math.columbia.edu/tag/06PG)
* [Stacks Project, Tag 0AHC](https://stacks.math.columbia.edu/tag/0AHC)
* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] hasSheafify_bigFppfOver

namespace Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Y : AlgebraicSpaces C S hS}

/-! ### The relative square of the object space -/

section RelativeSquare

variable (G : GroupoidInAlgebraicSpaces C S hS Y)

/-- The relative square `U ×_Y U` of the object space of a groupoid in algebraic spaces over
`Y`, read as the categorical product of the object space with itself in the slice of presheaves
over the base.  This is the target of the pre-relation
`AlgebraicGeometry.Space.groupoidPreRelation`. -/
noncomputable abbrev groupoidRelativeSquare : Over Y.obj :=
  Over.mk G.objectsToBase.hom ⨯ Over.mk G.objectsToBase.hom

/-- The two projections of the relative square are a fibre square of the structure morphism of
the object space with itself: the categorical product in a slice is the fibre product. -/
theorem isPullback_groupoidRelativeSquare :
    IsPullback
      (prod.fst : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left
      (prod.snd : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left
      G.objectsToBase.hom G.objectsToBase.hom :=
  Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom)
      (prod.snd : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom))
    (prodIsProd _ _)

/-- **Stacks 02X2** at the relative square: `U ×_Y U` is an algebraic space. -/
theorem isAlgebraicSpace_groupoidRelativeSquare :
    IsAlgebraicSpace C S hS (groupoidRelativeSquare G).left :=
  isAlgebraicSpace_of_isPullback G.objects.property G.objects.property Y.property.isSheaf
    Y.property.diagonal_representable (isPullback_groupoidRelativeSquare G)

/-- The relative square `U ×_Y U`, as an object of the category of algebraic spaces over
`S`. -/
noncomputable abbrev groupoidRelativeSquareSpace : AlgebraicSpaces C S hS :=
  ⟨(groupoidRelativeSquare G).left, isAlgebraicSpace_groupoidRelativeSquare G⟩

/-- The first projection of the relative square, as a morphism of algebraic spaces. -/
noncomputable abbrev groupoidRelativeSquareFst :
    groupoidRelativeSquareSpace G ⟶ G.objects :=
  ObjectProperty.homMk (prod.fst : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left

/-- The second projection of the relative square, as a morphism of algebraic spaces. -/
noncomputable abbrev groupoidRelativeSquareSnd :
    groupoidRelativeSquareSpace G ⟶ G.objects :=
  ObjectProperty.homMk (prod.snd : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left

/-- The fibre square of the relative square, read in the category of algebraic spaces over
`S`. -/
theorem isPullback_groupoidRelativeSquareSpace :
    IsPullback (groupoidRelativeSquareFst G) (groupoidRelativeSquareSnd G)
      G.objectsToBase G.objectsToBase :=
  IsPullback.of_map (ObjectProperty.ι (IsAlgebraicSpace C S hS))
    (ObjectProperty.hom_ext _ (isPullback_groupoidRelativeSquare G).w)
    (isPullback_groupoidRelativeSquare G)

/-- Every property of morphisms of algebraic spaces stable under base change that the structure
morphism of the object space has is had by the first projection of the relative square. -/
theorem groupoidRelativeSquareFst_prop (P : MorphismProperty (AlgebraicSpaces C S hS))
    (hP : P.IsStableUnderBaseChange) (h : P G.objectsToBase) :
    P (groupoidRelativeSquareFst G) :=
  have := hP
  MorphismProperty.of_isPullback (isPullback_groupoidRelativeSquareSpace G).flip h

/-- Every property of morphisms of algebraic spaces stable under base change that the structure
morphism of the object space has is had by the second projection of the relative square. -/
theorem groupoidRelativeSquareSnd_prop (P : MorphismProperty (AlgebraicSpaces C S hS))
    (hP : P.IsStableUnderBaseChange) (h : P G.objectsToBase) :
    P (groupoidRelativeSquareSnd G) :=
  have := hP
  MorphismProperty.of_isPullback (isPullback_groupoidRelativeSquareSpace G) h

/-- The target map of a groupoid in algebraic spaces is the pre-relation followed by the first
projection of the relative square. -/
theorem target_hom_eq_groupoidPreRelation_comp :
    G.target.hom =
      (groupoidPreRelation G).left ≫
        (prod.fst : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left := by
  simp [groupoidPreRelation, ← Over.comp_left]

/-- The source map of a groupoid in algebraic spaces is the pre-relation followed by the second
projection of the relative square. -/
theorem source_hom_eq_groupoidPreRelation_comp :
    G.source.hom =
      (groupoidPreRelation G).left ≫
        (prod.snd : groupoidRelativeSquare G ⟶ Over.mk G.objectsToBase.hom).left := by
  simp [groupoidPreRelation, ← Over.comp_left]

/-- Flat morphisms of algebraic spaces are stable under composition. -/
private instance flatProperty_isStableUnderComposition :
    (flatProperty C S hS).IsStableUnderComposition :=
  { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
      isFlat_comp C S hS A₁.property A₂.property A₃.property u.hom v.hom hu hv }

/-- Locally finitely presented morphisms of algebraic spaces are stable under composition. -/
private instance locallyOfFinitePresentationProperty_isStableUnderComposition :
    (locallyOfFinitePresentationProperty C S hS).IsStableUnderComposition :=
  { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
      isLocallyOfFinitePresentation_comp C S hS A₁.property A₂.property A₃.property
        u.hom v.hom hu hv }

/-- A property of morphisms of algebraic spaces stable under base change and composition that the
pre-relation and the structure morphism of the object space have is had by the target and the
source maps of the groupoid. -/
private theorem target_and_source_prop_of_preRelation
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition]
    (hR : P (ObjectProperty.homMk (groupoidPreRelation G).left :
      G.arrows ⟶ groupoidRelativeSquareSpace G))
    (h : P G.objectsToBase) : P G.target ∧ P G.source := by
  set jas : G.arrows ⟶ groupoidRelativeSquareSpace G := ObjectProperty.homMk _
  have ht : G.target = jas ≫ groupoidRelativeSquareFst G :=
    ObjectProperty.hom_ext _ (target_hom_eq_groupoidPreRelation_comp G)
  have hs : G.source = jas ≫ groupoidRelativeSquareSnd G :=
    ObjectProperty.hom_ext _ (source_hom_eq_groupoidPreRelation_comp G)
  rw [ht, hs]
  exact ⟨MorphismProperty.comp_mem _ _ _ hR (groupoidRelativeSquareFst_prop G P inferInstance h),
    MorphismProperty.comp_mem _ _ _ hR (groupoidRelativeSquareSnd_prop G P inferInstance h)⟩

end RelativeSquare

/-! ### Consequences of the pre-relation being an open immersion -/

section OpenRelation

variable {G : GroupoidInAlgebraicSpaces C S hS Y}
  (hopen : IsOpenImmersion C S hS (groupoidPreRelation G).left)

include hopen

/-- **Stacks 043C.** If the pre-relation of a groupoid in algebraic spaces is an open immersion
then it is an equivalence relation: an open immersion is an immersion, hence a monomorphism by
Stacks 042R, and the induced relation on the points of every test scheme is an equivalence
relation by Stacks 043X. -/
theorem isEquivalenceRelation_groupoidPreRelation_of_isOpenImmersion :
    CategoryTheory.IsEquivalenceRelation (groupoidPreRelation G).target
      (groupoidPreRelation G).source := by
  have hmonoLeft : Mono (groupoidPreRelation G).left :=
    mono_of_isImmersion C S hS (isImmersion_of_isOpenImmersion C S hS hopen)
  refine (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (groupoidPreRelation G)).2 ⟨?_, groupoidPreRelation_isPreEquivalenceRelation G⟩
  refine ⟨fun {Z} a b hab => ?_⟩
  exact Over.OverMorphism.ext
    ((cancel_mono (groupoidPreRelation G).left).mp (congrArg (fun k => k.left) hab))

/-- **Stacks 0467.** An open pre-relation is flat: it is étale, and an étale morphism of
algebraic spaces is flat. -/
theorem isFlat_groupoidPreRelation_of_isOpenImmersion :
    IsFlat C S hS (groupoidPreRelation G).left :=
  isFlat_of_isEtale C S hS
    (isEtale_of_isOpenImmersion C S hS hopen)

/-- **Stacks 06CN.** An open pre-relation is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_groupoidPreRelation_of_isOpenImmersion :
    IsLocallyOfFinitePresentation C S hS (groupoidPreRelation G).left :=
  isLocallyOfFinitePresentation_of_isOpenImmersion C S hS hopen

/-- **Stacks 03MN and Stacks 03MO.** The target map of a groupoid in algebraic spaces with open
pre-relation is flat as soon as the object space is flat over the base: the first projection of
the relative square is a base change of the structure morphism of the object space, and the
target is the pre-relation followed by it. -/
theorem isFlat_target_of_isOpenImmersion (hflat : IsFlat C S hS G.objectsToBase.hom) :
    IsFlat C S hS G.target.hom :=
  (target_and_source_prop_of_preRelation _ (flatProperty C S hS)
    (isFlat_groupoidPreRelation_of_isOpenImmersion hopen) hflat).1

/-- **Stacks 03MN and Stacks 03MO.** The source map of a groupoid in algebraic spaces with open
pre-relation is flat as soon as the object space is flat over the base. -/
theorem isFlat_source_of_isOpenImmersion (hflat : IsFlat C S hS G.objectsToBase.hom) :
    IsFlat C S hS G.source.hom :=
  (target_and_source_prop_of_preRelation _ (flatProperty C S hS)
    (isFlat_groupoidPreRelation_of_isOpenImmersion hopen) hflat).2

/-- **Stacks 03XQ and Stacks 03XR.** The target map of a groupoid in algebraic spaces with open
pre-relation is locally of finite presentation as soon as the object space is locally of finite
presentation over the base. -/
theorem isLocallyOfFinitePresentation_target_of_isOpenImmersion
    (hlfp : IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom) :
    IsLocallyOfFinitePresentation C S hS G.target.hom :=
  (target_and_source_prop_of_preRelation _ (locallyOfFinitePresentationProperty C S hS)
    (isLocallyOfFinitePresentation_groupoidPreRelation_of_isOpenImmersion hopen) hlfp).1

/-- **Stacks 03XQ and Stacks 03XR.** The source map of a groupoid in algebraic spaces with open
pre-relation is locally of finite presentation as soon as the object space is locally of finite
presentation over the base. -/
theorem isLocallyOfFinitePresentation_source_of_isOpenImmersion
    (hlfp : IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom) :
    IsLocallyOfFinitePresentation C S hS G.source.hom :=
  (target_and_source_prop_of_preRelation _ (locallyOfFinitePresentationProperty C S hS)
    (isLocallyOfFinitePresentation_groupoidPreRelation_of_isOpenImmersion hopen) hlfp).2

end OpenRelation

/-! ### Open immersions are fpqc local on the base -/

section FpqcLocal

/-- Open immersions of algebraic spaces are stable under isomorphisms. -/
private theorem openImmersionProperty_respectsIso (C : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : C.Contains S) :
    (openImmersionProperty C S hS).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)))
    (ObjectProperty.ι (IsAlgebraicSpace C S hS))

/-- **Stacks 041X in the form the diagonal argument of Stacks 0DU1 uses.** In a fibre square of
algebraic spaces whose right-hand morphism is surjective, flat and locally of finite
presentation, the left-hand morphism is an open immersion if its base change is: a surjective,
flat and locally finitely presented morphism is a one-member fppf covering, hence an fpqc
covering by Stacks 0DFQ, and being an open immersion is fpqc local on the base. -/
theorem isOpenImmersion_of_isPullback_of_fppfCover
    {A B D E : AlgebraicSpaces C S hS} {a : A ⟶ B} {b : A ⟶ D} {f : B ⟶ E} {g : D ⟶ E}
    (sq : IsPullback a b f g) (hgsurj : IsSurjective C S hS g.hom)
    (hgflat : IsFlat C S hS g.hom)
    (hglfp : IsLocallyOfFinitePresentation C S hS g.hom)
    (hb : IsOpenImmersion C S hS b.hom) : IsOpenImmersion C S hS f.hom := by
  have hcov : IsFppfCovering C S hS (fun _ : Unit => D.obj) (fun _ => g.hom) :=
    { target_isAlgebraicSpace := E.property
      source_isAlgebraicSpace := fun _ => D.property
      flat := fun _ => hgflat
      locallyOfFinitePresentation := fun _ => hglfp
      jointly_surjective := by
        simpa only [Set.iUnion_const] using Set.range_eq_univ.mpr hgsurj }
  have hK : Presieve.ofArrows (fun _ : Unit => D) (fun _ => g) ∈
      Topology.precoverage.{u, 0} .fpqc C S hS E :=
    ⟨Unit, (fun _ => D), (fun _ => g), rfl, E.property, (fun _ => D.property),
      isFpqcCovering_of_isFppfCovering C S hS _ _ hcov⟩
  have hri := openImmersionProperty_respectsIso C S hS
  have hloc : (openImmersionProperty C S hS).IsLocalAtTarget
      (Topology.precoverage.{u, 0} .fpqc C S hS) :=
    openImmersion_isLocalAtTarget_fpqc.{u, 0} C S hS
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := openImmersionProperty C S hS)
    (K := Topology.precoverage.{u, 0} .fpqc C S hS) hK ?_
  rintro _ _ _ ⟨i⟩
  have he : openImmersionProperty C S hS (sq.isoPullback.inv ≫ b) :=
    MorphismProperty.RespectsIso.precomp (openImmersionProperty C S hS) sq.isoPullback.inv b hb
  simpa only [IsPullback.isoPullback_inv_snd] using he

end FpqcLocal

/-! ### Stacks 04S6, carried -/

/-- **Stacks 04S6 as a hypothesis**, in the shape Stacks 0DU1 consumes it: the quotient sheaf
of a groupoid in algebraic spaces over a base algebraic space whose pre-relation cuts out an
equivalence relation and whose source and target are flat and locally of finite presentation is
an algebraic space.

This is a condition and proves nothing.  Stacks 04S6 is Theorem 10.1 of the Bootstrap chapter;
its only forms on base,
`AlgebraicGeometry.Space.isAlgebraicSpace_of_diag_of_flat_chart` and
`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_diag_of_flat_scheme_chart`,
are themselves conditional on
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`, which is condition (3)
of the tag.  Deliberately untagged, for the same reason that condition (3) is. -/
abbrev Theorem04S6Quotient (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    [HasSheafify (BigFppfOver.topology C S hS) (Type u)] : Prop :=
  ∀ (B : AlgebraicSpaces C S hS) (H : GroupoidInAlgebraicSpaces C S hS B),
    CategoryTheory.IsEquivalenceRelation (groupoidPreRelation H).target
        (groupoidPreRelation H).source →
      IsFlat C S hS H.source.hom → IsFlat C S hS H.target.hom →
        IsLocallyOfFinitePresentation C S hS H.source.hom →
          IsLocallyOfFinitePresentation C S hS H.target.hom →
            H.QuotientIsAlgebraicSpace

/-! ### Stacks 0DU1 -/

section Quotient

variable {G : GroupoidInAlgebraicSpaces C S hS Y}

/-- **Stacks 0DU1, algebraicity of the quotient.** Let `(U, R, s, t, c)` be a groupoid in
algebraic spaces over an algebraic space `Y` whose object space is flat and locally of finite
presentation over `Y` and whose pre-relation `(t, s) : R ⟶ U ×_Y U` is an open immersion.  Then
the quotient sheaf `U/R` of Stacks 044J is an algebraic space over `S`.

The pre-relation is an equivalence relation and `s` and `t` are flat and locally of finite
presentation, so Stacks 04S6, condition (1), applies. -/
@[stacks 0DU1 "algebraicity of the quotient U/R"]
theorem isAlgebraicSpace_quotientSheaf_of_isOpenImmersion
    (hflat : IsFlat C S hS G.objectsToBase.hom)
    (hlfp : IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom)
    (hopen : IsOpenImmersion C S hS (groupoidPreRelation G).left) :
    IsAlgebraicSpace C S hS (quotientSheaf (groupoidPreRelation G)).obj :=
  Space.bootstrap04S6QuotientSheaf C S hS (groupoidPreRelation G) G.arrows.property
    G.objects.property (isEquivalenceRelation_groupoidPreRelation_of_isOpenImmersion hopen)
    (by
      rw [Stack.groupoidPreRelation_target_left]
      exact isFlat_target_of_isOpenImmersion hopen hflat)
    (by
      rw [Stack.groupoidPreRelation_target_left]
      exact isLocallyOfFinitePresentation_target_of_isOpenImmersion hopen hlfp)
    (by
      rw [Stack.groupoidPreRelation_source_left]
      exact isFlat_source_of_isOpenImmersion hopen hflat)
    (by
      rw [Stack.groupoidPreRelation_source_left]
      exact isLocallyOfFinitePresentation_source_of_isOpenImmersion hopen hlfp)

/-- **Stacks 0DU1, étaleness of the quotient over the base, granted algebraicity of the
quotient.** With the hypotheses of Stacks 0DU1 and the quotient sheaf `U/R` assumed to be an
algebraic space, the canonical morphism `U/R ⟶ Y` of Stacks 044J is étale. -/
theorem isEtale_quotientSheafToBase_of_isOpenImmersion_of_isAlgebraicSpace
    (hX : IsAlgebraicSpace C S hS (quotientSheaf (groupoidPreRelation G)).obj)
    (hflat : IsFlat C S hS G.objectsToBase.hom)
    (hlfp : IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom)
    (hopen : IsOpenImmersion C S hS (groupoidPreRelation G).left) :
    IsEtale C S hS (quotientSheafToBase Y.property.isSheaf (groupoidPreRelation G)).hom := by
  set j := groupoidPreRelation G with hj
  set q := toQuotientSheaf j with hq
  set f := (quotientSheafToBase Y.property.isSheaf j).hom with hf
  have hrel : CategoryTheory.IsEquivalenceRelation j.target j.source :=
    isEquivalenceRelation_groupoidPreRelation_of_isOpenImmersion hopen
  have htflat : IsFlat C S hS G.target.hom := isFlat_target_of_isOpenImmersion hopen hflat
  have htlfp : IsLocallyOfFinitePresentation C S hS G.target.hom :=
    isLocallyOfFinitePresentation_target_of_isOpenImmersion hopen hlfp
  -- The three properties of the covering map `U ⟶ U/R`, Stacks 06PG.
  have hqsurj : IsSurjective C S hS q := isSurjective_toQuotientSheaf j
  have hqflat : IsFlat C S hS q := isFlat_toQuotientSheaf G hrel hX htflat
  have hqlfp : IsLocallyOfFinitePresentation C S hS q :=
    isLocallyOfFinitePresentation_toQuotientSheaf G hrel hX htlfp
  have hqloc : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) q :=
    isLocallySurjective_toQuotientSheaf j
  have hqf : q ≫ f = G.objectsToBase.hom :=
    toQuotientSheaf_quotientSheafToBase Y.property.isSheaf j
  -- Flatness and local finite presentation of `U/R ⟶ Y`, Stacks 06NR and Stacks 0AHC.
  have hflatBase : IsFlat C S hS f :=
    isFlat_of_comp_of_locallySurjective C S hS G.objects.property hX Y.property q f
      (by rw [hqf]; exact hflat) hqloc
  have hlfpBase : IsLocallyOfFinitePresentation C S hS f := by
    refine isLocallyOfFinitePresentation_of_commonFppfDescentSituation
      { site := C, S := S, hS := hS
        X := G.objects.obj, Y := (quotientSheaf j).obj, B := Y.obj
        algebraicSpaceX := G.objects.property
        algebraicSpaceY := hX
        algebraicSpaceB := Y.property
        f := q, q := f, p := G.objectsToBase.hom
        p_eq := hqf.symm
        surjective_f := hqsurj
        flat_f := hqflat
        locallyOfFinitePresentation_f := hqlfp } ?_
    exact hlfp
  -- Unramifiedness, Stacks 05W1, from the relative diagonal being an open immersion.
  have hunr : IsUnramified C S hS f := by
    refine isUnramified_of_isOpenImmersion_diagonal C S hS f
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation C S hS hlfpBase) ?_
    -- The quotient and the two morphisms, packaged in the category of algebraic spaces.
    let Xsp : AlgebraicSpaces C S hS := ⟨(quotientSheaf j).obj, hX⟩
    let qs : G.objects ⟶ Xsp := ObjectProperty.homMk q
    let fs : Xsp ⟶ Y := ObjectProperty.homMk f
    let jas : G.arrows ⟶ groupoidRelativeSquareSpace G := ObjectProperty.homMk j.left
    have hqfs : qs ≫ fs = G.objectsToBase := ObjectProperty.hom_ext _ hqf
    have hp : IsPullback (groupoidRelativeSquareFst G) (groupoidRelativeSquareSnd G)
        (qs ≫ fs) (qs ≫ fs) := by
      rw [hqfs]
      exact isPullback_groupoidRelativeSquareSpace G
    have hr : IsPullback (ObjectProperty.homMk j.target.left : G.arrows ⟶ G.objects)
        (ObjectProperty.homMk j.source.left : G.arrows ⟶ G.objects) qs qs :=
      IsPullback.of_map (ObjectProperty.ι (IsAlgebraicSpace C S hS))
        (ObjectProperty.hom_ext _ (target_toQuotientSheaf_eq_source j))
        ((isPullback_toQuotientSheaf j hrel G.arrows.property.isSheaf
          G.objects.property.isSheaf).flip)
    -- `R = U ×_{U/R} U` and `U ×_Y U = (U/R) ×_Y (U/R)`-base-change agree, so the comparison
    -- of the two chosen fibre products carries the pre-relation to the base change of the
    -- relative diagonal.
    have hcomm : jas ≫ hp.isoPullback.hom =
        hr.isoPullback.hom ≫ pullback.map qs qs (qs ≫ fs) (qs ≫ fs)
          (𝟙 G.objects) (𝟙 G.objects) fs
          (Category.id_comp _).symm (Category.id_comp _).symm := by
      refine pullback.hom_ext ?_ ?_ <;>
        simp only [Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd,
          pullback.map, pullback.lift_fst, pullback.lift_snd, Category.comp_id] <;>
        exact ObjectProperty.hom_ext _ rfl
    have hri := openImmersionProperty_respectsIso C S hS
    have hkopen : IsOpenImmersion C S hS
        (pullback.map qs qs (qs ≫ fs) (qs ≫ fs) (𝟙 G.objects) (𝟙 G.objects) fs
          (Category.id_comp _).symm (Category.id_comp _).symm).hom := by
      have h₁ : openImmersionProperty C S hS (jas ≫ hp.isoPullback.hom) :=
        MorphismProperty.RespectsIso.postcomp (openImmersionProperty C S hS)
          hp.isoPullback.hom jas hopen
      rw [hcomm] at h₁
      exact ((openImmersionProperty C S hS).cancel_left_of_respectsIso
        hr.isoPullback.hom _).mp h₁
    -- The right-hand column of the diagonal square is surjective, flat and locally of finite
    -- presentation, being a base change of a composite of such morphisms.
    have hm : ∀ (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
        [P.IsStableUnderComposition], P qs →
        P (pullback.map (qs ≫ fs) (qs ≫ fs) fs fs qs qs (𝟙 Y) (by simp) (by simp)) :=
      fun P _ _ h => MorphismProperty.pullbackMap (f := qs ≫ fs) (g := qs ≫ fs) (f' := fs)
        (g' := fs) (i₁ := qs) (i₂ := qs) h h rfl rfl
    have hmsurj := hm (surjectiveMorphismProperty C S hS) hqsurj
    have hmflat := hm (flatProperty C S hS) hqflat
    have hmlfp := hm (locallyOfFinitePresentationProperty C S hS) hqlfp
    have hd : IsOpenImmersion C S hS (pullback.diagonal fs).hom :=
      isOpenImmersion_of_isPullback_of_fppfCover
        (pullback_map_diagonal_isPullback qs qs fs) hmsurj hmflat hmlfp hkopen
    -- Transport from the chosen fibre product of algebraic spaces to the presheaf one.
    have hsq : IsPullback (pullback.fst fs fs).hom (pullback.snd fs fs).hom fs.hom fs.hom :=
      AlgebraicSpaces.isPullback_hom C S hS (IsPullback.of_hasPullback fs fs)
    have hdiageq : (pullback.diagonal fs).hom ≫ hsq.isoPullback.hom =
        pullback.diagonal fs.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.diagonal_fst]
        exact congrArg (fun m : Xsp ⟶ Xsp => m.hom) (pullback.diagonal_fst fs)
      · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.diagonal_snd]
        exact congrArg (fun m : Xsp ⟶ Xsp => m.hom) (pullback.diagonal_snd fs)
    have hdp : IsOpenImmersion C S hS (pullback.diagonal fs.hom) := by
      rw [← hdiageq]
      exact MorphismProperty.RespectsIso.postcomp
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme C S hS))) hsq.isoPullback.hom _ hd
    exact hdp
  exact isEtale_of_isFlat_of_isUnramified C S hS hX Y.property f hlfpBase hflatBase hunr

/-- **Stacks 0DU1, étaleness of the quotient over the base.** Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over an algebraic space `Y` whose object space is flat and locally
of finite presentation over `Y` and whose pre-relation `(t, s) : R ⟶ U ×_Y U` is an open
immersion.  Then the canonical morphism `U/R ⟶ Y` of Stacks 044J is étale.

Algebraicity of the quotient,
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`, is what Stacks 06PG
needs in order to give the three properties of the covering map `U ⟶ U/R`. -/
@[stacks 0DU1 "étaleness of the structural morphism U/R → Y"]
theorem isEtale_quotientSheafToBase_of_isOpenImmersion
    (hflat : IsFlat C S hS G.objectsToBase.hom)
    (hlfp : IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom)
    (hopen : IsOpenImmersion C S hS (groupoidPreRelation G).left) :
    IsEtale C S hS (quotientSheafToBase Y.property.isSheaf (groupoidPreRelation G)).hom :=
  isEtale_quotientSheafToBase_of_isOpenImmersion_of_isAlgebraicSpace
    (isAlgebraicSpace_quotientSheaf_of_isOpenImmersion hflat hlfp hopen) hflat hlfp hopen

end Quotient

end Space

namespace Stack

/-! ### The canonical comparison from the quotient stack to the quotient sheaf -/

section Comparison

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Y : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Y)
  (hflat : Space.IsFlat C S hS G.objectsToBase.hom)
  (hlfp : Space.IsLocallyOfFinitePresentation C S hS G.objectsToBase.hom)
  (hopen : Space.IsOpenImmersion C S hS (Space.groupoidPreRelation G).left)

/-- The quotient sheaf `U/R`, as an object of the category of algebraic spaces over `S`: under
the hypotheses of Stacks 0DU1 it is one by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`. -/
noncomputable abbrev quotientSheafSpace : AlgebraicSpaces C S hS :=
  ⟨(Space.quotientSheaf (Space.groupoidPreRelation G)).obj,
    Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion hflat hlfp hopen⟩

/-- The quotient projection `U ⟶ U/R`, as a morphism of algebraic spaces over `S`. -/
noncomputable abbrev quotientSheafProjection :
    G.objects ⟶ quotientSheafSpace G hflat hlfp hopen :=
  ObjectProperty.homMk (Space.toQuotientSheaf (Space.groupoidPreRelation G))

/-- The structural morphism `U/R ⟶ Y`, as a morphism of algebraic spaces over `S`. -/
noncomputable abbrev quotientSheafToBaseSpace :
    quotientSheafSpace G hflat hlfp hopen ⟶ Y :=
  ObjectProperty.homMk
    (Space.quotientSheafToBase Y.property.isSheaf (Space.groupoidPreRelation G)).hom

/-- The quotient projection is invariant: it identifies the target and the source of the
groupoid, which is Stacks 044J for the pre-relation the groupoid cuts out. -/
theorem target_comp_quotientSheafProjection :
    G.target ≫ quotientSheafProjection G hflat hlfp hopen =
      G.source ≫ quotientSheafProjection G hflat hlfp hopen := by
  have h : G.target.hom ≫ Space.toQuotientSheaf (Space.groupoidPreRelation G) =
      G.source.hom ≫ Space.toQuotientSheaf (Space.groupoidPreRelation G) := by
    simpa only [groupoidPreRelation_target_left, groupoidPreRelation_source_left] using
      Space.target_toQuotientSheaf_eq_source (Space.groupoidPreRelation G)
  exact ObjectProperty.hom_ext _ h

/-- **Stacks 0DU1, the canonical comparison `[U/R] ⟶ U/R`.** Under the hypotheses of Stacks 0DU1
the quotient sheaf is an algebraic space
(`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion`), so the quotient
projection `U ⟶ U/R` is an invariant morphism to an algebraic space, and it descends to a
1-morphism from the quotient stack to the category fibred in sets of `U/R`.

This is the comparison asserted by the equality `X = [U/R] = U/R` of the source.  It is a real
construction — the descent of Stacks 044R applied to the quotient projection — and not a choice
out of an existence statement; `AlgebraicGeometry.Stack.quotientStackToQuotientSheaf_unique`
shows it is the only 1-morphism restricting along the projection to the quotient map. -/
@[stacks 0DU1 "the canonical comparison [U/R] → U/R"]
noncomputable def quotientStackToQuotientSheaf :
    quotientStack G ⥤ᵇ
      (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val :=
  quotientStackOfInvariant G (quotientSheafProjection G hflat hlfp hopen)
    (target_comp_quotientSheafProjection G hflat hlfp hopen)

/-- **Stacks 0DU1.** The canonical comparison composed with the projection `U ⟶ [U/R]` of
Stacks 044R is the 1-morphism that Stacks 0458 attaches to the quotient map `U ⟶ U/R`. -/
@[stacks 0DU1 "the comparison composed with the quotient projection is the map attached to \
U → U/R"]
theorem quotientStackProjection_comp_quotientStackToQuotientSheaf :
    BasedFunctor.comp (quotientStackProjection G)
        (quotientStackToQuotientSheaf G hflat hlfp hopen) =
      (associatedMap C S hS (Space.toQuotientSheaf (Space.groupoidPreRelation G))).1.hom :=
  quotientStackProjection_comp_quotientStackOfInvariant G
    (quotientSheafProjection G hflat hlfp hopen)
    (target_comp_quotientSheafProjection G hflat hlfp hopen)

/-- The restriction of the canonical comparison along the projection is the quotient map. -/
theorem restrictedMorphism_quotientStackToQuotientSheaf :
    restrictedMorphism G (quotientStackToQuotientSheaf G hflat hlfp hopen) =
      quotientSheafProjection G hflat hlfp hopen :=
  restrictedMorphism_quotientStackOfInvariant G (quotientSheafProjection G hflat hlfp hopen)
    (target_comp_quotientSheafProjection G hflat hlfp hopen)

/-- The restriction of the structure arrow `[U/R] ⟶ Y` of Stacks 044R along the projection is
the structure morphism of the object space. -/
theorem restrictedMorphism_quotientStackToBase :
    restrictedMorphism G (quotientStackToBase G) = G.objectsToBase :=
  restrictedMorphism_quotientStackOfInvariant G G.objectsToBase
    (G.target_over.trans G.source_over.symm)

/-- **Stacks 0DU1.** The canonical comparison is a morphism over the base: composed with the
1-morphism attached to the structural morphism `U/R ⟶ Y` it is the structure arrow
`[U/R] ⟶ Y` of Stacks 044R.

Both sides restrict along the projection to the structure morphism `U ⟶ Y` of the object space,
and by Stacks 0DUH a 1-morphism from the quotient stack to an algebraic space is determined by
that restriction. -/
@[stacks 0DU1 "the comparison is compatible with the structural morphisms to the base"]
theorem quotientStackToQuotientSheaf_comp_toBase :
    BasedFunctor.comp (quotientStackToQuotientSheaf G hflat hlfp hopen)
        (associatedMap C S hS (quotientSheafToBaseSpace G hflat hlfp hopen).hom).1.hom =
      quotientStackToBase G := by
  refine (quotientStackHomEquivInvariant G Y).injective (Subtype.ext ?_)
  show restrictedMorphism G _ = restrictedMorphism G _
  rw [restrictedMorphism_comp_associatedMap, restrictedMorphism_quotientStackToQuotientSheaf,
    restrictedMorphism_quotientStackToBase]
  exact ObjectProperty.hom_ext _
    (Space.toQuotientSheaf_quotientSheafToBase Y.property.isSheaf (Space.groupoidPreRelation G))

/-- The canonical comparison is the only 1-morphism `[U/R] ⟶ U/R` whose restriction along the
projection is the quotient map, by Stacks 0DUH. -/
theorem quotientStackToQuotientSheaf_unique
    (f : quotientStack G ⥤ᵇ
      (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val)
    (hf : BasedFunctor.comp (quotientStackProjection G) f =
      (associatedMap C S hS (Space.toQuotientSheaf (Space.groupoidPreRelation G))).1.hom) :
    f = quotientStackToQuotientSheaf G hflat hlfp hopen := by
  refine (quotientStackHomEquivInvariant G (quotientSheafSpace G hflat hlfp hopen)).injective
    (Subtype.ext ?_)
  show restrictedMorphism G f = restrictedMorphism G _
  rw [restrictedMorphism_quotientStackToQuotientSheaf]
  refine ObjectProperty.hom_ext _ ?_
  have h := congrArg
    (fun θ : (fibredCategory C S hS G.objects.obj).val ⥤ᵇ
        (fibredCategory C S hS (quotientSheafSpace G hflat hlfp hopen).obj).val =>
      PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w) hf
  rwa [natTransOfBasedFunctor_associatedMap] at h

end Comparison

end Stack

end AlgebraicGeometry

end
