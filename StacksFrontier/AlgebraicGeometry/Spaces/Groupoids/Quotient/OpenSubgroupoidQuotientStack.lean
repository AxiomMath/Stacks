module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative

/-!
# The quotient stack of an open subgroupoid (Stacks 0DU2)

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a scheme
`S` of a big fppf site, with `s` and `t` flat and locally of finite presentation, and let
`(U, P, s|_P, t|_P, c|_P)` be a second groupoid on the same object space whose arrow space is an
open subspace `P ⊆ R`.  **Stacks 0DU2** says that the induced 1-morphism `[U/P] ⟶ [U/R]` of
Stacks 046Q is a morphism of algebraic stacks which is representable by algebraic spaces,
surjective and étale.

An open subgroupoid is encoded as a morphism `φ : G ⟶ H` of groupoids in algebraic spaces over
`A` whose map on objects is an isomorphism — the two groupoids have the same object space up to
isomorphism — and whose map on arrow spaces is an open immersion.  This file proves ingredients
of Stacks 0DU2: flatness and local finite presentation of the source and target of the open
subgroupoid, faithfulness and surjectivity on objects of `[φ]`, and the geometric input of
étaleness, namely the whole of **Stacks 0DU1** at the auxiliary groupoid of Section 78.21 of `φ`.
Stacks 0DU2 itself is
`AlgebraicGeometry.Stack.isAlgebraicStack_representable_surjective_etale_quotientStackMap`, in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStackFull`.

The auxiliary groupoid of Section 78.21 attached to `φ : G ⟶ G'` has object space
`U'' = U ×_{f, U', t'} R'` and arrow space `R'' = R ×_{f ∘ s, U', t'} R'`, and it is a groupoid
over the object space `U'` of the target.  Its pre-relation over `U'` is
`(t'', s'') : R'' ⟶ U'' ×_{U'} U''`, which, read through the isomorphism `U'' ≅ R'` available when
the map on objects is an isomorphism, is the morphism `(r, r') ↦ (c'(f(r), r'), r')` into the
space `R' ×_{s', U', s'} R'` of arrows of `G'` with a common source.  That morphism is an open
immersion as soon as the map on arrow spaces is, which is the clause of the source proof that
makes Stacks 0DU1 applicable, and is proved here in the generality of an arbitrary morphism
`ι : Q ⟶ R` to the arrow space of a groupoid.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toComposablePairs`: the morphism
  `Q ×_{ι ∘ s, U, t} R ⟶ R ×_{s, U, t} R`, `(q, r) ↦ (ι q, r)`, attached to a morphism
  `ι : Q ⟶ R` to the arrow space of a groupoid in algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonSourcePairsIso`: the shear isomorphism
  `(c, pr₁) : R ×_{s, U, t} R ≅ R ×_{s, U, s} R`, the counterpart on the source side of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.subPreRelation`: the pre-relation
  `(t', s') : Q ×_{ι ∘ s, U, t} R ⟶ R ×_{s, U, s} R`, `(q, r) ↦ (c(ι q, r), r)`, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxPreRelation`, that pre-relation at
  `ι = f : R ⟶ R'` the arrow map of a morphism of groupoids.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxGroupoidOverTargetObjects`: the auxiliary
  groupoid of Section 78.21, read as a groupoid in algebraic spaces over the object space `U'` of
  the target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxRelativeSquareIso`: the identification of its
  relative square `U'' ×_{U'} U''` with `R' ×_{s', U', s'} R'`.
* `AlgebraicGeometry.Stack.Theorem04Y5`: **Stacks 04Y5, the implication (2) ⟹ (3), as a
  hypothesis** — a 1-morphism of categories fibred in groupoids with faithful underlying functor
  is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.quotientStackMapCFGHom`: the 1-morphism `[φ]` of Stacks 046Q, read in
  the 2-category of categories fibred in groupoids over the big fppf site.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_toComposablePairs`:
  `Q ×_{ι ∘ s, U, t} R` is the base change of `Q` along the first projection of
  `R ×_{s, U, t} R`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isOpenImmersion_subPreRelation` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isOpenImmersion_auxPreRelation`: the pre-relation
  `(q, r) ↦ (c(ι q, r), r)` is an open immersion as soon as `ι` is.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_auxToTargetObjects` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_auxToTargetObjects`:
  the structure morphism `U'' ⟶ U'` of the auxiliary groupoid over the target object space is
  flat and locally of finite presentation when the source map of the target is.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isOpenImmersion_auxGroupoidPreRelation`:
  the pre-relation `(t'', s'') : R'' ⟶ U'' ×_{U'} U''` of the auxiliary groupoid over the target
  object space is an open immersion, which is the hypothesis Stacks 0DU1 consumes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isAlgebraicSpace_auxQuotientSheaf` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isEtale_auxQuotientSheafToBase`:
  **Stacks 0DU1** at the auxiliary groupoid — `U''/R''` is an algebraic space and
  `U''/R'' ⟶ U'` is étale.
* `AlgebraicGeometry.Stack.isFlat_source_of_mapArrows_isOpenImmersion`,
  `AlgebraicGeometry.Stack.isFlat_target_of_mapArrows_isOpenImmersion`,
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_source_of_mapArrows_isOpenImmersion` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_target_of_mapArrows_isOpenImmersion`:
  the source and target of an open subgroupoid inherit flatness and local finite presentation
  from the ambient groupoid.
* `AlgebraicGeometry.Stack.toQuotientStackFullyFaithful`: the stackification map out of the
  presentation of a quotient stack is fully faithful.
* `AlgebraicGeometry.Stack.faithful_quotientStackMap_of_mono`: the 1-morphism `[φ]` has faithful
  underlying functor as soon as the map on arrow spaces is a monomorphism.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_quotientStackMap`: the 1-morphism `[φ]` is
  surjective on objects in the sense of Stacks 06D4 as soon as the map on objects is an
  isomorphism.

## The argument

*Flatness and local finite presentation of `s|_P` and `t|_P`.*  The naturality of `φ` gives
`s|_P = ι ≫ s ≫ f⁻¹` with `ι : P ⟶ R` the open immersion and `f : U ⟶ U` the isomorphism on
objects.  An open immersion is étale (Stacks 03FP) hence flat (Stacks 0467) and locally of finite
presentation (Stacks 06CN), an isomorphism is an open immersion, and both properties are stable
under composition (Stacks 03MN, Stacks 03XQ).

*Algebraicity.*  Both quotient stacks are then algebraic by **Stacks 06FI**
(`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`).

*Representability.*  By **Stacks 04Y5** it is enough that `[φ]` be faithful, and that is proved
here from `ι` being a monomorphism.  The quotient stack is the stackification of the pointwise
groupoid fibration, so faithfulness is tested on the presentation: the evaluated functor of `φ`
at a test object is faithful because an arrow of the evaluated groupoid is determined by its
underlying point of the arrow space, the Grothendieck construction of a componentwise faithful
strong transformation is faithful, and faithfulness descends from the presentation to the
stackification because the morphism presheaves of a stack are sheaves and the presentation is
fully faithful and locally essentially surjective (Stacks 044X).

*Surjectivity.*  By **Stacks 06D7** it is enough that `[φ]` be surjective on objects.  The
pointwise map is surjective on objects outright, because the map on objects is an isomorphism;
the canonical map from the pointwise groupoid fibration to the quotient stack is surjective on
objects by Stacks 044X; and `[φ]` is recovered from the composite of the two by the
2-isomorphism of Stacks 046Q together with the cancellation and transport lemmas for
surjectivity on objects proved below.

## Implementation notes

**Stacks 04Y5, the implication (2) ⟹ (3).**  Representability is obtained in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStackFull` from
the faithfulness proved here, by the form of that implication for 1-morphisms of algebraic
quotient stacks,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful`.

**Étaleness of `[φ]` is not proved; its geometric input is.**  The source proof reduces étaleness,
by Stacks 04XD, to the base change of `[φ]` along the canonical projection of `[U/R]`, identifies
that base change by **Stacks 04Y4** with the quotient stack of the auxiliary groupoid of
Section 78.21, and concludes by **Stacks 0DU1**.  The Stacks 0DU1 step is carried out here in
full: the auxiliary groupoid is rebased over `U'`, its structure morphism is shown flat and
locally of finite presentation, its pre-relation over `U'` is shown to be an open immersion, and
Stacks 0DU1 is applied, giving that `U''/R''` is an algebraic space and that `U''/R'' ⟶ U'` is
étale.

Stacks 04Y4, the identification of that base change with the quotient stack of the auxiliary
groupoid, is `AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare`.  The other input is
still missing, and it is not Stacks 0DU2's own content:
Stacks 04XD cannot be instantiated at
étaleness, because `AlgebraicGeometry.Space.etaleMorphisms` is not known to be local at the
target for the fppf precoverage, which is the reason
`AlgebraicGeometry.Stack.IsRelativelyEtale` is written longhand in the first place.  A second,
smaller gap sits beside it: turning the étaleness of `U''/R'' ⟶ U'` into relative
étaleness of the leg `[U''/R''] ⟶ S_{U'}` needs that leg to be representable by algebraic
spaces and its representing morphism to be identified with `U''/R'' ⟶ U'`, and nothing in the
library produces either from the equivalence `[U''/R''] ≃ U''/R''` of Stacks 0DU1.  No étaleness
assertion is therefore stated, because stating one would have to assume the step it is supposed
to prove.

The surjectivity assertion of Stacks 0DU2 is stated through
`AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.surjectiveMorphismProperty`, which is Stacks 03YK at surjectivity and is
the sense the source fixes for the word.  The quotient stack has its morphisms one universe above
the site, so the 1-morphism is read in `CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1,
u + 1}`; the universes of Stacks 03YK and of Stacks 06D7 are pinned accordingly.

## References

* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 06CN](https://stacks.math.columbia.edu/tag/06CN)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 02YV](https://stacks.math.columbia.edu/tag/02YV)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The pre-relation cut out by a subspace of the arrow space -/

section SubPreRelation

variable (H : GroupoidInAlgebraicSpaces C S hS B) {Q W : AlgebraicSpaces C S hS}
  {ι : Q ⟶ H.arrows} {a : W ⟶ Q} {b : W ⟶ H.arrows}

/-- The morphism `Q ×_{ι ≫ s, U, t} R ⟶ R ×_{s, U, t} R` induced by a morphism `ι : Q ⟶ R` to
the arrow space of a groupoid in algebraic spaces: on points it sends `(q, r)` to `(ι q, r)`. -/
noncomputable def toComposablePairs (hW : IsPullback a b (ι ≫ H.source) H.target) :
    W ⟶ AlgebraicSpaces.fiberProduct C S hS H.source H.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.target).lift (a ≫ ι) b
    (by rw [Category.assoc, hW.w])

@[simp]
theorem toComposablePairs_comp_fst (hW : IsPullback a b (ι ≫ H.source) H.target) :
    toComposablePairs H hW ≫
        (ObjectProperty.homMk (pullback.fst H.source.hom H.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS H.source H.target ⟶ H.arrows) = a ≫ ι :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.target).lift_fst _ _ _

@[simp]
theorem toComposablePairs_comp_snd (hW : IsPullback a b (ι ≫ H.source) H.target) :
    toComposablePairs H hW ≫
        (ObjectProperty.homMk (pullback.snd H.source.hom H.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS H.source H.target ⟶ H.arrows) = b :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.target).lift_snd _ _ _

/-- **`Q ×_{ι ≫ s, U, t} R` is the base change of `Q` along the first projection of
`R ×_{s, U, t} R`.**  The square formed by the two first projections, `ι` and the induced
morphism is cartesian: the fibre square of `ι ≫ s` with `t` cancels the fibre square of `s`
with `t` out of itself, because the induced morphism is the lift through the latter. -/
theorem isPullback_toComposablePairs (hW : IsPullback a b (ι ≫ H.source) H.target) :
    IsPullback a (toComposablePairs H hW) ι
      (ObjectProperty.homMk (pullback.fst H.source.hom H.target.hom)) := by
  refine IsPullback.of_bot ?_ (toComposablePairs_comp_fst H hW).symm
    (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.target)
  rw [toComposablePairs_comp_snd H hW]
  exact hW

end SubPreRelation

section Shear

variable (H : GroupoidInAlgebraicSpaces C S hS B)

/-- **The shear isomorphism `(c, pr₁) : R ×_{s, U, t} R ≅ R ×_{s, U, s} R`** of a groupoid in
algebraic spaces, which on points sends a composable pair `(r₀, r₁)` to the pair
`(c(r₀, r₁), r₁)` of arrows with a common source.

Both sides are fibre products of the one cospan `s, s : R ⟶ U`: the right-hand side by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` and the left-hand side by
**Stacks 043Z**, `AlgebraicGeometry.Space.isPullback_comp_source`, whose two projections are the
composition and the second arrow.  So the shear is the canonical comparison of two fibre
products of one cospan, and this is the counterpart on the source side of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso`. -/
noncomputable def commonSourcePairsIso :
    AlgebraicSpaces.fiberProduct C S hS H.source H.target ≅
      AlgebraicSpaces.fiberProduct C S hS H.source H.source :=
  (Space.isPullback_comp_source H).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.source)

@[simp]
theorem commonSourcePairsIso_hom_comp_fst :
    (commonSourcePairsIso H).hom ≫
        (ObjectProperty.homMk (pullback.fst H.source.hom H.source.hom) :
          AlgebraicSpaces.fiberProduct C S hS H.source H.source ⟶ H.arrows) = H.comp :=
  (Space.isPullback_comp_source H).isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.source)

@[simp]
theorem commonSourcePairsIso_hom_comp_snd :
    (commonSourcePairsIso H).hom ≫
        (ObjectProperty.homMk (pullback.snd H.source.hom H.source.hom) :
          AlgebraicSpaces.fiberProduct C S hS H.source H.source ⟶ H.arrows) =
      ObjectProperty.homMk (pullback.snd H.source.hom H.target.hom) :=
  (Space.isPullback_comp_source H).isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS H.source H.source)

end Shear

section SubPreRelationOpen

variable (H : GroupoidInAlgebraicSpaces C S hS B) {Q W : AlgebraicSpaces C S hS}
  {ι : Q ⟶ H.arrows} {a : W ⟶ Q} {b : W ⟶ H.arrows}

/-- **The pre-relation `(t', s') : Q ×_{ι ≫ s, U, t} R ⟶ R ×_{s, U, s} R`** attached to a
morphism `ι : Q ⟶ R` to the arrow space of a groupoid in algebraic spaces: on points it sends
`(q, r)` to the pair `(c(ι q, r), r)`, which has a common source because the source of a
composite is the source of the arrow applied first.

It is the morphism `(q, r) ↦ (ι q, r)` into the composable pairs followed by the shear
isomorphism. -/
noncomputable def subPreRelation (hW : IsPullback a b (ι ≫ H.source) H.target) :
    W ⟶ AlgebraicSpaces.fiberProduct C S hS H.source H.source :=
  toComposablePairs H hW ≫ (commonSourcePairsIso H).hom

@[simp]
theorem subPreRelation_comp_fst (hW : IsPullback a b (ι ≫ H.source) H.target) :
    subPreRelation H hW ≫ (ObjectProperty.homMk (pullback.fst H.source.hom H.source.hom) :
        AlgebraicSpaces.fiberProduct C S hS H.source H.source ⟶ H.arrows) =
      toComposablePairs H hW ≫ H.comp := by
  rw [subPreRelation, Category.assoc, commonSourcePairsIso_hom_comp_fst]

@[simp]
theorem subPreRelation_comp_snd (hW : IsPullback a b (ι ≫ H.source) H.target) :
    subPreRelation H hW ≫ (ObjectProperty.homMk (pullback.snd H.source.hom H.source.hom) :
        AlgebraicSpaces.fiberProduct C S hS H.source H.source ⟶ H.arrows) = b := by
  rw [subPreRelation, Category.assoc, commonSourcePairsIso_hom_comp_snd,
    toComposablePairs_comp_snd]

/-- **The pre-relation of an open subspace of the arrow space is an open immersion.**  Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces and let `ι : Q ⟶ R` be an open immersion.
Then `(t', s') : Q ×_{ι ≫ s, U, t} R ⟶ R ×_{s, U, s} R`, the morphism sending `(q, r)` to
`(c(ι q, r), r)`, is an open immersion.

This is the clause of the proof of **Stacks 0DU2** which says that the pre-relation of the
auxiliary groupoid of Section 78.21 of an open subgroupoid is an open immersion.  The morphism
`(q, r) ↦ (ι q, r)` is a base change of `ι` along the first projection of `R ×_{s, U, t} R`, so
it is an open immersion by **Stacks 02YW**; the shear `(r₀, r₁) ↦ (c(r₀, r₁), r₁)` is an
isomorphism; and a composite of an open immersion with an isomorphism is an open immersion by
**Stacks 02YV**. -/
theorem isOpenImmersion_subPreRelation (hW : IsPullback a b (ι ≫ H.source) H.target)
    (hopen : Space.IsOpenImmersion C S hS ι.hom) :
    Space.IsOpenImmersion C S hS (subPreRelation H hW).hom := by
  have hm : Space.IsOpenImmersion C S hS (toComposablePairs H hW).hom :=
    Space.isOpenImmersion_of_isPullback C S hS (isPullback_toComposablePairs H hW) hopen
  have hs : Space.IsOpenImmersion C S hS (commonSourcePairsIso H).hom.hom :=
    Space.isOpenImmersion_of_isIso C S hS _
  change Space.IsOpenImmersion C S hS
    (toComposablePairs H hW ≫ (commonSourcePairsIso H).hom).hom
  exact Space.isOpenImmersion_comp C S hS _ _ hm hs

end SubPreRelationOpen

/-! ### The pre-relation of the auxiliary groupoid of a morphism of groupoids -/

section AuxPreRelation

variable {G G' : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G G')

/-- The space `R'' = R ×_{f ∘ s, U', t'} R'` of Section 78.21 is the fibre product of
`f(s(-)) = s'(f(-)) : R ⟶ U'` with `t' : R' ⟶ U'`, read with the arrow map of `φ` in front of
the source map of `G'`. -/
theorem isPullback_auxArrows_comp_source :
    IsPullback (auxArrowsFst φ) (auxArrowsSnd φ) (φ.arrowsMap ≫ G'.source) G'.target := by
  rw [Hom.arrowsMap_comp_source]
  exact isPullback_auxArrows φ

/-- **The pre-relation `(t', s') : R'' ⟶ R' ×_{s', U', s'} R'` of the auxiliary groupoid of
Section 78.21**, read through the projection `U'' ⟶ R'`: on points it sends `(r, r')` to the
pair `(c'(f(r), r'), r')` of arrows of `G'` with a common source. -/
noncomputable def auxPreRelation :
    auxArrows φ ⟶ AlgebraicSpaces.fiberProduct C S hS G'.source G'.source :=
  subPreRelation G' (isPullback_auxArrows_comp_source φ)

theorem toComposablePairs_isPullback_auxArrows_comp_source :
    toComposablePairs G' (isPullback_auxArrows_comp_source φ) = auxComposable φ := rfl

@[simp]
theorem auxPreRelation_comp_fst :
    auxPreRelation φ ≫ (ObjectProperty.homMk (pullback.fst G'.source.hom G'.source.hom) :
      AlgebraicSpaces.fiberProduct C S hS G'.source G'.source ⟶ G'.arrows) = auxTargetSnd φ :=
  subPreRelation_comp_fst G' (isPullback_auxArrows_comp_source φ)

@[simp]
theorem auxPreRelation_comp_snd :
    auxPreRelation φ ≫ (ObjectProperty.homMk (pullback.snd G'.source.hom G'.source.hom) :
      AlgebraicSpaces.fiberProduct C S hS G'.source G'.source ⟶ G'.arrows) = auxArrowsSnd φ :=
  subPreRelation_comp_snd G' (isPullback_auxArrows_comp_source φ)

/-- **The pre-relation of the auxiliary groupoid of an open subgroupoid is an open
immersion.**  If the map on arrow spaces of `φ : G ⟶ G'` is an open immersion then
`(t', s') : R'' ⟶ R' ×_{s', U', s'} R'` is an open immersion. -/
theorem isOpenImmersion_auxPreRelation
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows) :
    Space.IsOpenImmersion C S hS (auxPreRelation φ).hom :=
  isOpenImmersion_subPreRelation G' (isPullback_auxArrows_comp_source φ) hopen

end AuxPreRelation

/-! ### The auxiliary groupoid as a groupoid over the target object space -/

section OverTargetObjects

variable {G G' : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G G')

/-- **The auxiliary groupoid `(U'', R'', s'', t'', c'')` of Section 78.21, read as a groupoid in
algebraic spaces over the object space `U'` of the target.**  The underlying five maps are those
of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxGroupoid`; what changes is the base, which is
`U'` with structure morphism the morphism `U'' ⟶ U'` of Section 78.21.

The target map lies over the base because that morphism is invariant, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxToTargetObjects_invariant`; the composition lies
over the base because its second projection is the second projection of the arrow applied first,
and the two arrows of a composable pair already have the same image in `U'`. -/
noncomputable def auxGroupoidOverTargetObjects :
    GroupoidInAlgebraicSpaces C S hS G'.objects where
  objects := auxObjects φ
  arrows := auxArrows φ
  objectsToBase := auxToTargetObjects φ
  arrowsToBase := auxSource φ ≫ auxToTargetObjects φ
  source := auxSource φ
  target := auxTarget φ
  source_over := rfl
  target_over := auxToTargetObjects_invariant φ
  comp := auxComp φ
  comp_over := by
    have hsrc : auxSource φ ≫ auxToTargetObjects φ = auxArrowsSnd φ ≫ G'.source := by
      rw [auxToTargetObjects, ← Category.assoc, auxSource_comp_auxObjectsSnd]
    have hinv : auxTarget φ ≫ auxToTargetObjects φ = auxSource φ ≫ auxToTargetObjects φ :=
      auxToTargetObjects_invariant φ
    have hfirst : auxFirstArrow φ ≫ auxSource φ ≫ auxToTargetObjects φ =
        auxSecondArrow φ ≫ auxSource φ ≫ auxToTargetObjects φ := by
      rw [← Category.assoc, ← Category.assoc,
        (AlgebraicSpaces.isPullback_fiberProduct C S hS (auxSource φ) (auxTarget φ)).w,
        Category.assoc, hinv, Category.assoc]
    rw [hsrc, ← Category.assoc, auxComp_comp_auxArrowsSnd, Category.assoc, ← hsrc, hfirst]
  pointwiseGroupoid T := ⟨auxPointwiseGroupoid φ T⟩

/-- The map on objects of a morphism of groupoids in algebraic spaces is an isomorphism of
algebraic spaces as soon as it is an isomorphism of the underlying presheaves, the category of
algebraic spaces being a full subcategory of presheaves. -/
theorem isIso_objectsMap (hobj : IsIso φ.toGroupoidHom.mapObjects) : IsIso φ.objectsMap := by
  obtain ⟨g, h1, h2⟩ := hobj.out
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ h1, ObjectProperty.hom_ext _ h2⟩

/-- **The projection `U'' ⟶ R'` is an isomorphism when the map on objects is.**  It is the base
change of that map along the target map of `G'`, and isomorphisms are stable under base
change. -/
theorem isIso_auxObjectsSnd (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    IsIso (auxObjectsSnd φ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms (AlgebraicSpaces C S hS))
    (isPullback_auxObjects φ) (isIso_objectsMap φ hobj)

/-- The projection `U'' ⟶ R'` is an isomorphism of presheaves when the map on objects is. -/
theorem isIso_auxObjectsSnd_hom (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    IsIso (auxObjectsSnd φ).hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
    (AlgebraicSpaces.isPullback_hom C S hS (isPullback_auxObjects φ)) hobj

/-- **Flatness of the structure morphism `U'' ⟶ U'` of the auxiliary groupoid over the target
object space.**  It is the projection `U'' ⟶ R'` followed by the source map of `G'`; the
projection is an isomorphism when the map on objects is, an isomorphism is an open immersion
hence étale (Stacks 03FP) hence flat (Stacks 0467), and flatness is stable under composition
(Stacks 03MN). -/
theorem isFlat_auxToTargetObjects (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hs : Space.IsFlat C S hS G'.source.hom) :
    Space.IsFlat C S hS (auxToTargetObjects φ).hom := by
  have _hiso := isIso_auxObjectsSnd_hom φ hobj
  have hflat : Space.IsFlat C S hS (auxObjectsSnd φ).hom :=
    Space.isFlat_of_isEtale C S hS
      (Space.isEtale_of_isOpenImmersion C S hS
        (Space.isOpenImmersion_of_isIso C S hS (auxObjectsSnd φ).hom))
  exact Space.isFlat_comp C S hS (auxObjects φ).property G'.arrows.property
    G'.objects.property _ _ hflat hs

/-- **Local finite presentation of the structure morphism `U'' ⟶ U'` of the auxiliary groupoid
over the target object space.**  An isomorphism is an open immersion, hence locally of finite
presentation (Stacks 06CN), and that property is stable under composition (Stacks 03XQ). -/
theorem isLocallyOfFinitePresentation_auxToTargetObjects
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hs : Space.IsLocallyOfFinitePresentation C S hS G'.source.hom) :
    Space.IsLocallyOfFinitePresentation C S hS (auxToTargetObjects φ).hom := by
  have _hiso := isIso_auxObjectsSnd_hom φ hobj
  have hlfp : Space.IsLocallyOfFinitePresentation C S hS (auxObjectsSnd φ).hom :=
    Space.isLocallyOfFinitePresentation_of_isOpenImmersion C S hS
      (Space.isOpenImmersion_of_isIso C S hS (auxObjectsSnd φ).hom)
  exact Space.isLocallyOfFinitePresentation_comp C S hS (auxObjects φ).property
    G'.arrows.property G'.objects.property _ _ hlfp hs

end OverTargetObjects

/-! ### The relative square of the auxiliary groupoid over the target object space -/

section RelativeSquare

variable {G G' : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G G')

/-- **`U'' ×_{U'} U''` is `R' ×_{s', U', s'} R'` when the map on objects is an isomorphism.**
The relative square of the auxiliary groupoid over the target object space is a fibre product of
the structure morphism `U'' ⟶ U'` with itself, and that morphism is the isomorphism `U'' ≅ R'`
followed by the source map of `G'`. -/
theorem isPullback_groupoidRelativeSquare_auxGroupoidOverTargetObjects
    (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    IsPullback
      (Space.groupoidRelativeSquareFst (auxGroupoidOverTargetObjects φ) ≫ auxObjectsSnd φ)
      (Space.groupoidRelativeSquareSnd (auxGroupoidOverTargetObjects φ) ≫ auxObjectsSnd φ)
      G'.source G'.source := by
  let e : auxObjects φ ≅ G'.arrows :=
    @asIso _ _ _ _ (auxObjectsSnd φ) (isIso_auxObjectsSnd φ hobj)
  refine (Space.isPullback_groupoidRelativeSquareSpace
    (auxGroupoidOverTargetObjects φ)).of_iso (Iso.refl _) e e (Iso.refl _)
    (by simp [e]) (by simp [e]) ?_ ?_ <;>
    simp [e, auxGroupoidOverTargetObjects, auxToTargetObjects]

/-- The identification of the relative square `U'' ×_{U'} U''` of the auxiliary groupoid over
the target object space with the space `R' ×_{s', U', s'} R'` of arrows of `G'` with a common
source, as the canonical comparison of two fibre products of the cospan `s', s'`. -/
noncomputable def auxRelativeSquareIso (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    Space.groupoidRelativeSquareSpace (auxGroupoidOverTargetObjects φ) ≅
      AlgebraicSpaces.fiberProduct C S hS G'.source G'.source :=
  (isPullback_groupoidRelativeSquare_auxGroupoidOverTargetObjects φ hobj).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.source)

@[simp]
theorem auxRelativeSquareIso_hom_comp_fst (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    (auxRelativeSquareIso φ hobj).hom ≫
        (ObjectProperty.homMk (pullback.fst G'.source.hom G'.source.hom) :
          AlgebraicSpaces.fiberProduct C S hS G'.source G'.source ⟶ G'.arrows) =
      Space.groupoidRelativeSquareFst (auxGroupoidOverTargetObjects φ) ≫ auxObjectsSnd φ :=
  (isPullback_groupoidRelativeSquare_auxGroupoidOverTargetObjects φ
    hobj).isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.source)

@[simp]
theorem auxRelativeSquareIso_hom_comp_snd (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    (auxRelativeSquareIso φ hobj).hom ≫
        (ObjectProperty.homMk (pullback.snd G'.source.hom G'.source.hom) :
          AlgebraicSpaces.fiberProduct C S hS G'.source G'.source ⟶ G'.arrows) =
      Space.groupoidRelativeSquareSnd (auxGroupoidOverTargetObjects φ) ≫ auxObjectsSnd φ :=
  (isPullback_groupoidRelativeSquare_auxGroupoidOverTargetObjects φ
    hobj).isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.source)

/-- The pre-relation `(t'', s'') : R'' ⟶ U'' ×_{U'} U''` of the auxiliary groupoid over the
target object space, as a morphism of algebraic spaces over `S`. -/
noncomputable abbrev auxPreRelationSpace :
    auxArrows φ ⟶ Space.groupoidRelativeSquareSpace (auxGroupoidOverTargetObjects φ) :=
  ObjectProperty.homMk (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left

/-- **The pre-relation of the auxiliary groupoid over the target object space is the
pre-relation `(r, r') ↦ (c'(f(r), r'), r')` read through the identification of the relative
square with `R' ×_{s', U', s'} R'`.**  The two projections of the pre-relation are the target
and the source map of the auxiliary groupoid, and composing them with the projection
`U'' ⟶ R'` gives `c'(f(r), r')` and `r'`. -/
theorem auxPreRelationSpace_comp_auxRelativeSquareIso
    (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    auxPreRelationSpace φ ≫ (auxRelativeSquareIso φ hobj).hom = auxPreRelation φ := by
  have hfst : auxPreRelationSpace φ ≫
      Space.groupoidRelativeSquareFst (auxGroupoidOverTargetObjects φ) = auxTarget φ :=
    (ObjectProperty.hom_ext _
      (Space.target_hom_eq_groupoidPreRelation_comp
        (auxGroupoidOverTargetObjects φ))).symm
  have hsnd : auxPreRelationSpace φ ≫
      Space.groupoidRelativeSquareSnd (auxGroupoidOverTargetObjects φ) = auxSource φ :=
    (ObjectProperty.hom_ext _
      (Space.source_hom_eq_groupoidPreRelation_comp
        (auxGroupoidOverTargetObjects φ))).symm
  refine (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.source).hom_ext ?_ ?_
  · rw [Category.assoc, auxRelativeSquareIso_hom_comp_fst, auxPreRelation_comp_fst]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ auxObjectsSnd φ) hfst)).trans
      (auxTarget_comp_auxObjectsSnd φ)
  · rw [Category.assoc, auxRelativeSquareIso_hom_comp_snd, auxPreRelation_comp_snd]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ auxObjectsSnd φ) hsnd)).trans
      (auxSource_comp_auxObjectsSnd φ)

/-- **The pre-relation of the auxiliary groupoid of an open subgroupoid, over the target object
space, is an open immersion.**  Let `φ : G ⟶ G'` have open immersion on arrow spaces and
isomorphism on object spaces.  Then the pre-relation
`(t'', s'') : R'' ⟶ U'' ×_{U'} U''` of the auxiliary groupoid of Section 78.21, read over the
object space of the target, is an open immersion.

This is the hypothesis **Stacks 0DU1** consumes.  Under the identification of the relative
square with `R' ×_{s', U', s'} R'` the pre-relation becomes `(r, r') ↦ (c'(f(r), r'), r')`,
which is an open immersion by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isOpenImmersion_auxPreRelation`. -/
theorem isOpenImmersion_auxGroupoidPreRelation
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows) :
    Space.IsOpenImmersion C S hS
      (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left := by
  have heq : auxPreRelationSpace φ =
      auxPreRelation φ ≫ (auxRelativeSquareIso φ hobj).inv := by
    rw [← auxPreRelationSpace_comp_auxRelativeSquareIso φ hobj, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hopeniso : Space.IsOpenImmersion C S hS (auxRelativeSquareIso φ hobj).inv.hom :=
    Space.isOpenImmersion_of_isIso C S hS _
  change Space.IsOpenImmersion C S hS (auxPreRelationSpace φ).hom
  rw [congrArg (fun k => k.hom) heq]
  exact Space.isOpenImmersion_comp C S hS _ _ (isOpenImmersion_auxPreRelation φ hopen) hopeniso

end RelativeSquare

/-! ### Stacks 0DU1 at the auxiliary groupoid of an open subgroupoid -/

section QuotientSheaf

variable [HasSheafify (BigFppfOver.topology C S hS) (Type u)]
  {G G' : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom G G')

/-- **Stacks 0DU1 at the auxiliary groupoid of an open subgroupoid, algebraicity of the
quotient.**  Let `φ : G ⟶ G'` have open immersion on arrow spaces and isomorphism on object
spaces, and let the source map of `G'` be flat and locally of finite presentation.  Then the
quotient sheaf `U''/R''` of the auxiliary groupoid of Section 78.21 is an algebraic space.

The structure morphism `U'' ⟶ U'` is flat and locally of finite presentation and the
pre-relation over `U'` is an open immersion, so Stacks 0DU1 applies. -/
theorem isAlgebraicSpace_auxQuotientSheaf
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hsflat : Space.IsFlat C S hS G'.source.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G'.source.hom) :
    IsAlgebraicSpace C S hS
      (Space.quotientSheaf
        (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ))).obj :=
  Space.isAlgebraicSpace_quotientSheaf_of_isOpenImmersion
    (isFlat_auxToTargetObjects φ hobj hsflat)
    (isLocallyOfFinitePresentation_auxToTargetObjects φ hobj hslfp)
    (isOpenImmersion_auxGroupoidPreRelation φ hobj hopen)

/-- **Stacks 0DU1 at the auxiliary groupoid of an open subgroupoid, étaleness over the target
object space.**  Under the hypotheses above, the structural morphism `U''/R'' ⟶ U'` of the
quotient of the auxiliary groupoid of Section 78.21 is étale.

This is the étale input of the proof of Stacks 0DU2. -/
theorem isEtale_auxQuotientSheafToBase
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hsflat : Space.IsFlat C S hS G'.source.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G'.source.hom) :
    Space.IsEtale C S hS
      (Space.quotientSheafToBase G'.objects.property.isSheaf
        (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ))).hom :=
  Space.isEtale_quotientSheafToBase_of_isOpenImmersion
    (isFlat_auxToTargetObjects φ hobj hsflat)
    (isLocallyOfFinitePresentation_auxToTargetObjects φ hobj hslfp)
    (isOpenImmersion_auxGroupoidPreRelation φ hobj hopen)

end QuotientSheaf

end AlgebraicGeometry.GroupoidInAlgebraicSpaces


namespace AlgebraicGeometry.Stack

universe u w

section SurjectiveOnObjects

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

universe uX uY uZ vX vY vZ

/-- **Cancellation for surjectivity on objects.**  If a composite `F ⋙ G` of 1-morphisms over
the big fppf site of `S` is surjective on objects in the sense of Stacks 06D4, and `F` is a
1-morphism over the site, then `G` is surjective on objects: the lift of an object of the target
through `F ⋙ G` is in particular a lift through `G` of the image under `F` of its source. -/
theorem isSurjectiveOnObjects_of_comp
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {Z : Type uZ} [Category.{vZ} Z]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS) (F : X ⥤ Y) (G : Y ⥤ Z) (hF : F ⋙ pY = pX)
    (h : IsSurjectiveOnObjects B S hS pX pZ (F ⋙ G)) :
    IsSurjectiveOnObjects B S hS pY pZ G := by
  intro U hU z hz
  obtain ⟨V, hV, f, x, hx, α, hα⟩ := h U hU z hz
  exact ⟨V, hV, f, F.obj x, (Functor.congr_obj hF x).trans hx, α, hα⟩

/-- **Surjectivity on objects is invariant under a vertical 2-isomorphism.**  If `F` is
surjective on objects in the sense of Stacks 06D4 and `e : F ≅ F'` has every component lying over
an identity of the site, then `F'` is surjective on objects: precomposing a lift with the
component of `e⁻¹` keeps it lying over the same arrow of the site. -/
theorem isSurjectiveOnObjects_of_natIso
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (pX : X ⥤ BigFppfOver B S hS) (pY : Y ⥤ BigFppfOver B S hS) {F F' : X ⥤ Y}
    (e : F ≅ F') (he : ∀ x, pY.IsHomLift (𝟙 (pY.obj (F.obj x))) (e.hom.app x))
    (h : IsSurjectiveOnObjects B S hS pX pY F) :
    IsSurjectiveOnObjects B S hS pX pY F' := by
  intro U hU y hy
  obtain ⟨V, hV, f, x, hx, α, hα⟩ := h U hU y hy
  have : pY.IsHomLift (𝟙 (pY.obj (F.obj x))) (e.app x).hom := he x
  have : pY.IsHomLift (𝟙 (pY.obj (F.obj x))) (e.inv.app x) :=
    IsHomLift.lift_id_inv pY _ (e.app x)
  have := hα
  have hdom : pY.obj (F.obj x) = V := IsHomLift.domain_eq pY f α
  have : pY.IsHomLift (𝟙 V) (e.inv.app x) := by rw [← hdom]; infer_instance
  refine ⟨V, hV, f, x, hx, e.inv.app x ≫ α, ?_⟩
  simpa using IsHomLift.comp pY (𝟙 V) f (e.inv.app x) α

end SurjectiveOnObjects

section QuotientSurjective

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- **The canonical map from the pointwise groupoid fibration to the quotient stack is surjective
on objects**, in the sense of Stacks 06D4, with no hypothesis on the groupoid.

The canonical projection `S_U ⟶ [U/R]` of Stacks 044R factors through it, by the very definition
of that projection, and is surjective on objects because `[U/R]` is the stackification of the
pointwise groupoid fibration (part (1) of Stacks 044X). -/
theorem isSurjectiveOnObjects_pointwiseToQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS A) :
    IsSurjectiveOnObjects C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (quotientStack G).p (pointwiseToQuotientStack G) := by
  refine isSurjectiveOnObjects_of_comp _ _ _ (pointwiseObjectInclusion G) _ ?_
    (isSurjectiveOnObjects_quotientStackProjection G)
  rfl

/-- **The pointwise map attached to a morphism of groupoids whose map on objects is an
isomorphism is surjective on objects.**  An object of the pointwise groupoid fibration of the
target over a test object is a point of its object space, and it is the image of the point
obtained by applying the inverse isomorphism; no field extension and no nonidentity arrow of the
site are needed. -/
theorem isSurjectiveOnObjects_quotientPointwiseMap
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    IsSurjectiveOnObjects C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (presheafOfGroupoids (evaluationGroupoidFunctor H.toGroupoidInFunctors)).p
      (quotientPointwiseMap φ).toFunctor := by
  intro U hU y hy
  have hprop := (quotientPointwiseMapData φ).property.1 y.base
  obtain ⟨v, hv⟩ := ((isIso_iff_bijective
    (φ.toGroupoidHom.mapObjects.app (op y.base))).1 inferInstance).2 y.fiber
  have hob : (quotientPointwiseMap φ).toFunctor.obj ⟨y.base, v⟩ = y := by
    refine Pseudofunctor.CoGrothendieck.ext rfl (heq_of_eq ?_)
    change ((quotientPointwiseMapData φ).val.app ⟨op y.base⟩).toFunctor.obj v = y.fiber
    rw [hprop]
    exact hv
  exact ⟨U, hU, 𝟙 U, ⟨y.base, v⟩, hy, eqToHom hob,
    IsHomLift.eqToHom_domain_lift_id hob hy⟩

/-- **Stacks 0DU2, the surjectivity assertion in the sense of Stacks 06D4.**  The 1-morphism
`[φ] : [U/P] ⟶ [U/R]` of Stacks 046Q induced by a morphism of groupoids in algebraic spaces whose
map on objects is an isomorphism is surjective on objects.

The pointwise map of `φ` is surjective on objects, the canonical map from the pointwise groupoid
fibration of the target to its quotient stack is surjective on objects, so their composite is by
Stacks 06D6; the 2-isomorphism of Stacks 046Q identifies that composite with the canonical map of
the source followed by `[φ]`, and cancelling the canonical map of the source leaves `[φ]`. -/
theorem isSurjectiveOnObjects_quotientStackMap
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hobj : IsIso φ.toGroupoidHom.mapObjects) :
    IsSurjectiveOnObjects C S hS (quotientStack G).p (quotientStack H).p
      (quotientStackMap φ).toFunctor := by
  have hPK : IsSurjectiveOnObjects C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (quotientStack H).p
      ((quotientPointwiseMap φ).toFunctor ⋙ pointwiseToQuotientStack H) :=
    isSurjectiveOnObjects_comp C S hS _ _ _ _ _
      (isFibredOneMorphism_pointwiseToQuotientStack H).comp_eq
      (isSurjectiveOnObjects_quotientPointwiseMap φ hobj)
      (isSurjectiveOnObjects_pointwiseToQuotientStack H)
  have hIF : IsSurjectiveOnObjects C S hS
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
      (quotientStack H).p
      (pointwiseToQuotientStack G ⋙ (quotientStackMap φ).toFunctor) := by
    refine isSurjectiveOnObjects_of_natIso _ _
      ((BasedNatTrans.forgetful _ _).mapIso (quotientStackMap_commutes φ)) ?_ hPK
    intro x
    exact (quotientStackMap_commutes φ).hom.isHomLift' x
  exact isSurjectiveOnObjects_of_comp _ _ _ _ _
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq hIF

end QuotientSurjective

section Faithful

universe u1 v1 w1 u2 u3 u4 v2

open CategoryTheory.Functor CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Pseudofunctor.StrongTrans

/-- **A locally injective morphism of sheaves of types is injective on sections.**  Local
injectivity of a morphism of presheaves whose source and target are sheaves is injectivity of
each of its components. -/
private theorem injective_app_of_isLocallyInjective
    {D : Type u1} [Category.{v1} D] (J : GrothendieckTopology D)
    {P Q : Dᵒᵖ ⥤ Type w1} (φ : P ⟶ Q)
    (hP : Presheaf.IsSheaf J P) (hQ : Presheaf.IsSheaf J Q)
    [Presheaf.IsLocallyInjective J φ] (X : Dᵒᵖ) :
    Function.Injective (φ.app X) := by
  let ψ : (⟨P, hP⟩ : Sheaf J (Type w1)) ⟶ ⟨Q, hQ⟩ := ⟨φ⟩
  have : Sheaf.IsLocallyInjective ψ := inferInstanceAs (Presheaf.IsLocallyInjective J φ)
  exact (Sheaf.isLocallyInjective_iff_injective ψ).1 inferInstance X

/-- **Local injectivity of a morphism of presheaves on a slice site from injectivity over the
members of a covering sieve.**  If the component of `φ` at every object of `𝒞/U` lying over a
member of a covering sieve of `U` is injective, then `φ` is locally injective for the inherited
topology: the equalizer sieve of two sections identified by `φ` contains the pullback of that
covering sieve. -/
private theorem isLocallyInjective_of_cover_injective
    {D : Type u1} [Category.{v1} D] (J : GrothendieckTopology D)
    {U : D} {P Q : (Over U)ᵒᵖ ⥤ Type w1} (φ : P ⟶ Q)
    (R : Sieve U) (hR : R ∈ J U)
    (h : ∀ {V} (f : V ⟶ U), R f → Function.Injective (φ.app (op (Over.mk f)))) :
    Presheaf.IsLocallyInjective (J.over U) φ := by
  constructor
  intro X a b hab
  obtain ⟨X⟩ := X
  apply (J.over U).superset_covering _
    (J.overEquiv_symm_mem_over X (R.pullback X.hom) (J.pullback_stable X.hom hR))
  intro Y k hk
  have hk' : R (k.left ≫ X.hom) := (Sieve.overEquiv_symm_iff _ k).1 hk
  have hb := h Y.hom (by simpa using hk')
  apply hb
  change φ.app (op Y) (P.map k.op a) = φ.app (op Y) (P.map k.op b)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hab]

/-- **Injectivity of the map a functor induces on a hom-set transfers along isomorphisms of the
two endpoints.** -/
private theorem map_injective_of_iso
    {X : Type u1} {Y : Type u2} [Category.{v1} X] [Category.{v2} Y]
    (F : X ⥤ Y) {x y x' y' : X} (ex : x ≅ x') (ey : y ≅ y')
    (h : Function.Injective (F.map : (x' ⟶ y') → _)) :
    Function.Injective (F.map : (x ⟶ y) → _) := by
  intro m n hmn
  have he : ex.inv ≫ m ≫ ey.hom = ex.inv ≫ n ≫ ey.hom :=
    h (by simp only [Functor.map_comp, hmn])
  simpa using congrArg (fun a => ex.hom ≫ a ≫ ey.inv) he

/-- **A 1-morphism of stacks in groupoids which is injective on fibre hom-sets over a covering
is faithful.**

By Stacks 003Z (1) faithfulness is tested on the fibres.  On the fibre over `U` the hypothesis
makes the induced morphism of the sheaves `Mor(x, y)` of Stacks 02ZG locally injective, hence
injective on sections because both are sheaves; evaluating at the terminal object of `𝒞/U` and
transporting along the canonical isomorphisms of pullback fibres along the identity gives
injectivity of the fibre functor on the hom-set from `x` to `y`. -/
private theorem faithful_of_locally_injective
    {D : Type u1} [Category.{v1} D]
    {A₁ : Type u2} {A₂ : Type u3} [Category.{w1} A₁] [Category.{w1} A₂]
    {p : A₁ ⥤ D} {q : A₂ ⥤ D} [p.IsFibered] [q.IsFibered]
    {F : A₁ ⥤ A₂} (hF : p.IsFibredOneMorphism q F)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (J : GrothendieckTopology D) (hps : p.IsStack J) (hqs : q.IsStack J)
    (hlocal : ∀ U (x y : p.Fiber U), ∃ R ∈ J U, ∀ {V} (f : V ⟶ U), R f →
      Function.Injective ((fiberFunctorOfCompEq hF.comp_eq V).map :
        (pullbackFiber p x f ⟶ pullbackFiber p y f) → _)) :
    F.Faithful := by
  rw [IsFiberedInGroupoids.faithful_iff_forall_fiber p q hp hq F hF.comp_eq]
  intro U
  suffices hh : ∀ x y : p.Fiber U,
      Function.Injective ((fiberFunctorOfCompEq hF.comp_eq U).map : (x ⟶ y) → _) from
    ⟨fun {x y} {m n} hmn => hh x y hmn⟩
  intro x y
  obtain ⟨R, hR, hl⟩ := hlocal U x y
  have hli : Presheaf.IsLocallyInjective ((J.over U)) (hF.morPresheafMap x y) :=
    isLocallyInjective_of_cover_injective J _ R hR (fun {V} f hf => by
      let e := (hF.mapPullbackFiberIso x f).symm.homCongr (hF.mapPullbackFiberIso y f).symm
      exact e.injective.comp (hl f hf))
  have hb := injective_app_of_isLocallyInjective (J.over U) (hF.morPresheafMap x y)
    (hps.isMorSheaf U x y) (hqs.isMorSheaf U _ _) (op (Over.mk (𝟙 U)))
  let e := (hF.mapPullbackFiberIso x (𝟙 U)).symm.homCongr
    (hF.mapPullbackFiberIso y (𝟙 U)).symm
  have hh : Function.Injective ((fiberFunctorOfCompEq hF.comp_eq U).map :
      (pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U)) → _) :=
    (e.injective.of_comp_iff _).1 hb
  exact map_injective_of_iso _ (pullbackFiberIdIso x).symm (pullbackFiberIdIso y).symm hh

/-- **The Grothendieck construction of a componentwise faithful strong transformation of
pseudofunctors is faithful.**  Two arrows with the same image have the same component on the
base, and their fibre components become equal after cancelling the invertible naturality
constraint, so componentwise faithfulness identifies them. -/
private theorem cogrothendieckMapFaithful
    {D : Type u1} [Category.{v1} D]
    {P Q : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{w1, u2}} (α : P ⟶ Q)
    (hα : ∀ T, (α.app ⟨op T⟩).toFunctor.Faithful) :
    (Pseudofunctor.CoGrothendieck.map α).Faithful := by
  constructor
  intro X Y f g h
  obtain ⟨fb, ff⟩ := f
  obtain ⟨gb, gf⟩ := g
  have hb : fb = gb := congrArg (fun k => k.base) h
  subst hb
  have hfib : ((CoGrothendieck.map α).map ⟨fb, ff⟩).fiber =
      ((CoGrothendieck.map α).map ⟨fb, gf⟩).fiber ≫ eqToHom rfl :=
    Pseudofunctor.CoGrothendieck.Hom.congr h
  rw [eqToHom_refl, Category.comp_id] at hfib
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  change ff = gf ≫ eqToHom rfl
  rw [eqToHom_refl, Category.comp_id]
  have hiso : IsIso
      ((α.naturality fb.op.toLoc).hom.toNatTrans.app Y.fiber) := by
    refine ⟨(α.naturality fb.op.toLoc).inv.toNatTrans.app Y.fiber,
      ?_, ?_⟩ <;> simp [← Cat.Hom₂.comp_app]
  refine (hα X.base).map_injective ?_
  dsimp only [Pseudofunctor.CoGrothendieck.map] at hfib
  exact (cancel_mono _).mp hfib
/-- **Faithfulness descends from a presentation to a stackification.**  Let `I` be a fully
faithful 1-morphism into a stack `p` every object of whose fibres lies, over the members of a
covering sieve, in the essential image of `I`, and let `F` be a 1-morphism of stacks out of `p`.
If `I ⋙ F` is faithful then so is `F`: over the members of a covering sieve the fibre hom-sets of
`p` are those of the presentation, where `I ⋙ F` is injective and `I` bijective, so `F` is
injective on fibre hom-sets over a covering. -/
private theorem faithful_of_locally_essImage
    {D : Type u1} [Category.{v1} D]
    {A₀ : Type u2} {A₁ : Type u3} {A₂ : Type u4}
    [Category.{w1} A₀] [Category.{w1} A₁] [Category.{w1} A₂]
    {p₀ : A₀ ⥤ D} {p : A₁ ⥤ D} {q : A₂ ⥤ D} [p.IsFibered] [q.IsFibered]
    (I : A₀ ⥤ A₁) (hI : I ⋙ p = p₀) (hi : I.FullyFaithful)
    {F : A₁ ⥤ A₂} (hF : p.IsFibredOneMorphism q F) (hIF : (I ⋙ F).Faithful)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (J : GrothendieckTopology D) (hps : p.IsStack J) (hqs : q.IsStack J)
    (hlocal : ∀ U (x : p.Fiber U), ∃ R ∈ J U, ∀ {V} (f : V ⟶ U), R f →
      (fiberFunctorOfCompEq hI V).essImage (pullbackFiber p x f)) :
    F.Faithful := by
  apply faithful_of_locally_injective hF hp hq J hps hqs
  intro U x y
  obtain ⟨R₁, hR₁, hx⟩ := hlocal U x
  obtain ⟨R₂, hR₂, hy⟩ := hlocal U y
  refine ⟨R₁ ⊓ R₂, J.intersection_covering hR₁ hR₂, ?_⟩
  intro V f hf
  obtain ⟨a, ⟨ea⟩⟩ := hx f hf.1
  obtain ⟨b, ⟨eb⟩⟩ := hy f hf.2
  let If := fiberFunctorOfCompEq hI V
  let Ff := fiberFunctorOfCompEq hF.comp_eq V
  have : I.Full := hi.full
  have : I.Faithful := hi.faithful
  have : (I ⋙ F).Faithful := hIF
  have : If.Full := Fiber.full_mapOfComp hI V
  have : If.Faithful := Fiber.faithful_mapOfComp hI V
  have hw : (I ⋙ F) ⋙ q = p₀ := by rw [Functor.assoc, hF.comp_eq, hI]
  have : (If ⋙ Ff).Faithful := Fiber.faithful_mapOfComp hw V
  apply map_injective_of_iso Ff ea.symm eb.symm
  exact (Function.Injective.of_comp_iff' _
    ((FullyFaithful.ofFullyFaithful If).map_bijective a b)).1
    (Functor.map_injective (F := If ⋙ Ff) (X := a) (Y := b))

end Faithful

section QuotientFaithful

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

open CategoryTheory.Functor CategoryTheory.Pseudofunctor
open scoped CategoryTheory.Pseudofunctor.StrongTrans

/-- **The evaluated functors of a morphism of groupoids in algebraic spaces whose map on arrow
spaces is a monomorphism are faithful.**  An arrow of the evaluated groupoid at a test object is
determined by its underlying point of the arrow space, and a monomorphism of presheaves is
injective on points of every test object. -/
private theorem evaluation_faithful_of_mono
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hmono : Mono φ.toGroupoidHom.mapArrows) (T : (BigFppfOver C S hS)ᵒᵖ) :
    (φ.toGroupoidHom.evaluation T).Faithful := by
  let G' := G.toGroupoidInFunctors
  let H' := H.toGroupoidInFunctors
  let ηG := yonedaEquiv (X := Opposite.unop T) (F := G'.arrows)
  let ηH := yonedaEquiv (X := Opposite.unop T) (F := H'.arrows)
  constructor
  intro x y m n hmn
  apply G'.evaluationArrowEquiv T x y |>.injective
  apply Subtype.ext
  let a := (G'.evaluationArrowEquiv T x y m).1
  let b := (G'.evaluationArrowEquiv T x y n).1
  let α := ηG.symm a
  let β := ηG.symm b
  have hm := congrArg (fun k =>
    (H'.evaluationArrowEquiv T
      ((φ.toGroupoidHom.evaluation T).obj x)
      ((φ.toGroupoidHom.evaluation T).obj y) k).1) hmn
  rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
    Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow] at hm
  have hαβ : α ≫ φ.toGroupoidHom.mapArrows = β ≫ φ.toGroupoidHom.mapArrows := by
    apply ηH.injective
    dsimp only [ηH]
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa [α, β, ηG, ηH] using hm
  simpa [α, β, ηG] using congrArg ηG ((cancel_mono _).mp hαβ)

/-- **The canonical map from the presentation of a quotient stack to the quotient stack is fully
faithful.**  Part (2) of Stacks 044X makes it fully faithful on every fibre, and Stacks 003Z (1)
turns that into full faithfulness. -/
noncomputable def toQuotientStackFullyFaithful
    (G : GroupoidInAlgebraicSpaces C S hS A) : (toQuotientStack G).FullyFaithful := by
  have h := (IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (quotientPrestack G).p (quotientStack G).p
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (toQuotientStack G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq).2
    (fun T => ⟨(fullyFaithful_fiberFunctor_toQuotientStack G T).some.full,
      (fullyFaithful_fiberFunctor_toQuotientStack G T).some.faithful⟩)
  have : (toQuotientStack G).Full := h.1
  have : (toQuotientStack G).Faithful := h.2
  exact FullyFaithful.ofFullyFaithful _

/-- **The induced 1-morphism of quotient stacks is faithful once the evaluated functors of `φ`
are.**

This is the step of Stacks 0DU2 that Stacks 04Y5 converts into representability by algebraic
spaces, and it is strictly weaker than Stacks 046S, which makes `[φ]` *fully* faithful exactly
when the arrow space of the source is the restriction of that of the target — a cartesian square
that an open subgroupoid does not satisfy.

The canonical maps from the pointwise groupoid fibrations to the two quotient stacks are fully
faithful, and the 2-isomorphism of Stacks 046Q makes the restriction of `[φ]` to the presentation
of the source faithful; faithfulness then descends to the stackification.

Evaluated faithfulness is what the argument uses, and it is strictly weaker than a monomorphism
on arrow spaces: `AlgebraicGeometry.Stack.faithful_quotientStackMap_of_mono` is the corollary for
a monomorphism, and the base change of Stacks 0DTA satisfies the hypothesis without satisfying
that one, its arrow projection `X' ×_X R ⟶ R` not being a monomorphism. -/
theorem faithful_quotientStackMap_of_evaluation_faithful
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hev : ∀ T : (BigFppfOver C S hS)ᵒᵖ, (φ.toGroupoidHom.evaluation T).Faithful) :
    (quotientStackMap φ).toFunctor.Faithful := by
  let E := quotientPrestackEquivalence G
  let F := (quotientStackMap φ).toFunctor
  have hP : (quotientPointwiseMap φ).toFunctor.Faithful :=
    cogrothendieckMapFaithful (quotientPointwiseMapData φ).val (fun T => by
      rw [(quotientPointwiseMapData φ).property.1]
      exact hev (op T))
  have hK : (pointwiseToQuotientStack H).Faithful :=
    ((quotientPrestackEquivalence H).fullyFaithfulFunctor.comp
      (toQuotientStackFullyFaithful H)).faithful
  have hPK : ((BasedNatTrans.forgetful
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors))
      (quotientStack H)).obj
      (BasedFunctor.comp (quotientPointwiseMap φ) (pointwiseToQuotientStackBased H))).Faithful :=
    Faithful.comp (F := (quotientPointwiseMap φ).toFunctor)
      (G := pointwiseToQuotientStack H)
  have hIF : (pointwiseToQuotientStack G ⋙ F).Faithful :=
    Faithful.of_iso ((BasedNatTrans.forgetful _ _).mapIso (quotientStackMap_commutes φ))
  have hIF2 : ((E.functor ⋙ toQuotientStack G) ⋙ F).Faithful := hIF
  have hIF3 : (E.functor ⋙ (toQuotientStack G ⋙ F)).Faithful :=
    Faithful.of_iso (Functor.associator E.functor (toQuotientStack G) F)
  have hinv : E.inverse.Faithful := E.symm.fullyFaithfulFunctor.faithful
  have h1 : (E.inverse ⋙ (E.functor ⋙ (toQuotientStack G ⋙ F))).Faithful :=
    Faithful.comp (F := E.inverse) (G := E.functor ⋙ (toQuotientStack G ⋙ F))
  have hEF : (toQuotientStack G ⋙ F).Faithful :=
    Faithful.of_iso ((Functor.associator E.inverse E.functor _).symm ≪≫
      isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _)
  exact faithful_of_locally_essImage (toQuotientStack G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (toQuotientStackFullyFaithful G)
    (IsFibredOneMorphism.of_isFiberedInGroupoids
      (isFiberedInGroupoids_quotientStack H) (quotientStackMap φ).w)
    hEF (isFiberedInGroupoids_quotientStack G) (isFiberedInGroupoids_quotientStack H)
    (BigFppfOver.topology C S hS)
    (isStack_quotientStack G) (isStack_quotientStack H)
    (fun T x => by
      obtain ⟨R, hR, h⟩ := essImage_toQuotientStack G T x
      exact ⟨R, hR, fun f hf => h hf⟩)

/-- **The induced 1-morphism of quotient stacks is faithful once the map on arrow spaces is a
monomorphism.** A monomorphism of presheaves is injective on the points of every test object, and
an arrow of an evaluated groupoid is determined by its underlying point of the arrow space, so
the evaluated functors of `φ` are faithful and
`AlgebraicGeometry.Stack.faithful_quotientStackMap_of_evaluation_faithful` applies. -/
theorem faithful_quotientStackMap_of_mono
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hmono : Mono φ.toGroupoidHom.mapArrows) :
    (quotientStackMap φ).toFunctor.Faithful :=
  faithful_quotientStackMap_of_evaluation_faithful φ
    (fun T => evaluation_faithful_of_mono φ hmono T)

end QuotientFaithful

section Transfer

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS} {G H : GroupoidInAlgebraicSpaces C S hS A}

/-- **Naturality of the arrow map of a morphism of groupoids in algebraic spaces against the
source maps.** -/
theorem mapArrows_comp_source (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    φ.toGroupoidHom.mapArrows ≫ H.toGroupoidInFunctors.source =
      G.toGroupoidInFunctors.source ≫ φ.toGroupoidHom.mapObjects := by
  ext T a
  exact φ.toGroupoidHom.map_source T a

/-- **Naturality of the arrow map of a morphism of groupoids in algebraic spaces against the
target maps.** -/
theorem mapArrows_comp_target (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    φ.toGroupoidHom.mapArrows ≫ H.toGroupoidInFunctors.target =
      G.toGroupoidInFunctors.target ≫ φ.toGroupoidHom.mapObjects := by
  ext T a
  exact φ.toGroupoidHom.map_target T a

/-- A source or target map of an open subgroupoid factors as the arrow map, the corresponding map
of the target groupoid, and the inverse isomorphism on objects, an open immersion. -/
private theorem exists_eq_mapArrows_comp (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    {k : G.toGroupoidInFunctors.arrows ⟶ G.toGroupoidInFunctors.objects}
    {k' : H.toGroupoidInFunctors.arrows ⟶ H.toGroupoidInFunctors.objects}
    (hk : φ.toGroupoidHom.mapArrows ≫ k' = k ≫ φ.toGroupoidHom.mapObjects) :
    ∃ ι : H.toGroupoidInFunctors.objects ⟶ G.toGroupoidInFunctors.objects,
      Space.IsOpenImmersion C S hS ι ∧ k = φ.toGroupoidHom.mapArrows ≫ k' ≫ ι := by
  obtain ⟨ι, hι1, hι2⟩ := hobj.out
  have hιiso : IsIso ι := ⟨⟨φ.toGroupoidHom.mapObjects, hι2, hι1⟩⟩
  refine ⟨ι, Space.isOpenImmersion_of_isIso C S hS ι, ?_⟩
  rw [← Category.assoc, hk, Category.assoc, hι1, Category.comp_id]

/-- **Flatness of the factorization of the source or target map of an open subgroupoid.**  An
open immersion of algebraic spaces is étale (Stacks 03FP) hence flat (Stacks 0467), and flatness
is stable under composition (Stacks 03MN). -/
private theorem isFlat_mapArrows_comp (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    {ι : H.toGroupoidInFunctors.objects ⟶ G.toGroupoidInFunctors.objects}
    (hιopen : Space.IsOpenImmersion C S hS ι)
    {k : H.toGroupoidInFunctors.arrows ⟶ H.toGroupoidInFunctors.objects}
    (hk : Space.IsFlat C S hS k) :
    Space.IsFlat C S hS (φ.toGroupoidHom.mapArrows ≫ k ≫ ι) := by
  have hinv : Space.IsFlat C S hS ι :=
    Space.isFlat_of_isEtale C S hS
      (Space.isEtale_of_isOpenImmersion C S hS hιopen)
  refine Space.isFlat_comp C S hS G.arrows.property H.arrows.property G.objects.property _ _
    (Space.isFlat_of_isEtale C S hS
      (Space.isEtale_of_isOpenImmersion C S hS hopen)) ?_
  exact Space.isFlat_comp C S hS H.arrows.property H.objects.property G.objects.property _ _
    hk hinv

/-- **Local finite presentation of the factorization of the source or target map of an open
subgroupoid.**  An open immersion of algebraic spaces is locally of finite presentation
(Stacks 06CN), and that property is stable under composition (Stacks 03XQ). -/
private theorem isLocallyOfFinitePresentation_mapArrows_comp
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    {ι : H.toGroupoidInFunctors.objects ⟶ G.toGroupoidInFunctors.objects}
    (hιopen : Space.IsOpenImmersion C S hS ι)
    {k : H.toGroupoidInFunctors.arrows ⟶ H.toGroupoidInFunctors.objects}
    (hk : Space.IsLocallyOfFinitePresentation C S hS k) :
    Space.IsLocallyOfFinitePresentation C S hS (φ.toGroupoidHom.mapArrows ≫ k ≫ ι) := by
  have hinv : Space.IsLocallyOfFinitePresentation C S hS ι :=
    Space.isLocallyOfFinitePresentation_of_isOpenImmersion C S hS hιopen
  refine Space.isLocallyOfFinitePresentation_comp C S hS G.arrows.property H.arrows.property
    G.objects.property _ _
    (Space.isLocallyOfFinitePresentation_of_isOpenImmersion C S hS hopen) ?_
  exact Space.isLocallyOfFinitePresentation_comp C S hS H.arrows.property H.objects.property
    G.objects.property _ _ hk hinv

/-- **Flatness of the source map of an open subgroupoid.**  If the map on arrow spaces of
`φ : G ⟶ H` is an open immersion and its map on object spaces is an isomorphism, then the source
map of `G` is flat as soon as that of `H` is: it is the arrow map followed by the source map of
`H` followed by the inverse isomorphism on objects. -/
theorem isFlat_source_of_mapArrows_isOpenImmersion (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hH : Space.IsFlat C S hS H.source.hom) :
    Space.IsFlat C S hS G.source.hom := by
  obtain ⟨ι, hιopen, hfac⟩ := exists_eq_mapArrows_comp φ hobj
    (mapArrows_comp_source φ)
  change Space.IsFlat C S hS G.toGroupoidInFunctors.source
  rw [hfac]
  exact isFlat_mapArrows_comp φ hopen hιopen hH

/-- **Flatness of the target map of an open subgroupoid.**  The counterpart of
`AlgebraicGeometry.Stack.isFlat_source_of_mapArrows_isOpenImmersion` for the target map. -/
theorem isFlat_target_of_mapArrows_isOpenImmersion (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hH : Space.IsFlat C S hS H.target.hom) :
    Space.IsFlat C S hS G.target.hom := by
  obtain ⟨ι, hιopen, hfac⟩ := exists_eq_mapArrows_comp φ hobj
    (mapArrows_comp_target φ)
  change Space.IsFlat C S hS G.toGroupoidInFunctors.target
  rw [hfac]
  exact isFlat_mapArrows_comp φ hopen hιopen hH

/-- **Local finite presentation of the source map of an open subgroupoid.**  If the map on arrow
spaces of `φ : G ⟶ H` is an open immersion and its map on object spaces is an isomorphism, then
the source map of `G` is locally of finite presentation as soon as that of `H` is. -/
theorem isLocallyOfFinitePresentation_source_of_mapArrows_isOpenImmersion
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hH : Space.IsLocallyOfFinitePresentation C S hS H.source.hom) :
    Space.IsLocallyOfFinitePresentation C S hS G.source.hom := by
  obtain ⟨ι, hιopen, hfac⟩ := exists_eq_mapArrows_comp φ hobj
    (mapArrows_comp_source φ)
  change Space.IsLocallyOfFinitePresentation C S hS G.toGroupoidInFunctors.source
  rw [hfac]
  exact isLocallyOfFinitePresentation_mapArrows_comp φ hopen hιopen hH

/-- **Local finite presentation of the target map of an open subgroupoid.**  The counterpart of
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_source_of_mapArrows_isOpenImmersion` for
the target map. -/
theorem isLocallyOfFinitePresentation_target_of_mapArrows_isOpenImmersion
    (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hH : Space.IsLocallyOfFinitePresentation C S hS H.target.hom) :
    Space.IsLocallyOfFinitePresentation C S hS G.target.hom := by
  obtain ⟨ι, hιopen, hfac⟩ := exists_eq_mapArrows_comp φ hobj
    (mapArrows_comp_target φ)
  change Space.IsLocallyOfFinitePresentation C S hS G.toGroupoidInFunctors.target
  rw [hfac]
  exact isLocallyOfFinitePresentation_mapArrows_comp φ hopen hιopen hH

/-- **The arrow map of an open subgroupoid is a monomorphism.**  An open immersion of algebraic
spaces is an immersion, hence a monomorphism by Stacks 042R. -/
theorem mono_mapArrows_of_isOpenImmersion (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows) :
    Mono φ.toGroupoidHom.mapArrows :=
  Space.mono_of_isImmersion C S hS (Space.isImmersion_of_isOpenImmersion C S hS hopen)

end Transfer

section Conclusions

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- **Stacks 04Y5, the implication (2) ⟹ (3), as a hypothesis**: a 1-morphism of categories
fibred in groupoids over the big fppf site of `S` whose underlying functor is faithful is
representable by algebraic spaces.

This is a condition and proves nothing.  The library has the converse implication (3) ⟹ (2) and
the equivalence of (1) and (2), but not this one: its proof passes through the implication
(1) ⟹ (3) of Stacks 04SZ, which needs the bootstrap step that an fppf sheaf with representable
diagonal admitting a surjective *smooth* morphism from a scheme is an algebraic space, and the
library has only the surjective *étale* version.  Deliberately untagged, for the same reason that
the absent implication of Stacks 04SZ is. -/
abbrev Theorem04Y5 : Prop :=
  ∀ (𝒳 𝒴 : BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS)),
    𝒳.p.IsFiberedInGroupoids → 𝒴.p.IsFiberedInGroupoids →
      ∀ f : 𝒳 ⥤ᵇ 𝒴, f.toFunctor.Faithful → IsRepresentableByAlgebraicSpaces C S hS f

variable {C S hS} {A : AlgebraicSpaces C S hS}

/-- The 1-morphism `[φ] : [U/P] ⟶ [U/R]` of Stacks 046Q, read as a 1-morphism of the 2-category
of categories fibred in groupoids over the big fppf site of `S`.  This is the shape in which
Stacks 03YK and Stacks 06D7 consume it. -/
noncomputable def quotientStackMapCFGHom {G H : GroupoidInAlgebraicSpaces C S hS A}
    (φ : GroupoidInAlgebraicSpaces.Hom G H) :
    CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G) ⟶
      CatFiberedInGroupoids.mk (quotientStack H) (isFiberedInGroupoids_quotientStack H) :=
  Bicategory.InducedBicategory.mkHom (quotientStackMap φ)

end Conclusions

end AlgebraicGeometry.Stack

end
