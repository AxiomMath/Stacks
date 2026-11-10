module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.Integral
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion

/-!
# The normalization of an algebraic stack (Stacks 0GMJ)

Let `𝒳` be an algebraic stack presented by a smooth groupoid `(U, R, s, t, c)` in algebraic
spaces, so that `𝒳 = [U/R]`. Stacks 0GMJ asserts that there is an integral 1-morphism
`𝒳^ν ⟶ 𝒳` whose base change along every smooth morphism from a scheme `U ⟶ 𝒳` is the
normalization of `U`. The source builds `𝒳^ν` as the quotient stack `[U^ν/R^ν]` of the
normalized groupoid and `ν` as the 1-morphism induced by the morphism of groupoids
`(U^ν, R^ν) ⟶ (U, R)`.

The normalized groupoid is the input this library does not have. The existence half of Stacks
07U4 that it rests on is itself proved — for an algebraic space satisfying condition (2) of
Stacks 0BB1, by `AlgebraicGeometry.Space.nonempty_normalizationData` — but
what is missing is the lift of the groupoid structure to the normalized object and arrow spaces.
It is carried here as
`AlgebraicGeometry.Stack.NormalizationGroupoid`, and `𝒳^ν` and `ν` are then *built* from it as
`AlgebraicGeometry.Stack.quotientStackCFG` of the normalized groupoid and
`AlgebraicGeometry.Stack.quotientStackMapHom` of its morphism of groupoids — never chosen from
an existence statement.

## Main definitions

* `AlgebraicGeometry.Stack.IsIntegralHom`: integrality of a 1-morphism of categories fibred in
  groupoids representable by algebraic spaces, that is the notion of Stacks 04XB at
  `AlgebraicGeometry.Space.IsIntegralHom` of Stacks 03ZP.
* `AlgebraicGeometry.Stack.NormalizationGroupoid`: the normalized groupoid `(U^ν, R^ν)` of a
  groupoid in algebraic spaces, together with the morphism of groupoids to it, the normalization
  data of the object space, the cartesian source square `R^ν = R ×_{s, U} U^ν` and the
  smoothness of the normalized groupoid.

## Main results

* `AlgebraicGeometry.Stack.isIntegralHom_quotientStackMapHom_normalization`: the 1-morphism
  `[U^ν/R^ν] ⟶ [U/R]` is integral.
* `AlgebraicGeometry.Stack.exists_isIntegralHom_quotientStackMapHom_normalization`: the same
  conclusion in the existential form the source states, with the two witnesses exhibited.

## Partial coverage

Of the three assertions of Stacks 0GMJ — existence of `𝒳^ν ⟶ 𝒳`, its integrality, and the
identification of `𝒳^ν ×_𝒳 U` with the normalization of `U` for every smooth morphism from a
scheme — the first two are proved here. The third is proved at the presenting chart, in
`StacksFrontier.AlgebraicGeometry.Stacks.NormalizationChartFibreProduct`, out of the cartesian
source square of the normalized groupoid and Stacks 04ZN; it is in the 2-category of stacks in
groupoids, which is not the one the descent step below runs in. Every hypothesis carried is
named below, with the result it stands for.

* `AlgebraicGeometry.Stack.NormalizationGroupoid` carries the **existence half of Stacks 07U4**:
  that `U` and `R` have normalizations and that, normalization commuting with the smooth
  morphisms `s` and `t`, the normalization of `R` is `R ×_{s, U} U^ν`, so that the groupoid
  structure descends to `(U^ν, R^ν)`. Of this, the existence of the normalization of the object
  space alone is provable rather than forced: it is
  `AlgebraicGeometry.Space.nonempty_normalizationData`
  (`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction`), which this file does
  not import, for an algebraic space satisfying condition (2) of Stacks 0BB1. What has to stay a
  hypothesis is the rest: the library has no construction of the normalized *groupoid* — the
  groupoid object `(U^ν, R^ν)` with its lifted structure morphisms, the morphism of groupoids to
  `(U, R)` and its smoothness — so this is data, and `𝒳^ν` and `ν` are constructed from it
  rather than assumed to exist.
* `hf` is **Stacks 04ZP**, representability by algebraic spaces of the 1-morphism, which this
  library does not have.
* `Q`, `hQ`, `hQfst`, `a`, `ha`, `p`, `q`, `α`, `eF`, `eG₀` and `hrep` are **Stacks 04ZN**: they
  say that one base change of `[U^ν/R^ν] ⟶ [U/R]`, along the canonical projection
  `S_U ⟶ [U/R]` of Stacks 044R, is the normalization morphism `U^ν ⟶ U`. They take the shape
  `AlgebraicGeometry.Stack.hasRelativeProperty_quotientStackMapHom_of_representingMap` uses for
  that input, which is the 2-category of categories fibred in groupoids of Stacks 02XS. The
  library *does* prove Stacks 04ZN — it is
  `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`, and
  `AlgebraicGeometry.Stack.isTwoFibreProduct_normalizationChartSquare` instantiates it at the
  normalized groupoid — but in the 2-category of stacks in groupoids of Stacks 02ZK, and a square
  proved 2-cartesian in one of those two sub-2-categories of the categories over the site cannot
  be moved to the other, for the reason recorded in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquare`. The second obstruction is
  that the 1-morphism of Stacks 046Q appears twice in the library, as
  `AlgebraicGeometry.Stack.quotientStackMap` in the groupoid development and as
  `AlgebraicGeometry.Stack.quotientStackMapHom` here, and the proof of Stacks 04ZN is stated for
  the former. So these hypotheses stay. Integrality is genuinely derived from them: the descent
  step is Stacks 045D, which turns the single identified base change into the relative property
  over every scheme-valued point of `[U/R]`.
* The conclusion is stated with `AlgebraicGeometry.Stack.IsIntegralHom`, the Stacks 04XB notion
  for a category fibred in groupoids, rather than for a 1-morphism of
  `AlgebraicGeometry.Stack.AlgebraicStacks`: exhibiting a quotient stack as an element of that
  subtype is **Stacks 04TK**, which this library does not have, and whose absence is recorded in
  the same terms in `StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRestrictionImmersion`.
  So the statement does not assert that `[U^ν/R^ν]` is an algebraic stack.
* The hypothesis of Stacks 0GMI on `𝒳` is not a separate assumption here: the normalization data
  of the object space contains, through
  `AlgebraicGeometry.Space.NormalizationData.finite_irreducibleComponents_of_chart`, exactly the
  finiteness of the irreducible components over the quasi-compact opens of the charts of `U`
  which is condition (1) of Stacks 0GMI for the presenting chart, and which is what makes the
  normalization of `U` defined at all (Stacks 035N).

## Implementation notes

Integrality of a 1-morphism is `AlgebraicGeometry.Stack.HasRelativeProperty` at
`AlgebraicGeometry.Space.integralMorphismProperty`, the short spelling, rather than a
hand-written quantifier as in `StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism`: both
instance hypotheses of that definition are available for integrality. Stability under base
change is `AlgebraicGeometry.Space.integralMorphismProperty_isStableUnderBaseChange` (Stacks
03ZS), and locality at the target is Stacks 0425
(`AlgebraicGeometry.Space.integralMorphismProperty_isLocalAtTarget_fpqc`) carried from the fpqc
precoverage to the fppf one along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`; that transfer is supplied inside
the definition rather than as a global instance, so that no second copy of it is coined.

The source square of the morphism of groupoids is recorded as
`AlgebraicGeometry.Stack.NormalizationGroupoid.isPullback_source` although nothing in this module
consumes it: it is the hypothesis of Stacks 04ZN, and it is what
`StacksFrontier.AlgebraicGeometry.Stacks.NormalizationChartFibreProduct` reads off the structure in
order to prove the fibre-product assertion of Stacks 0GMJ at the presenting chart. The smoothness
field is recorded for the same kind of reason, for Stacks 04TK.

The normalization morphism of the object space is `AlgebraicGeometry.Space.NormalizationData.hom`
and is integral by Stacks 0BB4, part (2)
(`AlgebraicGeometry.Space.NormalizationData.isIntegralHom_hom`), for an arbitrary algebraic
space; no representability of the object space is needed, so the presenting groupoid is not
asked to have a scheme of objects.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 0425](https://stacks.math.columbia.edu/tag/0425)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0GMI](https://stacks.math.columbia.edu/tag/0GMI)
* [Stacks Project, Tag 0GMJ](https://stacks.math.columbia.edu/tag/0GMJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.Stack

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is integral* when every algebraic space representing its base
change along a scheme-valued point of the target has integral structural morphism, read as a
morphism of algebraic spaces over `S`.

This is the notion of Stacks 04XB at `AlgebraicGeometry.Space.IsIntegralHom` of Stacks 03ZP. It
is untagged because Stacks 04XB's general definition is already carried by
`AlgebraicGeometry.Stack.HasRelativeProperty` (Stacks 03YK), and its conjunction with
representability for a 1-morphism of `AlgebraicGeometry.Stack.AlgebraicStacks` is Stacks 0CHU,
part (1). -/
abbrev IsIntegralHom (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) : Prop :=
  letI : (Space.integralMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, t} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  HasRelativeProperty.{u, v, w, t} B S hS (Space.integralMorphismProperty B S hS) f hf

end FiberedInGroupoids

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The normalized groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)` of a groupoid in algebraic spaces.**

This is the data the proof of Stacks 0GMJ extracts from Stacks 07U4: the object space `U` has a
normalization `U^ν`, taking normalization commutes with the smooth morphisms `s` and `t`, so the
normalization of the arrow space is `R^ν = R ×_{s, U} U^ν`, and the groupoid structure of
`(U, R)` lifts to `(U^ν, R^ν)` along the resulting morphism of groupoids.

The library has the existence of a normalization for an algebraic space satisfying condition (2)
of Stacks 0BB1 — `AlgebraicGeometry.Space.nonempty_normalizationData`, which
this file does not import — but not for a groupoid in algebraic spaces, so the whole is carried
as a hypothesis; see the partial-coverage section of the module documentation. -/
structure NormalizationGroupoid (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The normalized groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)`. -/
  groupoid : GroupoidInAlgebraicSpaces C S hS B
  /-- The morphism of groupoids `(U^ν, R^ν) ⟶ (U, R)` of Stacks 043W, part (2). -/
  hom : GroupoidInAlgebraicSpaces.Hom groupoid G
  /-- The normalization of the object space, as data in the sense of Stacks 07U4. -/
  data : Space.NormalizationData C S hS G.objects.obj
  /-- The object space of the normalized groupoid is the normalization of the object space. -/
  objects_eq : groupoid.objects.obj = data.space
  /-- On objects the morphism of groupoids is the normalization morphism `U^ν ⟶ U`. -/
  mapObjects_eq : hom.toGroupoidHom.mapObjects = eqToHom objects_eq ≫ data.hom
  /-- The arrow space of the normalized groupoid is the base change of the arrow space along the
  normalization of the object space: `R^ν = R ×_{s, U} U^ν`. This is the consequence of
  Stacks 07U4 that makes the groupoid structure lift, and it is the hypothesis of
  Stacks 04ZN. -/
  isPullback_source : IsPullback hom.toGroupoidHom.mapArrows groupoid.source.hom
    G.source.hom hom.toGroupoidHom.mapObjects
  /-- The normalized groupoid is smooth, in the sense of Stacks 04TH. -/
  smooth : GroupoidInAlgebraicSpaces.IsSmooth C S hS groupoid

variable (C S hS)

/-- **Stacks 0GMJ, the 1-morphism `𝒳^ν ⟶ 𝒳` and its integrality.** Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces whose quotient stack is `𝒳 = [U/R]`, and let `N` be a normalized
groupoid for it. Then the 1-morphism `ν : [U^ν/R^ν] ⟶ [U/R]` of Stacks 046Q induced by the
morphism of groupoids `(U^ν, R^ν) ⟶ (U, R)` is integral in the sense of Stacks 04XB.

The source's argument is exactly this one: `U^ν ⟶ U` is integral, it is the base change of `ν`
along the presenting chart, and integrality descends. The base-change identification is
Stacks 04ZN and is carried; integrality of `U^ν ⟶ U` is Stacks 0BB4, part (2), and is proved in
this library. See the partial-coverage section of the module documentation for every hypothesis
and the result it stands for. -/
@[stacks 0GMJ "integrality of ν; the normalized groupoid, Stacks 04ZP and the 04ZN form of \
  the base change are hypotheses"]
theorem isIntegralHom_quotientStackMapHom_normalization
    {G : GroupoidInAlgebraicSpaces C S hS B} (N : NormalizationGroupoid C S hS G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMapHom N.hom).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackMapHom N.hom))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (N.data.space ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p)
    (hrep : representingMap C S hS 𝒜 𝒞 N.data.space G.objects.obj eF eG₀ a = N.data.hom) :
    IsIntegralHom C S hS (quotientStackMapHom N.hom) hf :=
  letI : (Space.integralMorphismProperty C S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} C S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage C S hS)
  hasRelativeProperty_quotientStackMapHom_of_representingMap.{u, u + 1} C S hS N.hom
    (Space.integralMorphismProperty C S hS) hf Q hQ hQfst a ha p q α
    N.data.space G.objects.obj N.data.isAlgebraicSpace G.objects.property eF eG₀
    (by simp only [hrep]; exact N.data.isIntegralHom_hom G.objects.property)

/-- **Stacks 0GMJ in the existential form the source states it.** For a groupoid in algebraic
spaces with a normalized groupoid, there is a category fibred in groupoids `𝒳^ν` over the big
fppf site together with an integral 1-morphism `𝒳^ν ⟶ [U/R]`.

The witnesses are the quotient stack `[U^ν/R^ν]` of Stacks 044Q and the 1-morphism of
Stacks 046Q, so the existential is inhabited by the source's own construction. -/
@[stacks 0GMJ "the existence assertion, witnessed by [U^ν/R^ν] and the 1-morphism of Stacks 046Q"]
theorem exists_isIntegralHom_quotientStackMapHom_normalization
    {G : GroupoidInAlgebraicSpaces C S hS B} (N : NormalizationGroupoid C S hS G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMapHom N.hom).hom)
    (Q : Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackMapHom N.hom))
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom)
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (a : 𝒜 ⟶ 𝒞) (ha : IsRepresentableByAlgebraicSpaces C S hS a.hom)
    (p : Q.pt.val ⥤ᵇ 𝒜.val) (q : (liftedObjectSpace G).val ⥤ᵇ 𝒞.val)
    [Functor.IsEquivalence p.toFunctor] [Functor.IsEquivalence q.toFunctor]
    (α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (N.data.space ⋙ typeToCat)).p)
    (eG₀ : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G.objects.obj ⋙ typeToCat)).p)
    (hrep : representingMap C S hS 𝒜 𝒞 N.data.space G.objects.obj eF eG₀ a = N.data.hom) :
    ∃ (𝒳ν : CatFiberedInGroupoids (BigFppfOver C S hS))
      (ν : 𝒳ν ⟶ quotientStackCFG C S hS G)
      (hν : IsRepresentableByAlgebraicSpaces C S hS ν.hom),
      IsIntegralHom.{u, u + 1, u + 1, u + 1} C S hS ν hν :=
  ⟨quotientStackCFG C S hS N.groupoid, quotientStackMapHom N.hom, hf,
    isIntegralHom_quotientStackMapHom_normalization.{u, u + 1} C S hS N hf Q hQ hQfst a ha p q α
      eF eG₀ hrep⟩

/-- **The normalization `ð³^Î½` of an algebraic stack.** For a groupoid in algebraic spaces
`(U, R, s, t, c)` presenting `ð³ = [U/R]`, and a normalized groupoid `N` for it, this is the
quotient stack `[U^Î½/R^Î½]` of Stacks 044Q of the normalized groupoid.

This is the source of the normalization morphism `AlgebraicGeometry.Stack.normalization`, which
carries the tag; the object is named here so that the morphism has a domain to be stated
against, exactly as `AlgebraicGeometry.Scheme.normalizationScheme` does for Stacks 035N. It is
the first witness of
`AlgebraicGeometry.Stack.exists_isIntegralHom_quotientStackMapHom_normalization`, named rather
than chosen out of that existential. -/
noncomputable abbrev normalizationStack {G : GroupoidInAlgebraicSpaces C S hS B}
    (N : NormalizationGroupoid C S hS G) :
    CatFiberedInGroupoids (BigFppfOver C S hS) :=
  quotientStackCFG C S hS N.groupoid

/-- **Stacks 0GMK, the normalization of an algebraic stack.** For a groupoid in algebraic spaces
`(U, R, s, t, c)` presenting `ð³ = [U/R]`, and a normalized groupoid `N` for it, the
*normalization* of `𝒳` is the 1-morphism `ν : 𝒳^ν ⟶ 𝒳` of Stacks 046Q induced by the
morphism
of groupoids `(U^Î½, R^Î½) â¶ (U, R)`, with `ð³^Î½ = [U^Î½/R^Î½]` the quotient stack
`AlgebraicGeometry.Stack.normalizationStack` of the normalized groupoid.

This is the morphism constructed in Stacks 0GMJ, named: the body is the construction
`AlgebraicGeometry.Stack.quotientStackMapHom` of the source's proof, so nothing is chosen out of
the existential of
`AlgebraicGeometry.Stack.exists_isIntegralHom_quotientStackMapHom_normalization`. Its
integrality is `AlgebraicGeometry.Stack.isIntegralHom_quotientStackMapHom_normalization`, which
applies to it unchanged.

The hypothesis of Stacks 0GMI on `ð³` is not a separate assumption, for the reason given in the
coverage notes of this module's documentation: it is carried inside `N`, whose
normalization data of the object space contains condition (1) of Stacks 0GMI for the presenting
chart through
`AlgebraicGeometry.Space.NormalizationData.finite_irreducibleComponents_of_chart`. The
equivalences of Stacks 0GMI are stated for `AlgebraicGeometry.Stack.AlgebraicStacks`, and
exhibiting a quotient stack there is Stacks 04TK, which this library does not have, so no 0GMI
condition can be stated at this presentation. -/
@[stacks 0GMK "the normalization ν : 𝒳^ν ⟶ 𝒳 at a presenting smooth groupoid, with the \
  normalized groupoid as data"]
noncomputable abbrev normalization {G : GroupoidInAlgebraicSpaces C S hS B}
    (N : NormalizationGroupoid C S hS G) :
    normalizationStack C S hS N ⟶ quotientStackCFG C S hS G :=
  quotientStackMapHom N.hom

end AlgebraicGeometry.Stack

end
