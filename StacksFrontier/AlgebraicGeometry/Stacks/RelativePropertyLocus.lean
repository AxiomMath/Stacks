module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The locus where a representable 1-morphism of algebraic stacks has a relative property

Let `P`, `Q`, `R` be properties of morphisms of algebraic spaces such that all three are fppf
local on the target and stable under arbitrary base change, smoothness implies `R`, every
morphism `f : X ⟶ Y` with `Q` has a largest open `W(P, f) ⊆ X` on which `f` has `P`, and that
largest open is compatible with base change along a morphism with `R`. **Stacks 06M3** asserts,
for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks representable by algebraic spaces and having
`Q`, that

* (A) there is a largest open substack `𝒳' ⊆ 𝒳` on which `f` has `P`, and
* (B) for `𝒵 ⟶ 𝒴` representable by algebraic spaces with `R`, the base change
  `𝒵 ×_𝒴 𝒳'` is the largest open substack of `𝒵 ×_𝒴 𝒳` on which `id_𝒵 × f` has `P`.

This file carries the property of being such a largest open substack, its uniqueness, an
existence statement from locality of `P` along unions of open substacks, and the containment of
assertion (B) that holds for an arbitrary base change. The complete statement of Stacks 06M3,
from its four hypotheses on `P`, `Q` and `R`, is
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_and_isRelativePropertyLocus_baseChange`
in `StacksFrontier/AlgebraicGeometry/Stacks/RelativePropertyLocusOnSpaces.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.IsRelativePropertyLocus`: an open substack of `𝒳` is *the `P`-locus*
  of `f` when `f` restricted to it has the relative property `P` of **Stacks 03YK** and it
  contains every open substack with that property. This is the conclusion of assertion (A) of
  **Stacks 06M3**, written as a predicate.
* `AlgebraicGeometry.Stack.IsRelativePropertyLocalOnOpenSubstackUnions`: locality of the
  relative property `P` on the source, read along a union of open substacks, as a hypothesis.

## Main results

* `AlgebraicGeometry.Stack.eq_of_isRelativePropertyLocus`: the `P`-locus is unique, which is
  what makes the definite article of the source legitimate. This needs no input at all.
* `AlgebraicGeometry.Stack.exists_isRelativePropertyLocus`: the existence of the `P`-locus from
  `AlgebraicGeometry.Stack.IsRelativePropertyLocalOnOpenSubstackUnions`.
* `AlgebraicGeometry.Stack.isRelativePropertyLocus_baseChange_apply`: the containment
  `𝒵 ×_𝒴 𝒳' ⊆ W(P, f')` of assertion (B), unconditionally and for an arbitrary base change.
* `AlgebraicGeometry.Stack.exists_openSubstack_comap_isEquivalence`: the inverse image of an
  open substack along a 1-morphism of algebraic stacks, together with the equivalence
  identifying it with the 2-fibre product. This refines
  `AlgebraicGeometry.Stack.exists_openSubstack_comap`, whose transfer clause is stated for
  smoothness alone, to a form every property invariant under equivalence can consume.
* `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange_algebraicStacks`: **Stacks 045C** for
  an arbitrary 2-fibre product square of algebraic stacks.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp`: the
  restriction of a representable 1-morphism to an open substack is representable.

## Relation to the complete statement

Hypothesis (1) of the source — `P` fppf local on the target and stable under arbitrary base
change — is used throughout, as the two instance hypotheses on `P` that **Stacks 03YK** carries.
Hypotheses (2), (3) and (4) and the property `Q` do not appear in this file. The source's route
from them — a smooth chart `V ⟶ 𝒴`, the base change `U = V ×_𝒴 𝒳`, the largest open
`W(P, f') ⊆ U` of hypothesis (3) and its `R`-invariance from hypotheses (2) and (4) — is carried
out in `StacksFrontier/AlgebraicGeometry/Stacks/RelativePropertyLocusOnSpaces.lean`, which proves
assertion (A) from those hypotheses, the reverse containment of assertion (B), and the complete
statement
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_and_isRelativePropertyLocus_baseChange`.

## Implementation notes

Containment of open substacks is containment of their object properties, as in
`StacksFrontier/AlgebraicGeometry/Stacks/SmoothLocus.lean`, which is the specialisation of this
file's assertion (A) to `P` smooth (**Stacks 0DZR**); maximality is part of the predicate for
the reason recorded there, that the supremum of the object properties of the members is not the
object property of their union.

The union of open substacks the existence statement takes is that of **Stacks 05UQ**,
`AlgebraicGeometry.Stack.OpenSubstack.iUnion`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction of a representable 1-morphism to an open substack is representable.** The
inclusion of an open substack is representable by algebraic spaces by **Stacks 04YL**, and
representability by algebraic spaces is stable under composition by **Stacks 0301**. -/
theorem isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (W : OpenSubstack 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f).hom.hom :=
  isRepresentableByAlgebraicSpaces_comp B S hS
    (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic).hom f.hom W.isOpenImmersion.1 hf

/-- An open substack `W` of `𝒳` is *the `P`-locus* of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` representable by algebraic spaces when the restriction of `f` to `W` has the
relative property `P` of **Stacks 03YK** and every open substack of `𝒳` with that property is
contained in `W`.

This is the conclusion of assertion (A) of **Stacks 06M3**: `W` is the `𝒳'` of the source, and
the second clause is the force of the word *maximal* there. -/
def IsRelativePropertyLocus (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (W : OpenSubstack 𝒳) : Prop :=
  HasRelativeProperty B S hS P
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f).hom
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf W) ∧
    ∀ V : OpenSubstack 𝒳,
      HasRelativeProperty B S hS P
          (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic ≫ f).hom
          (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf V) →
        V.property ≤ W.property

/-- **Stacks 06M3, assertion (A), uniqueness of the maximal open substack.** Two open substacks
of `𝒳` on which `f` has `P` and which are maximal with that property coincide: each is contained
in the other, and an open substack is determined by its object property.

This is what makes the definite article in *the* maximal open substack of the source legitimate,
and it needs no input beyond those of the ambient site. -/
theorem eq_of_isRelativePropertyLocus (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom} {W W' : OpenSubstack 𝒳}
    (h : IsRelativePropertyLocus B S hS P f hf W)
    (h' : IsRelativePropertyLocus B S hS P f hf W') :
    W = W' :=
  OpenSubstack.ext (le_antisymm (h'.2 W h.1) (h.2 W' h'.1))

/-- **Locality of the relative property `P` along a union of open substacks of the source.** If
an open substack `W` of `𝒳` is the union of a family of open substacks on each of which a
representable 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` restricts to a 1-morphism with
the relative property `P` of **Stacks 03YK**, then `f` restricts to a 1-morphism with `P` on `W`.

This is the one input the existence statement of assertion (A) of **Stacks 06M3** needs beyond
formal manipulation of open substacks. The source gets it from hypotheses (2), (3) and (4)
through a smooth chart and **Stacks 0505**; see the module documentation for why that route is
not available. It is indexed by a `Set` of open substacks rather than by an arbitrary type,
which keeps it free of a universe parameter beyond the two the algebraic stack already has. -/
def IsRelativePropertyLocalOnOpenSubstackUnions (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)] : Prop :=
  ∀ (𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ 𝒴)
      (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) (s : Set (OpenSubstack 𝒳))
      (W : OpenSubstack 𝒳),
    OpenSubstack.IsUnion 𝒳 (fun U : s => (U : OpenSubstack 𝒳)) W.property →
      (∀ U ∈ s, HasRelativeProperty B S hS P
          (fullSubcategoryInclusion 𝒳 U.property U.isAlgebraic ≫ f).hom
          (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf U)) →
        HasRelativeProperty B S hS P
          (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f).hom
          (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf W)

/-- **Stacks 06M3, assertion (A), the existence of the maximal open substack.** A 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by algebraic spaces has an open substack
of `𝒳` on which it restricts to a 1-morphism with the relative property `P` of **Stacks 03YK**
and which contains every open substack with that property.

It is the union `AlgebraicGeometry.Stack.OpenSubstack.iUnion` (**Stacks 05UQ**) of the set of
all open substacks on which `f` has `P`: that `f` has `P` on it is the carried `hLocal`, and
maximality is the first clause of `AlgebraicGeometry.Stack.OpenSubstack.IsUnion` and does not
need it. -/
theorem exists_isRelativePropertyLocus (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hLocal : IsRelativePropertyLocalOnOpenSubstackUnions.{u, w} B S hS P)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    ∃ W : OpenSubstack 𝒳, IsRelativePropertyLocus B S hS P f hf W := by
  have hW := OpenSubstack.isUnion_iUnion (fun U : {U : OpenSubstack 𝒳 |
    HasRelativeProperty B S hS P (fullSubcategoryInclusion 𝒳 U.property U.isAlgebraic ≫ f).hom
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf U)} =>
      (U : OpenSubstack 𝒳))
  exact ⟨_, hLocal 𝒳 𝒴 f hf _ _ hW fun _ hU => hU, fun V hV => hW.1 ⟨V, hV⟩⟩

/-! ### Base change -/

/-- **Stacks 045C for a 2-fibre product square of algebraic stacks.** In a 2-fibre product square
over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the projection to `𝒵` has
the relative property `P` of **Stacks 03YK** as soon as `f` does.

`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` is the same statement in the ambient
2-category of categories fibred in groupoids; the underlying square of a 2-fibre product of
algebraic stacks is a 2-fibre product there by
`CategoryTheory.Bicategory.isTwoFibreProduct_underlying`, whose hypothesis
is met because the cospan has the 2-fibre product
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` (**Stacks 04TF**). -/
theorem hasRelativeProperty_baseChange_algebraicStacks
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom)
    (hPf : HasRelativeProperty B S hS P f.hom hf) :
    HasRelativeProperty B S hS P Q.fst.hom hfst := by
  have hQc : Bicategory.IsTwoFibreProduct (Bicategory.TwoCommSq.underlying Q) :=
    Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS g f) hQ
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
  exact hasRelativeProperty_baseChange.{u, u, u + 1} B S hS P 𝒳.val 𝒴.val 𝒵.val f.hom g.hom
    (Bicategory.TwoCommSq.underlying Q) hQc hf hPf

/-- **Stacks 0302 for a 2-fibre product square of algebraic stacks.** In a 2-fibre product square
over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`, the projection to `𝒵` is
representable by algebraic spaces as soon as `f` is.

This is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` read through the
underlying square, exactly as in
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange_algebraicStacks`. -/
theorem isRepresentableByAlgebraicSpaces_baseChange_algebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom := by
  have hQc : Bicategory.IsTwoFibreProduct (Bicategory.TwoCommSq.underlying Q) :=
    Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS g f) hQ
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
  exact isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val 𝒴.val 𝒵.val
    f.hom g.hom (Bicategory.TwoCommSq.underlying Q) hQc hf

/-- The base change of the inclusion of an open substack along `g` is representable by algebraic
spaces and is an open immersion. -/
private theorem isRepresentableByAlgebraicSpaces_and_isOpenImmersion_twoFibreProductSquare
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (W : OpenSubstack 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic).hom).fst.hom ∧
    Stack.IsOpenImmersion B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic).hom).fst :=
  have hQc := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    g.hom (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic).hom
  ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ _ g.hom _ hQc
      W.isOpenImmersion.1,
    isOpenImmersion_baseChange.{u, u, u + 1} B S hS _ _ _ _ g.hom _ hQc W.isOpenImmersion.2⟩

/-- **The inverse image of an open substack along a 1-morphism of algebraic stacks over `S`, with
its comparison to the 2-fibre product.** For `g : 𝒳' ⟶ 𝒳` and an open substack `W` of `𝒳`, the
objects of `𝒳'` carried by `g` into `W` cut out an open substack `W'` of `𝒳'`, and the 2-fibre
product `𝒳' ×_𝒳 W` maps to `W'` by a 1-morphism whose underlying functor is an equivalence and
whose composite with the inclusion of `W'` is 2-isomorphic to the projection `𝒳' ×_𝒳 W ⟶ 𝒳'`.

The open substack is the essential image of that projection, an open immersion by **Stacks 045C**
and **Stacks 0302**, read through **Stacks 0506**; the equivalence is the factorization clause of
**Stacks 0506**. This is `AlgebraicGeometry.Stack.exists_openSubstack_comap` with the comparison
exposed in place of its transfer clause for smoothness, so that any property invariant under
equivalence of the source and under 2-isomorphism can be carried across it. -/
theorem exists_openSubstack_comap_isEquivalence
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (W : OpenSubstack 𝒳) :
    ∃ (W' : OpenSubstack 𝒳')
      (e : (twoFibreProductSquareAlgebraicStacks B S hS g
          (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic)).pt ⟶
        fullSubcategoryAlgebraicStack 𝒳' W'.property W'.isAlgebraic),
      (∀ x : 𝒳'.val.val.obj, W'.property x ↔ W.property (g.hom.hom.toFunctor.obj x)) ∧
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom) ∧
      Nonempty (e ≫ fullSubcategoryInclusion 𝒳' W'.property W'.isAlgebraic ≅
        (twoFibreProductSquareAlgebraicStacks B S hS g
          (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic)).fst) := by
  have := W.strictlyFull
  set j := fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic with hj
  obtain ⟨hrepr, hoi⟩ := isRepresentableByAlgebraicSpaces_and_isOpenImmersion_twoFibreProductSquare
    B S hS g W
  set Q := twoFibreProductSquareAlgebraicStacks B S hS g j with hQdef
  have himm : AlgebraicStacks.IsImmersion B S hS Q.fst :=
    ⟨hrepr, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hoi U y hy F hF he)⟩
  have hPalg := AlgebraicStacks.isAlgebraicStack_essImage Q.fst himm
  obtain ⟨e, he, hθ⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage Q.fst himm hPalg
  refine ⟨⟨(CatFiberedInGroupoids.homFunctor Q.fst.hom).essImage, inferInstance, hPalg,
    AlgebraicStacks.isOpenImmersion_essImageInclusion Q.fst ⟨hrepr, hoi⟩ himm hPalg⟩,
    e, fun x => ?_, he, hθ⟩
  constructor
  · rintro ⟨z, ⟨e'⟩⟩
    exact W.property.prop_of_iso
      (z.iso.symm ≪≫ g.hom.hom.toFunctor.mapIso e') z.y.property
  · intro hxW
    exact ⟨{ base := 𝒳'.val.val.p.obj x
             x := x
             y := ⟨g.hom.hom.toFunctor.obj x, hxW⟩
             hx := rfl
             hy := g.hom.hom.w_obj x
             iso := Iso.refl _
             vertical := IsHomLift.id (g.hom.hom.w_obj x) }, ⟨Iso.refl _⟩⟩

/-- **Stacks 06M3, assertion (B), the containment `g'^{-1}𝒳' ⊆ 𝒳''`.** Let `Q` be a 2-fibre
product square over the cospan `(g, f)`, so that `Q.fst` is the base change of
`f : 𝒳 ⟶ 𝒴` along `g : 𝒵 ⟶ 𝒴` and `Q.snd` is the projection to `𝒳`. Let `W` be the `P`-locus
of `f` and `W'` the `P`-locus of `Q.fst`. Then every object of the apex carried by `Q.snd` into
`W` lies in `W'`.

This is one of the two containments assertion (B) asserts, and it holds for an **arbitrary** base
change: the property `R` of the source is not used, nor is `Q`. The inverse image of `W` along
`Q.snd` is the 2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒳 W`, which by pasting (**Stacks 003Q**) is also
`W ×_𝒴 𝒵`, so its projection to `𝒵` is a base change of `f|_W` and has `P` by **Stacks 045C**;
maximality of `W'` finishes.

The reverse containment, which is where the hypotheses on `R` enter, is
`AlgebraicGeometry.Stack.isRelativePropertyLocus_baseChange_apply_symm`, and the two together are
assertion (B) of
`AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_and_isRelativePropertyLocus_baseChange`,
both in `StacksFrontier/AlgebraicGeometry/Stacks/RelativePropertyLocusOnSpaces.lean`. -/
theorem isRelativePropertyLocus_baseChange_apply
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴}
    {hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom}
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    {hfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom}
    {W : OpenSubstack 𝒳} {W' : OpenSubstack Q.pt}
    (hW : IsRelativePropertyLocus B S hS P f hf W)
    (hW' : IsRelativePropertyLocus B S hS P Q.fst hfst W')
    {x : Q.pt.val.val.obj} (hx : W.property (Q.snd.hom.hom.toFunctor.obj x)) :
    W'.property x := by
  obtain ⟨V, e, hprop, he, ⟨θ⟩⟩ := exists_openSubstack_comap_isEquivalence B S hS Q.snd W
  have hpaste : Bicategory.IsTwoFibreProduct
      (Q.pasteSnd (twoFibreProductSquareAlgebraicStacks B S hS Q.snd
        (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic))) :=
    Bicategory.isTwoFibreProduct_pasteSnd Q hQ _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS Q.snd _)
  -- the restriction of the base change to `𝒵 ×_𝒴 W` is a base change of `f|_W`, so it has `P`
  have hbc := hasRelativeProperty_baseChange_algebraicStacks B S hS P
    (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f) g _ hpaste
    (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS f hf W)
    (isRepresentableByAlgebraicSpaces_comp B S hS _ Q.fst.hom
      (isRepresentableByAlgebraicSpaces_and_isOpenImmersion_twoFibreProductSquare B S hS Q.snd W).1
 hfst) hW.1
  -- transport it along the equivalence of `(𝒵 ×_𝒴 𝒳) ×_𝒳 W` with `V`
  have hae : Functor.IsEquivalence e.hom.hom.toFunctor := he
  have hbe : Functor.IsEquivalence (BasedFunctor.id 𝒵.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒵.val.val.obj))
  refine hW'.2 V ?_ x ((hprop x).2 hx)
  exact relativeProperty_of_equivalences_symm B S hS P _
    (fullSubcategoryInclusion Q.pt V.property V.isAlgebraic ≫ Q.fst).hom.hom e.hom.hom
    (BasedFunctor.id 𝒵.val.val)
    (Bicategory.InducedBicategory.isoHom (Bicategory.InducedBicategory.isoHom
      ((Bicategory.associator e (fullSubcategoryInclusion Q.pt V.property V.isAlgebraic)
          Q.fst).symm ≪≫ Bicategory.whiskerRightIso θ Q.fst))) hbc

end AlgebraicGeometry.Stack

end
