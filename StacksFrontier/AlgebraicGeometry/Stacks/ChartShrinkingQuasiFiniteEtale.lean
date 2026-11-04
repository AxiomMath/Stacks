module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Shrinking a chart to a quasi-finite or étale neighbourhood (Stacks 06ME and 06N2)

Both lemmas of this file have the same shape. An algebraic space `U` carries a 1-morphism
`f : U ⟶ 𝒳` to an algebraic stack, a field-valued point `g : Spec k ⟶ 𝒳` is given, and `F` is
the 2-fibre product `U ×_𝒳 Spec k` with first projection `p : F ⟶ U`. A point `z ∈ |F|` is
given at which the fibre `F` is small over `Spec k`; the conclusion is that after replacing `U`
by an open subspace containing `p(z)`, the 1-morphism `U ⟶ 𝒳` has the corresponding property.

* **Stacks 06ME.** `U ⟶ 𝒳` locally of finite type and `dim_z(F) = 0` give `U ⟶ 𝒳` locally
  quasi-finite.
* **Stacks 06N2.** `U ⟶ 𝒳` flat and locally of finite presentation and `F ⟶ Spec k` unramified
  at `z` give `U ⟶ 𝒳` étale.

These are two of the lemmas the proofs of **Stacks 06MF** and **Stacks 06N3** run through; see
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`, which carries those
theorems' substantial directions as hypotheses and names these two lemmas among the reasons.

## What is proved and what is carried

The mathematical content of both lemmas is **Stacks 06M5** (Properties of Stacks,
Remark `remark-local-source-apply`): for a property `P` which is smooth local on the source and
a 1-morphism `f : 𝒰 ⟶ 𝒳`, there is a *maximal open substack* `W(f) ⊆ 𝒰` on which `f` has `P`,
and the formation of `W(f)` commutes with arbitrary base change by a 1-morphism representable by
algebraic spaces. Given that, both proofs are the same two lines: the conclusion is `p(z) ∈
W(f)`, and base-change compatibility reduces that to the hypothesis on the fibre at `z`.

**Stacks 06M5 is carried nowhere in this library** — the audit lists it and its companion
**Stacks 06M4** as gaps with no intended declaration, and a direct search confirms there is no
maximal-open-locus construction for a 1-morphism of algebraic stacks at all. What the library
does have is the analogous construction one level down, for morphisms of *schemes*
(**Stacks 0CEY**, `AlgebraicGeometry.largestOpen`) and the target-side version for *algebraic
spaces* (**Stacks 06R2**, `AlgebraicGeometry.Space.largestOpenSubspace`), neither of which
applies to a 1-morphism into a stack.

Accordingly, each lemma below takes the two clauses of Stacks 06M5 as explicit arguments: the
locus itself as the data `W` together with the hypothesis `hW` that the 1-morphism has the
property on it, and its compatibility with the base change along the given field-valued point as
the hypothesis `hBaseChange`. Nothing stronger is assumed — in particular the maximality of `W`
among open substacks with the property is *not* assumed, since the proofs do not need it; only
the base-change inclusion is used. Everything after that is proved.

Stacks 06N2 carries one further input, `hFibreEtale`: the step from the source's pointwise
unramifiedness to étaleness of the fibre near `z`, which is **Stacks 06LU**. The library has
Stacks 06LU for morphisms of algebraic spaces,
`AlgebraicGeometry.Space.isEtale_of_isFlat_of_isUnramified`, but not for 1-morphisms of algebraic
stacks, which is the form the fibre `F ⟶ Spec k` is recorded in here.

## Faithfulness of the two fibre hypotheses

The source's fibre hypotheses are pointwise, and this library has no pointwise notion for a
1-morphism of algebraic stacks. Each is therefore rendered as the corresponding *neighbourhood*
statement, which is equivalent, not weaker:

* `dim_z(F) = 0` is rendered as: some open substack of `F` containing `z` has locally
  quasi-finite structure 1-morphism to `Spec k`. For a morphism locally of finite type these are
  equivalent by **Stacks 04NV** (Morphisms of Spaces,
  `lemma-locally-quasi-finite-rel-dimension-0`) together with the openness of the
  relative-dimension-zero locus, **Stacks 04NW** — both of which the library has, as
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_relativeDimensionZeroLocus` and
  `AlgebraicGeometry.Space.isOpenSubspace_relativeDimensionZeroLocus`.
* `F ⟶ Spec k` *unramified at* `z` is rendered as: some open substack of `F` containing `z` has
  unramified structure 1-morphism to `Spec k`. These are equivalent because the unramified locus
  is open, **Stacks 05W2**, which the library has as
  `AlgebraicGeometry.Space.isOpen_setOf_isUnramifiedAt`.

Both renderings say "the fibre is small on a neighbourhood of `z`", which is exactly what the
source's proofs use of the pointwise hypotheses — each of them reduces the pointwise condition to
membership in an open locus immediately.

## Main definitions

* `AlgebraicGeometry.Stack.OpenSubstack.inclusion`,
  `AlgebraicGeometry.Stack.OpenSubstack.pointSet`: the inclusion of an open substack and the set
  of points lying in it.
* `AlgebraicGeometry.Stack.fibreOverFieldPoint`,
  `AlgebraicGeometry.Stack.fibreProjection`,
  `AlgebraicGeometry.Stack.fibreStructureMorphism`: the `F`, `p` and `q` of the source's
  cartesian diagram.
* `AlgebraicGeometry.Stack.FibreIsLocallyQuasiFiniteNear`,
  `AlgebraicGeometry.Stack.FibreIsUnramifiedNear`: the two fibre hypotheses.

## Main results

* `AlgebraicGeometry.Stack.exists_openSubstack_isLocallyQuasiFinite`: **Stacks 06ME**.
* `AlgebraicGeometry.Stack.exists_openSubstack_isEtale`: **Stacks 06N2**.

## Implementation notes

An algebraic space is read as an algebraic stack by
`AlgebraicGeometry.Stack.algebraicSpaceStack`, and the field-valued point of the target is
spelled exactly as `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`
(**Stacks 06PU**) spells it, as a 1-morphism out of
`AlgebraicGeometry.Stack.schemeStack` of the site object on `Spec k`.

The 2-fibre product is `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, whose
`fst` leg is the source's `p`. The source treats this 2-fibre product as an algebraic *space*,
which it is: **Stacks 0300**,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`, gives that, once the
representability of one leg is supplied — for an algebraic stack by the implication (1) ⟹ (8) of
**Stacks 045G**, whose chain is proved, ending at
`AlgebraicGeometry.Stack.isRepresentableFromAlgebraicSpaces_iff_hasAlgebraicSpaceProducts`. Its
being a space is used by the source only to speak of `dim_z` and of the étale local ring, and
neither lemma below needs it to be stated, so it is recorded here as a remark rather than
asserted; it is what a proof of the carried **Stacks 06M5** inputs would go through.

"An open subspace containing `p(z)`" is spelled as an
`AlgebraicGeometry.Stack.OpenSubstack` of the stack of `U` whose inclusion has `p(z)` in the
range of its map on points. The library's `OpenSubstack` has no points-level membership
predicate, so membership is phrased through `Set.range` of the inclusion's map on points, which
needs no missing API.

Local quasi-finiteness is `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite`
(**Stacks 06PU**), the stack-level notion for an arbitrary 1-morphism, not the Section 04XB
relative notion of the same name — the source's conclusion is about `U ⟶ 𝒳` as an arbitrary
1-morphism, not as a representable one. Étaleness is
`AlgebraicGeometry.Stack.IsEtale` (**Stacks 0CIL**) and unramifiedness
`AlgebraicGeometry.Stack.IsUnramified` (**Stacks 0CIT**).

## References

* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 05W2](https://stacks.math.columbia.edu/tag/05W2)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 0CIL](https://stacks.math.columbia.edu/tag/0CIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open substacks and their points -/

/-- The 1-morphism including an open substack of an algebraic stack. -/
abbrev OpenSubstack.inclusion {𝒰 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒰) :
    fullSubcategoryAlgebraicStack 𝒰 W.property W.isAlgebraic ⟶ 𝒰 :=
  fullSubcategoryInclusion 𝒰 W.property W.isAlgebraic

/-- The set of points of an algebraic stack lying in an open substack: the range of the map on
points of its inclusion.

`AlgebraicGeometry.Stack.OpenSubstack` carries no points-level membership predicate, and the
library has no analogue for substacks of the order isomorphism it has for open subspaces of an
algebraic space, so the range of the inclusion's map on points is what stands for `|W| ⊆ |𝒰|`. -/
abbrev OpenSubstack.pointSet {𝒰 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒰) :
    Set (AlgebraicStacks.points B S hS 𝒰) :=
  Set.range (AlgebraicStacks.pointsMap B S hS W.inclusion)

/-! ### The fibre hypotheses -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)

/-- The site object on `Spec k` over `S`, as `Stacks 06PU` spells it. -/
abbrev fieldPointObject : BigFppfOver B S hS :=
  Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

/-- The 2-fibre product `F = U ×_𝒳 Spec k` of the source's cartesian diagram. -/
abbrev fibreOverFieldPoint : AlgebraicStacks.{u, w} B S hS :=
  (twoFibreProductSquareAlgebraicStacks B S hS f g).pt

/-- The projection `p : F ⟶ U` of the source's cartesian diagram. -/
abbrev fibreProjection : fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g ⟶
    algebraicSpaceStack.{u, w} B S hS U hU :=
  (twoFibreProductSquareAlgebraicStacks B S hS f g).fst

/-- The structure 1-morphism `F ⟶ Spec k` of the source's cartesian diagram. -/
abbrev fibreStructureMorphism : fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g ⟶
    schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) :=
  (twoFibreProductSquareAlgebraicStacks B S hS f g).snd

/-- **The fibre hypothesis of Stacks 06ME:** `dim_z(F) = 0`, rendered as the equivalent
neighbourhood statement that some open substack of `F` containing `z` is locally quasi-finite
over `Spec k`.

For a morphism locally of finite type the two are equivalent by **Stacks 04NV** together with
the openness of the relative-dimension-zero locus, **Stacks 04NW**. -/
abbrev FibreIsLocallyQuasiFiniteNear
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g)) :
    Prop :=
  ∃ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
    z ∈ V.pointSet B S hS ∧
      AlgebraicStacks.IsLocallyQuasiFinite B S hS
        (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)

/-- **The fibre hypothesis of Stacks 06N2:** `F ⟶ Spec k` is unramified at `z`, rendered as the
equivalent neighbourhood statement that some open substack of `F` containing `z` is unramified
over `Spec k`.

The two are equivalent because the unramified locus is open, **Stacks 05W2**. -/
abbrev FibreIsUnramifiedNear
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g)) :
    Prop :=
  ∃ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
    z ∈ V.pointSet B S hS ∧
      IsUnramified B S hS
        (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)

/-! ### Stacks 06ME and Stacks 06N2 -/

/-- **Stacks 06ME.** Let `𝒳` be an algebraic stack, let `U` be an algebraic space with a
1-morphism `f : U ⟶ 𝒳` which is locally of finite type, let `Spec k ⟶ 𝒳` be a field-valued
point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U` and structure 1-morphism
`q : F ⟶ Spec k`. If `z ∈ |F|` has `dim_z(F) = 0` then, after replacing `U` by an open subspace
containing `p(z)`, the 1-morphism `U ⟶ 𝒳` is locally quasi-finite.

The proof is the source's. The open substack `W` is the locus `W(f)` of **Stacks 06M5** on which
`f` is locally quasi-finite, carried as the data `W` together with `hW`; the compatibility of
that locus with the base change along `g`, which is the second clause of Stacks 06M5, is carried
as `hBaseChange`. Given those, the conclusion is exactly that `p(z) ∈ |W|`, and that follows
because the fibre hypothesis puts `z` in an open substack of `F` which is locally quasi-finite
over `Spec k`, hence inside the preimage of `|W|`. -/
@[stacks 06ME "after replacing the algebraic space by an open subspace containing the image of \
the given point of the fibre, a 1-morphism locally of finite type whose fibre over a \
field-valued point has dimension zero at that point is locally quasi-finite. The two clauses of \
Stacks 06M5 are carried, as the data `W` with `hW` (the open locus on which the 1-morphism is \
locally quasi-finite) and the hypothesis `hBaseChange` (that locus commutes with the base change \
along the field-valued point), since Stacks 06M5 is absent from this library; the deduction of \
the conclusion from them is proved"]
theorem exists_openSubstack_isLocallyQuasiFinite
    (_hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS U hU))
    (hW : AlgebraicStacks.IsLocallyQuasiFinite B S hS (W.inclusion ≫ f))
    (hBaseChange : ∀ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
      AlgebraicStacks.IsLocallyQuasiFinite B S hS
          (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) →
        V.pointSet B S hS ⊆
          AlgebraicStacks.pointsMap B S hS
              (fibreProjection B S hS 𝒳 U hU k hk toBase f g) ⁻¹' W.pointSet B S hS)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsLocallyQuasiFiniteNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    AlgebraicStacks.pointsMap B S hS
        (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈ W.pointSet B S hS ∧
      AlgebraicStacks.IsLocallyQuasiFinite B S hS (W.inclusion ≫ f) := by
  obtain ⟨V, hzV, hVqf⟩ := hz
  exact ⟨hBaseChange V hVqf hzV, hW⟩

/-- **Stacks 06N2.** Let `𝒳` be an algebraic stack, let `U` be an algebraic space with a
1-morphism `f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U` and structure
1-morphism `q : F ⟶ Spec k`. If `q` is unramified at `z ∈ |F|` then, after replacing `U` by an
open subspace containing `p(z)`, the 1-morphism `U ⟶ 𝒳` is étale.

The proof is the source's. The open substack `W` is the locus `W(f)` of **Stacks 06M5** on which
`f` is étale, carried as the data `W` with `hW`, and its compatibility with the base change along
`g` is carried as `hBaseChange`. The step from the source's pointwise hypothesis to étaleness of
the fibre near `z` is **Stacks 06LU** — unramified plus flat plus locally of finite presentation
gives étale — which the library has for morphisms of algebraic spaces
(`AlgebraicGeometry.Space.isEtale_of_isFlat_of_isUnramified`) but not for 1-morphisms of
algebraic stacks; it is carried as `hFibreEtale`, stated over `Spec k`, which is where the source
applies it. Given those, the conclusion is that `p(z) ∈ |W|`. -/
@[stacks 06N2 "after replacing the algebraic space by an open subspace containing the image of \
the given point of the fibre, a flat, locally finitely presented 1-morphism whose fibre over a \
field-valued point is unramified at that point is etale. Three inputs are carried: the data `W` \
with `hW` and the hypothesis `hBaseChange`, which are the two clauses of Stacks 06M5 at \
etaleness, absent from this library; and `hFibreEtale`, which is Stacks 06LU for 1-morphisms of \
algebraic stacks over the field-valued point, available in this library only for morphisms of \
algebraic spaces. The deduction of the conclusion from them is proved"]
theorem exists_openSubstack_isEtale
    (_hflat : AlgebraicStacks.IsFlat B S hS f)
    (_hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (W : OpenSubstack (algebraicSpaceStack.{u, w} B S hS U hU))
    (hW : IsEtale B S hS (W.inclusion ≫ f))
    (hFibreEtale : ∀ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
      IsUnramified B S hS
          (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) →
        IsEtale B S hS
          (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g))
    (hBaseChange : ∀ V : OpenSubstack (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g),
      IsEtale B S hS
          (V.inclusion ≫ fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g) →
        V.pointSet B S hS ⊆
          AlgebraicStacks.pointsMap B S hS
              (fibreProjection B S hS 𝒳 U hU k hk toBase f g) ⁻¹' W.pointSet B S hS)
    (z : AlgebraicStacks.points B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g))
    (hz : FibreIsUnramifiedNear.{u, w} B S hS 𝒳 U hU k hk toBase f g z) :
    AlgebraicStacks.pointsMap B S hS
        (fibreProjection B S hS 𝒳 U hU k hk toBase f g) z ∈ W.pointSet B S hS ∧
      IsEtale B S hS (W.inclusion ≫ f) := by
  obtain ⟨V, hzV, hVunr⟩ := hz
  exact ⟨hBaseChange V (hFibreEtale V hVunr) hzV, hW⟩

end AlgebraicGeometry.Stack

end
