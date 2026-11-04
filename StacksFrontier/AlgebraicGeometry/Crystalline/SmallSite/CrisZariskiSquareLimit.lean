module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareCovering
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafComp
public import StacksFrontier.CategoryTheory.Functor.KanExtension.CommaSquare

/-!
# `u_{X/S, *} ∘ f_{cris, *}` as a single limit over the dominating pairs

Let `f : X' ⟶ X` be a morphism of the global crystalline situations of [Stacks, Tag 07I5].  The
square of topoi of [Stacks, Tag 07Q9] asks for

`u_{X/S, *} ∘ f_{cris, *} ≅ f_{Zar, *} ∘ u_{X'/S, *}`,

and the right-hand side is, on underlying presheaves, a single right Kan extension read at
`f^{-1}V`.  The left-hand side is *three* nested ones, because `f_{cris, *}` is the composite
`π_{X', *} ∘ f_{CRIS, *} ∘ i_{X, *}` of [Stacks, Tag 07IK].  **This file flattens them into one.**

Write `K : Cris(X'/S) ⥤ CRIS(X/S)` for the inclusion followed by change of divided power base
(`crisToBig` below).  Then the presheaf underlying `u_{X/S, *}f_{cris, *}ℋ` is, by the three
definitions and with no argument at all,

`Ran_{u_X} (i_X^{-1} (Ran_{f_CRIS} (Ran_{i_{X'}} ℋ)))`.

The two adjacent right Kan extensions collapse into `Ran_K` because right Kan extension along a
composite is the composite of the right Kan extensions
(`CategoryTheory.Functor.ranCompIsoOfAdjunctions`).  What blocks further collapsing is the
restriction `i_X^{-1}` between `Ran_K` and `Ran_{u_X}`: a restriction is *not* a right Kan
extension, and this is exactly the passage from the big crystalline site to the small one.  It is
removed by the general fact that a comma square is Guitart exact,
`CategoryTheory.TwoSquare.ranCommaIso` of
`StacksFrontier/CategoryTheory/Functor/KanExtension/CommaSquare.lean`: restriction along `i_X` after
`Ran_K` is right Kan extension along the first projection of the comma category of `i_X` and `K`,
of the restriction along the second projection.  That comma category is the category of
**dominating pairs** `(A, A', k)` — an object `A` of `Cris(X/S)`, an object `A'` of `Cris(X'/S)`,
and a morphism `K A' ⟶ i_X A` of `CRIS(X/S)` — and one more use of `ranCompIsoOfAdjunctions`
leaves a single right Kan extension along `(A, A', k) ↦ U_A`.

So the sections of `u_{X/S, *}f_{cris, *}ℋ` over an open `V` of `X` are the limit of `ℋ(A')` over
the dominating pairs with `U_A ⊆ V`, naturally in `V` and in `ℋ`; and the canonical `2`-cell of
the square of [Stacks, Tag 07Q9] becomes a `CategoryTheory.Limits.limit.pre` along the projection
`(A, A', k) ↦ A'`.  That is the first of the three steps that separate
`SmallSite/CrisZariskiSquareCovering.lean` from a term of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrisZariskiSquare`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisToBig` — the functor `K : Cris(X'/S) ⥤ CRIS(X/S)`, the inclusion of the small crystalline
  site of `X'/S` followed by change of divided power base along `f`.
* `DominationPairs` — the category of dominating pairs, as the opposite-side comma category of
  `i_X` and `K`.
* `dominationToOpens` — the functor `(A, A', k) ↦ U_A` of a dominating pair to the opens of `X`,
  opposed.
* `dominationRan` — the functor sending an abelian sheaf `ℋ` on `Cris(X'/S)` to the right Kan
  extension along `dominationToOpens` of `(A, A', k) ↦ ℋ(A')`, i.e. to the presheaf on `X_Zar`
  whose sections over `V` are the limit of `ℋ(A')` over the dominating pairs with `U_A ⊆ V`.
* `smallDominatedSieve` — the sieve on an object of `Cris(X'/S)` of those refinements which, after
  change of divided power base, map to an object of `Cris(X/S)` lying over a prescribed open `V`
  of `X`; the small-site form of
  `Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve`.
* `dominationStructuredArrow` — the index of the limit over the dominating pairs attached to a
  domination of an object of `Cris(X'/S)` by an object of `Cris(X/S)` lying over `V`.

## Main results

* `crisZariskiLeftRanIso` — **the flattening**: the presheaf-level composite
  `Ran_{u_X} ∘ i_X^{-1} ∘ Ran_{f_CRIS} ∘ Ran_{i_{X'}}` is `dominationRan`.
* `crisZariskiLeftIsoCoeff` — the same read on sheaves: the presheaf underlying
  `u_{X/S, *}f_{cris, *}ℋ` is `dominationRan ℋ`, naturally in `ℋ`.
* `crisZariskiLeftObjIsoCoeff` — and pointwise: the sections over an open `V` of `X` are the
  limit of `ℋ(A')` over the dominating pairs with `U_A ⊆ V`.
* `smallDominatedSieve_mem` — **the relative covering step of [Stacks, Tag 07Q9] in the small
  crystalline site**: the dominated refinements of an object lying over `f^{-1}V` cover it.  It is
  the big-site `dominatedSieve_mem` pulled back along the cocontinuous inclusion
  `i_{X'}`, and it is the covering sieve the two remaining sheaf-theoretic steps are applied to.

## What is and is not proved

No tag attribute is placed here: [Stacks, Tag 07Q9] is
`Crystalline.GlobalCrystallineSituation.SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
`SmallSite/AlphaPCover07Q9Main.lean`, and this file supplies one step of the commutation of the
square of topoi its comparison map is built on.  What is proved here is the
limit plumbing: one side of the square of topoi is identified with a single limit.  The two
sheaf-theoretic steps that remain after this file — separatedness of an abelian sheaf at a
covering sieve of an object, and amalgamation of a compatible family over that sieve, the
covering being
`Crystalline.GlobalCrystallineSituation.SmallSite.smallDominatedSieve_mem` — are done in
`SmallSite/CrisZariskiSquareIso.lean`, which does construct the commutation
`Crystalline.GlobalCrystallineSituation.SmallSite.CrisZariskiSquare`.  Both steps turned out to
be in Mathlib, for a sheaf at an arbitrary object rather than only at the final one:
`CategoryTheory.Presheaf.IsSheaf.hom_ext` and
`CategoryTheory.Presheaf.IsSheaf.amalgamate`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- **The functor `K : Cris(X'/S) ⥤ CRIS(X/S)`** reading an object of the small crystalline site
of the source situation as an object of the big crystalline site of the target: include it into
`CRIS(X'/S)` and change divided power base along `f`.  Its two factors are the two cocontinuous
stages of `f_{cris, *}`, and the two right Kan extensions along them collapse into one along
`K`. -/
def crisToBig : CrystallineThickening S ⥤ Thickening S' :=
  CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf

/-- **`K` opposed.** -/
abbrev crisToBigOp : (CrystallineThickening S)ᵒᵖ ⥤ (Thickening S')ᵒᵖ :=
  (CrystallineThickening.ι S).op ⋙ (changeBase S S' fS fX hf).op

/-- `crisToBigOp` is the opposite of `crisToBig`; it is written as the composite of the two
opposites so that the right Kan extension along it is literally the composite of the two right
Kan extensions. -/
theorem crisToBigOp_eq : crisToBigOp S S' fS fX hf = (crisToBig S S' fS fX hf).op :=
  rfl

/-- **The category of dominating pairs.**  An object is an object `A` of `Cris(X/S)`, an object
`A'` of `Cris(X'/S)` and a morphism `K A' ⟶ i_X A` of `CRIS(X/S)` — that is, a domination of `A'`
by `A` after change of divided power base.  These are the indices of the limit computing
`u_{X/S, *}f_{cris, *}ℋ`.

It is realized as Mathlib's comma category of the opposites of `i_X` and `K`, so that its first
projection lands in `Cris(X/S)` opposed and its second in `Cris(X'/S)` opposed, and the
tautological `2`-cell of that comma square is the domination morphism itself. -/
abbrev DominationPairs : Type (u + 1) :=
  Comma (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)

/-- **The open of `X` a dominating pair lies over**, opposed: the pair `(A, A', k)` goes to the
open image of the structure map of `A`.  The right Kan extension along this functor is the
left-hand side of the square of [Stacks, Tag 07Q9]. -/
abbrev dominationToOpens :
    DominationPairs S S' fS fX hf ⥤ (S'.X.Opens)ᵒᵖ :=
  Comma.fst (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙
    (forgetToOpens S').op

/-! ### The two sides, at arbitrary coefficients

Nothing in the comparison below is about abelian groups.  Both sides are right Kan extensions, and
inverting the `2`-cell between them uses only the sheaf condition, so the whole of this file and of
`SmallSite/CrisZariskiSquareIso.lean` is carried out at a coefficient category `E` with the limits
that compute those Kan extensions.  Two coefficient categories are used: `AddCommGrpCat.{u + 1}`,
where the square is the one the chapter's cohomology needs, and `Type (u + 1)`, where it is the
square of *topoi* — the upper square of the diagram of [Stacks, Tag 07IM] when `f` is the structure
morphism `X ⟶ S₀`, which is what
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/UpperSquare.lean` reads off. -/

variable (E : Type (u + 2)) [Category.{u + 1} E] [HasLimitsOfSize.{u, u + 1} E]

/-- The right Kan extensions along the first projection of the category of dominating pairs exist
at any coefficients with limits of the relevant size: they are limits indexed by structured arrow
categories whose objects form a `Type (u + 1)` and whose morphisms a `Type u`. -/
instance instHasPointwiseRightKanExtensionCommaFst
    (F : DominationPairs S S' fS fX hf ⥤ E) :
    (Comma.fst (CrystallineThickening.ι S').op
      (crisToBigOp S S' fS fX hf)).HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- The right Kan extensions along `K` opposed exist at any coefficients with limits of the
relevant size. -/
instance instHasPointwiseRightKanExtensionCrisToBig
    (F : (CrystallineThickening S)ᵒᵖ ⥤ E) :
    (crisToBigOp S S' fS fX hf).HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- The right Kan extensions along `(A, A', k) ↦ U_A` exist at any coefficients with limits of the
relevant size; these are the limits the two sides of the square are compared as. -/
instance instHasPointwiseRightKanExtensionDominationToOpens
    (F : DominationPairs S S' fS fX hf ⥤ E) :
    (dominationToOpens S S' fS fX hf).HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- **The limit over the dominating pairs, as a functor of the coefficient presheaf.**  It sends
`ℋ` to the presheaf on the small Zariski site of `X` whose sections over an open `V` are the limit
of `ℋ(A')` over the dominating pairs `(A, A', k)` with `U_A ⊆ V`. -/
def dominationRan :
    ((CrystallineThickening S)ᵒᵖ ⥤ E) ⥤ ((S'.X.Opens)ᵒᵖ ⥤ E) :=
  (Functor.whiskeringLeft _ _ E).obj
      (Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf)) ⋙
    (dominationToOpens S S' fS fX hf).ran

/-- **The flattening of the three nested right Kan extensions computing `u_{X/S, *}f_{cris, *}`
into a single one over the dominating pairs.**

The two adjacent ones — along the inclusion `i_{X'}` and along change of divided power base —
collapse by `CategoryTheory.Functor.ranCompIsoOfAdjunctions` into the right Kan extension along
`K = crisToBig`.  The restriction `i_X^{-1}` which then separates it from the right Kan extension
along `u_X` is removed by `CategoryTheory.TwoSquare.ranCommaIso`, the comma square being Guitart
exact: that produces the right Kan extension along the first projection of the dominating pairs,
of the restriction along the second.  A second use of `ranCompIsoOfAdjunctions` merges it with the
one along `u_X`. -/
def crisZariskiLeftRanIso :
    (CrystallineThickening.ι S).op.ran ⋙ (changeBase S S' fS fX hf).op.ran ⋙
        (Functor.whiskeringLeft _ _ E).obj
          (CrystallineThickening.ι S').op ⋙
        (forgetToOpens S').op.ran ≅
      dominationRan S S' fS fX hf E :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.ranCompIsoOfAdjunctions E (CrystallineThickening.ι S).op
        (changeBase S S' fS fX hf).op).symm _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (TwoSquare.ranCommaIso (H := E) (CrystallineThickening.ι S').op
        (crisToBigOp S S' fS fX hf)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.ranCompIsoOfAdjunctions E
        (Comma.fst (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf))
        (forgetToOpens S').op).symm

/-- **The presheaf underlying `u_{X/S, *}f_{cris, *}ℋ` is the limit over the dominating pairs**,
naturally in the sheaf `ℋ` on `Cris(X'/S)`.

Both of the two sheaf-level stages that are pushforwards along cocontinuous functors of sites are
right Kan extensions on underlying presheaves on the nose, and so is the one along `u_{X/S}`,
while restriction to the small crystalline site is restriction on the nose; so the underlying
presheaf of the composite *is* the left-hand side of `crisZariskiLeftRanIso`. -/
def crisZariskiLeftIsoCoeff :
    crisDirectImageCoeff S S' fS fX hf E ⋙ zariskiDirectImageCoeff S' E ⋙
        sheafToPresheaf (opensTopology S') E ≅
      sheafToPresheaf (smallTopology S) E ⋙ dominationRan S S' fS fX hf E :=
  Functor.isoWhiskerLeft _ (crisZariskiLeftRanIso S S' fS fX hf E)

/-- **The sections of `u_{X/S, *}f_{cris, *}ℋ` over an open `V` of `X` are the limit of `ℋ(A')`
over the dominating pairs `(A, A', k)` with `U_A ⊆ V`.**  This is `crisZariskiLeftIsoCoeff` read at
`V`, through the pointwise formula for a right Kan extension. -/
def crisZariskiLeftObjIsoCoeff (G : Sheaf (smallTopology S) E)
    (V : S'.X.Opens) :
    ((zariskiDirectImageCoeff S' E).obj
        ((crisDirectImageCoeff S S' fS fX hf E).obj G)).obj.obj (op V) ≅
      limit (StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
        Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) :=
  ((crisZariskiLeftIsoCoeff S S' fS fX hf E).app G).app (op V) ≪≫
    (dominationToOpens S S' fS fX hf).ranObjObjIsoLimit _ (op V)

/-- `crisZariskiLeftIsoCoeff` at the abelian coefficients of this chapter, phrased with the
chapter's own `f_{cris, *}` and `u_{X/S, *}`. -/
def crisZariskiLeftIso :
    crisDirectImage S S' fS fX hf ⋙ zariskiDirectImage S' ⋙
        sheafToPresheaf (opensTopology S') AddCommGrpCat.{u + 1} ≅
      sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        dominationRan S S' fS fX hf AddCommGrpCat.{u + 1} :=
  crisZariskiLeftIsoCoeff S S' fS fX hf AddCommGrpCat.{u + 1}

/-- `crisZariskiLeftObjIsoCoeff` at the abelian coefficients of this chapter, phrased with the
chapter's own `f_{cris, *}` and `u_{X/S, *}`. -/
def crisZariskiLeftObjIso (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (V : S'.X.Opens) :
    ((zariskiDirectImage S').obj ((crisDirectImage S S' fS fX hf).obj G)).obj.obj (op V) ≅
      limit (StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
        Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) ⋙ G.obj) :=
  crisZariskiLeftObjIsoCoeff S S' fS fX hf AddCommGrpCat.{u + 1} G V

/-! ### The covering of the small crystalline site by the dominated objects -/

/-- **The sieve of refinements of an object of `Cris(X'/S)` dominated by an object of `Cris(X/S)`
lying over `V`**, the small-site form of
`Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve`.  A morphism `C ⟶ A` of
`Cris(X'/S)` belongs to it when `C`, read over `X/S` through `K = crisToBig`, admits a morphism to
an object of `Cris(X/S)` whose structure map has image inside the open `V` of `X`.

These are exactly the objects `A'` for which the projection `(A, A', k) ↦ A'` out of the
dominating pairs over `V` has a preimage, so a covering by them is what the comparison of the two
limits of the square of [Stacks, Tag 07Q9] is applied to — the sheaf condition being a statement
about covering sieves of the site the coefficient sheaf lives on, which is the small one. -/
def smallDominatedSieve (V : S'.X.Opens) (A : CrystallineThickening S) : Sieve A where
  arrows C _ := ∃ B : CrystallineThickening S',
    (∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V) ∧
      Nonempty ((crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B)
  downward_closed := fun {_ _ _} h g ↦ by
    obtain ⟨B, hBV, ⟨k⟩⟩ := h
    exact ⟨B, hBV, ⟨(crisToBig S S' fS fX hf).map g ≫ k⟩⟩

/-- `smallDominatedSieve` is the pullback of `dominatedSieve` along the inclusion of the small
crystalline site: an arrow of `Cris(X'/S)` is dominated exactly when its image in `CRIS(X'/S)`
is, the domination condition being about `K = i_{X'} ⋙ f_CRIS` on both sides. -/
theorem smallDominatedSieve_eq_functorPullback (V : S'.X.Opens) (A : CrystallineThickening S) :
    smallDominatedSieve S S' fS fX hf V A =
      Sieve.functorPullback (CrystallineThickening.ι S)
        (dominatedSieve S S' fS fX hf V ((CrystallineThickening.ι S).obj A)) :=
  rfl

/-- **The relative covering step of [Stacks, Tag 07Q9] in the small crystalline site.**  Let `V`
be an open of `X` and let `A` be an object of `Cris(X'/S)` whose structure map lands, after
composition with `f`, inside `V`.  Then the refinements of `A` which are dominated by an object of
`Cris(X/S)` lying over `V` form a covering sieve of `A` *in the small crystalline site*.

This is the big-site statement
`Crystalline.GlobalCrystallineSituation.SmallSite.dominatedSieve_mem` pulled back along the
inclusion `i_{X'} : Cris(X'/S) ⥤ CRIS(X'/S)`, which is cocontinuous — that is exactly what makes
`i_{X', *}` a right Kan extension — so the pullback of a covering sieve is covering. -/
theorem smallDominatedSieve_mem (V : S'.X.Opens) (A : CrystallineThickening S)
    (hA : ∀ z : A.obj.thickening.source, fX.base (A.obj.toX.base z) ∈ V) :
    smallDominatedSieve S S' fS fX hf V A ∈ smallTopology S A :=
  (CrystallineThickening.ι S).cover_lift (smallTopology S) (topology S)
    (dominatedSieve_mem S S' fS fX hf V ((CrystallineThickening.ι S).obj A) hA)

/-- **The dominating pair attached to an arrow of `smallDominatedSieve`, as an index of the limit
computing `u_{X/S, *}f_{cris, *}ℋ` over an open `V`.**  A domination of `C` by an object `B` of
`Cris(X/S)` lying over `V` is an object of `DominationPairs` whose open of `X` is contained in
`V`, i.e. an object of the structured arrow category indexing that limit. -/
def dominationStructuredArrow (V : S'.X.Opens) (C : CrystallineThickening S)
    (B : CrystallineThickening S')
    (hB : ∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V)
    (k : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B) :
    StructuredArrow (op V) (dominationToOpens S S' fS fX hf) :=
  StructuredArrow.mk (Y := ⟨op B, op C, k.op⟩)
    (homOfLE (by rintro _ ⟨z, rfl⟩; exact hB z)).op

/-- The object of `Cris(X'/S)` underlying `dominationStructuredArrow V C B hB k` is `C`. -/
@[simp]
theorem dominationStructuredArrow_right_snd (V : S'.X.Opens) (C : CrystallineThickening S)
    (B : CrystallineThickening S')
    (hB : ∀ z : B.obj.thickening.source, B.obj.toX.base z ∈ V)
    (k : (crisToBig S S' fS fX hf).obj C ⟶ (CrystallineThickening.ι S').obj B) :
    (dominationStructuredArrow S S' fS fX hf V C B hB k).right.right = op C :=
  rfl

/-! ### The canonical `2`-cell of the square, as a comparison of limits -/

/-- **A dominating pair over `V` has its object of `Cris(X'/S)` over `f^{-1}V`.**  A domination
`K A' ⟶ i_X A` factors the structure map of `A'`, read over `X`, through that of `A`, whose image
is inside `V`; and the structure map of `A'` read over `X` is its own followed by `f`,
`Crystalline.GlobalCrystallineSituation.changeBase_obj_toX`. -/
theorem dominationPairs_le_preimage (V : S'.X.Opens)
    (d : StructuredArrow (op V) (dominationToOpens S S' fS fX hf)) :
    (forgetToOpens S).obj d.right.right.unop ≤ fX ⁻¹ᵁ V := by
  rintro _ ⟨z, rfl⟩
  have hB : ∀ y : d.right.left.unop.obj.thickening.source,
      d.right.left.unop.obj.toX.base y ∈ V := fun y ↦
    leOfHom d.hom.unop ⟨y, rfl⟩
  exact Thickening.mem_of_hom d.right.hom.unop V hB z

/-- **The projection of the dominating pairs over `V` to the objects of `Cris(X'/S)` over
`f^{-1}V`**, `(A, A', k) ↦ A'`.  The limits of an abelian sheaf `ℋ` over these two categories are
the two sides of the square of topoi of [Stacks, Tag 07Q9] read at the open `V` of `X`:
`crisZariskiLeftObjIsoCoeff` for the source and
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiDirectImageObjObjIsoLimit` at `f^{-1}V`
for the target, the sections of `f_{Zar, *}` over `V` being those of its argument over `f^{-1}V`
by definition.

Restricting a cone along this projection is the canonical `2`-cell of the square, which runs from
`f_{Zar, *}u_{X'/S, *}` to `u_{X/S, *}f_{cris, *}`; the content of [Stacks, Tag 07Q9] is that it
is invertible. -/
def dominationProj (V : S'.X.Opens) :
    StructuredArrow (op V) (dominationToOpens S S' fS fX hf) ⥤
      StructuredArrow (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op where
  obj d := StructuredArrow.mk (Y := d.right.right)
    (homOfLE (dominationPairs_le_preimage S S' fS fX hf V d)).op
  map φ := StructuredArrow.homMk φ.right.right (Subsingleton.elim _ _)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection of the dominating pairs is compatible with the two diagrams: reading the
coefficient sheaf at the object of `Cris(X'/S)` of a dominating pair is the same whether one
projects first or takes the second component first. -/
theorem dominationProj_comp_proj (V : S'.X.Opens) :
    dominationProj S S' fS fX hf V ⋙ StructuredArrow.proj (op (fX ⁻¹ᵁ V))
        (forgetToOpens S).op =
      StructuredArrow.proj (op V) (dominationToOpens S S' fS fX hf) ⋙
        Comma.snd (CrystallineThickening.ι S').op (crisToBigOp S S' fS fX hf) :=
  rfl

/-- **The canonical `2`-cell of the square of topoi of [Stacks, Tag 07Q9], read at an open `V` of
`X`.**  It is the restriction of cones along `dominationProj`, i.e.
`CategoryTheory.Limits.limit.pre`, transported through the two limit formulas: from the sections
of `f_{Zar, *}u_{X'/S, *}ℋ` over `V` — which are those of `u_{X'/S, *}ℋ` over `f^{-1}V` — to the
sections of `u_{X/S, *}f_{cris, *}ℋ` over `V`.

This is the direction the comparison map of [Stacks, Tag 07Q9] does *not* need; it is the one that
is free, `Crystalline.GlobalCrystallineSituation.SmallSite.HasFreeCrisZariskiCell`.  What
[Stacks, Tag 07Q9] needs is its inverse, and the two steps left for that are separatedness of `ℋ`
at the covering sieve `smallDominatedSieve_mem` and amalgamation of a compatible family over it,
the family being indexed by `dominationStructuredArrow` and compatible by
`Crystalline.GlobalCrystallineSituation.SmallSite.exists_cone_domination`. -/
def crisZariskiCellApp (G : Sheaf (smallTopology S) E) (V : S'.X.Opens) :
    ((zariskiDirectImageCoeff S E).obj G).obj.obj (op (fX ⁻¹ᵁ V)) ⟶
      ((zariskiDirectImageCoeff S' E).obj
        ((crisDirectImageCoeff S S' fS fX hf E).obj G)).obj.obj (op V) :=
  ((forgetToOpens S).op.ranObjObjIsoLimit G.obj (op (fX ⁻¹ᵁ V))).hom ≫
    limit.pre (StructuredArrow.proj (op (fX ⁻¹ᵁ V)) (forgetToOpens S).op ⋙ G.obj)
      (dominationProj S S' fS fX hf V) ≫
    (crisZariskiLeftObjIsoCoeff S S' fS fX hf E G V).inv

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
