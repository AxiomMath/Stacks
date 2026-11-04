module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# The cardinality-restricted polynomial site, and a small model of it

Let `A → B` be a map of commutative rings. The site `C_{B/A}` of Tag 08PR is the opposite of
the category of `A`-algebra maps `α : P → B` with `P` a polynomial algebra over `A`. The source
restricts the sets of variables by a footnote to the section: *"It suffices to consider sets of
cardinality at most the cardinality of `B`."* That restriction is not a theorem about the
unrestricted category — it is part of the definition of `C_{B/A}`, and it is what makes the site
small enough for the criterion of Tag 08Q9, which is proved through the projective generators of
the category of abelian presheaves and therefore needs a small index category.

`CommAlgCat.polynomialSite` carries no such restriction: its objects are objects of
`CommAlgCat.{u} A`, hence live in `Type (u + 1)`, and the iso classes of its objects are indexed
by the cardinals of `Type u`, a `Type (u + 1)`-sized collection. So it is not even essentially
small at `u`. This file implements the footnote, at an arbitrary cardinal bound `κ`:

* the full subcategory of the polynomial augmentations whose set of variables has cardinality at
  most `κ`;
* a *genuinely small* model of it — a category whose type of objects is a `Type u` — namely the
  augmentations `A[S] → B` for `S` a subset of a fixed `Type u` representative of `κ`;
* the resulting essential smallness at `u`.

## Main definitions

* `CommAlgCat.IsPolynomialAlgebraBelow` and `CommAlgCat.IsPolynomialAlgebraOverBelow`: the
  property of an `A`-algebra, resp. of an `A`-algebra over `B`, of being a polynomial algebra on a
  set of variables of cardinality at most `κ`.
* `CommAlgCat.BoundedPolynomialAugmentation` and `CommAlgCat.boundedPolynomialSite`: the
  corresponding full subcategory of `CommAlgCat.PolynomialAugmentation`, and the site it cuts out
  of `CommAlgCat.polynomialSite`.
* `CommAlgCat.boundedPolynomialIndex` and `CommAlgCat.boundedPolynomialModel`: the `Type u` of
  pairs `(S, g)` with `S` a subset of `κ.out` and `g : S → B`, and the augmentation
  `A[S] → B, X_s ↦ g s` it names.
* `CommAlgCat.SmallBoundedPolynomialAugmentation` and
  `CommAlgCat.smallBoundedPolynomialSite`: the small model and its opposite, a `SmallCategory`
  whose objects live in `Type u`.
* `CommAlgCat.boundedPolynomialAugmentationι` and `CommAlgCat.boundedPolynomialSiteι`: the
  inclusion of the restricted category into the unrestricted one.

## Main results

* `CommAlgCat.essSurj_smallBoundedPolynomialAugmentationι`: every polynomial augmentation with at
  most `κ` variables is isomorphic, over `B`, to one in the small model.
* `CommAlgCat.boundedPolynomialAugmentationEquiv` and
  `CommAlgCat.boundedPolynomialSiteEquiv`: the small model is equivalent to the restricted
  category, resp. to the restricted site.
* `CommAlgCat.essentiallySmall_boundedPolynomialAugmentation` and
  `CommAlgCat.essentiallySmall_boundedPolynomialSite`: the restricted category and the restricted
  site are essentially small at `u`.

## Implementation notes

**Why a small model and not merely essential smallness.** `CategoryTheory.SmallModel` would
produce a small category from essential smallness, but only through `Classical.choose`. The model
built here is explicit: its objects are the pairs `(S, g)` with `S : Set κ.out` and `g : S → B`,
a type that genuinely lives in `Type u`, and its morphisms are *by construction* the morphisms of
`CommAlgCat.BoundedPolynomialAugmentation` between the named objects, through
`CategoryTheory.InducedCategory`. So the inclusion is fully faithful with no proof obligation and
the only thing to prove is essential surjectivity — which is the mathematical content of the
footnote: a set of variables of cardinality at most `κ` may be replaced by a subset of a fixed
representative of `κ`, and the augmentation transported along
`MvPolynomial.renameEquiv`.

**The universe bookkeeping.** `CommAlgCat.{u} A` lives in `Type (u + 1)` and its morphisms in
`Type u`, so `CommAlgCat.PolynomialAugmentation` is a large category with small hom types; the
small model has both in `Type u`, which is what `SmallCategory` means and what the criterion of
Tag 08Q9 asks for. The cardinal `κ` is a `Cardinal.{u}`, and `κ.out` its chosen `Type u`
representative, as in `CommRingCat.essentiallySmall_cardinalMk_lt`.

**The bound.** The source's footnote takes `κ = #B`. Nothing below depends on that choice, and
the bound is left free, because `κ = #B` does *not* suffice for the standard resolution: its term
in degree `n + 1` is a polynomial algebra on the underlying set of its term in degree `n`, which
for `B` finite is already infinite. The bound needed is recorded where the resolutions are, in
`StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean`.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### The cardinality-restricted site -/

/-- A commutative `A`-algebra is a polynomial algebra over `A` on at most `κ` variables if it is
isomorphic, as an `A`-algebra, to a multivariate polynomial algebra over `A` whose index type has
cardinality at most `κ`. This is `CommAlgCat.IsPolynomialAlgebra` with the restriction imposed by
the footnote to the source's section, which takes `κ` to be the cardinality of `B`. -/
abbrev IsPolynomialAlgebraBelow (P : CommAlgCat.{u} A) : Prop :=
  ∃ ι : Type u, Cardinal.mk ι ≤ κ ∧ Nonempty (MvPolynomial ι A ≃ₐ[A] P)

/-- A polynomial algebra on at most `κ` variables is a polynomial algebra. -/
lemma IsPolynomialAlgebraBelow.isPolynomialAlgebra {P : CommAlgCat.{u} A}
    (h : IsPolynomialAlgebraBelow A κ P) : IsPolynomialAlgebra A P :=
  h.imp fun _ h => h.2

/-- The property of an `A`-algebra over `B` of being a polynomial algebra over `A` on a set of
variables of cardinality at most `κ`. -/
abbrev IsPolynomialAlgebraOverBelow : ObjectProperty (Over B) :=
  fun P => IsPolynomialAlgebraBelow A κ P.left

/-- A polynomial algebra over `B` with at most `κ` variables is a polynomial algebra over `B`. -/
lemma isPolynomialAlgebraOverBelow_le_isPolynomialAlgebraOver :
    IsPolynomialAlgebraOverBelow A B κ ≤ IsPolynomialAlgebraOver A B :=
  fun _ h => h.isPolynomialAlgebra

/-- The category whose objects are the `A`-algebra maps `α : P → B` with `P` a polynomial algebra
over `A` on at most `κ` variables, and whose morphisms are the `A`-algebra maps compatible with
the augmentations: the category underlying the site `C_{B/A}` as the source defines it, with the
footnote's restriction in place. -/
abbrev BoundedPolynomialAugmentation := (IsPolynomialAlgebraOverBelow A B κ).FullSubcategory

/-- The site `C_{B/A}` cut down to the polynomial algebras on at most `κ` variables: the opposite
of `CommAlgCat.BoundedPolynomialAugmentation`. For `κ = #B` this is the site of the source,
footnote included; `CommAlgCat.polynomialSite` is the same construction with the footnote
omitted. -/
@[stacks 08PR "the site C_{B/A} with the section's footnote in force, restricting the sets of \
  variables to cardinality at most κ. The unrestricted version is \
  `CommAlgCat.polynomialSite`; only this one is essentially small"]
abbrev boundedPolynomialSite := (BoundedPolynomialAugmentation A B κ)ᵒᵖ

/-- The inclusion of the restricted category of polynomial augmentations into the unrestricted
one. -/
abbrev boundedPolynomialAugmentationι :
    BoundedPolynomialAugmentation A B κ ⥤ PolynomialAugmentation A B :=
  ObjectProperty.ιOfLE (isPolynomialAlgebraOverBelow_le_isPolynomialAlgebraOver A B κ)

/-- The inclusion of the restricted site into the unrestricted site
`CommAlgCat.polynomialSite`. -/
abbrev boundedPolynomialSiteι : boundedPolynomialSite A B κ ⥤ polynomialSite A B :=
  (boundedPolynomialAugmentationι A B κ).op

/-! ### The small model -/

/-- The index type of the small model of the restricted category: a subset `S` of a fixed `Type u`
representative of `κ`, together with the images in `B` of the variables indexed by `S`. -/
abbrev boundedPolynomialIndex : Type u := Σ S : Set κ.out, (S → B)

/-- The polynomial augmentation named by an index `(S, g)`: the polynomial algebra `A[S]` with the
augmentation sending the variable `X_s` to `g s`. Its set of variables is a subset of a
representative of `κ`, so it has at most `κ` variables. -/
def boundedPolynomialModel (i : boundedPolynomialIndex A B κ) :
    BoundedPolynomialAugmentation A B κ where
  obj := Over.mk (CommAlgCat.ofHom (MvPolynomial.aeval (R := A) fun s : i.1 => (i.2 s : B)))
  property := ⟨i.1, (Cardinal.mk_set_le i.1).trans_eq (Cardinal.mk_out κ), ⟨AlgEquiv.refl⟩⟩

/-- The small model of the restricted category of polynomial augmentations: the category whose
objects are the indices `(S, g)` of `CommAlgCat.boundedPolynomialIndex` and whose morphisms are
the morphisms of `CommAlgCat.BoundedPolynomialAugmentation` between the augmentations they name.
Both its objects and its morphisms live in `Type u`, so it is a `SmallCategory`. -/
abbrev SmallBoundedPolynomialAugmentation : Type u :=
  InducedCategory (BoundedPolynomialAugmentation A B κ) (boundedPolynomialModel A B κ)

/-- The small model of the restricted site `C_{B/A}`: the opposite of
`CommAlgCat.SmallBoundedPolynomialAugmentation`, a `SmallCategory` in `Type u`. -/
abbrev smallBoundedPolynomialSite := (SmallBoundedPolynomialAugmentation A B κ)ᵒᵖ

/-- The fully faithful inclusion of the small model into the restricted category of polynomial
augmentations. -/
abbrev smallBoundedPolynomialAugmentationι :
    SmallBoundedPolynomialAugmentation A B κ ⥤ BoundedPolynomialAugmentation A B κ :=
  inducedFunctor (boundedPolynomialModel A B κ)

/-- The fully faithful inclusion of the small model of the restricted site into the restricted
site. -/
abbrev smallBoundedPolynomialSiteι :
    smallBoundedPolynomialSite A B κ ⥤ boundedPolynomialSite A B κ :=
  (smallBoundedPolynomialAugmentationι A B κ).op

/-- **The content of the footnote.** Every polynomial `A`-algebra augmented to `B` on at most `κ`
variables is isomorphic, over `B`, to one of the small model: a set of variables of cardinality at
most `κ` embeds into a representative of `κ`, so it may be replaced by a subset of that
representative, and the augmentation is transported along the renaming of variables. -/
instance essSurj_smallBoundedPolynomialAugmentationι :
    (smallBoundedPolynomialAugmentationι A B κ).EssSurj where
  mem_essImage X := by
    obtain ⟨ι, hι, ⟨e⟩⟩ := X.property
    obtain ⟨f⟩ : Nonempty (ι ↪ κ.out) :=
      (Cardinal.le_def ι κ.out).mp (hι.trans_eq (Cardinal.mk_out κ).symm)
    set σ : ι ≃ (Set.range f : Set κ.out) := Equiv.ofInjective f f.injective with hσ
    refine ⟨⟨Set.range f, fun s => X.obj.hom (e (MvPolynomial.X (σ.symm s)))⟩,
      ⟨ObjectProperty.isoMk _ (Over.isoMk
        (CommAlgCat.isoMk ((MvPolynomial.renameEquiv A σ.symm).trans e)) ?_)⟩⟩
    apply CommAlgCat.hom_ext
    refine MvPolynomial.algHom_ext fun s => ?_
    simp [boundedPolynomialModel, MvPolynomial.renameEquiv]

/-- The inclusion of the small model into the restricted category of polynomial augmentations is
an equivalence of categories. -/
instance isEquivalence_smallBoundedPolynomialAugmentationι :
    (smallBoundedPolynomialAugmentationι A B κ).IsEquivalence where

/-- The small model is equivalent to the restricted category of polynomial augmentations. -/
def boundedPolynomialAugmentationEquiv :
    SmallBoundedPolynomialAugmentation A B κ ≌ BoundedPolynomialAugmentation A B κ :=
  (smallBoundedPolynomialAugmentationι A B κ).asEquivalence

/-- The small model of the restricted site is equivalent to the restricted site. -/
def boundedPolynomialSiteEquiv :
    smallBoundedPolynomialSite A B κ ≌ boundedPolynomialSite A B κ :=
  (boundedPolynomialAugmentationEquiv A B κ).op

/-- **The restricted category of polynomial augmentations is essentially small at `u`.** This is
what the footnote buys, and what the unrestricted `CommAlgCat.PolynomialAugmentation` does not
satisfy. -/
instance essentiallySmall_boundedPolynomialAugmentation :
    EssentiallySmall.{u} (BoundedPolynomialAugmentation A B κ) :=
  EssentiallySmall.mk' (boundedPolynomialAugmentationEquiv A B κ).symm

/-- **The restricted site `C_{B/A}` is essentially small at `u`.** -/
instance essentiallySmall_boundedPolynomialSite :
    EssentiallySmall.{u} (boundedPolynomialSite A B κ) :=
  EssentiallySmall.mk' (boundedPolynomialSiteEquiv A B κ).symm

/-- The fully faithful functor from the small model of the restricted site to the unrestricted
site `CommAlgCat.polynomialSite`: the composite of the inclusion of the model into the restricted
site with the inclusion of the restricted site into the unrestricted one. -/
abbrev smallBoundedPolynomialSiteToPolynomialSite :
    smallBoundedPolynomialSite A B κ ⥤ polynomialSite A B :=
  smallBoundedPolynomialSiteι A B κ ⋙ boundedPolynomialSiteι A B κ

/-- `CommAlgCat.smallBoundedPolynomialSiteToPolynomialSite` is fully faithful, being a composite
of inclusions of full subcategories read in opposite categories. -/
def fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite :
    (smallBoundedPolynomialSiteToPolynomialSite A B κ).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end CommAlgCat

end
