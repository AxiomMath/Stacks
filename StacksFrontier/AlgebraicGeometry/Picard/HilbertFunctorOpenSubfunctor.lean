module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorClosedSubschemes

/-!
# Open subfunctors of the Hilbert functor of points

A subfunctor `F` of the degree-`d` Hilbert functor `Hilb^d_{X/S}` is *open* if for every scheme
`T` over `S` and every `Z ∈ Hilb^d_{X/S}(T)` there is an open `U ⊆ T` such that for every
`g : T' ⟶ T` over `S`, the base change `Z_{T'}` lies in `F(T')` exactly when `g` maps `T'` into
`U`; this is condition (2)(b) of the gluing criterion of Stacks 01JJ. This file defines open
subfunctors and shows that a representation of `Hilb^d_{X/S}` gives a representing scheme.

## Main definitions

* `Stacks.Hilbert.IsOpenHilbertSubfunctor`: condition (2)(b) of Stacks 01JJ for a subfunctor of
  `Hilb^d_{X/S}`.
* `Stacks.Hilbert.RepresentsHilbertFunctorOfRank.ofRepresentableBy`: a scheme representing the
  functor `Stacks.Hilbert.hilbertFunctorOfRank` represents it in the sense of
  `Stacks.Hilbert.RepresentsHilbertFunctorOfRank`.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- **Openness of a subfunctor of the Hilbert functor** (condition (2)(b) of Stacks 01JJ, in the
set-theoretic form). For every family `Z` over `T` there is an open `U ⊆ T` such that the base
change of `Z` along `g : T' ⟶ T` lies in the subfunctor exactly when `g` maps into `U`. -/
def IsOpenHilbertSubfunctor {X : Over S} {d : ℕ} (F : Subfunctor (hilbertFunctorOfRank X d)) :
    Prop :=
  ∀ (T : Over S) (Z : HilbertFamily X T d), ∃ U : T.left.Opens,
    ∀ (T' : Over S) (g : T' ⟶ T), baseChange X g Z ∈ F.obj (op T') ↔ Set.range g.left ⊆ U

/-- A representation of the functor `Stacks.Hilbert.hilbertFunctorOfRank` gives a representing
scheme of the degree-`d` Hilbert functor in the sense of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank`. This is the converse of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank.representableBy`. -/
def RepresentsHilbertFunctorOfRank.ofRepresentableBy {X H : Over S} {d : ℕ}
    (h : (hilbertFunctorOfRank X d).RepresentableBy H) : RepresentsHilbertFunctorOfRank X H d where
  family := h.homEquiv
  naturality g f := congrArg HilbertFamily.ideal (h.homEquiv_comp g f)

end Stacks.Hilbert

end
