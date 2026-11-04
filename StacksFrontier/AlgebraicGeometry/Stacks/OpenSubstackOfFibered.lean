module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# Open substacks of a category fibred in groupoids

Stacks 04YM defines an open substack of an *algebraic* stack `𝒳` as a strictly full subcategory
`𝒳' ⊆ 𝒳` which is an algebraic stack and whose inclusion `𝒳' → 𝒳` is an open immersion, that
is (Stacks 04YL, 04XB) representable by algebraic spaces with open immersions as base changes
along scheme-valued points. Every clause but "`𝒳'` is an algebraic stack" makes sense for an
arbitrary category fibred in groupoids `𝒳` over the big fppf site, and for an algebraic `𝒳`
that clause is automatic: a category fibred in groupoids with a 1-morphism to an algebraic stack
which is representable by algebraic spaces is itself an algebraic stack (Stacks 05UM).

This module records the notion for an arbitrary category fibred in groupoids: an open substack
is a strictly full subcategory, fibred in groupoids over the site (so closed under base change),
whose inclusion is representable by algebraic spaces and an open immersion. It is the notion
the chapter on moduli of curves uses when it speaks of open substacks of `Curves` before
`Curves` is known to be algebraic (Stacks 0E0E, the method of Section 109.6), and it agrees with
Stacks 04YM on algebraic stacks: `AlgebraicGeometry.Stack.openSubstackEquivFibered` identifies
the open substacks of an algebraic stack `𝒳` in the sense of
`AlgebraicGeometry.Stack.OpenSubstack` with those of its underlying category fibred in groupoids,
property for property.

## Main definitions

* `AlgebraicGeometry.Stack.fiberedFullSubcategory`: the full subcategory of a category fibred in
  groupoids selected by a property of objects, as a category fibred in groupoids, given that its
  structure functor is fibred in groupoids.
* `AlgebraicGeometry.Stack.fiberedFullSubcategoryInclusion`: its inclusion 1-morphism.
* `AlgebraicGeometry.Stack.FiberedOpenSubstack`: an open substack of a category fibred in
  groupoids over the big fppf site, with `AlgebraicGeometry.Stack.FiberedOpenSubstack.toFibered`
  and `AlgebraicGeometry.Stack.FiberedOpenSubstack.inclusion` the substack as a category fibred
  in groupoids and its inclusion 1-morphism.
* `AlgebraicGeometry.Stack.openSubstackEquivFibered`: for an algebraic stack, open substacks in
  the sense of Stacks 04YM are the same as open substacks of the underlying category fibred in
  groupoids.

## Main results

* `AlgebraicGeometry.fullSubcategory_isFiberedInGroupoids` (from
  `StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal`): the full subcategory selected by a property
  inherited along morphisms is fibred in groupoids.
* `AlgebraicGeometry.Stack.FiberedOpenSubstack.exists_obj_eq_iff`: an object lies in the image
  of the inclusion of an open substack exactly when it has the selecting property.
* `AlgebraicGeometry.Stack.FiberedOpenSubstack.property_of_hom`: membership of an open substack
  is inherited along morphisms, i.e. an open substack is closed under base change.

## References

* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The full subcategory of a category fibred in groupoids `𝒳` over the big fppf site of `S`
selected by a property of objects, as a category fibred in groupoids, given that the restriction
of the structure functor to it is fibred in groupoids. -/
abbrev fiberedFullSubcategory (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (P : ObjectProperty 𝒳.val.obj) (hP : (P.ι ⋙ 𝒳.val.p).IsFiberedInGroupoids) :
    CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (P.ι ⋙ 𝒳.val.p)) hP

/-- The inclusion of the full subcategory `AlgebraicGeometry.Stack.fiberedFullSubcategory` into
`𝒳`, as a 1-morphism of categories fibred in groupoids over the big fppf site of `S`. -/
@[implicit_reducible]
def fiberedFullSubcategoryInclusion
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (P : ObjectProperty 𝒳.val.obj) (hP : (P.ι ⋙ 𝒳.val.p).IsFiberedInGroupoids) :
    fiberedFullSubcategory 𝒳 P hP ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom { toFunctor := P.ι, w := rfl }

/-- An *open substack* of a category fibred in groupoids `𝒳` over the big fppf site of `S`: a
strictly full subcategory `𝒳' ⊆ 𝒳` whose structure functor is fibred in groupoids and whose
inclusion `𝒳' → 𝒳` is representable by algebraic spaces and an open immersion (Stacks 04XB,
04YL).

This is Stacks 04YM with the clause "`𝒳'` is an algebraic stack" dropped, which is what makes
sense when `𝒳` itself is not (yet) known to be algebraic — the situation of Stacks 0E0E, where
open substacks of `Curves` are produced before Stacks 0D5A. Nothing is lost: when `𝒳` is an
algebraic stack the dropped clause follows from the others by Stacks 05UM, and
`AlgebraicGeometry.Stack.openSubstackEquivFibered` identifies these open substacks with those of
`AlgebraicGeometry.Stack.OpenSubstack`. Requiring the structure functor of `𝒳'` to be fibred in
groupoids is part of `𝒳'` being a substack (for Stacks it is implied by `𝒳'` being an algebraic
stack); for a strictly full subcategory it says exactly that `𝒳'` is closed under base change,
see `AlgebraicGeometry.Stack.FiberedOpenSubstack.property_of_hom`. -/
structure FiberedOpenSubstack (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    where
  /-- The property of objects of `𝒳` selecting the full subcategory. -/
  property : ObjectProperty 𝒳.val.obj
  /-- Strict fullness: membership is invariant under isomorphism. -/
  strictlyFull : property.IsClosedUnderIsomorphisms
  /-- The full subcategory is fibred in groupoids over the site. -/
  isFiberedInGroupoids : (property.ι ⋙ 𝒳.val.p).IsFiberedInGroupoids
  /-- Its inclusion into `𝒳` is representable by algebraic spaces. -/
  isRepresentable : IsRepresentableByAlgebraicSpaces B S hS
    (fiberedFullSubcategoryInclusion 𝒳 property isFiberedInGroupoids).hom
  /-- Its inclusion into `𝒳` is an open immersion. -/
  isOpenImmersion : Stack.IsOpenImmersion B S hS
    (fiberedFullSubcategoryInclusion 𝒳 property isFiberedInGroupoids)

/-- Two open substacks of a category fibred in groupoids with the same objects are equal. -/
@[ext]
theorem FiberedOpenSubstack.ext
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    {U V : FiberedOpenSubstack 𝒳} (h : U.property = V.property) : U = V := by
  cases U with
  | mk up us uf ur uo =>
    cases V with
    | mk vp vs vf vr vo =>
      subst h
      rfl

/-- The open substack `𝒳' ⊆ 𝒳` as a category fibred in groupoids. -/
abbrev FiberedOpenSubstack.toFibered
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : FiberedOpenSubstack 𝒳) : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS) :=
  fiberedFullSubcategory 𝒳 U.property U.isFiberedInGroupoids

/-- The inclusion `𝒳' → 𝒳` of an open substack, as a 1-morphism of categories fibred in
groupoids. -/
abbrev FiberedOpenSubstack.inclusion
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : FiberedOpenSubstack 𝒳) : U.toFibered ⟶ 𝒳 :=
  fiberedFullSubcategoryInclusion 𝒳 U.property U.isFiberedInGroupoids

/-- An object of `𝒳` lies in the image on objects of the inclusion of an open substack exactly
when it satisfies the property selecting the substack. -/
theorem FiberedOpenSubstack.exists_obj_eq_iff
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : FiberedOpenSubstack 𝒳) (x : 𝒳.val.obj) :
    (∃ Y : U.toFibered.val.obj, (CatFiberedInGroupoids.homFunctor U.inclusion).obj Y = x) ↔
      U.property x := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact Y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Membership of an open substack is inherited along morphisms of `𝒳`: an open substack is
closed under base change. A morphism `x ⟶ y` of `𝒳` with `y` in the substack is compared with a
lift inside the substack of its image in the site; the two are isomorphic because `𝒳` is fibred
in groupoids, and the substack is strictly full. -/
theorem FiberedOpenSubstack.property_of_hom
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : FiberedOpenSubstack 𝒳) {x y : 𝒳.val.obj} (f : x ⟶ y) (hy : U.property y) :
    U.property x := by
  obtain ⟨x', φ, hφ⟩ := U.isFiberedInGroupoids.exists_lift (𝒳.val.p.map f)
    (⟨y, hy⟩ : U.property.FullSubcategory) rfl
  have : 𝒳.val.p.IsHomLift (𝒳.val.p.map f) φ.hom :=
    IsHomLift.of_fac' 𝒳.val.p (𝒳.val.p.map f) φ.hom
      (IsHomLift.domain_eq (U.property.ι ⋙ 𝒳.val.p) (𝒳.val.p.map f) φ)
      (IsHomLift.codomain_eq (U.property.ι ⋙ 𝒳.val.p) (𝒳.val.p.map f) φ)
      (IsHomLift.fac' (U.property.ι ⋙ 𝒳.val.p) (𝒳.val.p.map f) φ)
  have : 𝒳.val.p.IsStronglyCartesian (𝒳.val.p.map f) φ.hom :=
    𝒳.property.isStronglyCartesian_homLift (𝒳.val.p.map f) φ.hom
  have : 𝒳.val.p.IsStronglyCartesian (𝒳.val.p.map f) f :=
    𝒳.property.isStronglyCartesian_homLift (𝒳.val.p.map f) f
  exact U.strictlyFull.of_iso
    (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.p (𝒳.val.p.map f) φ.hom f).symm x'.property

/-- **Open substacks of an algebraic stack are open substacks of its underlying category fibred
in groupoids.** For an algebraic stack `𝒳`, the open substacks of Stacks 04YM
(`AlgebraicGeometry.Stack.OpenSubstack`) are exactly the open substacks of the underlying
category fibred in groupoids (`AlgebraicGeometry.Stack.FiberedOpenSubstack`), by an equivalence
which keeps the property of objects selecting the substack.

The clause of Stacks 04YM which `AlgebraicGeometry.Stack.FiberedOpenSubstack` does not ask for,
that the substack is itself an algebraic stack, is recovered from the representability of its
inclusion by Stacks 05UM
(`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces`); in the
other direction the fibredness of the substack is part of its being an algebraic stack. -/
def openSubstackEquivFibered (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    OpenSubstack 𝒳 ≃ FiberedOpenSubstack 𝒳.val where
  toFun U :=
    { property := U.property
      strictlyFull := U.strictlyFull
      isFiberedInGroupoids := U.isAlgebraic.fst
      isRepresentable := U.isOpenImmersion.1
      isOpenImmersion := U.isOpenImmersion.2 }
  invFun V :=
    { property := V.property
      strictlyFull := V.strictlyFull
      isAlgebraic := isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS
        (fiberedFullSubcategoryInclusion 𝒳.val V.property V.isFiberedInGroupoids)
        V.isRepresentable 𝒳.property
      isOpenImmersion := ⟨V.isRepresentable, V.isOpenImmersion⟩ }
  left_inv _ := OpenSubstack.ext rfl
  right_inv _ := FiberedOpenSubstack.ext rfl

/-- The open substack of Stacks 04YM attached to an open substack of the underlying category
fibred in groupoids of an algebraic stack selects the same objects. -/
@[simp]
theorem openSubstackEquivFibered_symm_property (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (V : FiberedOpenSubstack 𝒳.val) :
    ((openSubstackEquivFibered 𝒳).symm V).property = V.property :=
  rfl

/-- The open substack of the underlying category fibred in groupoids attached to an open
substack of Stacks 04YM of an algebraic stack selects the same objects. -/
@[simp]
theorem openSubstackEquivFibered_property (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : OpenSubstack 𝒳) :
    (openSubstackEquivFibered 𝒳 U).property = U.property :=
  rfl

end AlgebraicGeometry.Stack

end
