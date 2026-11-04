module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization

/-!
# Essential smallness of the sites of a category fibred in groupoids

The fppf site of an algebraic stack, its flat-fppf subsite and its lisse-étale subsite are
all required to be essentially small: that is what makes sheafification available on them, and
hence what makes their topoi, structure sheaves and module categories exist at all.

This file reduces all of those statements to **two** inputs, by pure category theory.

The first reduction is for a category `p : 𝒮 ⥤ 𝒞` fibred in groupoids. Isomorphism classes of
objects of `𝒮` are accounted for by an isomorphism class of the base together with an
isomorphism class in one fibre: if `x` lies over `U'` and `e : U ≅ U'`, then transporting `x`
along `e` — which is possible because every morphism lifting an isomorphism in a category
fibred in groupoids is itself an isomorphism — produces an object over `U` isomorphic to `x`.
So `𝒮` is essentially small as soon as `𝒞` is and every fibre is.

The second reduction is that a full subcategory of an essentially small category is essentially
small, which applies to the flat-fppf and lisse-étale subsites of the fppf site of an algebraic
stack at once: both are full subcategories of the same category, cut out by flatness
respectively smoothness of the associated morphism from a scheme. So only *one* essential
smallness statement about the fppf site is needed, not one per subsite.

The over-category step — an over category of an essentially small category is again essentially
small — is `CategoryTheory.essentiallySmall_over`, which lives in
`StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange`, where it is needed as an
instance for the over categories indexing a cofiltered limit of schemes. It is imported here, so
`CategoryTheory.essentiallySmall_over` remains available to every consumer of this file.

What is left after these reductions is exactly:

* `EssentiallySmall.{u} B.Schemes`, i.e. that the size-bounded category of schemes `Sch_κ`
  underlying a big fppf site has only `u`-many isomorphism classes — Stacks 000J, which is
  `AlgebraicGeometry.essentiallySmall_schemeBelow`, so it is carried below as an instance
  hypothesis rather than reproved; and
* essential smallness of each fibre `𝒳(U)` of an algebraic stack, which is a descent statement
  about its smooth presentation and not formal.

The *slices* of the site need neither: `Over.post p` is fully faithful for a category fibred in
groupoids, because existence and uniqueness of fill-ins say exactly that a morphism into a fixed
object is determined by, and may be prescribed as, a compatible morphism of the base.  So
`Over x` embeds into `Over (p.obj x)` and is essentially small with no hypothesis on the fibres.
That is what makes sheafification, `Ext` and injective resolutions available on the localized
sites of Stacks 0GR0.

## Main results

* `CategoryTheory.essentiallySmall_fullSubcategory`: a full subcategory of an essentially small
  category is essentially small.
* `CategoryTheory.Functor.IsFiberedInGroupoids.exists_obj_eq_of_iso`: transport of an object of
  a category fibred in groupoids along an isomorphism of its image in the base.
* `CategoryTheory.Functor.IsFiberedInGroupoids.small_skeleton` and
  `CategoryTheory.Functor.IsFiberedInGroupoids.essentiallySmall`: the base-and-fibres criterion.
* `AlgebraicGeometry.Stack.essentiallySmall_bigFppfOver`,
  `AlgebraicGeometry.Stack.essentiallySmall_obj` and
  `AlgebraicGeometry.Stack.essentiallySmall_fullSubsite`: the three statements in the form the
  fppf, flat-fppf and lisse-étale sites of a category fibred in groupoids over a big fppf site
  need them.
  `CategoryTheory.Functor.IsFiberedInGroupoids.full_overPost` and
  `CategoryTheory.Functor.IsFiberedInGroupoids.essentiallySmall_over`: the slice criterion, which
  needs nothing about the fibres.
* `AlgebraicGeometry.Stack.essentiallySmall_over_obj` and
  `AlgebraicGeometry.Stack.essentiallySmall_over_fullSubsite`: the slice criterion for the fppf
  site of a category fibred in groupoids and for its full subsites.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

section General

variable {C : Type u₁} [Category.{v₁} C]

/-- A full subcategory of an essentially small category is essentially small. -/
theorem essentiallySmall_fullSubcategory (P : ObjectProperty C) [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} P.FullSubcategory :=
  essentiallySmall_of_fully_faithful P.ι

end General

namespace Functor.IsFiberedInGroupoids

variable {𝒮 : Type u₁} {𝒞 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒞] {p : 𝒮 ⥤ 𝒞}

/-- An object of a category fibred in groupoids can be transported along an isomorphism of its
image in the base: if `e : U ≅ p.obj x` then some `y` lying over `U` is isomorphic to `x`.

The lift of `e.hom` supplied by the fibred-in-groupoids condition is strongly cartesian, hence
an isomorphism because `e.hom` is one. -/
theorem exists_obj_eq_of_iso (hp : p.IsFiberedInGroupoids) {U : 𝒞} {x : 𝒮} (e : U ≅ p.obj x) :
    ∃ y : 𝒮, p.obj y = U ∧ Nonempty (y ≅ x) := by
  obtain ⟨y, φ, hφ⟩ := hp.exists_lift e.hom x rfl
  have hlift := hφ
  have : p.IsStronglyCartesian e.hom φ := hp.isStronglyCartesian_homLift e.hom φ
  have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso p e.hom φ
  exact ⟨y, IsHomLift.domain_eq p e.hom φ, ⟨asIso φ⟩⟩

/-- The isomorphism classes of the total category of a category fibred in groupoids are
`w`-small as soon as those of the base and of each fibre are.

Every object is isomorphic to one lying over the chosen representative of its base
isomorphism class, by `exists_obj_eq_of_iso`, so the pairs consisting of a base isomorphism
class and an isomorphism class in the fibre over its representative exhaust `Skeleton 𝒮`. -/
theorem small_skeleton (hp : p.IsFiberedInGroupoids) [Small.{w} (Skeleton 𝒞)]
    [∀ U : 𝒞, Small.{w} (Skeleton (p.Fiber U))] : Small.{w} (Skeleton 𝒮) := by
  refine small_of_surjective
    (f := fun s : (Σ c : Skeleton 𝒞, Skeleton (p.Fiber ((fromSkeleton 𝒞).obj c))) =>
      toSkeleton (Fiber.fiberInclusion.obj ((fromSkeleton _).obj s.2))) ?_
  intro q
  obtain ⟨y, hy, ⟨ey⟩⟩ := hp.exists_obj_eq_of_iso
    (fromSkeletonToSkeletonIso (p.obj ((fromSkeleton 𝒮).obj q)))
  refine ⟨⟨toSkeleton (p.obj ((fromSkeleton 𝒮).obj q)), toSkeleton (Fiber.mk hy)⟩, ?_⟩
  exact (congr_toSkeleton_of_iso
    (Fiber.fiberInclusion.mapIso (fromSkeletonToSkeletonIso (Fiber.mk hy)) ≪≫ ey)).trans
      (toSkeleton_fromSkeleton_obj q)

/-- The total category of a category fibred in groupoids is essentially small as soon as the
base is, each fibre is, and the total category is locally small. -/
theorem essentiallySmall (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{w} 𝒞]
    [LocallySmall.{w} 𝒮] (h : ∀ U : 𝒞, EssentiallySmall.{w} (p.Fiber U)) :
    EssentiallySmall.{w} 𝒮 := by
  have : ∀ U : 𝒞, Small.{w} (Skeleton (p.Fiber U)) := fun U => have := h U; inferInstance
  exact (essentiallySmall_iff 𝒮).2 ⟨hp.small_skeleton, inferInstance⟩

/-! ### Over categories

The over category of an object of the total category is essentially small as soon as the *base*
is — no smallness of the total category is needed. Indeed `Over.post p : Over x ⥤ Over (p.obj x)`
is fully faithful for a category fibred in groupoids: existence and uniqueness of fill-ins say
exactly that a morphism `y ⟶ x` of `𝒮` is determined by, and may be prescribed as, a morphism
`p.obj y ⟶ p.obj x` compatible with the two structure morphisms. -/

/-- **The slices of a category fibred in groupoids are essentially small as soon as the base
is.** Unlike `CategoryTheory.Functor.IsFiberedInGroupoids.essentiallySmall`, this needs nothing
about the fibres: `Over x` embeds fully faithfully into `Over (p.obj x)`.

This is what makes the *localizations* of the fppf site of an algebraic stack, and of its
flat-fppf and lisse-étale subsites, essentially small — hence what makes sheafification, `Ext`
and injective resolutions available on them — without assuming the site itself to be. -/
theorem essentiallySmall_over (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{w} 𝒞] (x : 𝒮) :
    EssentiallySmall.{w} (Over x) :=
  have := hp.faithful_overPost x
  have := hp.full_overPost x
  have : EssentiallySmall.{w} (Over (p.obj x)) := inferInstance
  essentiallySmall_of_fully_faithful (Over.post (X := x) p)

end Functor.IsFiberedInGroupoids

end CategoryTheory

namespace AlgebraicGeometry.Stack

open CategoryTheory

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf category over a scheme is essentially small as soon as the size-bounded
category of schemes underlying the big fppf site is. -/
theorem essentiallySmall_bigFppfOver [EssentiallySmall.{u} B.Schemes] :
    EssentiallySmall.{u} (BigFppfOver B S hS) :=
  essentiallySmall_over _

/-- The total category of a category fibred in groupoids over the big fppf category of a scheme
— for an algebraic stack, its fppf site — is essentially small as soon as the size-bounded
category of schemes is and every fibre is.

For an algebraic stack the fibres are its categories of scheme-valued points, and their
essential smallness is the remaining, non-formal, input. -/
theorem essentiallySmall_obj
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    [EssentiallySmall.{u} B.Schemes] [LocallySmall.{u} 𝒳.val.obj]
    (h : ∀ U : BigFppfOver B S hS, EssentiallySmall.{u} (𝒳.val.p.Fiber U)) :
    EssentiallySmall.{u} 𝒳.val.obj :=
  have := essentiallySmall_bigFppfOver B S hS
  𝒳.2.essentiallySmall h

/-- Every full subsite of the fppf site of a category fibred in groupoids over a big fppf
category is essentially small once that site is.

Both the flat-fppf site and the lisse-étale site of an algebraic stack are instances: they are
the full subcategories of the objects whose associated morphism from a scheme is flat,
respectively smooth. -/
theorem essentiallySmall_fullSubsite
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    [EssentiallySmall.{u} 𝒳.val.obj] (P : ObjectProperty 𝒳.val.obj) :
    EssentiallySmall.{u} P.FullSubcategory :=
  essentiallySmall_fullSubcategory P

/-- **Every slice of the fppf site of a category fibred in groupoids over a big fppf category is
essentially small**, with no hypothesis on the fibres: only the size-bounded category of schemes
needs to be essentially small, and that is `AlgebraicGeometry.essentiallySmall_schemeBelow`. -/
theorem essentiallySmall_over_obj
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    [EssentiallySmall.{u} B.Schemes] (x : 𝒳.val.obj) :
    EssentiallySmall.{u} (Over x) :=
  have := essentiallySmall_bigFppfOver B S hS
  𝒳.2.essentiallySmall_over x

/-- **Every slice of a full subsite of the fppf site is essentially small**, again with no
hypothesis on the fibres.

The flat-fppf site and the lisse-étale site of an algebraic stack are the two cases: their
slices at a flat, respectively smooth, object are the sites on which Stacks 0GR0 computes local
cohomology. -/
theorem essentiallySmall_over_fullSubsite
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    [EssentiallySmall.{u} B.Schemes] (P : ObjectProperty 𝒳.val.obj) (x : P.FullSubcategory) :
    EssentiallySmall.{u} (Over x) :=
  have := essentiallySmall_over_obj B S hS 𝒳 (P.ι.obj x)
  essentiallySmall_of_fully_faithful (Over.post (X := x) P.ι)

end AlgebraicGeometry.Stack

end
