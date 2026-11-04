module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sheaves on a category over the big fppf category of a scheme (Stacks 06TR, 06TS, 06TT)

Let `S` be a scheme contained in a big fppf site `B` and let `p : 𝒳 ⥤ (Sch/S)` be a category
over the big fppf category of `S`. Stacks 06TP equips `𝒳` with a site structure for each of the
five standard topologies — Zariski, étale, smooth, syntomic and fppf — and **Stacks 06TR** says
what a presheaf on `𝒳` being a sheaf for each of those five topologies means, namely that it is
a sheaf for the corresponding associated site, and records that the resulting categories of
sheaves `Sh(𝒳_Zar)`, …, `Sh(𝒳_fppf)` have morphisms of presheaves as their morphisms.

**Stacks 06TS** then says that a 1-morphism of categories fibred in groupoids over the big fppf
category of `S` carries `τ` sheaves to `τ` sheaves in both directions and so defines a morphism
of topoi `Sh(𝒳_τ) ⟶ Sh(𝒴_τ)`, for each of the five topologies.

**Stacks 06TT** is the definition that names that morphism of topoi: it is written
`f = (f⁻¹, f_*) : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` and called the *associated morphism of `τ` topoi*. The
source's `Sh(𝒳_τ)` is sheaves of sets, and for those the limits computing `f_* = {}_pG` are
produced rather than postulated, so the adjunction exists for every 1-morphism of categories
fibred in groupoids over the big fppf category of `S` and every one of the five topologies.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.IsSheaf`: **Stacks 06TR**, the five sheaf conditions, indexed
  by `AlgebraicGeometry.SiteKind`.
* `AlgebraicGeometry.BigFppfOver.AssociatedSheaf`: **Stacks 06TR**, the five categories of
  sheaves of sets, likewise indexed by `AlgebraicGeometry.SiteKind`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isContinuous_and_isCocontinuous_associatedTopology`:
  **Stacks 06TS**, both presheaf functors of a 1-morphism preserve `τ` sheaves.
* `AlgebraicGeometry.BigFppfOver.inverseImageCompSheafToPresheafIso_associatedTopology` and
  `AlgebraicGeometry.BigFppfOver.inverseImage_obj_obj_obj_associatedTopology`: **Stacks 06TS**,
  the inverse image is restriction, with the objectwise formula `f⁻¹(𝒢)(x) = 𝒢(G x)`.
* `AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_inverseImage_associatedTopology`:
  **Stacks 06TS**, the inverse image is left exact.
* `AlgebraicGeometry.BigFppfOver.directImageCompSheafToPresheafIso_associatedTopology`:
  **Stacks 06TS**, the direct image is the right Kan extension.
* `AlgebraicGeometry.BigFppfOver.sheafAdjunction_associatedTopology`: **Stacks 06TS**, the
  morphism of topoi `Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` itself, as the adjunction `f⁻¹ ⊣ f_*`.
* `AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor`: the limits that
  compute the right Kan extension `f_* = {}_pG` along a 1-morphism, for coefficients admitting
  limits of the size those limits have.
* `AlgebraicGeometry.BigFppfOver.sheafAdjunction_associatedSheaf`: **Stacks 06TT**, the associated
  morphism of `τ` topoi `f = (f⁻¹, f_*) : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` on the categories of sheaves of sets
  of Stacks 06TR, for each of the five topologies.

## Implementation notes

Both definitions quantify over the `AlgebraicGeometry.SiteKind` index of
`AlgebraicGeometry.BigFppfOver.associatedTopology`, so the five sheaf conditions and the five
categories of the source are the five values of one definition rather than five definitions.

The category of sheaves is `CategoryTheory.Sheaf`, Mathlib's full subcategory of presheaves
satisfying the sheaf condition; its morphisms are by construction natural transformations of
the underlying presheaves, which is the source's "a morphism of sheaves is just a morphism of
presheaves". It is named `AssociatedSheaf` rather than `Sheaf` because a declaration
`AlgebraicGeometry.BigFppfOver.Sheaf` would shadow `CategoryTheory.Sheaf` for every file
working inside `AlgebraicGeometry.BigFppfOver` — several already write `Sheaf (associatedTopology
B S hS p τ) RingCat` and mean Mathlib's.

The value universe of the presheaf is left independent of the universe of the site, as the
source's "presheaf on `𝒳`" is, so sheaves of sets of any size are covered.

## References

* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TR](https://stacks.math.columbia.edu/tag/06TR)
* [Stacks Project, Tag 06TS](https://stacks.math.columbia.edu/tag/06TS)
* [Stacks Project, Tag 06TT](https://stacks.math.columbia.edu/tag/06TT)
-/

@[expose] public section

open CategoryTheory

universe u v w t

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : Type v}
  [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **Stacks 06TR.** A presheaf of sets on a category `p : 𝒳 ⥤ (Sch/S)` over the big fppf
category of `S` is a *sheaf for the topology `τ`* when it is a sheaf on the associated site
`𝒳_τ` of Stacks 06TP. The five values of `τ` give the Zariski, étale, smooth, syntomic and
fppf sheaf conditions of the source. -/
@[stacks 06TR "sheaf conditions for the five topologies"]
abbrev IsSheaf (τ : SiteKind) (F : Xᵒᵖ ⥤ Type t) : Prop :=
  Presheaf.IsSheaf (associatedTopology B S hS p τ) F

/-- **Stacks 06TR.** The category `Sh(𝒳_τ)` of sheaves of sets on the associated site `𝒳_τ`
of Stacks 06TP, for `τ` one of the five topologies. Its morphisms are morphisms of the
underlying presheaves. -/
@[stacks 06TR "categories and morphisms of sheaves"]
abbrev AssociatedSheaf (τ : SiteKind) :=
  CategoryTheory.Sheaf (associatedTopology B S hS p τ) (Type t)

/-! ### Functoriality (Stacks 06TS)

A 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of `S`
(Stacks 02XS) induces, for each of the five topologies `τ`, a morphism of topoi
`Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` between the associated sites of Stacks 06TP, whose inverse image is
restriction of presheaves and whose direct image is right Kan extension.

Stacks 06TS is the specialisation to those five sites of the general Stacks 06NW, proved in
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/Functoriality.lean` for a 1-morphism of
fibred categories over an arbitrary site. The six declarations below are its six instances, each
closed by applying the corresponding general one: the base site is the big fppf category over
`S` with the localized topology `AlgebraicGeometry.BigFppfOver.baseOverTopology` of the chosen
`AlgebraicGeometry.SiteKind`, so that the inherited topologies are literally the two associated
topologies `AlgebraicGeometry.BigFppfOver.associatedTopology` of Stacks 06TP, whose sheaves of
sets are the `AlgebraicGeometry.BigFppfOver.AssociatedSheaf` of Stacks 06TR above. The general
result asks for a 1-morphism of *fibred* categories, which a 1-morphism of categories fibred in
groupoids is for free by `CategoryTheory.CatFiberedInGroupoids.isStronglyCartesian_map`, and for
fibre products in the base, which the big fppf slice has by Stacks 021U.

The coefficients `A` are left arbitrary, exactly as in the general result, so that the source's
`Sh(𝒳_τ)` — sheaves of sets, `AlgebraicGeometry.BigFppfOver.AssociatedSheaf` — is one value of
each statement rather than the only one; no hypothesis is imposed here that the general result
does not already carry.
-/

universe v₄ u₄

section Functoriality

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, w, u + 1, v} (BigFppfOver B S hS)}

/-- A 1-morphism of the 2-category of categories fibred in groupoids over the big fppf category
of `S` is a 1-morphism of fibred categories: it is strictly over the base by
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`, and it preserves strongly cartesian
morphisms by `CategoryTheory.CatFiberedInGroupoids.isStronglyCartesian_map`, which is the
parenthetical remark of Stacks 02XS. This is what lets the general Stacks 06NW apply. -/
public lemma isFibredOneMorphism_homFunctor (G : 𝒳 ⟶ 𝒴) :
    𝒳.val.p.IsFibredOneMorphism 𝒴.val.p (CatFiberedInGroupoids.homFunctor G) where
  comp_eq := CatFiberedInGroupoids.homFunctor_comp_p G
  map_isStronglyCartesian := by
    intro R T f a b φ h
    have := h
    exact CatFiberedInGroupoids.isStronglyCartesian_map G f φ

/-- The functor of a category fibred in groupoids over the big fppf category is fibred. -/
private instance isFibered_p (𝒵 : CatFiberedInGroupoids.{u, w, u + 1, v} (BigFppfOver B S hS)) :
    𝒵.val.p.IsFibered :=
  𝒵.isFiberedInGroupoids.isFibered

/-- **Stacks 06TS**, preservation of sheaves by both functors. For each of the five topologies
`τ`, the functor underlying a 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the
big fppf category of `S` is continuous and cocontinuous between the associated sites `𝒳_τ` and
`𝒴_τ` of Stacks 06TP. Continuity says that `G^p` carries `τ` sheaves on `𝒴` to `τ` sheaves on
`𝒳` and cocontinuity that `{}_pG` carries `τ` sheaves on `𝒳` to `τ` sheaves on `𝒴`, which is the
first assertion of the source.

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_and_isCocontinuous_inheritedTopology`)
at the base site `(Sch/S)_{fppf}` with the localized topology of `τ`. -/
@[stacks 06TS "preservation of sheaves by both functors"]
public theorem isContinuous_and_isCocontinuous_associatedTopology (G : 𝒳 ⟶ 𝒴) (τ : SiteKind) :
    (CatFiberedInGroupoids.homFunctor G).IsContinuous
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) ∧
      (CatFiberedInGroupoids.homFunctor G).IsCocontinuous
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) :=
  (isFibredOneMorphism_homFunctor B S hS G).isContinuous_and_isCocontinuous_inheritedTopology
    (baseOverTopology B S hS τ)

variable (G : 𝒳 ⟶ 𝒴) (τ : SiteKind) (A : Type u₄) [Category.{v₄} A]

/-- **Stacks 06TS**, `f⁻¹ = G^p`. The inverse image of the induced morphism of topoi
`Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` is plain restriction along `G.op`: as a functor to presheaves on `𝒳` it is
`sheafToPresheaf` followed by precomposition with `G.op`, with no sheafification intervening.

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.inverseImageCompSheafToPresheafIso`) at the five
associated sites. -/
@[stacks 06TS "inverse image is restriction"]
public def inverseImageCompSheafToPresheafIso_associatedTopology :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
    (CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous A
          (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) ⋙
        sheafToPresheaf (associatedTopology B S hS 𝒳.val.p τ) A ≅
      sheafToPresheaf (associatedTopology B S hS 𝒴.val.p τ) A ⋙
        (Functor.whiskeringLeft _ _ _).obj (CatFiberedInGroupoids.homFunctor G).op :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  (isFibredOneMorphism_homFunctor B S hS G).inverseImageCompSheafToPresheafIso
    (baseOverTopology B S hS τ) A

/-- **Stacks 06TS**, the objectwise formula `f⁻¹(𝒢)(x) = 𝒢(G x)`: the sections of the inverse
image of a `τ` sheaf `𝒢` on `𝒴` over an object `x` of `𝒳` are the sections of `𝒢` over `G x`.

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.inverseImage_obj_obj_obj`) at the five associated
sites. -/
@[stacks 06TS "objectwise inverse image formula"]
public theorem inverseImage_obj_obj_obj_associatedTopology :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
    ∀ (𝒢 : Sheaf (associatedTopology B S hS 𝒴.val.p τ) A) (x : 𝒳.val.obj),
      (((CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous A
            (associatedTopology B S hS 𝒳.val.p τ)
            (associatedTopology B S hS 𝒴.val.p τ)).obj 𝒢).obj.obj (Opposite.op x) =
        𝒢.obj.obj (Opposite.op ((CatFiberedInGroupoids.homFunctor G).obj x)) :=
  (isFibredOneMorphism_homFunctor B S hS G).inverseImage_obj_obj_obj
    (baseOverTopology B S hS τ) A

/-- **Stacks 06TS**, exactness of the inverse image. The inverse image of the induced morphism of
topoi preserves finite limits, which is the remaining clause in "morphism of topoi".

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.preservesFiniteLimits_inverseImage`) at the five
associated sites. -/
@[stacks 06TS "left exactness of inverse image"]
public theorem preservesFiniteLimits_inverseImage_associatedTopology [Limits.HasFiniteLimits A] :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
    Limits.PreservesFiniteLimits ((CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous A
      (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ)) :=
  (isFibredOneMorphism_homFunctor B S hS G).preservesFiniteLimits_inverseImage
    (baseOverTopology B S hS τ) A

/-- **Stacks 06TS**, `f_* = {}_pG`. The direct image of the induced morphism of topoi is the
right Kan extension along `G.op`, taken on sheaves: as a functor to presheaves on `𝒴` it is
`sheafToPresheaf` followed by `G.op.ran`.

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.directImageCompSheafToPresheafIso`) at the five
associated sites. -/
@[stacks 06TS "direct image is right Kan extension"]
public noncomputable def directImageCompSheafToPresheafIso_associatedTopology
    [∀ (F : 𝒳.val.objᵒᵖ ⥤ A),
      (CatFiberedInGroupoids.homFunctor G).op.HasPointwiseRightKanExtension F] :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).2
    (CatFiberedInGroupoids.homFunctor G).sheafPushforwardCocontinuous A
          (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) ⋙
        sheafToPresheaf (associatedTopology B S hS 𝒴.val.p τ) A ≅
      sheafToPresheaf (associatedTopology B S hS 𝒳.val.p τ) A ⋙
        (CatFiberedInGroupoids.homFunctor G).op.ran :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  (isFibredOneMorphism_homFunctor B S hS G).directImageCompSheafToPresheafIso
    (baseOverTopology B S hS τ) A

/-- **Stacks 06TS**, the morphism of topoi itself. A 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred
in groupoids over the big fppf category of `S` induces, for each of the five topologies `τ`, a
morphism of topoi `f : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)`: this is the adjunction `f⁻¹ ⊣ f_*` between the two
associated sites of Stacks 06TP, with `f⁻¹ = G^p` the restriction and `f_* = {}_pG` the right Kan
extension. It is the actual adjunction, not an existence claim; together with
`AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_inverseImage_associatedTopology` it is a
morphism of topoi in the source's sense.

This is the instance of **Stacks 06NW**
(`CategoryTheory.Functor.IsFibredOneMorphism.sheafAdjunctionInheritedTopology`) at the five
associated sites. -/
@[stacks 06TS "adjunction defining the morphism of topoi"]
public noncomputable def sheafAdjunction_associatedTopology
    [∀ (F : 𝒳.val.objᵒᵖ ⥤ A),
      (CatFiberedInGroupoids.homFunctor G).op.HasPointwiseRightKanExtension F] :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).2
    (CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous A
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) ⊣
      (CatFiberedInGroupoids.homFunctor G).sheafPushforwardCocontinuous A
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  (isFibredOneMorphism_homFunctor B S hS G).sheafAdjunctionInheritedTopology
    (baseOverTopology B S hS τ) A

end Functoriality

/-! ### The associated morphism of `τ` topoi (Stacks 06TT)

**Stacks 06TT** names the morphism of topoi that Stacks 06TS produces: for a 1-morphism
`G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of `S` and `τ` one of the
five topologies, `f = (f⁻¹, f_*) : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` is the *associated morphism of `τ` topoi*.

The source's `Sh(𝒳_τ)` is sheaves of sets, and for those the right Kan extension that `f_* = {}_pG`
is gets built here rather than postulated. Its value at an object `y` of `𝒴` is a limit indexed by
`CategoryTheory.StructuredArrow (Opposite.op y) G.op`, whose objects form a `Type (max v w)` and
whose morphisms a `Type w` when the two categories have objects in `Type v` and morphisms in
`Type w`; a `Type (max v w)` has limits of exactly that size, by
`CategoryTheory.Limits.Types.hasLimitsOfSize`, so those limits exist outright. That is
`AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor`, stated for any
coefficients with limits of that size, of which the source's sheaves of sets are the value at
`Type (max v w)`. `AlgebraicGeometry.BigFppfOver.sheafAdjunction_associatedSheaf` is then the
adjunction `f⁻¹ ⊣ f_*` between the two categories
`AlgebraicGeometry.BigFppfOver.AssociatedSheaf` of Stacks 06TR, for a 1-morphism of categories
fibred in groupoids and an `AlgebraicGeometry.SiteKind` and nothing else. Left exactness of `f⁻¹`
for those coefficients is
`AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_inverseImage_associatedTopology` at
`Type (max v w)`, whose `CategoryTheory.Limits.HasFiniteLimits` holds of every `Type`, so the pair
is a morphism of topoi in the source's sense.
-/

section AssociatedMorphismOfTopoi

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, w, u + 1, v} (BigFppfOver B S hS)} (G : 𝒳 ⟶ 𝒴)
  (τ : SiteKind)

/-- The limits that compute the right Kan extension along `G.op`, for a 1-morphism
`G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of `S`. They are the
limits of the functors indexed by `CategoryTheory.StructuredArrow (Opposite.op y) G.op` for the
objects `y` of `𝒴`, whose objects form a `Type (max v w)` and whose morphisms a `Type w` when
`𝒳` and `𝒴` have objects in `Type v` and morphisms in `Type w`, so
`CategoryTheory.Limits.HasLimitsOfSize.{w, max v w}` is exactly their size.

This is what the direct image `f_* = {}_pG` of Stacks 06TS is, so it is what makes that direct
image, and with it the morphism of topoi of Stacks 06TT, exist. -/
public instance hasPointwiseRightKanExtension_op_homFunctor (A : Type u₄) [Category.{v₄} A]
    [Limits.HasLimitsOfSize.{w, max v w} A] (F : 𝒳.val.objᵒᵖ ⥤ A) :
    (CatFiberedInGroupoids.homFunctor G).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- **Stacks 06TT.** The *associated morphism of `τ` topoi*
`f = (f⁻¹, f_*) : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` of a 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf category of `S`, for each of the five topologies `τ` — the Zariski,
étale, smooth, syntomic and fppf ones. It is the adjunction `f⁻¹ ⊣ f_*` between the two categories
`AlgebraicGeometry.BigFppfOver.AssociatedSheaf` of sheaves of sets on the associated sites of
Stacks 06TP, with `f⁻¹ = G^p` the restriction along `G` and `f_* = {}_pG` the right Kan extension
along `G.op`.

The limits that compute `f_*` are supplied by
`AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor`, a `Type (max v w)`
having limits of the shapes that index them by `CategoryTheory.Limits.Types.hasLimitsOfSize`, so
the data a reader must provide to obtain this morphism of topoi is a 1-morphism of categories
fibred in groupoids over `(Sch/S)_fppf` and a choice among the five topologies, which is what the
source provides. Left exactness of `f⁻¹`,
the remaining clause of "morphism of topoi", is
`AlgebraicGeometry.BigFppfOver.preservesFiniteLimits_inverseImage_associatedTopology` at these
same coefficients. -/
@[stacks 06TT "the associated morphism of tau topoi f = (f^{-1}, f_*), for each of the five"]
public noncomputable def sheafAdjunction_associatedSheaf :
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
    letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).2
    (CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous (Type max v w)
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) ⊣
      (CatFiberedInGroupoids.homFunctor G).sheafPushforwardCocontinuous (Type max v w)
        (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ) :=
  sheafAdjunction_associatedTopology B S hS G τ (Type max v w)

end AssociatedMorphismOfTopoi

end AlgebraicGeometry.BigFppfOver

end
