module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeIsomSiteSize
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomSchemeComparison
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import Mathlib.CategoryTheory.HomCongr

/-!
# The isomorphism presheaf of two degree-`d` covers is representable in the site

Let `S` be a scheme contained in a big fppf site, let `V` be an object of the big fppf site of
`S`, and let `c₁ : Z₁ ⟶ V` and `c₂ : Z₂ ⟶ V` be two morphisms of the site which are finite
locally free of degree `d`. Each of them gives a 1-morphism from the slice of the site at `V` to
the category `ℋ_d` of degree-`d` finite locally free covers, by base change
(`AlgebraicGeometry.Stack.finiteCoverPointFunctor`). The presheaf of *vertical* morphisms between
those two 1-morphisms is isomorphic to the presheaf represented by the object of the site
representing `Isom_V(Z₁, Z₂)`.

The dictionary has three layers, and each is a bijection at a fixed object `A` of the slice at
`V`, natural in `A`.

* A morphism of `ℋ_d` between the two base changes which lies over an identity of the base is
  the same thing as an **isomorphism of the two base changes over the base**.
* The slice of the site at `A.left` sits **fully faithfully** inside the slice, at the test
  object `A.left ⟶ V` read in schemes, of the schemes over the scheme underlying `V`; and the
  base change `Z ×_V A.left` formed in the site goes over to the product `Z ×_V T` formed in the
  schemes over the base scheme.
* An isomorphism `Z₁ ×_V T ≅ Z₂ ×_V T` over `T` is a morphism `T ⟶ Isom_V(Z₁, Z₂)` into the
  representing object of `Stacks.Morphisms.relativeIsomObj`, and that representing object lies
  in the site.

## Main definitions

* `AlgebraicGeometry.Stack.finiteCoverVertHomEquivIsoOver`: vertical morphisms of base changes
  are isomorphisms of the base changes over the base.
* `AlgebraicGeometry.Stack.siteSliceToTestSlice`: the embedding of the slice of the site at
  `A.left` into the schemes over the test object.
* `AlgebraicGeometry.Stack.siteSliceProdIso`: the image of the base change `Z ×_V A.left` under
  that embedding is the product `Z ×_V T`.
* `AlgebraicGeometry.Stack.finiteCoverProdIsomEquiv`: vertical morphisms of base changes are
  isomorphisms `Z₁ ×_V T ≅ Z₂ ×_V T` over `T`.
* `AlgebraicGeometry.Stack.finiteCoverVertHomSiteEquiv`: vertical morphisms of base changes are
  morphisms of the site into the object representing `Isom_V(Z₁, Z₂)`.
* `AlgebraicGeometry.Stack.finiteCoverVertHomPresheafIso`: the presheaf of vertical morphisms is
  isomorphic to the presheaf represented by that object.

## Main results

* `AlgebraicGeometry.Stack.finiteCoverProdIsomEquiv_naturality`: the dictionary is compatible
  with base change along a morphism of the slice at `V`.
* `AlgebraicGeometry.Stack.finiteCoverVertHomSiteEquiv_naturality`: restricting a vertical
  morphism is precomposing the corresponding morphism of the site.
* `AlgebraicGeometry.Stack.exists_siteObject_vertHomPresheafIso`: the presheaf of vertical
  morphisms is represented by an object of the site over `V`.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe u

open AlgebraicGeometry

namespace Stacks.Morphisms

variable {S : Scheme.{u}} {Z X W₁ W₂ V₁ V₂ : Over S}
  (e₁ : (relativeHom Z X).RepresentableBy W₁) (e₂ : (relativeHom X Z).RepresentableBy W₂)
  (e₃ : (relativeHom Z Z).RepresentableBy V₁) (e₄ : (relativeHom X X).RepresentableBy V₂)

/-- The first projection of the isomorphism of base changes named by `t : T ⟶ Isom_S(Z, X)` is
the relative morphism `t` names. -/
@[reassoc]
theorem relativeIsomObjEquivIso_hom_left_fst {T : Over S}
    (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    (relativeIsomObjEquivIso e₁ e₂ e₃ e₄ T t).hom.left ≫ prod.fst =
      toMor (relativeIsomFst e₁ e₂ e₃ e₄ t) := by
  change (relativeMorOverBase (relativeIsomFst e₁ e₂ e₃ e₄ t)).left ≫ prod.fst = _
  rw [relativeMorOverBase_left, prod.lift_fst]

/-- **The representing bijection of `Isom_S(Z, X)` is natural.** Precomposing with `h : T' ⟶ T`
base changes the isomorphism of base changes, read on first projections. -/
theorem relativeIsomObjEquivIso_comp_hom_left_fst {T T' : Over S} (h : T' ⟶ T)
    (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    (relativeIsomObjEquivIso e₁ e₂ e₃ e₄ T' (h ≫ t)).hom.left ≫ prod.fst =
      prod.map (𝟙 Z) h ≫ (relativeIsomObjEquivIso e₁ e₂ e₃ e₄ T t).hom.left ≫ prod.fst := by
  rw [relativeIsomObjEquivIso_hom_left_fst, relativeIsomObjEquivIso_hom_left_fst,
    relativeIsomFst_comp, toMor_map]

/-- An isomorphism of the two base changes over the test object is determined by the first
projection of its underlying morphism. -/
theorem isoProdOverBase_ext {T : Over S} {i j : prodOverBase Z T ≅ prodOverBase X T}
    (h : i.hom.left ≫ prod.fst = j.hom.left ≫ prod.fst) : i = j :=
  Iso.ext (Over.OverMorphism.ext (prod.hom_ext h ((Over.w i.hom).trans (Over.w j.hom).symm)))

end Stacks.Morphisms

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] finiteCoverPointObj finiteCoverProjection

/-- The underlying morphism of an isomorphism of a slice category is an isomorphism. -/
theorem isIso_left_of_iso {C : Type*} [Category* C] {W : C} {X Y : Over W} (e : X ≅ Y) :
    IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget W).map e.hom))

/-! ### Vertical morphisms of base changes -/

section Vertical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {V Z₁ Z₂ : BigFppfOver B S hS}

/-- The base component of a morphism of base changes lying over an identity is that identity. -/
theorem finiteCoverPointMap_f_eq_id (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) (φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A)
    (hφ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
      (𝟙 A.left) φ) : φ.f = 𝟙 A.left :=
  (CategoryTheory.IsHomLift.eq_of_isHomLift
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    (a := finiteCoverPointObj c₁ hc₁ A) (b := finiteCoverPointObj c₂ hc₂ A)
    (𝟙 A.left) φ).symm

/-- A vertical morphism of two base changes presents the first as the base change of the second
along an identity. -/
theorem isPullback_g_of_vertical (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) (φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A)
    (hφ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
      (𝟙 A.left) φ) :
    IsPullback φ.g (pullback.snd c₁ A.hom) (pullback.snd c₂ A.hom) (𝟙 A.left) :=
  finiteCoverPointMap_f_eq_id c₁ c₂ hc₁ hc₂ A φ hφ ▸ φ.square

/-- **The cover component of a vertical morphism of two base changes is an isomorphism.** -/
theorem isIso_g_of_vertical (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) (φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A)
    (hφ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
      (𝟙 A.left) φ) : IsIso φ.g :=
  (isPullback_g_of_vertical c₁ c₂ hc₁ hc₂ A φ hφ).isIso_fst_of_isIso

/-- An isomorphism of the two base changes over the base presents the first as the base change
of the second along an identity. -/
theorem isPullback_left_of_isoOver (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V) (A : Over V)
    (e : Over.mk (pullback.snd c₁ A.hom) ≅ Over.mk (pullback.snd c₂ A.hom)) :
    IsPullback e.hom.left (pullback.snd c₁ A.hom) (pullback.snd c₂ A.hom) (𝟙 A.left) := by
  have : IsIso e.hom.left := isIso_left_of_iso e
  exact IsPullback.of_horiz_isIso ⟨(Over.w e.hom).trans (Category.comp_id _).symm⟩

/-- **A vertical morphism of two base changes is an isomorphism of them over the base.** The
bijection sends a morphism of `ℋ_d` lying over `𝟙 A.left` to its cover component. -/
def finiteCoverVertHomEquivIsoOver (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) :
    {φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A.left) φ} ≃
      (Over.mk (pullback.snd c₁ A.hom) ≅ Over.mk (pullback.snd c₂ A.hom)) where
  toFun φ :=
    haveI : IsIso φ.1.g := isIso_g_of_vertical c₁ c₂ hc₁ hc₂ A φ.1 φ.2
    Over.isoMk (asIso φ.1.g)
      ((isPullback_g_of_vertical c₁ c₂ hc₁ hc₂ A φ.1 φ.2).w.trans (Category.comp_id _))
  invFun e :=
    ⟨⟨𝟙 A.left, e.hom.left, isPullback_left_of_isoOver c₁ c₂ A e⟩,
      CategoryTheory.IsHomLift.of_fac'
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) _ _ rfl rfl rfl⟩
  left_inv φ :=
    Subtype.ext (FiniteCover.Hom.ext (finiteCoverPointMap_f_eq_id c₁ c₂ hc₁ hc₂ A φ.1 φ.2).symm rfl)
  right_inv _ := Iso.ext (Over.OverMorphism.ext rfl)

/-- The isomorphism over the base attached to a vertical morphism has the cover component of
that morphism as its underlying morphism. -/
@[simp]
theorem finiteCoverVertHomEquivIsoOver_apply_hom_left (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) (φ : {φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A.left) φ}) :
    (finiteCoverVertHomEquivIsoOver c₁ c₂ hc₁ hc₂ A φ).hom.left = φ.1.g :=
  rfl

end Vertical

/-! ### The slice of the site inside the schemes over the base scheme -/

section Crossing

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V Z : BigFppfOver B S hS}

/-- **The slice of the site at a test object, inside the schemes over the base scheme.** For an
object `A` of the slice of the big fppf site of `S` at `V`, the slice of the site at `A.left`
embeds fully faithfully in the slice, at the test object `A.left ⟶ V` read in schemes, of the
category of schemes over the scheme underlying `V`. -/
def siteSliceToTestSlice (A : Over V) :
    Over A.left ⥤ Over (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom)) :=
  Over.iteratedSliceForward A.left ⋙ Over.post B.inclusion ⋙
    Over.iteratedSliceBackward (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))

/-- The embedding `AlgebraicGeometry.Stack.siteSliceToTestSlice A` is fully faithful. -/
def siteSliceToTestSliceFullyFaithful (A : Over V) :
    (siteSliceToTestSlice A).FullyFaithful :=
  ((Over.iteratedSliceEquiv A.left).fullyFaithfulFunctor.comp
      (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion))).comp
    (Over.iteratedSliceEquiv
      (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).symm.fullyFaithfulFunctor

/-- `Z ×_V T`, as an object of the schemes over the test object attached to `A`: the image of
the base change of `c` along `A` under `AlgebraicGeometry.Stack.siteSliceToTestSlice`. -/
abbrev finiteCoverTestProd (c : Z ⟶ V) (A : Over V) :
    Over (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom)) :=
  Over.mk (Over.homMk
    (U := Over.mk ((BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom) ≫
      (BigFppfOver.toScheme B S hS).map A.hom))
    ((BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom)) rfl)

/-- The image of the base change of `c` along `A` under
`AlgebraicGeometry.Stack.siteSliceToTestSlice` is `AlgebraicGeometry.Stack.finiteCoverTestProd`. -/
theorem siteSliceToTestSlice_obj_pullback (c : Z ⟶ V) (A : Over V) :
    (siteSliceToTestSlice A).obj (Over.mk (pullback.snd c A.hom)) =
      finiteCoverTestProd c A :=
  rfl

/-- **The base change of a morphism of the site is the product in the slice over the base
scheme.** The image under `AlgebraicGeometry.Stack.siteSliceToTestSlice` of the base change of
`c` along `A` is the object `Z ×_V T` of the schemes over the test object. -/
def siteSliceProdIso (c : Z ⟶ V) (A : Over V) :
    finiteCoverTestProd c A ≅
      prodOverBase (Over.mk ((BigFppfOver.toScheme B S hS).map c))
        (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom)) :=
  Over.isoMk
    (Over.isoMk
      ((BigFppfOver.toScheme B S hS).mapIso (pullbackSymmetry c A.hom) ≪≫
        Space.prodLeftIso c A.hom)
      (by
        change ((BigFppfOver.toScheme B S hS).map (pullbackSymmetry c A.hom).hom ≫
            (Space.prodLeftIso c A.hom).hom) ≫
          (Over.mk ((BigFppfOver.toScheme B S hS).map c) ⨯
            Over.mk ((BigFppfOver.toScheme B S hS).map A.hom)).hom =
          (BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom) ≫
            (BigFppfOver.toScheme B S hS).map A.hom
        rw [Category.assoc, Space.prodLeftIso_hom_comp_hom, ← Functor.map_comp,
          ← Functor.map_comp, ← Category.assoc, pullbackSymmetry_hom_comp_snd,
          pullback.condition]))
    (by
      refine Over.OverMorphism.ext ?_
      change ((BigFppfOver.toScheme B S hS).map (pullbackSymmetry c A.hom).hom ≫
          (Space.prodLeftIso c A.hom).hom) ≫
        (prod.snd (X := Over.mk ((BigFppfOver.toScheme B S hS).map c))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).left =
        (BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom)
      rw [Category.assoc, Space.prodLeftIso_hom_snd, ← Functor.map_comp,
        pullbackSymmetry_hom_comp_fst])

/-- The underlying morphism of schemes of `siteSliceProdIso c A` is the image of the symmetry of
the pullback followed by the comparison with the product. -/
private theorem siteSliceProdIso_hom_left_left (c : Z ⟶ V) (A : Over V) :
    (siteSliceProdIso c A).hom.left.left =
      (BigFppfOver.toScheme B S hS).map (pullbackSymmetry c A.hom).hom ≫
        (Space.prodLeftIso c A.hom).hom :=
  rfl

/-- Followed by the first projection of `Z ×_V T`, the comparison
`AlgebraicGeometry.Stack.siteSliceProdIso` is the first projection of the base change. -/
@[reassoc]
theorem siteSliceProdIso_hom_left_fst (c : Z ⟶ V) (A : Over V) :
    (siteSliceProdIso c A).hom.left.left ≫
        (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map c))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).left =
      (BigFppfOver.toScheme B S hS).map (pullback.fst c A.hom) := by
  rw [siteSliceProdIso_hom_left_left, Category.assoc, Space.prodLeftIso_hom_fst, ← Functor.map_comp,
    pullbackSymmetry_hom_comp_snd]

/-- Followed by the second projection of `Z ×_V T`, the comparison
`AlgebraicGeometry.Stack.siteSliceProdIso` is the second projection of the base change. -/
@[reassoc]
theorem siteSliceProdIso_hom_left_snd (c : Z ⟶ V) (A : Over V) :
    (siteSliceProdIso c A).hom.left.left ≫
        (prod.snd (X := Over.mk ((BigFppfOver.toScheme B S hS).map c))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).left =
      (BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom) := by
  rw [siteSliceProdIso_hom_left_left, Category.assoc, Space.prodLeftIso_hom_snd, ← Functor.map_comp,
    pullbackSymmetry_hom_comp_fst]

end Crossing

/-! ### Base change of the comparison -/

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {V Z : BigFppfOver B S hS}

/-- The morphism of test objects induced by a morphism of the slice of the site at `V`. -/
def finiteCoverTestMap {A' A : Over V} (H : A' ⟶ A) :
    Over.mk ((BigFppfOver.toScheme B S hS).map A'.hom) ⟶
      Over.mk ((BigFppfOver.toScheme B S hS).map A.hom) :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map H.left)
    (((BigFppfOver.toScheme B S hS).map_comp H.left A.hom).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (Over.w H)))

/-- The underlying morphism of `AlgebraicGeometry.Stack.finiteCoverTestMap H` is the image of
`H.left` in schemes. -/
@[simp]
theorem finiteCoverTestMap_left {A' A : Over V} (H : A' ⟶ A) :
    (finiteCoverTestMap H).left = (BigFppfOver.toScheme B S hS).map H.left :=
  rfl

/-- The morphism of base changes over the base scheme induced by a morphism of the slice of the
site at `V`: the image of the gap-filler of
`AlgebraicGeometry.Stack.finiteCoverPointMap`. -/
def finiteCoverProdMap (c : Z ⟶ V)
    (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c) d)
    {A' A : Over V} (H : A' ⟶ A) :
    (finiteCoverTestProd c A').left ⟶ (finiteCoverTestProd c A).left :=
  Over.homMk ((BigFppfOver.toScheme B S hS).map (finiteCoverPointMap c hc H).g) (by
    change (BigFppfOver.toScheme B S hS).map (finiteCoverPointMap c hc H).g ≫
        (BigFppfOver.toScheme B S hS).map (pullback.snd c A.hom) ≫
          (BigFppfOver.toScheme B S hS).map A.hom =
      (BigFppfOver.toScheme B S hS).map (pullback.snd c A'.hom) ≫
        (BigFppfOver.toScheme B S hS).map A'.hom
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      finiteCoverPointMap_g_comp_snd, Category.assoc, Over.w H])

/-- The underlying morphism of `AlgebraicGeometry.Stack.finiteCoverProdMap c hc H` is the image
in schemes of the gap-filler of `AlgebraicGeometry.Stack.finiteCoverPointMap`. -/
@[simp]
theorem finiteCoverProdMap_left (c : Z ⟶ V)
    (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c) d)
    {A' A : Over V} (H : A' ⟶ A) :
    (finiteCoverProdMap c hc H).left =
      (BigFppfOver.toScheme B S hS).map (finiteCoverPointMap c hc H).g :=
  rfl

/-- **The base change of `Z ×_V T` along a morphism of test objects is the gap-filler.**
Following the comparison `AlgebraicGeometry.Stack.siteSliceProdIso` with the base change of
`Z ×_V T` is the same as following the gap-filler of
`AlgebraicGeometry.Stack.finiteCoverPointMap` with that comparison. -/
@[reassoc]
theorem siteSliceProdIso_hom_comp_prodMap (c : Z ⟶ V)
    (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c) d)
    {A' A : Over V} (H : A' ⟶ A) :
    (siteSliceProdIso c A').hom.left ≫
        prod.map (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map c))) (finiteCoverTestMap H) =
      finiteCoverProdMap c hc H ≫ (siteSliceProdIso c A).hom.left := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, Category.comp_id, Category.assoc]
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, siteSliceProdIso_hom_left_fst, finiteCoverProdMap_left]
    rw [← Functor.map_comp, finiteCoverPointMap_g_comp_fst]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, finiteCoverProdMap_left, finiteCoverTestMap_left]
    rw [siteSliceProdIso_hom_left_snd, Category.assoc, siteSliceProdIso_hom_left_snd,
      ← Functor.map_comp, ← Functor.map_comp, finiteCoverPointMap_g_comp_snd]

end BaseChange


/-! ### The dictionary at a fixed test object -/

section Dictionary

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {V Z₁ Z₂ : BigFppfOver B S hS}

/-- For an isomorphism `e` of an iterated slice category, `e.hom.left.left ≫ e.inv.left.left`
is the identity. -/
@[reassoc]
theorem iso_hom_inv_left_left {C : Type*} [Category* C] {W₀ : C} {W : Over W₀}
    {X Y : Over W} (e : X ≅ Y) : e.hom.left.left ≫ e.inv.left.left = 𝟙 X.left.left := by
  simpa only [Over.comp_left, Over.id_left] using
    congrArg (fun k : X ⟶ X ↦ k.left.left) e.hom_inv_id

/-- The underlying morphism of schemes of the image of `k` under
`AlgebraicGeometry.Stack.siteSliceToTestSlice A` is the image of `k.left` in schemes. -/
@[simp]
theorem siteSliceToTestSlice_map_left_left {V : BigFppfOver B S hS} (A : Over V)
    {X Y : Over A.left} (k : X ⟶ Y) :
    ((siteSliceToTestSlice A).map k).left.left = (BigFppfOver.toScheme B S hS).map k.left :=
  rfl

/-- Isomorphisms over `A.left` of the two base changes of `c₁` and `c₂` along `A`, formed in the
site, are the same thing as isomorphisms of their images `finiteCoverTestProd c₁ A` and
`finiteCoverTestProd c₂ A` in the schemes over the test object attached to `A`. -/
def finiteCoverTestProdIsoEquiv (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V) (A : Over V) :
    (Over.mk (pullback.snd c₁ A.hom) ≅ Over.mk (pullback.snd c₂ A.hom)) ≃
      (finiteCoverTestProd c₁ A ≅ finiteCoverTestProd c₂ A) :=
  (siteSliceToTestSliceFullyFaithful A).isoEquiv

/-- The underlying morphism of schemes of `finiteCoverTestProdIsoEquiv c₁ c₂ A e` is the image
of `e.hom.left` in schemes. -/
@[simp]
theorem finiteCoverTestProdIsoEquiv_hom_left_left (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V) (A : Over V)
    (e : Over.mk (pullback.snd c₁ A.hom) ≅ Over.mk (pullback.snd c₂ A.hom)) :
    (finiteCoverTestProdIsoEquiv c₁ c₂ A e).hom.left.left =
      (BigFppfOver.toScheme B S hS).map e.hom.left :=
  rfl

/-- **A vertical morphism of two base changes is an isomorphism of `Z₁ ×_V T` with `Z₂ ×_V T`
over `T`.** -/
def finiteCoverProdIsomEquiv (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) :
    {φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A.left) φ} ≃
      (prodOverBase (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
          (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom)) ≅
        prodOverBase (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
          (Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))) :=
  (finiteCoverVertHomEquivIsoOver c₁ c₂ hc₁ hc₂ A).trans
    ((finiteCoverTestProdIsoEquiv c₁ c₂ A).trans
      (Iso.isoCongr (siteSliceProdIso c₁ A) (siteSliceProdIso c₂ A)))

/-- The defining factorisation of the dictionary: the first projection of the isomorphism of
base changes attached to a vertical morphism is its cover component. -/
theorem finiteCoverProdIsomEquiv_fac (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (A : Over V) (φ : {φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A.left) φ}) :
    (siteSliceProdIso c₁ A).hom.left.left ≫
        (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A φ).hom.left.left ≫
          (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
            (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).left =
      (BigFppfOver.toScheme B S hS).map (φ.1.g ≫ pullback.fst c₂ A.hom) := by
  have hhom : (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A φ).hom =
      (siteSliceProdIso c₁ A).inv ≫
        (finiteCoverTestProdIsoEquiv c₁ c₂ A
          (finiteCoverVertHomEquivIsoOver c₁ c₂ hc₁ hc₂ A φ)).hom ≫
        (siteSliceProdIso c₂ A).hom := rfl
  rw [hhom]
  simp only [Over.comp_left, Category.assoc, iso_hom_inv_left_left_assoc,
    finiteCoverTestProdIsoEquiv_hom_left_left, finiteCoverVertHomEquivIsoOver_apply_hom_left,
    siteSliceProdIso_hom_left_fst]
  exact ((BigFppfOver.toScheme B S hS).map_comp φ.1.g (pullback.fst c₂ A.hom)).symm

/-- **The dictionary is compatible with base change.** If a vertical morphism over `A'` and one
over `A` are related by the gap-filler square of a morphism `A' ⟶ A`, then the isomorphism of
base changes attached to the first is the base change of the one attached to the second. -/
theorem finiteCoverProdIsomEquiv_naturality (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    {A' A : Over V} (H : A' ⟶ A)
    (φ : {φ : finiteCoverPointObj c₁ hc₁ A ⟶ finiteCoverPointObj c₂ hc₂ A //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A.left) φ})
    (ρ : {φ : finiteCoverPointObj c₁ hc₁ A' ⟶ finiteCoverPointObj c₂ hc₂ A' //
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift
          (𝟙 A'.left) φ})
    (hρ : ρ.1 ≫ finiteCoverPointMap c₂ hc₂ H = finiteCoverPointMap c₁ hc₁ H ≫ φ.1) :
    (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A' ρ).hom.left ≫ prod.fst =
      prod.map (𝟙 (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))) (finiteCoverTestMap H) ≫
        (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A φ).hom.left ≫ prod.fst := by
  have : IsIso (siteSliceProdIso c₁ A').hom.left :=
    isIso_left_of_iso (siteSliceProdIso c₁ A')
  refine (cancel_epi (siteSliceProdIso c₁ A').hom.left).mp ?_
  refine Eq.trans ?_ (siteSliceProdIso_hom_comp_prodMap_assoc c₁ hc₁ H
    ((finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A φ).hom.left ≫ prod.fst)).symm
  refine Over.OverMorphism.ext ?_
  have hg : ρ.1.g ≫ (finiteCoverPointMap c₂ hc₂ H).g =
      (finiteCoverPointMap c₁ hc₁ H).g ≫ φ.1.g := congrArg FiniteCover.Hom.g hρ
  have key : ρ.1.g ≫ pullback.fst c₂ A'.hom =
      (finiteCoverPointMap c₁ hc₁ H).g ≫ φ.1.g ≫ pullback.fst c₂ A.hom := by
    rw [← finiteCoverPointMap_g_comp_fst c₂ hc₂ H, ← Category.assoc, hg, Category.assoc]
  change (siteSliceProdIso c₁ A').hom.left.left ≫
      (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A' ρ).hom.left.left ≫
        (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
          (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A'.hom))).left =
    (BigFppfOver.toScheme B S hS).map (finiteCoverPointMap c₁ hc₁ H).g ≫
      (siteSliceProdIso c₁ A).hom.left.left ≫
        (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ A φ).hom.left.left ≫
          (prod.fst (X := Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
            (Y := Over.mk ((BigFppfOver.toScheme B S hS).map A.hom))).left
  rw [finiteCoverProdIsomEquiv_fac, finiteCoverProdIsomEquiv_fac, key]
  exact (BigFppfOver.toScheme B S hS).map_comp _ _

end Dictionary

/-! ### The presheaf of vertical morphisms is representable in the site -/

section Presheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {V Z₁ Z₂ : BigFppfOver B S hS}

/-- The base-change 1-morphism into `ℋ_d`, precomposed with the iterated-slice functor and
followed by the projection of `ℋ_d`, is `CategoryTheory.Over.map V.hom`. -/
theorem finiteCoverPointFunctor_backward_comp (c : Z₁ ⟶ V)
    (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c) d) :
    (Over.iteratedSliceBackward V ⋙ finiteCoverPointFunctor c hc) ⋙
      finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d) = Over.map V.hom :=
  rfl

/-- Taking preimages under a fully faithful functor is compatible with composition. -/
theorem fullyFaithful_preimage_comp {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {X Y W : C} (f : X ⟶ Y) (g : F.obj Y ⟶ F.obj W) :
    hF.preimage (F.map f ≫ g) = f ≫ hF.preimage g :=
  hF.map_injective (by rw [hF.map_preimage, F.map_comp, hF.map_preimage])

/-- The bijection, for two objects of the slice of the site at `V.left`, between their
morphisms in the site and the morphisms of their images in the schemes over the scheme
underlying `V.left`. -/
def siteHomEquiv (a I : Over V.left) :
    (a ⟶ I) ≃ ((Over.post (X := V.left) B.inclusion).obj a ⟶
      (Over.post (X := V.left) B.inclusion).obj I) :=
  (Functor.FullyFaithful.ofFullyFaithful (Over.post (X := V.left) B.inclusion)).homEquiv

/-- The inverse of `AlgebraicGeometry.Stack.siteHomEquiv` is compatible with precomposition. -/
theorem siteHomEquiv_symm_comp {a' a I : Over V.left} (h : a' ⟶ a)
    (t : (Over.post (X := V.left) B.inclusion).obj a ⟶
      (Over.post (X := V.left) B.inclusion).obj I) :
    (siteHomEquiv a' I).symm ((Over.post (X := V.left) B.inclusion).map h ≫ t) =
      h ≫ (siteHomEquiv a I).symm t :=
  fullyFaithful_preimage_comp
    (Functor.FullyFaithful.ofFullyFaithful (Over.post (X := V.left) B.inclusion)) h t

variable {W₁ W₂ V₁ V₂ : Over ((BigFppfOver.toScheme B S hS).obj V)}

/-- **The dictionary at one object of the slice.** A vertical morphism between the two
base-change 1-morphisms into `ℋ_d` is a morphism of the site into the object representing
`Isom_V(Z₁, Z₂)`. -/
def finiteCoverVertHomSiteEquiv (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (e₁ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy W₁)
    (e₂ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy W₂)
    (e₃ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy V₁)
    (e₄ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy V₂)
    (hI : B.Contains (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).left) (a : Over V.left) :
    VertHom (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) (Over.map V.hom)
        (Over.iteratedSliceBackward V ⋙ finiteCoverPointFunctor c₁ hc₁)
        (Over.iteratedSliceBackward V ⋙ finiteCoverPointFunctor c₂ hc₂) a ≃
      (a ⟶ siteObject B V.left.1 V.left.2 hI
        (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).hom) :=
  (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ ((Over.iteratedSliceBackward V).obj a)).trans
    ((Stacks.Morphisms.relativeIsomObjEquivIso e₁ e₂ e₃ e₄
        (Over.mk ((BigFppfOver.toScheme B S hS).map
          ((Over.iteratedSliceBackward V).obj a).hom))).symm.trans
      (siteHomEquiv a (siteObject B V.left.1 V.left.2 hI
        (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).hom)).symm)

/-- **The dictionary is natural.** Restricting a vertical morphism along a morphism of the slice
is precomposing the corresponding morphism of the site with it. -/
theorem finiteCoverVertHomSiteEquiv_naturality (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (e₁ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy W₁)
    (e₂ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy W₂)
    (e₃ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy V₁)
    (e₄ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy V₂)
    (hI : B.Contains (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).left)
    {a' a : Over V.left} (h : a' ⟶ a)
    (φ : VertHom (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
      (Over.map V.hom) (Over.iteratedSliceBackward V ⋙ finiteCoverPointFunctor c₁ hc₁)
      (Over.iteratedSliceBackward V ⋙ finiteCoverPointFunctor c₂ hc₂) a) :
    finiteCoverVertHomSiteEquiv c₁ c₂ hc₁ hc₂ e₁ e₂ e₃ e₄ hI a'
        (VertHom.restrict isFiberedInGroupoids_finiteCoverProjection
          (finiteCoverPointFunctor_backward_comp c₁ hc₁)
          (finiteCoverPointFunctor_backward_comp c₂ hc₂) h φ) =
      h ≫ finiteCoverVertHomSiteEquiv c₁ c₂ hc₁ hc₂ e₁ e₂ e₃ e₄ hI a φ := by
  have hiso : Stacks.Morphisms.relativeIsomObjEquivIso e₁ e₂ e₃ e₄
        (Over.mk ((BigFppfOver.toScheme B S hS).map
          ((Over.iteratedSliceBackward V).obj a').hom))
        (finiteCoverTestMap ((Over.iteratedSliceBackward V).map h) ≫
          (Stacks.Morphisms.relativeIsomObjEquivIso e₁ e₂ e₃ e₄ _).symm
            (finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂
              ((Over.iteratedSliceBackward V).obj a) φ)) =
      finiteCoverProdIsomEquiv c₁ c₂ hc₁ hc₂ ((Over.iteratedSliceBackward V).obj a')
        (VertHom.restrict isFiberedInGroupoids_finiteCoverProjection
          (finiteCoverPointFunctor_backward_comp c₁ hc₁)
          (finiteCoverPointFunctor_backward_comp c₂ hc₂) h φ) := by
    refine (Stacks.Morphisms.isoProdOverBase_ext ?_).symm
    rw [Stacks.Morphisms.relativeIsomObjEquivIso_comp_hom_left_fst, Equiv.apply_symm_apply]
    exact finiteCoverProdIsomEquiv_naturality c₁ c₂ hc₁ hc₂
      ((Over.iteratedSliceBackward V).map h) φ _
      (VertHom.restrict_fac isFiberedInGroupoids_finiteCoverProjection
        (finiteCoverPointFunctor_backward_comp c₁ hc₁)
        (finiteCoverPointFunctor_backward_comp c₂ hc₂) h φ)
  change (siteHomEquiv a' (siteObject B V.left.1 V.left.2 hI
      (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).hom)).symm _ = _
  rw [← hiso, Equiv.symm_apply_apply]
  exact siteHomEquiv_symm_comp h _

/-- **The presheaf of vertical morphisms between two base-change 1-morphisms into `ℋ_d` is
represented by an object of the site.** -/
def finiteCoverVertHomPresheafIso (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d)
    (e₁ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy W₁)
    (e₂ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy W₂)
    (e₃ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₁))).RepresentableBy V₁)
    (e₄ : (AlgebraicGeometry.relativeHom (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))
      (Over.mk ((BigFppfOver.toScheme B S hS).map c₂))).RepresentableBy V₂)
    (hI : B.Contains (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).left) :
    VertHom.presheaf (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
          (d := d))
        (finiteCoverPointFunctor_backward_comp c₁ hc₁)
        (finiteCoverPointFunctor_backward_comp c₂ hc₂) ≅
      yoneda.obj (siteObject B V.left.1 V.left.2 hI
        (Stacks.Morphisms.relativeIsomObj e₁ e₂ e₃ e₄).hom) :=
  NatIso.ofComponents
    (fun a ↦ Equiv.toIso (finiteCoverVertHomSiteEquiv c₁ c₂ hc₁ hc₂ e₁ e₂ e₃ e₄ hI a.unop))
    fun h ↦ by
      ext φ
      exact finiteCoverVertHomSiteEquiv_naturality c₁ c₂ hc₁ hc₂ e₁ e₂ e₃ e₄ hI h.unop φ

/-- **The presheaf of vertical morphisms between the two base-change 1-morphisms of two
degree-`d` covers of `V` is representable by an object of the site over `V`.** -/
theorem exists_siteObject_vertHomPresheafIso (c₁ : Z₁ ⟶ V) (c₂ : Z₂ ⟶ V)
    (hc₁ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₁) d)
    (hc₂ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c₂) d) :
    ∃ I : BigFppfOver B V.left.1 V.left.2,
      Nonempty (VertHom.presheaf (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S)
            (hS := hS) (d := d))
          (finiteCoverPointFunctor_backward_comp c₁ hc₁)
          (finiteCoverPointFunctor_backward_comp c₂ hc₂) ≅ yoneda.obj I) := by
  have : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map c₁) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  have : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map c₂) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  obtain ⟨W₁, W₂, V₁, V₂, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, ⟨e₄⟩⟩ :=
    Stacks.Morphisms.exists_representableBy_four ((BigFppfOver.toScheme B S hS).map c₁)
      ((BigFppfOver.toScheme B S hS).map c₂)
  exact ⟨_, ⟨finiteCoverVertHomPresheafIso c₁ c₂ hc₁ hc₂ e₁ e₂ e₃ e₄
    (Space.contains_relativeIsomObj_left c₁ c₂ e₁ e₂ e₃ e₄)⟩⟩

end Presheaf

end AlgebraicGeometry.Stack

end
