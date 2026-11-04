module

public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The criteria for a representable diagonal (Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Stacks 045G asserts that eight conditions on `𝒳` are
equivalent: that the diagonal `𝒳 ⟶ 𝒳 ×_S 𝒳` is representable by algebraic spaces; that every
isomorphism sheaf `Isom(x, y)` of two objects over a scheme is an algebraic space; that every
1-morphism from a scheme, respectively from a scheme-representable, respectively from an
algebraic-space-representable category fibred in groupoids, is representable by algebraic
spaces; and the three corresponding statements that the 2-fibre product of two such 1-morphisms
is representable by an algebraic space.

This file carries the eight conditions and the two auxiliary constructions they are stated
with. The seven equivalences themselves are **not** proved here; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.schemeFibredCategory`: a scheme over the base, presented as a
  category fibred in groupoids over the big fppf site of the base.
* `AlgebraicGeometry.Stack.twoFibreProduct`: the 2-fibre product of two 1-morphisms of
  categories fibred in groupoids over the site, with independent universes for all three total
  categories.
* `AlgebraicGeometry.Stack.HasRepresentableDiagonal`,
  `AlgebraicGeometry.Stack.IsAlgebraicSpaceIsomPresheaf`,
  `AlgebraicGeometry.Stack.IsRepresentableFromSchemes`,
  `AlgebraicGeometry.Stack.HasAlgebraicSpaceSchemePointProducts`,
  `AlgebraicGeometry.Stack.IsRepresentableFromRepresentableCategories`,
  `AlgebraicGeometry.Stack.HasAlgebraicSpaceRepresentableProducts`,
  `AlgebraicGeometry.Stack.IsRepresentableFromAlgebraicSpaces`,
  `AlgebraicGeometry.Stack.HasAlgebraicSpaceProducts`: the eight conditions of Stacks 045G, in
  the order in which the source lists them.

## Implementation notes

The category represented by a scheme `U` over the base is modelled by the slice of the big fppf
site of `S` over `U`, with the forgetful functor as structure functor; the iterated-slice
equivalence identifies that slice with the big fppf site of `U`, and the 2-Yoneda lemma
identifies its 1-morphisms into a category fibred in groupoids with the objects of the fibre
over `U`. Universal quantification over those 1-morphisms therefore expresses the source's
quantification over objects of fibres. The isomorphism presheaf is a presheaf on the slice and
is transported to the big fppf site of `U` along `CategoryTheory.Over.iteratedSliceBackward`.

The total category of `𝒳` has independent object and morphism universes, and 1-morphisms
between categories in different universes are `CategoryTheory.BasedFunctor`s, so a
scheme-valued point may retain the universes of the fixed site. Algebraicity of a possibly
large isomorphism presheaf means that it becomes isomorphic to an algebraic space after both
presheaves are lifted to a common value universe; no smallness of the total category of `𝒳` is
assumed. The auxiliary source categories of the last four conditions have independent universe
parameters, enlarged by the site universes so that lifted scheme categories are included in
each quantifier.

The seven equivalences of Stacks 045G — between conditions (1) and (2), (2) and (3), and so on
up to (7) and (8) — are **not** in this file.

They are **not** blocked on the three results they need from the chapters on algebraic spaces
and on bootstrapping: **all three are in the library**.
* The category of algebraic spaces over `S` has fibre products (Stacks 02X2):
  `AlgebraicGeometry.Space.isAlgebraicSpace_pullback` and
  `AlgebraicGeometry.Space.isPullback_fiberProduct` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Category.lean`, registered under the roles
  "algebraicity of the fibre product" and "universal property among algebraic spaces".
* An algebraic space over a scheme `U` over `S` is the same thing as an algebraic space over `S`
  with a morphism to `U` (Stacks 03I4): `AlgebraicGeometry.Space.isAlgebraicSpace_extend` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Extension.lean` and
  `AlgebraicGeometry.Space.restrict_representable` of
  `StacksFrontier/AlgebraicGeometry/Spaces/PointsAndCoverings/ChangeOfBaseScheme.lean`, which carry
  both directions.
* The bootstrap criterion, that the source of a morphism representable by algebraic spaces whose
  target is an algebraic space is itself an algebraic space (Stacks 02YS):
  `AlgebraicGeometry.Space.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentableByAlgebraicSpaces.lean`. This is what the
  source's proof of (6) ⇔ (7) goes through.

So what remains unproved here is the assembly of the equivalences themselves, not their inputs.
This note claims nothing about how much work that assembly is; it only withdraws a false claim
that the inputs are absent. The remaining equivalence, between
conditions (1) and (2), needs no result about algebraic spaces — it is Stacks 04SI
(`CategoryTheory.Functor.isFiberedInSetoids_and_isoClassPresheaf_iso_isomPresheaf`) together
with a comparison, not yet available, between an equivalence over the site with
`CategoryTheory.presheafOfCategories` of a presheaf and an isomorphism of that presheaf with
the presheaf of isomorphism classes of the fibres (Stacks 0045 and 04SD for a general presheaf;
`CategoryTheory.Functor.isoClassMap` is currently stated only for total categories sharing one
object universe and having the morphism universe of the site).

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂

/-- The category fibred in groupoids over the big fppf site of `S` represented by a scheme `U`
over `S`: the slice of the site over `U`, with the forgetful functor as structure functor. -/
abbrev schemeFibredCategory (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor.{u, u + 1, u, u + 1} (Over.forget.{u, u + 1} U))
    (Functor.IsFiberedInGroupoids.over_forget.{u, u + 1} U)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The 2-fibre product of two 1-morphisms of categories fibred in groupoids over the big fppf
site of `S`, with independent universes for all three total categories. -/
def twoFibreProduct
    (𝒯₁ : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
        x.toFunctor y.toFunctor))
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
      x.toFunctor y.toFunctor 𝒯₁.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids
      𝒳.isFiberedInGroupoids x.w y.w)

/-- Condition (1) of Stacks 045G: the diagonal of `𝒳` is representable by algebraic spaces. -/
abbrev HasRepresentableDiagonal : Prop :=
  let productCategory := BasedCategory.ofFunctor
    (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p
      (𝟭 (BigFppfOver B S hS)) 𝒳.val.p 𝒳.val.p)
  IsRepresentableByAlgebraicSpaces B S hS
    (𝒳 := 𝒳.val) (𝒴 := productCategory)
    { toFunctor := TwoFibreProductOver.diagonal (Functor.comp_id 𝒳.val.p)
      w := by rfl }

/-- Condition (2) of Stacks 045G: for every scheme `U` over `S` and all objects `x`, `y` of the
fibre of `𝒳` over `U`, the isomorphism sheaf `Isom(x, y)` is an algebraic space over `U`. The
comparison isomorphism is taken after universe lifts, so that the morphisms of the fibre may
live in any universe. -/
abbrev IsAlgebraicSpaceIsomPresheaf : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  ∀ (U : BigFppfOver B S hS) (x y : 𝒳.val.p.Fiber U),
    ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 F ∧
        Nonempty (F ⋙ uliftFunctor.{v, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x y) ⋙
            uliftFunctor.{u, v})

/-- Condition (3) of Stacks 045G: every 1-morphism to `𝒳` from the category represented by a
scheme over `S` is representable by algebraic spaces. -/
abbrev IsRepresentableFromSchemes : Prop :=
  ∀ (U : BigFppfOver B S hS) (x : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val),
    IsRepresentableByAlgebraicSpaces B S hS x

/-- Condition (4) of Stacks 045G: the 2-fibre product of any two scheme-valued points of `𝒳` is
representable by an algebraic space. -/
abbrev HasAlgebraicSpaceSchemePointProducts : Prop :=
  ∀ (U V : BigFppfOver B S hS)
    (x : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val)
    (y : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val),
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProduct B S hS 𝒳
        (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V) x y)

/-- Condition (5) of Stacks 045G: every 1-morphism to `𝒳` from a representable category fibred
in groupoids is representable by algebraic spaces. -/
abbrev IsRepresentableFromRepresentableCategories : Prop :=
  ∀ (𝒯 : CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) w₁} (BigFppfOver B S hS)),
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯.val.p →
    ∀ (x : 𝒯.val ⥤ᵇ 𝒳.val), IsRepresentableByAlgebraicSpaces B S hS x

/-- Condition (6) of Stacks 045G: the 2-fibre product over `𝒳` of any two representable
categories fibred in groupoids is representable by an algebraic space. -/
abbrev HasAlgebraicSpaceRepresentableProducts : Prop :=
  ∀ (𝒯₁ : CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) w₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, max u v₂, u + 1, max (u + 1) w₂} (BigFppfOver B S hS)),
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯₁.val.p →
    Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯₂.val.p →
    ∀ (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val),
      IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y)

/-- Condition (7) of Stacks 045G: every 1-morphism to `𝒳` from a category fibred in groupoids
representable by an algebraic space is representable by algebraic spaces. -/
abbrev IsRepresentableFromAlgebraicSpaces : Prop :=
  ∀ (𝒯 : CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) w₁} (BigFppfOver B S hS)),
    IsRepresentableByAlgebraicSpace B S hS 𝒯 →
    ∀ (x : 𝒯.val ⥤ᵇ 𝒳.val), IsRepresentableByAlgebraicSpaces B S hS x

/-- Condition (8) of Stacks 045G: the 2-fibre product over `𝒳` of any two categories fibred in
groupoids representable by algebraic spaces is representable by an algebraic space. -/
abbrev HasAlgebraicSpaceProducts : Prop :=
  ∀ (𝒯₁ : CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) w₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, max u v₂, u + 1, max (u + 1) w₂} (BigFppfOver B S hS)),
    IsRepresentableByAlgebraicSpace B S hS 𝒯₁ →
    IsRepresentableByAlgebraicSpace B S hS 𝒯₂ →
    ∀ (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val),
      IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y)

/-- Over a category fibred in groupoids the presheaf `Isom(x, y)` of Stacks 02ZB is the whole of
`Mor(x, y)`, every morphism of a fibre being invertible. -/
noncomputable def isomPresheafIsoMorPresheaf {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    (p : 𝒟 ⥤ 𝒞) [p.IsFibered] (hp : p.IsFiberedInGroupoids) {U : 𝒞} (x y : p.Fiber U) :
    p.isomPresheaf x y ≅ p.morPresheaf x y := by
  have h : p.isomSubpresheaf x y = ⊤ := by
    refine le_antisymm le_top fun V m _ => ?_
    have := hp.fiber_isGroupoid V.unop.left
    rw [Functor.mem_isomSubpresheaf_obj]
    infer_instance
  have hι : IsIso (p.isomSubpresheaf x y).ι := (p.isomSubpresheaf x y).eq_top_iff_isIso.mp h
  exact @asIso _ _ _ _ _ hι

end AlgebraicGeometry.Stack

end
