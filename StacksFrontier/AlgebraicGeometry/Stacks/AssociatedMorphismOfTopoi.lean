module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSheaves
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The morphism of topoi of a 1-morphism of categories fibred in groupoids (Stacks 06TS)

Let `S` be a scheme contained in a big fppf site `B`, let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over the big fppf category `(Sch/S)_fppf`, and let `τ` be one of the
five topologies Zariski, étale, smooth, syntomic, fppf. Restriction of presheaves along `f`,
`f^p 𝒢 = 𝒢 ∘ f`, has as right adjoint the pushforward of presheaves `{}_pf` of Stacks 06TK, with
value `({}_pf ℱ)(y) = lim_{f(x) → y} ℱ(x)` at an object `y` of `𝒴`: the right Kan extension of
`ℱ` along `f`. **Stacks 06TS** says that both functors carry `τ` sheaves of sets to `τ` sheaves of
sets and that the resulting pair is a morphism of topoi `Sh(𝒳_τ) ⟶ Sh(𝒴_τ)`.

The limits computing `{}_pf ℱ` are indexed by the comma categories of pairs `(x, f(x) → y)`, whose
objects form a `Type (max v w)` and whose morphisms a `Type w` when `𝒳` and `𝒴` have objects in
`Type v` and morphisms in `Type w`. Sets in any universe containing `Type (max v w)` have limits
of that size (`AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor`), so for
sheaves of sets with values in `Type (max v w t)` the pushforward exists and nothing is assumed:
the statements below take a 1-morphism `f` and a topology `τ` and nothing else.

## Main results

* `AlgebraicGeometry.BigFppfOver.presheafAdjunction` and
  `AlgebraicGeometry.BigFppfOver.presheafPushforwardObjObjIsoLimit`: **Stacks 06TK**, the pullback
  `f^p` and pushforward `{}_pf` of presheaves of sets, their adjointness, and the limit formula for
  `{}_pf`.
* `AlgebraicGeometry.BigFppfOver.isSheaf_comp_op_and_isSheaf_ran_obj`: **Stacks 06TS**, the
  pullback `f^p` and the pushforward `{}_pf` of presheaves of sets carry `τ` sheaves to `τ`
  sheaves.
* `AlgebraicGeometry.BigFppfOver.morphismOfTopoi_associatedSheaf`: **Stacks 06TS**, the morphism of
  topoi `f : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` they define, as a `CategoryTheory.MorphismOfTopoi`: the adjunction
  `f⁻¹ ⊣ f_*` together with left exactness of `f⁻¹`.
* `BigFppfOver.morphismOfTopoi_associatedSheaf_pushforwardCompSheafToPresheafIso` and
  `BigFppfOver.morphismOfTopoi_associatedSheaf_inverseImageCompSheafToPresheafIso`: **Stacks
  06TS**, the two functors of that morphism of topoi are `{}_pf` and `f^p` on underlying
  presheaves.

## Implementation notes

The source's `Sh(𝒳_τ)` is the category of sheaves of sets. Here it is
`AlgebraicGeometry.BigFppfOver.AssociatedSheaf` with values in `Type (max v w t)`: the universe of
sets must contain the size of the comma categories indexing the limits of `{}_pf`, which is the
set-theoretic convention under which the source's limits exist, and `t` lets that universe be as
large as wanted. The functors are Mathlib's `CategoryTheory.Functor.sheafPushforwardContinuous`
(precomposition with `f.op`) and `CategoryTheory.Functor.sheafPushforwardCocontinuous` (right Kan
extension along `f.op`), which exist because `f` is continuous and cocontinuous for the associated
topologies, `AlgebraicGeometry.BigFppfOver.isContinuous_and_isCocontinuous_associatedTopology`.

## References

* [Stacks Project, Tag 06TK](https://stacks.math.columbia.edu/tag/06TK)
* [Stacks Project, Tag 06TS](https://stacks.math.columbia.edu/tag/06TS)
-/

@[expose] public section

open CategoryTheory

universe u v w t

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, w, u + 1, v} (BigFppfOver B S hS)} (G : 𝒳 ⟶ 𝒴)
  (τ : SiteKind)

/-- **Stacks 06TK**, the pullback and pushforward of presheaves and their adjointness. For a
1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of `S`, the
pullback `G^p : PSh(𝒴) ⥤ PSh(𝒳)` of presheaves of sets is precomposition with `G.op`, so that
`G^p 𝒢 (x) = 𝒢 (G x)` by definition, and the pushforward `{}_pG : PSh(𝒳) ⥤ PSh(𝒴)` is the right
Kan extension along `G.op`; `G^p` is left adjoint to `{}_pG`. -/
@[stacks 06TK "presheaf pullback f^p, pushforward {}_pf, and the adjunction f^p ⊣ {}_pf"]
noncomputable def presheafAdjunction :
    (Functor.whiskeringLeft _ _ (Type max v w t)).obj (CatFiberedInGroupoids.homFunctor G).op ⊣
      (CatFiberedInGroupoids.homFunctor G).op.ran :=
  (CatFiberedInGroupoids.homFunctor G).op.ranAdjunction _

/-- **Stacks 06TK**, the formula `({}_pG ℱ)(y) = lim_{G(x) → y} ℱ(x)` for the pushforward of a
presheaf of sets `ℱ` on `𝒳` along a 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over
the big fppf category of `S`, at an object `y` of `𝒴`: the limit is indexed by the pairs of an
object `x` of `𝒳` and a morphism `G(x) → y`. -/
@[stacks 06TK "the formula ({}_pf F)(y) = lim_{f(x) -> y} F(x) for the pushforward"]
noncomputable def presheafPushforwardObjObjIsoLimit (ℱ : 𝒳.val.objᵒᵖ ⥤ Type (max v w t))
    (y : 𝒴.val.obj) :
    ((CatFiberedInGroupoids.homFunctor G).op.ran.obj ℱ).obj (Opposite.op y) ≅
      Limits.limit (StructuredArrow.proj (Opposite.op y) (CatFiberedInGroupoids.homFunctor G).op ⋙
        ℱ) :=
  (CatFiberedInGroupoids.homFunctor G).op.ranObjObjIsoLimit ℱ (Opposite.op y)

/-- **Stacks 06TS**, preservation of sheaves. For a 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf category of `S` and `τ` one of the five topologies, the pullback
`G^p 𝒢 = 𝒢 ∘ G` of a `τ` sheaf of sets `𝒢` on `𝒴` is a `τ` sheaf on `𝒳`, and the pushforward
`{}_pG ℱ`, the right Kan extension of `ℱ` along `G`, of a `τ` sheaf of sets `ℱ` on `𝒳` is a `τ`
sheaf on `𝒴`. -/
@[stacks 06TS "the functors f^p and {}_pf of presheaves of sets transform tau sheaves into tau \
sheaves"]
theorem isSheaf_comp_op_and_isSheaf_ran_obj :
    (∀ 𝒢 : 𝒴.val.objᵒᵖ ⥤ Type t, IsSheaf B S hS 𝒴.val.p τ 𝒢 →
      IsSheaf B S hS 𝒳.val.p τ ((CatFiberedInGroupoids.homFunctor G).op ⋙ 𝒢)) ∧
    ∀ ℱ : 𝒳.val.objᵒᵖ ⥤ Type (max v w t), IsSheaf B S hS 𝒳.val.p τ ℱ →
      IsSheaf B S hS 𝒴.val.p τ ((CatFiberedInGroupoids.homFunctor G).op.ran.obj ℱ) := by
  have h := isContinuous_and_isCocontinuous_associatedTopology B S hS G τ
  have := h.1
  have := h.2
  exact ⟨fun 𝒢 h𝒢 ↦ (CatFiberedInGroupoids.homFunctor G).op_comp_isSheaf_of_isSheaf _ _ 𝒢 h𝒢,
    fun ℱ hℱ ↦ ran_isSheaf_of_isCocontinuous (CatFiberedInGroupoids.homFunctor G)
      (associatedTopology B S hS 𝒴.val.p τ)
      (⟨ℱ, hℱ⟩ : Sheaf (associatedTopology B S hS 𝒳.val.p τ) _)⟩

/-- **Stacks 06TS**, the morphism of topoi. A 1-morphism `G : 𝒳 ⟶ 𝒴` of categories fibred in
groupoids over the big fppf category of `S` defines, for each of the five topologies `τ`, a
morphism of topoi `f : Sh(𝒳_τ) ⟶ Sh(𝒴_τ)` between the categories of sheaves of sets of Stacks
06TR: its inverse image `f⁻¹` is the pullback `G^p` of sheaves, its direct image `f_*` is the
pushforward `{}_pG` of sheaves, `f⁻¹` is left adjoint to `f_*`, and `f⁻¹` is left exact. -/
@[stacks 06TS "the morphism of topoi f : Sh(X_tau) -> Sh(Y_tau) defined by f^p and {}_pf, for \
sheaves of sets"]
noncomputable def morphismOfTopoi_associatedSheaf :
    MorphismOfTopoi (AssociatedSheaf.{u, v, w, max v w t} B S hS 𝒳.val.p τ)
      (AssociatedSheaf.{u, v, w, max v w t} B S hS 𝒴.val.p τ) :=
  letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).1
  letI := (isContinuous_and_isCocontinuous_associatedTopology B S hS G τ).2
  { pushforward := (CatFiberedInGroupoids.homFunctor G).sheafPushforwardCocontinuous _
      (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ)
    inverseImage := (CatFiberedInGroupoids.homFunctor G).sheafPushforwardContinuous _
      (associatedTopology B S hS 𝒳.val.p τ) (associatedTopology B S hS 𝒴.val.p τ)
    adj := sheafAdjunction_associatedTopology B S hS G τ _
    preservesFiniteLimits := preservesFiniteLimits_inverseImage_associatedTopology B S hS G τ _ }

/-- **Stacks 06TS**, `f_* = {}_pG`. The direct image of the morphism of topoi
`AlgebraicGeometry.BigFppfOver.morphismOfTopoi_associatedSheaf` is the pushforward of presheaves:
on underlying presheaves it is the right Kan extension along `G.op`. -/
@[stacks 06TS "the direct image of the morphism of topoi is the pushforward {}_pf of presheaves"]
noncomputable def morphismOfTopoi_associatedSheaf_pushforwardCompSheafToPresheafIso :
    (morphismOfTopoi_associatedSheaf.{u, v, w, t} B S hS G τ).pushforward ⋙
        sheafToPresheaf (associatedTopology B S hS 𝒴.val.p τ) (Type max v w t) ≅
      sheafToPresheaf (associatedTopology B S hS 𝒳.val.p τ) (Type max v w t) ⋙
        (CatFiberedInGroupoids.homFunctor G).op.ran :=
  directImageCompSheafToPresheafIso_associatedTopology B S hS G τ _

/-- **Stacks 06TS**, `f⁻¹ = G^p`. The inverse image of the morphism of topoi
`AlgebraicGeometry.BigFppfOver.morphismOfTopoi_associatedSheaf` is the pullback of presheaves:
on underlying presheaves it is precomposition with `G.op`. -/
@[stacks 06TS "the inverse image of the morphism of topoi is the pullback f^p of presheaves"]
noncomputable def morphismOfTopoi_associatedSheaf_inverseImageCompSheafToPresheafIso :
    (morphismOfTopoi_associatedSheaf.{u, v, w, t} B S hS G τ).inverseImage ⋙
        sheafToPresheaf (associatedTopology B S hS 𝒳.val.p τ) (Type max v w t) ≅
      sheafToPresheaf (associatedTopology B S hS 𝒴.val.p τ) (Type max v w t) ⋙
        (Functor.whiskeringLeft _ _ _).obj (CatFiberedInGroupoids.homFunctor G).op :=
  inverseImageCompSheafToPresheafIso_associatedTopology B S hS G τ _

end AlgebraicGeometry.BigFppfOver
