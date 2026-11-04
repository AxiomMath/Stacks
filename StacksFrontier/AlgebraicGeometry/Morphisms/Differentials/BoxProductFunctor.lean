module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartExtensionalityOverBase

/-!
# The box-product bifunctor of differential operators

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. The external tensor product
`F ⊠ G = pr₁^*F ⊗ pr₂^*G` of two quasi-coherent modules and the box product `D ⊠ E` of two
finite-order differential operators together form a functor
`(F, G) ↦ F ⊠ G` from the product of the categories of finite-order differential operators on
`X/S` and on `Y/S` to the category on `X ×_S Y / S`. Both functor laws are read off from the
action of `D ⊠ E` on the sections of `F ⊠ G` attached to a pair of local sections: such an
operator carries the section attached to `s` and `t` to the section attached to `D s` and `E t`,
and a differential operator of finite order relative to `S` out of a quasi-coherent module is
determined by its action on the sections over the affine charts of `X ×_S Y`. The same
computation makes the box product additive in each of its two arguments separately.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductFunctor`: the box product
  as a functor from the product of the categories of finite-order differential operators on
  `X/S` and on `Y/S` to the category on `X ×_S Y / S`.

## Main results

* `Stacks.Tag01VSPullbackTensor.externalTensorSection_add_left` and
  `Stacks.Tag01VSPullbackTensor.externalTensorSection_add_right`: the section of `F ⊠ G` attached
  to a pair of local sections is additive in each of the two sections.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_externalTensorSection`:
  `D ⊠ E` carries the section of `F ⊠ G` attached to `s` and `t` to the section of `F' ⊠ G'`
  attached to `D s` and `E t`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hom_ext_of_externalTensorSection`:
  two finite-order differential operators out of `F ⊠ G` which agree on the sections attached to
  pairs of local sections over every affine chart are equal.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_id` and
  `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_comp`: the two functor laws
  for the box product.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_add_left` and
  `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_add_right`: the box product
  is additive in each of its two arguments.

## Implementation notes

The extensionality used is the `S`-relative one,
`AlgebraicGeometry.globalDiffOp_ext_of_chart_sections_overBase`: the two factors `D ⊠ 1` and
`1 ⊠ E` of `D ⊠ E` have finite order relative to the two projections separately, so their
composite has finite order only relative to `S`.

Several steps are written in term mode rather than by `rewrite`, because the goals involve the
coincidence of `AlgebraicGeometry.Scheme.Modules` with the sheaves of modules on the underlying
ringed space, which is not available at the transparency at which `rewrite` checks its motive.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.FibreProductAffineChart
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- **The section of `F ⊠ G` attached to a pair of local sections is additive in the section of
`F`.** -/
theorem externalTensorSection_add_left {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (x x' : Γ(F, U)) (y : Γ(G, V))
    (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G (x + x') y W hW₁ hW₂ =
      externalTensorSection p q F G x y W hW₁ hW₂ +
        externalTensorSection p q F G x' y W hW₁ hW₂ := by
  unfold externalTensorSection
  exact (congrArg _ ((congrArg (· ⊗ₜ _) ((congrArg _ (map_add _ x x')).trans (map_add _ _ _))).trans
    (TensorProduct.add_tmul _ _ _))).trans (toTensorSheafSection_add _ _ _ _ _ _)

/-- **The section of `F ⊠ G` attached to a pair of local sections is additive in the section of
`G`.** -/
theorem externalTensorSection_add_right {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S)
    (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (x : Γ(F, U)) (y y' : Γ(G, V))
    (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    externalTensorSection p q F G x (y + y') W hW₁ hW₂ =
      externalTensorSection p q F G x y W hW₁ hW₂ +
        externalTensorSection p q F G x y' W hW₁ hW₂ := by
  unfold externalTensorSection
  exact (congrArg _ ((congrArg (_ ⊗ₜ ·) ((congrArg _ (map_add _ y y')).trans (map_add _ _ _))).trans
    (TensorProduct.tmul_add _ _ _))).trans (toTensorSheafSection_add _ _ _ _ _ _)

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

/-- A sum of two finite-order differential operators acts on local sections as the sum of their
actions. -/
theorem hom_add_coe_apply {X S : Scheme.{u}} {a : X ⟶ S}
    {F G : FiniteOrderDifferentialOperatorCategory a} (D D' : F ⟶ G) (U : X.Opensᵒᵖ)
    (s : F.module.val.obj U) : (D + D').1 U s = D.1 U s + D'.1 U s := rfl

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **`D ⊠ E` on the section attached to a pair of local sections.** It carries the section of
`F ⊠ G` attached to a section `s` of `F` over `U'` and a section `t` of `G` over `V'`, over any
open `W` of `X ×_S Y` inside `pr₁⁻¹U' ⊓ pr₂⁻¹V'`, to the section of `F' ⊠ G'` attached to `D s`
and `E t`. -/
theorem boxHom_externalTensorSection {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G')
    {U' : X.Opens} {V' : Y.Opens} (s : Γ(F.module, U')) (t : Γ(G.module, V'))
    (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    (boxHom D E).1 (op W) (externalTensorSection a b F.module G.module s t W hW₁ hW₂) =
      externalTensorSection a b F'.module G'.module (D.1 (op U') s) (E.1 (op V') t) W hW₁ hW₂ := by
  change (boxHomRight F' E).1 (op W) ((boxHomLeft G D).1 (op W) _) = _
  exact (congrArg (fun z ↦ (boxHomRight F' E).1 (op W) z)
      (boxHomLeft_externalTensorSection G D s t W hW₁ hW₂)).trans
    (boxHomRight_externalTensorSection F' E (D.1 (op U') s) t W hW₁ hW₂)

/-- **Two finite-order differential operators out of `F ⊠ G` agreeing on the sections attached to
pairs of local sections over every affine chart are equal.** An operator out of `F ⊠ G` has
finite order relative to `S` and `F ⊠ G` is quasi-coherent, so it is determined by its action on
the sections over each affine chart of `X ×_S Y`, and those sections are generated by the ones
attached to a pair of sections over the chart's two factors. -/
theorem hom_ext_of_externalTensorSection {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b}
    (P Q : boxProductObj F G ⟶ boxProductObj F' G')
    (h : ∀ (c : Chart a b) (s : Γ(F.module, c.left)) (t : Γ(G.module, c.right))
      (h₁ : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left)
      (h₂ : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right),
      P.1 (op c.ι.opensRange)
          (externalTensorSection a b F.module G.module s t c.ι.opensRange h₁ h₂) =
        Q.1 (op c.ι.opensRange)
          (externalTensorSection a b F.module G.module s t c.ι.opensRange h₁ h₂)) :
    P = Q := by
  obtain ⟨k, hk⟩ := P.2
  obtain ⟨l, hl⟩ := Q.2
  refine Subtype.ext (globalDiffOp_ext_of_chart_sections_overBase a b (max k l) P.1 Q.1
    (isGlobalDiffOpOfOrder_of_le _ (Nat.le_max_left k l) _ hk)
    (isGlobalDiffOpOfOrder_of_le _ (Nat.le_max_right k l) _ hl) fun c x ↦ ?_)
  have h₁ : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left := c.opensRange_ι.le.trans inf_le_left
  have h₂ : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right := c.opensRange_ι.le.trans inf_le_right
  exact c.ext_of_externalTensorSection_of_eq F.module G.module
    (by rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]) h₁ h₂
    (P.1 (op c.ι.opensRange)) (Q.1 (op c.ι.opensRange)) (fun s t ↦ h c s t h₁ h₂) x

/-- **The box product of two identities is the identity.** Both operators fix the section of
`F ⊠ G` attached to a pair of local sections. -/
theorem boxHom_id (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    boxHom (𝟙 F) (𝟙 G) = 𝟙 (boxProductObj F G) :=
  hom_ext_of_externalTensorSection _ _ fun c s t h₁ h₂ ↦
    (boxHom_externalTensorSection (𝟙 F) (𝟙 G) s t c.ι.opensRange h₁ h₂).trans rfl

/-- **The box product of two composites is the composite of the two box products.** Both
operators carry the section of `F₁ ⊠ G₁` attached to `s` and `t` to the section of `F₃ ⊠ G₃`
attached to `D₁ (D₂ s)` and `E₁ (E₂ t)`. -/
theorem boxHom_comp {F₁ F₂ F₃ : FiniteOrderDifferentialOperatorCategory a}
    {G₁ G₂ G₃ : FiniteOrderDifferentialOperatorCategory b}
    (D₂ : F₁ ⟶ F₂) (D₁ : F₂ ⟶ F₃) (E₂ : G₁ ⟶ G₂) (E₁ : G₂ ⟶ G₃) :
    boxHom (D₂ ≫ D₁) (E₂ ≫ E₁) = boxHom D₂ E₂ ≫ boxHom D₁ E₁ := by
  refine hom_ext_of_externalTensorSection _ _ fun c s t h₁ h₂ ↦ ?_
  refine (boxHom_externalTensorSection (D₂ ≫ D₁) (E₂ ≫ E₁) s t c.ι.opensRange h₁ h₂).trans ?_
  change _ = (boxHom D₁ E₁).1 (op c.ι.opensRange) ((boxHom D₂ E₂).1 (op c.ι.opensRange) _)
  exact ((congrArg (fun z ↦ (boxHom D₁ E₁).1 (op c.ι.opensRange) z)
      (boxHom_externalTensorSection D₂ E₂ s t c.ι.opensRange h₁ h₂)).trans
    (boxHom_externalTensorSection D₁ E₁ (D₂.1 (op c.left) s) (E₂.1 (op c.right) t)
      c.ι.opensRange h₁ h₂)).symm

/-- Two finite-order differential operators out of `F ⊠ G`, with `D₁ ⊠ E₁` a sum of two
box products, are equal as soon as the sections attached to `D₁ s`, `E₁ t` split accordingly. -/
private theorem boxHom_eq_add_of_externalTensorSection
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D₁ D₂ D₃ : F ⟶ F') (E₁ E₂ E₃ : G ⟶ G')
    (h : ∀ (c : Chart a b) (s : Γ(F.module, c.left)) (t : Γ(G.module, c.right))
      (h₁ : c.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c.left)
      (h₂ : c.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c.right),
      externalTensorSection a b F'.module G'.module (D₁.1 (op c.left) s) (E₁.1 (op c.right) t)
          c.ι.opensRange h₁ h₂ =
        externalTensorSection a b F'.module G'.module (D₂.1 (op c.left) s) (E₂.1 (op c.right) t)
          c.ι.opensRange h₁ h₂ +
        externalTensorSection a b F'.module G'.module (D₃.1 (op c.left) s) (E₃.1 (op c.right) t)
          c.ι.opensRange h₁ h₂) :
    boxHom D₁ E₁ = boxHom D₂ E₂ + boxHom D₃ E₃ := by
  refine hom_ext_of_externalTensorSection _ _ fun c s t h₁ h₂ ↦ ?_
  refine (boxHom_externalTensorSection D₁ E₁ s t _ h₁ h₂).trans ((h c s t h₁ h₂).trans ?_)
  exact (congrArg₂ (· + ·) (boxHom_externalTensorSection D₂ E₂ s t _ h₁ h₂)
    (boxHom_externalTensorSection D₃ E₃ s t _ h₁ h₂)).symm

/-- **The box product is additive in its first argument.** -/
@[stacks 0G46 "half of the bilinearity on morphisms asserted by the remark: the box product \
`D ⊠ E` is additive in the operator `D` on `X/S`"]
theorem boxHom_add_left {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D D' : F ⟶ F') (E : G ⟶ G') :
    boxHom (D + D') E = boxHom D E + boxHom D' E :=
  boxHom_eq_add_of_externalTensorSection _ _ _ _ _ _ fun c s t h₁ h₂ ↦
    externalTensorSection_add_left a b F'.module G'.module (D.1 (op c.left) s)
      (D'.1 (op c.left) s) (E.1 (op c.right) t) c.ι.opensRange h₁ h₂

/-- **The box product is additive in its second argument.** -/
@[stacks 0G46 "the other half of the bilinearity on morphisms asserted by the remark: the box \
product `D ⊠ E` is additive in the operator `E` on `Y/S`"]
theorem boxHom_add_right {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E E' : G ⟶ G') :
    boxHom D (E + E') = boxHom D E + boxHom D E' :=
  boxHom_eq_add_of_externalTensorSection _ _ _ _ _ _ fun c s t h₁ h₂ ↦
    externalTensorSection_add_right a b F'.module G'.module (D.1 (op c.left) s)
      (E.1 (op c.right) t) (E'.1 (op c.right) t) c.ι.opensRange h₁ h₂

/-- **The box-product bifunctor of [Stacks, Tag 0G46].** The external tensor product on objects
and the box product of two differential operators on morphisms form a functor from the product
of the categories of finite-order differential operators on `X/S` and on `Y/S` to the category
of finite-order differential operators on `X ×_S Y / S`. -/
@[stacks 0G46 "the box product bifunctor of the remark: `(F, G) ↦ F ⊠ G` on objects and \
`(D, E) ↦ D ⊠ E` on morphisms, with both functor laws. NOT the notation `F ⊠ G`, and NOT the \
affine description `(M, N) ↦ M ⊗_R N`, `(D, D') ↦ D ⊗ D'`, which is covered by \
`Chart.boxSectionsEquiv` and `Chart.boxHom_boxSectionOfTensor`"]
noncomputable def boxProductFunctor (a : X ⟶ S) (b : Y ⟶ S) :
    FiniteOrderDifferentialOperatorCategory a × FiniteOrderDifferentialOperatorCategory b ⥤
      FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a) where
  obj P := boxProductObj P.1 P.2
  map f := boxHom f.1 f.2
  map_id P := boxHom_id P.1 P.2
  map_comp f g := boxHom_comp f.1 g.1 f.2 g.2

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
