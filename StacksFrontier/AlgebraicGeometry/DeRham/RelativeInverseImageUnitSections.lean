module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections

/-!
# The comparison `p^{-1}𝓕 ⟶ p^*𝓕` on a pullback-unit section

Let `p : W ⟶ X` and `a : X ⟶ S` be morphisms of schemes and write `f = p ∘ a`. The comparison
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback` of `f^{-1}𝒪_S`-modules is the transpose
along `p^{-1} ⊣ p_*` of the unit of `p^* ⊣ p_*` read through the square comparing the two
factorizations of `p`. This file evaluates it on local sections: it carries the pullback-unit
section of `p^{-1}𝓕` attached to a section `s` of `𝓕` to the pullback-unit section of `p^*𝓕`
attached to `s`.

It also records the canonical lax comparison

`(𝓜|_{f^{-1}𝒪_S}) ⊗_{f^{-1}𝒪_S} (𝓝|_{f^{-1}𝒪_S}) ⟶ (𝓜 ⊗_{𝒪_X} 𝓝)|_{f^{-1}𝒪_S}`

of the tensor product with the direct image along `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`, which is
restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, together with its value on the canonical
sections of a tensor product sheaf.

## Main definitions

* `Stacks.DeRhamDirectImage.inverseImageTensorLax`: the lax comparison
  `f_*𝓜 ⊗_{f^{-1}𝒪_S} f_*𝓝 ⟶ f_*(𝓜 ⊗_{𝒪_X} 𝓝)` for the direct image along
  `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`.

## Main results

* `Stacks.DeRhamDirectImage.relativeToPullbackLeg_val_app`: **the transposed comparison is the
  unit of `p^* ⊣ p_*` on sections**; the three transports in its definition act trivially.
* `Stacks.DeRhamDirectImage.relativeInverseImageToPullback_pullbackUnitSection`: **the comparison
  `p^{-1}𝓕 ⟶ p^*𝓕` carries the pullback-unit section attached to `s` to the pullback-unit
  section of `p^*𝓕` attached to `s`.**
* `Stacks.DeRhamDirectImage.inverseImageTensorLax_toTensorSheafSection`: the lax comparison
  carries the canonical section of a tensor product sheaf attached to a pure tensor over
  `f^{-1}𝒪_S` to the one attached to the same pure tensor over `𝒪_X`.

## Implementation notes

The three transports composed into
`Stacks.DeRhamDirectImage.relativeToPullbackLeg` after the unit — two instances of
`pushforwardComp` and one `eqToHom` between direct images along equal morphisms of ringed spaces
— are each the identity on local sections, but the two sides of each identity are spelled at
different iterated preimages of the open set, so the single `rfl` for the composite does not
elaborate. Each step is therefore taken separately against an explicitly ascribed value, and the
`eqToHom` step is discharged by substituting the equality of morphisms, which is why
`relativeSquareTransport_app_apply` takes its target section and a `HEq` as arguments rather than
naming it.

`inverseImageTensorLax` is **not** identified here with the lax tensorator
`CategoryTheory.Functor.LaxMonoidal.μ` of
`Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal` at
`Stacks.DeRhamDirectImage.toInverseImageBase`. That tensorator is the adjoint transpose of the
*oplax* tensorator of the pullback for `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, so
the identification is equivalent to identifying the latter with the comparison of Stacks 01CD.
That is now available —
`Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq`, resting on the computation of
the localization tensorator on local sections in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite` — so the
identification is no longer blocked; it is simply not needed by anything here.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct
open _root_.AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.PullbackUnitGenerators
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.DeRhamDirectImage

/-! ### The transposed comparison on local sections -/

section Leg

variable {W X S : Scheme.{u}} (p : W ⟶ X) (a : X ⟶ S)

/-- A four-step composite of morphisms of sheaves of modules over a ringed space, on a local
section, with the four one-step evaluations supplied as hypotheses. Supplying them, rather than
unfolding the composite, keeps the sheaf of modules at each stage the one the hypothesis names. -/
private theorem comp4_val_app_apply_of (Z : RingedSpace.{u}) {A B C D E : Modules Z} (g : A ⟶ B)
    (k : B ⟶ C) (l : C ⟶ D) (m : D ⟶ E) (V : (Opens Z.carrier)ᵒᵖ) (s : A.val.obj V)
    {b : B.val.obj V} (hb : (g.val.app V).hom s = b)
    {c : C.val.obj V} (hc : (k.val.app V).hom b = c)
    {d : D.val.obj V} (hd : (l.val.app V).hom c = d)
    {e : E.val.obj V} (he : (m.val.app V).hom d = e) :
    ((g ≫ k ≫ l ≫ m).val.app V).hom s = e := by
  subst hb hc hd he
  rfl

/-- A transport of sheaves of modules between equal objects, on a local section: it carries a
section to the one that is heterogeneously equal to it. -/
private theorem eqToHom_val_app_apply {Z : RingedSpace.{u}} {A B : Modules Z} (h : A = B)
    (V : (Opens Z.carrier)ᵒᵖ) (s : A.val.obj V) (t : B.val.obj V) (hst : HEq s t) :
    ((eqToHom h).val.app V).hom s = t := by
  subst h
  cases hst
  rfl

/-- **The transport along the square acts trivially on local sections.** The target section is
taken as an argument, with a heterogeneous equality, because the two direct images it lies in are
spelled at different composites of morphisms of ringed spaces. -/
theorem relativeSquareTransport_app_apply (F : Modules W.toRingedSpace)
    (V : (Opens (inverseImageBase a).carrier)ᵒᵖ)
    (s : ((pushforward (p.toLRSHom.toShHom ≫ toInverseImageBase a)).obj F).val.obj V)
    (t : ((pushforward (toInverseImageBase (p ≫ a) ≫ relativeInverseImageProjection p a)).obj
      F).val.obj V) (hst : HEq s t) :
    ((relativeSquareTransport p a F).val.app V).hom s = t :=
  eqToHom_val_app_apply _ V s t hst

/-- The pullback-unit section of `s`, in the direct image along `(X, 𝒪_X) ⟶ (X, a^{-1}𝒪_S)` of
the composite of the pullback and the direct image along `p`. -/
private def legStep₁ (F : X.Modules) (V : X.Opensᵒᵖ) (s : F.val.obj V) :
    (((pushforward (toInverseImageBase a)).obj
      ((_root_.pullback p.toLRSHom.toShHom ⋙
        pushforward p.toLRSHom.toShHom).obj F)).val.obj V) :=
  modulesPullbackUnit p F V.unop s

/-- The pullback-unit section of `s`, in the direct image along the composite
`(W, 𝒪_W) ⟶ (X, 𝒪_X) ⟶ (X, a^{-1}𝒪_S)`. -/
private def legStep₂ (F : X.Modules) (V : X.Opensᵒᵖ) (s : F.val.obj V) :
    (((pushforward (p.toLRSHom.toShHom ≫ toInverseImageBase a)).obj
      ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.obj V) :=
  modulesPullbackUnit p F V.unop s

/-- The pullback-unit section of `s`, in the direct image along the other factorization
`(W, 𝒪_W) ⟶ (W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` of the same morphism of ringed spaces. -/
private def legStep₃ (F : X.Modules) (V : X.Opensᵒᵖ) (s : F.val.obj V) :
    (((pushforward (toInverseImageBase (p ≫ a) ≫
      relativeInverseImageProjection p a)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.obj V) :=
  modulesPullbackUnit p F V.unop s

/-- The pullback-unit section of `s`, in the iterated direct image of `p^*𝓕` that is the target
of `Stacks.DeRhamDirectImage.relativeToPullbackLeg`. -/
private def legStep₄ (F : X.Modules) (V : X.Opensᵒᵖ) (s : F.val.obj V) :
    (((relativeInverseImagePushforward p a).obj
      ((pushforward (toInverseImageBase (p ≫ a))).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj F))).val.obj V) :=
  modulesPullbackUnit p F V.unop s

/-- **The unit of `p^* ⊣ p_*` read through the square is that unit on local sections.** The
target section is taken as an argument, with a heterogeneous equality to the pullback-unit
section of `s`, because it lies in a direct image spelled at an iterated preimage of `V`. -/
theorem relativeToPullbackLeg_val_app (F : X.Modules) (V : X.Opensᵒᵖ) (s : F.val.obj V)
    (t : (((relativeInverseImagePushforward p a).obj
        ((pushforward (toInverseImageBase (p ≫ a))).obj
          ((_root_.pullback p.toLRSHom.toShHom).obj F))).val.obj V))
    (hst : HEq (modulesPullbackUnit p F V.unop s) t) :
    ((relativeToPullbackLeg p a F).val.app V).hom s = t := by
  have e₁ : ((((pushforward (toInverseImageBase a)).map
        ((_root_.pullbackPushforwardAdjunction p.toLRSHom.toShHom).unit.app F)).val.app V).hom s)
      = legStep₁ p a F V s := rfl
  have e₂ : ((((pushforwardComp p.toLRSHom.toShHom (toInverseImageBase a)).inv.app
        ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.app V).hom (legStep₁ p a F V s))
      = legStep₂ p a F V s := rfl
  have e₃ : (((relativeSquareTransport p a
        ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.app V).hom (legStep₂ p a F V s))
      = legStep₃ p a F V s :=
    relativeSquareTransport_app_apply p a _ V _ _ HEq.rfl
  have e₄ : ((((pushforwardComp (toInverseImageBase (p ≫ a))
          (relativeInverseImageProjection p a)).hom.app
        ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.app V).hom (legStep₃ p a F V s))
      = legStep₄ p a F V s := rfl
  exact comp4_val_app_apply_of (inverseImageBase a)
    ((pushforward (toInverseImageBase a)).map
      ((_root_.pullbackPushforwardAdjunction p.toLRSHom.toShHom).unit.app F))
    ((pushforwardComp p.toLRSHom.toShHom (toInverseImageBase a)).inv.app
      ((_root_.pullback p.toLRSHom.toShHom).obj F))
    (relativeSquareTransport p a ((_root_.pullback p.toLRSHom.toShHom).obj F))
    ((pushforwardComp (toInverseImageBase (p ≫ a))
        (relativeInverseImageProjection p a)).hom.app
      ((_root_.pullback p.toLRSHom.toShHom).obj F))
    V s e₁ e₂ e₃ (e₄.trans (eq_of_heq (HEq.trans HEq.rfl hst)))

/-- **The comparison `p^{-1}𝓕 ⟶ p^*𝓕` on a pullback-unit section.** It carries the section of
`p^{-1}𝓕` attached by the unit of `p^{-1} ⊣ p_*` to a section `s` of `𝓕` to the section of `p^*𝓕`
attached by the unit of `p^* ⊣ p_*` to `s`. -/
theorem relativeInverseImageToPullback_pullbackUnitSection (F : X.Modules) (V : X.Opensᵒᵖ)
    (s : ((pushforward (toInverseImageBase a)).obj F).val.obj V)
    (t : (((relativeInverseImagePushforward p a).obj
        ((pushforward (toInverseImageBase (p ≫ a))).obj
          ((_root_.pullback p.toLRSHom.toShHom).obj F))).val.obj V))
    (hst : HEq (modulesPullbackUnit p F V.unop s) t) :
    ((relativeInverseImageToPullback p a F).val.app
        ((opensMap (relativeInverseImageProjection p a)).op.obj V)).hom
      (pullbackUnitSection (relativeInverseImageProjection p a)
        ((pushforward (toInverseImageBase a)).obj F) V s) = t :=
  Eq.trans
    (SheafOfModules.GradedAlgebra.homEquiv_symm_val_app_unit
      (relativeInverseImageProjection p a) (relativeToPullbackLeg p a F) V s)
    (relativeToPullbackLeg_val_app p a F V s t hst)

end Leg

/-! ### The lax comparison of the tensor product with the direct image to `(X, f^{-1}𝒪_S)` -/

section Lax

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The lax comparison `f_*𝓜 ⊗_{f^{-1}𝒪_S} f_*𝓝 ⟶ f_*(𝓜 ⊗_{𝒪_X} 𝓝)`** for the direct image
along `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`: that direct image is restriction of scalars along
`f^{-1}𝒪_S ⟶ 𝒪_X`, and a pure tensor of two sections is a pure tensor over either ring. -/
def inverseImageTensorLax (M N : Modules X.toRingedSpace) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((inverseImageBase f))).presheaf, (((inverseImageBase f))).IsSheaf⟩).obj
          (((pushforward (toInverseImageBase f)).obj M))).obj
        (((pushforward (toInverseImageBase f)).obj N))) ⟶
      (pushforward (toInverseImageBase f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (N))) :=
  Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf) X.sheaf
    (inverseImageStructureMap f) M N

/-- **The lax comparison on the canonical sections of a tensor product sheaf.** It carries the
section attached to a pure tensor over `f^{-1}𝒪_S` to the section attached to the same pure
tensor over `𝒪_X`. -/
theorem inverseImageTensorLax_toTensorSheafSection (M N : Modules X.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ)
    (x : ((pushforward (toInverseImageBase f)).obj M).val.obj U)
    (y : ((pushforward (toInverseImageBase f)).obj N).val.obj U)
    (x' : M.val.obj U) (y' : N.val.obj U) (hx : HEq x x') (hy : HEq y y') :
    ((inverseImageTensorLax f M N).val.app U).hom
        (toTensorSheafSection (inverseImageBase f)
          ((pushforward (toInverseImageBase f)).obj M)
          ((pushforward (toInverseImageBase f)).obj N) U
          (x ⊗ₜ[(inverseImageBase f).presheaf.obj U] y)) =
      toTensorSheafSection X.toRingedSpace M N U (x' ⊗ₜ[X.presheaf.obj U] y') := by
  cases hx
  cases hy
  exact Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_toTensorSheafSection
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf) X.sheaf
    (inverseImageStructureMap f) M N U _

end Lax

end Stacks.DeRhamDirectImage

end
