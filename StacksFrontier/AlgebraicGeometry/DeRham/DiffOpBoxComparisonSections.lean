module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensorExtensionality

/-!
# The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖` on local sections

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a`. The comparison
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` of
[Stacks, Tag 0G46] is step (5) of the construction of the Künneth maps of [Stacks, Tag 0G4A].
On a pure tensor of restricted pullback-unit sections it is the section of `𝓕 ⊠ 𝓖` attached to
the pair of sections.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison_tmul`: **the
  comparison carries the pure tensor of two restricted pullback-unit sections to
  `Stacks.Tag01VSPullbackTensor.externalTensorSection`**, the section of `𝓕 ⊠ 𝓖` attached to the
  pair of local sections.
* `Stacks.BoxKunnethSections.comparison_restrict_ofFactors`: the comparison `p^{-1}𝓕 ⟶ p^*𝓕`,
  in its form transported along a factorization of `W ⟶ S`, on a restricted pullback-unit
  section.
* `Stacks.BoxKunnethSections.map_pullbackUnitSection`: the pullback-unit section is natural in
  the module.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductRelative_map` and
  `toInverseImageModules_boxHom_val_app`: the box bifunctor read over `f^{-1}𝒪_S` is the box
  product of the two operators, and it acts on local sections by that operator.

## Implementation notes

A section of `p^{-1}𝓕` restricted from a pullback-unit section, a section of the direct image of
`p^*𝓕`, and the target of the comparison are each taken as a binder constrained by an equation or
a heterogeneous equality, in the idiom of
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback_pullbackUnitSection`. The comparison is
the composite of `relativeBoxComparisonLeg₁` and `relativeBoxComparisonLeg₂`, which meet at
`relativeBoxMid`.

## References

* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
open Stacks.DeRhamDirectImage
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.PullbackUnitGenerators
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.BoxKunnethSections

/-! ### Local sections of a morphism of sheaves of modules -/

/-- **A morphism of sheaves of modules commutes with restriction of sections.** -/
theorem app_map_apply {Z : RingedSpace.{u, u}} {M N : Modules Z} (g : M ⟶ N)
    {U V : (Opens Z.carrier)ᵒᵖ} (i : U ⟶ V) (m : M.val.obj U) :
    (g.val.app V).hom ((M.val.map i).hom m) = (N.val.map i).hom ((g.val.app U).hom m) :=
  PresheafOfModules.naturality_apply g.val i m

/-- Restriction of sections applied to an equality of sections. -/
theorem map_congr {Z : RingedSpace.{u, u}} {N : Modules Z} {U V : (Opens Z.carrier)ᵒᵖ} (i : U ⟶ V)
    {m m' : N.val.obj U} (h : m = m') :
    (N.val.map i).hom m = (N.val.map i).hom m' :=
  congrArg _ h

/-- **The composite of two morphisms of sheaves of modules on a local section**: if `g` carries `s`
to `b₀` and `k` carries `b₀` to `c₀`, then `g ≫ k` carries `s` to `c₀`. -/
theorem comp_val_app_apply_of {Z : RingedSpace.{u, u}} {A B C : Modules Z} (g : A ⟶ B) (k : B ⟶ C)
    (V : (Opens Z.carrier)ᵒᵖ) (s : A.val.obj V)
    {b₀ : B.val.obj V} (hb : (g.val.app V).hom s = b₀)
    {c₀ : C.val.obj V} (hc : (k.val.app V).hom b₀ = c₀) :
    ((g ≫ k).val.app V).hom s = c₀ := by
  subst hb hc
  rfl

/-- The canonical section of a tensor product sheaf, on an equality in each factor. -/
theorem toTensorSheafSection_congr₂ {Z : RingedSpace.{u, u}} (M N : Modules Z)
    (V : (Opens Z.carrier)ᵒᵖ) {m m' : M.val.obj V} {n n' : N.val.obj V}
    (hm : m = m') (hn : n = n') :
    toTensorSheafSection Z M N V (m ⊗ₜ[Z.presheaf.obj V] n) =
      toTensorSheafSection Z M N V (m' ⊗ₜ[Z.presheaf.obj V] n') := by
  subst hm hn
  rfl

/-! ### The pullback-unit section -/

/-- **The pullback-unit section is natural in the module**: the inverse image of a morphism
carries the unit section of `m` to the unit section of its image. -/
theorem map_pullbackUnitSection {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')
    {M M' : Modules Z'} (wm : M ⟶ M') (V : (Opens Z'.carrier)ᵒᵖ) (m : M.val.obj V) :
    (((modulePullback g).map wm).val.app ((opensMap g).op.obj V)).hom
        (pullbackUnitSection g M V m) =
      pullbackUnitSection g M' V ((wm.val.app V).hom m) :=
  (congrArg (fun k : M ⟶ (modulePullback g ⋙ modulePushforward g).obj M' =>
      (k.val.app V).hom m)
    ((modulePullbackPushforwardAdjunction g).unit.naturality wm)).symm

/-- The pullback-unit section applied to an equality of sections. -/
theorem pullbackUnitSection_congr {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z') (M : Modules Z')
    (V : (Opens Z'.carrier)ᵒᵖ) {m m' : M.val.obj V} (h : m = m') :
    pullbackUnitSection g M V m = pullbackUnitSection g M V m' :=
  congrArg _ h

/-! ### The comparison `p^{-1}𝓕 ⟶ p^*𝓕` transported along a factorization -/

section Factors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)

/-- **The transported comparison `p^{-1}𝓕 ⟶ p^*𝓕` on a pullback-unit section.** -/
theorem relativeInverseImageToPullbackOfFactors_pullbackUnitSection (F : X'.Modules)
    (V : X'.Opensᵒᵖ) (s : ((pushforward (toInverseImageBase c)).obj F).val.obj V)
    (t : (((pushforward (relativeInverseImageProjectionOfFactors p c g hg)).obj
        ((pushforward (toInverseImageBase g)).obj
          ((_root_.pullback p.toLRSHom.toShHom).obj F))).val.obj V))
    (hst : HEq (modulesPullbackUnit p F V.unop s) t) :
    ((relativeInverseImageToPullbackOfFactors p c g hg F).val.app
        ((opensMap (relativeInverseImageProjectionOfFactors p c g hg)).op.obj V)).hom
      (pullbackUnitSection (relativeInverseImageProjectionOfFactors p c g hg)
        ((pushforward (toInverseImageBase c)).obj F) V s) = t := by
  subst hg
  exact relativeInverseImageToPullback_pullbackUnitSection p c F V s t hst

/-- **The open underlying the transported projection is the preimage along `p`.** -/
theorem opensMap_relativeInverseImageProjectionOfFactors (U' : X'.Opens) :
    (opensMap (relativeInverseImageProjectionOfFactors p c g hg)).obj U' = p ⁻¹ᵁ U' := by
  subst hg
  rfl

/-- **The transported comparison `p^{-1}𝓕 ⟶ p^*𝓕` on a restricted pullback-unit section.** -/
theorem comparison_restrict_ofFactors (F : X'.Modules) (U' : X'.Opens) (s : Γ(F, U'))
    (W₀ : W.Opens) (h₁ : W₀ ≤ p ⁻¹ᵁ U')
    (i : (opensMap (relativeInverseImageProjectionOfFactors p c g hg)).op.obj (op U') ⟶ op W₀)
    (x : ((modulePullback (relativeInverseImageProjectionOfFactors p c g hg)).obj
        ((pushforward (toInverseImageBase c)).obj F)).val.obj (op W₀))
    (hx : (((modulePullback (relativeInverseImageProjectionOfFactors p c g hg)).obj
          ((pushforward (toInverseImageBase c)).obj F)).val.map i).hom
        (pullbackUnitSection (relativeInverseImageProjectionOfFactors p c g hg)
          ((pushforward (toInverseImageBase c)).obj F) (op U') s) = x)
    (z : ((pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj F)).val.obj (op W₀))
    (hz : HEq ((((Scheme.Modules.pullback p).obj F).presheaf.map (homOfLE h₁).op).hom
        (modulesPullbackUnit p F U' s)) z) :
    ((relativeInverseImageToPullbackOfFactors p c g hg F).val.app (op W₀)).hom x = z := by
  subst hg hx
  obtain rfl : i = (homOfLE h₁).op := Subsingleton.elim _ _
  exact Eq.trans
    (app_map_apply (relativeInverseImageToPullback p c F) (homOfLE h₁).op _)
    (Eq.trans
      (map_congr (homOfLE h₁).op
        (relativeInverseImageToPullback_pullbackUnitSection p c F (op U') s _ HEq.rfl))
      (eq_of_heq hz))

end Factors

/-! ### Morphisms out of a tensor product sheaf, on a pure tensor -/

section Eval

variable {Z : RingedSpace.{u, u}} {M N M' N' C C' : SheafOfModules.{u} (structureSheafRing Z)}

/-- A morphism out of a tensor product sheaf postcomposed with a morphism, on a pure tensor. -/
theorem tensorEvalMap_comp_tmul
    (u : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Z.presheaf, Z.IsSheaf⟩).obj M).obj N ⟶ C) (k : C ⟶ C')
    (V : Opens Z.carrier) (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
    tensorEvalMap (u ≫ k) (op V) (m ⊗ₜ[Z.presheaf.obj (op V)] n) =
      (k.val.app (op V)).hom (tensorEvalMap u (op V) (m ⊗ₜ[Z.presheaf.obj (op V)] n)) :=
  comp_val_app_apply_of u k (op V) _ rfl rfl

/-- **The functorial action of the tensor product precomposed into a morphism out of it, on a
pure tensor**: the pure tensor of the two images. -/
theorem tensorEvalMap_tensorSheafMap_comp (φ : M ⟶ M') (ψ : N ⟶ N')
    (u : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Z.presheaf, Z.IsSheaf⟩).obj M').obj N' ⟶ C) (V : Opens Z.carrier)
    (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
    tensorEvalMap ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.presheaf, Z.IsSheaf⟩)).map ((φ, ψ) : (M, N) ⟶ (M', N')) ≫ u) (op V)
        (m ⊗ₜ[Z.presheaf.obj (op V)] n) =
      tensorEvalMap u (op V) ((φ.val.app (op V)).hom m ⊗ₜ[Z.presheaf.obj (op V)]
        (ψ.val.app (op V)).hom n) :=
  comp_val_app_apply_of ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩)).map
        ((φ, ψ) : (M, N) ⟶ (M', N'))) u (op V) _
    (tensorSheafMap_app_toTensorSheafSection Z M N M' N' φ ψ V m n) rfl

end Eval

end Stacks.BoxKunnethSections

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

open Stacks.BoxKunnethSections

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-! ### The comparison on a pure tensor of pullback-unit sections -/

/-- **The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖` on a pure tensor of restricted
pullback-unit sections.** For `s` a section of `𝓕` over `U'`, `t` a section of `𝓖` over `V'`, and
`W₀` an open of `X ×_S Y` inside `p⁻¹U' ⊓ q⁻¹V'`, the comparison carries the pure tensor of the
restrictions to `W₀` of the two unit sections to the section of `𝓕 ⊠ 𝓖` attached to `s` and `t`.
-/
theorem relativeBoxComparison_tmul (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b)
    (U' : X.Opens) (s : Γ(F.module, U')) (V' : Y.Opens) (t : Γ(G.module, V'))
    (W₀ : (Limits.pullback a b).Opens)
    (h₁ : W₀ ≤ pullback.fst a b ⁻¹ᵁ U') (h₂ : W₀ ≤ pullback.snd a b ⁻¹ᵁ V')
    (i₂ : (opensMap (sndRelativeInverseImageProjection a b)).op.obj (op V') ⟶ op W₀)
    (x : ((leftRelativeInverseImage a b).obj F).val.obj (op W₀))
    (y : ((rightRelativeInverseImage a b).obj G).val.obj (op W₀))
    (hx : (((leftRelativeInverseImage a b).obj F).val.map (homOfLE h₁).op).hom
        (pullbackUnitSection (relativeInverseImageProjection (pullback.fst a b) a)
          ((toInverseImageModules a).obj F) (op U') s) = x)
    (hy : (((rightRelativeInverseImage a b).obj G).val.map i₂).hom
        (pullbackUnitSection (sndRelativeInverseImageProjection a b)
          ((toInverseImageModules b).obj G) (op V') t) = y)
    (zL : ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module)).val.obj (op W₀))
    (zR : ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module)).val.obj (op W₀))
    (hzL : HEq ((((Scheme.Modules.pullback (pullback.fst a b)).obj F.module).presheaf.map
        (homOfLE h₁).op).hom (modulesPullbackUnit (pullback.fst a b) F.module U' s)) zL)
    (hzR : HEq ((((Scheme.Modules.pullback (pullback.snd a b)).obj G.module).presheaf.map
        (homOfLE h₂).op).hom (modulesPullbackUnit (pullback.snd a b) G.module V' t)) zR)
    (w : ((boxProductRelative a b).obj (F, G)).val.obj (op W₀))
    (hw : HEq (externalTensorSection a b F.module G.module s t W₀ h₁ h₂) w) :
    tensorEvalMap (relativeBoxComparison a b F G) (op W₀)
        (x ⊗ₜ[(inverseImageBase (pullback.fst a b ≫ a)).presheaf.obj (op W₀)] y) = w := by
  have hleft := comparison_restrict_ofFactors (pullback.fst a b) a (pullback.fst a b ≫ a) rfl
    F.module U' s W₀ h₁ (homOfLE h₁).op x hx zL hzL
  have hright := comparison_restrict_ofFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
    pullback.condition.symm G.module V' t W₀ h₂ i₂ y hy zR hzR
  have step₁ := Eq.trans
    (tensorSheafMap_app_toTensorSheafSection (inverseImageBase (pullback.fst a b ≫ a))
      ((relativeInverseImage (pullback.fst a b) a).obj
        ((pushforward (toInverseImageBase a)).obj F.module))
      ((_root_.pullback (sndRelativeInverseImageProjection a b)).obj
        ((pushforward (toInverseImageBase b)).obj G.module))
      ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module))
      ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module))
      (relativeInverseImageToPullback (pullback.fst a b) a F.module)
      (sndRelativeInverseImageToPullback a b G.module) W₀ x y)
    (toTensorSheafSection_congr₂
      ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module))
      ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module))
      (op W₀) hleft hright)
  have step₂ := Eq.trans
    (inverseImageTensorLax_toTensorSheafSection (pullback.fst a b ≫ a)
      ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module)
      ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module) (op W₀)
      zL zR _ _ hzL.symm hzR.symm)
    (eq_of_heq hw)
  exact comp_val_app_apply_of (relativeBoxComparisonLeg₁ a b F G)
    (relativeBoxComparisonLeg₂ a b F G) (op W₀) _ step₁ step₂

/-! ### The box bifunctor read over `f^{-1}𝒪_S`, on morphisms -/

/-- The functor to the modules over the inverse image of `𝒪_S` acts on local sections by the
differential operator itself. -/
theorem toInverseImageModules_map_val_app {Z S' : Scheme.{u}} {c : Z ⟶ S'}
    {A B : FiniteOrderDifferentialOperatorCategory c} (D : A ⟶ B) (V : Z.Opensᵒᵖ)
    (z : ((toInverseImageModules c).obj A).val.obj V) :
    (((toInverseImageModules c).map D).val.app V).hom z = D.1 V z :=
  rfl

/-- **The box product of two operators, read over `f^{-1}𝒪_S`, acts on local sections by the
operator itself.** -/
theorem toInverseImageModules_boxHom_val_app
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G')
    (V : (Opens (inverseImageBase (pullback.fst a b ≫ a)).carrier)ᵒᵖ)
    (z : ((boxProductRelative a b).obj (F, G)).val.obj V) :
    (((toInverseImageModules (pullback.fst a b ≫ a)).map (boxHom D E)).val.app V).hom z =
      (boxHom D E).1 V z :=
  rfl

/-- **The box bifunctor read over `f^{-1}𝒪_S` sends a pair of operators to their box product**,
read over `f^{-1}𝒪_S`. -/
theorem boxProductRelative_map {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G') :
    (boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E) =
      (toInverseImageModules (pullback.fst a b ≫ a)).map (boxHom D E) :=
  CategoryTheory.Functor.comp_map _ _ _

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
