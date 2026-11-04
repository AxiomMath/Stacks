module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonSections

/-!
# Naturality of `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖` in the two differential operators

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a`. The comparison
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison` of
[Stacks, Tag 0G46] is natural in the pair of finite-order differential operators: for
`D : 𝓕 ⟶ 𝓕'` on `X/S` and `E : 𝓖 ⟶ 𝓖'` on `Y/S` the square

`p^{-1}D ⊗ q^{-1}E ≫ comparison(𝓕', 𝓖') = comparison(𝓕, 𝓖) ≫ (D ⊠ E)`

commutes.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison_naturality`:
  **the comparison is natural in the pair of differential operators.**
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory`
  `.boxProductRelative_map_externalTensorSection`: the box bifunctor read over `f^{-1}𝒪_S`
  carries the section of `𝓕 ⊠ 𝓖` attached to `s` and `t` to the section of `𝓕' ⊠ 𝓖'` attached to
  `D s` and `E t`.

## References

* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
open Stacks.DeRhamDirectImage
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.PullbackUnitGenerators
open Stacks.Tag01VSPullbackTensor
open Stacks.BoxKunnethSections

universe u

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-! ### An operator carried across the unit of the first inverse image -/

/-- **The inverse image along a morphism `g` of an operator, on a restricted pullback-unit
section**: it is the restriction of the pullback-unit section of the image. -/
private theorem pullback_toInverseImageModules_map_restrict_pullbackUnitSection
    {X' S' : Scheme.{u}} {c : X' ⟶ S'} {Z : RingedSpace.{u, u}} (g : Z ⟶ inverseImageBase c)
    {F F' : FiniteOrderDifferentialOperatorCategory c} (D : F ⟶ F')
    (U' : X'.Opens) (s : Γ(F.module, U')) (W₀ : Opens Z.carrier)
    (i : (opensMap g).op.obj (op U') ⟶ op W₀) :
    ((((toInverseImageModules c ⋙ pullback g).map D).val.app (op W₀)).hom
        ((((toInverseImageModules c ⋙ pullback g).obj F).val.map i).hom
          (pullbackUnitSection g ((toInverseImageModules c).obj F) (op U') s))) =
      (((toInverseImageModules c ⋙ pullback g).obj F').val.map i).hom
        (pullbackUnitSection g ((toInverseImageModules c).obj F') (op U') (D.1 (op U') s)) :=
  Eq.trans
    (app_map_apply ((toInverseImageModules c ⋙ pullback g).map D) i _)
    (congrArg (fun z ↦ (((toInverseImageModules c ⋙ pullback g).obj F').val.map i).hom z)
      (Eq.trans
        (map_pullbackUnitSection g ((toInverseImageModules c).map D) (op U') s)
        (pullbackUnitSection_congr g ((toInverseImageModules c).obj F') (op U')
          (toInverseImageModules_map_val_app D (op U') s))))

/-- **The inverse image along the first projection of an operator, on a restricted pullback-unit
section**: it is the restriction of the pullback-unit section of the image. -/
theorem leftRelativeInverseImage_map_restrict_pullbackUnitSection
    {F F' : FiniteOrderDifferentialOperatorCategory a} (D : F ⟶ F')
    (U' : X.Opens) (s : Γ(F.module, U')) (W₀ : (pullback a b).Opens)
    (i₁ : (opensMap (relativeInverseImageProjection (pullback.fst a b) a)).op.obj (op U') ⟶
      op W₀) :
    (((leftRelativeInverseImage a b).map D).val.app (op W₀)).hom
        ((((leftRelativeInverseImage a b).obj F).val.map i₁).hom
          (pullbackUnitSection (relativeInverseImageProjection (pullback.fst a b) a)
            ((toInverseImageModules a).obj F) (op U') s)) =
      (((leftRelativeInverseImage a b).obj F').val.map i₁).hom
        (pullbackUnitSection (relativeInverseImageProjection (pullback.fst a b) a)
          ((toInverseImageModules a).obj F') (op U') (D.1 (op U') s)) :=
  pullback_toInverseImageModules_map_restrict_pullbackUnitSection
    (relativeInverseImageProjection (pullback.fst a b) a) D U' s W₀ i₁

/-- **The inverse image along the second projection of an operator, on a restricted
pullback-unit section.** -/
theorem rightRelativeInverseImage_map_restrict_pullbackUnitSection
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G')
    (V' : Y.Opens) (t : Γ(G.module, V')) (W₀ : (pullback a b).Opens)
    (i₂ : (opensMap (sndRelativeInverseImageProjection a b)).op.obj (op V') ⟶ op W₀) :
    (((rightRelativeInverseImage a b).map E).val.app (op W₀)).hom
        ((((rightRelativeInverseImage a b).obj G).val.map i₂).hom
          (pullbackUnitSection (sndRelativeInverseImageProjection a b)
            ((toInverseImageModules b).obj G) (op V') t)) =
      (((rightRelativeInverseImage a b).obj G').val.map i₂).hom
        (pullbackUnitSection (sndRelativeInverseImageProjection a b)
          ((toInverseImageModules b).obj G') (op V') (E.1 (op V') t)) :=
  pullback_toInverseImageModules_map_restrict_pullbackUnitSection
    (sndRelativeInverseImageProjection a b) E V' t W₀ i₂

/-! ### The box product of two operators, on the section attached to a pair of sections -/

/-- **The box bifunctor read over `f^{-1}𝒪_S` carries the section of `𝓕 ⊠ 𝓖` attached to `s` and
`t` to the section of `𝓕' ⊠ 𝓖'` attached to `D s` and `E t`.** -/
theorem boxProductRelative_map_externalTensorSection
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G')
    (U' : X.Opens) (s : Γ(F.module, U')) (V' : Y.Opens) (t : Γ(G.module, V'))
    (W₀ : (pullback a b).Opens) (h₁ : W₀ ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : W₀ ≤ pullback.snd a b ⁻¹ᵁ V')
    (w : ((boxProductRelative a b).obj (F, G)).val.obj (op W₀))
    (hw : HEq (externalTensorSection a b F.module G.module s t W₀ h₁ h₂) w)
    (w' : ((boxProductRelative a b).obj (F', G')).val.obj (op W₀))
    (hw' : HEq (externalTensorSection a b F'.module G'.module (D.1 (op U') s) (E.1 (op V') t)
      W₀ h₁ h₂) w') :
    (((boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)).val.app (op W₀)).hom w =
      w' :=
  Eq.trans
    (congrArg (fun m ↦ (m.val.app (op W₀)).hom w) (boxProductRelative_map a b D E))
    (Eq.trans (toInverseImageModules_boxHom_val_app a b D E (op W₀) w)
      (Eq.trans (congrArg (fun z ↦ (boxHom D E).1 (op W₀) z) (eq_of_heq hw).symm)
        (Eq.trans (boxHom_externalTensorSection D E s t W₀ h₁ h₂) (eq_of_heq hw'))))

/-! ### The two sides of the naturality square, on a pure tensor of unit sections -/

/-- **The left-hand side of the naturality square on a pure tensor of restricted pullback-unit
sections**: the two operators are carried across the two units, and the comparison then produces
the section of `𝓕' ⊠ 𝓖'` attached to `D s` and `E t`. -/
theorem relativeBoxComparison_map_tmul
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G')
    (U' : X.Opens) (s : Γ(F.module, U')) (V' : Y.Opens) (t : Γ(G.module, V'))
    (W₀ : (pullback a b).Opens) (h₁ : W₀ ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : W₀ ≤ pullback.snd a b ⁻¹ᵁ V')
    (i₂ : (opensMap (sndRelativeInverseImageProjection a b)).op.obj (op V') ⟶ op W₀)
    (w' : ((boxProductRelative a b).obj (F', G')).val.obj (op W₀))
    (hw' : HEq (externalTensorSection a b F'.module G'.module (D.1 (op U') s) (E.1 (op V') t)
      W₀ h₁ h₂) w') :
    tensorEvalMap ((relativeInverseImageTensor a b).map (X := (F, G)) (Y := (F', G')) (D, E) ≫
          relativeBoxComparison a b F' G') (op W₀)
        ((((leftRelativeInverseImage a b).obj F).val.map (homOfLE h₁).op).hom
            (pullbackUnitSection (relativeInverseImageProjection (pullback.fst a b) a)
              ((toInverseImageModules a).obj F) (op U') s) ⊗ₜ
          (((rightRelativeInverseImage a b).obj G).val.map i₂).hom
            (pullbackUnitSection (sndRelativeInverseImageProjection a b)
              ((toInverseImageModules b).obj G) (op V') t)) = w' :=
  Eq.trans
    (Eq.trans
      (tensorEvalMap_tmul
        ((relativeInverseImageTensor a b).map (X := (F, G)) (Y := (F', G')) (D, E) ≫
          relativeBoxComparison a b F' G') (op W₀) _ _)
      (comp_val_app_apply_of
        ((relativeInverseImageTensor a b).map (X := (F, G)) (Y := (F', G')) (D, E))
        (relativeBoxComparison a b F' G') (op W₀) _
        (tensorSheafMap_app_toTensorSheafSection (inverseImageBase (pullback.fst a b ≫ a))
          _ _ _ _ ((leftRelativeInverseImage a b).map D) ((rightRelativeInverseImage a b).map E)
          W₀ _ _)
        (tensorEvalMap_tmul (relativeBoxComparison a b F' G') (op W₀) _ _).symm))
    (Eq.trans
      (congrArg₂ (fun z z' ↦ tensorEvalMap (relativeBoxComparison a b F' G') (op W₀)
          (z ⊗ₜ[(inverseImageBase (pullback.fst a b ≫ a)).presheaf.obj (op W₀)] z'))
        (leftRelativeInverseImage_map_restrict_pullbackUnitSection a b D U' s W₀ (homOfLE h₁).op)
        (rightRelativeInverseImage_map_restrict_pullbackUnitSection a b E V' t W₀ i₂))
      (relativeBoxComparison_tmul a b F' G' U' (D.1 (op U') s) V' (E.1 (op V') t) W₀ h₁ h₂ i₂
        _ _ rfl rfl _ _ HEq.rfl HEq.rfl w' hw'))

/-- **The right-hand side of the naturality square on a pure tensor of restricted pullback-unit
sections**: the comparison produces the section of `𝓕 ⊠ 𝓖` attached to `s` and `t`, and the box
product of the two operators then carries it to the section attached to `D s` and `E t`. -/
theorem relativeBoxComparison_tmul_map
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G')
    (U' : X.Opens) (s : Γ(F.module, U')) (V' : Y.Opens) (t : Γ(G.module, V'))
    (W₀ : (pullback a b).Opens) (h₁ : W₀ ≤ pullback.fst a b ⁻¹ᵁ U')
    (h₂ : W₀ ≤ pullback.snd a b ⁻¹ᵁ V')
    (i₂ : (opensMap (sndRelativeInverseImageProjection a b)).op.obj (op V') ⟶ op W₀)
    (w : ((boxProductRelative a b).obj (F, G)).val.obj (op W₀))
    (hw : HEq (externalTensorSection a b F.module G.module s t W₀ h₁ h₂) w)
    (w' : ((boxProductRelative a b).obj (F', G')).val.obj (op W₀))
    (hw' : HEq (externalTensorSection a b F'.module G'.module (D.1 (op U') s) (E.1 (op V') t)
      W₀ h₁ h₂) w') :
    tensorEvalMap (relativeBoxComparison a b F G ≫
          (boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)) (op W₀)
        ((((leftRelativeInverseImage a b).obj F).val.map (homOfLE h₁).op).hom
            (pullbackUnitSection (relativeInverseImageProjection (pullback.fst a b) a)
              ((toInverseImageModules a).obj F) (op U') s) ⊗ₜ
          (((rightRelativeInverseImage a b).obj G).val.map i₂).hom
            (pullbackUnitSection (sndRelativeInverseImageProjection a b)
              ((toInverseImageModules b).obj G) (op V') t)) = w' :=
  Eq.trans
    (Eq.trans
      (tensorEvalMap_tmul (relativeBoxComparison a b F G ≫
        (boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)) (op W₀) _ _)
      (comp_val_app_apply_of (relativeBoxComparison a b F G)
        ((boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)) (op W₀) _ rfl
        (congrArg
          (fun z ↦ (((boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)).val.app
            (op W₀)).hom z)
          (tensorEvalMap_tmul (relativeBoxComparison a b F G) (op W₀) _ _).symm)))
    (Eq.trans
      (congrArg
        (fun z ↦ (((boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E)).val.app
          (op W₀)).hom z)
        (relativeBoxComparison_tmul a b F G U' s V' t W₀ h₁ h₂ i₂ _ _ rfl rfl _ _
          HEq.rfl HEq.rfl w hw))
      (boxProductRelative_map_externalTensorSection a b D E U' s V' t W₀ h₁ h₂ w hw w' hw'))

/-! ### The naturality square -/

/-- **The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖` is natural in the pair of
finite-order differential operators.** For `D : 𝓕 ⟶ 𝓕'` on `X/S` and `E : 𝓖 ⟶ 𝓖'` on `Y/S` the
comparison intertwines `p^{-1}D ⊗ q^{-1}E` with the box product `D ⊠ E` read over `f^{-1}𝒪_S`. -/
theorem relativeBoxComparison_naturality
    {F F' : FiniteOrderDifferentialOperatorCategory a}
    {G G' : FiniteOrderDifferentialOperatorCategory b} (D : F ⟶ F') (E : G ⟶ G') :
    (relativeInverseImageTensor a b).map (X := (F, G)) (Y := (F', G')) (D, E) ≫
        relativeBoxComparison a b F' G' =
      relativeBoxComparison a b F G ≫
        (boxProductRelative a b).map (X := (F, G)) (Y := (F', G')) (D, E) := by
  refine relativeInverseImageTensor_hom_ext a b F G ?_
  rintro ⟨W₀⟩ x y ⟨⟨U'⟩, i₁, s, rfl⟩ ⟨⟨V'⟩, i₂, t, rfl⟩
  obtain ⟨h₁, rfl⟩ : ∃ h : W₀ ≤ pullback.fst a b ⁻¹ᵁ U', i₁ = (homOfLE h).op :=
    ⟨leOfHom i₁.unop, Subsingleton.elim _ _⟩
  have h₂ : W₀ ≤ pullback.snd a b ⁻¹ᵁ V' :=
    (leOfHom i₂.unop : W₀ ≤ (opensMap (sndRelativeInverseImageProjection a b)).obj V').trans
      (opensMap_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
        (pullback.fst a b ≫ a) pullback.condition.symm V').le
  obtain ⟨w, hw⟩ : ∃ w : ((boxProductRelative a b).obj (F, G)).val.obj (op W₀),
      HEq (externalTensorSection a b F.module G.module s t W₀ h₁ h₂) w := ⟨_, HEq.rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : ((boxProductRelative a b).obj (F', G')).val.obj (op W₀),
      HEq (externalTensorSection a b F'.module G'.module (D.1 (op U') s) (E.1 (op V') t)
        W₀ h₁ h₂) w' := ⟨_, HEq.rfl⟩
  exact (relativeBoxComparison_map_tmul a b D E U' s V' t W₀ h₁ h₂ i₂ w' hw').trans
    (relativeBoxComparison_tmul_map a b D E U' s V' t W₀ h₁ h₂ i₂ w hw w' hw').symm

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
