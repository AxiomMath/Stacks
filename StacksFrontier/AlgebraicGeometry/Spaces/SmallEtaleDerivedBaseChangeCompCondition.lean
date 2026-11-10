module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompKunneth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompKunnethLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf

/-!
# Stacks 0DKH from condition (2) of Stacks 0DKG

For a cartesian square `g' ≫ f = f' ≫ g` of algebraic spaces with `f` quasi-compact and
quasi-separated, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, the composite
`Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is invertible as soon as condition (2) of Stacks 0DKG
holds: the composite of Stacks 065Z is an isomorphism on every affine étale quadruple.

The proof reduces to squares of affine étale charts of `Y'` and `Y`, then by the Künneth
reduction and its étale locality on `X` to squares of affine representables, where the
composite is read on the ring comparison.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Coherence

variable {P U Xv X Xw X' : AlgebraicSpaces B S hS}

/-- **A coherence of iterated derived pullbacks** for the restriction of a map
`L(g')^*K ⟶ K'` along a square of charts, through the composition laws and the transports. -/
theorem smallEtaleDerivedModulePullback_chart_coherence (fs : P ⟶ U) (u : U ⟶ Xv) (ι : Xv ⟶ X)
    (qi : P ⟶ Xw) (ιW : Xw ⟶ X')
    (g' : X' ⟶ X) (c : Xw ⟶ Xv) (e1 : c ≫ ι = ιW ≫ g') (e2 : qi ≫ c = fs ≫ u)
    (ha' : @CategoryStruct.comp (ObjectProperty.FullSubcategory
        fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) _ _ _ _ fs
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ u ι) =
      @CategoryStruct.comp (ObjectProperty.FullSubcategory
        fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) _ _ _ _
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ qi ιW) g')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS fs).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS u ι).inv.app K) ≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS fs u).hom ≫
            (smallEtaleDerivedModulePullbackSquareIso B S hS c u fs qi e2).inv).app
          ((smallEtaleDerivedModulePullback B S hS ι).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS qi).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS c ι).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K) =
      (smallEtaleDerivedModulePullbackCompIso B S hS fs (u ≫ ι)).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (qi ≫ ιW) g').inv.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).inv.app
          ((smallEtaleDerivedModulePullback B S hS g').obj K) := by
  suffices key : ((smallEtaleDerivedModulePullback B S hS fs).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS u ι).inv.app K) ≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS fs u).hom ≫
            (smallEtaleDerivedModulePullbackSquareIso B S hS c u fs qi e2).inv).app
          ((smallEtaleDerivedModulePullback B S hS ι).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS qi).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS c ι).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K)) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).hom.app
          ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS (qi ≫ ιW) g').hom.app K =
      (smallEtaleDerivedModulePullbackCompIso B S hS fs (u ≫ ι)).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K by
    rw [← reassoc_of% key]
    simp
  have hA := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS qi ιW g' K
  have hB := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS qi c ι K
  have hC := smallEtaleDerivedModulePullbackCompIso_assoc_app B S hS fs u ι K
  have hR := smallEtaleDerivedModulePullbackCompIso_congr_right B S hS qi e1 K
  have hL := smallEtaleDerivedModulePullbackCompIso_congr_left B S hS e2.symm ι K
  have hS' := smallEtaleDerivedPullbackSquareIso_inv_app B S hS c u fs qi e2
    ((smallEtaleDerivedModulePullback B S hS ι).obj K)
  simp only [Category.assoc]
  rw [hA, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Functor.map_comp_assoc, smallEtaleDerivedModulePullbackCongr_hom_app, hR,
    ← Category.assoc ((smallEtaleDerivedModulePullback B S hS qi).map _), ← hB,
    NatTrans.comp_app, hS']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hL,
    ← Category.assoc ((smallEtaleDerivedModulePullbackCompIso B S hS fs u).hom.app _), hC]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    smallEtaleDerivedModulePullbackCongr_hom_app]
  simp

/-- `smallEtaleDerivedModulePullback_chart_coherence` with the map `φ : L(g')^*K ⟶ K'`, in the
form consumed by `isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso`. -/
theorem smallEtaleDerivedModulePullback_chart_coherence_map (fs : P ⟶ U) (u : U ⟶ Xv)
    (ι : Xv ⟶ X) (qi : P ⟶ Xw) (ιW : Xw ⟶ X') (g' : X' ⟶ X) (c : Xw ⟶ Xv)
    (e1 : c ≫ ι = ιW ≫ g') (e2 : qi ≫ c = fs ≫ u)
    (ha' : @CategoryStruct.comp (ObjectProperty.FullSubcategory
        fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) _ _ _ _ fs
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ u ι) =
      @CategoryStruct.comp (ObjectProperty.FullSubcategory
        fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F) _ _ _ _
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ qi ιW) g')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    @CategoryStruct.comp _ _
      ((smallEtaleDerivedModulePullback B S hS fs).obj
        ((smallEtaleDerivedModulePullback B S hS (u ≫ ι)).obj K))
      ((smallEtaleDerivedModulePullback B S hS fs).obj
        ((smallEtaleDerivedModulePullback B S hS u).obj
          ((smallEtaleDerivedModulePullback B S hS ι).obj K)))
      ((smallEtaleDerivedModulePullback B S hS qi).obj
        ((smallEtaleDerivedModulePullback B S hS ιW).obj K'))
      ((smallEtaleDerivedModulePullback B S hS fs).map
        (@Iso.hom _ _ ((smallEtaleDerivedModulePullback B S hS (u ≫ ι)).obj K)
          ((smallEtaleDerivedModulePullback B S hS u).obj
            ((smallEtaleDerivedModulePullback B S hS ι).obj K))
          ((smallEtaleDerivedModulePullbackCompIso B S hS u ι).app K).symm))
      (((smallEtaleDerivedModulePullbackCompIso B S hS fs u).hom ≫
          (smallEtaleDerivedModulePullbackSquareIso B S hS c u fs qi e2).inv).app
          ((smallEtaleDerivedModulePullback B S hS ι).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS qi).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS c ι).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS ιW).map φ)) =
      @CategoryStruct.comp _ _
        ((smallEtaleDerivedModulePullback B S hS fs).obj
          ((smallEtaleDerivedModulePullback B S hS (u ≫ ι)).obj K))
        ((smallEtaleDerivedModulePullback B S hS (qi ≫ ιW)).obj K')
        ((smallEtaleDerivedModulePullback B S hS qi).obj
          ((smallEtaleDerivedModulePullback B S hS ιW).obj K'))
        ((smallEtaleDerivedModulePullbackCompIso B S hS fs (u ≫ ι)).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS (qi ≫ ιW) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (qi ≫ ιW)).map φ)
        (@Iso.hom _ _ ((smallEtaleDerivedModulePullback B S hS (qi ≫ ιW)).obj K')
          ((smallEtaleDerivedModulePullback B S hS qi).obj
            ((smallEtaleDerivedModulePullback B S hS ιW).obj K'))
          ((smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).app K').symm) := by
  have hc := smallEtaleDerivedModulePullback_chart_coherence B S hS fs u ι qi ιW g' c e1 e2 ha' K
  have hn : (smallEtaleDerivedModulePullback B S hS (qi ≫ ιW)).map φ ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).inv.app K' =
      (smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).inv.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B S hS qi).map
        ((smallEtaleDerivedModulePullback B S hS ιW).map φ) :=
    (smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).inv.naturality φ
  simp only [Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc] at hc ⊢
  rw [hn, ← reassoc_of% hc]

end Coherence

section Congr

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- Transport of the composite of Stacks 0DKH along equalities of the vertical morphisms. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_congr_vertical {f₁ f₂ : X ⟶ Y} {f₁' f₂' : X' ⟶ Y'}
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (hf : f₁ = f₂) (hf' : f₁' = f₂') (w₁ : g' ≫ f₁ = f₁' ≫ g)
    (w₂ : g' ≫ f₂ = f₂' ≫ g) (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f₁ g f₁' g' w₁ K K' φ)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f₂ g f₂' g' w₂ K K' φ) := by
  subst hf hf'
  exact h

end Congr

section Quadruple

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **Condition (2) of Stacks 0DKG at one affine quadruple**, read on the composite of Stacks
0DKH for its square of affine representables. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_quadruple
    (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ)
    {U V V' U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom)
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (hfa : representedSpaceMap B S hS f₀ ≫ b = a ≫ f)
    (hgb : representedSpaceMap B S hS g₀ ≫ b = c ≫ g)
    (hfc : representedSpaceMap B S hS f₀' ≫ c = a' ≫ f')
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g') :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
      ((smallEtaleDerivedModulePullback B S hS a).obj K)
      ((smallEtaleDerivedModulePullback B S hS a').obj K')
      ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
          a).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS a').map φ)) :=
  (isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff B S hS f₀ g₀ f₀' g₀' w₀ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK') _).mpr
    (h2.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb hfa hgb hfc ha')

end Quadruple








section Stack

variable {X₁ X₁' Y₁ Y₁' U₁ P₁ : AlgebraicSpaces B S hS}

/-- The composite of Stacks 0DKH for a square `P₁ ⟶ U₁` over `Y₁' ⟶ Y₁` stacked on a square
`X₁' ⟶ X₁` over `Y₁' ⟶ Y₁` along a chart `u : U₁ ⟶ X₁`, at the restrictions `Lu^*E`,
`L(q)^*K'` and the map induced by `φ : L(c₁)^*E ⟶ K'`. -/
noncomputable def smallEtaleDerivedBaseChangeCompStack (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁' ⟶ Y₁)
    (f₁' : X₁' ⟶ Y₁') (c₁ : X₁' ⟶ X₁) (u : U₁ ⟶ X₁) (p : P₁ ⟶ U₁) (q : P₁ ⟶ X₁')
    (wT : p ≫ u ≫ f₁ = (q ≫ f₁') ≫ g₁) (e : q ≫ c₁ = p ≫ u)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁')))
    (φ : (smallEtaleDerivedModulePullback B S hS c₁).obj E ⟶ K') :=
  smallEtaleDerivedBaseChangeComp B S hS (u ≫ f₁) g₁ (q ≫ f₁') p wT
    ((smallEtaleDerivedModulePullback B S hS u).obj E)
    ((smallEtaleDerivedModulePullback B S hS q).obj K')
    (((smallEtaleDerivedModulePullbackCompIso B S hS p u).hom ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS c₁ u p q e).inv).app E ≫
      (smallEtaleDerivedModulePullback B S hS q).map φ)

end Stack

section ChartQuadruple

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The affine step of the reduction.** For a square of charts `X'_1 ⟶ X_1` over
`W₀ ⟶ V₀` mapping étale to the original square, an affine chart `u : U₀ ⟶ X_1` and the induced
`P₀ = W₀ ×_{V₀} U₀`, condition (2) of Stacks 0DKG gives the invertibility of the composite of
Stacks 0DKH for the square of `P₀ ⟶ U₀` over `W₀ ⟶ V₀`, at the restrictions of `K`, `K'`, `φ`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chartQuadruple
    (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ)
    {X₁ X₁' : AlgebraicSpaces B S hS} {V₀ W₀ U₀ P₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P₀)]
    (f₁ : X₁ ⟶ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
    (f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩) (c₁ : X₁' ⟶ X₁)
    (q₀ : W₀ ⟶ V₀) (ι : X₁ ⟶ X) (ιW : X₁' ⟶ X')
    (b : (⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (cW : (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (hι : IsEtale B S hS ι.hom) (hb : IsEtale B S hS b.hom) (hcW : IsEtale B S hS cW.hom)
    (e1 : c₁ ≫ ι = ιW ≫ g') (hιf : ι ≫ f = f₁ ≫ b) (hιWf : ιW ≫ f' = f₁' ≫ cW)
    (hq₀ : representedSpaceMap B S hS q₀ ≫ b = cW ≫ g)
    (u : (⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ : AlgebraicSpaces B S hS) ⟶ X₁)
    (hu : IsEtale B S hS u.hom) (f₀ : U₀ ⟶ V₀) (hf₀ : representedSpaceMap B S hS f₀ = u ≫ f₁)
    (fs : P₀ ⟶ U₀) (sn : P₀ ⟶ W₀) (hpb : IsPullback fs sn f₀ q₀)
    (qi : (⟨yoneda.obj P₀, isAlgebraicSpace_yoneda B S hS P₀⟩ : AlgebraicSpaces B S hS) ⟶ X₁')
    (e2 : qi ≫ c₁ = representedSpaceMap B S hS fs ≫ u)
    (hqi : qi ≫ f₁' = representedSpaceMap B S hS sn)
    (wT : representedSpaceMap B S hS fs ≫ u ≫ f₁ = (qi ≫ f₁') ≫ representedSpaceMap B S hS q₀) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (u ≫ f₁) (representedSpaceMap B S hS q₀)
      (qi ≫ f₁') (representedSpaceMap B S hS fs) wT
      ((smallEtaleDerivedModulePullback B S hS u).obj
        ((smallEtaleDerivedModulePullback B S hS ι).obj K))
      ((smallEtaleDerivedModulePullback B S hS qi).obj
        ((smallEtaleDerivedModulePullback B S hS ιW).obj K'))
      (((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS fs) u).hom ≫
          (smallEtaleDerivedModulePullbackSquareIso B S hS c₁ u (representedSpaceMap B S hS fs) qi
            e2).inv).app ((smallEtaleDerivedModulePullback B S hS ι).obj K) ≫
        (smallEtaleDerivedModulePullback B S hS qi).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS c₁ ι).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS ιW).map φ))) := by
  have ha' : representedSpaceMap B S hS fs ≫ u ≫ ι = (qi ≫ ιW) ≫ g' := by
    rw [← Category.assoc, ← e2, Category.assoc, e1, Category.assoc]
  have hfa : representedSpaceMap B S hS f₀ ≫ b = (u ≫ ι) ≫ f := by
    rw [hf₀, Category.assoc, Category.assoc, hιf]
  have hfc : representedSpaceMap B S hS sn ≫ cW = (qi ≫ ιW) ≫ f' := by
    rw [← hqi, Category.assoc, Category.assoc, hιWf]
  have T := isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_quadruple B S hS
    f g f' g' w K hK K' hK' φ h2 (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ u ι) b cW
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ qi ιW) f₀ q₀ sn fs hpb.w
    (isEtale_comp B S hS hu hι) hb hcW hpb hfa hq₀ hfc ha'
  refine isIso_smallEtaleDerivedBaseChangeComp_congr_vertical B S hS _ _ hf₀ hqi.symm _ _ _ _ _
    ((isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
      (representedSpaceMap_square B S hS f₀ q₀ sn fs hpb.w) _ _ _ _ _ _
      ((smallEtaleDerivedModulePullbackCompIso B S hS u ι).app K).symm
      ((smallEtaleDerivedModulePullbackCompIso B S hS qi ιW).app K').symm ?_).mp T)
  exact smallEtaleDerivedModulePullback_chart_coherence_map B S hS _ u ι qi ιW g' c₁ e1 e2 ha'
    K K' φ

/-- `isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chartQuadruple` for
algebraic spaces `U₁ = U₀` and `P₁ = P₀` given up to equality, so that it applies to charts
spelled as `chartSpace`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chartQuadruple_of_eq
    (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ)
    {X₁ X₁' : AlgebraicSpaces B S hS} {V₀ W₀ U₀ P₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P₀)]
    (f₁ : X₁ ⟶ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
    (f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩) (c₁ : X₁' ⟶ X₁)
    (q₀ : W₀ ⟶ V₀) (ι : X₁ ⟶ X) (ιW : X₁' ⟶ X')
    (b : (⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (cW : (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (hι : IsEtale B S hS ι.hom) (hb : IsEtale B S hS b.hom) (hcW : IsEtale B S hS cW.hom)
    (e1 : c₁ ≫ ι = ιW ≫ g') (hιf : ι ≫ f = f₁ ≫ b) (hιWf : ιW ≫ f' = f₁' ≫ cW)
    (hq₀ : representedSpaceMap B S hS q₀ ≫ b = cW ≫ g)
    {U₁ P₁ : AlgebraicSpaces B S hS}
    (hU₁ : U₁ = ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩)
    (hP₁ : P₁ = ⟨yoneda.obj P₀, isAlgebraicSpace_yoneda B S hS P₀⟩)
    (u : U₁ ⟶ X₁) (hu : IsEtale B S hS u.hom) (f₀ : U₀ ⟶ V₀)
    (hf₀ : eqToHom hU₁.symm ≫ u ≫ f₁ = representedSpaceMap B S hS f₀)
    (fs : P₀ ⟶ U₀) (sn : P₀ ⟶ W₀) (hpb : IsPullback fs sn f₀ q₀) (p : P₁ ⟶ U₁)
    (hp : eqToHom hP₁.symm ≫ p = representedSpaceMap B S hS fs ≫ eqToHom hU₁.symm)
    (qi : P₁ ⟶ X₁') (e2 : qi ≫ c₁ = p ≫ u)
    (hqi : eqToHom hP₁.symm ≫ qi ≫ f₁' = representedSpaceMap B S hS sn)
    (wT : p ≫ u ≫ f₁ = (qi ≫ f₁') ≫ representedSpaceMap B S hS q₀) :
    IsIso (smallEtaleDerivedBaseChangeCompStack B S hS f₁ (representedSpaceMap B S hS q₀) f₁' c₁
      u p qi wT e2 ((smallEtaleDerivedModulePullback B S hS ι).obj K)
      ((smallEtaleDerivedModulePullback B S hS ιW).obj K')
      ((smallEtaleDerivedModulePullbackCompIso B S hS c₁ ι).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS ιW).map φ)) := by
  subst hU₁ hP₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf₀ hp hqi
  subst hp
  exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chartQuadruple B S hS
    f g f' g' w K hK K' hK' φ h2 f₁ f₁' c₁ q₀ ι ιW b cW hι hb hcW e1 hιf hιWf hq₀ u hu f₀ hf₀.symm
    fs sn hpb qi e2 hqi wT

end ChartQuadruple


section KunnethCover

variable {X₁ X₁' Y₁ Y₁' : AlgebraicSpaces B S hS} (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁' ⟶ Y₁) (f₁' : X₁' ⟶ Y₁')
  (c₁ : X₁' ⟶ X₁)

/-- **The Künneth reduction of Stacks 0DKH, étale local on `X`.** For a cartesian square with
`f, g` quasi-compact and quasi-separated and `Y'` affine, the composite attached to `φ` is
invertible as soon as, for a covering family of affine étale charts `V i` of `X` and cartesian
squares `U'_i = V i ×_X X'`, the composites for the squares `U'_i ⟶ V i` over `Y' ⟶ Y`, at the
restrictions of `E`, `K'`, `φ`, are. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_coversTop_of_isAffine
    (sq₁ : IsPullback c₁ f₁' f₁ g₁)
    (hfqc : IsQuasiCompact B S hS f₁.hom) (hfqs : IsQuasiSeparated B S hS f₁.hom)
    (hgqc : IsQuasiCompact B S hS g₁.hom) (hgqs : IsQuasiSeparated B S hS g₁.hom)
    (hY' : IsAffineSpace B S hS Y₁'.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁)))
    (hE : QcohDerived B S hS X₁ E)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁')))
    (hK' : QcohDerived B S hS X₁' K')
    (φ : (smallEtaleDerivedModulePullback B S hS c₁).obj E ⟶ K')
    {ι : Type*} {V : ι → SmallEtale B S hS X₁.1}
    (hV : (SmallEtale.topology B S hS X₁.1).CoversTop V)
    (hVa : ∀ i, IsAffineSpace B S hS (chartSpace B S hS X₁ (V i)).1)
    (U' : ι → AlgebraicSpaces B S hS) (p : ∀ i, U' i ⟶ chartSpace B S hS X₁ (V i))
    (q : ∀ i, U' i ⟶ X₁')
    (sq : ∀ i, IsPullback (q i) (p i) c₁ (chartToSpace B S hS X₁ (V i)))
    (hfV : ∀ i, IsQuasiCompact B S hS (chartToSpace B S hS X₁ (V i) ≫ f₁).hom)
    (hfV' : ∀ i, IsQuasiSeparated B S hS (chartToSpace B S hS X₁ (V i) ≫ f₁).hom)
    (h : ∀ i, IsIso (smallEtaleDerivedBaseChangeCompStack B S hS f₁ g₁ f₁' c₁
        (chartToSpace B S hS X₁ (V i)) (p i) (q i)
        (comp_stack B S hS _ f₁ _ f₁' _ c₁ g₁ (sq i).w.symm sq₁.w) (sq i).w E K' φ)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f₁ g₁ f₁' c₁ sq₁.w E K' φ) := by
  refine isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensorBaseChangeCompMap B S hS _ _ _ _ sq₁
    hfqc hfqs hgqc hgqs hY' E hE K' hK' φ ?_
  refine isIso_smallEtaleTensorBaseChangeCompMap_of_coversTop B S hS f₁ g₁ f₁' c₁ sq₁.w E K' φ hV
    U' p q sq fun i => ?_
  have sqi : IsPullback (p i) (q i ≫ f₁') (chartToSpace B S hS X₁ (V i) ≫ f₁) g₁ :=
    (sq i).flip.paste_vert sq₁
  exact isIso_smallEtaleTensorBaseChangeCompMap_of_isIso B S hS _ _ _ _ sqi (hfV i) (hfV' i)
    hgqc hgqs (hVa i) _ (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ _ hE) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ _ hK') _ (h i)

end KunnethCover

section Chart

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- The pullback in the big fppf site of two morphisms of affine objects is affine. -/
theorem isAffine_toScheme_pullback {U V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (a : U ⟶ V) (c : W ⟶ V) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback a c)) :=
  IsAffine.of_isPullback ((IsPullback.of_hasPullback a c).map (BigFppfOver.toScheme B S hS))

/-- A cartesian square of the big fppf site gives a cartesian square of represented algebraic
spaces. -/
theorem isPullback_representedSpaceMap {P U V W : BigFppfOver B S hS} {a : P ⟶ U} {b : P ⟶ W}
    {c : U ⟶ V} {d : W ⟶ V} (h : IsPullback a b c d) :
    IsPullback (representedSpaceMap B S hS a) (representedSpaceMap B S hS b)
      (representedSpaceMap B S hS c) (representedSpaceMap B S hS d) :=
  IsPullback.of_map (ObjectProperty.ι _)
    (ObjectProperty.hom_ext _ (by
      change yoneda.map a ≫ yoneda.map c = yoneda.map b ≫ yoneda.map d
      rw [← yoneda.map_comp, h.w, yoneda.map_comp]))
    (h.map yoneda)

section ChartFamily

variable {X₁ X₁' : AlgebraicSpaces B S hS} {V₀ W₀ : BigFppfOver B S hS}
  (f₁ : X₁ ⟶ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩) (q₀ : W₀ ⟶ V₀)
  (i : {U : SmallEtale B S hS X₁.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X₁.1).obj U))})

/-- The morphism of the big fppf site underlying an affine chart of `X₁` followed by
`f₁ : X₁ ⟶ V₀`. -/
noncomputable def affineChartBaseMap : (SmallEtale.toOver B S hS X₁.1).obj i.1 ⟶ V₀ :=
  Yoneda.fullyFaithful.preimage (chartToSpace B S hS X₁ i.1 ≫ f₁).hom

theorem representedSpaceMap_affineChartBaseMap :
    representedSpaceMap B S hS (affineChartBaseMap B S hS f₁ i) = chartToSpace B S hS X₁ i.1 ≫ f₁ :=
  ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)

/-- The fibre product `U ×_{V₀} W₀` of an affine chart `U` of `X₁` with `q₀ : W₀ ⟶ V₀`. -/
noncomputable def affineChartPullback : BigFppfOver B S hS :=
  pullback (affineChartBaseMap B S hS f₁ i) q₀

/-- The algebraic space represented by `affineChartPullback`. -/
noncomputable def affineChartPullbackSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (affineChartPullback B S hS f₁ q₀ i), isAlgebraicSpace_yoneda B S hS _⟩

/-- The first projection of `affineChartPullback`, as a morphism of algebraic spaces. -/
noncomputable def affineChartPullbackFst :
    affineChartPullbackSpace B S hS f₁ q₀ i ⟶ chartSpace B S hS X₁ i.1 :=
  representedSpaceMap B S hS (pullback.fst (affineChartBaseMap B S hS f₁ i) q₀)

theorem affineChartPullback_condition :
    (affineChartPullbackFst B S hS f₁ q₀ i ≫ chartToSpace B S hS X₁ i.1) ≫ f₁ =
      representedSpaceMap B S hS (pullback.snd (affineChartBaseMap B S hS f₁ i) q₀) ≫
        representedSpaceMap B S hS q₀ :=
  (Category.assoc _ _ _).trans <| (congrArg (fun k =>
    representedSpaceMap B S hS (pullback.fst (affineChartBaseMap B S hS f₁ i) q₀) ≫ k)
      (representedSpaceMap_affineChartBaseMap B S hS f₁ i)).symm.trans <|
    (representedSpaceMap_comp B S hS _ _).trans <|
    (congrArg (representedSpaceMap B S hS) pullback.condition).trans
    (representedSpaceMap_comp B S hS _ _).symm

/-- The morphism `affineChartPullbackSpace ⟶ X₁'` into a cartesian square `sq₁`. -/
noncomputable def affineChartPullbackLift {c₁ : X₁' ⟶ X₁}
    {f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩}
    (sq₁ : IsPullback c₁ f₁' f₁ (representedSpaceMap B S hS q₀))
    (j : {U : SmallEtale B S hS X₁.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X₁.1).obj U))}) :
    affineChartPullbackSpace B S hS f₁ q₀ j ⟶ X₁' :=
  sq₁.lift _ _ (affineChartPullback_condition B S hS f₁ q₀ j)

theorem affineChartPullbackLift_comp_snd {c₁ : X₁' ⟶ X₁}
    {f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩}
    (sq₁ : IsPullback c₁ f₁' f₁ (representedSpaceMap B S hS q₀)) :
    affineChartPullbackLift B S hS f₁ q₀ sq₁ i ≫ f₁' =
      representedSpaceMap B S hS (pullback.snd (affineChartBaseMap B S hS f₁ i) q₀) :=
  sq₁.lift_snd _ _ _

theorem affineChartPullbackLift_comp_fst {c₁ : X₁' ⟶ X₁}
    {f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩}
    (sq₁ : IsPullback c₁ f₁' f₁ (representedSpaceMap B S hS q₀)) :
    affineChartPullbackLift B S hS f₁ q₀ sq₁ i ≫ c₁ =
      affineChartPullbackFst B S hS f₁ q₀ i ≫ chartToSpace B S hS X₁ i.1 :=
  sq₁.lift_fst _ _ _

end ChartFamily

end Chart

section ChartMain

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The chart step of the reduction.** For a cartesian square of charts `X'_1 ⟶ X_1` over
`W₀ ⟶ V₀` (affine) mapping étale to the original square, with `X_1 ⟶ V₀` quasi-compact and
quasi-separated, condition (2) of Stacks 0DKG for the original square gives the invertibility of
the composite of Stacks 0DKH for the square of charts at the restrictions of `K`, `K'`, `φ`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chart
    (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ)
    {X₁ X₁' : AlgebraicSpaces B S hS} {V₀ W₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    (f₁ : X₁ ⟶ ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
    (f₁' : X₁' ⟶ ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩) (c₁ : X₁' ⟶ X₁)
    (q₀ : W₀ ⟶ V₀) (sq₁ : IsPullback c₁ f₁' f₁ (representedSpaceMap B S hS q₀))
    (hf₁qc : IsQuasiCompact B S hS f₁.hom) (hf₁qs : IsQuasiSeparated B S hS f₁.hom)
    (ι : X₁ ⟶ X) (ιW : X₁' ⟶ X')
    (b : (⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (cW : (⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (hι : IsEtale B S hS ι.hom) (hb : IsEtale B S hS b.hom) (hcW : IsEtale B S hS cW.hom)
    (e1 : c₁ ≫ ι = ιW ≫ g') (hιf : ι ≫ f = f₁ ≫ b) (hιWf : ιW ≫ f' = f₁' ≫ cW)
    (hq₀ : representedSpaceMap B S hS q₀ ≫ b = cW ≫ g) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f₁ (representedSpaceMap B S hS q₀) f₁' c₁ sq₁.w
      ((smallEtaleDerivedModulePullback B S hS ι).obj K)
      ((smallEtaleDerivedModulePullback B S hS ιW).obj K')
      ((smallEtaleDerivedModulePullbackCompIso B S hS c₁ ι).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS ιW).map φ))   := by
  have hV₀ := isAffineSpace_yoneda B S hS V₀ inferInstance
  have hW₀ := isAffineSpace_yoneda B S hS W₀ inferInstance
  have hqcs : ∀ {F G : AlgebraicSpaces B S hS} (h : F ⟶ G), IsAffineSpace B S hS F.1 →
      IsAffineSpace B S hS G.1 → IsQuasiCompact B S hS h.hom ∧ IsQuasiSeparated B S hS h.hom :=
    fun h hF hG => let hA := isAffineHom_of_isAffineSpace B S hS _ hF hG
      ⟨isQuasiCompact_of_isAffineHom_hom _ hA, isQuasiSeparated_of_isAffineHom_hom _ hA⟩
  have hout : ∀ i, IsPullback (affineChartPullbackFst B S hS f₁ q₀ i)
      (affineChartPullbackLift B S hS f₁ q₀ sq₁ i ≫ f₁') (chartToSpace B S hS X₁ i.1 ≫ f₁)
      (representedSpaceMap B S hS q₀) := by
    intro i
    have h := isPullback_representedSpaceMap B S hS
      (IsPullback.of_hasPullback (affineChartBaseMap B S hS f₁ i) q₀)
    rwa [← affineChartPullbackLift_comp_snd B S hS f₁ q₀ i sq₁,
      representedSpaceMap_affineChartBaseMap B S hS f₁ i] at h
  have hsq : ∀ i, IsPullback (affineChartPullbackLift B S hS f₁ q₀ sq₁ i)
      (affineChartPullbackFst B S hS f₁ q₀ i) c₁ (chartToSpace B S hS X₁ i.1) := fun i =>
    IsPullback.of_right (hout i).flip (affineChartPullbackLift_comp_fst B S hS f₁ q₀ i sq₁)
      sq₁.flip
  have hAi : ∀ i : {U : SmallEtale B S hS X₁.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X₁.1).obj U))},
      IsAffineSpace B S hS (chartSpace B S hS X₁ i.1).1 := fun i =>
    isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS X₁.1).obj i.1) i.2
  refine isIso_smallEtaleDerivedBaseChangeComp_of_coversTop_of_isAffine B S hS f₁
    (representedSpaceMap B S hS q₀) f₁' c₁ sq₁ hf₁qc hf₁qs
    (hqcs _ hW₀ hV₀).1 (hqcs _ hW₀ hV₀).2 hW₀ _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ ι K hK) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ ιW K' hK') _ (V := Subtype.val)
    (SmallEtale.coversTop_affineCharts B S hS X₁.1)
    hAi (affineChartPullbackSpace B S hS f₁ q₀) (affineChartPullbackFst B S hS f₁ q₀)
    (affineChartPullbackLift B S hS f₁ q₀ sq₁) hsq
    (fun i => (hqcs _ (hAi i) hV₀).1) (fun i => (hqcs _ (hAi i) hV₀).2) fun i => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X₁.1).obj i.1)) := i.2
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (affineChartPullback B S hS f₁ q₀ i)) :=
    isAffine_toScheme_pullback B S hS _ _
  exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chartQuadruple_of_eq
    B S hS f g f' g' w K hK K' hK' φ h2 f₁ f₁' c₁ q₀ ι ιW b cW hι hb hcW e1 hιf hιWf hq₀
    (U₀ := (SmallEtale.toOver B S hS X₁.1).obj i.1) (P₀ := affineChartPullback B S hS f₁ q₀ i)
    rfl rfl (chartToSpace B S hS X₁ i.1) (isEtale_chartToSpace B S hS X₁ i.1)
    (affineChartBaseMap B S hS f₁ i)
    ((Category.id_comp _).trans (representedSpaceMap_affineChartBaseMap B S hS f₁ i).symm)
    _ _ (IsPullback.of_hasPullback _ _) (affineChartPullbackFst B S hS f₁ q₀ i)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    (affineChartPullbackLift B S hS f₁ q₀ sq₁ i) (hsq i).w
    ((Category.id_comp _).trans (affineChartPullbackLift_comp_snd B S hS f₁ q₀ i sq₁)) _

/-- `isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chart` for the affine
charts `Y₁ = V₀`, `Y₁' = W₀` of `Y`, `Y'` given up to equality. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chart_of_eq
    (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' w K K' φ)
    {X₁ X₁' Y₁ Y₁' : AlgebraicSpaces B S hS} {V₀ W₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    (hY₁ : Y₁ = ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩)
    (hY₁' : Y₁' = ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩)
    (f₁ : X₁ ⟶ Y₁) (f₁' : X₁' ⟶ Y₁') (c₁ : X₁' ⟶ X₁) (g₁ : Y₁' ⟶ Y₁) (q₀ : W₀ ⟶ V₀)
    (hg₁ : eqToHom hY₁'.symm ≫ g₁ ≫ eqToHom hY₁ = representedSpaceMap B S hS q₀)
    (sq₁ : IsPullback c₁ f₁' f₁ g₁)
    (hf₁qc : IsQuasiCompact B S hS f₁.hom) (hf₁qs : IsQuasiSeparated B S hS f₁.hom)
    (ι : X₁ ⟶ X) (ιW : X₁' ⟶ X') (b : Y₁ ⟶ Y) (cW : Y₁' ⟶ Y')
    (hι : IsEtale B S hS ι.hom) (hb : IsEtale B S hS b.hom) (hcW : IsEtale B S hS cW.hom)
    (e1 : c₁ ≫ ι = ιW ≫ g') (hιf : ι ≫ f = f₁ ≫ b) (hιWf : ιW ≫ f' = f₁' ≫ cW)
    (hq₀ : g₁ ≫ b = cW ≫ g) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f₁ g₁ f₁' c₁ sq₁.w
      ((smallEtaleDerivedModulePullback B S hS ι).obj K)
      ((smallEtaleDerivedModulePullback B S hS ιW).obj K')
      ((smallEtaleDerivedModulePullbackCompIso B S hS c₁ ι).hom.app K ≫
        (smallEtaleDerivedModulePullbackCongr B S hS e1).hom.app K ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS ιW g').inv.app K ≫
        (smallEtaleDerivedModulePullback B S hS ιW).map φ)) := by
  subst hY₁ hY₁'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg₁
  subst hg₁
  exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chart B S hS
    f g f' g' w K hK K' hK' φ h2 f₁ f₁' c₁ q₀ sq₁ hf₁qc hf₁qs ι ιW b cW hι hb hcW e1 hιf hιWf hq₀

end ChartMain

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **Stacks 0DKH from condition (2) of Stacks 0DKG.** For a cartesian square of algebraic
spaces with `f` quasi-compact and quasi-separated, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'` such that the composite of Stacks 065Z is an isomorphism on every affine
étale quadruple, the composite `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` is an isomorphism. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange
    (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h2 : AffineChartwiseBaseChange B S hS f g f' g' sq.w K K' φ) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w K K' φ) :=
  isIso_smallEtaleDerivedBaseChangeComp_of_affineCharts B S hS f g f' g' sq K K' φ
    fun W V q hq hW hV => by
      have := hW
      have := hV
      exact isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange_chart_of_eq B S hS
        f g f' g' sq.w K hK K' hK' φ h2 (V₀ := V.1.left) (W₀ := W.1.left)
        (Y₁ := (SpacesEtale.toSpaces B S hS Y).obj ((comparisonFunctor B S hS Y).obj V))
        (Y₁' := (SpacesEtale.toSpaces B S hS Y').obj ((comparisonFunctor B S hS Y').obj W))
        (X₁ := chartBaseChangeSpace B S hS f V) (X₁' := chartBaseChangeSpace B S hS f' W) rfl rfl
        (chartBaseChangeProjection B S hS f V) (chartBaseChangeProjection B S hS f' W)
        (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq) (chartSpaceMapOver B S hS q) q
        ((Category.id_comp _).trans (Category.comp_id _))
        (isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq)
        (isQuasiCompact_chartBaseChangeProjection B S hS f V hfqc)
        (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
        (chartBaseChangeInclusion B S hS f V) (chartBaseChangeInclusion B S hS f' W)
        (chartToSpace B S hS Y V) (chartToSpace B S hS Y' W)
        (isEtale_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y' W)
        (chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq)
        (isPullback_chartBaseChangeInclusion B S hS f V).w
        (isPullback_chartBaseChangeInclusion B S hS f' W).w
        (chartSpaceMapOver_comp_chartToSpace B S hS g q hq)

end Main

end AlgebraicGeometry.Space
