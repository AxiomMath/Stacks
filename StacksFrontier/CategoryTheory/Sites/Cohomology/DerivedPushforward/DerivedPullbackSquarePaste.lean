module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom

/-!
# Pasting the derived squares of 2-commutative squares of ringed topoi

A 2-commutative square of morphisms of ringed topoi, `τ : f ∘ c ≅ c' ∘ x` (Stacks 04IC), gives
the isomorphism of derived pullbacks `Lf^* ⋙ Lc^* ≅ L(f ∘ c)^* ≅ L(c' ∘ x)^* ≅ Lc'^* ⋙ Lx^*`
through the composition isomorphisms of Stacks 0D6D. This file proves that these derived squares
paste: for two squares stacked along a common edge, and a third square whose 2-isomorphism is
their pasting conjugated by 2-isomorphisms `f₂ ∘ f₁ ≅ f₁₂` and `x₂ ∘ x₁ ≅ x₁₂` of its sides, the
derived square of the third is the pasting of the derived squares of the first two, read through
the derived pullback isomorphisms of the side 2-isomorphisms.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackSquare_pasteHorizontal_hom_app`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe vA uA wA vC uC wC

-- no global `HasDerivedCategory` instance on sheaves of modules over a ringed topos
attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

noncomputable section

variable {A₁ A₂ A₃ : RingedTopos.{vA, uA, wA}} {C₁ C₂ C₃ : RingedTopos.{vC, uC, wC}}
  [A₁.J.HasSheafCompose (forget RingCat.{wA})]
  [A₁.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [A₁.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [HasSheafify A₁.J AddCommGrpCat.{wA}] [A₁.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasSheafify A₁.J (Type wA)]
  [A₂.J.HasSheafCompose (forget RingCat.{wA})]
  [A₂.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [A₂.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [HasSheafify A₂.J AddCommGrpCat.{wA}] [A₂.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasSheafify A₂.J (Type wA)]
  [A₃.J.HasSheafCompose (forget RingCat.{wA})]
  [A₃.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
  [A₃.J.HasSheafCompose (forget AddCommGrpCat.{wA})]
  [HasSheafify A₃.J AddCommGrpCat.{wA}] [A₃.J.WEqualsLocallyBijective AddCommGrpCat.{wA}]
  [HasSheafify A₃.J (Type wA)]
  [C₁.J.HasSheafCompose (forget RingCat.{wC})]
  [C₁.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C₁.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [HasSheafify C₁.J AddCommGrpCat.{wC}] [C₁.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C₁.J (Type wC)]
  [C₂.J.HasSheafCompose (forget RingCat.{wC})]
  [C₂.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C₂.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [HasSheafify C₂.J AddCommGrpCat.{wC}] [C₂.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C₂.J (Type wC)]
  [C₃.J.HasSheafCompose (forget RingCat.{wC})]
  [C₃.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [C₃.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [HasSheafify C₃.J AddCommGrpCat.{wC}] [C₃.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify C₃.J (Type wC)]
  (c₁ : RingedToposHom A₁ C₁) (c₂ : RingedToposHom A₂ C₂) (c₃ : RingedToposHom A₃ C₃)
  (f₁ : RingedToposHom C₁ C₂) (f₂ : RingedToposHom C₂ C₃) (f₁₂ : RingedToposHom C₁ C₃)
  (x₁ : RingedToposHom A₁ A₂) (x₂ : RingedToposHom A₂ A₃) (x₁₂ : RingedToposHom A₁ A₃)

/-- **The derived squares of 2-commutative squares of ringed topoi paste.** For squares
`τ₁ : f₁ ∘ c₁ ≅ c₂ ∘ x₁` and `τ₂ : f₂ ∘ c₂ ≅ c₃ ∘ x₂` and a square `τ₁₂ : f₁₂ ∘ c₁ ≅ c₃ ∘ x₁₂`
which is the horizontal pasting of `τ₂` and `τ₁` conjugated by `σC : f₂ ∘ f₁ ≅ f₁₂` and
`σX : x₂ ∘ x₁ ≅ x₁₂`, the derived square of `τ₁₂`, precomposed with the composition comparison
`Lf₂^* ⋙ Lf₁^* ⟶ L(f₂ ∘ f₁)^* ≅ Lf₁₂^*`, is the derived square of `τ₁` followed by that of `τ₂`
and by the composition isomorphism `Lx₂^* ⋙ Lx₁^* ≅ L(x₂ ∘ x₁)^* ≅ Lx₁₂^*`. -/
theorem derivedPullbackSquare_pasteHorizontal_hom_app
    (τ₁ : RingedToposHom.TwoIso (f₁.comp c₁) (c₂.comp x₁))
    (τ₂ : RingedToposHom.TwoIso (f₂.comp c₂) (c₃.comp x₂))
    (τ₁₂ : RingedToposHom.TwoIso (f₁₂.comp c₁) (c₃.comp x₁₂))
    (σC : RingedToposHom.TwoIso (f₂.comp f₁) f₁₂) (σX : RingedToposHom.TwoIso (x₂.comp x₁) x₁₂)
    (hτ : τ₁₂ = (σC.symm.whiskerLeft c₁).trans
      ((RingedToposHom.TwoIso.pasteHorizontal τ₂ τ₁).trans (σX.whiskerRight c₃)))
    (K : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₃.O))) :
    (derivedPullback c₁).map ((derivedPullbackCompComparison f₁ f₂).app K ≫
        (derivedPullbackIsoOfTwoIso σC).hom.app K) ≫
      (derivedPullbackCompIso c₁ f₁₂ ≪≫ derivedPullbackIsoOfTwoIso τ₁₂ ≪≫
        (derivedPullbackCompIso x₁₂ c₃).symm).hom.app K =
    (derivedPullbackCompIso c₁ f₁ ≪≫ derivedPullbackIsoOfTwoIso τ₁ ≪≫
        (derivedPullbackCompIso x₁ c₂).symm).hom.app ((derivedPullback f₂).obj K) ≫
      (derivedPullback x₁).map ((derivedPullbackCompIso c₂ f₂ ≪≫ derivedPullbackIsoOfTwoIso τ₂ ≪≫
        (derivedPullbackCompIso x₂ c₃).symm).hom.app K) ≫
      (derivedPullbackCompComparison x₁ x₂).app ((derivedPullback c₃).obj K) ≫
      (derivedPullbackIsoOfTwoIso σX).hom.app ((derivedPullback c₃).obj K) := by
  subst hτ
  have h₂ : (derivedPullback c₁).map ((derivedPullbackCompComparison f₁ f₂).app K) ≫
      (derivedPullbackCompComparison c₁ (f₂.comp f₁)).app K ≫
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator c₁ f₁ f₂)).inv.app K =
      (derivedPullbackCompComparison c₁ f₁).app ((derivedPullback f₂).obj K) ≫
        (derivedPullbackCompComparison (f₁.comp c₁) f₂).app K := by
    rw [← Category.assoc, ← derivedPullbackCompComparison_assoc_associator c₁ f₁ f₂ K]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have h₄ : (derivedPullbackCompComparison (c₂.comp x₁) f₂).app K ≫
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator x₁ c₂ f₂)).hom.app K =
      (derivedPullbackCompIso x₁ c₂).inv.app ((derivedPullback f₂).obj K) ≫
        (derivedPullback x₁).map ((derivedPullbackCompComparison c₂ f₂).app K) ≫
        (derivedPullbackCompComparison x₁ (f₂.comp c₂)).app K := by
    rw [← derivedPullbackCompComparison_assoc_associator x₁ c₂ f₂ K,
      ← derivedPullbackCompIso_hom x₁ c₂, Iso.inv_hom_id_app_assoc]
  have h₆ : (derivedPullbackCompComparison x₁ (c₃.comp x₂)).app K ≫
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator x₁ x₂ c₃)).inv.app K =
      (derivedPullback x₁).map ((derivedPullbackCompIso x₂ c₃).inv.app K) ≫
        (derivedPullbackCompComparison x₁ x₂).app ((derivedPullback c₃).obj K) ≫
        (derivedPullbackCompComparison (x₂.comp x₁) c₃).app K := by
    rw [← cancel_epi ((derivedPullback x₁).map ((derivedPullbackCompIso x₂ c₃).hom.app K)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, derivedPullbackCompIso_hom,
      ← reassoc_of% (derivedPullbackCompComparison_assoc_associator x₁ x₂ c₃ K),
      Iso.hom_inv_id_app, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, derivedPullbackCompIso_hom,
    derivedPullbackIsoOfTwoIso_trans, RingedToposHom.TwoIso.pasteHorizontal,
    derivedPullbackIsoOfTwoIso_symm, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (derivedPullbackCompComparison_whiskerLeft c₁ σC.symm K),
    derivedPullbackIsoOfTwoIso_symm, Iso.symm_hom,
    ← Functor.map_comp_assoc (derivedPullback c₁) ((derivedPullbackIsoOfTwoIso σC).hom.app K),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₂,
    reassoc_of% (derivedPullbackCompComparison_whiskerRight τ₁ f₂ K), reassoc_of% h₄,
    reassoc_of% (derivedPullbackCompComparison_whiskerLeft x₁ τ₂ K), reassoc_of% h₆,
    reassoc_of% (derivedPullbackCompComparison_whiskerRight σX c₃ K),
    ← derivedPullbackCompIso_hom x₁₂ c₃, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

omit [HasSheafify A₁.J (Type wA)] [HasSheafify A₂.J (Type wA)] [HasSheafify A₃.J (Type wA)]
  [HasSheafify C₁.J (Type wC)] [HasSheafify C₂.J (Type wC)] [HasSheafify C₃.J (Type wC)]
  [HasSheafify A₂.J AddCommGrpCat.{wA}] [A₂.J.WEqualsLocallyBijective AddCommGrpCat.{wA}] in
/-- A 2-isomorphism `σ` and its inverse have inverse pullback isomorphisms. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso_symm
    {f g : RingedToposHom A₁ A₂} (σ : RingedToposHom.TwoIso f g) :
    σ.symm.pullbackModulesIso = σ.pullbackModulesIso.symm := by
  have h := RingedToposHom.TwoIso.pullbackModulesIso_trans σ σ.symm
  rw [RingedToposHom.TwoIso.trans_symm_self, RingedToposHom.TwoIso.pullbackModulesIso_refl] at h
  refine Iso.ext ?_
  rw [Iso.symm_hom, ← cancel_epi σ.pullbackModulesIso.hom, Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm

/-- **The pasting law of `derivedPullbackSquare_pasteHorizontal_hom_app`, for derived squares
read through given models of the derived pullbacks of the transitions.** Here `F₁`, `F₂`, `F₁₂`
are functors identified with `Lf₁^*`, `Lf₂^*`, `Lf₁₂^*` by `ι₁`, `ι₂`, `ι₁₂`, the comparison
`Γ : F₂ ⋙ F₁ ⟶ F₁₂` is the composition comparison read through them, and the composite
`x₂ ∘ x₁` is compared with `x₁₂` through a 2-isomorphism `σX : x₁₂' ≅ x₂ ∘ x₁` and an equality
`x₁₂' = x₁₂`. -/
theorem derivedPullbackSquare_paste_hom_app
    {F₁ : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₂.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₁.O))}
    {F₂ : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₃.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₂.O))}
    {F₁₂ : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₃.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₁.O))}
    (ι₁ : F₁ ≅ derivedPullback f₁) (ι₂ : F₂ ≅ derivedPullback f₂)
    (ι₁₂ : F₁₂ ≅ derivedPullback f₁₂) (Γ : F₂ ⋙ F₁ ⟶ F₁₂)
    (τ₁ : RingedToposHom.TwoIso (f₁.comp c₁) (c₂.comp x₁))
    (τ₂ : RingedToposHom.TwoIso (f₂.comp c₂) (c₃.comp x₂))
    (τ₁₂ : RingedToposHom.TwoIso (f₁₂.comp c₁) (c₃.comp x₁₂))
    (σC : RingedToposHom.TwoIso (f₂.comp f₁) f₁₂) {x₁₂' : RingedToposHom A₁ A₃}
    (σX : RingedToposHom.TwoIso x₁₂' (x₂.comp x₁)) (hx : x₁₂' = x₁₂)
    (hΓ : ∀ K, Γ.app K ≫ ι₁₂.hom.app K = ι₁.hom.app (F₂.obj K) ≫
      (derivedPullback f₁).map (ι₂.hom.app K) ≫ (derivedPullbackCompComparison f₁ f₂).app K ≫
        (derivedPullbackIsoOfTwoIso σC).hom.app K)
    (hτ : τ₁₂ = (σC.symm.whiskerLeft c₁).trans
      ((RingedToposHom.TwoIso.pasteHorizontal τ₂ τ₁).trans
        ((σX.symm.trans (RingedToposHom.TwoIso.ofEq hx)).whiskerRight c₃)))
    (K : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf C₃.O))) :
    (derivedPullback c₁).map (Γ.app K) ≫
      (Functor.isoWhiskerRight ι₁₂ (derivedPullback c₁) ≪≫ derivedPullbackCompIso c₁ f₁₂ ≪≫
        derivedPullbackIsoOfPullbackModulesIso τ₁₂.pullbackModulesIso ≪≫
        (derivedPullbackCompIso x₁₂ c₃).symm).hom.app K =
    (Functor.isoWhiskerRight ι₁ (derivedPullback c₁) ≪≫ derivedPullbackCompIso c₁ f₁ ≪≫
        derivedPullbackIsoOfPullbackModulesIso τ₁.pullbackModulesIso ≪≫
        (derivedPullbackCompIso x₁ c₂).symm).hom.app (F₂.obj K) ≫
      (derivedPullback x₁).map ((Functor.isoWhiskerRight ι₂ (derivedPullback c₂) ≪≫
        derivedPullbackCompIso c₂ f₂ ≪≫
        derivedPullbackIsoOfPullbackModulesIso τ₂.pullbackModulesIso ≪≫
        (derivedPullbackCompIso x₂ c₃).symm).hom.app K) ≫
      (derivedPullbackCompIso x₁ x₂ ≪≫
        derivedPullbackIsoOfPullbackModulesIso σX.pullbackModulesIso.symm).hom.app
          ((derivedPullback c₃).obj K) ≫
      (derivedPullbackCongr hx).hom.app ((derivedPullback c₃).obj K) := by
  subst hx
  have key := derivedPullbackSquare_pasteHorizontal_hom_app c₁ c₂ c₃ f₁ f₂ f₁₂ x₁ x₂ x₁₂' τ₁ τ₂
    τ₁₂ σC σX.symm (by rw [hτ, RingedToposHom.TwoIso.ofEq_rfl]; rfl) K
  have hσ : derivedPullbackIsoOfPullbackModulesIso σX.pullbackModulesIso.symm =
      derivedPullbackIsoOfTwoIso σX.symm := by
    rw [← RingedToposHom.TwoIso.pullbackModulesIso_symm]
    rfl
  have hcongr : (derivedPullbackCongr (rfl : x₁₂' = x₁₂')).hom.app ((derivedPullback c₃).obj K) =
      𝟙 _ := rfl
  have hN := (derivedPullbackCompIso c₁ f₁ ≪≫
    derivedPullbackIsoOfPullbackModulesIso τ₁.pullbackModulesIso ≪≫
    (derivedPullbackCompIso x₁ c₂).symm).hom.naturality (ι₂.hom.app K)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc, hσ, hcongr,
    Category.comp_id] at key hN ⊢
  unfold derivedPullbackIsoOfTwoIso at key
  rw [← Functor.map_comp_assoc (derivedPullback c₁) (Γ.app K), hΓ K]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← reassoc_of% hN]
  congr 1

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
