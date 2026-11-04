module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.Iso
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrChart
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial

/-!
# The base-change morphism of relative homogeneous spectra along an identification of algebras

Let `g : S' ⟶ S` be a morphism of schemes, `A` a quasi-coherent graded algebra on `S` and `A'` one
on `S'`, identified with `g^*A` by a unital homomorphism `Ξ : g^*A ⟶ A'` invertible in every
degree.  The base-change morphism `Proj_{S'}(A') ⟶ Proj_S(A)` built by glueing charts along `Ξ` is,
through the presentation isomorphisms, the isomorphism `Proj_{S'}(A') ≅ Proj_{S'}(g^*A)` induced
by `Ξ⁻¹` followed by the base-change morphism of `A` along `g`.

## Main results

* `presentationIso_hom_relativeProjBaseChange`: through the presentation isomorphisms, the
  base-change morphism along `Ξ` is the isomorphism induced by `Ξ⁻¹` followed by the base-change
  morphism of `A`.
* `relativeProjCongr_baseChange_square`: a square of base-change morphisms and identifications of
  algebras commutes as soon as the underlying square of graded algebras does.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjPresentation Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (A' : SheafGradedAlgebra S') (g : S' ⟶ S)
  (Ξ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g (situation A).algebra) (situation A').algebra)
  (hΞ : ∀ n : ℤ, IsIso (Ξ.app n))

/-- `Proj.map` of a fourfold composite, followed by a morphism. -/
theorem proj_map_comp_four_assoc {R₀ R₁ R₂ R₃ R₄ σ₀ σ₁ σ₂ σ₃ σ₄ : Type u} [CommRing R₀]
    [SetLike σ₀ R₀] [AddSubgroupClass σ₀ R₀] [CommRing R₁] [SetLike σ₁ R₁]
    [AddSubgroupClass σ₁ R₁] [CommRing R₂] [SetLike σ₂ R₂] [AddSubgroupClass σ₂ R₂]
    [CommRing R₃] [SetLike σ₃ R₃] [AddSubgroupClass σ₃ R₃] [CommRing R₄] [SetLike σ₄ R₄]
    [AddSubgroupClass σ₄ R₄] {𝒜₀ : ℕ → σ₀} {𝒜₁ : ℕ → σ₁} {𝒜₂ : ℕ → σ₂} {𝒜₃ : ℕ → σ₃}
    {𝒜₄ : ℕ → σ₄} [GradedRing 𝒜₀] [GradedRing 𝒜₁] [GradedRing 𝒜₂] [GradedRing 𝒜₃]
    [GradedRing 𝒜₄] (f₁ : 𝒜₀ →+*ᵍ 𝒜₁) (f₂ : 𝒜₁ →+*ᵍ 𝒜₂) (f₃ : 𝒜₂ →+*ᵍ 𝒜₃)
    (f₄ : 𝒜₃ →+*ᵍ 𝒜₄)
    (h₁ : HomogeneousIdeal.irrelevant 𝒜₁ ≤ (HomogeneousIdeal.irrelevant 𝒜₀).map f₁)
    (h₂ : HomogeneousIdeal.irrelevant 𝒜₂ ≤ (HomogeneousIdeal.irrelevant 𝒜₁).map f₂)
    (h₃ : HomogeneousIdeal.irrelevant 𝒜₃ ≤ (HomogeneousIdeal.irrelevant 𝒜₂).map f₃)
    (h₄ : HomogeneousIdeal.irrelevant 𝒜₄ ≤ (HomogeneousIdeal.irrelevant 𝒜₃).map f₄)
    (h : HomogeneousIdeal.irrelevant 𝒜₄ ≤
      (HomogeneousIdeal.irrelevant 𝒜₀).map (f₄.comp (f₃.comp (f₂.comp f₁))))
    {Z : Scheme.{u}} (k : AlgebraicGeometry.Proj 𝒜₀ ⟶ Z) :
    AlgebraicGeometry.Proj.map (f₄.comp (f₃.comp (f₂.comp f₁))) h ≫ k =
      AlgebraicGeometry.Proj.map f₄ h₄ ≫ AlgebraicGeometry.Proj.map f₃ h₃ ≫
        AlgebraicGeometry.Proj.map f₂ h₂ ≫ AlgebraicGeometry.Proj.map f₁ h₁ ≫ k := by
  rw [AlgebraicGeometry.Proj.map_comp _ _ (HomogeneousIdeal.irrelevant_le_map_comp
      (HomogeneousIdeal.irrelevant_le_map_comp h₁ h₂) h₃) h₄,
    AlgebraicGeometry.Proj.map_comp _ _ (HomogeneousIdeal.irrelevant_le_map_comp h₁ h₂) h₃,
    AlgebraicGeometry.Proj.map_comp _ _ h₁ h₂]
  simp only [Category.assoc]

/-- The identification `A' ≅ g^*A` inverse to `Ξ`, as a unital homomorphism between the graded
algebras of the two `SheafGradedAlgebra`s. -/
abbrev baseChangeCongrHom :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A')
      (situationAlgebra (A.pullback g)) :=
  (unitalHomInverse Ξ hΞ).comp (pullbackHom A g)

/-- `baseChangeCongrHom` is an isomorphism in every degree. -/
instance isIso_baseChangeCongrHom_app (n : ℤ) : IsIso ((baseChangeCongrHom A A' g Ξ hΞ).app n) := by
  have := isIso_unitalHomInverse_app Ξ hΞ n
  exact inferInstanceAs (IsIso ((unitalHomInverse Ξ hΞ).app n ≫ 𝟙 _))

/-- The inverse of `baseChangeCongrHom` is `Ξ` in every degree. -/
theorem unitalHomInverse_baseChangeCongrHom_app (n : ℤ) :
    (unitalHomInverse (baseChangeCongrHom A A' g Ξ hΞ) (fun n => inferInstance)).app n =
      Ξ.app n := by
  have := hΞ n
  refine IsIso.inv_eq_of_hom_inv_id ?_
  show (inv (Ξ.app n) ≫ 𝟙 _) ≫ Ξ.app n = 𝟙 _
  rw [Category.comp_id, IsIso.inv_hom_id]

/-- The graded ring maps of sections of the two descriptions of the base change agree. -/
theorem gradedBaseChange_eq_comp (U : S.AffineZariskiSite) (U' : S'.AffineZariskiSite)
    (h : U'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    Stacks.RelativeProj.Situation.gradedBaseChange (s := situation A) (s' := situation A') g Ξ
        U.toOpens U'.toOpens h =
      (chartHom A' U').comp ((congrSectionHom (baseChangeCongrHom A A' g Ξ hΞ)
        (fun n => inferInstance) U'.toOpens).comp
          ((sectionBaseChange A g U U' h).comp (chartInv A U))) := by
  refine GradedRingHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n a =>
    have e1 := Stacks.RelativeProj.Situation.sectionRingBaseChange_of (s := situation A)
      (s' := situation A') g Ξ U.toOpens U'.toOpens h n a
    have e2 := situationSectionRingEquiv_symm_of (algebra A) (isCommutative A)
      (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens n a
    have e3 := sectionBaseChange_of A g U U' h n a
    have e4 := SheafGradedAlgebraHom.sectionHom_of (SheafGradedAlgebraHom.ofSituationHom
      (unitalHomInverse (baseChangeCongrHom A A' g Ξ hΞ) (fun n => inferInstance))) U'.toOpens
      (Scheme.Modules.pullbackSection g (A.piece (n : ℤ)) U.toOpens U'.toOpens h a)
    have e5 := situationSectionRingEquiv_of (algebra A') (isCommutative A')
      (vanishesInNegativeDegrees A') A'.isQuasicoherent U'.toOpens n
      (((unitalHomInverse (baseChangeCongrHom A A' g Ξ hΞ) (fun n => inferInstance)).app
        (n : ℤ)).val.app (op U'.toOpens)
          (Scheme.Modules.pullbackSection g (A.piece (n : ℤ)) U.toOpens U'.toOpens h a))
    refine e1.trans (Eq.trans ?_ ((congrArg (chartHom A' U') ((congrArg
      (congrSectionHom (baseChangeCongrHom A A' g Ξ hΞ) (fun n => inferInstance) U'.toOpens)
      ((congrArg (sectionBaseChange A g U U' h) e2).trans e3)).trans e4)).trans e5).symm)
    refine congrArg (DirectSum.of _ n) ?_
    exact congrArg (fun f => f.val.app (op U'.toOpens)
      (Scheme.Modules.pullbackSection g (A.piece (n : ℤ)) U.toOpens U'.toOpens h a))
      (unitalHomInverse_baseChangeCongrHom_app A A' g Ξ hΞ n).symm

/-- **The base-change morphism along `Ξ`, through the presentation isomorphisms**, is the
isomorphism induced by `Ξ⁻¹` followed by the base-change morphism of `A`. -/
theorem presentationIso_hom_relativeProjBaseChange :
    (presentationIso A').hom ≫ Stacks.RelativeProj.Situation.relativeProjBaseChange
        (s := situation A) (s' := situation A') g Ξ (fun m => hΞ m) =
      (relativeProjCongr (baseChangeCongrHom A A' g Ξ hΞ) (fun n => inferInstance)).hom ≫
        baseChangeHom A g ≫ (presentationIso A).hom := by
  refine (Iso.eq_inv_comp _).1 ?_
  refine (Stacks.RelativeProj.Situation.baseChangeCover (s := situation A) (s' := situation A')
    g).hom_ext _ _ fun p => ?_
  obtain ⟨⟨W', W⟩, h⟩ := p
  let U : S.AffineZariskiSite := ⟨W.1, W.2⟩
  let U' : S'.AffineZariskiSite := ⟨W'.1, W'.2⟩
  have c0 := Stacks.RelativeProj.Situation.relativeProjChart_comp_relativeProjBaseChange
    (s := situation A) (s' := situation A') g Ξ (fun m => hΞ m) ⟨(W', W), h⟩
  have c1 := relativeProjChart_presentationIso_inv A' U'
  have c2 := chart_comp_relativeProjCongr_hom (baseChangeCongrHom A A' g Ξ hΞ)
    (fun n => inferInstance) U'.toOpens (isAffineOpen_toOpens U')
  have c3 := chart_baseChangeHom A g U U' h
  have c4 := chart_presentationIso_hom A U
  have key := (Category.assoc _ _ _).symm.trans ((c1 =≫ _).trans ((Category.assoc _ _ _).trans
    (whisker_eq _ ((Category.assoc _ _ _).symm.trans ((c2 =≫ _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).symm.trans
        ((c3 =≫ _).trans ((Category.assoc _ _ _).trans (whisker_eq _ c4)))))))))))
  refine c0.trans (Eq.trans ?_ key.symm)
  have hirr := Stacks.RelativeProj.Situation.irrelevant_le_gradedBaseChange (s := situation A)
      (s' := situation A') g Ξ W W' h (fun m => hΞ m)
  rw [gradedBaseChange_eq_comp A A' g Ξ hΞ U U' h] at hirr
  refine (congrArg (fun z => z ≫ Stacks.RelativeProj.Situation.relativeProjChart (situation A)
    (siteAffineOpen U)) (AlgebraicGeometry.Proj.map_congr
      (gradedBaseChange_eq_comp A A' g Ξ hΞ U U' h) _ hirr)).trans ?_
  exact proj_map_comp_four_assoc _ _ _ _ _ _ _ _ _ _

/-- The isomorphism induced by a degreewise isomorphism depends only on the homomorphism. -/
theorem relativeProjCongr_hom_congr {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
    {Φ₁ Φ₂ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂)}
    (e : Φ₁ = Φ₂) (h₁ : ∀ n : ℤ, IsIso (Φ₁.app n)) (h₂ : ∀ n : ℤ, IsIso (Φ₂.app n)) :
    (relativeProjCongr Φ₁ h₁).hom = (relativeProjCongr Φ₂ h₂).hom := by
  subst e
  rfl

/-- **A square of base-change morphisms and identifications of algebras commutes** as soon as the
underlying square of graded algebras commutes: for identifications `ρ : B' ≅ g^*B`,
`Ψ : B ≅ A`, `Ψ' : B' ≅ A'` and `Ξ : g^*A ≅ A'`, if `ρ` followed by `g^*Ψ` is `Ψ'` followed by
`Ξ⁻¹`, then the base-change morphism of `B` read through `Ψ` and `ρ` is the one along `Ξ` read
through `Ψ'`. -/
theorem relativeProjCongr_baseChange_square {B₀ : SheafGradedAlgebra S}
    {B₀' : SheafGradedAlgebra S'}
    (ρ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra B₀')
      (situationAlgebra (B₀.pullback g))) (hρ : ∀ n : ℤ, IsIso (ρ.app n))
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra B₀) (situationAlgebra A))
    (hΨ : ∀ n : ℤ, IsIso (Ψ.app n))
    (Ψ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra B₀') (situationAlgebra A'))
    (hΨ' : ∀ n : ℤ, IsIso (Ψ'.app n))
    (hsq : ρ.comp (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom g Ψ) =
      Ψ'.comp (baseChangeCongrHom A A' g Ξ hΞ)) :
    (relativeProjCongr ρ hρ).hom ≫ baseChangeHom B₀ g ≫ (relativeProjCongr Ψ hΨ).hom ≫
        (presentationIso A).hom =
      (relativeProjCongr Ψ' hΨ').hom ≫ (presentationIso A').hom ≫
        Stacks.RelativeProj.Situation.relativeProjBaseChange
          (s := situation A) (s' := situation A') g Ξ (fun m => hΞ m) := by
  have hgΨ : ∀ n : ℤ,
      IsIso ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom g Ψ).app n) :=
    fun n => by
      have := hΨ n
      exact Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isIso_baseAlgebraMapHom_app g Ψ n
  have h₁ : ∀ n : ℤ, IsIso ((ρ.comp
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom g Ψ)).app n) :=
    fun n => @IsIso.comp_isIso _ _ _ _ _ _ _ (hρ n) (hgΨ n)
  have h₂ : ∀ n : ℤ, IsIso ((Ψ'.comp (baseChangeCongrHom A A' g Ξ hΞ)).app n) :=
    fun n => by
      have := hΨ' n
      infer_instance
  have e1 := baseChangeHom_comp_relativeProjCongr_hom g Ψ hΨ
  have e2 := relativeProjCongr_comp_hom (A₃ := A.pullback g) ρ hρ
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom g Ψ) hgΨ h₁
  have e3 := relativeProjCongr_comp_hom Ψ' hΨ' (baseChangeCongrHom A A' g Ξ hΞ)
    (fun n => inferInstance) h₂
  have e4 := relativeProjCongr_hom_congr hsq h₁ h₂
  have e5 := presentationIso_hom_relativeProjBaseChange A A' g Ξ hΞ
  refine (whisker_eq _ (((Category.assoc _ _ _).symm.trans (e1 =≫ _)).trans
    (Category.assoc _ _ _))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans ((e2.symm.trans (e4.trans e3)) =≫ _)).trans ?_
  exact (Category.assoc _ _ _).trans (whisker_eq _ e5.symm)

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
