module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit

/-!
# Naturality of `RG' ⋙ r_M ≅ r_A ⋙ RG` in endomorphisms of the exact functors

Let `r_A : 𝒜' ⥤ 𝒜`, `r_M : ℳ' ⥤ ℳ` be exact functors with `e : G' ⋙ r_M ≅ r_A ⋙ G`, and let
`CategoryTheory.Functor.rightDerivedRestrictionIso` be the induced comparison
`RG' ⋙ r_M ≅ r_A ⋙ RG`.  Given natural endomorphisms `θ_A` of `r_A` and `θ_M` of `r_M`
compatible with `e` (that is, `G'(θ_M) ∘ e = e ∘ G(θ_A)` as transformations
`G' ⋙ r_M ⟶ r_A ⋙ G`), the comparison intertwines the degreewise actions of `θ_M` and `θ_A` on
derived categories.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryPlusNatTrans_app_Qh_comp_factorsh`: the degreewise
  action of a transformation on `D⁺`, read through the factorizations through `K⁺`.
* `CategoryTheory.Functor.rightDerivedRestrictionIso_hom_naturality`: the comparison
  `RG' ⋙ r_M ≅ r_A ⋙ RG` intertwines the degreewise actions of compatible endomorphisms `θ_M` and
  `θ_A`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Factorsh

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] {T S : A ⥤ B} [T.Additive] [S.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- **The degreewise action of `τ : T ⟶ S` on `D⁺`, read through the factorizations of the two
actions through `K⁺`**: it is `τ` applied degreewise. -/
theorem mapDerivedCategoryPlusNatTrans_app_Qh_comp_factorsh (τ : T ⟶ S)
    (M : HomotopyCategory.Plus A) :
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans τ).app
        (DerivedCategory.Plus.Qh.obj M) ≫ S.mapDerivedCategoryPlusFactorsh.hom.app M =
      T.mapDerivedCategoryPlusFactorsh.hom.app M ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans τ).app M) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  exact Stacks.DerivedFunctor.mapDerivedNatTrans_factorsh_app τ M.obj

/-- `mapDerivedCategoryPlusNatTrans_app_Qh_comp_factorsh` solved for the inverse
factorizations. -/
theorem Qh_map_comp_mapDerivedCategoryPlusFactorsh_inv_app (τ : T ⟶ S)
    (M : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans τ).app M) ≫
        S.mapDerivedCategoryPlusFactorsh.inv.app M =
      T.mapDerivedCategoryPlusFactorsh.inv.app M ≫
        (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans τ).app
          (DerivedCategory.Plus.Qh.obj M) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  exact Stacks.DerivedFunctor.Qh_map_comp_mapDerivedCategoryFactorsh_inv_app τ M.obj

/-- **The degreewise action of `τ : T ⟶ S` on `D⁺`, read through `Q ⋙ T⁺ ≅ T ⋙ Q`**: on the
image of a bounded below complex `N` it is the image of `τ` applied degreewise to `N`. -/
theorem mapDerivedCategoryPlusNatTrans_app_Q_comp_mapDerivedCategoryPlusQIso (τ : T ⟶ S)
    (N : CochainComplex.Plus A) :
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans τ).app
        (DerivedCategory.Plus.Q.obj N) ≫ (mapDerivedCategoryPlusQIso S).hom.app N =
      (mapDerivedCategoryPlusQIso T).hom.app N ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk (X := T.mapCochainComplexPlus.obj N)
          (Y := S.mapCochainComplexPlus.obj N)
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app N.obj)) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusQIso_hom_app]
  exact Stacks.DerivedFunctor.mapDerivedNatTrans_factors_app τ N.obj

end Factorsh

/-- A chase through three commutative squares, the last one under a functor. -/
private theorem comp_eq_of_squares_map_square {C D : Type*} [Category* C] [Category* D] (R : C ⥤ D)
    {X₀ X₁ X₂ : D} {Y₀ Y₁ : C} (a : X₀ ⟶ X₁) (p : X₁ ⟶ X₁) (b : X₁ ⟶ X₂) (q : X₂ ⟶ X₂)
    (u : X₂ ⟶ R.obj Y₀) (w : Y₀ ⟶ Y₀) (f : Y₀ ⟶ Y₁) (θ : Y₁ ⟶ Y₁) (h₁ : p ≫ b = b ≫ q)
    (h₂ : q ≫ u = u ≫ R.map w) (h₃ : w ≫ f = f ≫ θ) :
    a ≫ p ≫ b ≫ u ≫ R.map f = a ≫ b ≫ u ≫ R.map f ≫ R.map θ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, ← R.map_comp, h₃, R.map_comp]

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M'] [HasDerivedCategory M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]

/-- **The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` is natural in compatible endomorphisms of `r_A`
and `r_M`.** If `θ_A : r_A ⟶ r_A` and `θ_M : r_M ⟶ r_M` satisfy
`G'(θ_M) ≫ e = e ≫ G(θ_A)`, then the comparison carries the degreewise action of `θ_M` on
`r_M(RG'(K))` to `RG` of the degreewise action of `θ_A` on `r_A(K)`. -/
theorem rightDerivedRestrictionIso_hom_naturality (e : G' ⋙ rM ≅ rA ⋙ G)
    (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) (θA : rA ⟶ rA) (θM : rM ⟶ rM)
    (hθ : Functor.whiskerLeft G' θM ≫ e.hom = e.hom ≫ Functor.whiskerRight θA G)
    (K : DerivedCategory.Plus A') :
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θM).app
        (G'.rightDerivedFunctorPlus.obj K) ≫
        (rightDerivedRestrictionIso G' G rA rM e hac).hom.app K =
      (rightDerivedRestrictionIso G' G rA rM e hac).hom.app K ≫
        G.rightDerivedFunctorPlus.map
          ((Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θA).app K) := by
  let γ₁ : G'.rightDerivedFunctorPlus ⋙ rM.mapDerivedCategoryPlus ⟶
      rA.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
    Functor.whiskerLeft G'.rightDerivedFunctorPlus
        (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θM) ≫
      (rightDerivedRestrictionIso G' G rA rM e hac).hom
  let γ₂ : G'.rightDerivedFunctorPlus ⋙ rM.mapDerivedCategoryPlus ⟶
      rA.mapDerivedCategoryPlus ⋙ G.rightDerivedFunctorPlus :=
    (rightDerivedRestrictionIso G' G rA rM e hac).hom ≫
      Functor.whiskerRight (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θA)
        G.rightDerivedFunctorPlus
  suffices h : γ₁ = γ₂ from congrArg (fun γ => NatTrans.app γ K) h
  refine Functor.rightDerived_ext (G'.rightDerivedFunctorPlus ⋙ rM.mapDerivedCategoryPlus)
    (Functor.whiskerRight G'.rightDerivedFunctorPlusUnit rM.mapDerivedCategoryPlus)
    (HomotopyCategory.Plus.quasiIso A') _ γ₁ γ₂ ?_
  refine NatTrans.ext (funext fun L => ?_)
  have hsq : (mapHomotopyCategoryPlusNatTrans θM).app (G'.mapHomotopyCategoryPlus.obj L) ≫
      (mapHomotopyCategoryPlusNatIso e).hom.app L =
      (mapHomotopyCategoryPlusNatIso e).hom.app L ≫
        G.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatTrans θA).app L) := by
    have h2 := congrArg (fun t => (mapHomotopyCategoryPlusNatTrans t).app L) hθ
    simp only [mapHomotopyCategoryPlusNatTrans_comp_app] at h2
    rw [Stacks.LerayPullbackComparison.mapHomotopyCategoryPlusNatIso_hom_app]
    exact h2
  have hU := map_unit_comp_rightDerivedRestrictionIso_hom_app G' G rA rM e hac L
  have hθM := (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θM).naturality
    (G'.rightDerivedFunctorPlusUnit.app L)
  have hfM := mapDerivedCategoryPlusNatTrans_app_Qh_comp_factorsh θM
    (G'.mapHomotopyCategoryPlus.obj L)
  have hfA := Qh_map_comp_mapDerivedCategoryPlusFactorsh_inv_app θA L
  have hu : DerivedCategory.Plus.Qh.map
      (G.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatTrans θA).app L)) ≫
        G.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj L) =
      G.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj L) ≫
        G.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans θA).app L)) :=
    G.rightDerivedFunctorPlusUnit.naturality ((mapHomotopyCategoryPlusNatTrans θA).app L)
  have hc₂ : (mapHomotopyCategoryPlusCompIso (Iso.refl (rA ⋙ G))).inv.app L = 𝟙 _ := by
    apply (HomotopyCategory.Plus.ι M).map_injective
    rfl
  dsimp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map]
  have hx : (mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app L ≫
      (mapHomotopyCategoryPlusNatIso e).hom.app L ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (rA ⋙ G))).inv.app L =
      (mapHomotopyCategoryPlusNatIso e).hom.app L := by
    rw [mapHomotopyCategoryPlusCompIso_refl_hom_app, hc₂]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [hx] at hU
  have h3 : DerivedCategory.Plus.Qh.map
      ((mapHomotopyCategoryPlusNatTrans θM).app (G'.mapHomotopyCategoryPlus.obj L)) ≫
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app L) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatIso e).hom.app L) ≫
        DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatTrans θA).app L)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg _ hsq).trans (Functor.map_comp _ _ _))
  rw [reassoc_of% hθM, hU, reassoc_of% hfM, reassoc_of% hU]
  exact comp_eq_of_squares_map_square G.rightDerivedFunctorPlus _ _ _ _ _ _ _ _ h3 hu hfA

end CategoryTheory.Functor

end
