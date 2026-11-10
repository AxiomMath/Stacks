module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# Descending a transformation out of an exact functor along a change of source category

Let `F` be an exact functor out of an abelian category `A₁` and let `Γ` be an additive functor
into the target of `F` with a right derived functor `RΓ` and unit `η`. A natural transformation
`F ⟶ R ⋙ Γ`, for an exact `R`, extends to the unbounded derived categories as
`Stacks.DerivedFunctor.exactDerivedDesc`, the unique transformation
`F.mapDerivedCategory ⟶ R.mapDerivedCategory ⋙ RΓ` factoring the degreewise comparison through
`η`.

A transformation `F.mapDerivedCategory ⟶ R.mapDerivedCategory ⋙ RΓ` can also be assembled from a
transformation attached to a *different* pair of functors, together with the comparisons
`CategoryTheory.Functor.mapDerivedCategoryCompIso` of the degreewise actions of a composite with
the composite of the degreewise actions. This file proves that the two constructions agree, in the
following two shapes:

* a transformation `F' ⟶ Q' ⋙ Γ` out of a second exact functor `F'` on a second category `A₂`,
  carried to `F` by an isomorphism `P ⋙ F' ≅ F` and to `R` by an isomorphism `P ⋙ Q' ≅ R`, for an
  exact `P : A₁ ⥤ A₂` — this is
  `Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc`;
* a transformation `F ⟶ Q ⋙ Γ'` into a *different* additive functor `Γ'`, followed by a
  transformation `Γ' ⟶ I ⋙ Γ` and an isomorphism `Q ⋙ I ≅ R` — this is
  `Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc`.

## Main results

* `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_trans` — the degreewise action on homotopy
  categories of a transformation assembled in two steps, with a composition comparison at the
  end, is the composite of the two degreewise actions.
* `Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc` and
  `Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc` — the two shapes above are
  descents of the corresponding transformation on the abelian categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Degreewise actions on homotopy categories -/

section HomotopyCategory

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]

/-- The inverse of the comparison of homotopy categories attached to an isomorphism
`e : F ⋙ G ≅ H` is the degreewise action of the transformation `e.inv : H ⟶ F ⋙ G`. -/
public theorem mapHomotopyCategoryCompIso_inv_app (F : A₁ ⥤ A₂) [F.Additive] (G : A₂ ⥤ A₄)
    [G.Additive] (H : A₁ ⥤ A₄) [H.Additive] (e : F ⋙ G ≅ H)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app J =
      (mapHomotopyCategoryOfComp H F G e.inv).app J :=
  (mapHomotopyCategoryOfComp_app H F G e.inv J).symm

/-- **The degreewise action of a transformation assembled in two steps.** For `σ : F ⟶ G ⋙ F'`,
`τ : F' ⟶ Q ⋙ Γ` and an isomorphism `e : G ⋙ Q ≅ R`, the degreewise action on homotopy
categories of the composite `F ⟶ R ⋙ Γ` is the action of `σ`, followed by the action of `τ` after
`G`, followed by `Γ` applied to the comparison of homotopy categories attached to `e`. -/
public theorem mapHomotopyCategoryOfComp_trans (F : A₁ ⥤ A₄) [F.Additive] (G : A₁ ⥤ A₂)
    [G.Additive] (F' : A₂ ⥤ A₄) [F'.Additive] (Q : A₂ ⥤ A₃) [Q.Additive] (Γ : A₃ ⥤ A₄)
    [Γ.Additive] (R : A₁ ⥤ A₃) [R.Additive] (σ : F ⟶ G ⋙ F') (τ : F' ⟶ Q ⋙ Γ) (e : G ⋙ Q ≅ R)
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp F G F' σ).app J ≫
        (mapHomotopyCategoryOfComp F' Q Γ τ).app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) =
      (mapHomotopyCategoryOfComp F R Γ (σ ≫ Functor.whiskerLeft G τ ≫
        (Functor.associator G Q Γ).inv ≫ Functor.whiskerRight e.hom Γ)).app J := by
  rw [mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app,
    mapHomotopyCategoryOfComp_app]
  have he : (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) =
      (HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map
        ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app J.as)) := rfl
  rw [he]
  have key : (NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app J.as ≫
        (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj J).as ≫
          (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app J.as) =
      (NatTrans.mapHomologicalComplex (σ ≫ Functor.whiskerLeft G τ ≫
        (Functor.associator G Q Γ).inv ≫ Functor.whiskerRight e.hom Γ)
          (ComplexShape.up ℤ)).app J.as :=
    HomologicalComplex.hom_ext _ _ fun i => by
      change σ.app (J.as.X i) ≫ τ.app (G.obj (J.as.X i)) ≫ Γ.map (e.hom.app (J.as.X i)) =
        σ.app (J.as.X i) ≫ τ.app (G.obj (J.as.X i)) ≫
          𝟙 (Γ.obj (Q.obj (G.obj (J.as.X i)))) ≫ Γ.map (e.hom.app (J.as.X i))
      simp
  refine Eq.trans (congrArg ((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app J.as) ≫ ·)
      ((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map_comp _ _).symm) ?_
  exact ((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg _ key)

end HomotopyCategory

/-! ### The two shapes of descent -/

section Derived

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃] [HasDerivedCategory.{w₃} A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄] [HasDerivedCategory.{w₄} A₄]
  (F : A₁ ⥤ A₄) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : A₁ ⥤ A₃) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (Γ : A₃ ⥤ A₄) [Γ.Additive] (RΓ : DerivedCategory A₃ ⥤ DerivedCategory A₄)
  (η : Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)

/-- Cancelling the factorization comparisons in a degreewise factorization through `η`. -/
private theorem factorsh_tail (K : A₁ ⥤ A₂) [K.Additive] [PreservesFiniteLimits K]
    [PreservesFiniteColimits K] (I' : A₂ ⥤ A₃) [I'.Additive] [PreservesFiniteLimits I']
    [PreservesFiniteColimits I'] (e : K ⋙ I' ≅ R) (J : HomotopyCategory A₁ (ComplexShape.up ℤ))
    {X Y : HomotopyCategory A₄ (ComplexShape.up ℤ)} (x : X ⟶ Y)
    (y : Y ⟶ (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((I'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((K.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)))
    (z : X ⟶ (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))
    (h : (x ≫ y) ≫ (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) = z) :
    DerivedCategory.Qh.map x ≫ DerivedCategory.Qh.map y ≫
        η.app ((I'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((K.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
      RΓ.map (I'.mapDerivedCategoryFactorsh.inv.app
          ((K.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RΓ.map (I'.mapDerivedCategory.map (K.mapDerivedCategoryFactorsh.inv.app J)) ≫
          RΓ.map (I'.mapDerivedCategory.map (K.mapDerivedCategoryFactorsh.hom.app J)) ≫
            RΓ.map (I'.mapDerivedCategoryFactorsh.hom.app
                ((K.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
              RΓ.map (DerivedCategory.Qh.map
                ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J)) ≫
                RΓ.map (R.mapDerivedCategoryFactorsh.inv.app J) =
      DerivedCategory.Qh.map z ≫ η.app ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        RΓ.map (R.mapDerivedCategoryFactorsh.inv.app J) := by
  have hη := η.naturality ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J)
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [I'.mapDerivedCategory.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc, ← h, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hη]

section Source

variable (P : A₁ ⥤ A₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (F' : A₂ ⥤ A₄) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  (Q' : A₂ ⥤ A₃) [Q'.Additive] [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
  (e₁ : P ⋙ F' ≅ F) (e₂ : P ⋙ Q' ≅ R) (u' : F' ⟶ Q' ⋙ Γ)
  (V' : F'.mapDerivedCategory ⟶ Q'.mapDerivedCategory ⋙ RΓ)

/-- The degreewise factorization of a transformation out of `F'` carried to one out of `F` by the
two composition comparisons: it factors the degreewise action of the transformation
`F ⟶ R ⋙ Γ` assembled from `u'`, exactly as a descent along `η` does. -/
private theorem compIso_whiskerLeft_fac_app
    (hV' : ∀ J, F'.mapDerivedCategoryFactorsh.inv.app J ≫ V'.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F' Q' Γ u').app J) ≫
        η.app ((Q'.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (Q'.mapDerivedCategoryFactorsh.inv.app J))
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app J ≫
        ((Functor.mapDerivedCategoryCompIsoOfCompIso e₁).inv ≫
          Functor.whiskerLeft P.mapDerivedCategory V' ≫
            (Functor.associator _ _ _).inv ≫
              Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso e₂).hom RΓ).app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F R Γ
          (e₁.inv ≫ Functor.whiskerLeft P u' ≫ (Functor.associator P Q' Γ).inv ≫
            Functor.whiskerRight e₂.hom Γ)).app J) ≫
        η.app ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (R.mapDerivedCategoryFactorsh.inv.app J) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [Functor.mapDerivedCategoryCompIso_inv_app_Qh,
    Functor.mapDerivedCategoryCompIso_hom_app_Qh]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have hnat : F'.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.inv.app J) ≫
        V'.app (P.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      V'.app (DerivedCategory.Qh.obj ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RΓ.map (Q'.mapDerivedCategory.map (P.mapDerivedCategoryFactorsh.inv.app J)) :=
    V'.naturality (P.mapDerivedCategoryFactorsh.inv.app J)
  rw [reassoc_of% hnat, reassoc_of% (hV' ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))]
  have hbig : ((Functor.mapHomotopyCategoryCompIso e₁ (ComplexShape.up ℤ)).inv.app J ≫
        (mapHomotopyCategoryOfComp F' Q' Γ u').app
          ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso e₂ (ComplexShape.up ℤ)).hom.app J) =
      (mapHomotopyCategoryOfComp F R Γ (e₁.inv ≫ Functor.whiskerLeft P u' ≫
        (Functor.associator P Q' Γ).inv ≫ Functor.whiskerRight e₂.hom Γ)).app J := by
    rw [Category.assoc, mapHomotopyCategoryCompIso_inv_app]
    exact mapHomotopyCategoryOfComp_trans F P F' Q' Γ R e₁.inv u' e₂ J
  exact factorsh_tail R Γ RΓ η P Q' e₂ J _ _ _ hbig

/-- **A transformation carried along a change of the source category is a descent.** For an
exact `P : A₁ ⥤ A₂`, isomorphisms `e₁ : P ⋙ F' ≅ F` and `e₂ : P ⋙ Q' ≅ R`, and a transformation
`V'` on unbounded derived categories which descends `u' : F' ⟶ Q' ⋙ Γ`, the transformation
`F.mapDerivedCategory ⟶ R.mapDerivedCategory ⋙ RΓ` obtained from `V'` by the two composition
comparisons descends the transformation `F ⟶ R ⋙ Γ` obtained from `u'` by `e₁` and `e₂`. -/
public theorem compIso_whiskerLeft_eq_exactDerivedDesc
    (hV' : ∀ J, F'.mapDerivedCategoryFactorsh.inv.app J ≫ V'.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F' Q' Γ u').app J) ≫
        η.app ((Q'.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (Q'.mapDerivedCategoryFactorsh.inv.app J)) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e₁).inv ≫
        Functor.whiskerLeft P.mapDerivedCategory V' ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso e₂).hom RΓ =
      exactDerivedDesc F R Γ RΓ η (e₁.inv ≫ Functor.whiskerLeft P u' ≫
        (Functor.associator P Q' Γ).inv ≫ Functor.whiskerRight e₂.hom Γ) :=
  Functor.rightDerived_ext F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) _ _ _
    (NatTrans.ext (funext fun J =>
      (compIso_whiskerLeft_fac_app F R Γ RΓ η P F' Q' e₁ e₂ u' V' hV' J).trans
        (exactDerivedDesc_fac_app F R Γ RΓ η _ J).symm))

end Source

section Target

variable (Q : A₁ ⥤ A₂) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  (Γ' : A₂ ⥤ A₄) [Γ'.Additive] (I : A₂ ⥤ A₃) [I.Additive] [PreservesFiniteLimits I]
  [PreservesFiniteColimits I] (RΓ' : DerivedCategory A₂ ⥤ DerivedCategory A₄)
  (η' : Γ'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ')
  (e₃ : Q ⋙ I ≅ R) (u : F ⟶ Q ⋙ Γ') (r : Γ' ⟶ I ⋙ Γ)
  (V : F.mapDerivedCategory ⟶ Q.mapDerivedCategory ⋙ RΓ')
  (Res : RΓ' ⟶ I.mapDerivedCategory ⋙ RΓ)

/-- The degreewise factorization of a transformation out of `F` followed by a restriction of the
derived target: it factors the degreewise action of the transformation `F ⟶ R ⋙ Γ` assembled from
`u` and `r`, exactly as a descent along `η` does. -/
private theorem whiskerLeft_compIso_fac_app
    (hV : ∀ J, F.mapDerivedCategoryFactorsh.inv.app J ≫ V.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F Q Γ' u).app J) ≫
        η'.app ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ'.map (Q.mapDerivedCategoryFactorsh.inv.app J))
    (hRes : ∀ J, η'.app J ≫ Res.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp Γ' I Γ r).app J) ≫
        η.app ((I.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (I.mapDerivedCategoryFactorsh.inv.app J))
    (J : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app J ≫
        (V ≫ Functor.whiskerLeft Q.mapDerivedCategory Res ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso e₃).hom RΓ).app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F R Γ
          (u ≫ Functor.whiskerLeft Q r ≫ (Functor.associator Q I Γ).inv ≫
            Functor.whiskerRight e₃.hom Γ)).app J) ≫
        η.app ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (R.mapDerivedCategoryFactorsh.inv.app J) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Qh]
  simp only [Functor.map_comp]
  rw [reassoc_of% (hV J)]
  have hnat : RΓ'.map (Q.mapDerivedCategoryFactorsh.inv.app J) ≫
        Res.app (Q.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      Res.app (DerivedCategory.Qh.obj ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        RΓ.map (I.mapDerivedCategory.map (Q.mapDerivedCategoryFactorsh.inv.app J)) :=
    Res.naturality (Q.mapDerivedCategoryFactorsh.inv.app J)
  rw [reassoc_of% hnat, reassoc_of% (hRes ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))]
  have hbig : ((mapHomotopyCategoryOfComp F Q Γ' u).app J ≫
        (mapHomotopyCategoryOfComp Γ' I Γ r).app
          ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj J)) ≫
        (Γ.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso e₃ (ComplexShape.up ℤ)).hom.app J) =
      (mapHomotopyCategoryOfComp F R Γ (u ≫ Functor.whiskerLeft Q r ≫
        (Functor.associator Q I Γ).inv ≫ Functor.whiskerRight e₃.hom Γ)).app J :=
    (Category.assoc _ _ _).trans (mapHomotopyCategoryOfComp_trans F Q Γ' I Γ R u r e₃ J)
  exact factorsh_tail R Γ RΓ η Q I e₃ J _ _ _ hbig

/-- **A transformation followed by a restriction of the derived target is a descent.** For a
transformation `V` on unbounded derived categories descending `u : F ⟶ Q ⋙ Γ'`, a transformation
`Res` descending `r : Γ' ⟶ I ⋙ Γ`, and an isomorphism `e₃ : Q ⋙ I ≅ R`, the transformation
`F.mapDerivedCategory ⟶ R.mapDerivedCategory ⋙ RΓ` obtained by composing them descends the
transformation `F ⟶ R ⋙ Γ` obtained from `u`, `r` and `e₃`. -/
public theorem whiskerLeft_compIso_eq_exactDerivedDesc
    (hV : ∀ J, F.mapDerivedCategoryFactorsh.inv.app J ≫ V.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp F Q Γ' u).app J) ≫
        η'.app ((Q.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ'.map (Q.mapDerivedCategoryFactorsh.inv.app J))
    (hRes : ∀ J, η'.app J ≫ Res.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((mapHomotopyCategoryOfComp Γ' I Γ r).app J) ≫
        η.app ((I.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          RΓ.map (I.mapDerivedCategoryFactorsh.inv.app J)) :
    V ≫ Functor.whiskerLeft Q.mapDerivedCategory Res ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso e₃).hom RΓ =
      exactDerivedDesc F R Γ RΓ η (u ≫ Functor.whiskerLeft Q r ≫
        (Functor.associator Q I Γ).inv ≫ Functor.whiskerRight e₃.hom Γ) :=
  Functor.rightDerived_ext F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ)) _ _ _
    (NatTrans.ext (funext fun J =>
      (whiskerLeft_compIso_fac_app F R Γ RΓ η Q Γ' I RΓ' η' e₃ u r V Res hV hRes J).trans
        (exactDerivedDesc_fac_app F R Γ RΓ η _ J).symm))

end Target

end Derived

end Stacks.DerivedFunctor

end
