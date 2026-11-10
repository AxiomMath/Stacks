module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition

/-!
# A coherence triangle for composition comparisons of right derived functors

Let `F : 𝒜 ⥤ 𝒜₁`, `G : 𝒜₁ ⥤ ℬ`, `G' : 𝒜 ⥤ ℬ`, `H : ℬ ⥤ 𝒞`, `P : 𝒜 ⥤ 𝒞` and `P₁ : 𝒜₁ ⥤ 𝒞` be
additive functors with isomorphisms

`ea : F ⋙ P₁ ≅ P`, `eb : G ⋙ H ≅ P₁`, `eb' : G' ⋙ H ≅ P`, `ec : F ⋙ G ≅ G'`,

and assume `F`, `G`, `G'` preserve injective objects.  Each isomorphism gives a composition
comparison of right derived functors on `D⁺`
(`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso`). This file proves that the two
resulting maps `RP(M) ⟶ RH(RG(RF(M)))` agree as soon as the underived triangle commutes.

This is the coherence needed to compare an endomorphism of `RΓ(Y, M)` induced by an endomorphism
`π` of `Y` over `Z` with the endomorphism it induces on `RΓ(Z, Rg_* M)`.

The argument is the one of `Stacks.DerivedFunctor.LeraySquare.derived_coherence`: both sides
are transformations out of the right derived functor `RP`, so `Functor.rightDerived_ext`
reduces the identity to the derived-functor unit of `RP` at complexes, where every comparison is
computed by its factorization, and what is left is a degreewise identity.
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Functor Limits

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Factorization

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} Z]
  [Abelian X] [Abelian Y] [Abelian Z]
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y] [HasDerivedCategory.{w₂} Z]
  [EnoughInjectives X] [EnoughInjectives Y]

/-- **The factorization characterising `rightDerivedFunctorPlusCompIsoOfIso F G H e`**: composed
with the derived-functor unit of `RH` at a bounded below complex `K`, it is the degreewise action
of `e.inv`, followed by the unit of `RG` at `F(K)` and `RG` of the unit of `RF` at `K`. -/
theorem unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom (F : X ⥤ Y) (G : Y ⥤ Z) (H : X ⥤ Z)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory.Plus X) :
    H.rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).inv.app K) ≫
        G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
  have h1 : H.rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusIsoOfCompIso F G H e).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIsoOfCompIso F G H e).inv.app K) ≫
        (F ⋙ G).rightDerivedFunctorPlusUnith.app K := by
    rw [rightDerivedFunctorPlusIsoOfCompIso, rightDerivedNatIso_inv]
    exact rightDerivedNatTrans_app _ _ _ _ _ _ K
  dsimp only [rightDerivedFunctorPlusCompIsoOfIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← Category.assoc, h1, Category.assoc, rightDerivedFunctorPlusCompIso_hom,
    rightDerivedFunctorPlusComp_fac_app, ← Category.assoc, ← Functor.map_comp]
  congr 2
  simp [mapHomotopyCategoryPlusIsoOfCompIso]

end Factorization

section Triangle

variable {A : Type u₁} {A₁ : Type u₂} {B : Type u₃} {C : Type u₄}
  [Category.{v₁} A] [Category.{v₂} A₁] [Category.{v₃} B] [Category.{v₄} C]
  [Abelian A] [Abelian A₁] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} A₁] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₂} C]
  [EnoughInjectives A] [EnoughInjectives A₁] [EnoughInjectives B]
  {F : A ⥤ A₁} {G : A₁ ⥤ B} {G' : A ⥤ B} {H : B ⥤ C} {P : A ⥤ C} {P₁ : A₁ ⥤ C}
  [F.Additive] [G.Additive] [G'.Additive] [H.Additive] [P.Additive] [P₁.Additive]
  [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] [G'.PreservesInjectiveObjects]

omit [HasDerivedCategory A] [HasDerivedCategory A₁] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives A₁] [EnoughInjectives B] [F.PreservesInjectiveObjects]
  [G.PreservesInjectiveObjects] [G'.PreservesInjectiveObjects] in
/-- The underived triangle, solved for the degreewise maps on bounded below homotopy
categories. -/
private lemma triangle_homotopy (ea : F ⋙ P₁ ≅ P) (eb : G ⋙ H ≅ P₁) (eb' : G' ⋙ H ≅ P)
    (ec : F ⋙ G ≅ G')
    (h : ∀ N : A, eb'.inv.app N ≫ H.map (ec.inv.app N) = ea.inv.app N ≫ eb.inv.app (F.obj N))
    (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusCompIso eb').inv.app K ≫
        H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusCompIso ec).inv.app K) =
      (mapHomotopyCategoryPlusCompIso ea).inv.app K ≫
        (mapHomotopyCategoryPlusCompIso eb).inv.app (F.mapHomotopyCategoryPlus.obj K) := by
  ext
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso eb' (ComplexShape.up ℤ)).inv.app K.obj.as) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((mapHomologicalComplexCompIso ec (ComplexShape.up ℤ)).inv.app K.obj.as)) =
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso ea (ComplexShape.up ℤ)).inv.app K.obj.as) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((mapHomologicalComplexCompIso eb (ComplexShape.up ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj.as))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f]
  exact h _

/-- **The coherence triangle of composition comparisons.**  If the underived triangle
`eb'⁻¹ ≫ H(ec⁻¹) = ea⁻¹ ≫ eb⁻¹` commutes, then the two maps `RP(M) ⟶ RH(RG(RF(M)))` built from
the derived comparisons `RP ≅ RG' ⋙ RH`, `RG' ≅ RF ⋙ RG`, `RP ≅ RF ⋙ RP₁` and
`RP₁ ≅ RG ⋙ RH` agree. -/
theorem rightDerivedFunctorPlusCompIsoOfIso_triangle (ea : F ⋙ P₁ ≅ P) (eb : G ⋙ H ≅ P₁)
    (eb' : G' ⋙ H ≅ P) (ec : F ⋙ G ≅ G')
    (h : ∀ N : A, eb'.inv.app N ≫ H.map (ec.inv.app N) = ea.inv.app N ≫ eb.inv.app (F.obj N))
    (M : DerivedCategory.Plus A) :
    (rightDerivedFunctorPlusCompIsoOfIso G' H P eb').hom.app M ≫
        H.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusCompIsoOfIso F G G' ec).hom.app M) =
      (rightDerivedFunctorPlusCompIsoOfIso F P₁ P ea).hom.app M ≫
        (rightDerivedFunctorPlusCompIsoOfIso G H P₁ eb).hom.app
          (F.rightDerivedFunctorPlus.obj M) := by
  have key : (rightDerivedFunctorPlusCompIsoOfIso G' H P eb').hom ≫
      Functor.whiskerRight (rightDerivedFunctorPlusCompIsoOfIso F G G' ec).hom
        H.rightDerivedFunctorPlus =
      (rightDerivedFunctorPlusCompIsoOfIso F P₁ P ea).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIsoOfIso G H P₁ eb).hom := by
    refine Functor.rightDerived_ext P.rightDerivedFunctorPlus P.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K => ?_))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have hu : ∀ {X Y : HomotopyCategory.Plus B} (ψ : X ⟶ Y),
        H.rightDerivedFunctorPlusUnith.app X ≫
          H.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map ψ) =
        DerivedCategory.Plus.Qh.map (H.mapHomotopyCategoryPlus.map ψ) ≫
          H.rightDerivedFunctorPlusUnith.app Y :=
      fun ψ => (H.rightDerivedFunctorPlusUnith.naturality ψ).symm
    have hn : P₁.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (rightDerivedFunctorPlusCompIsoOfIso G H P₁ eb).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
        (rightDerivedFunctorPlusCompIsoOfIso G H P₁ eb).hom.app
            (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
          H.rightDerivedFunctorPlus.map
            (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K)) :=
      (rightDerivedFunctorPlusCompIsoOfIso G H P₁ eb).hom.naturality _
    rw [reassoc_of% (unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom G' H P eb' K),
      ← Functor.map_comp, unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom F G G' ec K,
      Functor.map_comp, ← Category.assoc (H.rightDerivedFunctorPlusUnith.app _),
      hu,
      reassoc_of% (unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom F P₁ P ea K),
      hn,
      reassoc_of% (unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom G H P₁ eb
        (F.mapHomotopyCategoryPlus.obj K))]
    have e2 := congrArg DerivedCategory.Plus.Qh.map (triangle_homotopy ea eb eb' ec h K)
    simp only [Functor.map_comp] at e2
    simp only [Category.assoc, Functor.map_comp]
    rw [reassoc_of% e2]
    rfl
  exact NatTrans.congr_app key M

end Triangle

end Stacks.EtaleCohomology

end
