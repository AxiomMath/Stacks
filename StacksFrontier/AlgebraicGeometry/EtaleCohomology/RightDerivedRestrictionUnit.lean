module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived

/-!
# The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` on the termwise image of a complex

Let `CategoryTheory.Functor.rightDerivedRestrictionIso` be the comparison `RG' ⋙ r_M ≅ r_A ⋙ RG`
attached to exact functors `r_A`, `r_M` and an isomorphism `e : G' ⋙ r_M ≅ r_A ⋙ G`.  On the
image in the derived category of a bounded below complex `N`, this comparison is computed by
`e` on the termwise images: `r_M` of the canonical map `Q(G'(N)) ⟶ RG'(Q N)`, followed by the
comparison, is `Q(e_N)` followed by the canonical map `Q(G(r_A N)) ⟶ RG(Q(r_A N))`, up to the
commutation of `Q` with `r_A` and `r_M`.

This is how the comparison of the cohomology of a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules with that of the
same sheaf viewed over `ℤ/ℓⁿ⁺²ℤ` is read on an injective resolution, in [Tag 03V2].

## Main results

* `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_comp_rightDerivedRestrictionIso_hom_app`

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Quotient

variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]

/-- The action on bounded below homotopy categories of an isomorphism of additive functors is,
on the image of a complex, the image of the termwise isomorphism. -/
theorem mapHomotopyCategoryPlusNatIso_hom_app_quotient {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) (N : CochainComplex.Plus A) :
    (mapHomotopyCategoryPlusNatIso e).hom.app ((HomotopyCategory.Plus.quotient A).obj N) =
      (HomotopyCategory.Plus.quotient B).map
        (ObjectProperty.homMk (X := F.mapCochainComplexPlus.obj N)
          (Y := G.mapCochainComplexPlus.obj N)
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj)) := by
  apply (HomotopyCategory.Plus.ι B).map_injective
  show (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N.obj) = _
  rfl

end Quotient

section Unbounded

/-- A functor sends a pair of mutually inverse morphisms to a pair of mutually inverse morphisms. -/
private lemma map_comp_eq_id {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {X Y : C}
    {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 _) : H.map f ≫ H.map g = 𝟙 _ := by
  rw [← H.map_comp, h, H.map_id]

/-- Cancellation of three inverse pairs around a morphism, on variables. -/
private lemma comp_eq_of_three_inverses {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₀) (c : X₀ ⟶ X₂) (d : X₂ ⟶ X₃) (e : X₃ ⟶ X₄) (f : X₄ ⟶ X₃)
    (g : X₃ ⟶ X₂) (hab : a ≫ b = 𝟙 _) (hef : e ≫ f = 𝟙 _) (hdg : d ≫ g = 𝟙 _) :
    a ≫ (b ≫ c ≫ d ≫ e) ≫ f ≫ g = c := by
  simp only [Category.assoc]
  rw [reassoc_of% hab, reassoc_of% hef, hdg, Category.comp_id]

private lemma ι_map_quotientCompQhIso_hom_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K) =
      (DerivedCategory.quotientCompQhIso C).hom.app K.obj := by
  refine ((DerivedCategory.Plus.ι).map_preimage _).trans ?_
  show 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  rw [DerivedCategory.Qh.map_id]
  exact (Category.id_comp _).trans (Category.id_comp _)

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- In the unbounded derived category, the commutation `Q ⋙ F⁺ ≅ F ⋙ Q` of the localization
with an exact functor on bounded below complexes is the commutation
`CategoryTheory.Functor.mapDerivedCategoryFactors` on all complexes. -/
theorem ι_map_mapDerivedCategoryPlusQIso_hom_app (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusQIso F).hom.app K) =
      F.mapDerivedCategoryFactors.hom.app K.obj := by
  have hA : DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso A).inv.app K) =
      (DerivedCategory.quotientCompQhIso A).inv.app K.obj :=
    congrArg Iso.inv (Iso.ext (ι_map_quotientCompQhIso_hom_app K) :
      DerivedCategory.Plus.ι.mapIso ((DerivedCategory.Plus.quotientCompQhIso A).app K) =
        (DerivedCategory.quotientCompQhIso A).app K.obj)
  have hH : (HomotopyCategory.Plus.ι B).map
      ((Stacks.AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).hom.app K) =
      (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K.obj :=
    (HomotopyCategory.Plus.ι B).map_preimage _
  simp only [mapDerivedCategoryPlusQIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Iso.symm_hom,
    associator_hom_app, associator_inv_app, Category.id_comp, Functor.map_comp]
  show F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.quotientCompQhIso A).inv.app K)) ≫
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K.obj) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι B).map
      ((Stacks.AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).hom.app K)) ≫
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso B).hom.app
      (F.mapCochainComplexPlus.obj K)) = _
  rw [hA, F.mapDerivedCategoryFactorsh_hom_app K.obj, hH, ι_map_quotientCompQhIso_hom_app]
  exact comp_eq_of_three_inverses _ _ _ _ _ _ _ (map_comp_eq_id _ (Iso.inv_hom_id_app _ _))
    (map_comp_eq_id _ (Iso.inv_hom_id_app _ _)) (Iso.inv_hom_id_app _ _)

/-- The inverse of the commutation `Q ⋙ F⁺ ≅ F ⋙ Q` at a bounded below complex, through the
factorization of `F⁺` on the bounded below homotopy category. -/
private theorem mapDerivedCategoryPlusQIso_inv_app (K : CochainComplex.Plus A) :
    (mapDerivedCategoryPlusQIso F).inv.app K =
      ((DerivedCategory.Plus.quotientCompQhIso B).app (F.mapCochainComplexPlus.obj K)).inv ≫
        F.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
          F.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).app K).hom := by
  simp only [mapDerivedCategoryPlusQIso, Iso.trans_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app,
    whiskerRight_app, Iso.symm_inv, associator_hom_app,
    associator_inv_app, Category.id_comp, Category.assoc,
    mapHomotopyCategoryPlusFactors_inv_app]
  exact whisker_eq _ ((eq_whisker (DerivedCategory.Plus.Qh.map_id _) _).trans
    (Category.id_comp _))

end Unbounded

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M'] [HasDerivedCategory M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]

/-- **The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` on the termwise image of a bounded below complex.**
`r_M` of the canonical map `Q(G'(N)) ⟶ RG'(Q N)`, followed by the comparison, is the termwise
identification `Q(r_M(G'(N))) ≅ Q(G(r_A(N)))` followed by the canonical map for `G` at
`r_A(N)`, up to the commutation of `Q` with `r_A` and `r_M`. -/
theorem mapCochainComplexPlusDerivedUnit_comp_rightDerivedRestrictionIso_hom_app
    (e : G' ⋙ rM ≅ rA ⋙ G) (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I))
    (N : CochainComplex.Plus A') :
    (mapDerivedCategoryPlusQIso rM).inv.app (G'.mapCochainComplexPlus.obj N) ≫
        rM.mapDerivedCategoryPlus.map (G'.mapCochainComplexPlusDerivedUnit.app N) ≫
        (rightDerivedRestrictionIso G' G rA rM e hac).hom.app (DerivedCategory.Plus.Q.obj N) =
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          (X := rM.mapCochainComplexPlus.obj (G'.mapCochainComplexPlus.obj N))
          (Y := G.mapCochainComplexPlus.obj (rA.mapCochainComplexPlus.obj N))
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj)) ≫
        G.mapCochainComplexPlusDerivedUnit.app (rA.mapCochainComplexPlus.obj N) ≫
        G.rightDerivedFunctorPlus.map ((mapDerivedCategoryPlusQIso rA).inv.app N) := by
  let K := (HomotopyCategory.Plus.quotient A').obj N
  let qA' := (DerivedCategory.Plus.quotientCompQhIso A').app N
  let qM' := (DerivedCategory.Plus.quotientCompQhIso M').app (G'.mapCochainComplexPlus.obj N)
  let qA := (DerivedCategory.Plus.quotientCompQhIso A).app (rA.mapCochainComplexPlus.obj N)
  let qM := (DerivedCategory.Plus.quotientCompQhIso M).app
    (rM.mapCochainComplexPlus.obj (G'.mapCochainComplexPlus.obj N))
  let qM₂ := (DerivedCategory.Plus.quotientCompQhIso M).app
    (G.mapCochainComplexPlus.obj (rA.mapCochainComplexPlus.obj N))
  let θ := rightDerivedRestrictionIso G' G rA rM e hac
  let eN : rM.mapCochainComplexPlus.obj (G'.mapCochainComplexPlus.obj N) ⟶
      G.mapCochainComplexPlus.obj (rA.mapCochainComplexPlus.obj N) :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj)
  have hQM : (mapDerivedCategoryPlusQIso rM).inv.app (G'.mapCochainComplexPlus.obj N) =
      qM.inv ≫ rM.mapDerivedCategoryPlusFactorsh.inv.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        rM.mapDerivedCategoryPlus.map qM'.hom :=
    mapDerivedCategoryPlusQIso_inv_app rM _
  have hQA : (mapDerivedCategoryPlusQIso rA).inv.app N =
      qA.inv ≫ rA.mapDerivedCategoryPlusFactorsh.inv.app K ≫
        rA.mapDerivedCategoryPlus.map qA'.hom :=
    mapDerivedCategoryPlusQIso_inv_app rA N
  have hdu' : G'.mapCochainComplexPlusDerivedUnit.app N =
      qM'.inv ≫ G'.rightDerivedFunctorPlusUnit.app K ≫ G'.rightDerivedFunctorPlus.map qA'.hom :=
    rfl
  have hdu : G.mapCochainComplexPlusDerivedUnit.app (rA.mapCochainComplexPlus.obj N) =
      qM₂.inv ≫ G.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map qA.hom :=
    rfl
  have s1 : rM.mapDerivedCategoryPlus.map qM'.hom ≫
      rM.mapDerivedCategoryPlus.map (G'.mapCochainComplexPlusDerivedUnit.app N) =
      rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnit.app K) ≫
        rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlus.map qA'.hom) := by
    rw [hdu', ← Functor.map_comp, Iso.hom_inv_id_assoc]
    exact rM.mapDerivedCategoryPlus.map_comp _ _
  have s2 : rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlus.map qA'.hom) ≫
      θ.hom.app (DerivedCategory.Plus.Q.obj N) =
      θ.hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlus.map qA'.hom) :=
    θ.hom.naturality qA'.hom
  have hE : (mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ rM))).hom.app K ≫
      (mapHomotopyCategoryPlusNatIso e).hom.app K ≫
      (mapHomotopyCategoryPlusCompIso (Iso.refl (rA ⋙ G))).inv.app K =
      (HomotopyCategory.Plus.quotient M).map eN := by
    rw [mapHomotopyCategoryPlusCompIso_refl_hom_app, mapHomotopyCategoryPlusCompIso_refl_inv_app]
    exact (Category.id_comp _).trans ((Category.comp_id _).trans
      (mapHomotopyCategoryPlusNatIso_hom_app_quotient e N))
  have hnq : DerivedCategory.Plus.Q.map eN ≫ qM₂.inv =
      qM.inv ≫ DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient M).map eN) :=
    (DerivedCategory.Plus.quotientCompQhIso M).inv.naturality eN
  rw [hQM, hQA, hdu]
  let a := rM.mapDerivedCategoryPlusFactorsh.inv.app (G'.mapHomotopyCategoryPlus.obj K)
  let b := rM.mapDerivedCategoryPlus.map qM'.hom
  let c := rM.mapDerivedCategoryPlus.map (G'.mapCochainComplexPlusDerivedUnit.app N)
  let d := θ.hom.app (DerivedCategory.Plus.Q.obj N)
  let u' := rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlusUnit.app K)
  let x := rM.mapDerivedCategoryPlus.map (G'.rightDerivedFunctorPlus.map qA'.hom)
  let θK := θ.hom.app (DerivedCategory.Plus.Qh.obj K)
  let y := G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlus.map qA'.hom)
  let eh := rM.mapDerivedCategoryPlusFactorsh.hom.app (G'.mapHomotopyCategoryPlus.obj K)
  let E := DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient M).map eN)
  let v := G.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj K)
  let w := G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusFactorsh.inv.app K)
  have s3' : u' ≫ θK = eh ≫ E ≫ v ≫ w :=
    (map_unit_comp_rightDerivedRestrictionIso_hom_app G' G rA rM e hac K).trans
      (whisker_eq _ (eq_whisker (congrArg DerivedCategory.Plus.Qh.map hE) _))
  have L : (a ≫ b) ≫ c ≫ d = E ≫ v ≫ w ≫ y := by
    have t1 : (a ≫ b) ≫ c ≫ d = a ≫ (b ≫ c) ≫ d :=
      (Category.assoc a b (c ≫ d)).trans (congrArg (a ≫ ·) (Category.assoc b c d).symm)
    have t2 : a ≫ (b ≫ c) ≫ d = a ≫ u' ≫ x ≫ d :=
      congrArg (a ≫ ·) ((congrArg (· ≫ d) s1).trans (Category.assoc u' x d))
    have t3 : a ≫ u' ≫ x ≫ d = a ≫ (u' ≫ θK) ≫ y :=
      congrArg (a ≫ ·) ((congrArg (u' ≫ ·) s2).trans (Category.assoc u' θK y).symm)
    have t4 : a ≫ (u' ≫ θK) ≫ y = (a ≫ eh) ≫ E ≫ v ≫ w ≫ y := by
      refine (congrArg (a ≫ ·) (congrArg (· ≫ y) s3')).trans ?_
      refine Eq.trans ?_ (Category.assoc a eh (E ≫ v ≫ w ≫ y)).symm
      refine whisker_eq a ((Category.assoc eh (E ≫ v ≫ w) y).trans (whisker_eq eh ?_))
      exact (Category.assoc E (v ≫ w) y).trans (whisker_eq E (Category.assoc v w y))
    have t5 : a ≫ eh = 𝟙 _ := Iso.inv_hom_id_app _ _
    exact t1.trans (t2.trans (t3.trans (t4.trans ((congrArg (· ≫ E ≫ v ≫ w ≫ y) t5).trans
      (Category.id_comp _)))))
  have R : (v ≫ G.rightDerivedFunctorPlus.map qA.hom) ≫
      G.rightDerivedFunctorPlus.map (qA.inv ≫
          rA.mapDerivedCategoryPlusFactorsh.inv.app K ≫ rA.mapDerivedCategoryPlus.map qA'.hom) =
      v ≫ w ≫ y := by
    refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
    refine (whisker_eq _ (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).symm.trans ?_)
    exact (eq_whisker (map_comp_eq_id _ qA.hom_inv_id) _).trans
      ((Category.id_comp _).trans (Functor.map_comp _ _ _))
  calc (qM.inv ≫ a ≫ b) ≫ c ≫ d = qM.inv ≫ (a ≫ b) ≫ c ≫ d := Category.assoc _ _ _
    _ = qM.inv ≫ E ≫ v ≫ w ≫ y := congrArg (qM.inv ≫ ·) L
    _ = (qM.inv ≫ E) ≫ v ≫ w ≫ y := (Category.assoc _ _ _).symm
    _ = (DerivedCategory.Plus.Q.map eN ≫ qM₂.inv) ≫ v ≫ w ≫ y := congrArg (· ≫ v ≫ w ≫ y) hnq.symm
    _ = DerivedCategory.Plus.Q.map eN ≫ qM₂.inv ≫ (v ≫ G.rightDerivedFunctorPlus.map qA.hom) ≫
          G.rightDerivedFunctorPlus.map (qA.inv ≫ rA.mapDerivedCategoryPlusFactorsh.inv.app K ≫
            rA.mapDerivedCategoryPlus.map qA'.hom) :=
        (Category.assoc _ _ _).trans (whisker_eq _ (whisker_eq _ R.symm))
    _ = _ := whisker_eq _ (Category.assoc _ _ _).symm

end CategoryTheory.Functor
