module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition

/-!
# Computing `Hᵐ(RG(N))` on acyclic complexes commutes with exact restriction functors

Let `G' : 𝒜' ⥤ ℳ'` and `G : 𝒜 ⥤ ℳ` be additive functors, `r_𝒜 : 𝒜' ⥤ 𝒜` and `r_ℳ : ℳ' ⥤ ℳ` exact
functors and `e : G' ⋙ r_ℳ ≅ r_𝒜 ⋙ G`, with `r_𝒜` carrying injectives to `G`-acyclic objects, so
that `RG' ⋙ r_ℳ ≅ r_𝒜 ⋙ RG` (`CategoryTheory.Functor.rightDerivedRestrictionIso`). For a bounded
below complex `N` of `G'`-acyclic objects whose image `r_𝒜 N` is `G`-acyclic, the identifications
`Hᵐ(G' N) ≅ Hᵐ(RG'(N))` and `Hᵐ(G(r_𝒜 N)) ≅ Hᵐ(RG(r_𝒜 N))`
(`CategoryTheory.Functor.homologyIsoRightDerivedFunctorPlusOfRightAcyclic`) are compatible with
`r_ℳ`, `e` and the comparison
(`CategoryTheory.Functor.homologyIsoRightDerivedFunctorPlusOfRightAcyclic_restriction`).

For `G = Γ(Y, -)` on sheaves of `Λ`-modules and `r` the restriction of scalars to `ℤ`, this says
that the cohomology of a sheaf of `Λ`-modules computed on an acyclic resolution, read as an
abelian group, is the cohomology of the underlying abelian sheaf computed on the same resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]

/-- The diagram chase behind
`CategoryTheory.Functor.homologyIsoRightDerivedFunctorPlusOfRightAcyclic_restriction`, on abstract
morphisms. -/
private lemma restriction_chase {C D : Type*} [Category* C] [Category* D] (r : C ⥤ D)
    {x0 y0 y1 : C} {X P0 P1 P2 P0' Q0 Q1 : D} (f' : x0 ⟶ y0) (f'' : y0 ⟶ x0)
    (hf : f' ≫ f'' = 𝟙 x0) (du : y0 ⟶ y1) (i0 : r.obj y0 ⟶ P0) (i1 : r.obj y1 ⟶ P1)
    (g : P0 ⟶ P1) (t : P1 ⟶ P2) (q : P0 ⟶ P0') (c : r.obj x0 ⟶ X) (φ : X ⟶ P0')
    {Q2 : D} (a : P0' ⟶ Q0) (b₁ : Q0 ⟶ Q2) (b₂ : Q2 ⟶ P2) (hm : X ⟶ Q1) (φ₂ : Q1 ⟶ Q0)
    (hn : r.map du ≫ i1 = i0 ≫ g) (hU : g ≫ t = q ≫ a ≫ b₁ ≫ b₂)
    (hD : i0 ≫ q = r.map f'' ≫ c ≫ φ) (hF : φ ≫ a = hm ≫ φ₂) :
    r.map (f' ≫ du) ≫ i1 ≫ t = c ≫ hm ≫ (φ₂ ≫ b₁) ≫ b₂ := by
  rw [r.map_comp, Category.assoc, reassoc_of% hn, hU, reassoc_of% hD, ← r.map_comp_assoc, hf,
    r.map_id, Category.id_comp, reassoc_of% hF, Category.assoc]

/-- Inverting the factorization of an isomorphism. -/
private lemma inv_comp_chase {D : Type*} [Category* D] {A B C' X Y : D} (I : A ≅ B) (q : B ⟶ C')
    (u : C' ≅ X) (v : X ≅ Y) (w : Y ≅ A) (h : I.inv = q ≫ u.hom ≫ v.hom ≫ w.hom) :
    I.hom ≫ q = w.inv ≫ v.inv ≫ u.inv := by
  rw [← cancel_mono (u.hom ≫ v.hom ≫ w.hom), Category.assoc, ← h, Iso.hom_inv_id]
  simp

/-- **`Hᵐ` on acyclic complexes commutes with exact restriction functors.** -/
theorem homologyIsoRightDerivedFunctorPlusOfRightAcyclic_restriction
    (e : G' ⋙ rM ≅ rA ⋙ G) (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I))
    (N : CochainComplex.Plus A') (hN : ∀ n, G'.rightAcyclic (N.obj.X n))
    (hN' : ∀ n, G.rightAcyclic ((rA.mapCochainComplexPlus.obj N).obj.X n)) (m : ℤ) :
    rM.map (G'.homologyIsoRightDerivedFunctorPlusOfRightAcyclic N hN m).hom ≫
        (Stacks.DerivedFunctor.derivedHomologyIso rM m).inv.app
          (DerivedCategory.Plus.ι.obj
            (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N))) ≫
        (DerivedCategory.Plus.homologyFunctor M m).map
          ((rightDerivedRestrictionIso G' G rA rM e hac).hom.app (DerivedCategory.Plus.Q.obj N)) =
      (Stacks.DerivedFunctor.complexHomologyIso rM (ComplexShape.up ℤ) m).inv.app
          ((G'.mapHomologicalComplex _).obj N.obj) ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj) m ≫
        (G.homologyIsoRightDerivedFunctorPlusOfRightAcyclic
          (rA.mapCochainComplexPlus.obj N) hN' m).hom ≫
        (DerivedCategory.Plus.homologyFunctor M m).map
          (G.rightDerivedFunctorPlus.map ((mapDerivedCategoryPlusQIso rA).inv.app N)) := by
  have hU := mapCochainComplexPlusDerivedUnit_comp_rightDerivedRestrictionIso_hom_app G' G rA rM e
    hac N
  have hD := Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q rM m
    ((G'.mapHomologicalComplex _).obj N.obj)
  have hι := ι_map_mapDerivedCategoryPlusQIso_hom_app rM (G'.mapCochainComplexPlus.obj N)
  have hn := (Stacks.DerivedFunctor.derivedHomologyIso rM m).inv.naturality
    (DerivedCategory.Plus.ι.map (G'.mapCochainComplexPlusDerivedUnit.app N))
  have hF := (DerivedCategory.homologyFunctorFactors M m).inv.naturality
    ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj)
  have e1 : (G'.homologyIsoRightDerivedFunctorPlusOfRightAcyclic N hN m).hom =
      (DerivedCategory.homologyFunctorFactors M' m).inv.app
          ((G'.mapHomologicalComplex _).obj N.obj) ≫
        (DerivedCategory.Plus.homologyFunctor M' m).map
          (G'.mapCochainComplexPlusDerivedUnit.app N) :=
    rfl
  have e2 : (G.homologyIsoRightDerivedFunctorPlusOfRightAcyclic
      (rA.mapCochainComplexPlus.obj N) hN' m).hom =
      (DerivedCategory.homologyFunctorFactors M m).inv.app
          ((G.mapHomologicalComplex _).obj (rA.mapCochainComplexPlus.obj N).obj) ≫
        (DerivedCategory.Plus.homologyFunctor M m).map
          (G.mapCochainComplexPlusDerivedUnit.app (rA.mapCochainComplexPlus.obj N)) :=
    rfl
  rw [e1, e2]
  have hU' := (Iso.inv_comp_eq ((mapDerivedCategoryPlusQIso rM).app
    (G'.mapCochainComplexPlus.obj N))).1 hU
  have hU2 := congrArg (fun φ => (DerivedCategory.homologyFunctor M m).map
    (DerivedCategory.Plus.ι.map φ)) hU'
  simp only [CategoryTheory.Functor.map_comp, Iso.app_hom] at hU2
  rw [hι] at hU2
  have hD' := inv_comp_chase ((Stacks.DerivedFunctor.derivedHomologyIso rM m).app
      (DerivedCategory.Q.obj ((G'.mapHomologicalComplex _).obj N.obj))).symm
    ((DerivedCategory.homologyFunctor M m).map
      (rM.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex _).obj N.obj)))
    ((DerivedCategory.homologyFunctorFactors M m).app
      ((rM.mapHomologicalComplex _).obj ((G'.mapHomologicalComplex _).obj N.obj)))
    ((Stacks.DerivedFunctor.complexHomologyIso rM (ComplexShape.up ℤ) m).app
      ((G'.mapHomologicalComplex _).obj N.obj))
    (rM.mapIso ((DerivedCategory.homologyFunctorFactors M' m).app
      ((G'.mapHomologicalComplex _).obj N.obj)).symm) hD
  exact restriction_chase rM _ _ (Iso.inv_hom_id_app _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ hn hU2 hD'
    hF.symm


/-- **`Hᵐ(G' N) ≅ Rᵐ G'(X)`** for a bounded below complex `N` of `G'`-acyclic objects and an
isomorphism `ξ : X[0] ≅ N` in the derived category (`N` is an acyclic resolution of `X`). -/
def homologyIsoRightDerivedPlusOfResolution {X : A'} (N : CochainComplex.Plus A')
    (hN : ∀ n, G'.rightAcyclic (N.obj.X n))
    (ξ : (DerivedCategory.Plus.singleFunctor A' 0).obj X ≅ DerivedCategory.Plus.Q.obj N) (m : ℤ) :
    ((G'.mapHomologicalComplex _).obj N.obj).homology m ≅ (G'.rightDerivedPlus m).obj X :=
  G'.homologyIsoRightDerivedFunctorPlusOfRightAcyclic N hN m ≪≫
    (DerivedCategory.Plus.homologyFunctor M' m).mapIso (G'.rightDerivedFunctorPlus.mapIso ξ).symm

/-- The comparison `r_ℳ Rᵐ G'(X) ≅ Rᵐ G(r_𝒜 X)` of an exact restriction: the derived homology
comparison of `r_ℳ`, the comparison `RG' ⋙ r_ℳ ≅ r_𝒜 ⋙ RG` and `r_𝒜(X[0]) ≅ (r_𝒜 X)[0]`. -/
def rightDerivedPlusRestrictionIso (e : G' ⋙ rM ≅ rA ⋙ G)
    (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) (X : A') (m : ℤ) :
    rM.obj ((G'.rightDerivedPlus m).obj X) ≅ (G.rightDerivedPlus m).obj (rA.obj X) :=
  ((Stacks.DerivedFunctor.derivedHomologyIso rM m).app
      (DerivedCategory.Plus.ι.obj (G'.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A' 0).obj X)))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor M m).mapIso
      ((rightDerivedRestrictionIso G' G rA rM e hac).app
          ((DerivedCategory.Plus.singleFunctor A' 0).obj X) ≪≫
        G.rightDerivedFunctorPlus.mapIso (rA.mapDerivedCategoryPlusObjSingleIso X))

/-- The diagram chase behind `rightDerivedPlusRestrictionIso_resolution`, on abstract morphisms. -/
private lemma resolution_chase {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] (r : C ⥤ D) (H : E ⥤ D) (R : F ⥤ E)
    {x0 y1 z1 : C} {W0 W1 : D} {E0 E1 : E} {F0 F1 F2 F3 : F}
    (ac' : x0 ⟶ y1) (xi : y1 ⟶ z1) (j1 : r.obj y1 ⟶ H.obj E0) (j2 : r.obj z1 ⟶ H.obj E1)
    (gE : E0 ⟶ E1) (θs : E1 ⟶ R.obj F1) (θN : E0 ⟶ R.obj F0) (x : F0 ⟶ F1) (s0 : F1 ⟶ F2)
    (q0 : F3 ⟶ F0) (c : r.obj x0 ⟶ W0) (hm : W0 ⟶ W1) (acG : W1 ⟶ H.obj (R.obj F3))
    (hn : r.map xi ≫ j2 = j1 ≫ H.map gE) (hθ : gE ≫ θs = θN ≫ R.map x)
    (hG : r.map ac' ≫ j1 ≫ H.map θN = c ≫ hm ≫ acG ≫ H.map (R.map q0)) :
    r.map (ac' ≫ xi) ≫ j2 ≫ H.map (θs ≫ R.map s0) =
      c ≫ hm ≫ acG ≫ H.map (R.map ((q0 ≫ x) ≫ s0)) := by
  rw [r.map_comp, Category.assoc, reassoc_of% hn, ← H.map_comp, ← Category.assoc gE, hθ,
    Category.assoc, H.map_comp, reassoc_of% hG]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The resolution computation of `Rᵐ G'(X)` commutes with exact restriction functors**: read
through `rightDerivedPlusRestrictionIso`, the identification `Hᵐ(G' N) ≅ Rᵐ G'(X)` of an acyclic
resolution `ξ : X[0] ≅ N` is the identification `Hᵐ(G(r_𝒜 N)) ≅ Rᵐ G(r_𝒜 X)` of the restricted
resolution, after `r_ℳ(Hᵐ(G' N)) ≅ Hᵐ(r_ℳ(G' N)) ≅ Hᵐ(G(r_𝒜 N))`. -/
theorem rightDerivedPlusRestrictionIso_resolution
    (e : G' ⋙ rM ≅ rA ⋙ G) (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) {X : A'}
    (N : CochainComplex.Plus A') (hN : ∀ n, G'.rightAcyclic (N.obj.X n))
    (hN' : ∀ n, G.rightAcyclic ((rA.mapCochainComplexPlus.obj N).obj.X n))
    (ξ : (DerivedCategory.Plus.singleFunctor A' 0).obj X ≅ DerivedCategory.Plus.Q.obj N) (m : ℤ) :
    rM.map (G'.homologyIsoRightDerivedPlusOfResolution N hN ξ m).hom ≫
        (rightDerivedPlusRestrictionIso G' G rA rM e hac X m).hom =
      (Stacks.DerivedFunctor.complexHomologyIso rM (ComplexShape.up ℤ) m).inv.app
          ((G'.mapHomologicalComplex _).obj N.obj) ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app N.obj) m ≫
        (G.homologyIsoRightDerivedPlusOfResolution (rA.mapCochainComplexPlus.obj N) hN'
          ((rA.mapDerivedCategoryPlusObjSingleIso X).symm ≪≫ rA.mapDerivedCategoryPlus.mapIso ξ ≪≫
            (mapDerivedCategoryPlusQIso rA).app N) m).hom := by
  have hG :=
    homologyIsoRightDerivedFunctorPlusOfRightAcyclic_restriction G' G rA rM e hac N hN hN' m
  have hn := (Stacks.DerivedFunctor.derivedHomologyIso rM m).inv.naturality
    (DerivedCategory.Plus.ι.map (G'.rightDerivedFunctorPlus.map ξ.inv))
  have hθ := (rightDerivedRestrictionIso G' G rA rM e hac).hom.naturality ξ.inv
  have e3 : (G'.homologyIsoRightDerivedPlusOfResolution N hN ξ m).hom =
      (G'.homologyIsoRightDerivedFunctorPlusOfRightAcyclic N hN m).hom ≫
        (DerivedCategory.Plus.homologyFunctor M' m).map (G'.rightDerivedFunctorPlus.map ξ.inv) :=
    rfl
  have e4 : (rightDerivedPlusRestrictionIso G' G rA rM e hac X m).hom =
      (Stacks.DerivedFunctor.derivedHomologyIso rM m).inv.app
          (DerivedCategory.Plus.ι.obj (G'.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor A' 0).obj X))) ≫
        (DerivedCategory.Plus.homologyFunctor M m).map
          ((rightDerivedRestrictionIso G' G rA rM e hac).hom.app
              ((DerivedCategory.Plus.singleFunctor A' 0).obj X) ≫
            G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusObjSingleIso X).hom) := rfl
  have e5 : (G.homologyIsoRightDerivedPlusOfResolution (rA.mapCochainComplexPlus.obj N) hN'
      ((rA.mapDerivedCategoryPlusObjSingleIso X).symm ≪≫ rA.mapDerivedCategoryPlus.mapIso ξ ≪≫
        (mapDerivedCategoryPlusQIso rA).app N) m).hom =
      (G.homologyIsoRightDerivedFunctorPlusOfRightAcyclic
          (rA.mapCochainComplexPlus.obj N) hN' m).hom ≫
        (DerivedCategory.Plus.homologyFunctor M m).map (G.rightDerivedFunctorPlus.map
          (((mapDerivedCategoryPlusQIso rA).inv.app N ≫ rA.mapDerivedCategoryPlus.map ξ.inv) ≫
            (rA.mapDerivedCategoryPlusObjSingleIso X).hom)) := rfl
  rw [e3, e4, e5]
  exact resolution_chase rM (DerivedCategory.Plus.homologyFunctor M m) G.rightDerivedFunctorPlus
    _ _ _ _ _ _ _ _ (rA.mapDerivedCategoryPlusObjSingleIso X).hom _ _ _ _ hn hθ hG

omit [EnoughInjectives A] [rA.Additive] [PreservesFiniteLimits rA] [PreservesFiniteColimits rA] in
/-- The diagram chase behind `homologyIsoRightDerivedPlusOfResolution_hom_naturality`. -/
private lemma resolution_naturality_chase {D E F : Type*} [Category* D] [Category* E]
    [Category* F] (H : E ⥤ D) (R : F ⥤ E) {W W' : D} {F0 F1 F2 F3 : F}
    (a : W ⟶ W') (acy : W ⟶ H.obj (R.obj F0)) (acy' : W' ⟶ H.obj (R.obj F1)) (q : F0 ⟶ F1)
    (x : F0 ⟶ F2) (x' : F1 ⟶ F3) (s : F2 ⟶ F3)
    (hacy : a ≫ acy' = acy ≫ H.map (R.map q)) (hx : q ≫ x' = x ≫ s) :
    a ≫ acy' ≫ H.map (R.map x') = (acy ≫ H.map (R.map x)) ≫ H.map (R.map s) := by
  rw [reassoc_of% hacy, ← H.map_comp, ← R.map_comp, hx, R.map_comp, H.map_comp, Category.assoc]

omit [EnoughInjectives A] [EnoughInjectives M'] [rA.Additive] [PreservesFiniteLimits rA]
  [PreservesFiniteColimits rA] in
/-- **The resolution computation of `Rᵐ G'(X)` is natural**: a morphism of acyclic resolutions
`g : N ⟶ N'` over `h : X ⟶ X'` induces `Rᵐ G'(h)` on cohomology. -/
theorem homologyIsoRightDerivedPlusOfResolution_hom_naturality {X X' : A'} (h : X ⟶ X')
    {N N' : CochainComplex.Plus A'} (g : N ⟶ N') (hN : ∀ n, G'.rightAcyclic (N.obj.X n))
    (hN' : ∀ n, G'.rightAcyclic (N'.obj.X n))
    (ξ : (DerivedCategory.Plus.singleFunctor A' 0).obj X ≅ DerivedCategory.Plus.Q.obj N)
    (ξ' : (DerivedCategory.Plus.singleFunctor A' 0).obj X' ≅ DerivedCategory.Plus.Q.obj N')
    (hξ : ξ.hom ≫ DerivedCategory.Plus.Q.map g =
      (DerivedCategory.Plus.singleFunctor A' 0).map h ≫ ξ'.hom) (m : ℤ) :
    HomologicalComplex.homologyMap ((G'.mapHomologicalComplex _).map g.hom) m ≫
        (G'.homologyIsoRightDerivedPlusOfResolution N' hN' ξ' m).hom =
      (G'.homologyIsoRightDerivedPlusOfResolution N hN ξ m).hom ≫
        (G'.rightDerivedPlus m).map h := by
  have hacy := G'.homologyIsoRightDerivedFunctorPlusOfRightAcyclic_hom_naturality g hN hN' m
  have hx : DerivedCategory.Plus.Q.map g ≫ ξ'.inv =
      ξ.inv ≫ (DerivedCategory.Plus.singleFunctor A' 0).map h := by
    refine (Iso.eq_inv_comp ξ).2 ?_
    rw [← Category.assoc, hξ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact resolution_naturality_chase (DerivedCategory.Plus.homologyFunctor M' m)
    G'.rightDerivedFunctorPlus _ _ _ _ _ _ _ hacy hx

end CategoryTheory.Functor

end
