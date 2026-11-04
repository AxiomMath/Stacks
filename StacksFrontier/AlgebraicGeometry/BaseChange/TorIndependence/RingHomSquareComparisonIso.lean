module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapMate
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapSquareIso
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingHomSquareComparisonModel
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineFamily

/-!
# The comparison of Stacks 065Z under an isomorphism of squares

For two pushout squares of commutative rings related by isomorphisms of their four corners, the
derived base change comparison of [Stacks, Tag 065Z] of the first square at `K`, followed by a
morphism `φ`, is invertible exactly when the comparison of the second square at `K ⊗ᴸ_A A₁`,
followed by the induced morphism, is. This holds both at the standard and at the locally small
model of the derived category.

## Main results

* `RingTheory.TorIndependence.isIso_squareDerivedComparison_comp_iff_of_bijective`: the
  comparison is invariant under bijections of the four corners of a tensor product square.
* `RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_iff_of_iso`: the comparison at
  the standard model is invariant under an isomorphism of pushout squares.
* `RingTheory.TorIndependence.totalDerivedExtensionScalarsComp_hom_app_modelIso`: the model
  comparison of derived extension of scalars is compatible with the composition isomorphisms.
* `RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff_of_iso`: the comparison at
  the locally small model is invariant under an isomorphism of pushout squares.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace RingTheory.TorIndependence

section ModelComp

/-- A diagram chase in four categories: given the commutations `h1`, `hn`, `h2`, `h4`, `h3`, `h5`
and `hG`, the composite `Lψ.map k₁ ≫ k₂ ≫ G.map d ≫ k₃ ≫ a` equals `dL ≫ a`. -/
theorem modelComp_chase {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁] [Category* D₀]
    [Category* D₁] (G : C₁ ⥤ D₁) (GA : C₀ ⥤ D₀) (Lψ : D₀ ⥤ D₁) (Sψ : C₀ ⥤ C₁)
    {X₀ : D₀} {Y₀ Z₀' : C₀} {W' T V' : C₁} {U : D₁}
    {k₁ : X₀ ⟶ GA.obj Y₀} {αφ : X₀ ⟶ GA.obj Z₀'} {αSφ : Y₀ ⟶ Z₀'}
    {k₂ : Lψ.obj (GA.obj Y₀) ⟶ G.obj (Sψ.obj Y₀)} {k₂' : Lψ.obj (GA.obj Z₀') ⟶ G.obj (Sψ.obj Z₀')}
    {αψ : Lψ.obj (GA.obj Z₀') ⟶ G.obj W'} {αSψ : Sψ.obj Z₀' ⟶ W'} {d : Sψ.obj Y₀ ⟶ T}
    {αSψφ : T ⟶ V'} {eS : W' ⟶ V'} {k₃ : G.obj T ⟶ U} {a : U ⟶ G.obj V'}
    {dL : Lψ.obj X₀ ⟶ U} {eL : G.obj W' ⟶ G.obj V'}
    (h1 : k₁ ≫ GA.map αSφ = αφ)
    (hn : k₂ ≫ G.map (Sψ.map αSφ) = Lψ.map (GA.map αSφ) ≫ k₂')
    (h2 : k₂' ≫ G.map αSψ = αψ) (h4 : Sψ.map αSφ ≫ αSψ ≫ eS = d ≫ αSψφ)
    (h3 : k₃ ≫ a = G.map αSψφ) (h5 : Lψ.map αφ ≫ αψ ≫ eL = dL ≫ a) (hG : G.map eS = eL) :
    Lψ.map k₁ ≫ k₂ ≫ G.map d ≫ k₃ ≫ a = dL ≫ a := by
  rw [h3, ← G.map_comp, ← h4, G.map_comp, G.map_comp, reassoc_of% hn, reassoc_of% h2, hG,
    ← Lψ.map_comp_assoc, h1, h5]

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The model comparison of derived extension of scalars is compatible with the composition
isomorphisms at the standard and at the locally small model. -/
theorem totalDerivedExtensionScalarsComp_hom_app_modelIso (φ : R →+* A) (ψ : A →+* B)
    (M : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        ψ).functor.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
          φ).inv.app M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso ψ).inv.app
        ((dext φ).obj M) ≫
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor.map
        ((dcomp φ ψ).hom.app M) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
        (ψ.comp φ)).hom.app M =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u, u, u, u}
      φ ψ).hom.app
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor.obj M) := by
  have hLD := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
    (ψ.comp φ)).isLeftDerived
  have hT := StacksDraft.DerivedModel.isLeftDerivedFunctor_comp_isEquivalence
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (G := (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor)
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      (ψ.comp φ)).comparison
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R)))
  have e := Functor.leftDerived_ext
    ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        (ψ.comp φ)).functor)
    (StacksDraft.DerivedModel.transportLeftDerivedCounit
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        (ψ.comp φ)).comparison
      (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R))))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    _ (Functor.whiskerRight
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso φ).inv
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
          ψ).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (dext φ)
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso ψ).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (dcomp φ ψ).hom
        (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso (ψ.comp φ)).hom)
    ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u, u, u, u}
        φ ψ).hom) ?_
  · have := congrArg (fun t => NatTrans.app t M) e
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at this
    exact this
  · ext P
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      StacksDraft.DerivedModel.transportLeftDerivedCounit, eqToIso.hom, eqToHom_app,
      Category.assoc]
    have h1 := totalDerivedExtensionScalarsModelIso_hom_app_comparison' φ P
    have h2 := totalDerivedExtensionScalarsModelIso_hom_app_comparison' ψ
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    have h3 := totalDerivedExtensionScalarsModelIso_hom_app_comparison' (ψ.comp φ) P
    have h4 := @CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison
      R A B _ _ _ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) φ ψ P
    have h5 :=
      CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison.{u, u, u,
        u, u} φ ψ P
    have hE : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
          (ψ.comp φ)).functor.map (eqToHom (Functor.congr_obj
            (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R)) P)) =
        𝟙 _ := by
      rw [eqToHom_map]
      rfl
    refine modelComp_chase (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        ψ).functor
      (dext ψ)
      ((congrArg (_ ≫ ·) h1).symm.trans (Iso.inv_hom_id_app_assoc _ _ _))
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
        ψ).inv.naturality _).symm
      ((congrArg (_ ≫ ·) h2).symm.trans (Iso.inv_hom_id_app_assoc _ _ _)) h4 ?_ ?_ rfl
    · exact (congrArg (_ ≫ ·) ((congrArg (· ≫ _) hE).trans (Category.id_comp _))).trans h3
    · exact h5.trans (congrArg (_ ≫ ·) ((congrArg (· ≫ _) hE).trans (Category.id_comp _)).symm)

end ModelComp

attribute [local instance 10000] HasDerivedCategory.standard

section SquareIso

variable {R A R' A' R₁ A₁ R₁' A₁' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing R₁] [CommRing A₁] [CommRing R₁'] [CommRing A₁']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁] [Algebra R₁ R₁'] [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R₁'] [Algebra A' A₁']
  [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [Algebra R R₁'] [IsScalarTower R R' R₁'] [IsScalarTower R R₁ R₁']
  [Algebra A A₁'] [IsScalarTower A A' A₁'] [IsScalarTower A A₁ A₁']
  [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']

/-- If the four ring maps `R → R₁`, `A → A₁`, `R' → R₁'`, `A' → A₁'` are bijective and the maps
`R' ⊗_R A → A'` and `R₁' ⊗_{R₁} A₁ → A₁'` are bijective, the derived base change comparison of the
first square at `K` followed by `φ` is invertible exactly when the comparison of the second square
at `K ⊗ᴸ_A A₁` followed by the induced morphism is. -/
theorem isIso_squareDerivedComparison_comp_iff_of_bijective
    (hR : Function.Bijective (algebraMap R R₁)) (hA : Function.Bijective (algebraMap A A₁))
    (hR' : Function.Bijective (algebraMap R' R₁'))
    (hA' : Function.Bijective (algebraMap A' A₁'))
    (hT : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    (hT₁ : Function.Bijective
      (baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')))
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') :
    IsIso ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ) ↔
      IsIso ((squareDerivedComparison (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')).app
          ((dext (algebraMap A A₁)).obj K) ≫
        (ModuleCat.restrictScalars (algebraMap R₁' A₁')).mapDerivedCategory.map
          (extendScalarsBaseChangeHom K K' φ)) := by
  rw [isIso_squareDerivedComparison_comp_iff, isIso_squareDerivedComparison_comp_iff]
  refine forall_congr' fun n => ?_
  rw [← isIso_ringBaseChangeCohomologyMap_iff hT, ← isIso_ringBaseChangeCohomologyMap_iff hT₁]
  exact isIso_ringBaseChangeCohomologyMap_iff_of_bijective hR hA hR' hA' K K' φ n

end SquareIso

section CommRingCatSquareIso

variable {R A R' A' R₁ A₁ R₁' A₁' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'}
  {d : R' ⟶ A'} {a₁ : R₁ ⟶ A₁} {b₁ : R₁ ⟶ R₁'} {c₁ : A₁ ⟶ A₁'} {d₁ : R₁' ⟶ A₁'}

/-- `isIso_squareDerivedComparison_comp_iff_of_bijective` for pushout squares of commutative
rings related by isomorphisms. -/
theorem isIso_ringHomSquareComparison_comp_iff_of_iso (hpo : IsPushout a b c d)
    (hpo₁ : IsPushout a₁ b₁ c₁ d₁) (sq : c.hom.comp a.hom = d.hom.comp b.hom)
    (sq₁ : c₁.hom.comp a₁.hom = d₁.hom.comp b₁.hom) (eR : R ≅ R₁) (eA : A ≅ A₁) (eR' : R' ≅ R₁')
    (eA' : A' ≅ A₁') (wa : a ≫ eA.hom = eR.hom ≫ a₁) (wb : b ≫ eR'.hom = eR.hom ≫ b₁)
    (wc : c ≫ eA'.hom = eA.hom ≫ c₁) (wd : d ≫ eA'.hom = eR'.hom ≫ d₁)
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext c.hom).obj K ⟶ K') :
    IsIso ((ringHomSquareComparison a.hom b.hom c.hom d.hom sq).app K ≫
        (ModuleCat.restrictScalars d.hom).mapDerivedCategory.map φ) ↔
      IsIso ((ringHomSquareComparison a₁.hom b₁.hom c₁.hom d₁.hom sq₁).app
          ((dext eA.hom.hom).obj K) ≫
        (ModuleCat.restrictScalars d₁.hom).mapDerivedCategory.map
          ((dcomp eA.hom.hom c₁.hom).hom.app K ≫
            eqToHom (congrArg (fun t => (dext t).obj K)
              (congrArg CommRingCat.Hom.hom wc.symm)) ≫
            (dcomp c.hom eA'.hom.hom).inv.app K ≫ (dext eA'.hom.hom).map φ)) := by
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  let := c.hom.toAlgebra
  let := d.hom.toAlgebra
  let := (c.hom.comp a.hom).toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' sq
  let := a₁.hom.toAlgebra
  let := b₁.hom.toAlgebra
  let := c₁.hom.toAlgebra
  let := d₁.hom.toAlgebra
  let := (c₁.hom.comp a₁.hom).toAlgebra
  have : IsScalarTower R₁ A₁ A₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R₁ R₁' A₁' := IsScalarTower.of_algebraMap_eq' sq₁
  let := eR.hom.hom.toAlgebra
  let := eA.hom.hom.toAlgebra
  let := eR'.hom.hom.toAlgebra
  let := eA'.hom.hom.toAlgebra
  let := (eA.hom.hom.comp a.hom).toAlgebra
  have : IsScalarTower R A A₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R₁ A₁ := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom wa)
  let := (eR'.hom.hom.comp b.hom).toAlgebra
  have : IsScalarTower R R' R₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R₁ R₁' := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom wb)
  let := (eA'.hom.hom.comp c.hom).toAlgebra
  have : IsScalarTower A A' A₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A A₁ A₁' := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom wc)
  let := (eA'.hom.hom.comp d.hom).toAlgebra
  have : IsScalarTower R' A' A₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R' R₁' A₁' := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom wd)
  have : Algebra.IsPushout R A R' A' := (CommRingCat.isPushout_iff_isPushout).mp hpo
  have : Algebra.IsPushout R₁ A₁ R₁' A₁' := (CommRingCat.isPushout_iff_isPushout).mp hpo₁
  exact isIso_squareDerivedComparison_comp_iff_of_bijective
    (ConcreteCategory.bijective_of_isIso eR.hom) (ConcreteCategory.bijective_of_isIso eA.hom)
    (ConcreteCategory.bijective_of_isIso eR'.hom) (ConcreteCategory.bijective_of_isIso eA'.hom)
    bijective_baseChangeTensorRingMap_of_isPushout bijective_baseChangeTensorRingMap_of_isPushout
    K K' φ

end CommRingCatSquareIso

end RingTheory.TorIndependence

namespace RingTheory.TorIndependence

section LSSquareIso

open CochainComplex.DerivedExtensionScalars in
/-- Transport of the model comparison of derived extension of scalars along an equality of ring
maps. -/
theorem totalDerivedExtensionScalarsModelIso_inv_app_eqToHom {A B : Type u} [CommRing A]
    [CommRing B] {t₁ t₂ : A →+* B} (h : t₁ = t₂)
    (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) :
    (totalDerivedExtensionScalarsModelIso t₁).inv.app M ≫
        (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor.map
          (eqToHom (congrArg (fun t => (dext t).obj M) h)) =
      eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u, u, u} t).functor.obj
          ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M)) h) ≫
        (totalDerivedExtensionScalarsModelIso t₂).inv.app M := by
  subst h
  exact (congrArg (_ ≫ ·) (((Stacks.Injectives.grothendieckModelEquiv.{u}
    (ModuleCat.{u} B)).functor.congr_map (eqToHom_refl _ _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans
    ((Category.comp_id _).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans
      (Category.id_comp _)).symm)

/-- A diagram chase in five categories: given the commutations `h₁`, `hT`, `h₂`, `hN` and the
retractions `hm₁`, `hs`, `hn₂`, `hl`, the composite
`Lc₁.map f ≫ k ≫ G.map (s₁ ≫ q ≫ s₂ ≫ Se.map x)` equals
`(l₁ ≫ E ≫ l₂ ≫ Le.map (kc ≫ G'.map x)) ≫ f'`. -/
theorem modelSquareIso_chase {C₁ C' D₀ D' D₁ : Type*} [Category* C₁] [Category* C']
    [Category* D₀] [Category* D'] [Category* D₁]
    (G : C₁ ⥤ D₁) (G' : C' ⥤ D') (Lc₁ : D₀ ⥤ D₁) (Le : D' ⥤ D₁) (Se : C' ⥤ C₁)
    {X₀ Y₀ : D₀} {P₁ P₂ P₃ : C₁} {P₄ P₅ : C'} {Q₁ Q₂ : D₁} {Q₃ : D'}
    (f : X₀ ⟶ Y₀) (k : Lc₁.obj Y₀ ⟶ G.obj P₁) (s₁ : P₁ ⟶ P₂) (q : P₂ ⟶ P₃) (s₂ : P₃ ⟶ Se.obj P₄)
    (s₂' : Se.obj P₄ ⟶ P₃) (x : P₄ ⟶ P₅) (m₁ : G.obj P₂ ⟶ Q₁) (n₁ : Q₁ ⟶ G.obj P₂)
    (n₂ : Q₂ ⟶ G.obj P₃) (m₂ : G.obj P₃ ⟶ Q₂) (l₁ : Lc₁.obj X₀ ⟶ Q₁) (E : Q₁ ⟶ Q₂)
    (l₂ : Q₂ ⟶ Le.obj Q₃) (l₂' : Le.obj Q₃ ⟶ Q₂) (kc : Q₃ ⟶ G'.obj P₄)
    (k' : Le.obj (G'.obj P₄) ⟶ G.obj (Se.obj P₄)) (f' : Le.obj (G'.obj P₅) ⟶ G.obj (Se.obj P₅))
    (h₁ : Lc₁.map f ≫ k ≫ G.map s₁ ≫ m₁ = l₁) (hm₁ : m₁ ≫ n₁ = 𝟙 _)
    (hT : n₁ ≫ G.map q = E ≫ n₂) (h₂ : Le.map kc ≫ k' ≫ G.map s₂' ≫ m₂ = l₂')
    (hs : s₂' ≫ s₂ = 𝟙 _) (hn₂ : m₂ ≫ n₂ = 𝟙 _) (hl : l₂ ≫ l₂' = 𝟙 _)
    (hN : k' ≫ G.map (Se.map x) = Le.map (G'.map x) ≫ f') :
    Lc₁.map f ≫ k ≫ G.map (s₁ ≫ q ≫ s₂ ≫ Se.map x) =
      (l₁ ≫ E ≫ l₂ ≫ Le.map (kc ≫ G'.map x)) ≫ f' := by
  have e₁ : Lc₁.map f ≫ k ≫ G.map s₁ = l₁ ≫ n₁ := by
    rw [← h₁]; simp only [Category.assoc, hm₁, Category.comp_id]
  have e₂ : n₂ ≫ G.map s₂ = l₂ ≫ Le.map kc ≫ k' := by
    calc n₂ ≫ G.map s₂ = l₂ ≫ l₂' ≫ n₂ ≫ G.map s₂ := by rw [reassoc_of% hl]
      _ = l₂ ≫ Le.map kc ≫ k' := by
        rw [← h₂]
        simp only [Category.assoc, reassoc_of% hn₂, ← G.map_comp, hs, CategoryTheory.Functor.map_id,
          Category.comp_id]
  simp only [G.map_comp, Le.map_comp, Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% hT, reassoc_of% e₂, hN]

/-- Invertibility of a component of a natural transformation followed by the image of a morphism
is invariant under isomorphisms of the source and of the target. -/
theorem isIso_app_comp_map_iff_of_iso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (τ : F ⟶ G ⋙ H) {X Y : C} (ι : Y ≅ X) {Z Z' : D}
    (ψ : G.obj Y ⟶ Z) (φ : G.obj X ⟶ Z') (e : Z ≅ Z') (h : G.map ι.hom ≫ φ = ψ ≫ e.hom) :
    IsIso (τ.app Y ≫ H.map ψ) ↔ IsIso (τ.app X ≫ H.map φ) := by
  refine Iff.trans ?_ (Stacks.Generic.isIso_app_comp_map_comp_iff τ ι φ)
  rw [h, H.map_comp, ← Category.assoc]
  exact (isIso_comp_right_iff _ (H.map e.hom)).symm

variable {R A R' A' R₁ A₁ R₁' A₁' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'}
  {d : R' ⟶ A'} {a₁ : R₁ ⟶ A₁} {b₁ : R₁ ⟶ R₁'} {c₁ : A₁ ⟶ A₁'} {d₁ : R₁' ⟶ A₁'}

open CochainComplex.DerivedExtensionScalars in
/-- For pushout squares of commutative rings related by isomorphisms of their four corners, `M`,
`M'` at the standard model and any `ψ` at the locally small one, the derived base change
comparison at the locally small model of the first square followed by `ψ` is invertible exactly
when the comparison of the second square at `M ⊗ᴸ_A A₁` followed by the induced morphism is. -/
theorem isIso_ringHomSquareComparisonLS_comp_iff_of_iso (hpo : IsPushout a b c d)
    (hpo₁ : IsPushout a₁ b₁ c₁ d₁) (sq : c.hom.comp a.hom = d.hom.comp b.hom)
    (sq₁ : c₁.hom.comp a₁.hom = d₁.hom.comp b₁.hom) (eR : R ≅ R₁) (eA : A ≅ A₁) (eR' : R' ≅ R₁')
    (eA' : A' ≅ A₁') (wa : a ≫ eA.hom = eR.hom ≫ a₁) (wb : b ≫ eR'.hom = eR.hom ≫ b₁)
    (wc : c ≫ eA'.hom = eA.hom ≫ c₁) (wd : d ≫ eA'.hom = eR'.hom ≫ d₁)
    (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (M' : @DerivedCategory (ModuleCat.{u} A') _ _ (HasDerivedCategory.standard _))
    (ψ : (totalDerivedExtensionScalars.{u, u, u, u, u} c.hom).functor.obj
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) ⟶
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.obj M') :
    IsIso ((ringHomSquareComparisonLS a.hom b.hom c.hom d.hom sq).app
          ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) ≫
        (ModuleCat.restrictScalars.{u} d.hom).mapDerivedCategory.map ψ) ↔
      IsIso ((ringHomSquareComparisonLS a₁.hom b₁.hom c₁.hom d₁.hom sq₁).app
          ((totalDerivedExtensionScalars.{u, u, u, u, u} eA.hom.hom).functor.obj
            ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M)) ≫
        (ModuleCat.restrictScalars.{u} d₁.hom).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u, u, u, u} eA.hom.hom c₁.hom).hom.app
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) ≫
            eqToHom (congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u, u, u} t).functor.obj
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M))
              (congrArg CommRingCat.Hom.hom wc.symm)) ≫
            (totalDerivedExtensionScalarsComp.{u, u, u, u, u} c.hom eA'.hom.hom).inv.app
              ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) ≫
            (totalDerivedExtensionScalars.{u, u, u, u, u} eA'.hom.hom).functor.map ψ)) := by
  obtain ⟨x, rfl⟩ : ∃ x : (dext c.hom).obj M ⟶ M',
      (totalDerivedExtensionScalarsModelIso c.hom).inv.app M ≫
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.map x = ψ :=
    ⟨(Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.preimage
      ((totalDerivedExtensionScalarsModelIso c.hom).hom.app M ≫ ψ), by
        exact (congrArg ((totalDerivedExtensionScalarsModelIso c.hom).inv.app M ≫ ·)
          (Functor.map_preimage (Stacks.Injectives.grothendieckModelEquiv.{u}
            (ModuleCat.{u} A')).functor _)).trans
          (Iso.inv_hom_id_app_assoc (totalDerivedExtensionScalarsModelIso c.hom) M ψ)⟩
  refine (isIso_ringHomSquareComparisonLS_comp_iff a.hom b.hom c.hom d.hom sq M M' x).trans
    ((isIso_ringHomSquareComparison_comp_iff_of_iso hpo hpo₁ sq sq₁ eR eA eR' eA' wa wb wc wd
      M M' x).trans ((isIso_ringHomSquareComparisonLS_comp_iff a₁.hom b₁.hom c₁.hom d₁.hom sq₁
        _ _ _).symm.trans ?_))
  refine (isIso_app_comp_map_iff_of_iso
    (ringHomSquareComparisonLS a₁.hom b₁.hom c₁.hom d₁.hom sq₁)
    ((totalDerivedExtensionScalarsModelIso eA.hom.hom).app M).symm _ _
    ((totalDerivedExtensionScalarsModelIso eA'.hom.hom).app M').symm
    (modelSquareIso_chase (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A₁')).functor
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor
      (totalDerivedExtensionScalars.{u, u, u, u, u} c₁.hom).functor
      (totalDerivedExtensionScalars.{u, u, u, u, u} eA'.hom.hom).functor (dext eA'.hom.hom)
      _ _ _ _ _ ((dcomp c.hom eA'.hom.hom).hom.app M) x _
      ((totalDerivedExtensionScalarsModelIso (c₁.hom.comp eA.hom.hom)).inv.app M)
      _ ((totalDerivedExtensionScalarsModelIso (eA'.hom.hom.comp c.hom)).hom.app M) _ _ _
      ((totalDerivedExtensionScalarsComp.{u, u, u, u, u} c.hom eA'.hom.hom).hom.app
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M))
      _ _ _
      (totalDerivedExtensionScalarsComp_hom_app_modelIso eA.hom.hom c₁.hom M)
      (Iso.hom_inv_id_app _ _)
      (totalDerivedExtensionScalarsModelIso_inv_app_eqToHom
        (congrArg CommRingCat.Hom.hom wc.symm) M)
      (totalDerivedExtensionScalarsComp_hom_app_modelIso c.hom eA'.hom.hom M)
      (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)
      ((totalDerivedExtensionScalarsModelIso eA'.hom.hom).inv.naturality x).symm)).symm

end LSSquareIso

end RingTheory.TorIndependence
