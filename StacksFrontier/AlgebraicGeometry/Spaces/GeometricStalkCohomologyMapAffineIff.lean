module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineDerived
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsCentral
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp

/-!
# The pointwise base-change map of Equation 0DKF on affine representables

Let `b : P ⟶ U` be a morphism of affine objects of the big fppf site over `S`, with rings of
global functions `A₀ → A₀'`, and let `x̄'` be a geometric point of `yoneda.obj P` with image
`x̄` in `yoneda.obj U`.  The geometric stalks `𝒪_{x̄}` and `𝒪_{x̄'}` are flat over `A₀` and `A₀'`,
and the stalk of the associated module of a complex is its derived base change.  This file
proves that the map of Equation 0DKF at `x̄'` attached to `K = Φ(K₀)`, `K' = Φ(K₀')` and
`φ = β ≫ Φ(φ₀)` is invertible exactly when the ring-level map of Stacks 0DJ7 for the
square `A₀ → A₀', 𝒪_{x̄} → 𝒪_{x̄'}` at `K₀ ⊗ᴸ 𝒪_{x̄}`, `K₀' ⊗ᴸ 𝒪_{x̄'}` is.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineStalkPathLeft`,
  `AlgebraicGeometry.Space.representedAffineStalkPathRight`: the two module-level
  identifications `𝒪_{x̄'} ⊗_{𝒪_{x̄}} (M^~)_{x̄} ≅ 𝒪_{x̄'} ⊗_{A₀'} (A₀' ⊗_{A₀} M)`, through
  `g^*(M^~)` and through the stalk ring maps.

## Main results

* `AlgebraicGeometry.Space.exists_isUnit_representedAffineStalkPath`: the two identifications
  differ by multiplication by a unit of `𝒪_{x̄'}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace ModuleCat.ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- **A natural automorphism of a functor isomorphic to extension of scalars is multiplication
by a unit.** -/
theorem exists_isUnit_hom_app_eq_smul {F : ModuleCat.{u} A ⥤ ModuleCat.{u} B}
    (e : ModuleCat.extendScalars.{u, u, u} f ≅ F) (θ : F ≅ F) :
    ∃ c : B, IsUnit c ∧ ∀ M, θ.hom.app M = c • 𝟙 (F.obj M) := by
  have key : ∀ θ' : F ⟶ F, ∃ c : B, ∀ M, θ'.app M = c • 𝟙 (F.obj M) := by
    intro θ'
    obtain ⟨c, hc⟩ := natTrans_app_eq_smul
      (P := (⊤ : ObjectProperty (ModuleCat.{u} A))) trivial
      (Functor.whiskerLeft (⊤ : ObjectProperty _).ι (e.hom ≫ θ' ≫ e.inv))
    refine ⟨c, fun M => ?_⟩
    have h := hc ⟨M, trivial⟩
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app, ObjectProperty.ι_obj] at h
    simpa only [Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp] using
      congrArg (fun t => e.inv.app M ≫ t ≫ e.hom.app M) h
  obtain ⟨c, hc⟩ := key θ.hom
  obtain ⟨d, hd⟩ := key θ.inv
  refine ⟨c, IsUnit.of_mul_eq_one (b := d) ?_, hc⟩
  have h₁ := θ.inv_hom_id_app (ModuleCat.of A A)
  rw [hc, hd, Linear.smul_comp, Category.id_comp, smul_smul, mul_comm] at h₁
  have h₂ := congrArg (fun t => e.hom.app (ModuleCat.of A A) ≫ t ≫ e.inv.app (ModuleCat.of A A)) h₁
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.hom_inv_id_app] at h₂
  exact ModuleCat.ExtendScalars.eq_one_of_smul_id_eq_id (f := f) _ h₂

/-- Natural transformations of functors to modules which differ by a scalar induce maps of
complexes which differ by that scalar. -/
theorem mapHomologicalComplex_app_eq_smul {C : Type*} [Category* C] [Preadditive C]
    {F G : C ⥤ ModuleCat.{u} B} [F.Additive] [G.Additive] (α β : F ⟶ G) (c : B)
    (h : ∀ M, α.app M = c • β.app M) (M : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app M =
      c • (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app M := by
  ext n : 1
  simp [h]

end ModuleCat.ExtendScalars

namespace CochainComplex.DerivedExtensionScalars

section Comparison

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Transporting derived extension of scalars along an equality of ring maps is compatible with
the comparison to degreewise extension of scalars. -/
theorem totalDerivedExtensionScalars_eqToHom_comp_comparison {f f' : A →+* B} (h : f = f')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    eqToHom (congrArg (fun φ : A →+* B =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj (DerivedCategory.Q.obj M)) h) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f').comparison.app M =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).comparison.app M ≫
      DerivedCategory.Q.map (eqToHom (congrArg (fun φ : A →+* B =>
        ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
          h)) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact (congrArg (_ ≫ ·) (DerivedCategory.Q.map_id _)).trans (Category.comp_id _) |>.symm

end Comparison

end CochainComplex.DerivedExtensionScalars

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {P U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  (g : P ⟶ U) (x : GeometricPoint B S hS (yoneda.obj P))

/-- The square of rings `A₀ → A₀'`, `A₀ → 𝒪_{g(x̄')}`, `A₀' → 𝒪_{x̄'}`, `𝒪_{g(x̄')} → 𝒪_{x̄'}`
commutes. -/
theorem representedAffineStalkRingHom_square :
    (stalkStructureMap B S hS (representedSpaceMap B S hS g) x).hom.comp
        (representedAffineGlobalStalkRingHom B S hS U
          (geometricPointMap (representedSpaceMap B S hS g).hom x)) =
      (representedAffineGlobalStalkRingHom B S hS P x).comp
        (representedAffineCommRingCatHom B S hS g).hom :=
  RingHom.ext (stalkStructureMap_representedAffineStalkRingHom B S hS g x)

/-- The identification `𝒪_{x̄'} ⊗_{𝒪_{x̄}} (M^~)_{x̄} ≅ 𝒪_{x̄'} ⊗_{A₀'} (A₀' ⊗_{A₀} M)` through the
stalk ring maps: `(M^~)_{x̄} ≅ 𝒪_{x̄} ⊗_{A₀} M` and the scalar tower of the square. -/
def representedAffineStalkPathRight :
    representedAffineStalk B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x) ⋙
        ModuleCat.extendScalars.{u, u, u}
          (stalkStructureMap B S hS (representedSpaceMap B S hS g) x).hom ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        ModuleCat.extendScalars.{u, u, u} (representedAffineGlobalStalkRingHom B S hS P x) :=
  Functor.isoWhiskerRight (representedAffineStalkIso B S hS U
      (geometricPointMap (representedSpaceMap B S hS g).hom x)).symm _ ≪≫
    (ModuleCat.extendScalarsComp _ _).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars.{u, u, u}
      (representedAffineStalkRingHom_square B S hS g x)) ≪≫
    ModuleCat.extendScalarsComp _ _

/-- The identification `𝒪_{x̄'} ⊗_{𝒪_{x̄}} (M^~)_{x̄} ≅ 𝒪_{x̄'} ⊗_{A₀'} (A₀' ⊗_{A₀} M)` through
the pullback: Stacks 05V5 at `x̄'`, `g^*(M^~) ≅ (A₀' ⊗_{A₀} M)^~`, and the stalk of an associated
module at `x̄'`. -/
def representedAffineStalkPathLeft :
    representedAffineStalk B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x) ⋙
        ModuleCat.extendScalars.{u, u, u}
          (stalkStructureMap B S hS (representedSpaceMap B S hS g) x).hom ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        ModuleCat.extendScalars.{u, u, u} (representedAffineGlobalStalkRingHom B S hS P x) :=
  Functor.isoWhiskerLeft
      (representedAffineStalk B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x))
      (eqToIso (congrArg ModuleCat.extendScalars.{u, u, u}
        (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived
          (representedSpaceMap B S hS g) x))) ≪≫
    (representedAffinePullbackStalkIso B S hS g x).symm ≪≫
    representedAffinePullbackStalkIso' B S hS g x ≪≫
    Functor.isoWhiskerLeft _ (representedAffineStalkIso B S hS P x).symm

/-- **The two identifications differ by a unit of `𝒪_{x̄'}`.** -/
theorem exists_isUnit_representedAffineStalkPath :
    ∃ c : geometricStalkRing B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x,
      IsUnit c ∧ ∀ M, (representedAffineStalkPathLeft B S hS g x).hom.app M =
        c • (representedAffineStalkPathRight B S hS g x).hom.app M := by
  obtain ⟨c, hc, h⟩ := ModuleCat.ExtendScalars.exists_isUnit_hom_app_eq_smul _
    (ModuleCat.extendScalarsComp (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineGlobalStalkRingHom B S hS P x))
    ((representedAffineStalkPathRight B S hS g x).symm ≪≫ representedAffineStalkPathLeft B S hS g x)
  refine ⟨c, hc, fun M => ?_⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.hom_inv_id_app_assoc,
    Linear.comp_smul, Category.comp_id] using
    congrArg (fun t => (representedAffineStalkPathRight B S hS g x).hom.app M ≫ t) (h M)

/-- If the two identifications differ by the scalar `c` on every module, the induced maps on
cochain complexes differ by `c`. -/
theorem representedAffineStalkPath_mapHomologicalComplex_eq_smul
    (c : geometricStalkRing B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x)
    (hc : ∀ M, (representedAffineStalkPathLeft B S hS g x).hom.app M =
        c • (representedAffineStalkPathRight B S hS g x).hom.app M)
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (NatTrans.mapHomologicalComplex (representedAffineStalkPathLeft B S hS g x).hom
        (ComplexShape.up ℤ)).app M =
      c • (NatTrans.mapHomologicalComplex (representedAffineStalkPathRight B S hS g x).hom
        (ComplexShape.up ℤ)).app M :=
  ModuleCat.ExtendScalars.mapHomologicalComplex_app_eq_smul _ _ c hc M

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The counit of the derived pullback-stalk comparison at `K` is the geometric stalk at `x̄'` of
the pullback comparison map at `K`. -/
theorem derivedPullbackGeometricStalkCounit_app
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ)) :
    (derivedPullbackGeometricStalkCounit (representedSpaceMap B S hS g) x).app K =
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((smallEtaleDerivedModulePullbackComparison B S hS
          (representedSpaceMap B S hS g)).app K) := by
  rw [derivedPullbackGeometricStalkCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Category.id_comp, Functor.whiskerRight_app]

/-- The geometric stalk at `x̄'` of the affine derived base change morphism at a complex `M`,
followed by the comparison, factors through the canonical factorizations, the pullback
comparison and the degreewise pullback of associated modules. -/
theorem geometricDerivedStalk_map_representedAffineDerivedBaseChangeIso
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj M) ≫
          (representedAffineDerivedAssociated B S hS P).map
            ((representedAffineDerivedExtension B S hS g).comparison.app M)) =
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
            ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M)) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
            ((representedAffineHomotopyAssociated B S hS U).obj M)) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          (DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g).hom.app M)) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((representedAffineDerivedAssociatedFactors B S hS P).inv.app
            (((ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) :=
  (congrArg (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩)
      x).map (representedAffineDerivedBaseChangeIso_hom_app_comparison B S hS g M)).trans
    (((geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩)
        x).map_comp _ _).trans (congrArg (_ ≫ ·)
      (((geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩)
          x).map_comp _ _).trans (congrArg (_ ≫ ·)
        ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩)
          x).map_comp _ _)))))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The derived pullback-stalk comparison at an object mapping to the class of a complex. -/
theorem derivedPullbackGeometricStalkMap_app_comp_map_comparison
    {Y : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))}
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ))
    (f : Y ⟶ DerivedCategory.Qh.obj K) :
    (derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g) x).app Y ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map f) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((smallEtaleDerivedModulePullbackComparison B S hS
            (representedSpaceMap B S hS g)).app K) =
      (geometricStalkDerivedExtension (representedSpaceMap B S hS g) x).functor.map
          ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
            (geometricPointMap (representedSpaceMap B S hS g).hom x)).map f) ≫
        (derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app K := by
  have hn := (derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g) x).naturality f
  have hf := derivedPullbackGeometricStalkMap_fac (representedSpaceMap B S hS g) x K
  rw [derivedPullbackGeometricStalkCounit_app] at hf
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn.symm, hf]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The class of the degreewise associated module, in the two spellings of the module category. -/
theorem representedAffineHomotopyAssociated_obj_eq
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineHomotopyAssociated B S hS U).obj M =
      (HomotopyCategory.quotient (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ)).obj
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
private theorem heq_derivedPullbackGeometricStalkHomotopyMap_app
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    HEq ((derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
        ((representedAffineHomotopyAssociated B S hS U).obj M))
      ((derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ)).obj
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M))) :=
  congr_arg_heq (derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
    (representedAffineHomotopyAssociated_obj_eq B S hS M)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The homotopy-level comparison at the class of `M^~` agrees with its value at the quotient of
the degreewise associated complex. -/
theorem derivedPullbackGeometricStalkHomotopyMap_app_representedAffineHomotopyAssociated
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
        ((representedAffineHomotopyAssociated B S hS U).obj M) =
      (derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ)).obj
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)) :=
  eq_of_heq (heq_derivedPullbackGeometricStalkHomotopyMap_app B S hS g x M)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- The comparison on the homotopy category at the class of `M^~` is the comparison on
complexes. -/
theorem derivedPullbackGeometricStalkHomotopyMap_app_representedAffine
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (derivedPullbackGeometricStalkHomotopyMap (representedSpaceMap B S hS g) x).app
        ((representedAffineHomotopyAssociated B S hS U).obj M) =
      (derivedPullbackGeometricStalkComplexMap (representedSpaceMap B S hS g) x).app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) :=
  (derivedPullbackGeometricStalkHomotopyMap_app_representedAffineHomotopyAssociated
    B S hS g x M).trans (derivedPullbackGeometricStalkHomotopyMap_app _ _ _)

/-- **The derived pullback-stalk comparison at `Φ(M)`, followed by the stalk of the affine base
change morphism.** On a complex `M` of `A₀`-modules, it is the degreewise comparison of
`AlgebraicGeometry.Space.derivedPullbackGeometricStalkComplexMap` at `M^~`, between the canonical
factorizations and the degreewise pullback of associated modules. -/
theorem derivedPullbackGeometricStalkMap_app_representedAffine
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (derivedPullbackGeometricStalkMap (representedSpaceMap B S hS g) x).app
        ((representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj M)) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
        ((representedAffineDerivedBaseChangeIso B S hS g).hom.app (DerivedCategory.Q.obj M) ≫
          (representedAffineDerivedAssociated B S hS P).map
            ((representedAffineDerivedExtension B S hS g).comparison.app M)) =
      (geometricStalkDerivedExtension (representedSpaceMap B S hS g) x).functor.map
          ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
            (geometricPointMap (representedSpaceMap B S hS g).hom x)).map
              ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M)) ≫
        (derivedPullbackGeometricStalkComplexMap (representedSpaceMap B S hS g) x).app
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          (DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g).hom.app M)) ≫
        (geometricDerivedStalk B S hS (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x).map
          ((representedAffineDerivedAssociatedFactors B S hS P).inv.app
            (((ModuleCat.extendScalars.{u, u, u}
              (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) := by
  refine (congrArg (_ ≫ ·)
    (geometricDerivedStalk_map_representedAffineDerivedBaseChangeIso B S hS g x M)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)).trans (Category.assoc _ _ _)
  refine ((Category.assoc _ _ _).trans
    (derivedPullbackGeometricStalkMap_app_comp_map_comparison B S hS g x _ _)).trans ?_
  exact congrArg (_ ≫ ·)
    (derivedPullbackGeometricStalkHomotopyMap_app_representedAffine B S hS g x M)

end Square

section Factors

variable {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (y : GeometricPoint B S hS (yoneda.obj U))

/-- The inverse of `DerivedCategory.quotientCompQhIso` followed by its forward map, in the two
spellings of the module category, is the identity at `M^~`. -/
theorem quotientCompQhIso_inv_hom_app_representedAffine
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (DerivedCategory.quotientCompQhIso
        (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))).inv.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) = 𝟙 _ :=
  (DerivedCategory.quotientCompQhIso
    (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))).inv_hom_id_app _

/-- The forward component at a complex `M` of the canonical factorization of `Φ` is that of the
associated-module functor followed by the inverse of `DerivedCategory.quotientCompQhIso`. -/
theorem representedAffineDerivedAssociatedFactors_hom_app
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedAssociatedFactors B S hS U).hom.app M =
      (representedAffineAssociated B S hS U).mapDerivedCategoryFactors.hom.app M ≫
        (DerivedCategory.quotientCompQhIso
            (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))).inv.app
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) := by
  simp [representedAffineDerivedAssociatedFactors]

/-- The inverse component at a complex `M` of the canonical factorization of `Φ` is
`DerivedCategory.quotientCompQhIso` followed by that of the associated-module functor. -/
theorem representedAffineDerivedAssociatedFactors_inv_app
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedAssociatedFactors B S hS U).inv.app M =
      (DerivedCategory.quotientCompQhIso
          (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))).hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
        (representedAffineAssociated B S hS U).mapDerivedCategoryFactors.inv.app M := by
  simp [representedAffineDerivedAssociatedFactors]

/-- The stalk at a geometric point of the canonical factorization of `Φ`, in the two spellings of
the module category. -/
theorem geometricDerivedStalk_map_representedAffineDerivedAssociatedFactors
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
            y).map ((representedAffineDerivedAssociatedFactors B S hS U).hom.app M) ≫
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
            y).map ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u}
              (ringedToposStructureRingSheaf B S hS
                ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))).hom.app
              (((representedAffineAssociated B S hS U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M)) ≫
      (Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS (yoneda.obj U) y
            (isAlgebraicSpace_yoneda B S hS U))
          (smallEtaleRingedTopos B S hS
            ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).mapDerivedCategoryFactors.hom.app
          (((representedAffineAssociated B S hS U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) =
    (representedStalkFunctor B S hS U y).mapDerivedCategory.map
        ((representedAffineAssociated B S hS U).mapDerivedCategoryFactors.hom.app M) ≫
      (representedStalkFunctor B S hS U y).mapDerivedCategoryFactors.hom.app
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) := by
  refine (congrArg (· ≫ _) ((congrArg
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) y).map
      (representedAffineDerivedAssociatedFactors_hom_app B S hS M)).trans
    ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      y).map_comp _ _))).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _)
    (((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      y).map_comp _ _).symm.trans
    ((congrArg
      (geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) y).map
      (quotientCompQhIso_inv_hom_app_representedAffine B S hS M)).trans
    ((geometricDerivedStalk B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      y).map_id _)))).trans ?_
  exact Category.id_comp _

end Factors

end AlgebraicGeometry.Space

