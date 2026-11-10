module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral.ToTensorExactness

/-!
# Existence of the derived tensor product at three independent universes

The compatibility of the derived tensor bifunctor with the shifts, its exactness in each
variable, and Stacks 06YU: `Stacks.SheafOfModules.exists_derivedTensorProduct_general` and the
canonical derived tensor product `Stacks.SheafOfModules.canonicalDerivedTensorProductGeneral`.
-/

/-! ### Compatibility with the shifts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

attribute [local instance] derivedTensorBifunctorLiftingGeneral
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex

/-- `Stacks.SheafOfModules.tensorComplex_commShift₂Int` for a ringed site whose objects,
morphisms and sections live in three independent universes `c`, `v`, `w`. It is the instance of
the copy `CategoryTheory.Functor.map₂HomologicalComplexReg` that `tensorComplex` unfolds to. -/
instance tensorComplex_commShift₂Int_general :
    (Stacks.SheafOfModules.Tensor.tensorComplex.{c, v, w} X.O).CommShift₂Int :=
  Functor.map₂HomologicalComplexReg_commShift₂Int _

/-- The total tensor product of a K-flat complex with an arbitrary complex, pushed into the
derived category, commutes with the shifts in both variables. -/
instance kFlatTensorToDerived_commShift₂Int_general :
    (kFlatTensorToDerivedGeneral X).CommShift₂Int :=
  (inferInstance : ((kFlatComplexesGeneral X).ι ⋙
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)).CommShift₂Int)

/-- The derived tensor bifunctor commutes with the shifts in both variables. -/
instance derivedTensorBifunctor_commShift₂Int_general :
    (derivedTensorBifunctorGeneral X).CommShift₂Int :=
  Functor.CommShift₂.ofLocalizationInt (kFlatComplexQGeneral X) DerivedCategory.Q
    (kFlatComplexQuasiIsoGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
      (ComplexShape.up ℤ))
    (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X)

/-! ### The shift on the K-flat models, and the two factorisations of `Pc.ι ⋙ Q` -/

/-- The quotient from K-flat complexes to K-flat objects of the homotopy category commutes
with the shifts. -/
instance complexSubcategoryQuotient_commShift_general :
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O)).CommShift ℤ :=
  Functor.CommShift.ofComp (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O)
    ((kFlatComplexesGeneral X).ι ⋙
      HomotopyCategory.quotient
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
        (ComplexShape.up ℤ)) (fun Y ↦ Y.2)) ℤ

/-- The isomorphism of `complexSubcategoryQuotient_commShift_general` is itself compatible with the
shifts. -/
instance complexSubcategoryQuotient_liftCompιIso_commShift_general :
    NatTrans.CommShift (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O)
      ((kFlatComplexesGeneral X).ι ⋙
        HomotopyCategory.quotient
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
          (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The comparison of the two factorisations of `Pc.ι ⋙ Q` is compatible with the shifts. -/
instance complexSubcategoryQuotientCompIso_commShift_general :
    NatTrans.CommShift
      (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, v, w} X.O)).hom ℤ := by
  have h : (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, v, w} X.O)).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O)
          ((kFlatComplexesGeneral X).ι ⋙
            HomotopyCategory.quotient
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).hom DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))).hom :=
    rfl
  rw [h]
  infer_instance

/-! ### Exactness in the second variable, at the canonical structure -/

/-- For every object `N`, the derived tensor product `N ⊗^L -` is a triangulated functor. -/
instance derivedTensorBifunctor_isTriangulated_obj_general
    (N : DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))) :
    ((derivedTensorBifunctorGeneral X).obj N).IsTriangulated :=
  Localization.isTriangulated_objCommShift (kFlatComplexQGeneral X) DerivedCategory.Q
    (kFlatComplexQuasiIsoGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
      (ComplexShape.up ℤ))
    (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X)
    (fun Â => by
      let := Localization.Lifting₂.fst (kFlatComplexQGeneral X) DerivedCategory.Q
        (kFlatComplexQuasiIsoGeneral X)
        (HomologicalComplex.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
          (ComplexShape.up ℤ))
        (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X) Â
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      -- `bifunctorPhiFactors` with its target at `tensorComplex`: instance search compares the
      -- functors of the composites below at implicit transparency, where `tensorComplex` unfolds
      -- to the copy but not to Mathlib's `map₂HomologicalComplex`.
      let φ : HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ≅
          (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj ⋙
            HomotopyCategory.quotient _ (ComplexShape.up ℤ) :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      have : NatTrans.CommShift φ.hom ℤ :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors_commShift_reg _ Â.obj
      let :
          ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â)).CommShift ℤ :=
        Functor.commShiftOfLocalization DerivedCategory.Q
          (HomologicalComplex.quasiIso
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)) ℤ
          ((kFlatTensorToDerivedGeneral X).obj Â)
          ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))
      let : Localization.Lifting
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerivedGeneral X).obj Â)
          (DerivedCategory.Qh ⋙
            (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â)) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
            ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â)) ≪≫
          Localization.Lifting.iso DerivedCategory.Q
            (HomologicalComplex.quasiIso
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerivedGeneral X).obj Â)
            ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))⟩
      let : Localization.Lifting
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerivedGeneral X).obj Â)
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight φ DerivedCategory.Qh ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj)
            (DerivedCategory.quotientCompQhIso _)⟩
      have e1 : (Localization.Lifting.iso
            (HomotopyCategory.quotient
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerivedGeneral X).obj Â)
            (DerivedCategory.Qh ⋙
              (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))).hom =
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom
              ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â)) ≫
            (Localization.Lifting.iso DerivedCategory.Q
              (HomologicalComplex.quasiIso
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerivedGeneral X).obj Â)
              ((derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))).hom :=
        rfl
      have e2 : (Localization.Lifting.iso
            (HomotopyCategory.quotient
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerivedGeneral X).obj Â)
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                DerivedCategory.Qh)).inv =
          ((Functor.whiskerLeft
                ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj)
                (DerivedCategory.quotientCompQhIso _).inv ≫
              (Functor.associator _ _ _).inv) ≫
            Functor.whiskerRight φ.inv DerivedCategory.Qh) ≫
            (Functor.associator _ _ _).hom :=
        rfl
      have : NatTrans.CommShift
          (Localization.liftNatIso
            (HomotopyCategory.quotient
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerivedGeneral X).obj Â) ((kFlatTensorToDerivedGeneral X).obj Â)
            (DerivedCategory.Qh ⋙
              (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh)
            (Iso.refl _)).hom ℤ := by
        refine Localization.natTrans_commShift_of_whiskerLeft
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)) _ ?_
        have heq : Functor.whiskerLeft
              (HomotopyCategory.quotient
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              (Localization.liftNatIso
                (HomotopyCategory.quotient
                  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                  (ComplexShape.up ℤ))
                (HomologicalComplex.homotopyEquivalences
                  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                  (ComplexShape.up ℤ))
                ((kFlatTensorToDerivedGeneral X).obj Â) ((kFlatTensorToDerivedGeneral X).obj Â)
                (DerivedCategory.Qh ⋙
                  (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))
                (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
                  (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                    DerivedCategory.Qh)
                (Iso.refl _)).hom =
            (Localization.Lifting.iso
              (HomotopyCategory.quotient
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              (HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerivedGeneral X).obj Â)
              (DerivedCategory.Qh ⋙
                (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))).hom ≫
            (Localization.Lifting.iso
              (HomotopyCategory.quotient
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              (HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerivedGeneral X).obj Â)
              (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                  DerivedCategory.Qh)).inv := by
          ext K
          simp
        rw [heq, e1, e2]
        infer_instance
      exact Functor.isTriangulated_of_precomp_iso
        (Localization.liftNatIso
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerivedGeneral X).obj Â) ((kFlatTensorToDerivedGeneral X).obj Â)
          (DerivedCategory.Qh ⋙
            (derivedTensorBifunctorGeneral X).obj ((kFlatComplexQGeneral X).obj Â))
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh)
          (Iso.refl _)))
    N

/-! ### Exactness in the first variable, at the canonical structure -/

attribute [local instance] kFlatQ_isLocalization_general
  kFlatQuasiIso_hasLeftCalculusOfFractions_general kFlatQ_mapArrow_essSurj_general

/-- For every object `M`, the derived tensor product `- ⊗^L M` is a triangulated functor. -/
instance derivedTensorBifunctor_isTriangulated_flipObj_general
    (M : DerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))) :
    ((derivedTensorBifunctorGeneral X).flip.obj M).IsTriangulated :=
  Localization.isTriangulated_objCommShift DerivedCategory.Q (kFlatComplexQGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
      (ComplexShape.up ℤ))
    (kFlatComplexQuasiIsoGeneral X)
    (kFlatTensorToDerivedGeneral X).flip (derivedTensorBifunctorGeneral X).flip
    (fun B => by
      let := Localization.Lifting₂.fst DerivedCategory.Q (kFlatComplexQGeneral X)
        (HomologicalComplex.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
          (ComplexShape.up ℤ))
        (kFlatComplexQuasiIsoGeneral X)
        (kFlatTensorToDerivedGeneral X).flip (derivedTensorBifunctorGeneral X).flip B
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      -- `bifunctorPhiRFactors` with its target at `tensorComplex`, as in
      -- `derivedTensorBifunctor_isTriangulated_obj_general`.
      let φ : HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ≅
          (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B ⋙
            HomotopyCategory.quotient _ (ComplexShape.up ℤ) :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      have : NatTrans.CommShift φ.hom ℤ :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors_commShift_reg _ B
      let : ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)).CommShift ℤ :=
        Functor.commShiftOfLocalization (kFlatComplexQGeneral X) (kFlatComplexQuasiIsoGeneral X) ℤ
          ((kFlatTensorToDerivedGeneral X).flip.obj B)
          ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))
      let : Localization.Lifting
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
          ((kFlatTensorToDerivedGeneral X).flip.obj B)
          (kFlatQGeneral.{c, v, w, d} X ⋙
            (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, v, w} X.O))
            ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) ≪≫
          Localization.Lifting.iso (kFlatComplexQGeneral X) (kFlatComplexQuasiIsoGeneral X)
            ((kFlatTensorToDerivedGeneral X).flip.obj B)
            ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))⟩
      let : Localization.Lifting
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
          ((kFlatTensorToDerivedGeneral X).flip.obj B)
          ((kFlatObjects.{c, v, w} X.O).ι ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O)
              ((kFlatComplexesGeneral X).ι ⋙
                HomotopyCategory.quotient
                  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                  (ComplexShape.up ℤ)) (fun Y ↦ Y.2))
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (kFlatComplexesGeneral X).ι
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight φ DerivedCategory.Qh ≪≫
              Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft
                ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
                (DerivedCategory.quotientCompQhIso _))⟩
      have e1 : (Localization.Lifting.iso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
            ((kFlatTensorToDerivedGeneral X).flip.obj B)
            (kFlatQGeneral.{c, v, w, d} X ⋙
              (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))).hom =
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight
              (ObjectProperty.complexSubcategoryQuotientCompIso
                (kFlatObjects.{c, v, w} X.O)).hom
              ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) ≫
            (Localization.Lifting.iso (kFlatComplexQGeneral X) (kFlatComplexQuasiIsoGeneral X)
              ((kFlatTensorToDerivedGeneral X).flip.obj B)
              ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))).hom :=
        rfl
      have e2 : (Localization.Lifting.iso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
            ((kFlatTensorToDerivedGeneral X).flip.obj B)
            ((kFlatObjects.{c, v, w} X.O).ι ⋙
              Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                  DerivedCategory.Qh)).inv =
          ((Functor.whiskerLeft (kFlatComplexesGeneral X).ι
                (((Functor.whiskerLeft
                      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
                      (DerivedCategory.quotientCompQhIso _).inv ≫
                    (Functor.associator _ _ _).inv) ≫
                  Functor.whiskerRight φ.inv DerivedCategory.Qh) ≫
                  (Functor.associator _ _ _).hom) ≫
              (Functor.associator _ _ _).inv) ≫
            Functor.whiskerRight
              (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O)
                ((kFlatComplexesGeneral X).ι ⋙
                  HomotopyCategory.quotient
                  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                  (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).inv
              (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                  DerivedCategory.Qh)) ≫
            (Functor.associator _ _ _).hom :=
        rfl
      have : NatTrans.CommShift
          (Localization.liftNatIso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
            ((kFlatTensorToDerivedGeneral X).flip.obj B)
            ((kFlatTensorToDerivedGeneral X).flip.obj B)
            (kFlatQGeneral.{c, v, w, d} X ⋙
              (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))
            ((kFlatObjects.{c, v, w} X.O).ι ⋙
              Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh)
            (Iso.refl _)).hom ℤ := by
        refine Localization.natTrans_commShift_of_whiskerLeft
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι) _ ?_
        have heq : Functor.whiskerLeft
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
              (Localization.liftNatIso
                (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
                ((HomologicalComplex.homotopyEquivalences
                  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                  (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
                ((kFlatTensorToDerivedGeneral X).flip.obj B)
                ((kFlatTensorToDerivedGeneral X).flip.obj B)
                (kFlatQGeneral.{c, v, w, d} X ⋙
                  (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))
                ((kFlatObjects.{c, v, w} X.O).ι ⋙
                  Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                      DerivedCategory.Qh)
                (Iso.refl _)).hom =
            (Localization.Lifting.iso
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
              ((HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
              ((kFlatTensorToDerivedGeneral X).flip.obj B)
              (kFlatQGeneral.{c, v, w, d} X ⋙
                (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))).hom ≫
            (Localization.Lifting.iso
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
              ((HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
                (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
              ((kFlatTensorToDerivedGeneral X).flip.obj B)
              ((kFlatObjects.{c, v, w} X.O).ι ⋙
                Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                  (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                    DerivedCategory.Qh)).inv := by
          ext K
          simp
        rw [heq, e1, e2]
        infer_instance
      exact Functor.isTriangulated_of_precomp_iso
        (Localization.liftNatIso
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexesGeneral X).ι)
          ((kFlatTensorToDerivedGeneral X).flip.obj B)
          ((kFlatTensorToDerivedGeneral X).flip.obj B)
          (kFlatQGeneral.{c, v, w, d} X ⋙
            (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))
          ((kFlatObjects.{c, v, w} X.O).ι ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh)
          (Iso.refl _)))
    M

end Stacks.SheafOfModules

end

/-! ### Existence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

/-- **Stacks 06YU.** The derived tensor product of sheaves of modules on a ringed site exists,
with its canonical natural map to the ordinary total tensor product, its one-sided K-flat
comparisons, and exactness in both variables.

The objects of the site form a type in a universe `c`, its morphisms lie in a universe `v`, and
the sections of its structure sheaf and of its modules lie in a universe `w`, all three
independent; the derived category's hom universe `d` is independent of them all. In particular
it applies to a small étale site, whose objects sit one universe above its morphisms, and to the
constant coefficient ringed site of Stacks 03TR, whose sections sit above both. -/
theorem exists_derivedTensorProduct_general :
    Nonempty (DerivedTensorProduct.{c, v, w, d} X) :=
  nonempty_derivedTensorProduct_of_exact_general X inferInstance (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)

/-- The canonical derived tensor product of sheaves of modules on a ringed site, with its
natural map to the ordinary total tensor product, K-flat comparisons, and exactness in both
variables. The objects, the morphisms, and the sections each live in a universe of their own. -/
def canonicalDerivedTensorProductGeneral : DerivedTensorProduct.{c, v, w, d} X :=
  derivedTensorProductOfExactGeneral X inferInstance (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance)

/-- The derived tensor bifunctor on the unbounded derived category of `X`. -/
abbrev derivedTensorProductFunctorGeneral :=
  (canonicalDerivedTensorProductGeneral.{c, v, w, d} X).tensor

end Stacks.SheafOfModules

end
