module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftOfConjugation
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.CategoryTheory.Shift.RestrictFullyFaithfulCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorFlipCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ComparisonCommShift
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.LiftBifunctorFlip

/-!
# Stacks 0E5P for algebraic spaces

For a quasi-compact quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, the derived tensor
products restrict to `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_Y)` (Stacks 08F5), derived pullback and derived
pushforward restrict to an adjunction between them, and Stacks 07A4 restricts to a comparison of
the two tensor products. Together they form an
`AlgebraicGeometry.Space.PullbackComparisonData`, from which the map of Stacks 0E5P is built:
for `X`, `Y` quasi-compact and quasi-separated and `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55), the map `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)`,
functorial in `K` and compatible with distinguished triangles.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedTensor`: `- ⊗^L -` on `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPullbackTensorComparison`: Stacks 07A4 on
  `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentPullbackComparisonData`.
* `AlgebraicGeometry.Space.quasicoherentDerivedTensorRightUnitor`: `K ⊗^L 𝒪_X ≅ K` on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedCompareWithPullbackTensor`: the two-variable map
  `Lf^*K ⊗^L a(L) ⟶ a(K ⊗^L L)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedCompareWithPullback`: **Stacks 0E5P**.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedCompareWithPullback_commShift`: **Stacks 0E5P**,
  compatibility with distinguished triangles.

## References

* [Stacks Project, Tag 0E5P](https://stacks.math.columbia.edu/tag/0E5P)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.K0
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The derived tensor product of `D_QCoh(𝒪_X)`, the restriction of `- ⊗^L_{𝒪_X} -`. -/
def quasicoherentDerivedTensor (X : AlgebraicSpaces B S hS) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
        QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  liftBifunctor (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
    (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)

variable {X Y : AlgebraicSpaces B S hS}

/-- Stacks 07A4 on the quasi-coherent derived categories, with the factors exchanged as in
`AlgebraicGeometry.Space.PullbackComparisonData`: `Lf^*(K₂ ⊗ K₁) ⟶ Lf^*K₂ ⊗ Lf^*K₁`. -/
def quasicoherentDerivedPullbackTensorComparison (f : X ⟶ Y) :
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (quasicoherentDerivedTensor B S hS Y)) ⋙
        quasicoherentDerivedModulePullback f ⟶
      (quasicoherentDerivedModulePullback f).prod (quasicoherentDerivedModulePullback f) ⋙
        (CategoryTheory.Prod.swap _ _ ⋙
          Functor.uncurry.obj (quasicoherentDerivedTensor B S hS X)) where
  app K := ObjectProperty.homMk ((smallEtaleDerivedPullbackTensorIso f).hom.app (K.2.obj, K.1.obj))
  naturality {K K'} g := by
    ext
    exact (smallEtaleDerivedPullbackTensorIso f).hom.naturality
      ((g.2.hom, g.1.hom) : ((K.2.obj, K.1.obj) : _ × _) ⟶ (K'.2.obj, K'.1.obj))

/-- The data entering Stacks 0E5P for a quasi-compact quasi-separated morphism of algebraic
spaces: the derived tensor products of `D_QCoh`, `Lf^* ⊣ Rf_*` on `D_QCoh`, and Stacks 07A4. -/
abbrev quasicoherentPullbackComparisonData (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    PullbackComparisonData B S hS f where
  isQuasiCompact := hfqc
  isQuasiSeparated := hfqs
  tensorX := quasicoherentDerivedTensor B S hS X
  tensorY := quasicoherentDerivedTensor B S hS Y
  pullback := quasicoherentDerivedModulePullback f
  pushforward := quasicoherentDerivedPushforward B S hS f hfqc hfqs
  adj := quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs
  tensorPullbackComparison := quasicoherentDerivedPullbackTensorComparison f

/-! ### Compatibility of the data with the shift -/

attribute [local instance 5000] SheafOfModules.instAbelian

/-- Fixing its second argument, the derived tensor product of `D_QCoh(𝒪_X)` commutes with the
shift. -/
instance quasicoherentDerivedTensor_flip_obj_commShift (X : AlgebraicSpaces B S hS)
    (T : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    ((quasicoherentDerivedTensor B S hS X).flip.obj T).CommShift ℤ :=
  liftBifunctorCommShiftLeft (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
    (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
    (smallEtaleDerivedTensorProduct B S hS X).commShift_left T

/-- A morphism in the second argument of the derived tensor product of `D_QCoh(𝒪_X)` gives a
transformation commuting with the shift. -/
instance quasicoherentDerivedTensor_flip_map_commShift (X : AlgebraicSpaces B S hS)
    {T T' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2} (g : T ⟶ T') :
    NatTrans.CommShift ((quasicoherentDerivedTensor B S hS X).flip.map g) ℤ :=
  liftBifunctor_flip_map_commShift (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
    (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
    (smallEtaleDerivedTensorProduct B S hS X).commShift_left
    (fun g => (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      _).commShift₂.commShift_flip_map g) g

/-- The inclusion of `D_QCoh(𝒪_Y)` followed by `Lf^*` commutes with the shift. -/
instance ι_comp_smallEtaleDerivedModulePullback_commShift (f : X ⟶ Y) :
    ((QcohDerived B S hS Y).ι ⋙ smallEtaleDerivedModulePullback B S hS f).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
    (commShift_smallEtaleDerivedModulePullback B S hS f)

/-- `Lf^*` on `D_QCoh` commutes with the shift. -/
instance commShift_quasicoherentDerivedModulePullback (f : X ⟶ Y) :
    (quasicoherentDerivedModulePullback f).CommShift ℤ :=
  @Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _ (quasicoherentDerivedModulePullbackCompιIso f) _ _
    ℤ _ _ _ _ inferInstance (ι_comp_smallEtaleDerivedModulePullback_commShift f)

/-- The adjunction `Lf^* ⊣ Rf_*` on `D_QCoh` is compatible with the shifts. -/
instance quasicoherentDerivedModuleAdjunction_commShift (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).CommShift ℤ :=
  Adjunction.commShift_restrictFullyFaithful_of_adjunction
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y))
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X))
    (quasicoherentDerivedModulePullbackCompιIso f).symm
    (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs).symm ℤ
    (hiCs := (inferInstance : (QcohDerived B S hS Y).ι.CommShift ℤ))
    (hiDs := (inferInstance : (QcohDerived B S hS X).ι.CommShift ℤ))
    (hLs := commShift_quasicoherentDerivedModulePullback f)
    (hRs := commShift_quasicoherentDerivedPushforward B S hS f hfqc hfqs)
    (hL's := commShift_smallEtaleDerivedModulePullback B S hS f)
    (hR's := derivedModulePushforward_commShift B S hS f)
    (hadj := smallEtaleDerivedModuleAdjunction_commShift B S hS f)
    (h1 := @NatTrans.CommShift.of_iso_inv _ _ _ _ _ _
      (quasicoherentDerivedModulePullbackCompιIso f) ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (commShift_quasicoherentDerivedModulePullback f) inferInstance)
      (ι_comp_smallEtaleDerivedModulePullback_commShift f)
      (@Functor.CommShift.ofComp_compatibility _ _ _ _ _ _ _ _ _
        (quasicoherentDerivedModulePullbackCompιIso f) _ _ ℤ _ _ _ _ inferInstance
          (ι_comp_smallEtaleDerivedModulePullback_commShift f)))
    (h2 := @NatTrans.CommShift.of_iso_inv _ _ _ _ _ _
      (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs) ℤ _ _ _ _ _
        (Functor.CommShift.ofComp_compatibility _ _))

/-- Stacks 07A4 on `D_QCoh`, with its second argument fixed, commutes with the shift in the
first. -/
instance quasicoherentPullbackComparisonData_tensorPullbackComparisonFlip_commShift
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    NatTrans.CommShift
      ((quasicoherentPullbackComparisonData f hfqc hfqs).tensorPullbackComparisonFlip G) ℤ :=
  NatTrans.commShift_of_conj_lift (quasicoherentDerivedModulePullbackCompιIso f)
    (liftBifunctorFlipObjCompιIso (QcohDerived B S hS Y) (smallEtaleDerivedTensor B S hS Y)
      (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor Y K L hK hL) G)
    (liftBifunctorFlipObjCompιIso (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
      (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
      ((quasicoherentDerivedModulePullback f).obj G))
    (Functor.flipObjIsoOfUncurryIso (smallEtaleDerivedPullbackTensorIso f) G.obj).hom
    ((quasicoherentPullbackComparisonData f hfqc hfqs).tensorPullbackComparisonFlip G)
    (hι₁ := (inferInstance : (QcohDerived B S hS Y).ι.CommShift ℤ))
    (hι₂ := (inferInstance : (QcohDerived B S hS X).ι.CommShift ℤ))
    (hT₁ := quasicoherentDerivedTensor_flip_obj_commShift Y G)
    (hP := commShift_quasicoherentDerivedModulePullback f)
    (hT₂ := quasicoherentDerivedTensor_flip_obj_commShift X
      ((quasicoherentDerivedModulePullback f).obj G))
    (hT₁' := (smallEtaleDerivedTensorProduct B S hS Y).commShift_left G.obj)
    (hL := commShift_smallEtaleDerivedModulePullback B S hS f)
    (hT₂' := (smallEtaleDerivedTensorProduct B S hS X).commShift_left
      ((smallEtaleDerivedModulePullback B S hS f).obj G.obj))
    (heP := @Functor.CommShift.ofComp_compatibility _ _ _ _ _ _ _ _ _
      (quasicoherentDerivedModulePullbackCompιIso f) _ _ ℤ _ _ _ _ inferInstance
      (ι_comp_smallEtaleDerivedModulePullback_commShift f))
    (he₁ := Functor.CommShift.ofComp_compatibility _ _)
    (he₂ := @Functor.CommShift.ofComp_compatibility _ _ _ _ _ _ _ _ _
      (liftBifunctorFlipObjCompιIso (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
        (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
        ((quasicoherentDerivedModulePullback f).obj G)) _ _ ℤ _ _ _ _ inferInstance
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
        ((smallEtaleDerivedTensorProduct B S hS X).commShift_left
          ((smallEtaleDerivedModulePullback B S hS f).obj G.obj))))
    (hβ :=
      Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorFlipObjIso_commShift_of_eq
      (smallEtaleRingedToposHom B S hS f) (smallEtaleDerivedTensorProduct B S hS X)
      (smallEtaleDerivedTensorProduct B S hS Y) rfl rfl (smallEtaleDerivedPullbackTensorIso f) rfl
      G.obj)
    (h := fun K => by
      have e1 : (quasicoherentDerivedModulePullbackCompιIso f).hom.app
          (((quasicoherentDerivedTensor B S hS Y).flip.obj G).obj K) = 𝟙 _ := rfl
      have e2 : (liftBifunctorFlipObjCompιIso (QcohDerived B S hS Y)
          (smallEtaleDerivedTensor B S hS Y)
          (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor Y K L hK hL) G).hom.app K =
            𝟙 _ := rfl
      have e3 : (quasicoherentDerivedModulePullbackCompιIso f).inv.app K = 𝟙 _ := rfl
      simp only [e1, e2, e3, liftBifunctorFlipObjCompιIso_inv_app]
      refine Eq.trans ?_ (Category.id_comp _).symm
      refine Eq.trans ?_
        (eq_whisker ((smallEtaleDerivedModulePullback B S hS f).map_id _) _).symm
      refine Eq.trans ?_ (Category.id_comp _).symm
      refine Eq.trans ?_ (whisker_eq _ (Category.comp_id _)).symm
      refine Eq.trans ?_ (whisker_eq _ (((smallEtaleDerivedTensorProduct B S hS X).tensor.flip.obj
        ((smallEtaleDerivedModulePullback B S hS f).obj G.obj)).map_id _)).symm
      refine Eq.trans ?_ (Category.comp_id _).symm
      rfl)

/-! ### The projection formula on `D_QCoh` -/

/-- The projection-formula map of the data on `D_QCoh` is the projection-formula map
`K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)` of `D(𝒪_Y)`. -/
theorem quasicoherentPullbackComparisonData_projectionFormulaMap_hom (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    ((quasicoherentPullbackComparisonData f hfqc hfqs).projectionFormulaMap E K).hom =
      smallEtaleProjectionFormulaMapSnd f K.obj E.obj := by
  refine (ι_map_quasicoherentDerivedModuleAdjunction_homEquiv B S hS f hfqc hfqs _ _ _).trans ?_
  have h2 := ι_map_quasicoherentDerivedModuleAdjunction_counit_app B S hS f hfqc hfqs E
  change (smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _
      ((smallEtaleDerivedPullbackTensorIso f).hom.app (K.obj, _) ≫
        ((smallEtaleDerivedTensor B S hS X).map (𝟙 _)).app _ ≫
          ((smallEtaleDerivedTensor B S hS X).obj _).map
            ((quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).counit.app E).hom) =
    (smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _
      ((smallEtaleDerivedPullbackTensorIso f).hom.app (K.obj, _) ≫
        ((smallEtaleDerivedTensor B S hS X).map (𝟙 _)).app _ ≫
          ((smallEtaleDerivedTensor B S hS X).obj _).map
            ((smallEtaleDerivedModuleAdjunction B S hS f).counit.app E.obj))
  exact congrArg ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _)
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
      (congrArg (((smallEtaleDerivedTensor B S hS X).obj _).map) h2)))

/-- **Stacks 08IN on `D_QCoh`**: the projection-formula map of the data is invertible. -/
instance isIso_quasicoherentPullbackComparisonData_projectionFormulaMap (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso ((quasicoherentPullbackComparisonData f hfqc hfqs).projectionFormulaMap E K) := by
  have h := isIso_smallEtaleProjectionFormulaMapSnd B S hS f hfqc hfqs K.obj K.property E.obj
    E.property
  rw [← quasicoherentPullbackComparisonData_projectionFormulaMap_hom f hfqc hfqs E K] at h
  exact (ObjectProperty.isIso_hom_iff _).1 h

/-! ### The right unitor on `D_QCoh` -/

variable (B S hS) in
/-- The right unitor `K ⊗^L 𝒪_X ≅ K` of the derived tensor product of `D_QCoh(𝒪_X)`. -/
def quasicoherentDerivedTensorRightUnitor (X : AlgebraicSpaces B S hS) :
    (quasicoherentDerivedTensor B S hS X).flip.obj (derivedStructureSheaf B S hS X.1 X.2) ≅
      𝟭 _ :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      ((smallEtaleDerivedTensorProduct B S hS X).unitComplexNatIso.app K.obj))
    (fun h => ObjectProperty.hom_ext _
      ((smallEtaleDerivedTensorProduct B S hS X).unitComplexNatIso.hom.naturality h.hom))

/-- The right unitor of `D_QCoh(𝒪_X)` commutes with the shift. -/
instance quasicoherentDerivedTensorRightUnitor_commShift (X : AlgebraicSpaces B S hS) :
    NatTrans.CommShift (quasicoherentDerivedTensorRightUnitor B S hS X).hom ℤ :=
  NatTrans.commShift_of_conj_app (QcohDerived B S hS X).ι
    (liftBifunctorFlipObjCompιIso (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
      (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
      (derivedStructureSheaf B S hS X.1 X.2))
    (Functor.leftUnitor (QcohDerived B S hS X).ι)
    (Functor.whiskerLeft (QcohDerived B S hS X).ι
        (smallEtaleDerivedTensorProduct B S hS X).unitComplexNatIso.hom ≫
      (Functor.rightUnitor (QcohDerived B S hS X).ι).hom)
    (quasicoherentDerivedTensorRightUnitor B S hS X).hom
    (hF := quasicoherentDerivedTensor_flip_obj_commShift X (derivedStructureSheaf B S hS X.1 X.2))
    (hF' := @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
      ((smallEtaleDerivedTensorProduct B S hS X).commShift_left
        (derivedStructureSheaf B S hS X.1 X.2).obj))
    (heF := @Functor.CommShift.ofComp_compatibility _ _ _ _ _ _ _ _ _
      (liftBifunctorFlipObjCompιIso (QcohDerived B S hS X) (smallEtaleDerivedTensor B S hS X)
        (fun K L hK hL => qcohDerived_smallEtaleDerivedTensor X K L hK hL)
        (derivedStructureSheaf B S hS X.1 X.2)) _ _ ℤ _ _ _ _ inferInstance
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
        ((smallEtaleDerivedTensorProduct B S hS X).commShift_left
          (derivedStructureSheaf B S hS X.1 X.2).obj)))
    (hθ := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
        ((smallEtaleDerivedTensorProduct B S hS X).commShift_left
          (derivedStructureSheaf B S hS X.1 X.2).obj))
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance (Functor.CommShift.id _))
      inferInstance
      (@NatTrans.CommShift.whiskerLeft _ _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ inferInstance
        ((smallEtaleDerivedTensorProduct B S hS X).commShift_left _) (Functor.CommShift.id _)
        (Stacks.SheafOfModules.unitNatIso_commShift (smallEtaleRingedSite B S hS X.1 X.2)))
      (@NatTrans.CommShift.rightUnitor _ _ _ _ _ ℤ _ _ _ inferInstance))
    (fun K => by
      simp only [liftBifunctorFlipObjCompιIso_hom_app, NatTrans.comp_app,
        Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app]
      refine Eq.trans ?_ (Category.id_comp _).symm
      refine Eq.trans ?_ (Category.comp_id _).symm
      refine Eq.trans ?_ (Category.comp_id _).symm
      rfl)

/-! ### Stacks 0E5P -/

section RightAdjoint

variable (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.1)
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- The data of Stacks 0E5P for a morphism of quasi-compact quasi-separated algebraic spaces. -/
abbrev quasicoherentDualityData : PullbackComparisonData B S hS f :=
  quasicoherentPullbackComparisonData f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)

/-- The adjunction `Rf_* ⊣ a` on `D_QCoh` of Stacks 0E55, for the data of Stacks 0E5P. -/
abbrev quasicoherentDualityAdjunction :
    (quasicoherentDualityData hZ f hXqc hXqs hYqs).pushforward ⊣
      quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs :=
  quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)

/-- The right adjoint `a` of `Rf_*` on `D_QCoh` (Stacks 0E55) commutes with the shift, as the
right adjoint of a functor commuting with the shift. -/
instance quasicoherentDerivedRightAdjoint_commShift :
    (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).CommShift ℤ :=
  (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs).rightAdjointCommShift ℤ

/-- The adjunction `Rf_* ⊣ a` is compatible with the shifts. -/
instance quasicoherentDualityAdjunction_commShift :
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs).CommShift ℤ :=
  (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs).commShift_of_leftAdjoint ℤ

/-- **The two-variable map of Stacks 0E5P**: for `K, L ∈ D_QCoh(𝒪_Y)`, the map
`Lf^*K ⊗^L_{𝒪_X} a(L) ⟶ a(K ⊗^L_{𝒪_Y} L)` adjoint to the inverse of the projection formula
`Rf_*(Lf^*K ⊗^L a(L)) ≅ K ⊗^L Rf_*a(L)` (Stacks 08IN) followed by `K` tensored with the trace
map `Rf_*a(L) ⟶ L`. -/
def quasicoherentDerivedCompareWithPullbackTensor
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    ((quasicoherentDerivedTensor B S hS X).obj ((quasicoherentDerivedModulePullback f).obj K)).obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj L) ⟶
      (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
        (((quasicoherentDerivedTensor B S hS Y).obj K).obj L) :=
  (quasicoherentDualityData hZ f hXqc hXqs hYqs).compareWithPullbackTensor
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs) K L

/-- **Stacks 0E5P.** Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated algebraic
spaces over `S` and let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
(Stacks 0E55). The map `Lf^*K ⊗^L_{𝒪_X} a(𝒪_Y) ⟶ a(K)`, the two-variable map at `L = 𝒪_Y`
followed by `a` of the unitor, is functorial in `K`. -/
@[stacks 0E5P]
def quasicoherentDerivedCompareWithPullback :
    quasicoherentDerivedModulePullback f ⋙ (quasicoherentDerivedTensor B S hS X).flip.obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
          (derivedStructureSheaf B S hS Y.1 Y.2)) ⟶
      quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs :=
  (quasicoherentDualityData hZ f hXqc hXqs hYqs).compareWithPullbackNatTrans
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs)
    (quasicoherentDerivedTensorRightUnitor B S hS Y)

/-- The component of Stacks 0E5P at `K` is the two-variable map at `(K, 𝒪_Y)` followed by `a` of
the unitor `K ⊗^L 𝒪_Y ≅ K`. -/
theorem quasicoherentDerivedCompareWithPullback_app
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (quasicoherentDerivedCompareWithPullback hZ f hXqc hXqs hYqs).app K =
      quasicoherentDerivedCompareWithPullbackTensor hZ f hXqc hXqs hYqs K
          (derivedStructureSheaf B S hS Y.1 Y.2) ≫
        (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).map
          ((quasicoherentDerivedTensorRightUnitor B S hS Y).hom.app K) :=
  rfl

/-- **Stacks 0E5P, compatibility with distinguished triangles.** The map
`Lf^*K ⊗^L_{𝒪_X} a(𝒪_Y) ⟶ a(K)` commutes with the shift, so it carries the third morphism of a
distinguished triangle in `K` to the third morphism of its image. -/
@[stacks 0E5P]
theorem quasicoherentDerivedCompareWithPullback_commShift :
    NatTrans.CommShift (quasicoherentDerivedCompareWithPullback hZ f hXqc hXqs hYqs) ℤ := by
  have := (quasicoherentDualityData hZ f hXqc hXqs hYqs).projectionFormulaNatTrans_commShift
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
      (derivedStructureSheaf B S hS Y.1 Y.2))
  exact PullbackComparisonData.compareWithPullbackNatTrans_commShift_of_commShift_flip
    (quasicoherentDualityData hZ f hXqc hXqs hYqs)
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs)
    (quasicoherentDerivedTensorRightUnitor B S hS Y)

end RightAdjoint

end AlgebraicGeometry.Space

end
