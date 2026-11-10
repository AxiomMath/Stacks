module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushoutBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings

/-!
# A model for the derived base change along a ring map

Let `R → R'` be a ring map, `R₀` a flat `R`-algebra with an `R`-algebra map `R₀ → R'`, and `F` a
K-flat resolution of `R'` over `R₀`.  For a complex `X` of `R`-modules the complex
`(R₀ ⊗_R X) ⊗_{R₀} F` computes `X ⊗^L_R R'`, read over `R₀`.  This file builds that model as a
functor, shows that it descends to derived categories, and identifies the descended functor with
the derived base change.

## Main definitions

* `RingTheory.TorIndependence.baseModelFunctor`: `X ↦ (R₀ ⊗_R X) ⊗_{R₀} F`.
* `RingTheory.TorIndependence.baseModelDerived`: the functor it induces on derived categories.

## Main results

* `RingTheory.TorIndependence.isLeftDerivedFunctor_baseModelDerived`
* `RingTheory.TorIndependence.isIso_baseModelLift`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

open CochainComplex.DerivedExtensionScalars

variable {R R₀ R' : Type u} [CommRing R] [CommRing R₀] [CommRing R']
  [Algebra R R₀] [Algebra R R'] [Algebra R₀ R'] [IsScalarTower R R₀ R']

variable (R) in
/-- Base change to `R₀` followed by the tensor product with a fixed complex `F` of
`R₀`-modules. -/
def baseModelFunctor (F : CochainComplex (ModuleCat.{u} R₀) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R₀) ℤ :=
  (baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ tensorRight F

/-- `(R₀ ⊗_R X) ⊗_{R₀} R' ≃ R' ⊗_R X`, `(r ⊗ x) ⊗ s ↦ π(r) s ⊗ x`, over `R₀`. -/
def baseTensorLinearEquiv (X : Type u) [AddCommGroup X] [Module R X] :
    (R₀ ⊗[R] X) ⊗[R₀] R' ≃ₗ[R₀] R' ⊗[R] X :=
  TensorProduct.comm R₀ (R₀ ⊗[R] X) R' ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R₀ R₀ R' X

/-- `baseTensorLinearEquiv` sends `(r ⊗ x) ⊗ s` to `(r • s) ⊗ x`. -/
theorem baseTensorLinearEquiv_tmul (X : Type u) [AddCommGroup X] [Module R X] (r : R₀) (x : X)
    (s : R') :
    baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X ((r ⊗ₜ[R] x) ⊗ₜ[R₀] s) =
      (r • s) ⊗ₜ[R] x := by
  simp [baseTensorLinearEquiv]

/-- `baseTensorLinearEquiv` is natural in `X`: it intertwines `(f.baseChange R₀) ⊗ R'` with
`f.baseChange R'`. -/
theorem baseTensorLinearEquiv_naturality {X Y : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (t : (R₀ ⊗[R] X) ⊗[R₀] R') :
    baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') Y
        (LinearMap.rTensor R' (f.baseChange R₀) t) =
      f.baseChange R' (baseTensorLinearEquiv X t) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a s =>
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => rw [TensorProduct.add_tmul, map_add, map_add, ha, hb, map_add, map_add]
    | tmul r x => simp [baseTensorLinearEquiv_tmul]

/-- The linear equivalence `baseTensorLinearEquiv`, landing in the restriction of scalars of
`R' ⊗_R X` along `R₀ → R'`. -/
def baseTensorRestrictLinearEquiv (X : ModuleCat.{u} R) :
    ((baseChangeFunctor R R₀ ⋙ StacksDraft.TorAmplitude.tensorModuleRight
        (ModuleCat.of R₀ R')).obj X) ≃ₗ[R₀]
      ((baseChangeFunctor R R' ⋙ ModuleCat.restrictScalars (algebraMap R₀ R')).obj X) where
  toFun t := baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X t
  invFun t := (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X).symm t
  map_add' := map_add (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X)
  map_smul' r t := (map_smul (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X) r t).trans
    (algebraMap_smul R' r (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X t)).symm
  left_inv := (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X).left_inv
  right_inv := (baseTensorLinearEquiv (R := R) (R₀ := R₀) (R' := R') X).right_inv

/-- Base change to `R₀` followed by `- ⊗_{R₀} R'` is base change to `R'` read over `R₀`. -/
def baseTensorIso :
    baseChangeFunctor R R₀ ⋙ StacksDraft.TorAmplitude.tensorModuleRight (ModuleCat.of R₀ R') ≅
      baseChangeFunctor R R' ⋙ ModuleCat.restrictScalars (algebraMap R₀ R') :=
  NatIso.ofComponents (fun X => (baseTensorRestrictLinearEquiv X).toModuleIso) fun {X Y} f => by
    ext t
    exact baseTensorLinearEquiv_naturality (R := R) (R₀ := R₀) (R' := R') f.hom t

section Descent

variable {V W H : Type*} [Category V] [Category W] [Abelian V] [Abelian W] [Category H]
  [HasDerivedCategory W] (F : V ⥤ W) [F.Additive] (G : DerivedCategory W ⥤ H)

/-- A functor of the form `X ↦ G(Q(F X))` factors through the homotopy category. -/
def homotopyDescentIso :
    HomotopyCategory.quotient V (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ G ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso W)) G

end Descent

section SingleTensor

variable {S : Type u} [CommRing S] (N : ModuleCat.{u} S)

/-- The total tensor product with `N` in degree `0` is termwise tensoring with `N`, naturally. -/
def tensorSingleIso :
    (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) :=
  NatIso.ofComponents (fun K =>
    @asIso _ _ _ _ (StacksDraft.TorAmplitude.tensorSingleInclusion N K)
      (StacksDraft.TorAmplitude.tensorSingleInclusion_isIso N K)) fun {K K'} g => by
    ext n : 1
    change (g.f n ▷ N) ≫ HomologicalComplex.ιMapBifunctor K'
        ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N) (curriedTensor (ModuleCat.{u} S))
        (ComplexShape.up ℤ) n 0 n (add_zero n) =
      HomologicalComplex.ιMapBifunctor K ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N)
        (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
        (HomologicalComplex.mapBifunctorMap g
          (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N))
          (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ)).f n
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp
    rfl

/-- In degree `n`, the component of `tensorSingleIso` is the inclusion of the summand
`K n ⊗ N` of the total tensor product. -/
theorem tensorSingleIso_hom_f (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ((tensorSingleIso N).hom.app K).f n =
      HomologicalComplex.ιMapBifunctor K ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).obj N)
        (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ) n 0 n (add_zero n) := rfl

end SingleTensor

section Model

variable (R R₀) in
/-- Base change along a flat algebra preserves quasi-isomorphisms of complexes. -/
theorem quasiIso_baseChangeFunctor_map [Module.Flat R R₀]
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have : (algebraMap R R₀).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have := extendScalars_preservesHomology_of_flat.{u, u} (algebraMap R R₀) this
  have e := NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars R R₀) (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso e (Arrow.mk f))).2
    (inferInstanceAs (QuasiIso
      (((ModuleCat.extendScalars (algebraMap R R₀)).mapHomologicalComplex _).map f)))

variable (R R₀) in
/-- Base change preserves K-flatness of complexes. -/
theorem kFlat_baseChangeFunctor_obj {X : CochainComplex (ModuleCat.{u} R) ℤ} (hX : X.KFlat) :
    CochainComplex.KFlat (((baseChangeFunctor R R₀).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X) :=
  CochainComplex.KFlat.of_iso
    ((NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars R R₀)
      (ComplexShape.up ℤ)).symm.app X)
    (kFlat_baseChange (algebraMap R R₀) X hX)

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- The comparison `(R₀ ⊗_R X) ⊗_{R₀} F ⟶ R' ⊗_R X`, read over `R₀`, induced by `ε`. -/
def baseModelComparison :
    baseModelFunctor R F ⟶
      (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.whiskerLeft ((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ))
      ((tensoringRight _).map ε ≫
        (tensorSingleIso (ModuleCat.of R₀ R')).inv) ≫
    (Functor.mapHomologicalComplexCompIso (baseTensorIso ≪≫
      Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
        (ModuleCat.restrictScalars (algebraMap R₀ R'))) (ComplexShape.up ℤ)).hom ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv

variable [Module.Flat R R₀]

variable {F} in
/-- Base change to `R₀` followed by the tensor product with a K-flat `F` inverts
quasi-isomorphisms. -/
theorem baseModelFunctor_inverts (hF : F.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (baseModelFunctor R F ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have := quasiIso_baseChangeFunctor_map R R₀ f
  have := StacksDraft.TorAmplitude.quasiIso_tensorRight_map hF
    (((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this

variable {F} (hF : F.KFlat)

/-- The functor `D(R) ⥤ D(R₀)`, `X ↦ (R₀ ⊗_R X) ⊗_{R₀} F`, for a K-flat `F`. -/
def baseModelDerived : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R₀) :=
  Localization.lift (baseModelFunctor R F ⋙ DerivedCategory.Q) (baseModelFunctor_inverts hF)
    DerivedCategory.Q

/-- The defining isomorphism of `baseModelDerived`. -/
def baseModelDerivedFac :
    DerivedCategory.Q ⋙ baseModelDerived (R := R) hF ≅ baseModelFunctor R F ⋙ DerivedCategory.Q :=
  Localization.fac _ _ _

/-- The target of the comparison: termwise base change to `R'`, read in `D(R₀)`. -/
abbrev baseModelTarget :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} R₀) :=
  extensionOfScalarsComplexGeneral.{u, u, u, u + 1} (algebraMap R R') ⋙
    (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory

/-- The comparison of `baseModelDerived` with termwise base change to `R'`. -/
def baseModelDerivedComparison :
    DerivedCategory.Q ⋙ baseModelDerived (R := R) hF ⟶
      baseModelTarget (R := R) (R₀ := R₀) (R' := R') :=
  (baseModelDerivedFac hF).hom ≫ Functor.whiskerRight (baseModelComparison F ε) DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv

/-- At a K-flat complex the comparison of `baseModelDerived` is invertible. -/
theorem isIso_baseModelDerivedComparison_app [QuasiIso ε] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) : IsIso ((baseModelDerivedComparison (R := R) ε hF).app K) := by
  have hbc := kFlat_baseChangeFunctor_obj R R₀ hK
  have : QuasiIso
      ((((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ◁ ε) :=
    StacksDraft.TorAmplitude.quasiIso_tensorLeft_map _ hbc ε
  have : IsIso (DerivedCategory.Q.map
      ((((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ◁ ε)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this
  have hc : IsIso (DerivedCategory.Q.map ((baseModelComparison F ε).app K)) := by
    change IsIso (DerivedCategory.Q.map
      ((((baseChangeFunctor R R₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ◁ ε ≫
        (tensorSingleIso (ModuleCat.of R₀ R')).inv.app _ ≫
        (Functor.mapHomologicalComplexCompIso (baseTensorIso ≪≫
          Functor.isoWhiskerRight (baseChangeIsoExtendScalars R R')
            (ModuleCat.restrictScalars (algebraMap R₀ R'))) (ComplexShape.up ℤ)).hom.app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app K))
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    infer_instance
  have h3 : IsIso ((ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) := inferInstance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hc
    (IsIso.comp_isIso' (IsIso.id _) (IsIso.comp_isIso' h3 (IsIso.id _))))


/-- `baseModelDerived` is a left derived functor of termwise base change to `R'`, as soon as
`ε` is a quasi-isomorphism. -/
theorem isLeftDerivedFunctor_baseModelDerived [QuasiIso ε] :
    (baseModelDerived (R := R) hF).IsLeftDerivedFunctor (baseModelDerivedComparison ε hF)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_of_isIso_on_kFlat.{u, u}
    _ _ (homotopyDescentIso (ModuleCat.extendScalars (algebraMap R R'))
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory) _ _
    (isIso_baseModelDerivedComparison_app ε hF)

/-- The comparison of derived base change to `R'`, read in `D(R₀)`, with termwise base change. -/
abbrev derivedBaseChangeRestrictComparison :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory) ⟶
      baseModelTarget (R := R) (R₀ := R₀) (R' := R') :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory

/-- **The model of derived base change.** The comparison from derived base change to `R'`, read
in `D(R₀)`, to `X ↦ (R₀ ⊗_R X) ⊗_{R₀} F`. -/
def baseModelLift [QuasiIso ε] :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
        (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory ⟶
      baseModelDerived (R := R) hF :=
  haveI := isLeftDerivedFunctor_baseModelDerived (R := R) ε hF
  (baseModelDerived (R := R) hF).leftDerivedLift (baseModelDerivedComparison ε hF)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    derivedBaseChangeRestrictComparison

/-- On the image of a complex `X`, `baseModelLift` composed with the comparison of
`baseModelDerived` is the comparison of derived base change to `R'` with termwise base change. -/
theorem baseModelLift_fac [QuasiIso ε] (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj X) ≫
        (baseModelDerivedComparison ε hF).app X =
      (ModuleCat.restrictScalars (algebraMap R₀ R')).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison.app X) := by
  have := isLeftDerivedFunctor_baseModelDerived (R := R) ε hF
  have h := (baseModelDerived (R := R) hF).leftDerived_fac_app (baseModelDerivedComparison ε hF)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    derivedBaseChangeRestrictComparison X
  refine h.trans ?_
  simp

/-- The comparison `baseModelLift` from derived base change to `R'`, read in `D(R₀)`, to
`baseModelDerived` is an isomorphism. -/
instance isIso_baseModelLift [QuasiIso ε] : IsIso (baseModelLift (R := R) ε hF) := by
  have hQ : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ, P.KFlat →
      IsIso ((baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj P)) := by
    intro P hP
    have := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).comparison_isIso_of_kFlat
      P hP
    have := isIso_baseModelDerivedComparison_app (R := R) ε hF P hP
    have h := baseModelLift_fac (R := R) ε hF P
    have h' : IsIso ((baseModelLift (R := R) ε hF).app (DerivedCategory.Q.obj P) ≫
        (baseModelDerivedComparison ε hF).app P) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((baseModelDerivedComparison ε hF).app P)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Z => ?_
  obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u, u + 1} Z
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  exact hQ P hP

end Model

end RingTheory.TorIndependence
