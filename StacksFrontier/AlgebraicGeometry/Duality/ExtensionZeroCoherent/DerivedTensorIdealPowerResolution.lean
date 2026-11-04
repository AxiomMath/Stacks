module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerMap

/-!
# The system `(𝓕^• ⊗^L 𝓘^n)_n` computed on a K-flat resolution

For a quasi-isomorphism `π : 𝓟^• ⟶ 𝓕^•` from a K-flat complex, the inverse system
`(𝓕^• ⊗^L 𝓘^n)_n` of `AlgebraicGeometry.derivedTensorIdealPowerSystem` is isomorphic to the system
of total tensor complexes `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n`, compatibly with the canonical maps to
`(𝓘^n 𝓕^•)_n`: under the isomorphism the canonical maps become the classes of the maps of complexes
`AlgebraicGeometry.idealPowerResolutionMap`.

## Main definitions

* `AlgebraicGeometry.derivedTensorResolutionIso`: the isomorphism of inverse systems.

## Main results

* `AlgebraicGeometry.derivedTensorResolutionIso_hom_comp`: its compatibility with the canonical
  maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) {F : CochainComplex X.Modules ℤ}
  {P : Stacks.Duality.TensorComplex X} (hP : Stacks.Duality.KFlatComplex P)
  (π : P ⟶ (show Stacks.Duality.TensorComplex X from F))

/-- The isomorphism `𝓕^• ⊗^L 𝓘^n ≅ Tot(𝓟^• ⊗ 𝓘^n[0])` at the stage `n`. -/
public def derivedTensorResolutionIsoApp [IsIso (DerivedCategory.Q.map π)] (n : ℕ) :
    (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).obj (op n) ≅
      DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex P (idealPowerSingle I n)) :=
  (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.mapIso
      (asIso (DerivedCategory.Q.map π))).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n))).symm ≪≫
    ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj
      (DerivedCategory.Q.obj P)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app (idealPowerSheaf I n)) ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonLeft P
      (idealPowerSingle I n) hP

/-- At each stage, the canonical map is the class of `AlgebraicGeometry.idealPowerResolutionMap`
through `AlgebraicGeometry.derivedTensorResolutionIsoApp`. -/
public lemma derivedTensorIdealPowerMap_eq_resolutionIsoApp [IsIso (DerivedCategory.Q.map π)]
    (n : ℕ) :
    derivedTensorIdealPowerMap I n F =
      (derivedTensorResolutionIsoApp I hP π n).hom ≫
        DerivedCategory.Q.map (idealPowerResolutionMap I n π) := by
  have h := derivedTensorIdealPowerMap_eq_of_kFlat I n F P hP π
  let e := ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.mapIso
    (asIso (DerivedCategory.Q.map π))).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n))
  refine (e.inv_hom_id_assoc _).symm.trans ((congrArg (e.inv ≫ ·) h).trans ?_)
  exact (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ DerivedCategory.Q.map (idealPowerResolutionMap I n π))
      (Category.assoc _ _ _)))

/-- The stagewise isomorphisms commute with the transitions. -/
public lemma derivedTensorResolutionIsoApp_naturality [IsIso (DerivedCategory.Q.map π)] (n : ℕ) :
    (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).map (homOfLE (Nat.le_succ n)).op ≫
        (derivedTensorResolutionIsoApp I hP π n).hom =
      (derivedTensorResolutionIsoApp I hP π (n + 1)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P)
          (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ)) := by
  let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
  let GF := T.tensor.obj (DerivedCategory.Q.obj F)
  let GP := T.tensor.obj (DerivedCategory.Q.obj P)
  let a := (DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)
  let g := DerivedCategory.Q.map (idealPowerSingleTransition I n)
  let s₀ := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)
  let s₁ := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app
    (idealPowerSheaf I (n + 1))
  let e₀ := (T.tensor.mapIso (asIso (DerivedCategory.Q.map π))).app
    ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n))
  let e₁ := (T.tensor.mapIso (asIso (DerivedCategory.Q.map π))).app
    ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I (n + 1)))
  let c₀ := (T.comparisonLeft P (idealPowerSingle I n) hP).hom
  let c₁ := (T.comparisonLeft P (idealPowerSingle I (n + 1)) hP).hom
  let mb := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P)
    (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (ComplexShape.up ℤ))
  have hmap : (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).map
      (homOfLE (Nat.le_succ n)).op = GF.map a :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  have h₁ : GF.map a ≫ e₀.inv = e₁.inv ≫ GP.map a :=
    ((T.tensor.mapIso (asIso (DerivedCategory.Q.map π))).inv.naturality a)
  have h₂ : a ≫ s₀ = s₁ ≫ g :=
    (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.naturality
      (idealPowerSheafTransition I n)
  have h₃ : GP.map g ≫ c₀ = c₁ ≫ mb := by
    have h := T.comparisonLeft_naturality (𝟙 P) (idealPowerSingleTransition I n) hP hP
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
    exact h
  rw [hmap]
  show GF.map a ≫ e₀.inv ≫ GP.map s₀ ≫ c₀ = (e₁.inv ≫ GP.map s₁ ≫ c₁) ≫ mb
  have k₁ : GF.map a ≫ e₀.inv ≫ GP.map s₀ ≫ c₀ = e₁.inv ≫ GP.map (a ≫ s₀) ≫ c₀ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ GP.map s₀ ≫ c₀) h₁).trans
      ((Category.assoc _ _ _).trans (congrArg (e₁.inv ≫ ·)
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ c₀) (GP.map_comp a s₀).symm)))))
  have k₂ : e₁.inv ≫ GP.map (a ≫ s₀) ≫ c₀ = e₁.inv ≫ GP.map s₁ ≫ (GP.map g ≫ c₀) :=
    (congrArg (fun x => e₁.inv ≫ GP.map x ≫ c₀) h₂).trans
      (congrArg (e₁.inv ≫ ·) ((congrArg (· ≫ c₀) (GP.map_comp s₁ g)).trans
        (Category.assoc _ _ _)))
  have k₃ : e₁.inv ≫ GP.map s₁ ≫ (GP.map g ≫ c₀) = (e₁.inv ≫ GP.map s₁ ≫ c₁) ≫ mb :=
    (congrArg (fun x => e₁.inv ≫ GP.map s₁ ≫ x) h₃).trans
      ((congrArg (e₁.inv ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)
  exact k₁.trans (k₂.trans k₃)

/-- The stagewise isomorphisms, as a map of inverse systems. -/
public def derivedTensorResolutionHom [IsIso (DerivedCategory.Q.map π)] :
    derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F) ⟶
      idealPowerResolutionSystem I P ⋙ DerivedCategory.Q :=
  NatTrans.ofOpSequence (fun n => (derivedTensorResolutionIsoApp I hP π n).hom) fun n =>
    (derivedTensorResolutionIsoApp_naturality I hP π n).trans
      (congrArg ((derivedTensorResolutionIsoApp I hP π (n + 1)).hom ≫ ·)
        (congrArg DerivedCategory.Q.map (Functor.ofOpSequence_map_homOfLE_succ
          (X := fun n => Stacks.Duality.totalTensorComplex P (idealPowerSingle I n))
          (fun n => HomologicalComplex.mapBifunctorMap (𝟙 P) (idealPowerSingleTransition I n)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) n).symm))

/-- The stagewise maps are isomorphisms. -/
public instance isIso_derivedTensorResolutionHom [IsIso (DerivedCategory.Q.map π)] :
    IsIso (derivedTensorResolutionHom I hP π) := by
  have : ∀ n, IsIso ((derivedTensorResolutionHom I hP π).app n) := fun n => by
    obtain ⟨n⟩ := n
    change IsIso (derivedTensorResolutionIsoApp I hP π n).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The system `(𝓕^• ⊗^L 𝓘^n)_n` is the system `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n`** for a K-flat complex
`𝓟^•` quasi-isomorphic to `𝓕^•` through `π`. -/
public def derivedTensorResolutionIso [IsIso (DerivedCategory.Q.map π)] :
    derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F) ≅
      idealPowerResolutionSystem I P ⋙ DerivedCategory.Q :=
  asIso (derivedTensorResolutionHom I hP π)

/-- **Under `derivedTensorResolutionIso`, the canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` are the
classes of the maps of complexes `AlgebraicGeometry.idealPowerResolutionMap`.** -/
public lemma derivedTensorResolutionIso_hom_comp [IsIso (DerivedCategory.Q.map π)] :
    derivedTensorIdealPowerNatTrans I F =
      (derivedTensorResolutionIso I hP π).hom ≫
        Functor.whiskerRight (idealPowerResolutionNatTrans I π) DerivedCategory.Q := by
  ext n : 2
  obtain ⟨n⟩ := n
  exact (derivedTensorIdealPowerNatTrans_app I F n).trans
    (derivedTensorIdealPowerMap_eq_resolutionIsoApp I hP π n)

end AlgebraicGeometry

end
