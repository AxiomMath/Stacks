module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveCupDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ShiftedConstantTensor
public import StacksFrontier.CategoryTheory.Adjunction.CupProductDualityCriterion
public import StacksFrontier.Algebra.Homology.DerivedCategory.RelativeTraceMapShift
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness

/-!
# The duality map of a relative curve detects relative duality

Let `f : X ⟶ S` be a morphism of schemes, `ℓ` a natural number and `Λ = ℤ/ℓ`. Write
`E = f⁻¹Λ_S[0]` and `K = Rf_* E` (unbounded). For a trace `t : K ⟶ Λ_S[-2]`, the duality map
`D_t : K ⟶ RHom(K, Λ_S[-2])` detects the bijectivity of the trace maps of relative duality.

## Main definitions

* `Stacks.EtaleCohomology.curveDualityLeftUnitIso`: the isomorphism `E ⊗^L_Λ - ≅ 𝟭`.
* `Stacks.EtaleCohomology.curveDualityMultiplication`: the multiplication `E ⊗^L_Λ E ⟶ E`.

## Main results

* `Stacks.EtaleCohomology.bijective_map_comp_iff_curveDualityMap`: for every `m`,
  `y ↦ t ∘ Rf_*(y)` is bijective on `Hom(f⁻¹(Λ_S[m]), E)` exactly when composition with `D_t` is
  bijective on `Hom(Λ_S[m], K)`.
* `Stacks.EtaleCohomology.isBijectiveAt_of_isIso_curveDualityMap`: if `D_t` is invertible, the
  trace map `Hom(E, E[m]) → Hom(K, Λ_S[m - 2])`, `y ↦ t[m] ∘ Rf_*(y)`, is bijective for every `m`.
* `Stacks.EtaleCohomology.bijective_comp_curveDualityMap_of_isBijectiveAt`: if the trace maps are
  bijective at `E`, composition with `D_t` is bijective on morphisms out of every shift of `Λ_S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

variable (ℓ : ℕ) {S X : Scheme.{u}} (f : X ⟶ S)

/-- `E = f⁻¹Λ_S[0]` read on the constant ringed site of `X` is the unit object `𝒪[0]`. -/
abbrev curveDualityUnitIso :
    (etaleDerivedEquivalence.{u, 0} (ZMod ℓ) X).functor.obj (curveDualityUnit ℓ f) ≅
      Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, 0} (ZMod ℓ) X) :=
  etaleDerivedEquivalenceInverseImageSingleConstantIso.{u, 0} (ZMod ℓ) f

/-- The isomorphism `E ⊗^L_Λ - ≅ 𝟭` on `D(X_étale, Λ)`, for `E = f⁻¹Λ_S[0]`. -/
def curveDualityLeftUnitIso :
    (etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f) ≅ 𝟭 _ :=
  etaleDerivedTensorLeftUnitIso.{u, 0} (ZMod ℓ) X (curveDualityUnitIso ℓ f)

/-- The multiplication `E ⊗^L_Λ E ⟶ E` of `E = f⁻¹Λ_S[0]`: the component at `E` of
`curveDualityLeftUnitIso`. -/
abbrev curveDualityMultiplication :
    ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f :=
  (curveDualityLeftUnitIso ℓ f).hom.app _

/-- The multiplication is an isomorphism. -/
instance isIso_curveDualityMultiplication : IsIso (curveDualityMultiplication ℓ f) :=
  inferInstanceAs (IsIso ((curveDualityLeftUnitIso ℓ f).app _).hom)

/-- The duality map `curveDualityMap` is `Stacks.CupDuality.dualityMap` for the adjunction
`f⁻¹ ⊣ Rf_*`, the tensor–internal-Hom adjunction of `S`, its symmetry and the multiplication
`curveDualityLeftUnitIso`. -/
theorem curveDualityMap_eq_dualityMap
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t =
      Stacks.CupDuality.dualityMap
        (α := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom)
        (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f)
        (etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S)
        (etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S) (curveDualityUnit ℓ f)
        (fun Z => (curveDualityLeftUnitIso ℓ f).hom.app Z) _ t := by
  unfold curveDualityMap curveDualityCup Stacks.CupDuality.dualityMap
  beta_reduce
  with_reducible rfl

/-- The projection map `K ⊗^L Λ_S[m] ⟶ Rf_*(E ⊗^L f⁻¹Λ_S[m]) ⟶ Rf_*(f⁻¹Λ_S[m])` at a shift of `Λ_S`
is invertible. -/
instance isIso_curveDuality_projectionMultiplication (m : ℤ) :
    IsIso (Stacks.CupDuality.projectionMultiplication
      (α := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom)
      (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f) (curveDualityUnit ℓ f)
      (fun Z => (curveDualityLeftUnitIso ℓ f).hom.app Z)
      (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦m⟧)) := by
  have := isEquivalence_etaleTensorRightOf.{u, 0} (ZMod ℓ) S _ m
    (etaleDerivedEquivalenceShiftSingleConstantIso.{u, 0} (ZMod ℓ) S m)
  have := isEquivalence_etaleTensorRightOf.{u, 0} (ZMod ℓ) X _ m
    (etaleDerivedEquivalenceInverseImageShiftIso.{u, 0} (ZMod ℓ) X f m)
  have := Stacks.ProjectionFormula.isIso_adjunctionTensorMap
    (etaleModuleDerivedInverseImageAdj.{u, 0} (ZMod ℓ) f)
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S))
    (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) X))
    (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom (curveDualityUnit ℓ f)
    (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦m⟧) (fun _ ↦ inferInstance)
  unfold Stacks.CupDuality.projectionMultiplication
  infer_instance

/-- For a trace `t : K ⟶ Λ_S[-2]` and every `m`, `y ↦ t ∘ Rf_*(y)` is bijective on
`Hom(f⁻¹(Λ_S[m]), E)` exactly when composition with the duality map `D_t` is bijective on
`Hom(Λ_S[m], K)`. -/
theorem bijective_map_comp_iff_curveDualityMap
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) (m : ℤ) :
    Function.Bijective (fun y : (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) f).obj
        (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦m⟧) ⟶
          curveDualityUnit ℓ f =>
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map y ≫ t) ↔
      Function.Bijective (fun z : ((DerivedCategory.singleFunctor _ 0).obj
          (unitSheaf (X := S) ℓ))⟦m⟧ ⟶ curveDualityComplex ℓ f =>
        z ≫ curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t) := by
  rw [curveDualityMap_eq_dualityMap]
  refine Stacks.CupDuality.bijective_comp_map_iff
    (α := (etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) f).hom) _ _ _ _ t
    (fun A _ _ g ↦ etaleDerivedTensorBraidingIso_naturality.{u, 0} (ZMod ℓ) S A g)
    (fun {Z Z'} y ↦ ?_) _
  simpa using (curveDualityLeftUnitIso ℓ f).hom.naturality y

/-- Composition with an isomorphism is bijective. -/
lemma bijective_comp_of_isIso' {C : Type*} [Category C] {A B B' : C} (g : B ⟶ B') [IsIso g] :
    Function.Bijective (fun z : A ⟶ B => z ≫ g) :=
  ⟨fun _ _ h ↦ (cancel_mono g).1 h, fun z ↦ ⟨z ≫ inv g, by simp⟩⟩

/-- The two sides of the trace map of relative duality, in degree `m` at `E` and in degree `0`
at `f⁻¹(Λ_S[-m])`, are bijective together. -/
theorem bijective_traceMap_iff_curveDuality
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (m c : ℤ) (h : -2 + m = c) :
    letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
    haveI := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
    Function.Bijective (traceMap (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) t
        (curveDualityUnit ℓ f) m c h) ↔
      Function.Bijective (fun z : ((DerivedCategory.singleFunctor _ 0).obj
          (unitSheaf (X := S) ℓ))⟦-m⟧ ⟶ curveDualityComplex ℓ f =>
        z ≫ curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t) := by
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
  rw [← Stacks.RelativeDuality.bijective_traceMap_iff_of_isIso
      (Φ := etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) t
      (((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) f).commShiftIso (-m)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)))
      (m' := 0) (by omega) h (add_zero _) (by omega),
    Stacks.RelativeDuality.bijective_traceMap_zero_iff]
  exact bijective_map_comp_iff_curveDualityMap ℓ f t (-m)

/-- If the duality map `D_t : K ⟶ RHom(K, Λ_S[-2])` is an isomorphism, the trace map
`Hom(E, E[m]) → Hom(K, Λ_S[m - 2])`, `y ↦ t[m] ∘ Rf_*(y)`, is bijective for every `m`. -/
theorem isBijectiveAt_of_isIso_curveDualityMap
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    [IsIso (curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t)] :
    letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
    haveI := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
    IsBijectiveAt (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) t
      (curveDualityUnit ℓ f) :=
  fun m c h ↦ (bijective_traceMap_iff_curveDuality ℓ f t m c h).2 (bijective_comp_of_isIso' _)

/-- If the trace maps of relative duality are bijective at `E`, composition with `D_t` is bijective
on `Hom(Λ_S[m], K)` for every `m`. -/
theorem bijective_comp_curveDualityMap_of_isBijectiveAt
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, 0} (ZMod ℓ) f
      haveI := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, 0} (ZMod ℓ) f
      IsBijectiveAt (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f) t
        (curveDualityUnit ℓ f)) (m : ℤ) :
    Function.Bijective (fun z : ((DerivedCategory.singleFunctor _ 0).obj
        (unitSheaf (X := S) ℓ))⟦m⟧ ⟶ curveDualityComplex ℓ f =>
      z ≫ curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t) := by
  have := (bijective_traceMap_iff_curveDuality ℓ f t (-m) (-2 + -m) rfl).1 (ht _ _ _)
  rwa [neg_neg] at this

end Stacks.EtaleCohomology

end
