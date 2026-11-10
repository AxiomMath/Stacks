module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentChartCover

/-!
# Flat base change of tangent modules of an algebraic stack

For an algebraic stack `𝒳` locally of finite presentation over `S`, an object `x` over `Spec A`
and a flat `A`-algebra `C`, the map of Stacks 07YA induces `C ⊗_A T_x(M) ≅ T_y(C ⊗_A M)` for
`y = x|_{Spec C}` (Stacks 0DNT). The proof is the first paragraph of the source: over a
faithfully flat finitely presented chart cover `A → A₁` the object `x` becomes a chart point
(`AlgebraicGeometry.Stack.GroupoidLift.exists_chartPoint_cover`), where flat base change holds
(`Deformation.Artin.ChartLift.isTangentBaseChangeIso_chart_tensor`), and the rows
`T_x(M) → T_{x₁}(M₁) ⇉ T_{x₂}(M₂)` are exact by the sheaf property of lift classes
(`Deformation.Artin.liftClassRowExact_of_tensorProduct`), so the diagram chase
`Deformation.Artin.isTangentBaseChangeIso_of_equalizer` concludes.

## Main results

* `Deformation.Artin.isTangentBaseChangeIso_of_tensorCover`: flat base change descends along an
  fppf tensor cover. The assembly over a chart cover,
  `Deformation.Artin.isTangentBaseChangeIso_of_isAlgebraicStack`, is in
  `StacksFrontier.Deformation.Artin.Infinitesimal.TangentFlatBaseChangeStack`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits AlgebraicGeometry
open AlgebraicGeometry.Stack AlgebraicGeometry.Stack.GroupoidLift
open AlgebraicGeometry.Stack.GroupoidLift.StackChart AlgebraicGeometry.Space.ChartDescent

namespace Deformation.Artin

universe w u

/-! ### The chart cover over `Spec A` -/

section Base

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- The isomorphism `Γ(Spec A) → A`. -/
noncomputable abbrev fromRingOf : ringOf B S hS (algebraOver A B S hS toS hA) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

/-- The isomorphism `fromRingOf : Γ(Spec A) → A` is bijective. -/
theorem fromRingOf_bijective :
    Function.Bijective (fromRingOf (B := B) (S := S) (hS := hS) (toS := toS) (hA := hA)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom

variable {X : SmallAlg (ringOf B S hS (algebraOver A B S hS toS hA)) B.cutoff} [Algebra A X.obj]
  (hAX : ∀ r, algebraMap A X.obj (fromRingOf r) =
    algebraMap (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj r)

include hAX in
/-- If `A` acts on the chart point `X` compatibly with `fromRingOf`, then `A → X` is the
structure map `Γ(Spec A) → X` precomposed with `A → Γ(Spec A)`. -/
theorem algebraMap_eq_of_fromRingOf :
    algebraMap A X.obj = (algebraMap (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj).comp
      (ChartLift.toRingOf A toS hA) := by
  ext a
  rw [RingHom.comp_apply, ← hAX]
  congr 1
  exact (congrArg (fun φ ↦ φ.hom a) (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id).symm

include hAX in
/-- The structure morphism of a chart point over `Spec A` factors through `Spec A`. -/
theorem specMap_comp_toS_eq_toSOf' :
    Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) ≫ toS = ChartLift.toSOf X := by
  rw [algebraMap_eq_of_fromRingOf hAX]
  exact ChartLift.specMap_comp_toS_eq_toSOf X

include hAX in
/-- The map `Spec X → Spec A` of a chart point is its structure morphism to `T' = Spec A`. -/
theorem algebraOverMapOfRingHom_eq_specOverToBase :
    algebraOverMapOfRingHom (algebraMap A X.obj) B S hS toS (ChartLift.toSOf X) hA
      (contains_spec X) (specMap_comp_toS_eq_toSOf' hAX) = specOverToBase X := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  change Spec.map (CommRingCat.ofHom (algebraMap A X.obj)) = specToBase X
  rw [specToBase, algebraMap_eq_of_fromRingOf hAX]
  have h1 : ((BigFppfOver.toScheme B S hS).obj (algebraOver A B S hS toS hA)).isoSpec.inv =
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
    Scheme.isoSpec_Spec_inv (CommRingCat.of A)
  rw [h1, CommRingCat.ofHom_comp, Spec.map_comp]
  rfl

include hAX in
/-- A faithfully flat finitely presented chart cover is flat, surjective and locally of finite
presentation over `Spec A`. -/
theorem specMap_algebraMap_fppf
    [Module.FaithfullyFlat (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj]
    [Algebra.FinitePresentation (ringOf B S hS (algebraOver A B S hS toS hA)) X.obj] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A X.obj))) := by
  have hb : Function.Bijective (ChartLift.toRingOf A toS hA (B := B) (hS := hS)) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv
  have hFF : (algebraMap A X.obj).FaithfullyFlat := by
    rw [algebraMap_eq_of_fromRingOf hAX]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ (.of_bijective hb)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hFP : (algebraMap A X.obj).FinitePresentation := by
    rw [algebraMap_eq_of_fromRingOf hAX]
    exact RingHom.FinitePresentation.comp
      (RingHom.finitePresentation_algebraMap.mpr inferInstance) (.of_bijective hb)
  obtain ⟨h1, h2⟩ :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A X.obj))).mpr hFF
  exact ⟨h1, h2, HasRingHomProperty.Spec_iff.mpr hFP⟩

end Base

/-! ### Cancelling a base change -/

/-- `R ⊗_C (C ⊗_A M) ≅ R ⊗_A M`, as additive groups. -/
noncomputable def cancelTensorAddEquiv (A C R : Type u) [CommRing A] [CommRing C] [CommRing R]
    [Algebra A C] [Algebra C R] [Algebra A R] [IsScalarTower A C R] (M : Type u)
    [AddCommGroup M] [Module A M] : R ⊗[C] (C ⊗[A] M) ≃+ R ⊗[A] M :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A C R R M).toAddEquiv

/-- `cancelTensorAddEquiv` sends `r ⊗ (c ⊗ m)` to `(c • r) ⊗ m`. -/
theorem cancelTensorAddEquiv_tmul (A C R : Type u) [CommRing A] [CommRing C] [CommRing R]
    [Algebra A C] [Algebra C R] [Algebra A R] [IsScalarTower A C R] (M : Type u)
    [AddCommGroup M] [Module A M] (r : R) (c : C) (m : M) :
    cancelTensorAddEquiv A C R M (r ⊗ₜ (c ⊗ₜ m)) = (c • r) ⊗ₜ m := rfl

/-! ### The rings `C → C ⊗_A A₁ ⇉ C ⊗_A A₂` -/

section TensorRings

open TensorProduct

variable (A A₁ C : Type u) [CommRing A] [CommRing A₁] [CommRing C] [Algebra A A₁] [Algebra A C]

/-- `C ⊗_A (A₁ ⊗_A A₁) = (A₁ ⊗_A C) ⊗_C (A₁ ⊗_A C)`, as a pushout of commutative rings. -/
theorem isPushout_tensor_doubleOverlap :
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁) (B := C)
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁ ⊗[A] A₁) (B := C)
    IsPushout (CommRingCat.ofHom (algebraMap C (A₁ ⊗[A] C)))
      (CommRingCat.ofHom (algebraMap C (A₁ ⊗[A] C)))
      (CommRingCat.ofHom (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁) (B := C)
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁ ⊗[A] A₁) (B := C)
  have h := CommRingCat.isPushout_tensorProduct A A₁ C
  have h₂ := CommRingCat.isPushout_tensorProduct A A₁ A₁
  have hout := CommRingCat.isPushout_tensorProduct A (A₁ ⊗[A] A₁) C
  have hb : IsPushout (CommRingCat.ofHom (S := A₁ ⊗[A] A₁)
        Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := A₁ ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := (A₁ ⊗[A] A₁) ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) := by
    refine IsPushout.of_left ?_ ?_ h
    · have e1 : CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom (S := A₁ ⊗[A] A₁)
          Algebra.TensorProduct.includeLeftRingHom =
          CommRingCat.ofHom (algebraMap A (A₁ ⊗[A] A₁)) := by
        apply CommRingCat.hom_ext; ext r; rfl
      have e2 : CommRingCat.ofHom (S := A₁ ⊗[A] C) Algebra.TensorProduct.includeRight.toRingHom ≫
          CommRingCat.ofHom (Algebra.TensorProduct.map
            (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom =
          CommRingCat.ofHom (S := (A₁ ⊗[A] A₁) ⊗[A] C)
            Algebra.TensorProduct.includeRight.toRingHom := by
        apply CommRingCat.hom_ext; ext c
        change (Algebra.TensorProduct.includeLeft (R := A) (S := A) (B := A₁) (1 : A₁)) ⊗ₜ[A] c =
          (1 : A₁ ⊗[A] A₁) ⊗ₜ[A] c
        rw [map_one]
      rw [e1, e2]
      exact hout
    · apply CommRingCat.hom_ext; ext x
      rfl
  refine isPushout_doubleOverlap h h₂ hb ?_ ?_
  · apply CommRingCat.hom_ext; ext x
    rfl
  · apply CommRingCat.hom_ext; ext c
    change (Algebra.TensorProduct.includeRight (R := A) (A := A₁) (B := A₁) (1 : A₁)) ⊗ₜ[A] c =
      (Algebra.TensorProduct.includeLeft (R := A) (S := A) (B := A₁) (1 : A₁)) ⊗ₜ[A] c
    rw [map_one, map_one]

end TensorRings

/-! ### The row of lift classes over `C` -/

/-- Base change along `g : A₁ → A₂` fixes the unit tensor `1 ⊗ c` of `A₁ ⊗_A C`. -/
private theorem map_tmul_one_left {A A₁ A₂ C : Type u} [CommRing A] [CommRing A₁] [CommRing A₂]
    [CommRing C] [Algebra A A₁] [Algebra A A₂] [Algebra A C] (g : A₁ →ₐ[A] A₂) (c : C) :
    (Algebra.TensorProduct.map g (AlgHom.id A C)) ((1 : A₁) ⊗ₜ[A] c) = (1 : A₂) ⊗ₜ[A] c := by
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/-- `cancelTensorAddEquiv` turns `r ⊗ n` into `r • ψ n` when `ψ` sends `c ⊗ m` to `c ⊗ m`. -/
private theorem cancelTensorAddEquiv_tmul_eq_smul (A C R M : Type u) [CommRing A] [CommRing C]
    [CommRing R] [Algebra A C] [Algebra C R] [Algebra A R] [IsScalarTower A C R] [AddCommGroup M]
    [Module A M] (ψ : C ⊗[A] M →+ R ⊗[A] M)
    (hψ : ∀ (c : C) (m : M), ψ (c ⊗ₜ m) = algebraMap C R c ⊗ₜ m)
    (r : R) (n : C ⊗[A] M) : cancelTensorAddEquiv A C R M (r ⊗ₜ[C] n) = r • ψ n := by
  induction n using TensorProduct.inductionOn with
  | tmul c m =>
    rw [cancelTensorAddEquiv_tmul, hψ, TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def,
      mul_comm]
  | add n n' h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, smul_add]

section RowBase

open TensorProduct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A A₁ C : Type u} [CommRing A] [CommRing A₁] [CommRing C] [Algebra A A₁] [Algebra A C]
  {toSC : Spec (.of C) ⟶ S} {toSC₁ : Spec (.of (A₁ ⊗[A] C)) ⟶ S}
  {toSC₂ : Spec (.of ((A₁ ⊗[A] A₁) ⊗[A] C)) ⟶ S}
  {hC : B.Contains (Spec (.of C))} {hC₁ : B.Contains (Spec (.of (A₁ ⊗[A] C)))}
  {hC₂ : B.Contains (Spec (.of ((A₁ ⊗[A] A₁) ⊗[A] C)))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom) ≫ toSC = toSC₁}
  {hfa : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) ≫
      toSC₁ = toSC₂}
  {hfb : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) ≫
      toSC₁ = toSC₂}
  {y y₁ y₂ : 𝒳.val.obj}
  {hy : 𝒳.val.p.obj y = algebraOver C B S hS toSC hC}
  {hy₁ : 𝒳.val.p.obj y₁ = algebraOver (A₁ ⊗[A] C) B S hS toSC₁ hC₁}
  {hy₂ : 𝒳.val.p.obj y₂ = algebraOver ((A₁ ⊗[A] A₁) ⊗[A] C) B S hS toSC₂ hC₂}
  {φ₀₁ : y₁ ⟶ y}
  {hφ₀₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom B S hS toSC toSC₁ hC hC₁
      hf₀₁) φ₀₁}
  {α β : y₂ ⟶ y₁}
  {hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom
      B S hS toSC₁ toSC₂ hC₁ hC₂ hfa) α}
  {hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom
      B S hS toSC₁ toSC₂ hC₁ hC₂ hfb) β}
  {M : SiteModule A B}

/-- **The row of lift classes over `C` is exact** along `C → A₁ ⊗_A C ⇉ (A₁ ⊗_A A₁) ⊗_A C`,
with the coefficients `C ⊗_A M`, `(A₁ ⊗_A C) ⊗_A M`, `((A₁ ⊗_A A₁) ⊗_A C) ⊗_A M`, as soon as
`Spec A₁ → Spec A` is flat, surjective and locally of finite presentation. -/
theorem liftClassRowExact_of_tensorProduct_base (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hf : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hFl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hSu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hLp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hN : IsSiteModule C B (ModuleCat.of C (C ⊗[A] M.obj)))
    (hN₁ : IsSiteModule (A₁ ⊗[A] C) B (ModuleCat.of (A₁ ⊗[A] C) ((A₁ ⊗[A] C) ⊗[A] M.obj)))
    (hN₂ : IsSiteModule ((A₁ ⊗[A] A₁) ⊗[A] C) B
      (ModuleCat.of ((A₁ ⊗[A] A₁) ⊗[A] C) (((A₁ ⊗[A] A₁) ⊗[A] C) ⊗[A] M.obj)))
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) :
    LiftClassRowExact 𝒳.isFiberedInGroupoids hφ₀₁ hα hβ (M := ⟨_, hN⟩) (M₁ := ⟨_, hN₁⟩)
      (M₂ := ⟨_, hN₂⟩)
      (tensorCoeffMap (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C) M.obj)
      (tensorCoeffMap (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)) M.obj)
      (tensorCoeffMap (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)) M.obj)
      (hx := hy) (hx₁ := hy₁) (hx₂ := hy₂) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁) (B := C)
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁ ⊗[A] A₁) (B := C)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A A₁ C)
  have ha : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁)
      (AlgHom.id A C)).toRingHom.comp (algebraMap C (A₁ ⊗[A] C)) =
      algebraMap C ((A₁ ⊗[A] A₁) ⊗[A] C) := RingHom.ext fun c ↦ map_tmul_one_left _ c
  have hb : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁)
      (AlgHom.id A C)).toRingHom.comp (algebraMap C (A₁ ⊗[A] C)) =
      algebraMap C ((A₁ ⊗[A] A₁) ⊗[A] C) := RingHom.ext fun c ↦ map_tmul_one_left _ c
  have hψab : ∀ n : C ⊗[A] M.obj,
      restrictScalarsAddHom _ (tensorCoeffMap (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)) M.obj)
        (restrictScalarsAddHom _ (tensorCoeffMap
          (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C) M.obj) n) =
      restrictScalarsAddHom _ (tensorCoeffMap (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)) M.obj)
        (restrictScalarsAddHom _ (tensorCoeffMap
          (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C) M.obj) n) := fun n ↦ by
    induction n using TensorProduct.inductionOn with
    | tmul c m =>
      change TensorProduct.map _ LinearMap.id (TensorProduct.map _ LinearMap.id (c ⊗ₜ m)) =
        TensorProduct.map _ LinearMap.id (TensorProduct.map _ LinearMap.id (c ⊗ₜ m))
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.includeRight_apply, map_tmul_one_left]
    | add n n' h₁ h₂ => simp only [map_add, h₁, h₂]
  refine liftClassRowExact_of_tensor h𝒳 f hf ?_ ?_ ?_ ?_ ha hb
    (cancelTensorAddEquiv A C (A₁ ⊗[A] C) M.obj) ?_
    (cancelTensorAddEquiv A C ((A₁ ⊗[A] A₁) ⊗[A] C) M.obj) ?_ hψab hγ
  · exact MorphismProperty.of_isPullback hpb hFl
  · exact MorphismProperty.of_isPullback hpb hSu
  · exact MorphismProperty.of_isPullback hpb hLp
  · exact isPushout_tensor_doubleOverlap A A₁ C
  · exact cancelTensorAddEquiv_tmul_eq_smul A C _ _ _ (fun _ _ ↦ rfl)
  · refine cancelTensorAddEquiv_tmul_eq_smul A C _ _
      ((restrictScalarsAddHom _ (tensorCoeffMap (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)) M.obj)).comp
        (restrictScalarsAddHom _ (tensorCoeffMap
          (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C) M.obj))) (fun c m ↦ ?_)
    exact congrArg (· ⊗ₜ[A] m) (map_tmul_one_left _ c)

end RowBase

/-! ### The diagram chase over a tensor cover -/

section TensorCover

open TensorProduct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {A A₁ C : Type u} [CommRing A] [CommRing A₁] [CommRing C] [Algebra A A₁] [Algebra A C]
  {toS : Spec (.of A) ⟶ S} {toS₁ : Spec (.of A₁) ⟶ S} {toS₂ : Spec (.of (A₁ ⊗[A] A₁)) ⟶ S}
  {toSC : Spec (.of C) ⟶ S} {toSC₁ : Spec (.of (A₁ ⊗[A] C)) ⟶ S}
  {toSC₂ : Spec (.of ((A₁ ⊗[A] A₁) ⊗[A] C)) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hA₁ : B.Contains (Spec (.of A₁))}
  {hA₂ : B.Contains (Spec (.of (A₁ ⊗[A] A₁)))}
  {hC : B.Contains (Spec (.of C))} {hC₁ : B.Contains (Spec (.of (A₁ ⊗[A] C)))}
  {hC₂ : B.Contains (Spec (.of ((A₁ ⊗[A] A₁) ⊗[A] C)))}
  {hf₀₁ : Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ toS = toS₁}
  {hfa : Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁).toRingHom) ≫ toS₁ = toS₂}
  {hfb : Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁).toRingHom) ≫ toS₁ = toS₂}
  {hf : Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ toS = toSC}
  {hf₁ : Spec.map (CommRingCat.ofHom (algebraMap A₁ (A₁ ⊗[A] C))) ≫ toS₁ = toSC₁}
  {hf₂ : Spec.map (CommRingCat.ofHom (algebraMap (A₁ ⊗[A] A₁) ((A₁ ⊗[A] A₁) ⊗[A] C))) ≫ toS₂ =
    toSC₂}
  {hfc₀₁ : Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom) ≫ toSC = toSC₁}
  {hfa' : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) ≫
      toSC₁ = toSC₂}
  {hfb' : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom) ≫
      toSC₁ = toSC₂}
  {x x₁ x₂ y y₁ y₂ : 𝒳.val.obj}
  {hx : 𝒳.val.p.obj x = algebraOver A B S hS toS hA}
  {hx₁ : 𝒳.val.p.obj x₁ = algebraOver A₁ B S hS toS₁ hA₁}
  {hx₂ : 𝒳.val.p.obj x₂ = algebraOver (A₁ ⊗[A] A₁) B S hS toS₂ hA₂}
  {hy : 𝒳.val.p.obj y = algebraOver C B S hS toSC hC}
  {hy₁ : 𝒳.val.p.obj y₁ = algebraOver (A₁ ⊗[A] C) B S hS toSC₁ hC₁}
  {hy₂ : 𝒳.val.p.obj y₂ = algebraOver ((A₁ ⊗[A] A₁) ⊗[A] C) B S hS toSC₂ hC₂}
  {φ₀₁ : x₁ ⟶ x}
  {hφ₀₁ : 𝒳.val.p.IsHomLift
    (algebraOverMapOfRingHom (algebraMap A A₁) B S hS toS toS₁ hA hA₁ hf₀₁) φ₀₁}
  {α β : x₂ ⟶ x₁}
  {hα : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁).toRingHom
      B S hS toS₁ toS₂ hA₁ hA₂ hfa) α}
  {hβ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁).toRingHom
      B S hS toS₁ toS₂ hA₁ hA₂ hfb) β}
  {φ : y ⟶ x}
  {hφ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A C) B S hS toS toSC hA hC hf) φ}
  {φ₁ : y₁ ⟶ x₁}
  {hφ₁ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (algebraMap A₁ (A₁ ⊗[A] C))
    B S hS toS₁ toSC₁ hA₁ hC₁ hf₁) φ₁}
  {φ₂ : y₂ ⟶ x₂}
  {hφ₂ : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
    (algebraMap (A₁ ⊗[A] A₁) ((A₁ ⊗[A] A₁) ⊗[A] C)) B S hS toS₂ toSC₂ hA₂ hC₂ hf₂) φ₂}
  {φ₀₁' : y₁ ⟶ y}
  {hφ₀₁' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom
      B S hS toSC toSC₁ hC hC₁ hfc₀₁) φ₀₁'}
  {α' β' : y₂ ⟶ y₁}
  {hα' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom
      B S hS toSC₁ toSC₂ hC₁ hC₂ hfa') α'}
  {hβ' : 𝒳.val.p.IsHomLift (algebraOverMapOfRingHom (Algebra.TensorProduct.map
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁) (AlgHom.id A C)).toRingHom
      B S hS toSC₁ toSC₂ hC₁ hC₂ hfb') β'}
  {M : SiteModule A B} {hN : IsSiteModule C B (ModuleCat.of C (C ⊗[A] M.obj))}
  {F : TangentFunctorData A B S hS toS hA 𝒳.val.p x hx}
  {F₁ : TangentFunctorData A₁ B S hS toS₁ hA₁ 𝒳.val.p x₁ hx₁}
  {F₂ : TangentFunctorData (A₁ ⊗[A] A₁) B S hS toS₂ hA₂ 𝒳.val.p x₂ hx₂}
  {G : TangentFunctorData C B S hS toSC hC 𝒳.val.p y hy}
  {G₁ : TangentFunctorData (A₁ ⊗[A] C) B S hS toSC₁ hC₁ 𝒳.val.p y₁ hy₁}
  {G₂ : TangentFunctorData ((A₁ ⊗[A] A₁) ⊗[A] C) B S hS toSC₂ hC₂ 𝒳.val.p y₂ hy₂}

include hφ₀₁ hα hβ hφ₀₁' hα' hβ' in
/-- **Flat base change descends along a tensor cover.** Let `A → A₁` be flat, surjective and
locally of finite presentation on spectra, `A₂ = A₁ ⊗_A A₁`, `C` a flat `A`-algebra with
`C₁ = A₁ ⊗_A C`, `C₂ = A₂ ⊗_A C`, and let `x ← x₁ ⇇ x₂`, `y ← y₁ ⇇ y₂` be compatible objects over
these rings. If the tangent modules of `x₁` and `x₂` commute with the base changes `A₁ → C₁` and
`A₂ → C₂`, then those of `x` commute with `A → C`, for the coefficients `C ⊗_A M`. -/
theorem isTangentBaseChangeIso_of_tensorCover [Module.Flat A C]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ Stack.schemeFibredCategory B S hS (Over.mk (𝟙 (B.obj hS))))
    (hfS : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B S hS g) f)
    (hFl : Flat (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hSu : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hLp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A A₁))))
    (hγ : α ≫ φ₀₁ = β ≫ φ₀₁) (hγ' : α' ≫ φ₀₁' = β' ≫ φ₀₁')
    (hsq₀₁ : φ₀₁' ≫ φ = φ₁ ≫ φ₀₁) (hsqa : α' ≫ φ₁ = φ₂ ≫ α) (hsqb : β' ≫ φ₁ = φ₂ ≫ β)
    (h₁ : IsTangentBaseChangeIso 𝒳.isFiberedInGroupoids hf₁ φ₁ hφ₁ F₁ G₁
      (M := ⟨_, isSiteModule_tensor hA₁ M⟩) (N := ⟨_, isSiteModule_tensor hC₁ M⟩)
      (tensorCoeffMap (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] C) M.obj))
    (h₂ : IsTangentBaseChangeIso 𝒳.isFiberedInGroupoids hf₂ φ₂ hφ₂ F₂ G₂
      (M := ⟨_, isSiteModule_tensor hA₂ M⟩) (N := ⟨_, isSiteModule_tensor hC₂ M⟩)
      (tensorCoeffMap (Algebra.TensorProduct.includeLeft :
        A₁ ⊗[A] A₁ →ₐ[A] (A₁ ⊗[A] A₁) ⊗[A] C) M.obj)) :
    IsTangentBaseChangeIso 𝒳.isFiberedInGroupoids hf φ hφ F G (M := M) (N := ⟨_, hN⟩)
      (tensorCoeff M.obj) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁) (B := C)
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := A₁ ⊗[A] A₁) (B := C)
  have hrow := rowExact_of_liftClassRowExact 𝒳.isFiberedInGroupoids F F₁ F₂
    (liftClassRowExact_of_tensorProduct (A := A) (A₁ := A₁) (A₂ := A₁ ⊗[A] A₁) (M := M)
      (a := (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁))
      (b := (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁)) (hf₀₁ := hf₀₁) (hfa := hfa)
      (hfb := hfb)
      (hφ₀₁ := hφ₀₁) (hα := hα) (hβ := hβ) h𝒳 f hfS hFl hSu hLp
      (CommRingCat.isPushout_tensorProduct A A₁ A₁).flip (isSiteModule_tensor hA₁ M)
      (isSiteModule_tensor hA₂ M) hγ)
  have hrow' := rowExact_of_liftClassRowExact 𝒳.isFiberedInGroupoids G G₁ G₂
    (liftClassRowExact_of_tensorProduct_base (A := A) (A₁ := A₁) (C := C) (M := M) (hf₀₁ := hfc₀₁)
      (hfa := hfa') (hfb := hfb')
      (hφ₀₁ := hφ₀₁') (hα := hα') (hβ := hβ') h𝒳 f hfS hFl hSu hLp hN
      (isSiteModule_tensor hC₁ M) (isSiteModule_tensor hC₂ M) hγ')
  have hmap' : ∀ (g : A₁ →ₐ[A] A₁ ⊗[A] A₁) (z : A₁),
      (Algebra.TensorProduct.map g (AlgHom.id A C)) (z ⊗ₜ[A] (1 : C)) = (g z) ⊗ₜ[A] (1 : C) :=
    fun g z ↦ by rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  refine isTangentBaseChangeIso_of_equalizer 𝒳.isFiberedInGroupoids ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ hrow hrow' h₁ h₂
  · exact (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A] A₁ ⊗[A] A₁).comp_algebraMap
  · exact (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] A₁ ⊗[A] A₁).comp_algebraMap
  · exact RingHom.ext fun z ↦ hmap' _ z
  · exact RingHom.ext fun z ↦ hmap' _ z
  · exact RingHom.ext fun c ↦ map_tmul_one_left _ c
  · exact RingHom.ext fun c ↦ map_tmul_one_left _ c
  · exact hsq₀₁
  · exact hsqa
  · exact hsqb
  · intro m
    exact (tensorCoeffMap_apply_tensorCoeff _ _ _).trans
      (tensorCoeffMap_apply_tensorCoeff _ _ _).symm
  all_goals
    intro t
    refine tensorCoeffMap_comp_apply M.obj _ _ _ _ ?_ t
    ext z
    change (_ ⊗ₜ[A] (1 : C)) = Algebra.TensorProduct.map _ (AlgHom.id A C) (z ⊗ₜ[A] (1 : C))
    rw [hmap']
    rfl

end TensorCover

end Deformation.Artin

end
