module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponent
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Basic
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse

/-!
# The projection formula for a ring map, resolved

Let `f : R → A` be a homomorphism of commutative rings, `F` a model of derived extension of
scalars along `f` and `U` derived restriction of scalars.  This file constructs an isomorphism
`F ⋙ U ≅ (- ⊗ᴸ_R A)` — the projection formula — whose component at the class of a K-flat complex
`K` is, by construction, the composite of explicit chain-level isomorphisms:
the comparison of `F` at `K`, the factorization of `U` through `DerivedCategory.Q`, the chain
isomorphism `(A ⊗_R K)|_R ≅ Tot(K ⊗_R A[0])`, the class of `K ⊗ p` for a chosen K-flat
resolution `p : P ⟶ A[0]`, the K-flat comparison of the derived tensor product of [stacks 0A63],
and the resolution of the algebra.

The isomorphism is obtained by descending these components along the K-flat resolutions of
[stacks 06Y4]; no universe lift of the rings is involved, which is what makes its components
computable.

## Main definitions

* `Dualizing.extendRestrictComplexIso` — the chain-level projection formula
  `(A ⊗_R K)|_R ≅ Tot(K ⊗_R A[0])`.
* `Dualizing.resolvedProjectionComponent` — the component at a K-flat complex.
* `Dualizing.resolvedProjectionFormula` — the projection formula.

## Main results

* `Dualizing.resolvedProjectionFormula_hom_app` — its component at the class of a K-flat complex.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe v uR uA

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The algebra `A` as an `R`-module, in the module universe `max v uR uA`. -/
abbrev algebraModule : ModuleCat.{max v uR uA} R :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max v uR uA} A))

/-- The algebra `A` as a degree-zero complex of `R`-modules. -/
abbrev algebraComplex : CochainComplex (ModuleCat.{max v uR uA} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{max v uR uA} R) 0).obj (algebraModule.{v} f)

/-- Tensoring on the right with a fixed module is additive. -/
instance moduleTensor_flip_obj_additive {S : Type uR} [CommRing S] (N : ModuleCat.{max uR v} S) :
    ((moduleTensor.{uR, v} S).flip.obj N).Additive where
  map_add {_ _} a b := ModuleCat.hom_ext (LinearMap.rTensor_add N a.hom b.hom)

/-- The identification of `Tot(K ⊗ N[0])` with `K ⊗ N` degreewise is natural in `K`. -/
theorem singleRightIsoMapBifunctor_hom_naturality {S : Type uR} [CommRing S]
    {K K' : CochainComplex (ModuleCat.{max uR v} S) ℤ}
    (g : K ⟶ K') (N : ModuleCat.{max uR v} S) :
    haveI := moduleTensor_flip_obj_additive.{v, uR} N
    (((moduleTensor.{uR, v} S).flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
        (HomologicalComplex.singleRightIsoMapBifunctor (moduleTensor.{uR, v} S) K' N).hom =
      (HomologicalComplex.singleRightIsoMapBifunctor (moduleTensor.{uR, v} S) K N).hom ≫
        HomologicalComplex.mapBifunctorMap g (𝟙 ((CochainComplex.singleFunctor _ 0).obj N))
          (moduleTensor.{uR, v} S) (ComplexShape.up ℤ) := by
  have := moduleTensor_flip_obj_additive.{v, uR} N
  ext i : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.singleRightIsoMapBifunctor,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom,
    HomologicalComplex.mapBifunctorSingleRightXIso_inv]
  rw [Category.assoc, HomologicalComplex.singleRightι, HomologicalComplex.singleRightι,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (((moduleTensor.{uR, v} S).map (g.f i)).naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv).symm

/-- Extension then restriction of scalars is tensoring on the right with the algebra. -/
def extendRestrictFlipIso :
    ModuleCat.extendScalars.{uR, uA, max v uR uA} f ⋙ ModuleCat.restrictScalars.{max v uR uA} f ≅
      (moduleTensor.{uR, max v uR uA} R).flip.obj (algebraModule.{v} f) := by
  letI := f.toAlgebra
  exact NatIso.ofComponents (fun M =>
    ((TensorProduct.comm R A M).trans (TensorProduct.congr (LinearEquiv.refl R M)
      (ULift.moduleEquiv : ULift.{max v uR uA} A ≃ₗ[R] A).symm)).toModuleIso) (by
        intros
        ext : 1
        apply TensorProduct.ext'
        intros
        rfl)

/-- `Dualizing.extendRestrictFlipIso` on a pure tensor. -/
theorem extendRestrictFlipIso_hom_tmul (M : ModuleCat.{max v uR uA} R) (a : A) (m : M) :
    letI := f.toAlgebra
    ((extendRestrictFlipIso.{v} f).hom.app M).hom (a ⊗ₜ[R] m) =
      (m ⊗ₜ[R] (ULift.up a : ULift.{max v uR uA} A) : TensorProduct R M (ULift.{max v uR uA} A)) :=
  rfl

/-- The chain-level projection formula. -/
def extendRestrictComplexIso (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :
    ((ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      tensorComplex.{uR, max v uR uA} K (algebraComplex.{v} f) := by
  haveI := moduleTensor_flip_obj_additive.{max v uR uA, uR} (algebraModule.{v} f)
  exact (NatIso.mapHomologicalComplex (extendRestrictFlipIso.{v} f) (ComplexShape.up ℤ)).app K ≪≫
      HomologicalComplex.singleRightIsoMapBifunctor (moduleTensor.{uR, max v uR uA} R) K
        (algebraModule.{v} f)

/-- The chain-level projection formula is natural. -/
theorem extendRestrictComplexIso_hom_naturality
    {K K' : CochainComplex (ModuleCat.{max v uR uA} R) ℤ}
    (g : K ⟶ K') :
    ((ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) ≫ (extendRestrictComplexIso.{v} f K').hom =
      (extendRestrictComplexIso.{v} f K).hom ≫
        HomologicalComplex.mapBifunctorMap g (𝟙 (algebraComplex.{v} f))
          (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ) := by
  have h1 := ((NatIso.mapHomologicalComplex (extendRestrictFlipIso.{v} f)
    (ComplexShape.up ℤ)).hom.naturality g)
  have h2 := singleRightIsoMapBifunctor_hom_naturality.{max v uR uA} g (algebraModule.{v} f)
  dsimp only [extendRestrictComplexIso, Iso.trans_hom]
  rw [← Category.assoc]
  refine (congrArg (fun x => x ≫ _) h1).trans ?_
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun x => _ ≫ x) h2

section Clean

variable (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
  (P : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (hP : CochainComplex.KFlat.{uR, max v uR uA} P)
  (p : P ⟶ algebraComplex.{v} f) [QuasiIso p]

/-- The algebra, identified with the class of a resolution. -/
def algebraResolutionIso : derivedAlgebraSingle.{uR, uA, v} f ≅ DerivedCategory.Q.obj P :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v uR uA} R) 0).app
      (algebraModule.{v} f) ≪≫ (asIso (DerivedCategory.Q.map p)).symm

/-- Tensoring a K-flat complex with the resolution of the algebra. -/
def kFlatTensorResolutionIso (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    DerivedCategory.Q.obj (tensorComplex.{uR, max v uR uA} K P) ≅
      DerivedCategory.Q.obj (tensorComplex.{uR, max v uR uA} K (algebraComplex.{v} f)) :=
  haveI : QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA} R)
      (ComplexShape.up ℤ)) := quasiIso_tleft_map_of_kFlat.{uR, max v uR uA} K hK p
  asIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) p
    (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)))

/-- The underlying morphism of `Dualizing.kFlatTensorResolutionIso`. -/
theorem kFlatTensorResolutionIso_hom (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    (kFlatTensorResolutionIso.{v} f P p K hK).hom =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) p
        (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) :=
  rfl

/-- The component at a K-flat complex of the resolved projection formula. -/
def resolvedProjectionComponent (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    (F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory).obj
        (DerivedCategory.Q.obj K) ≅
      (derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f).obj (DerivedCategory.Q.obj K) := by
  haveI := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, v}
    f F comparison K hK
  exact (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.mapIso
      (asIso (comparison.app K)) ≪≫
    (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso (extendRestrictComplexIso.{v} f K) ≪≫
    (kFlatTensorResolutionIso.{v} f P p K hK).symm ≪≫
    (derivedTensor_comparison.{uR, max v uR uA} R K P hP).symm ≪≫
    (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj K)) (algebraResolutionIso.{v} f P p).symm)

/-- The underlying morphism of `Dualizing.resolvedProjectionComponent`. -/
theorem resolvedProjectionComponent_hom (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    haveI := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, v}
      f F comparison K hK
    (resolvedProjectionComponent.{v} f F comparison P hP p K hK).hom =
      (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map (comparison.app K) ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (extendRestrictComplexIso.{v} f K).hom ≫
        (kFlatTensorResolutionIso.{v} f P p K hK).inv ≫
        (derivedTensor_comparison.{uR, max v uR uA} R K P hP).inv ≫
        (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K), (algebraResolutionIso.{v} f P p).inv) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f)) :=
  rfl

/-- A composite of six morphisms followed by six retractions of them, in reverse order, is the
identity. -/
theorem comp_telescope_six {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄) (a₅ : X₄ ⟶ X₅) (a₆ : X₅ ⟶ X₆)
    (b₁ : X₁ ⟶ X₀) (b₂ : X₂ ⟶ X₁) (b₃ : X₃ ⟶ X₂) (b₄ : X₄ ⟶ X₃) (b₅ : X₅ ⟶ X₄) (b₆ : X₆ ⟶ X₅)
    (h₁ : a₁ ≫ b₁ = 𝟙 X₀) (h₂ : a₂ ≫ b₂ = 𝟙 X₁) (h₃ : a₃ ≫ b₃ = 𝟙 X₂) (h₄ : a₄ ≫ b₄ = 𝟙 X₃)
    (h₅ : a₅ ≫ b₅ = 𝟙 X₄) (h₆ : a₆ ≫ b₆ = 𝟙 X₅) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆) ≫ b₆ ≫ b₅ ≫ b₄ ≫ b₃ ≫ b₂ ≫ b₁ = 𝟙 X₀ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₆, reassoc_of% h₅, reassoc_of% h₄, reassoc_of% h₃, reassoc_of% h₂, h₁]

/-- The inverse of `Dualizing.resolvedProjectionComponent`. -/
theorem resolvedProjectionComponent_inv (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    haveI := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, v}
      f F comparison K hK
    (resolvedProjectionComponent.{v} f F comparison P hP p K hK).inv =
      (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K), (algebraResolutionIso.{v} f P p).hom) :
            (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f) ⟶
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P)) ≫
        (derivedTensor_comparison.{uR, max v uR uA} R K P hP).hom ≫
        (kFlatTensorResolutionIso.{v} f P p K hK).hom ≫
        DerivedCategory.Q.map (extendRestrictComplexIso.{v} f K).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
          (CategoryTheory.inv (comparison.app K)) := by
  refine Iso.inv_ext ?_
  rw [resolvedProjectionComponent_hom]
  refine comp_telescope_six _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · exact Iso.hom_inv_id_app _ _
  · simp
  · exact Iso.inv_hom_id _
  · exact Iso.inv_hom_id _
  · exact Iso.hom_inv_id ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
      R).tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj K))
        (algebraResolutionIso.{v} f P p).symm))

/-- Pasting six commuting squares along a ladder. -/
theorem comp_ladder_six {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₀ B₁ B₂ B₃ B₄ B₅ B₆ : C}
    (t : A₀ ⟶ B₀)
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅) (a₆ : A₅ ⟶ A₆)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (b₅ : B₄ ⟶ B₅) (b₆ : B₅ ⟶ B₆)
    (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₃ : A₃ ⟶ B₃) (v₄ : A₄ ⟶ B₄) (v₅ : A₅ ⟶ B₅) (v₆ : A₆ ⟶ B₆)
    (s₁ : t ≫ b₁ = a₁ ≫ v₁) (s₂ : v₁ ≫ b₂ = a₂ ≫ v₂) (s₃ : v₂ ≫ b₃ = a₃ ≫ v₃)
    (s₄ : v₃ ≫ b₄ = a₄ ≫ v₄) (s₅ : v₄ ≫ b₅ = a₅ ≫ v₅) (s₆ : v₅ ≫ b₆ = a₆ ≫ v₆) :
    t ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ ≫ b₆ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆) ≫ v₆ := by
  simp only [Category.assoc]
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, reassoc_of% s₄, reassoc_of% s₅, s₆]

/-- A commuting square of isomorphisms, read with the inverses. -/
theorem inv_comp_eq_of_comp_hom {C : Type*} [Category C] {X Y X' Y' : C} (e : X ≅ Y)
    (e' : X' ≅ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ e'.hom = e.hom ≫ b) :
    b ≫ e'.inv = e.inv ≫ a := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The interchange law for the total tensor product of complexes. -/
theorem mapBifunctorMap_interchange {S : Type uR} [CommRing S]
    {K K' L L' : CochainComplex (ModuleCat.{max uR v} S) ℤ} (g : K ⟶ K') (q : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap g (𝟙 L) (moduleTensor.{uR, v} S) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 K') q (moduleTensor.{uR, v} S) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 K) q (moduleTensor.{uR, v} S) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap g (𝟙 L') (moduleTensor.{uR, v} S)
          (ComplexShape.up ℤ) := by
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext (fun i j hij => ?_)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (((moduleTensor.{uR, v} S).map (g.f i)).naturality (q.f j)).symm

/-- The components of the resolved projection formula are natural in chain maps between K-flat
complexes. -/
theorem resolvedProjectionComponent_naturality
    (K K' : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K)
    (hK' : CochainComplex.KFlat.{uR, max v uR uA} K')
    (g : K ⟶ K') :
    (F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory).map
          (DerivedCategory.Q.map g) ≫
        (resolvedProjectionComponent.{v} f F comparison P hP p K' hK').hom =
      (resolvedProjectionComponent.{v} f F comparison P hP p K hK).hom ≫
        (derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f).map
          (DerivedCategory.Q.map g) := by
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, v}
    f F comparison K hK
  have := CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, v}
    f F comparison K' hK'
  have h1 := comparison.naturality g
  have h2 := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors_hom_naturality
    (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g)
  dsimp only [Functor.comp_map] at h1
  have h4' : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap g (𝟙 (algebraComplex.{v} f))
        (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) ≫
      (kFlatTensorResolutionIso.{v} f P p K' hK').inv =
      (kFlatTensorResolutionIso.{v} f P p K hK).inv ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap g (𝟙 P)
          (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) := by
    refine inv_comp_eq_of_comp_hom _ _ _ _ ?_
    rw [kFlatTensorResolutionIso_hom, kFlatTensorResolutionIso_hom, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, mapBifunctorMap_interchange.{max v uR uA} g p]
  have h5' : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap g (𝟙 P)
        (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) ≫
      (derivedTensor_comparison.{uR, max v uR uA} R K' P hP).inv =
      (derivedTensor_comparison.{uR, max v uR uA} R K P hP).inv ≫
        (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((DerivedCategory.Q.map g, DerivedCategory.Q.map (𝟙 P)) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj P)) :=
    inv_comp_eq_of_comp_hom _ _ _ _
      (Dualizing.ProjectionFormula.derivedTensor_comparison_naturality.{uR, max v uR uA} R g
        (𝟙 P) hP hP)
  have s1 : (F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory).map
        (DerivedCategory.Q.map g) ≫
      (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map (comparison.app K') =
      (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map (comparison.app K) ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
          (DerivedCategory.Q.map (((ModuleCat.extendScalars.{uR, uA, max v uR uA}
            f).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
    rw [Functor.comp_map, ← Functor.map_comp, h1, Functor.map_comp]
  have s3 : DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max v uR uA}
        f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g)) ≫
      DerivedCategory.Q.map (extendRestrictComplexIso.{v} f K').hom =
      DerivedCategory.Q.map (extendRestrictComplexIso.{v} f K).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap g (𝟙 (algebraComplex.{v} f))
          (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) := by
    rw [← DerivedCategory.Q.map_comp, extendRestrictComplexIso_hom_naturality.{v} f g,
      DerivedCategory.Q.map_comp]
  have s6 : (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((DerivedCategory.Q.map g, DerivedCategory.Q.map (𝟙 P)) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj P)) ≫
        (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K'), (algebraResolutionIso.{v} f P p).inv) :
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K', derivedAlgebraSingle.{uR, uA, v} f)) =
      (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((𝟙 (DerivedCategory.Q.obj K), (algebraResolutionIso.{v} f P p).inv) :
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
              (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f)) ≫
        (derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f).map
          (DerivedCategory.Q.map g) := by
    have hT : (derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f).map
        (DerivedCategory.Q.map g) =
        (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
          ((DerivedCategory.Q.map g, 𝟙 (derivedAlgebraSingle.{uR, uA, v} f)) :
            (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f) ⟶
              (DerivedCategory.Q.obj K', derivedAlgebraSingle.{uR, uA, v} f)) := rfl
    rw [hT]
    refine Eq.trans ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
      R).tensor_map_comp _ _ _ _) (Eq.trans ?_ ((derivedHomAdjunctionOverRing.{uR, max v uR uA,
        max v uR uA + 1} R).tensor_map_comp _ _ _ _).symm)
    refine congrArg _ (Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) ?_)
    change DerivedCategory.Q.map (𝟙 P) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [resolvedProjectionComponent_hom, resolvedProjectionComponent_hom]
  exact comp_ladder_six _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 h2 s3 h4' h5' s6

/-- **The projection formula, resolved.**  The isomorphism `F ⋙ U ≅ (- ⊗ᴸ_R A)` whose component at
the class of a K-flat complex is `Dualizing.resolvedProjectionComponent`. -/
def resolvedProjectionFormula :
    F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory ≅
      derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f :=
  ModuleSystemRlimTensor.natIsoOfResolutions (fun K => CochainComplex.KFlat.{uR, max v uR uA} K)
    (fun K => by
      obtain ⟨L, s, hL, -, hs, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, max v uA} K
      exact ⟨L, s, hL, hs⟩)
    (F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory)
    (derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f)
    (fun K hK => resolvedProjectionComponent.{v} f F comparison P hP p K hK)
    (fun K K' hK hK' g =>
      resolvedProjectionComponent_naturality.{v} f F comparison P hP p K K' hK hK' g)

/-- **The component of the resolved projection formula at a K-flat complex.** -/
theorem resolvedProjectionFormula_hom_app (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    (resolvedProjectionFormula.{v} f F comparison P hP p).hom.app (DerivedCategory.Q.obj K) =
      (resolvedProjectionComponent.{v} f F comparison P hP p K hK).hom :=
  ModuleSystemRlimTensor.natIsoOfResolutions_hom_app_of_prop _ _ _ _ _ _ K hK

end Clean

end Dualizing
