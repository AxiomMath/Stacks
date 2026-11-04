module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorTorsion
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleNakayama
public import StacksFrontier.Homology.DerivedComplete.TriangulatedReflectionKill

/-!
# The completed base change map is detected modulo `I`

Consider the setting of `Stacks.ConstantModuleTensor.isIso_derivedTensor_map_baseChange_iff`: a
square of `Λ`-linear functors between categories of sheaves of `Λ`-modules, with base change map
`β : RF ⋙ Gb ⟶ Ga ⋙ RF'`. Let `I ⊆ Λ` be a finitely generated ideal and `P` a bounded complex
of finitely generated projective modules representing `Λ/I`. Let `c : (Gb RF K)^∧ ⟶
RF'((Ga K)^∧)` be a map of derived complete objects whose composite with the completion map is
`β_K` followed by `RF'` of the completion map, the target being derived complete.

If `β_K ⊗^L_Λ P` is an isomorphism, then so is `c`. Indeed `- ⊗^L_Λ P` kills every object on
which an element of `I` acts invertibly, so it inverts the completion maps; by the projection
formula for `RF'` it inverts `RF'` of a completion map; so it inverts `c`. The cone of `c` is
then derived complete with vanishing `- ⊗^L_Λ Λ/I`, hence zero by derived Nakayama. This is the
reduction modulo `I` in the proof of Stacks 09C9.

## Main results

* `Stacks.ConstantModuleTensor.isIso_of_isIso_derivedTensor_map_baseChange`.

## Implementation notes

The derived categories are taken in the standard model `HasDerivedCategory.standard`, the one
for which `Stacks.ConstantModuleTensor.acyclic_of_isDerivedComplete_of_acyclic_tensor` is stated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v

namespace Stacks.ConstantModuleTensor

open Stacks.Cohomology.UnboundedComplexes

attribute [local instance] HasDerivedCategory.standard

variable {C₁ : Type w} [Category.{v} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type w} [Category.{v} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type w} [Category.{v} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type w} [Category.{v} C₄] {J₄ : GrothendieckTopology C₄}
  {Λ : Type w} [CommRing Λ]
  [HasSheafify J₁ (ModuleCat.{w} Λ)] [HasSheafify J₂ (ModuleCat.{w} Λ)]
  [HasSheafify J₃ (ModuleCat.{w} Λ)] [HasSheafify J₄ (ModuleCat.{w} Λ)]
  (F : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₂ (ModuleCat.{w} Λ)) [F.Additive] [F.Linear Λ]
  (Gb : Sheaf J₂ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)) [Gb.Additive] [Gb.Linear Λ]
  [PreservesFiniteLimits Gb] [PreservesFiniteColimits Gb]
  (Ga : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₃ (ModuleCat.{w} Λ)) [Ga.Additive] [Ga.Linear Λ]
  [PreservesFiniteLimits Ga] [PreservesFiniteColimits Ga]
  (F' : Sheaf J₃ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)) [F'.Additive] [F'.Linear Λ]
  (θ : F ⋙ Gb ⟶ Ga ⋙ F')
  (RF : DerivedCategory (Sheaf J₁ (ModuleCat.{w} Λ)) ⥤ DerivedCategory (Sheaf J₂ (ModuleCat.{w} Λ)))
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  (RF' : DerivedCategory (Sheaf J₃ (ModuleCat.{w} Λ)) ⥤
    DerivedCategory (Sheaf J₄ (ModuleCat.{w} Λ)))
  (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{w} (Sheaf J₁ (ModuleCat.{w} Λ))]
  [IsGrothendieckAbelian.{w} (Sheaf J₃ (ModuleCat.{w} Λ))]
  [IsGrothendieckAbelian.{w} (Sheaf J₄ (ModuleCat.{w} Λ))]

/-- An element of `I` acts by zero on `Λ/I` in the derived category. -/
theorem smul_id_Q_obj_eq_zero (I : Ideal Λ) (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (eP : (DerivedCategory.singleFunctor (ModuleCat.{w} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)) ≅
      DerivedCategory.Q.obj P) {μ : Λ} (hμ : μ ∈ I) :
    μ • 𝟙 (DerivedCategory.Q.obj P) = 0 := by
  have h0 : μ • 𝟙 (ModuleCat.of Λ (Λ ⧸ I)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change μ • Ideal.Quotient.mk I y = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_right y hμ
  have h1 : μ • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{w} Λ) 0).obj
      (ModuleCat.of Λ (Λ ⧸ I))) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, h0, Functor.map_zero]
  have : μ • 𝟙 (DerivedCategory.Q.obj P) = eP.inv ≫ (μ • 𝟙 _) ≫ eP.hom := by simp
  rw [this, h1, Limits.zero_comp, Limits.comp_zero]

omit [Functor.Linear Λ F] [Functor.Linear Λ Gb] [Functor.Linear Λ Ga] in
/-- **The completed base change map is an isomorphism as soon as it is modulo `I`**: if
`β_K ⊗^L_Λ P` is invertible, where `P` represents `Λ/I`, then so is every map `c` out of the
completion of `Gb(RF K)` into the derived complete object `RF'((Ga K)^∧)` compatible with `β_K`
and the completion maps. -/
theorem isIso_of_isIso_derivedTensor_map_baseChange (I : Ideal Λ) (hI : I.FG)
    [HasProductsOfShape ℕ (DerivedCategory (Sheaf J₃ (ModuleCat.{w} Λ)))]
    [HasProductsOfShape ℕ (DerivedCategory (Sheaf J₄ (ModuleCat.{w} Λ)))]
    [HasProductsOfShape ℕ (Sheaf J₄ (ModuleCat.{w} Λ))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} Λ))]
    {L₃ : DerivedCategory (Sheaf J₃ (ModuleCat.{w} Λ)) ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete I :
        ObjectProperty (DerivedCategory (Sheaf J₃ (ModuleCat.{w} Λ))))}
    (adj₃ : L₃ ⊣ ObjectProperty.ι _)
    {L₄ : DerivedCategory (Sheaf J₄ (ModuleCat.{w} Λ)) ⥤
      ObjectProperty.FullSubcategory (IsDerivedComplete I :
        ObjectProperty (DerivedCategory (Sheaf J₄ (ModuleCat.{w} Λ))))}
    (adj₄ : L₄ ⊣ ObjectProperty.ι _)
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ)
    [P.IsStrictlyLE b] [P.IsStrictlyGE a] [∀ q, Module.Finite Λ (P.X q)]
    [∀ q, Module.Projective Λ (P.X q)] [Stacks.DerivedTensor.IsKFlat (sheafTensor J₃ Λ) P]
    [Stacks.DerivedTensor.IsKFlat (sheafTensor J₄ Λ) P]
    (eP : (DerivedCategory.singleFunctor (ModuleCat.{w} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)) ≅
      DerivedCategory.Q.obj P)
    (K : DerivedCategory (Sheaf J₁ (ModuleCat.{w} Λ)))
    (c : (L₄.obj (Gb.mapDerivedCategory.obj (RF.obj K))).obj ⟶
      RF'.obj (L₃.obj (Ga.mapDerivedCategory.obj K)).obj)
    (hc : adj₄.unit.app _ ≫ c = (derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app K ≫
      RF'.map (adj₃.unit.app _))
    (hT : IsDerivedComplete I (RF'.obj (L₃.obj (Ga.mapDerivedCategory.obj K)).obj))
    (hβ : IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
      ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app K))) :
    IsIso c := by
  have hμ := fun μ (hμ : μ ∈ I) => smul_id_Q_obj_eq_zero I P eP hμ
  have hKP : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  have hu₄ := DerivedCompletionReflection.isIso_map_unit_of_kills
    (Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P) I hI adj₄
    (Gb.mapDerivedCategory.obj (RF.obj K))
    (fun μ hm N hN => isZero_derivedTensor_obj_of_isIso_smul J₄ Λ P μ (hμ μ hm) N hN)
  have hu₃ := DerivedCompletionReflection.isIso_map_unit_of_kills
    (Stacks.DerivedTensor.derivedTensor (sheafTensor J₃ Λ) P) I hI adj₃
    (Ga.mapDerivedCategory.obj K)
    (fun μ hm N hN => isZero_derivedTensor_obj_of_isIso_smul J₃ Λ P μ (hμ μ hm) N hN)
  have hR := isIso_derivedTensor_map_rightDerived_map F' RF' αF' P a b _ hu₃
  have hTc : IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map c) := by
    have e := congrArg (Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map hc
    rw [Functor.map_comp, Functor.map_comp] at e
    have : IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
        ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app K) ≫
        (Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
          (RF'.map (adj₃.unit.app _))) := IsIso.comp_isIso' hβ hR
    rw [← e] at this
    exact IsIso.of_isIso_comp_left ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
      (adj₄.unit.app _)) _
  obtain ⟨Z, g, h, hdist⟩ := distinguished_cocone_triangle c
  have hZT : IsZero ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((Stacks.DerivedTensor.derivedTensor
      (sheafTensor J₄ Λ) P).map_distinguished _ hdist)).2 hTc
  have hZc : IsDerivedComplete I Z :=
    DerivedCompletionReflection.isDerivedComplete_obj₃_of_distTriang hdist
      (L₄.obj (Gb.mapDerivedCategory.obj (RF.obj K))).property hT
  obtain ⟨Lc, hLc, ⟨eZ⟩⟩ := exists_iso_Qh_obj_quotient_obj_of_isKInjective
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck Z
  let eZ' : Z ≅ DerivedCategory.Q.obj Lc := eZ ≪≫ (DerivedCategory.quotientCompQhIso _).app Lc
  have hLcomp : IsDerivedComplete I (DerivedCategory.Q.obj Lc) :=
    DerivedCompleteRecurrence.isDerivedComplete_of_iso eZ' hZc
  have hacyc : (CochainComplex.KFlatBifunctor.totalComplex (sheafTensor J₄ Λ) Lc P).Acyclic := by
    rw [HomologicalComplex.acyclic_iff_isZero_Q]
    exact hZT.of_iso (((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).mapIso eZ') ≪≫
      Stacks.DerivedTensor.derivedTensorObjIso (sheafTensor J₄ Λ) P Lc).symm
  have hL0 := acyclic_of_isDerivedComplete_of_acyclic_tensor J₄ Λ I hI Lc hLcomp P a b eP hacyc
  have hZ0 : IsZero Z := ((HomologicalComplex.acyclic_iff_isZero_Q _).1 hL0).of_iso eZ'
  exact (Triangle.isZero₃_iff_isIso₁ _ hdist).1 hZ0

end Stacks.ConstantModuleTensor
