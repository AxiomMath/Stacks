module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformation
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorTotalComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantModuleTensorProjective

/-!
# The base change map commutes with tensoring by a bounded complex of projective modules

Consider a square of `Λ`-linear functors between categories of sheaves of `Λ`-modules
```
A  --Ga-->  A'
|           |
F           F'
v           v
B  --Gb-->  B'
```
with `Ga`, `Gb` exact, a transformation `θ : F ⋙ Gb ⟶ Ga ⋙ F'`, and right derived functors
`RF`, `RF'` on Grothendieck abelian categories; let `β : RF ⋙ Gb ⟶ Ga ⋙ RF'` be the base
change map (`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap`). Let `P` be a bounded
complex of finitely generated projective `Λ`-modules.

Then for a K-injective complex `K`, `β_K ⊗^L_Λ P` is invertible if and only if `β_{K ⊗_Λ P}` is.
Indeed `Tot(- ⊗_Λ P)` commutes with all four functors on complexes, compatibly with `θ`
(`Stacks.ConstantModuleTensor.totalComparison`), it preserves K-injective complexes, and it
carries a K-injective resolution of `Ga(K)` to one of `Ga(K ⊗_Λ P)`.

## Main results

* `Stacks.ConstantModuleTensor.isIso_derivedTensor_map_baseChange_iff`.
* `Stacks.ConstantModuleTensor.isIso_derivedTensor_map_rightDerived_map`: if `φ ⊗^L_Λ P` is
  invertible, so is `RF'(φ) ⊗^L_Λ P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.ConstantModuleTensor

open Stacks.Cohomology.UnboundedComplexes

/-- The comparison `totalComparison` is compatible with a transformation `θ : H ⟶ Ga ⋙ F'`
followed by `F'` applied to a morphism out of `Ga(K)`. -/
theorem mapBifunctorMap_comp_totalComparison {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
    {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄} {Λ : Type w} [CommRing Λ]
    [HasSheafify J₁ (ModuleCat.{w} Λ)] [HasSheafify J₃ (ModuleCat.{w} Λ)]
    [HasSheafify J₄ (ModuleCat.{w} Λ)]
    {Ga : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₃ (ModuleCat.{w} Λ)} [Ga.Additive] [Ga.Linear Λ]
    {F' : Sheaf J₃ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)} [F'.Additive] [F'.Linear Λ]
    {H : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)} [H.Additive] [H.Linear Λ]
    (θ : H ⟶ Ga ⋙ F') (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J₁ (ModuleCat.{w} Λ)) ℤ)
    {L : CochainComplex (Sheaf J₃ (ModuleCat.{w} Λ)) ℤ} (ι : (Ga.mapHomologicalComplex _).obj K ⟶ L)
    [IsIso (totalComparison J₁ J₃ Ga P K)] :
    HomologicalComplex.mapBifunctorMap ((NatTrans.mapHomologicalComplex θ _).app K ≫
        (F'.mapHomologicalComplex _).map ι) (𝟙 P) (sheafTensor J₄ Λ) (ComplexShape.up ℤ) ≫
        totalComparison J₃ J₄ F' P L =
      totalComparison J₁ J₄ H P K ≫ (NatTrans.mapHomologicalComplex θ _).app
          (HomologicalComplex.mapBifunctor K P (sheafTensor J₁ Λ) (ComplexShape.up ℤ)) ≫
        (F'.mapHomologicalComplex _).map (inv (totalComparison J₁ J₃ Ga P K) ≫
          HomologicalComplex.mapBifunctorMap ι (𝟙 P) (sheafTensor J₃ Λ) (ComplexShape.up ℤ)) := by
  rw [← totalComparison_natTrans_assoc J₁ J₄ H P (Ga ⋙ F') θ K,
    totalComparison_comp J₁ J₃ Ga J₄ F' P K, mapBifunctorMap_comp_id,
    (F'.mapHomologicalComplex _).map_comp]
  simp only [Category.assoc]
  rw [totalComparison_naturality, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Through the comparisons `totalComparison`, `Tot(- ⊗_Λ P)` of `θ_K ≫ F'(ι)` is invertible in
the derived category if and only if `θ` at `Tot(K ⊗_Λ P)` followed by `F'` of the induced map
is. -/
theorem isIso_Q_map_totRight_map_comp_iff {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
    {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄} {Λ : Type w} [CommRing Λ]
    [HasSheafify J₁ (ModuleCat.{w} Λ)] [HasSheafify J₃ (ModuleCat.{w} Λ)]
    [HasSheafify J₄ (ModuleCat.{w} Λ)] [HasDerivedCategory.{w'} (Sheaf J₄ (ModuleCat.{w} Λ))]
    {Ga : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₃ (ModuleCat.{w} Λ)} [Ga.Additive] [Ga.Linear Λ]
    {F' : Sheaf J₃ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)} [F'.Additive] [F'.Linear Λ]
    {H : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₄ (ModuleCat.{w} Λ)} [H.Additive] [H.Linear Λ]
    (θ : H ⟶ Ga ⋙ F') (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (K : CochainComplex (Sheaf J₁ (ModuleCat.{w} Λ)) ℤ)
    {L : CochainComplex (Sheaf J₃ (ModuleCat.{w} Λ)) ℤ} (ι : (Ga.mapHomologicalComplex _).obj K ⟶ L)
    [IsIso (totalComparison J₁ J₃ Ga P K)] [IsIso (totalComparison J₁ J₄ H P K)]
    [IsIso (totalComparison J₃ J₄ F' P L)] :
    IsIso (DerivedCategory.Q.map ((Stacks.DerivedTensor.totRight (sheafTensor J₄ Λ) P).map
        ((NatTrans.mapHomologicalComplex θ _).app K ≫ (F'.mapHomologicalComplex _).map ι))) ↔
      IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ _).app
          ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K) ≫
        (F'.mapHomologicalComplex _).map (inv (totalComparison J₁ J₃ Ga P K) ≫
          (Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).map ι))) := by
  have e : DerivedCategory.Q.map ((Stacks.DerivedTensor.totRight (sheafTensor J₄ Λ) P).map
      ((NatTrans.mapHomologicalComplex θ _).app K ≫ (F'.mapHomologicalComplex _).map ι)) ≫
        DerivedCategory.Q.map (totalComparison J₃ J₄ F' P L) =
      DerivedCategory.Q.map (totalComparison J₁ J₄ H P K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ _).app
            ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K) ≫
          (F'.mapHomologicalComplex _).map (inv (totalComparison J₁ J₃ Ga P K) ≫
            (Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).map ι)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (mapBifunctorMap_comp_totalComparison θ P K ι)).trans (DerivedCategory.Q.map_comp _ _))
  exact (isIso_comp_right_iff _ (DerivedCategory.Q.map (totalComparison J₃ J₄ F' P L))).symm.trans
    ((Iff.of_eq (congrArg (fun f => IsIso f) e)).trans
      (isIso_comp_left_iff (DerivedCategory.Q.map (totalComparison J₁ J₄ H P K)) _))

/-- A morphism of complexes is invertible in the derived category through `Qh` if and only if it
is through `Q`. -/
private theorem isIso_Qh_map_quotient_map_iff {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w'} 𝒜] {K L : CochainComplex 𝒜 ℤ} (ψ : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ)) ↔
      IsIso (DerivedCategory.Q.map ψ) := by
  have := NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso 𝒜) ψ
  rwa [Functor.comp_map] at this

/-- A functor with a right derived functor on the unbounded derived category carries a morphism
between K-injective complexes which is invertible in the derived category to one which is. -/
theorem isIso_Q_map_mapHomologicalComplex_map_of_isKInjective {𝒜 : Type*} [Category 𝒜]
    [Abelian 𝒜] [IsGrothendieckAbelian.{w} 𝒜] [HasDerivedCategory.{w'} 𝒜] {ℬ : Type*} [Category ℬ]
    [Abelian ℬ] [HasDerivedCategory.{w'} ℬ] (G : 𝒜 ⥤ ℬ) [G.Additive]
    (RG : DerivedCategory 𝒜 ⥤ DerivedCategory ℬ)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    {I J : CochainComplex 𝒜 ℤ} (hI : I.IsKInjective) (hJ : J.IsKInjective) (ψ : I ⟶ J)
    (hψ : IsIso (DerivedCategory.Q.map ψ)) :
    IsIso (DerivedCategory.Q.map ((G.mapHomologicalComplex _).map ψ)) := by
  have := isIso_app_of_isKInjective _ _ RG αG I hI
  have := isIso_app_of_isKInjective _ _ RG αG J hJ
  have hQh := (isIso_Qh_map_quotient_map_iff ψ).2 hψ
  have hR : IsIso ((DerivedCategory.Qh ⋙ RG).map ((HomotopyCategory.quotient _ _).map ψ)) := by
    rw [Functor.comp_map]
    infer_instance
  have h2 : IsIso ((G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient _ _).map ψ)) := by
    rw [← isIso_comp_right_iff _ (αG.app _), αG.naturality]
    infer_instance
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map] at h2
  exact (isIso_Qh_map_quotient_map_iff _).1 h2

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  {Λ : Type w} [CommRing Λ]
  [HasSheafify J₁ (ModuleCat.{w} Λ)] [HasSheafify J₂ (ModuleCat.{w} Λ)]
  [HasSheafify J₃ (ModuleCat.{w} Λ)] [HasSheafify J₄ (ModuleCat.{w} Λ)]
  [HasDerivedCategory.{w'} (Sheaf J₁ (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{w'} (Sheaf J₂ (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{w'} (Sheaf J₃ (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{w'} (Sheaf J₄ (ModuleCat.{w} Λ))]
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

/-- The image of a complex in the derived category through the homotopy category, compared with
the localization functor. -/
def quotientQhCompIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]
    {ℰ : Type*} [Category ℰ] (Φ : DerivedCategory 𝒜 ⥤ ℰ) :
    HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ Φ ≅
      DerivedCategory.Q ⋙ Φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso 𝒜) Φ

/-- `Tot(- ⊗_Λ P)` followed by the localization detects the invertibility of the image of a
morphism of complexes, for `P` K-flat. -/
theorem isIso_derivedTensor_map_Qh_map_iff {C₀ : Type*} [Category C₀] {J₀ : GrothendieckTopology C₀}
    [HasSheafify J₀ (ModuleCat.{w} Λ)] [HasDerivedCategory.{w'} (Sheaf J₀ (ModuleCat.{w} Λ))]
    (P : CochainComplex (ModuleCat.{w} Λ) ℤ) [Stacks.DerivedTensor.IsKFlat (sheafTensor J₀ Λ) P]
    {K L : CochainComplex (Sheaf J₀ (ModuleCat.{w} Λ)) ℤ} (ψ : K ⟶ L) :
    IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₀ Λ) P).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ))) ↔
      IsIso (DerivedCategory.Q.map
        ((Stacks.DerivedTensor.totRight (sheafTensor J₀ Λ) P).map ψ)) := by
  have := NatIso.isIso_map_iff (quotientQhCompIso
    (Stacks.DerivedTensor.derivedTensor (sheafTensor J₀ Λ) P)) ψ
  rw [Functor.comp_map, Functor.comp_map] at this
  rw [this, NatIso.isIso_map_iff (Stacks.DerivedTensor.derivedTensorQIso (sheafTensor J₀ Λ) P) ψ,
    Functor.comp_map]

/-- **The base change map commutes with `- ⊗^L_Λ P`** for a bounded complex `P` of finitely
generated projective modules: on a K-injective complex `K`, `β_K ⊗^L_Λ P` is invertible if and
only if `β_{K ⊗_Λ P}` is. -/
theorem isIso_derivedTensor_map_baseChange_iff (P : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ)
    [P.IsStrictlyLE b] [P.IsStrictlyGE a] [∀ q, Module.Finite Λ (P.X q)]
    [∀ q, Module.Projective Λ (P.X q)] [Stacks.DerivedTensor.IsKFlat (sheafTensor J₃ Λ) P]
    [Stacks.DerivedTensor.IsKFlat (sheafTensor J₄ Λ) P]
    (K : CochainComplex (Sheaf J₁ (ModuleCat.{w} Λ)) ℤ) (hK : K.IsKInjective) :
    IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
        ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)))) ↔
      IsIso ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K)))) := by
  obtain ⟨L, ι, hL, hι⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    ((Ga.mapHomologicalComplex _).obj K)
  have hP : ∀ q, Module.Finite Λ (P.X q) ∧ Module.Projective Λ (P.X q) :=
    fun q => ⟨inferInstance, inferInstance⟩
  have hκa := isIso_totalComparison J₁ J₃ Ga P a b K
  let ι' : (Ga.mapHomologicalComplex _).obj
      ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K) ⟶
      (Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).obj L :=
    @inv _ _ _ _ (totalComparison J₁ J₃ Ga P K) hκa ≫
      (Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).map ι
  have hι' : QuasiIso ι' := by
    have : IsIso (DerivedCategory.Q.map
        ((Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).map ι)) :=
      (NatIso.isIso_map_iff (Stacks.DerivedTensor.derivedTensorQIso (sheafTensor J₃ Λ) P) ι).1
        (by rw [Functor.comp_map]; infer_instance)
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    change IsIso (DerivedCategory.Q.map
      (@inv _ _ _ _ (totalComparison J₁ J₃ Ga P K) hκa ≫ _))
    rw [DerivedCategory.Q.map_comp (@inv _ _ _ _ (totalComparison J₁ J₃ Ga P K) hκa)
      ((Stacks.DerivedTensor.totRight (sheafTensor J₃ Λ) P).map ι)]
    exact IsIso.comp_isIso' inferInstance this
  obtain ⟨e₁⟩ := nonempty_derivedBaseChangeMapArrowIso Ga Gb F F' RF RF' αF αF' θ K hK ι hL
  obtain ⟨e₂⟩ := nonempty_derivedBaseChangeMapArrowIso Ga Gb F F' RF RF' αF αF' θ
    ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K)
    (isKInjective_totalComplex J₁ K P a b hP) ι' (isKInjective_totalComplex J₃ L P a b hP)
  have h1 : IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
        ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)))) ↔
      IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex θ _).app K ≫ (F'.mapHomologicalComplex _).map ι)))) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).mapArrow.mapIso e₁)
  have h2 : IsIso ((derivedBaseChangeMap Ga Gb F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K)))) ↔
      IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex θ _).app
            ((Stacks.DerivedTensor.totRight (sheafTensor J₁ Λ) P).obj K) ≫
          (F'.mapHomologicalComplex _).map ι'))) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff e₂
  rw [h1, h2, isIso_derivedTensor_map_Qh_map_iff, isIso_Qh_map_quotient_map_iff]
  have := isIso_totalComparison J₁ J₄ (F ⋙ Gb) P a b K
  have := isIso_totalComparison J₃ J₄ F' P a b L
  exact isIso_Q_map_totRight_map_comp_iff θ P K ι

/-- If every cochain complex in `𝒜` admits a quasi-isomorphism to a K-injective complex, then
every object of the derived category of `𝒜` is isomorphic to the image of a K-injective
complex. -/
theorem exists_iso_Qh_obj_quotient_obj_of_isKInjective {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w'} 𝒜]
    (h𝒜 : ∀ K : CochainComplex 𝒜 ℤ, ∃ (I : CochainComplex 𝒜 ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q) (M : DerivedCategory 𝒜) :
    ∃ I : CochainComplex 𝒜 ℤ, I.IsKInjective ∧
      Nonempty (M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) := by
  obtain ⟨I, q, hI, hq⟩ := h𝒜 (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map q) := by rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact ⟨I, hI, ⟨(DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map q) ≪≫
    ((DerivedCategory.quotientCompQhIso 𝒜).app I).symm⟩⟩

include F' αF' in
/-- **The projection formula for `RF'`**: if `φ ⊗^L_Λ P` is invertible then so is
`RF'(φ) ⊗^L_Λ P`, for `P` a bounded complex of finitely generated projective modules. -/
theorem isIso_derivedTensor_map_rightDerived_map (P : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (a b : ℤ) [P.IsStrictlyLE b] [P.IsStrictlyGE a] [∀ q, Module.Finite Λ (P.X q)]
    [∀ q, Module.Projective Λ (P.X q)] [Stacks.DerivedTensor.IsKFlat (sheafTensor J₃ Λ) P]
    [Stacks.DerivedTensor.IsKFlat (sheafTensor J₄ Λ) P]
    {M N : DerivedCategory (Sheaf J₃ (ModuleCat.{w} Λ))} (φ : M ⟶ N)
    (hφ : IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₃ Λ) P).map φ)) :
    IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map (RF'.map φ)) := by
  obtain ⟨I, hI, ⟨eM⟩⟩ := exists_iso_Qh_obj_quotient_obj_of_isKInjective
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck M
  obtain ⟨J, hJ, ⟨eN⟩⟩ := exists_iso_Qh_obj_quotient_obj_of_isKInjective
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck N
  obtain ⟨χ, hχ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).2 (eM.inv ≫ φ ≫ eN.hom)
  obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective χ
  have hφeq : φ = eM.hom ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ) ≫
      eN.inv := by
    rw [hχ]
    simp
  rw [hφeq] at hφ ⊢
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    isIso_comp_left_iff, isIso_comp_right_iff]
  rw [Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff,
    isIso_derivedTensor_map_Qh_map_iff] at hφ
  have hP : ∀ q, Module.Finite Λ (P.X q) ∧ Module.Projective Λ (P.X q) :=
    fun q => ⟨inferInstance, inferInstance⟩
  have hI' := isIso_app_of_isKInjective _ _ RF' αF' I hI
  have hJ' := isIso_app_of_isKInjective _ _ RF' αF' J hJ
  have e1 : RF'.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ψ)) =
      inv (αF'.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
          ((HomotopyCategory.quotient _ _).map ψ) ≫
        αF'.app ((HomotopyCategory.quotient _ _).obj J) := by
    rw [IsIso.eq_inv_comp]
    exact (αF'.naturality _).symm
  rw [e1, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
  change IsIso ((Stacks.DerivedTensor.derivedTensor (sheafTensor J₄ Λ) P).map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((F'.mapHomologicalComplex _).map ψ))))
  rw [isIso_derivedTensor_map_Qh_map_iff]
  have hκI := isIso_totalComparison J₃ J₄ F' P a b I
  have hκJ := isIso_totalComparison J₃ J₄ F' P a b J
  have hQsq := congrArg DerivedCategory.Q.map (totalComparison_naturality J₃ J₄ F' P ψ)
  rw [Functor.map_comp, Functor.map_comp] at hQsq
  have hF : IsIso (DerivedCategory.Q.map ((F'.mapHomologicalComplex _).map
      (HomologicalComplex.mapBifunctorMap ψ (𝟙 P) (sheafTensor J₃ Λ) (ComplexShape.up ℤ)))) :=
    isIso_Q_map_mapHomologicalComplex_map_of_isKInjective F' RF' αF'
      (isKInjective_totalComplex J₃ I P a b hP) (isKInjective_totalComplex J₃ J P a b hP)
      (HomologicalComplex.mapBifunctorMap ψ (𝟙 P) (sheafTensor J₃ Λ) (ComplexShape.up ℤ)) hφ
  have hc : IsIso (DerivedCategory.Q.map (totalComparison J₃ J₄ F' P I) ≫
      DerivedCategory.Q.map ((F'.mapHomologicalComplex _).map
        (HomologicalComplex.mapBifunctorMap ψ (𝟙 P) (sheafTensor J₃ Λ) (ComplexShape.up ℤ)))) :=
    inferInstance
  rw [← hQsq] at hc
  exact (isIso_comp_right_iff _ (DerivedCategory.Q.map (totalComparison J₃ J₄ F' P J))).1 hc

end Stacks.ConstantModuleTensor
