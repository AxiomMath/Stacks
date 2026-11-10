module

public import StacksFrontier.Algebra.Homology.KoszulConeTensor
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Linear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Products
public import StacksFrontier.CategoryTheory.Triangulated.LimitOfFunctorTriangle

/-!
# Tensoring with the Koszul complex in the derived category of sheaves of modules

Let `(C, J)` be a site, `Λ` a commutative ring and `f₁, …, f_r ∈ Λ`. The Koszul complex
`Kos(f)` of sheaves of `Λ`-modules is the iterated mapping cone of multiplication by the `fᵢ`,
starting from the unit `\underline{Λ}`. Tensoring with it in `D(C, Λ)` is an exact functor which
reaches `X ⊗_Λ^L Kos(f)` from `X` by `r` cones of multiplication by the `fᵢ`.

## Main definitions

* `Stacks.ModuleSheaf.koszulComplex`: the Koszul complex `Kos(f)` of sheaves of `Λ`-modules.

## Main results

* `Stacks.ModuleSheaf.exists_cone_chain_tensor_koszulComplex`: the chain of cones from `X` to
  `X ⊗_Λ^L Kos(f)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

universe t w v u

namespace CochainComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [Preadditive C₁]
  [Preadditive C₂] [Preadditive D]

/-- **Removing the shift from the second factor of a total complex is natural in the first
factor.** -/
@[reassoc]
theorem mapBifunctorShift₂Iso_hom_naturality₁ {K₁ L₁ : CochainComplex C₁ ℤ} (f₁ : K₁ ⟶ L₁)
    (K₂ : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
    (y : ℤ) [K₁.HasMapBifunctor K₂ F] [L₁.HasMapBifunctor K₂ F]
    [K₁.HasMapBifunctor (K₂⟦y⟧) F] [L₁.HasMapBifunctor (K₂⟦y⟧) F] :
    HomologicalComplex.mapBifunctorMap f₁ (𝟙 (K₂⟦y⟧)) F (ComplexShape.up ℤ) ≫
        (L₁.mapBifunctorShift₂Iso K₂ F y).hom =
      (K₁.mapBifunctorShift₂Iso K₂ F y).hom ≫
        (HomologicalComplex.mapBifunctorMap f₁ (𝟙 K₂) F (ComplexShape.up ℤ))⟦y⟧' := by
  ext n p q h
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]
  simp

/-- **The shift isomorphisms of the functors `K₁ ⊗ -` on cochain complexes are natural in
`K₁`.** -/
@[reassoc]
theorem map₂CochainComplex_map_app_commShiftIso_hom_app {K₁ L₁ : CochainComplex C₁ ℤ}
    (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
    [∀ X₁, (F.obj X₁).Additive]
    [∀ (X₁ : CochainComplex C₁ ℤ) (X₂ : CochainComplex C₂ ℤ), X₁.HasMapBifunctor X₂ F] (y : ℤ) :
    (F.map₂CochainComplex.map f₁).app (K₂⟦y⟧) ≫
        ((F.map₂CochainComplex.obj L₁).commShiftIso y).hom.app K₂ =
      ((F.map₂CochainComplex.obj K₁).commShiftIso y).hom.app K₂ ≫
        ((F.map₂CochainComplex.map f₁).app K₂)⟦y⟧' := by
  rw [Functor.commShiftIso_map₂CochainComplex_hom_app,
    Functor.commShiftIso_map₂CochainComplex_hom_app]
  exact mapBifunctorShift₂Iso_hom_naturality₁ f₁ K₂ F y

end CochainComplex

namespace CategoryTheory.Functor

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ] [HasShift 𝒞 ℤ] [HasShift 𝒟 ℤ]
  [HasShift ℰ ℤ]

/-- Composing a map `Z ⟶ Y⟦1⟧` with the shift isomorphisms of two functors related by a
transformation compatible with the shift at `Y`, and then with a functor commuting with shifts,
is natural along the transformation. -/
theorem map_comp_commShiftIso_naturality {F G : 𝒞 ⥤ 𝒟} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : F ⟶ G) {Y Z : 𝒞} (f : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hα : α.app (Y⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app Y =
      (F.commShiftIso (1 : ℤ)).hom.app Y ≫ (α.app Y)⟦(1 : ℤ)⟧')
    (L : 𝒟 ⥤ ℰ) [L.CommShift ℤ] :
    L.map (α.app Z) ≫ (L.map (G.map f ≫ (G.commShiftIso (1 : ℤ)).hom.app Y) ≫
        (L.commShiftIso (1 : ℤ)).hom.app (G.obj Y)) =
      (L.map (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y) ≫
        (L.commShiftIso (1 : ℤ)).hom.app (F.obj Y)) ≫ (L.map (α.app Y))⟦(1 : ℤ)⟧' := by
  rw [Category.assoc, ← L.commShiftIso_hom_naturality, ← L.map_comp_assoc, ← L.map_comp_assoc,
    ← α.naturality_assoc, hα, Category.assoc]

end CategoryTheory.Functor

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- **The Koszul complex** `Kos(f₁, …, f_r)` of sheaves of `Λ`-modules: the iterated mapping
cone of multiplication by the `fᵢ` on the unit complex `\underline{Λ}[0]`. -/
abbrev koszulComplex {r : ℕ} (f : Fin r → Λ) : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  Stacks.KoszulCone.koszulTensor r f (𝟙_ (CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ))

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

variable {J Λ}

/-- **The chain of cones from `X` to `X ⊗_Λ^L Kos(f)`.** In `D(C, Λ)` there are objects
`M₀ ≅ X, M₁, …, M_r ≅ X ⊗_Λ^L Kos(f)` and distinguished triangles
`Mᵢ --fᵢ--> Mᵢ → Mᵢ₊₁ → Mᵢ[1]`. -/
theorem exists_cone_chain_tensor_koszulComplex {r : ℕ} (f : Fin r → Λ)
    (X : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    ∃ (M : Fin (r + 1) → DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
      (v : ∀ i : Fin r, M i.castSucc ⟶ M i.succ)
      (w : ∀ i : Fin r, M i.succ ⟶ (M i.castSucc)⟦(1 : ℤ)⟧),
      (∀ i, Triangle.mk (f i • 𝟙 (M i.castSucc)) (v i) (w i) ∈ distTriang _) ∧
        Nonempty (M 0 ≅ X) ∧
        Nonempty (M (Fin.last r) ≅ X ⊗ DerivedCategory.Q.obj (koszulComplex J Λ f)) := by
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorLeft J Λ X
  let Y : (i : ℕ) → i ≤ r → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ := fun i h ↦
    Stacks.KoszulCone.koszulTensor i (fun j ↦ f (Fin.castLE h j))
      (𝟙_ (CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ))
  refine ⟨fun i ↦ X ⊗ DerivedCategory.Q.obj (Y i (Nat.lt_succ_iff.mp i.isLt)),
    fun i ↦ X ◁ DerivedCategory.Q.map (CochainComplex.mappingCone.inr
      (f i • 𝟙 (Y i i.isLt.le))),
    fun i ↦ X ◁ (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
      (f i • 𝟙 (Y i i.isLt.le))).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _) ≫
      ((tensorLeft X).commShiftIso (1 : ℤ)).hom.app _, fun i ↦ ?_, ⟨?_⟩, ⟨Iso.refl _⟩⟩
  · have hT := (tensorLeft X).map_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (f i • 𝟙 (Y i i.isLt.le)))
    have h : f i • 𝟙 (X ⊗ DerivedCategory.Q.obj (Y i i.isLt.le)) =
        X ◁ DerivedCategory.Q.map (f i • 𝟙 (Y i i.isLt.le)) := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, derived_whiskerLeft_smul_id]
    change Triangle.mk (f i • 𝟙 (X ⊗ DerivedCategory.Q.obj (Y i i.isLt.le))) _ _ ∈ _
    rw [h]
    exact hT
  · exact whiskerLeftIso X (CochainComplex.KFlatMonoidal.derivedUnitIso _
      (exists_kFlat_quasiIso (J := J) (Λ := Λ))).symm ≪≫ ρ_ X

/-- The connecting map `Q(X ⊗ Cone(φ)) ⟶ Q(X ⊗ Ỹ)[1]` of the image in `D(C, Λ)` of the
mapping cone triangle of `φ : Ỹ ⟶ Ỹ` tensored on the left with `X`. -/
def Q_map₂CochainComplex_mappingConeδ {Y : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (φ : Y ⟶ Y) (X : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    DerivedCategory.Q.obj (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.obj
        X).obj (CochainComplex.mappingCone φ)) ⟶
      (DerivedCategory.Q.obj (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.obj
        X).obj Y))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map ((((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.obj
      X).map ((CochainComplex.mappingCone.triangle φ).mor₃ :
      CochainComplex.mappingCone φ ⟶ Y⟦(1 : ℤ)⟧)) ≫
      ((((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.obj X).commShiftIso
        (1 : ℤ)).hom.app Y)) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _

/-- The connecting maps `Q_map₂CochainComplex_mappingConeδ` are natural in `X`. -/
theorem Q_map₂CochainComplex_mappingConeδ_naturality
    {Y : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (φ : Y ⟶ Y)
    {X X' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (g : X ⟶ X') :
    DerivedCategory.Q.map (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map
        g).app (CochainComplex.mappingCone φ)) ≫ Q_map₂CochainComplex_mappingConeδ φ X' =
    Q_map₂CochainComplex_mappingConeδ φ X ≫
      (DerivedCategory.Q.map (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map
        g).app Y))⟦(1 : ℤ)⟧' :=
  Functor.map_comp_commShiftIso_naturality _ _
    (CochainComplex.map₂CochainComplex_map_app_commShiftIso_hom_app g Y _ 1) _

/-- **Tensoring on the right with a cone of an endomorphism preserves the products that
tensoring with the complex itself preserves**, after localization: if the maps
`Q(P ⊗ Ỹ) ⟶ Q(xⱼ ⊗ Ỹ)` exhibit a product in `D(C, Λ)`, so do the maps
`Q(P ⊗ Cone(φ)) ⟶ Q(xⱼ ⊗ Cone(φ))`. -/
theorem isIso_lift_Q_map_map₂CochainComplex_mappingCone {ι : Type} [HasProductsOfShape ι
    (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
    {x : ι → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (π : ∀ j, P ⟶ x j)
    {Y : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (φ : Y ⟶ Y)
    (h : IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map
      (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map (π j)).app Y))) :
    IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map
      (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map (π j)).app
        (CochainComplex.mappingCone φ))) := by
  let B := (curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex
  exact isIso_lift_map_of_distTriang (F := B.flip.obj Y ⋙ DerivedCategory.Q)
    (G := B.flip.obj (CochainComplex.mappingCone φ) ⋙ DerivedCategory.Q) π
    (Functor.whiskerRight (B.flip.map φ) DerivedCategory.Q)
    (Functor.whiskerRight (B.flip.map (CochainComplex.mappingCone.inr φ)) DerivedCategory.Q)
    { app X := (DerivedCategory.Q.mapTriangle.obj ((B.obj X).mapTriangle.obj
        (CochainComplex.mappingCone.triangle φ))).mor₃
      naturality X X' g := Q_map₂CochainComplex_mappingConeδ_naturality φ g }
    (fun X ↦ isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished
      ((B.obj X).map φ)) _ (DerivedCategory.Q.mapTriangle.mapIso
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorMapTriangleIso
          (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) X φ))) h

end Stacks.ModuleSheaf
