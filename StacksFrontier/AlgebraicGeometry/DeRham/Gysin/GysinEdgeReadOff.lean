module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift

/-!
# The degree-`c` cohomology of `A[0] ⊗^L G[c]`

The canonical map `A[0] ⊗^L G[c] ⟶ Tot(A[0] ⊗ G[c])` is an isomorphism on cohomology in degree
`c`, with no hypothesis on `A` or `G`: `isIso_homologyMap_toTensor_singleShift`. Resolving
`A[0]` by a bounded above complex of flat modules reduces this to right exactness of `- ⊗ G`,
after the shift by `c` is moved out of the total tensor complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u d

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

/-- A functor inverts `g` if `f ≫ g = k ≫ l` with `f`, `k` isomorphisms and `l` inverted. -/
private lemma isIso_map_of_comp_eq {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ d) (l : d ⟶ c) (hf : IsIso f) (hk : IsIso k)
    (hl : IsIso (H.map l)) (h : f ≫ g = k ≫ l) : IsIso (H.map g) := by
  have : IsIso (H.map (f ≫ g)) := by rw [h, H.map_comp]; infer_instance
  rw [H.map_comp] at this
  exact IsIso.of_isIso_comp_left (H.map f) (H.map g)

/-- A functor inverts `k` if `f₁ ≫ f₂ ≫ g = k ≫ l` with `f₁`, `f₂`, `l` isomorphisms and `g`
inverted. -/
private lemma isIso_map_of_comp_eq' {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {a b b' c d : C} (f₁ : a ⟶ b) (f₂ : b ⟶ b') (g : b' ⟶ c) (k : a ⟶ d) (l : d ⟶ c)
    (hf₁ : IsIso f₁) (hf₂ : IsIso f₂) (hg : IsIso (H.map g)) (hl : IsIso l)
    (h : f₁ ≫ f₂ ≫ g = k ≫ l) : IsIso (H.map k) := by
  have e : H.map k = H.map (f₁ ≫ f₂ ≫ g) ≫ H.map (inv l) := by
    rw [h, ← H.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [e, H.map_comp, H.map_comp]
  infer_instance

/-- A functor carries a retraction to a retraction. At variables. -/
private lemma map_comp_eq_id {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {a b : C}
    (f : a ⟶ b) (g : b ⟶ a) (h : f ≫ g = 𝟙 a) : F.map f ≫ F.map g = 𝟙 _ := by
  rw [← F.map_comp, h, F.map_id]

section StandardModel

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

section Generic

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules R)]

/-- **`H^c(A[0] ⊗^L G[c]) = H^c(Tot(A[0] ⊗ G[c]))`**: the canonical map is an isomorphism on
cohomology in degree `c`. -/
theorem isIso_homologyMap_toTensor_singleShift
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d} R)
    (A B : Stacks.DerivedTensor.RingedSite.Modules R) (c : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (Stacks.DerivedTensor.RingedSite.Modules R) c).map
      (T.toTensor
        ((CochainComplex.singleFunctor _ 0).obj A)
        ((CochainComplex.singleFunctor _ c).obj B))) := by
  let sA := (CochainComplex.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj A
  let sB := (CochainComplex.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules R) c).obj B
  let sB₀ := (CochainComplex.singleFunctor (Stacks.DerivedTensor.RingedSite.Modules R) 0).obj B
  let F := sheafTensor.{_, _, _, u, u} R
  let G := F.flip.obj B
  obtain ⟨L, s, hs, hLflat, hLE⟩ := (CochainComplex.exists_quasiIso_prop
    (Stacks.DerivedTensor.RingedSite.flatModules R)
    (fun M => by
      obtain ⟨N, π, hflat, hepi⟩ :=
        Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat R M
      exact ⟨N, hflat, π, hepi⟩) 0).2 sA
  have hL : Stacks.SheafOfModules.IsKFlat R L :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat R L ⟨0, hLE⟩ hLflat
  have nat := T.toTensor_naturality s (𝟙 sB)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id] at nat
  replace nat := (congrArg (_ ≫ ·) (Category.id_comp _)).symm.trans nat
  rw [T.toTensor_eq_comparisonLeft L sB hL] at nat
  have hQs : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  -- the shifted map of total complexes
  let e := ((CochainComplex.singleFunctors (Stacks.DerivedTensor.RingedSite.Modules R)).shiftIso
    (-c) c 0 (by omega)).app B
  let m := HomologicalComplex.mapBifunctorMap s (𝟙 sB) F (ComplexShape.up ℤ)
  let m₀ := HomologicalComplex.mapBifunctorMap s (𝟙 sB₀) F (ComplexShape.up ℤ)
  have h₀ : IsIso (HomologicalComplex.homologyMap m₀ 0) := by
    have hm : m₀ = (HomologicalComplex.mapBifunctorSingleRightIso _ L B).hom ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map s ≫
          (HomologicalComplex.mapBifunctorSingleRightIso _ sA B).inv := by
      rw [← HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_assoc, Iso.hom_inv_id,
        Category.comp_id]
    have : IsIso (HomologicalComplex.homologyMap s 0) := inferInstance
    have hG : IsIso (HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0) :=
      HomologicalComplex.isIso_homologyMap_mapHomologicalComplex_zero G s
    rw [hm, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    infer_instance
  -- the shift out of the total complex
  let m' := HomologicalComplex.mapBifunctorMap s (𝟙 (sB₀⟦-c⟧)) F (ComplexShape.up ℤ)
  have h₁ : IsIso (HomologicalComplex.homologyMap (m₀⟦-c⟧') c) :=
    (NatIso.isIso_map_iff ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso
      (-c) c 0 (by omega)) m₀).2 h₀
  have hsq := Stacks.Cohomology.DerivedGlobalCupProduct.mapBifunctorShift₂Iso_hom_naturality₁
    F s sB₀ (-c)
  have h₂ : IsIso (HomologicalComplex.homologyMap m' c) := by
    have h := congrArg (fun t => HomologicalComplex.homologyMap t c) hsq
    simp only [HomologicalComplex.homologyMap_comp] at h
    have : IsIso (HomologicalComplex.homologyMap m' c ≫ HomologicalComplex.homologyMap
        (CochainComplex.mapBifunctorShift₂Iso sA sB₀ F (-c)).hom c) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap m' c)
      (HomologicalComplex.homologyMap (CochainComplex.mapBifunctorShift₂Iso sA sB₀ F (-c)).hom c)
  have h₃ : IsIso (HomologicalComplex.homologyMap m c) := by
    have hc : HomologicalComplex.mapBifunctorMap (𝟙 L) e.hom F (ComplexShape.up ℤ) ≫ m =
        m' ≫ HomologicalComplex.mapBifunctorMap (𝟙 sA) e.hom F (ComplexShape.up ℤ) := by
      simp only [m, m', HomologicalComplex.mapBifunctorMap_comp, Category.id_comp]
      exact congrArg (fun t => HomologicalComplex.mapBifunctorMap s t F (ComplexShape.up ℤ))
        (Category.comp_id _)
    have hiso : ∀ (P : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ),
        IsIso (HomologicalComplex.mapBifunctorMap (𝟙 P) e.hom F (ComplexShape.up ℤ)) := fun P =>
      ⟨HomologicalComplex.mapBifunctorMap (𝟙 P) e.inv F (ComplexShape.up ℤ), by
        rw [HomologicalComplex.mapBifunctorMap_comp, Iso.hom_inv_id, Category.id_comp,
          HomologicalComplex.mapBifunctorMap_id], by
        rw [HomologicalComplex.mapBifunctorMap_comp, Iso.inv_hom_id, Category.id_comp,
          HomologicalComplex.mapBifunctorMap_id]⟩
    have h := congrArg (fun t => HomologicalComplex.homologyMap t c) hc
    simp only [HomologicalComplex.homologyMap_comp] at h
    have : IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.mapBifunctorMap (𝟙 L) e.hom F (ComplexShape.up ℤ)) c ≫
          HomologicalComplex.homologyMap m c) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
      (HomologicalComplex.mapBifunctorMap (𝟙 L) e.hom F (ComplexShape.up ℤ)) c)
      (HomologicalComplex.homologyMap m c)
  have h₄ := (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ c)
    (HomologicalComplex.mapBifunctorMap s (𝟙 sB) (sheafTensor.{_, _, _, u, u} R)
      (ComplexShape.up ℤ))).2 h₃
  have k₁ : IsIso ((T.tensor.map (DerivedCategory.Q.map s)).app (DerivedCategory.Q.obj sB)) :=
    inferInstance
  have h₄' : IsIso ((DerivedCategory.homologyFunctor
      (Stacks.DerivedTensor.RingedSite.Modules R) c).map (DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap s (𝟙 sB) (sheafTensor.{_, _, _, u, u} R)
          (ComplexShape.up ℤ)))) := h₄
  exact isIso_map_of_comp_eq _ _ _ _ _ k₁ (Iso.isIso_hom (T.comparisonLeft L sB hL)) h₄' nat

/-- `isIso_homologyMap_toTensor_singleShift` transported along isomorphisms of complexes. -/
theorem isIso_homologyMap_toTensor_of_iso
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d} R)
    {K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules R) ℤ}
    (A B : Stacks.DerivedTensor.RingedSite.Modules R) (c : ℤ)
    (eK : K ≅ (CochainComplex.singleFunctor _ 0).obj A)
    (eL : L ≅ (CochainComplex.singleFunctor _ c).obj B) :
    IsIso ((DerivedCategory.homologyFunctor (Stacks.DerivedTensor.RingedSite.Modules R) c).map
      (T.toTensor K L)) := by
  have nat := T.toTensor_naturality eK.hom eL.hom
  refine isIso_map_of_comp_eq' _ _ _ _ _ _ inferInstance inferInstance
    (isIso_homologyMap_toTensor_singleShift R T A B c) ?_ nat
  refine ⟨DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap eK.inv eL.inv _ _), ?_, ?_⟩
  · exact map_comp_eq_id DerivedCategory.Q _ _
      ((HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _).trans (by
        rw [Iso.hom_inv_id, Iso.hom_inv_id, HomologicalComplex.mapBifunctorMap_id]; rfl))
  · exact map_comp_eq_id DerivedCategory.Q _ _
      ((HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _).trans (by
        rw [Iso.inv_hom_id, Iso.inv_hom_id, HomologicalComplex.mapBifunctorMap_id]; rfl))

end Generic

end StandardModel

end Stacks.DeRham.GysinCupHodge
