module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFlatAction
public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorProjection
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.MapHomologicalComplexHomologyIsoNatTrans
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyIsoId

/-!
# Flat base change of the cohomology of a tensor product of complexes

Let `A → A₁` be a flat ring map and `P`, `E` complexes of `A`-modules. The map
`Hⁿ(P ⊗_A E) → Hⁿ((A₁ ⊗_A P) ⊗_A E)` induced by the unit `P → A₁ ⊗_A P` exhibits the target, with
`A₁` acting through `A₁ ⊗_A P`, as the base change `A₁ ⊗_A Hⁿ(P ⊗_A E)`.

## Main definitions

* `RingTheory.TorIndependence.projectionMap`: the chain-level projection formula
  `L|_R ⊗_R K ⟶ (L ⊗_S (S ⊗_R K))|_R`.

## Main results

* `RingTheory.TorIndependence.isBaseChangeOfActions_homologyMap_unit_whiskerRight`: the
  base-change statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CochainComplex.ExtendScalars
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

/-! ### Linearity of the tensor product and of cohomology -/

section Linear

variable {S : Type u} [CommRing S]

/-- Multiplication by a scalar, tensored with a complex, is multiplication by that scalar. -/
theorem smul_id_whiskerRight (s : S) (X Y : CochainComplex (ModuleCat.{u} S) ℤ) :
    (s • 𝟙 X) ▷ Y = s • 𝟙 (X ⊗ Y) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  have e : (s • 𝟙 X) ▷ Y = HomologicalComplex.mapBifunctorMap (s • 𝟙 X) (𝟙 Y)
      (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ) := rfl
  rw [e, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  change ((s • 𝟙 (X.X i)) ▷ Y.X j) ≫ _ = _
  rw [MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp, Category.id_comp,
    Linear.comp_smul]
  exact congrArg (s • ·) (Category.comp_id _).symm

/-- Cohomology carries multiplication by a scalar to multiplication by that scalar. -/
theorem homologyMap_smul_id (s : S) (X : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map (s • 𝟙 X) =
      s • 𝟙 _ := by
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map
      (s • 𝟙 X) = s • 𝟙 _ := by
    ext : 1 <;> exact HomologicalComplex.smul_f_apply s (𝟙 X) _
  change ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map
      (s • 𝟙 X)) = _
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

end Linear

/-! ### The chain-level projection formula -/

section ProjectionMap

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- **The chain-level projection formula** `L|_R ⊗_R K ⟶ (L ⊗_S (S ⊗_R K))|_R`: the unit of
`K` followed by the lax monoidal structure map of restriction of scalars. -/
def projectionMap (L : CochainComplex (ModuleCat.{u} S) ℤ)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ⊗ K ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj (L ⊗ (mapCochainComplex φ).obj K) :=
  (𝟙 _ ⊗ₘ (extendRestrictScalarsComplexAdj φ).unit.app K) ≫
    restrictScalarsLaxTensor φ L ((mapCochainComplex φ).obj K)

instance (L : CochainComplex (ModuleCat.{u} S) ℤ) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (projectionMap φ L K) := by
  rw [projectionMap, ← baseChange_tensor_iso_inv_eq φ K L]
  exact Iso.isIso_inv _

/-- The projection formula is natural in the complex of `S`-modules. -/
theorem projectionMap_naturality {L L' : CochainComplex (ModuleCat.{u} S) ℤ} (v : L ⟶ L')
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v ▷ K) ≫ projectionMap φ L' K =
      projectionMap φ L K ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map (v ▷ (mapCochainComplex φ).obj K) := by
  have h := restrictScalarsLaxTensor_naturality φ v (𝟙 ((mapCochainComplex φ).obj K))
  rw [CategoryTheory.Functor.map_id] at h
  have e : ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v ▷ K) ≫
      (𝟙 _ ⊗ₘ (extendRestrictScalarsComplexAdj φ).unit.app K) =
      (𝟙 _ ⊗ₘ (extendRestrictScalarsComplexAdj φ).unit.app K) ≫
        ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v ⊗ₘ 𝟙 _) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  simp only [projectionMap, Category.assoc]
  rw [reassoc_of% e, h, tensorHom_id]

/-- The projection formula after the unit of the first factor is the unit of the tensor
product, read through the monoidality of extension of scalars. -/
theorem whiskerRight_unit_comp_projectionMap (P E : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((extendRestrictScalarsComplexAdj φ).unit.app P ▷ E) ≫
        projectionMap φ ((mapCochainComplex φ).obj P) E ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
            (extendScalarsMonoidalIso φ P E).hom =
      (extendRestrictScalarsComplexAdj φ).unit.app (P ⊗ E) := by
  set adj := extendRestrictScalarsComplexAdj φ
  have e1 : (adj.unit.app P ▷ E) ≫ (𝟙 _ ⊗ₘ adj.unit.app E) = adj.unit.app P ⊗ₘ adj.unit.app E := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have e2 : ((mapCochainComplex φ).map (adj.unit.app P) ⊗ₘ
        (mapCochainComplex φ).map (adj.unit.app E)) ≫
      (adj.counit.app ((mapCochainComplex φ).obj P) ⊗ₘ adj.counit.app ((mapCochainComplex φ).obj E)) =
      𝟙 _ := by
    rw [tensorHom_comp_tensorHom]
    exact (congrArg₂ (· ⊗ₘ ·) (adj.left_triangle_components P)
      (adj.left_triangle_components E)).trans (id_tensorHom_id _ _)
  simp only [projectionMap, Category.assoc]
  rw [reassoc_of% e1, restrictScalarsLaxTensor_comp_map, ← Adjunction.homEquiv_naturality_left,
    ← Category.assoc ((mapCochainComplex φ).map _), extendScalarsMonoidalIso_inv_naturality,
    Category.assoc, reassoc_of% e2, Iso.inv_hom_id, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end ProjectionMap

/-! ### Flat base change of the cohomology of a tensor product -/

section FlatChain

variable {A A₁ : Type u} [CommRing A] [CommRing A₁] [Algebra A A₁]

/-- The unit `M → A₁ ⊗_A M` is a base change along `A → A₁`. -/
theorem isBaseChangeOfActions_extendScalars_unit (M : ModuleCat.{u} A) :
    IsBaseChangeOfActions (Module.toAddMonoidEnd A M)
      (Module.toAddMonoidEnd A₁ ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₁)).obj M))
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₁)).unit.app M).hom.toAddMonoidHom := by
  letI iA : Module A ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₁)).obj M) :=
    Module.compHom _ (algebraMap A A₁)
  haveI iT : IsScalarTower A A₁ ((ModuleCat.extendScalars.{u, u, u} (algebraMap A A₁)).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine isBaseChangeOfActions_of_isBaseChange (instN := iA) (instT := iT)
    (fun _ _ => rfl) (fun _ _ => rfl)
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₁)).unit.app M).hom
    (fun _ => rfl) ?_
  exact IsBaseChange.of_equiv
    (StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv M).symm fun _ => rfl

omit [Algebra A A₁] in
/-- Tensoring on the right with a complex is additive. -/
instance tensorRight_additive_cochainComplex (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    (tensorRight E).Additive :=
  inferInstanceAs ((TrightCochain E).Additive)

instance restrictScalarsLarge_additive_flatChain :
    (CochainComplex.restrictScalarsLarge.{u, u, u} (algebraMap A A₁)).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars.{u} (algebraMap A A₁)).mapHomologicalComplex
    (ComplexShape.up ℤ)).Additive

variable [Module.Flat A A₁]

/-- **Flat base change of the cohomology of a tensor product of complexes.** For a flat ring map
`A → A₁` and complexes `P`, `E` of `A`-modules, the map `Hⁿ(P ⊗ E) → Hⁿ((A₁ ⊗_A P) ⊗ E)` induced
by the unit exhibits the target, with `A₁` acting through `A₁ ⊗_A P`, as `A₁ ⊗_A Hⁿ(P ⊗ E)`. -/
theorem isBaseChangeOfActions_homologyMap_unit_whiskerRight
    (P E : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    IsBaseChangeOfActions
      (functorAction (A := A) (tensorRight E ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n) P)
      (functorAction (A := A₁) (CochainComplex.restrictScalarsLarge.{u, u, u} (algebraMap A A₁) ⋙
          tensorRight E ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n)
        ((mapCochainComplex (algebraMap A A₁)).obj P))
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n).map
        ((extendRestrictScalarsComplexAdj (algebraMap A A₁)).unit.app P ▷ E)).hom.toAddMonoidHom := by
  let a := algebraMap A A₁
  let adj := extendRestrictScalarsComplexAdj a
  let restr := CochainComplex.restrictScalarsLarge.{u, u, u} a
  let ext := mapCochainComplex a
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) n
  let H₁ := HomologicalComplex.homologyFunctor (ModuleCat.{u} A₁) (ComplexShape.up ℤ) n
  let C := P ⊗ E
  let μ := extendScalarsMonoidalIso a P E
  let Φ : restr.obj (ext.obj P) ⊗ E ⟶ restr.obj (ext.obj C) :=
    projectionMap a (ext.obj P) E ≫ restr.map μ.hom
  haveI : IsIso Φ := inferInstance
  have hf' : a.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} a) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hf'
  letI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} a) :=
    ModuleCat.extendScalars_preservesFiniteColimits _
  let res := ModuleCat.restrictScalars.{u} a
  let es := ModuleCat.extendScalars.{u, u, u} a
  let mAdj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} a
  let rI := (res.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom
  let eI := (es.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom
  let rIi : H.obj (restr.obj (ext.obj C)) ≅ res.obj (H₁.obj (ext.obj C)) :=
    (res.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).app (ext.obj C)
  let eHi : H.obj (restr.obj (ext.obj C)) ≅ res.obj (es.obj (H.obj C)) :=
    rIi ≪≫
      res.mapIso ((es.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).app C)
  let eH : H.obj (restr.obj (ext.obj C)) ⟶ res.obj (es.obj (H.obj C)) := eHi.hom
  have heH : eH = rI.app (ext.obj C) ≫ res.map (eI.app C) := rfl
  let Ψi : H.obj (restr.obj (ext.obj P) ⊗ E) ≅ res.obj (es.obj (H.obj C)) :=
    H.mapIso (asIso Φ) ≪≫ eHi
  let Ψ : H.obj (restr.obj (ext.obj P) ⊗ E) ⟶ res.obj (es.obj (H.obj C)) := Ψi.hom
  have hΨ : Ψ = H.map Φ ≫ eH := rfl
  -- the unit
  have hu : adj.unit.app C = (NatTrans.mapHomologicalComplex mAdj.unit (ComplexShape.up ℤ)).app C :=
    HomologicalComplex.hom_ext _ _ fun _ => rfl
  have hF : H.map (adj.unit.app C) ≫ eH = mAdj.unit.app (H.obj C) := by
    rw [hu, heH]
    refine (Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans
      (𝟭 (ModuleCat.{u} A)) es res mAdj.unit (ComplexShape.up ℤ) n C).trans ?_
    refine (congrArg (fun t => t ≫ mAdj.unit.app (C.homology n))
      (CategoryTheory.ShortComplex.mapHomologyIso_id_hom (C.sc n))).trans (Category.id_comp _)
  have X1 : H.map (adj.unit.app P ▷ E) ≫ Ψ = mAdj.unit.app (H.obj C) := by
    rw [← hF, hΨ, ← Category.assoc, ← H.map_comp]
    exact congrArg (· ≫ eH) (congrArg H.map (whiskerRight_unit_comp_projectionMap a P E))
  have X2 : ∀ y : A₁, H.map (restr.map (y • 𝟙 (ext.obj P)) ▷ E) ≫ Ψ = Ψ ≫ res.map (y • 𝟙 _) := by
    intro y
    have w : (y • 𝟙 ((mapCochainComplex a).obj P)) ▷ ((mapCochainComplex a).obj E) ≫ μ.hom =
        μ.hom ≫ (y • 𝟙 ((mapCochainComplex a).obj C)) := by
      rw [smul_id_whiskerRight, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
        Category.comp_id]
    have c1 : (restr.map (y • 𝟙 (ext.obj P)) ▷ E) ≫ Φ = Φ ≫ restr.map (y • 𝟙 (ext.obj C)) := by
      simp only [Φ]
      rw [← Category.assoc, projectionMap_naturality, Category.assoc, ← restr.map_comp, w,
        restr.map_comp, Category.assoc]
    have c2 : H.map (restr.map (y • 𝟙 (ext.obj C))) ≫ eH = eH ≫ res.map (y • 𝟙 _) := by
      have n1 := rI.naturality (y • 𝟙 (ext.obj C))
      have n2 : H₁.map (y • 𝟙 (ext.obj C)) = y • 𝟙 _ := homologyMap_smul_id y (ext.obj C) n
      have n1' : H.map (restr.map (y • 𝟙 (ext.obj C))) ≫ rI.app (ext.obj C) =
          rI.app (ext.obj C) ≫ res.map (H₁.map (y • 𝟙 (ext.obj C))) := n1
      refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
      have h1 := congrArg (fun t => t.hom z) n1'
      change (res.map (eI.app C)).hom ((rI.app (ext.obj C)).hom
          ((H.map (restr.map (y • 𝟙 (ext.obj C)))).hom z)) =
        (res.map (y • 𝟙 _)).hom ((res.map (eI.app C)).hom ((rI.app (ext.obj C)).hom z))
      have h1' : (rI.app (ext.obj C)).hom ((H.map (restr.map (y • 𝟙 (ext.obj C)))).hom z) =
          (res.map (H₁.map (y • 𝟙 (ext.obj C)))).hom ((rI.app (ext.obj C)).hom z) := h1
      rw [h1', n2]
      exact (eI.app C).hom.map_smul y _
    rw [hΨ, ← Category.assoc, ← H.map_comp, c1, H.map_comp, Category.assoc, c2, Category.assoc]
  refine IsBaseChangeOfActions.of_equiv (AddEquiv.refl _) Ψi.symm.toLinearEquiv.toAddEquiv
    (fun x m => ?_) (fun y z => ?_) (fun m => ?_) (isBaseChangeOfActions_extendScalars_unit (H.obj C))
  · change x • m = (H.map ((tensorRight E).map (x • 𝟙 P))).hom m
    change x • m = (H.map ((x • 𝟙 P) ▷ E)).hom m
    rw [smul_id_whiskerRight, homologyMap_smul_id]
    rfl
  · have h := congrArg (fun t => t.hom (Ψi.inv.hom z)) (X2 y)
    have h2 : Ψ.hom (Ψi.inv.hom z) = z := Ψi.inv_hom_id_apply z
    change Ψi.inv.hom (y • z) = (H.map (restr.map (y • 𝟙 (ext.obj P)) ▷ E)).hom (Ψi.inv.hom z)
    have h3 : (H.map (restr.map (y • 𝟙 (ext.obj P)) ▷ E)).hom (Ψi.inv.hom z) =
        Ψi.inv.hom (Ψ.hom ((H.map (restr.map (y • 𝟙 (ext.obj P)) ▷ E)).hom (Ψi.inv.hom z))) :=
      (Ψi.hom_inv_id_apply _).symm
    rw [h3]
    refine congrArg Ψi.inv.hom ?_
    refine Eq.trans ?_ h.symm
    change y • z = (res.map (y • 𝟙 _)).hom (Ψ.hom (Ψi.inv.hom z))
    rw [h2]
    rfl
  · have h := congrArg (fun t => t.hom m) X1
    change Ψi.inv.hom (mAdj.unit.app (H.obj C) m) = _
    rw [← h]
    exact Ψi.hom_inv_id_apply _

end FlatChain

end RingTheory.TorIndependence

end
