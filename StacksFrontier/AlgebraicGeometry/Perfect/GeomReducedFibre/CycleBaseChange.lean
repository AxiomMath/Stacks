module

public import StacksFrontier.Homology.Perfect.FlatComplexFibreVanishing
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Degree-zero cocycles of a base change

Let `D` be a cochain complex of `R`-modules and `φ : R →+* T` a ring map. This file studies the
condition `DegreeZeroCyclesSurjective φ D`: every degree-zero cocycle of the termwise base change
`D ⊗_R T` lies in the image of `(Z⁰ D) ⊗_R T`. For a complex vanishing in negative degrees this is
the surjectivity of the degree-zero base-change map `H⁰(D) ⊗_R T → H⁰(D ⊗_R T)`.

## Main results

* `DegreeZeroCyclesSurjective.of_iso`: the condition only depends on the isomorphism class of `D`.
* `DegreeZeroCyclesSurjective.of_flat_comp`: if `φ : R → B` is flat, the condition for the
  `B`-complex `D ⊗_R B` along `ψ : B → T` gives it for `D` along `ψ ∘ φ`.
* `DegreeZeroCyclesSurjective.of_field_comp`: it descends along an extension of fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

universe u

namespace StacksDraft.Perfect.GeomReducedFibre

variable {R : Type u} [CommRing R]

/-- Every degree-zero cocycle of the base change `D ⊗_R T` comes from the base change of the
degree-zero cocycles of `D`. -/
def DegreeZeroCyclesSurjective {T : Type u} [CommRing T] (φ : R →+* T)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ x : (extendScalarsCx φ D).X 0, (extendScalarsCx φ D).d 0 1 x = 0 →
    x ∈ LinearMap.range ((ModuleCat.extendScalars.{u, u, u} φ).map (D.iCycles 0)).hom

/-- A chain map commutes with the termwise base change of the degree-zero differential. -/
theorem extendScalars_d_zero_one_apply {T : Type u} [CommRing T] (φ : R →+* T)
    {D D' : CochainComplex (ModuleCat.{u} R) ℤ} (u : D ⟶ D') (x : (extendScalarsCx φ D).X 0) :
    (extendScalarsCx φ D').d 0 1 ((ModuleCat.extendScalars.{u, u, u} φ).map (u.f 0) x) =
      (ModuleCat.extendScalars.{u, u, u} φ).map (u.f 1) ((extendScalarsCx φ D).d 0 1 x) := by
  have h := (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).map u).comm 0 1
  exact (ModuleCat.comp_apply _ _ x).symm.trans ((congrArg (fun m => m x) h).trans
    (ModuleCat.comp_apply _ _ x))

/-- The condition only depends on the isomorphism class of the complex. -/
theorem DegreeZeroCyclesSurjective.of_iso {T : Type u} [CommRing T] {φ : R →+* T}
    {D D' : CochainComplex (ModuleCat.{u} R) ℤ} (e : D ≅ D')
    (h : DegreeZeroCyclesSurjective φ D) : DegreeZeroCyclesSurjective φ D' := by
  intro x hx
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let e0 := F.mapIso ((HomologicalComplex.eval _ (ComplexShape.up ℤ) 0).mapIso e)
  have hx0 : (extendScalarsCx φ D).d 0 1 (e0.inv x) = 0 := by
    refine (extendScalars_d_zero_one_apply φ e.inv x).trans ?_
    rw [hx, map_zero]
  obtain ⟨y, hy⟩ := h _ hx0
  refine ⟨F.map (HomologicalComplex.cyclesMap e.hom 0) y, ?_⟩
  have hc : F.map (HomologicalComplex.cyclesMap e.hom 0) ≫ F.map (D'.iCycles 0) =
      F.map (D.iCycles 0) ≫ e0.hom := by
    rw [← F.map_comp, HomologicalComplex.cyclesMap_i, F.map_comp]
    rfl
  have := congrArg (fun m => m y) hc
  simp only [ModuleCat.comp_apply] at this
  show F.map (D'.iCycles 0) (F.map (HomologicalComplex.cyclesMap e.hom 0) y) = x
  rw [this]
  show e0.hom ((F.map (D.iCycles 0)).hom y) = x
  rw [hy]
  exact e0.inv_hom_id_apply x

/-- The comparison `(Z⁰ D) ⊗_R B → Z⁰(D ⊗_R B)`, lifting the base change of the inclusion of the
cocycles. -/
def cyclesBaseChange {B : Type u} [CommRing B] (φ : R →+* B)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (D.cycles 0) ⟶ (extendScalarsCx φ D).cycles 0 :=
  (extendScalarsCx φ D).liftCycles ((ModuleCat.extendScalars.{u, u, u} φ).map (D.iCycles 0)) 1
    (by simp) (by
      change (ModuleCat.extendScalars.{u, u, u} φ).map (D.iCycles 0) ≫
        (ModuleCat.extendScalars.{u, u, u} φ).map (D.d 0 1) = 0
      rw [← Functor.map_comp, D.iCycles_d, Functor.map_zero])

/-- The comparison `cyclesBaseChange φ D` followed by the inclusion of the cocycles of `D ⊗_R B`
is the base change of the inclusion of the cocycles of `D`. -/
@[reassoc (attr := simp)]
theorem cyclesBaseChange_iCycles {B : Type u} [CommRing B] (φ : R →+* B)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) :
    cyclesBaseChange φ D ≫ (extendScalarsCx φ D).iCycles 0 =
      (ModuleCat.extendScalars.{u, u, u} φ).map (D.iCycles 0) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- Along a flat ring map the comparison of cocycles is an isomorphism. -/
theorem isIso_cyclesBaseChange_of_flat {B : Type u} [CommRing B] (φ : R →+* B) (hφ : φ.Flat)
    (D : CochainComplex (ModuleCat.{u} R) ℤ) : IsIso (cyclesBaseChange φ D) := by
  let F := ModuleCat.extendScalars.{u, u, u} φ
  have : F.PreservesHomology := extendScalars_preservesHomology_of_flat.{u, u} φ hφ
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, u} φ hφ
  let S := D.sc 0
  let e : (extendScalarsCx φ D).cycles 0 ≅ F.obj (D.cycles 0) := S.mapCyclesIso F
  have h1 : e.hom ≫ F.map (D.iCycles 0) = (extendScalarsCx φ D).iCycles 0 :=
    ShortComplex.mapCyclesIso_hom_iCycles S F
  have h2 : cyclesBaseChange φ D ≫ e.hom = 𝟙 _ := by
    rw [← cancel_mono (F.map (D.iCycles 0)), Category.assoc, h1, cyclesBaseChange_iCycles,
      Category.id_comp]
  have : IsIso (cyclesBaseChange φ D ≫ e.hom) := by
    rw [h2]
    infer_instance
  exact IsIso.of_isIso_comp_right (cyclesBaseChange φ D) e.hom

/-- **Flat base change of the condition.** If `φ : R → B` is flat and every degree-zero cocycle of
`(D ⊗_R B) ⊗_B T` comes from the cocycles of `D ⊗_R B`, then every degree-zero cocycle of
`D ⊗_R T` comes from the cocycles of `D`. -/
theorem DegreeZeroCyclesSurjective.of_flat_comp {B T : Type u} [CommRing B] [CommRing T]
    (φ : R →+* B) (hφ : φ.Flat) (ψ : B →+* T) {D : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : DegreeZeroCyclesSurjective ψ (extendScalarsCx φ D)) :
    DegreeZeroCyclesSurjective (ψ.comp φ) D := by
  intro x hx
  let Fφ := ModuleCat.extendScalars.{u, u, u} φ
  let Fψ := ModuleCat.extendScalars.{u, u, u} ψ
  let Fψφ := ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)
  let c := ModuleCat.extendScalarsComp φ ψ
  have hx' : (extendScalarsCx ψ (extendScalarsCx φ D)).d 0 1 ((c.hom.app (D.X 0)) x) = 0 := by
    refine (NatTrans.naturality_apply c.hom (D.d 0 1) x).symm.trans ?_
    show (c.hom.app (D.X 1)) ((extendScalarsCx (ψ.comp φ) D).d 0 1 x) = 0
    rw [hx, map_zero]
  obtain ⟨y, hy⟩ := h _ hx'
  have := isIso_cyclesBaseChange_of_flat φ hφ D
  let y' := Fψ.map (inv (cyclesBaseChange φ D)) y
  refine ⟨c.inv.app (D.cycles 0) y', ?_⟩
  show Fψφ.map (D.iCycles 0) (c.inv.app (D.cycles 0) y') = x
  refine (NatTrans.naturality_apply c.inv (D.iCycles 0) y').symm.trans ?_
  have key : Fψ.map (inv (cyclesBaseChange φ D)) ≫ Fψ.map (Fφ.map (D.iCycles 0)) =
      Fψ.map ((extendScalarsCx φ D).iCycles 0) := by
    rw [← Functor.map_comp]
    exact congrArg Fψ.map (by rw [← cyclesBaseChange_iCycles φ D, IsIso.inv_hom_id_assoc])
  have hy' : Fψ.map (Fφ.map (D.iCycles 0)) y' = c.hom.app (D.X 0) x := by
    have := congrArg (fun m => m y) key
    simp only [ModuleCat.comp_apply] at this
    exact this.trans hy
  show c.inv.app (D.X 0) (Fψ.map (Fφ.map (D.iCycles 0)) y') = x
  rw [hy']
  exact (c.app (D.X 0)).hom_inv_id_apply x

/-- **Descent of the condition along an extension of fields.** If `φ : R → κ` lands in a field
and `ι : κ → k` is a field extension, the condition for `D` along `ι ∘ φ` gives it along `φ`. -/
theorem DegreeZeroCyclesSurjective.of_field_comp {κ k : Type u} [Field κ] [Field k]
    (φ : R →+* κ) (ι : κ →+* k) {D : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : DegreeZeroCyclesSurjective (ι.comp φ) D) : DegreeZeroCyclesSurjective φ D := by
  intro x hx
  let Fφ := ModuleCat.extendScalars.{u, u, u} φ
  let Fι := ModuleCat.extendScalars.{u, u, u} ι
  let Fιφ := ModuleCat.extendScalars.{u, u, u} (ι.comp φ)
  let c := ModuleCat.extendScalarsComp φ ι
  let j := Fφ.map (D.iCycles 0)
  let π := cokernel.π j
  let y : Fι.obj (Fφ.obj (D.X 0)) := (1 : k) ⊗ₜ[κ, ι] x
  have hdy : Fι.map (Fφ.map (D.d 0 1)) y = 0 := by
    show (1 : k) ⊗ₜ[κ, ι] ((extendScalarsCx φ D).d 0 1 x) = 0
    rw [hx]
    let : Module κ k := Module.compHom k ι
    exact TensorProduct.tmul_zero _ _
  have hz : (extendScalarsCx (ι.comp φ) D).d 0 1 (c.inv.app (D.X 0) y) = 0 := by
    show Fιφ.map (D.d 0 1) (c.inv.app (D.X 0) y) = 0
    refine (NatTrans.naturality_apply c.inv (D.d 0 1) y).symm.trans ?_
    show c.inv.app (D.X 1) (Fι.map (Fφ.map (D.d 0 1)) y) = 0
    rw [hdy, map_zero]
  obtain ⟨w, hw⟩ := h _ hz
  have hyw : Fι.map j (c.hom.app (D.cycles 0) w) = y := by
    refine (NatTrans.naturality_apply c.hom (D.iCycles 0) w).symm.trans ?_
    show c.hom.app (D.X 0) (Fιφ.map (D.iCycles 0) w) = y
    rw [show Fιφ.map (D.iCycles 0) w = c.inv.app (D.X 0) y from hw]
    exact (c.app (D.X 0)).inv_hom_id_apply y
  have hπy : Fι.map π y = 0 := by
    rw [← hyw]
    show (Fι.map j ≫ Fι.map π) (c.hom.app (D.cycles 0) w) = 0
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
    rfl
  have h1 : (1 : k) ⊗ₜ[κ, ι] (π x) = 0 := by
    rw [← ModuleCat.ExtendScalars.map_tmul]
    exact hπy
  let : Algebra κ k := ι.toAlgebra
  have h2 : (1 : k) ⊗ₜ[κ] (π x) = 0 := h1
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨z, hz⟩ := ((ShortComplex.mk j π (cokernel.condition j)).moduleCat_exact_iff.1
    (ShortComplex.exact_cokernel j)) x h2
  exact ⟨z, hz⟩

end StacksDraft.Perfect.GeomReducedFibre

end
