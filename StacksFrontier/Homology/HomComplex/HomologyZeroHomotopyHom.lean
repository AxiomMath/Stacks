module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# Degree-zero cohomology of the linear Hom complex and the homotopy category

Let `R` be a ring and `C` an `R`-linear category. For cochain complexes `K` and `L` in `C`, the
degree-zero cohomology of the Hom complex `Hom^•(K, L)`, taken as a complex of `R`-modules
(`CochainComplex.HomComplexR`), is the group of morphisms `K ⟶ L` in the homotopy category:
a degree-zero cycle is a morphism of complexes, and it is a boundary exactly when that morphism
is null-homotopic. The identification is natural in `L`.

The corresponding statement for the Hom complex of abelian groups is Mathlib's
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`; here the cohomology is the homology
object of a complex of `R`-modules.

## Main definitions

* `Stacks.HomComplex.cyclesToHomotopyHom`: a degree-zero cycle of `Hom^•(K, L)` gives a morphism
  `K ⟶ L` in the homotopy category.
* `Stacks.HomComplex.homologyZeroHomotopyHomEquiv`: `H⁰(Hom^•(K, L)) ≃+ Hom_{K(C)}(K, L)`.

## Main results

* `Stacks.HomComplex.homologyZeroHomotopyHomEquiv_homologyπ`: the identification sends the class
  of a cycle to the homotopy class of the corresponding morphism of complexes.
* `Stacks.HomComplex.homologyZeroHomotopyHomEquiv_naturality`: naturality in the target complex.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe v u w

namespace Stacks.HomComplex

open Stacks.HomComplex.TensorHomMap (postcomp postcomp_f_apply)

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  (K L : CochainComplex C ℤ)

/-- Applying an equation `f ≫ g = k` of morphisms of modules to an element. -/
private theorem hom_apply_hom_apply_eq {M N P : ModuleCat.{v} R} {f : M ⟶ N} {g : N ⟶ P}
    {k : M ⟶ P} (h : f ≫ g = k) (x : M) : g.hom (f.hom x) = k.hom x := by
  rw [← h]
  rfl

/-- The degree-zero cochain underlying a degree-zero cycle of the Hom complex. -/
def cyclesCochain : (HomComplexR R K L).cycles 0 →ₗ[R] Cochain K L 0 :=
  ((HomComplexR R K L).iCycles 0).hom

/-- The cochain underlying a degree-zero cycle of the Hom complex is a cocycle. -/
lemma δ_cyclesCochain (c : (HomComplexR R K L).cycles 0) : δ 0 1 (cyclesCochain R K L c) = 0 := by
  exact hom_apply_hom_apply_eq R ((HomComplexR R K L).iCycles_d 0 1) c

/-- A degree-zero cycle of the Hom complex is determined by its underlying cochain. -/
lemma injective_cyclesCochain : Function.Injective (cyclesCochain R K L) :=
  (ModuleCat.mono_iff_injective ((HomComplexR R K L).iCycles 0)).1 inferInstance

/-- The degree-zero cocycle underlying a degree-zero cycle of the Hom complex. -/
def cocycleOfCycles (c : (HomComplexR R K L).cycles 0) : Cocycle K L 0 :=
  Cocycle.mk (cyclesCochain R K L c) 1 (zero_add 1) (δ_cyclesCochain R K L c)

/-- The cochain of the cocycle `cocycleOfCycles R K L c` is the cochain underlying `c`. -/
@[simp]
lemma coe_cocycleOfCycles (c : (HomComplexR R K L).cycles 0) :
    (cocycleOfCycles R K L c : Cochain K L 0) = cyclesCochain R K L c :=
  rfl

/-- **A degree-zero cycle of the Hom complex gives a morphism in the homotopy category**: the
homotopy class of the morphism of complexes it is. -/
def cyclesToHomotopyHom :
    (HomComplexR R K L).cycles 0 →+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) where
  toFun c := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    (Cocycle.homOf (cocycleOfCycles R K L c))
  map_zero' := by
    rw [← Functor.map_zero (HomotopyCategory.quotient C (ComplexShape.up ℤ)) K L]
    congr 1
    ext p
    simp
  map_add' c c' := by
    rw [← Functor.map_add]
    congr 1
    ext p
    simp

/-- `cyclesToHomotopyHom R K L c` is the image in the homotopy category of the morphism of
complexes given by `c`. -/
lemma cyclesToHomotopyHom_apply (c : (HomComplexR R K L).cycles 0) :
    cyclesToHomotopyHom R K L c = (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (Cocycle.homOf (cocycleOfCycles R K L c)) :=
  rfl

/-- The inclusion of the degree-zero cocycles into `Hom^0(K, L)`, as a morphism of modules. -/
def cocyclesSubtype :
    ModuleCat.of R (LinearMap.ker ((HomComplexR R K L).d 0 1).hom) ⟶ (HomComplexR R K L).X 0 :=
  ModuleCat.ofHom (LinearMap.ker ((HomComplexR R K L).d 0 1).hom).subtype

/-- The inclusion of the degree-zero cocycles composed with the differential `d 0 1` is zero. -/
lemma cocyclesSubtype_comp_d : cocyclesSubtype R K L ≫ (HomComplexR R K L).d 0 1 = 0 := by
  ext ⟨x, hx⟩
  exact hx

/-- The degree-zero cycle attached to a degree-zero cocycle. -/
def cyclesOfCocycle (z : Cocycle K L 0) : (HomComplexR R K L).cycles 0 :=
  ((HomComplexR R K L).liftCycles (cocyclesSubtype R K L) 1 (by simp)
    (cocyclesSubtype_comp_d R K L)).hom ⟨(z : Cochain K L 0), Cocycle.δ_eq_zero z 1⟩

/-- The cochain underlying the cycle attached to a degree-zero cocycle `z` is `z`. -/
@[simp]
lemma cyclesCochain_cyclesOfCocycle (z : Cocycle K L 0) :
    cyclesCochain R K L (cyclesOfCocycle R K L z) = (z : Cochain K L 0) := by
  exact hom_apply_hom_apply_eq R ((HomComplexR R K L).liftCycles_i (cocyclesSubtype R K L) 1
    (by simp) (cocyclesSubtype_comp_d R K L)) ⟨(z : Cochain K L 0), Cocycle.δ_eq_zero z 1⟩

/-- Every morphism `K ⟶ L` in the homotopy category is the class of a degree-zero cycle of the
Hom complex. -/
lemma surjective_cyclesToHomotopyHom : Function.Surjective (cyclesToHomotopyHom R K L) := by
  intro f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
  refine ⟨cyclesOfCocycle R K L (Cocycle.ofHom g), ?_⟩
  rw [cyclesToHomotopyHom_apply]
  congr 1
  ext p
  simp

/-- A degree-zero cycle has zero homotopy class exactly when it is a coboundary. -/
lemma cyclesToHomotopyHom_eq_zero_iff (c : (HomComplexR R K L).cycles 0) :
    cyclesToHomotopyHom R K L c = 0 ↔
      ∃ y : Cochain K L (-1), δ (-1) 0 y = cyclesCochain R K L c := by
  rw [cyclesToHomotopyHom_apply, HomotopyCategory.quotient_map_eq_zero_iff]
  constructor
  · rintro ⟨h⟩
    obtain ⟨y, hy⟩ := Cochain.equivHomotopy _ _ h
    refine ⟨y, ?_⟩
    rw [Cochain.ofHom_zero, add_zero, Cocycle.cochain_ofHom_homOf_eq_coe,
      coe_cocycleOfCycles] at hy
    exact hy.symm
  · rintro ⟨y, hy⟩
    refine ⟨(Cochain.equivHomotopy _ _).symm ⟨y, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero, Cocycle.cochain_ofHom_homOf_eq_coe, coe_cocycleOfCycles]
    exact hy.symm

/-- A degree-zero cycle has zero cohomology class exactly when it is a coboundary. -/
lemma homologyπ_eq_zero_iff (c : (HomComplexR R K L).cycles 0) :
    ((HomComplexR R K L).homologyπ 0).hom c = 0 ↔
      ∃ y : Cochain K L (-1), δ (-1) 0 y = cyclesCochain R K L c := by
  have hex : (ShortComplex.mk ((HomComplexR R K L).toCycles (-1) 0)
      ((HomComplexR R K L).homologyπ 0)
      ((HomComplexR R K L).toCycles_comp_homologyπ (-1) 0)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((HomComplexR R K L).homologyIsCokernel (-1) 0 (by simp))
  have h := hex.moduleCat_range_eq_ker
  have hd (w : (HomComplexR R K L).X (-1)) :
      ((HomComplexR R K L).iCycles 0).hom (((HomComplexR R K L).toCycles (-1) 0).hom w) =
        ((HomComplexR R K L).d (-1) 0).hom w := by
    exact hom_apply_hom_apply_eq R ((HomComplexR R K L).toCycles_i (-1) 0) w
  constructor
  · intro hz
    have hz' : c ∈ LinearMap.ker ((HomComplexR R K L).homologyπ 0).hom := hz
    rw [← h] at hz'
    obtain ⟨w, hw⟩ := hz'
    exact ⟨w, (hd w).symm.trans (congrArg ((HomComplexR R K L).iCycles 0).hom hw)⟩
  · rintro ⟨w, hw⟩
    have hz : c = ((HomComplexR R K L).toCycles (-1) 0).hom w :=
      injective_cyclesCochain R K L (hw.symm.trans (hd w).symm)
    rw [hz]
    change _ ∈ LinearMap.ker _
    rw [← h]
    exact ⟨w, rfl⟩

/-- Every degree-zero cohomology class of the Hom complex is the class of a cycle. -/
lemma surjective_homologyπ :
    Function.Surjective ((HomComplexR R K L).homologyπ 0).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- A degree-zero cycle has zero cohomology class exactly when its homotopy class is zero. -/
lemma ker_homologyπ_eq_ker_cyclesToHomotopyHom :
    (((HomComplexR R K L).homologyπ 0).hom.toAddMonoidHom).ker =
      (cyclesToHomotopyHom R K L).ker := by
  ext c
  simp only [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe]
  rw [homologyπ_eq_zero_iff, cyclesToHomotopyHom_eq_zero_iff]

/-- **Degree-zero cohomology of the Hom complex is the group of morphisms in the homotopy
category**: `H⁰(Hom^•(K, L)) ≃+ Hom_{K(C)}(K, L)`, the Hom complex being the complex of
`R`-modules `CochainComplex.HomComplexR R K L`. -/
def homologyZeroHomotopyHomEquiv :
    (HomComplexR R K L).homology 0 ≃+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
      ((HomComplexR R K L).homologyπ 0).hom.toAddMonoidHom (surjective_homologyπ R K L)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_homologyπ_eq_ker_cyclesToHomotopyHom R K L)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_cyclesToHomotopyHom R K L)))

/-- The identification sends the class of a cycle to the homotopy class of the morphism of
complexes it is. -/
lemma homologyZeroHomotopyHomEquiv_homologyπ (c : (HomComplexR R K L).cycles 0) :
    homologyZeroHomotopyHomEquiv R K L (((HomComplexR R K L).homologyπ 0).hom c) =
      cyclesToHomotopyHom R K L c := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective
      ((HomComplexR R K L).homologyπ 0).hom.toAddMonoidHom (surjective_homologyπ R K L)).symm
      (((HomComplexR R K L).homologyπ 0).hom c) = QuotientAddGroup.mk c := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [homologyZeroHomotopyHomEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, h]
  rfl

/-- **Naturality in the target complex**: postcomposition on the Hom complex is postcomposition
in the homotopy category. -/
lemma homologyZeroHomotopyHomEquiv_naturality {L L' : CochainComplex C ℤ} (g : L ⟶ L')
    (x : (HomComplexR R K L).homology 0) :
    homologyZeroHomotopyHomEquiv R K L'
        ((HomologicalComplex.homologyMap (postcomp R K L L' g) 0).hom x) =
      homologyZeroHomotopyHomEquiv R K L x ≫
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g := by
  obtain ⟨c, rfl⟩ := surjective_homologyπ R K L x
  have h1 := congrArg (fun f => f.hom c)
    (HomologicalComplex.homologyπ_naturality (postcomp R K L L' g) 0)
  have h2 : cyclesCochain R K L' ((HomologicalComplex.cyclesMap (postcomp R K L L' g) 0).hom c) =
      (cyclesCochain R K L c).comp (Cochain.ofHom g) (add_zero 0) := by
    exact hom_apply_hom_apply_eq R (HomologicalComplex.cyclesMap_i (postcomp R K L L' g) 0) c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, homologyZeroHomotopyHomEquiv_homologyπ, homologyZeroHomotopyHomEquiv_homologyπ,
    cyclesToHomotopyHom_apply, cyclesToHomotopyHom_apply, ← Functor.map_comp]
  congr 1
  ext p
  simp only [Cocycle.homOf_f, coe_cocycleOfCycles, h2, HomologicalComplex.comp_f,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

end Stacks.HomComplex

end
