module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechBaseChangeFinite
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethCechDegreeOne
public import StacksFrontier.Algebra.Module.ConeNakayamaGlobal
public import StacksFrontier.AlgebraicGeometry.Modules.TrivialGenerator

/-!
# The theorem of the cube: Čech complexes over an affine chart of the third factor

Let `A` be a group scheme over a field `k` and `P = (A × A) × A` its triple self-product, with
projection `q : P ⟶ A × A` to the first two factors and `r : P ⟶ A` to the third. For an affine
open `V ⊆ A` with ring of functions `R`, the open `P_V = r⁻¹ V` is a scheme over `Spec R`, and a
finite affine open cover `U` of `A` gives the affine open cover `U a × U b × V` of `P_V`.

For a sheaf of modules `N` on `P`, this file defines the alternating Čech complex of `N` on
`P_V` for that cover, as a complex of `R`-modules, and the two-term complex of `R`-modules built
from functions on the opens `U_j × V` of `A × A`, with the evaluation at the identity point.

This is the set-up of the cohomology-and-base-change proof of the theorem of the cube,
[Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4), through
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2).

## Main definitions

* `Stacks.Cube.chartComplex`: The alternating Čech complex of `N` on `P_V`, over `R`.
* `Stacks.Cube.faceD`: The Čech differential on functions on the opens `U_j × V`.
* `Stacks.Cube.evalE`: Evaluation of a degree-zero face cochain at the identity point.
* `Stacks.Cube.targetD`: The differential of the two-term target complex.

## Main results

* `Stacks.Cube.baseRingHom_chartMap_apply`: The ring `R` acts on sections over the chart
  through `r`.

## References

* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
open CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Cube

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- `A × A`. -/
noncomputable abbrev B : Scheme.{u} := (A ⊗ A).left

/-- `(A × A) × A`. -/
noncomputable abbrev P : Scheme.{u} := (Stacks.Groupoids.cubeObj A).left

/-- The first factor of `A × A`. -/
noncomputable abbrev bx : B A ⟶ A.left := pullback.fst A.hom A.hom

/-- The second factor of `A × A`. -/
noncomputable abbrev bz : B A ⟶ A.left := pullback.snd A.hom A.hom

/-- The projection `(A × A) × A ⟶ A × A`. -/
noncomputable abbrev q : P A ⟶ B A := pullback.fst (A ⊗ A).hom A.hom

/-- The projection `(A × A) × A ⟶ A` to the third factor. -/
noncomputable abbrev r : P A ⟶ A.left := pullback.snd (A ⊗ A).hom A.hom

/-- `A × A`, with its two projections, is the fibre product of `A` with itself over `k`. -/
theorem isPullback_B : IsPullback (bx A) (bz A) A.hom A.hom := IsPullback.of_hasPullback _ _

/-! ### The affine chart over `V` -/

section Chart

variable {A} {V : A.left.Opens} (hV : IsAffineOpen V)

/-- The open `P_V = r⁻¹ V` of the triple product. -/
noncomputable abbrev PV (V : A.left.Opens) : (P A).Opens := r A ⁻¹ᵁ V

/-- The ring of functions of the chart. -/
abbrev chartRing (V : A.left.Opens) : Type u := Γ(A.left, V)

/-- The structure morphism of `P_V` over `Spec R`. -/
noncomputable def chartMap : (PV V).toScheme ⟶ Spec (.of (chartRing V)) :=
  (r A ∣_ V) ≫ hV.isoSpec.hom

variable {ι : Type u} (U : ι → A.left.Opens)

/-- The product cover of `A × A`. -/
noncomputable abbrev coverB : ι × ι → (B A).Opens :=
  Stacks.KunnethCech.prodCover (bx A) (bz A) U U

/-- The induced cover of `P_V`: the members `U a × U b × V`. -/
noncomputable def chartCover (V : A.left.Opens) (ab : ι × ι) : (PV V).toScheme.Opens :=
  (PV V).ι ⁻¹ᵁ (q A ⁻¹ᵁ coverB U ab)

variable (N : (P A).Modules)

/-- The module `N` restricted to the chart. -/
noncomputable abbrev chartModule (V : A.left.Opens) : (PV V).toScheme.Modules :=
  N.restrict (PV V).ι

/-- **The Čech complex of `N` over the chart**, a complex of modules over the ring of functions
of `V`. -/
noncomputable abbrev chartComplex :
    CochainComplex (ModuleCat.{u} (chartRing V)) ℕ :=
  Stacks.Cech.alternatingCechModuleComplex (chartMap hV) (chartCover U V) (chartModule N V)

/-- The image in `P` of an open of `P_V` lies in `r⁻¹ V`. -/
theorem image_le_preimage (V : A.left.Opens) (O' : (PV V).toScheme.Opens) :
    (PV V).ι ''ᵁ O' ≤ r A ⁻¹ᵁ V := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

/-- **The ring of the chart acts on sections over the chart through `r`.** -/
theorem baseRingHom_chartMap_apply (O' : (PV V).toScheme.Opens) (a : chartRing V) :
    (Stacks.Cech.baseRingHom (chartMap hV) O').hom a =
      (r A).appLE V ((PV V).ι ''ᵁ O') (image_le_preimage V O') a := by
  have e1 : Stacks.Cech.baseRingHom (chartMap hV) O' =
      (Scheme.ΓSpecIso Γ(A.left, V)).inv ≫ hV.isoSpec.hom.appTop ≫
        (r A ∣_ V).appLE ⊤ O' (Stacks.AffineProduct.le_preimage_top _ O') := by
    rw [Stacks.Cech.baseRingHom_eq_appLE (chartMap hV) O'
      (Stacks.AffineProduct.le_preimage_top _ O')]
    simp only [chartMap, Scheme.Hom.comp_appLE]
    rfl
  have e2 : (Scheme.ΓSpecIso Γ(A.left, V)).inv ≫ hV.isoSpec.hom.appTop = V.topIso.inv := by
    rw [IsAffineOpen.isoSpec_hom_appTop]
    exact (Scheme.ΓSpecIso Γ(A.left, V)).inv_hom_id_assoc _
  rw [e1, ← Category.assoc, e2, morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  exact congr($(Scheme.Hom.map_appLE' (r A) (image_le_preimage V O') V.ι_image_top) a)

end Chart

/-! ### The target complex: functions on the faces over the chart -/

section Target

open Stacks.KunnethCech

variable {A} (V : A.left.Opens) {ι : Type u} (U : ι → A.left.Opens)

/-- The open `U_j × V` of `A × A`. -/
noncomputable abbrev faceOpen {n : ℕ} (j : Fin n → ι) : (B A).Opens :=
  Stacks.AffineProduct.prodOpen (bx A) (bz A) (CechCochains.inter U j) V

/-- Degree-`p` cochains of functions on the face over the chart: a function on `U_j × V` for
every tuple `j`. -/
abbrev FaceCochain (p : ℕ) : Type u := ∀ j : Fin (p + 1) → ι, Γ(B A, faceOpen V U j)

/-- The ring of the chart acts on functions on `U_j × V` through the second projection. -/
noncomputable def faceAct {n : ℕ} (j : Fin n → ι) : chartRing V →+* Γ(B A, faceOpen V U j) :=
  ((bz A).appLE V (faceOpen V U j)
    (Stacks.AffineProduct.prodOpen_le_snd (bx A) (bz A) _ _)).hom

/-- The module structure on face cochains. -/
@[instance_reducible]
noncomputable def faceModule (p : ℕ) : Module (chartRing V) (FaceCochain V U p) :=
  letI := fun (j : Fin (p + 1) → ι) => Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
  inferInstanceAs (Module (chartRing V) (∀ j : Fin (p + 1) → ι, Γ(B A, faceOpen V U j)))

/-- A scalar acts on a face cochain componentwise, through `faceAct`. -/
theorem face_smul_apply (p : ℕ) (a : chartRing V) (F : FaceCochain V U p)
    (j : Fin (p + 1) → ι) :
    letI := faceModule V U p
    (a • F) j = faceAct V U j a * F j := rfl

/-- Restriction between faces commutes with the action of the ring of the chart. -/
theorem res_faceAct {n m : ℕ} {j : Fin n → ι} {j' : Fin m → ι}
    (h : faceOpen V U j ≤ faceOpen V U j') (a : chartRing V) :
    res h (faceAct V U j' a) = faceAct V U j a := by
  simp only [faceAct]
  rw [res_appLE]

/-- The Čech differential of face cochains. -/
noncomputable def faceD (p : ℕ) :
    letI := faceModule V U p
    letI := faceModule V U (p + 1)
    FaceCochain V U p →ₗ[chartRing V] FaceCochain V U (p + 1) :=
  letI := faceModule V U p
  letI := faceModule V U (p + 1)
  { toFun := fun F j => ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
      (res (Stacks.AffineProduct.prodOpen_mono (bx A) (bz A)
        (CechCochains.inter_le_omit U j l) le_rfl) (F (j ∘ l.succAbove)))
    map_add' := fun F G => by
      funext j
      simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
    map_smul' := fun a F => by
      funext j
      rw [face_smul_apply, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [face_smul_apply, map_mul, res_faceAct, mul_smul_comm] }

/-- The value of the Čech differential of a face cochain on a tuple `j` is the alternating sum
of the restrictions of its values on the faces of `j`. -/
theorem faceD_apply (p : ℕ) (F : FaceCochain V U p) (j : Fin (p + 2) → ι) :
    letI := faceModule V U p
    letI := faceModule V U (p + 1)
    faceD V U p F j = ∑ l : Fin (p + 2), ((-1 : ℤ) ^ (l : ℕ)) •
      (res (Stacks.AffineProduct.prodOpen_mono (bx A) (bz A)
        (CechCochains.inter_le_omit U j l) le_rfl) (F (j ∘ l.succAbove))) := rfl

attribute [local instance] faceModule

variable [GrpObj A]

/-- The identity point of `A`. -/
noncomputable abbrev eA : Spec (.of k) ⟶ A.left := (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ A).left

/-- The identity point is a section of the structure morphism of `A`. -/
theorem eA_hom : eA (A := A) ≫ A.hom = 𝟙 _ :=
  Over.w (MonObj.one : 𝟙_ (Over (Spec (.of k))) ⟶ A)

/-- The section `z ↦ (e, z)` of the second projection of `A × A`. -/
noncomputable def σe : A.left ⟶ B A :=
  pullback.lift (A.hom ≫ eA) (𝟙 A.left) (by rw [Category.assoc, eA_hom, Category.comp_id,
    Category.id_comp])

/-- The first coordinate of `σe` is the constant map to the identity point. -/
@[reassoc (attr := simp)] theorem σe_bx : σe (A := A) ≫ bx A = A.hom ≫ eA := pullback.lift_fst _ _ _

/-- The second coordinate of `σe` is the identity. -/
@[reassoc (attr := simp)] theorem σe_bz : σe (A := A) ≫ bz A = 𝟙 _ := pullback.lift_snd _ _ _

variable {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)
include ha₀

/-- If the identity point lies in `U a₀`, then `σe` maps `V` into `U a₀ × V`. -/
theorem le_σe_preimage : V ≤ σe ⁻¹ᵁ faceOpen V U (fun _ : Fin 1 => a₀) := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change (σe ≫ bx A) z ∈ CechCochains.inter U (fun _ : Fin 1 => a₀)
    rw [σe_bx, mem_inter]
    intro _
    have : A.hom z ∈ eA (A := A) ⁻¹ᵁ U a₀ := by rw [ha₀]; trivial
    exact this
  · change (σe ≫ bz A) z ∈ V
    rw [σe_bz]; exact hz

/-- Evaluation of a degree-zero face cochain at the identity point. -/
noncomputable def evalE : FaceCochain V U 0 →ₗ[chartRing V] chartRing V where
  toFun u := σe.appLE _ V (le_σe_preimage V U ha₀) (u (fun _ => a₀))
  map_add' u u' := by simp
  map_smul' a u := by
    rw [face_smul_apply, map_mul, RingHom.id_apply, smul_eq_mul]
    congr 1
    simp only [faceAct]
    rw [appLE_comp, appLE_congr (σe_bz (A := A)), id_appLE_self]

/-- The differential of the target two-term complex. -/
noncomputable def targetD :
    FaceCochain V U 0 × FaceCochain V U 0 →ₗ[chartRing V]
      FaceCochain V U 1 × FaceCochain V U 1 × chartRing V :=
  ((faceD V U 0).comp (LinearMap.fst _ _ _)).prod (((faceD V U 0).comp (LinearMap.snd _ _ _)).prod
    ((evalE V U ha₀).comp (LinearMap.fst _ _ _) - (evalE V U ha₀).comp (LinearMap.snd _ _ _)))

end Target

end Stacks.Cube

end
