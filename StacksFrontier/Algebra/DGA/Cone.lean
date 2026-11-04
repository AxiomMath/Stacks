module

public import Mathlib.LinearAlgebra.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# Mapping cones of differential graded module homomorphisms

The cone of a homomorphism `f : K ⟶ L` has underlying module `L × K`, degree-`n`
part `Lⁿ × Kⁿ⁺¹`, and differential `(l, k) ↦ (d l + f k, -d k)`.
The inclusion of `L` and projection to `K[1]` are canonical morphisms.

## Main definitions

* `DifferentialGradedModule.Cone` specifies the cone together with its canonical maps.
* `DifferentialGradedModule.cone` constructs this data.
* `DifferentialGradedModule.coneModule`, `DifferentialGradedModule.coneInclusion`, and
  `DifferentialGradedModule.coneProjection` expose the module and maps to clients.

## Implementation notes

The construction is bundled with an underlying linear equivalence to `L.M × K.M`.
This equivalence fixes the grading, differential, inclusion, and projection without
depending on a particular implementation of the internal direct-sum decomposition.
The displayed maps are differential graded module homomorphisms, hence in particular
morphisms of the underlying cochain complexes. The single construction obligation
inhabits the subtype-like specification `Cone`; its projections are the canonical API.

## References

* [Stacks Project, Tag 09KA](https://stacks.math.columbia.edu/tag/09KA)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}
variable {K L : DifferentialGradedModule.{u, v, w} A}

/-- The cone data of a differential graded module homomorphism. Its chosen
underlying linear equivalence records the prescribed direct-sum coordinates. -/
structure Cone (f : K ⟶ L) where
  /-- The differential graded module underlying the cone. -/
  module : DifferentialGradedModule.{u, v, w} A
  /-- Coordinates in the direct sum `L ⊕ K`. -/
  coordinates : module.M ≃ₗ[R] L.M × K.M
  /-- The degree-`n` component is `Lⁿ ⊕ Kⁿ⁺¹`. -/
  grading_iff : ∀ (n : ℤ) (x : module.M),
    x ∈ module.grading n ↔
      (coordinates x).1 ∈ L.grading n ∧ (coordinates x).2 ∈ K.grading (n + 1)
  /-- The matrix differential `(d_L, f; 0, -d_K)`. -/
  differential : ∀ x : module.M,
    coordinates (module.d x) =
      (L.d (coordinates x).1 + f.toFun (coordinates x).2,
        -K.d (coordinates x).2)
  /-- The canonical inclusion of `L`. -/
  inclusion : L ⟶ module
  /-- The inclusion is the first direct-sum injection. -/
  inclusion_coordinates : ∀ x : L.M,
    coordinates (inclusion.toFun x) = (x, 0)
  /-- The canonical projection to the shifted module. -/
  projection : module ⟶ shift K 1
  /-- The projection is the second direct-sum projection. -/
  projection_apply : ∀ x : module.M,
    projection.toFun x = (coordinates x).2

/-- The prescribed grading on the underlying module `L × K` of a cone: degree `n` is
`Lⁿ × Kⁿ⁺¹`. -/
def coneGrading (K L : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    Submodule R (L.M × K.M) :=
  (L.grading n).prod (K.grading (n + 1))

/-- Membership in the cone grading is membership in each coordinate. -/
theorem coneGrading_mem (n : ℤ) (x : L.M × K.M) :
    x ∈ coneGrading K L n ↔ x.1 ∈ L.grading n ∧ x.2 ∈ K.grading (n + 1) :=
  Submodule.mem_prod

/-- The cone grading is a direct-sum decomposition of `L × K`, since it is the product
of the decompositions of `L` and of `K[1]`. -/
@[instance_reducible] noncomputable def coneGradingDecomposition
    (K L : DifferentialGradedModule.{u, v, w} A) :
    DirectSum.Decomposition (coneGrading K L) := by
  classical
  let S := shift K 1
  have hind : iSupIndep (coneGrading K L) := by
    have hL := (DirectSum.Decomposition.isInternal L.grading).submodule_iSupIndep
    have hS := (DirectSum.Decomposition.isInternal S.grading).submodule_iSupIndep
    refine iSupIndep_def.mpr fun n => Submodule.disjoint_def.mpr fun x hx hy => ?_
    have hproj (M : Type w) [AddCommGroup M] [Module R M]
        (p : L.M × K.M →ₗ[R] M) (G : ℤ → Submodule R M)
        (hp : ∀ m, Submodule.map p (coneGrading K L m) ≤ G m) :
        p x ∈ ⨆ m, ⨆ (_ : m ≠ n), G m := by
      have hh : p x ∈ Submodule.map p
          (⨆ m, ⨆ (_ : m ≠ n), coneGrading K L m) := ⟨x, hy, rfl⟩
      have hle : Submodule.map p (⨆ m, ⨆ (_ : m ≠ n), coneGrading K L m) ≤
          ⨆ m, ⨆ (_ : m ≠ n), G m := by
        rw [Submodule.map_iSup]
        refine iSup_le fun m => ?_
        rw [Submodule.map_iSup]
        exact iSup_le fun hm => le_trans (hp m)
          (le_iSup₂ (f := fun m _ => G m) m hm)
      exact hle hh
    exact Prod.ext
      ((Submodule.disjoint_def.mp (iSupIndep_def.mp hL n)) x.1
        (coneGrading_mem n x |>.mp hx).1
        (hproj L.M (LinearMap.fst R L.M K.M) L.grading (fun m => by
          rintro _ ⟨y, hy, rfl⟩
          exact (coneGrading_mem m y).mp hy |>.1)))
      ((Submodule.disjoint_def.mp (iSupIndep_def.mp hS n)) x.2
        (coneGrading_mem n x |>.mp hx).2
        (hproj K.M (LinearMap.snd R L.M K.M) S.grading (fun m => by
          rintro _ ⟨y, hy, rfl⟩
          exact (coneGrading_mem m y).mp hy |>.2)))
  have htop : (⨆ n, coneGrading K L n) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hpair : x ∈ (⨆ n, L.grading n).prod (⨆ n, S.grading n) := by
      simp [(DirectSum.Decomposition.isInternal L.grading).submodule_iSup_eq_top,
        (DirectSum.Decomposition.isInternal S.grading).submodule_iSup_eq_top]
    rw [LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup] at hpair
    have hle :
        (⨆ n, Submodule.map (LinearMap.inl R L.M K.M) (L.grading n)) ⊔
          (⨆ n, Submodule.map (LinearMap.inr R L.M K.M) (S.grading n)) ≤
            ⨆ n, coneGrading K L n := by
      refine sup_le (iSup_le fun n => ?_) (iSup_le fun n => ?_) <;> rintro _ ⟨y, hy, rfl⟩
      · exact le_iSup (coneGrading K L) n
          ((coneGrading_mem n (y, 0)).mpr ⟨hy, (K.grading (n + 1)).zero_mem⟩)
      · exact le_iSup (coneGrading K L) n
          ((coneGrading_mem n (0, y)).mpr ⟨(L.grading n).zero_mem, hy⟩)
    exact hle hpair
  exact (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop).chooseDecomposition _

/-- The matrix differential `(l, k) ↦ (d l + f k, -d k)` on the underlying module of a
cone. -/
def coneD (f : K ⟶ L) : L.M × K.M →ₗ[R] L.M × K.M where
  toFun x := (L.d x.1 + f.toFun x.2, -K.d x.2)
  map_add' x y := by ext <;> simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' r x := by ext <;> simp [map_smul, smul_add]

/-- The cone differential in coordinates. -/
theorem coneD_apply (f : K ⟶ L) (x : L.M × K.M) :
    coneD f x = (L.d x.1 + f.toFun x.2, -K.d x.2) := rfl

/-- The differential graded module underlying the cone of `f`, with underlying module
`L × K`, the cone grading, and the matrix differential. -/
@[implicit_reducible] noncomputable def coneObject (f : K ⟶ L) :
    DifferentialGradedModule.{u, v, w} A where
  M := L.M × K.M
  grading := coneGrading K L
  decomposition := coneGradingDecomposition K L
  smul_mem := by
    intro n m x a hx ha
    rw [coneGrading_mem] at hx ⊢
    refine ⟨L.smul_mem n m x.1 a hx.1 ha, ?_⟩
    change (MulOpposite.op a • x.2) ∈ K.grading (n + m + 1)
    simpa only [add_assoc, add_comm, add_left_comm] using
      K.smul_mem (n + 1) m x.2 a hx.2 ha
  d := coneD f
  d_comp_d := by
    refine LinearMap.ext fun x => ?_
    have hL := LinearMap.congr_fun L.d_comp_d x.1
    have hK := LinearMap.congr_fun K.d_comp_d x.2
    have hf := LinearMap.congr_fun f.map_d x.2
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hL hK hf
    simp [coneD_apply, map_add, hL, hK, hf]
  d_mem := by
    intro n x hx
    rw [coneGrading_mem] at hx ⊢
    rw [coneD_apply]
    exact ⟨(L.grading (n + 1)).add_mem (L.d_mem n x.1 hx.1)
      (f.map_grading (n + 1) x.2 hx.2),
      (K.grading (n + 1 + 1)).neg_mem (K.d_mem (n + 1) x.2 hx.2)⟩
  leibniz := by
    intro n m x a hx ha
    have hx' := (coneGrading_mem n x).mp hx
    have hL := L.leibniz n m x.1 a hx'.1 ha
    have hK := (shift K 1).leibniz n m x.2 a hx'.2 ha
    have hf := f.map_smul x.2 a
    apply Prod.ext
    · change L.d (MulOpposite.op a • x.1) + f.toFun (MulOpposite.op a • x.2) =
        MulOpposite.op a • (L.d x.1 + f.toFun x.2) +
          (n.negOnePow : ℤ) • (MulOpposite.op (A.d a) • x.1)
      rw [hL, hf, smul_add]
      abel
    · simpa [coneD_apply] using hK

/-- The canonical inclusion `L ⟶ coneObject f`, the first direct-sum injection. -/
def coneIncl (f : K ⟶ L) : L ⟶ coneObject f where
  toFun := (LinearMap.id : L.M →ₗ[R] L.M).prod (0 : L.M →ₗ[R] K.M)
  map_smul := by
    intro x a
    change (MulOpposite.op a • x, (0 : K.M)) =
      (MulOpposite.op a • x, MulOpposite.op a • (0 : K.M))
    simp
  map_grading n x hx := (coneGrading_mem n (x, 0)).mpr ⟨hx, (K.grading (n + 1)).zero_mem⟩
  map_d := by
    refine LinearMap.ext fun x => ?_
    change (L.d x, (0 : K.M)) = (L.d x + f.toFun 0, -K.d 0)
    simp

/-- The canonical projection `coneObject f ⟶ K[1]`, the second direct-sum projection. -/
def coneProj (f : K ⟶ L) : coneObject f ⟶ shift K 1 where
  toFun := LinearMap.snd R L.M K.M
  map_smul _ _ := rfl
  map_grading n x hx := ((coneGrading_mem n x).mp hx).2
  map_d := by
    refine LinearMap.ext fun x => ?_
    change (coneD f x).2 = ((shift K 1).d x.2)
    simp [coneD_apply, shift_d, Int.negOnePow_one, Units.smul_def]

/-- The mapping cone, with its direct-sum coordinates and canonical maps. -/
@[stacks 09KA]
noncomputable def cone (f : K ⟶ L) : Cone f where
  module := coneObject f
  coordinates := LinearEquiv.refl R (L.M × K.M)
  grading_iff := coneGrading_mem
  differential := coneD_apply f
  inclusion := coneIncl f
  inclusion_coordinates _ := rfl
  projection := coneProj f
  projection_apply _ := rfl

/-- The differential graded module of a mapping cone. -/
noncomputable abbrev coneModule (f : K ⟶ L) : DifferentialGradedModule.{u, v, w} A :=
  (cone f).module

/-- The canonical inclusion into a mapping cone. -/
noncomputable abbrev coneInclusion (f : K ⟶ L) : L ⟶ coneModule f :=
  (cone f).inclusion

/-- The canonical projection from a mapping cone. -/
noncomputable abbrev coneProjection (f : K ⟶ L) : coneModule f ⟶ shift K 1 :=
  (cone f).projection

end DifferentialGradedModule

end
