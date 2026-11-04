module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleCriterion
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedSubmodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.OrthogonalAcyclic

/-!
# Differential graded modules with a triangular cell decomposition

Let `(A, d)` be a differential graded algebra and let `M` be a right differential graded
`A`-module whose underlying *graded* right `A`-module is a direct sum `⨁_{m ∈ ℕ} L_m` of
differential graded `A`-modules `L_m`, in such a way that the differential of `M` is *lower
triangular* for that decomposition: the `m`-th coordinate of `d x` involves only the
coordinates of `x` in degrees `≤ m`, and on the top coordinate of an element of a stage it
is the differential of `L_m`. If each `L_m` is orthogonal on the left to the acyclic modules
and only finitely many of them are nonzero, then so is `M`.

This is the mechanism by which a module built out of cells becomes orthogonal on the left to
the acyclic modules without producing a property-(P) filtration: the stages
`F_k = {x : the coordinates of x in degrees ≥ k vanish}` are differential graded submodules, the
inclusions `F_k ⊆ F_{k+1}` are admissible monomorphisms with the coordinate truncation as a
graded retraction, and the `k`-th coordinate is a surjection `F_{k+1} ⟶ L_k` with kernel `F_k`.
`DifferentialGradedModule.leftOrthogonal_acyclic_stage_of_admissibleFiltration` then gives
orthogonality of every stage, and the filtration is exhausted by one of them.

The intended instance is a Koszul-type module: for a differential graded algebra `A` over `R`
with a map `R → A` the tensor product `A ⊗_R K` with a Koszul algebra `K` on `r` elements is
filtered by exterior degree, with graded pieces direct sums of shifts of `A` indexed by the
wedge monomials of a fixed exterior degree, and with the differential lowering exterior degree
by one. The data below is exactly what that filtration provides, and
`DifferentialGradedModule.leftOrthogonal_acyclic_directSumShifts` supplies the orthogonality of
the graded pieces.

## Main definitions

* `DifferentialGradedModule.GradedCellData`: the data of such a cell decomposition — the pieces
  `L_m`, their orthogonality, the coordinate isomorphism, its compatibility with the action and
  the grading, the bound beyond which the coordinates vanish, and the two triangularity
  properties of the differential.
* `DifferentialGradedModule.GradedCellData.stage`: the differential graded submodule `F_k`.
* `DifferentialGradedModule.GradedCellData.layerHom`: the `k`-th coordinate, as a homomorphism
  `F_{k+1} ⟶ L_k`.

## Main results

* `DifferentialGradedModule.GradedCellData.isAdmissibleShortExact_stageIncl_layerHom`: each step
  of the filtration is an admissible short exact sequence `F_k ⟶ F_{k+1} ⟶ L_k`.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_gradedCellData`: a module with such a cell
  decomposition is orthogonal on the left to the acyclic modules.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_cellCoords`: the same conclusion from
  coordinates valued in direct sums of shifts of the algebra, which is the form in which a
  module with a graded basis presents them — the hypotheses then mention only the grading and
  the differential of the algebra itself.

## Implementation notes

*Why the graded pieces are arbitrary differential graded modules.* The pieces of the intended
instance are direct sums of shifts of `A`, which is what Tag 09KK asks of a property-(P)
filtration. Nothing below uses that: only their orthogonality is used, and stating the data with
abstract pieces keeps the index types and the `DecidableEq` instances of the direct sums out of
the construction, where they would else have to be carried through every stage.

*Why the coordinate isomorphism is `R`-linear with a separate compatibility.* The coordinate
isomorphism is a map of right `A`-modules, but stating it as such would make every map built
from it an `A`-linear map that has to be restricted to `R` before it can be used as the
underlying map of a homomorphism of differential graded modules. It is therefore recorded as an
`R`-linear equivalence together with the compatibility `coords_smul` with the right action,
which is the only consequence of `A`-linearity that is used.

*The coordinates of a Koszul tensor product.* For a differential graded algebra `A` over `R`
and the Koszul algebra `K` on `f₁, …, f_r`, the cells of `A ⊗_R K` over `A` are the wedge
monomials `1 ⊗ ξ_s` for `s ⊆ {1, …, r}`, of exterior degree `m = |s|` and of degree `-m`; so
`bound = r + 1` and the shift of every cell of exterior degree `m` is `m`. The `s`-th coordinate
of `a ⊗ ξ_s` is then not `a` but `(-1)^{m · deg a} a`: the right `A`-action on the tensor product
carries the Koszul sign `(-1)^{(deg a - m) · deg b}` while the action on a shift of the regular
module carries `(-1)^{deg a · deg b}`, and the two differ by `(-1)^{m · deg b}`, which the twist
by the parity of the exterior degree absorbs. With that twist `d_coords` holds with the sign
`(-1)^m` carried by the shift, since `d (a ⊗ ξ_s) = d a ⊗ ξ_s ± a ⊗ d ξ_s` and the second term has
lower exterior degree, so it does not contribute to the coordinates of exterior degree `m`.

*The filtration is indexed so that the bottom stage is a graded piece.* `F_0` is the zero
module, so the filtration fed to
`DifferentialGradedModule.leftOrthogonal_acyclic_stage_of_admissibleFiltration` starts at `F_1`,
which the coordinate map identifies with `L_0`. This avoids having to know that the zero module
is orthogonal to the acyclic modules.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P), the
  filtration whose shape this reproduces.
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality of the
  modules with property (P) to the acyclic ones.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **An unbounded triangular cell decomposition of a differential graded module.** The
underlying graded right `A`-module of `M` is the direct sum of the differential graded modules
`layer m`, each orthogonal on the left to the acyclic modules, and the differential of `M` is
lower triangular: it preserves the vanishing of the coordinates in degrees `≥ k`, and on the
`k`-th coordinate of an element whose coordinates in degrees `> k` vanish it is the differential
of `layer k`.

This is `DifferentialGradedModule.GradedCellData` without its `bound`: the coordinates of an
individual element still vanish from some index on, since they form an element of a direct sum,
but no single index need work for every element. -/
structure ExhaustiveCellData (M : DifferentialGradedModule.{u, u, u} A) where
  /-- The graded pieces. -/
  layer : ℕ → DifferentialGradedModule.{u, u, u} A
  /-- Each graded piece is orthogonal on the left to the acyclic modules. -/
  layer_leftOrthogonal : ∀ m : ℕ,
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (layer m))
  /-- The coordinates of an element of `M` with respect to the decomposition. -/
  coords : M.M ≃ₗ[R] (⨁ (m : ℕ), (layer m).M)
  /-- The coordinates are compatible with the right `A`-action. -/
  coords_smul : ∀ (a : A.A) (x : M.M) (m : ℕ),
    (coords (MulOpposite.op a • x)) m = MulOpposite.op a • (coords x) m
  /-- The coordinates are compatible with the gradings: an element is homogeneous of degree `n`
  exactly when all of its coordinates are. -/
  mem_grading_iff : ∀ (n : ℤ) (x : M.M),
    x ∈ M.grading n ↔ ∀ m : ℕ, (coords x) m ∈ (layer m).grading n
  /-- The differential preserves the vanishing of the coordinates in degrees `≥ k`: this is the
  lower triangularity of the differential. -/
  d_coords_eq_zero : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k ≤ m → (coords x) m = 0) →
    ∀ m : ℕ, k ≤ m → (coords (M.d x)) m = 0
  /-- On the top coordinate of an element whose higher coordinates vanish the differential of
  `M` is the differential of the graded piece. -/
  d_coords : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k + 1 ≤ m → (coords x) m = 0) →
    (coords (M.d x)) k = (layer k).d ((coords x) k)

namespace ExhaustiveCellData

variable {M : DifferentialGradedModule.{u, u, u} A} (D : ExhaustiveCellData M)

/-! ### The coordinate maps -/

/-- The `m`-th coordinate of an element of `M`, as an `R`-linear map. -/
def coord (m : ℕ) : M.M →ₗ[R] (D.layer m).M :=
  (DirectSum.component R ℕ (fun m => (D.layer m).M) m).comp (D.coords : M.M →ₗ[R] _)

/-- The `m`-th coordinate of `x` is the `m`-th component of `D.coords x`. -/
@[simp] theorem coord_apply (m : ℕ) (x : M.M) : D.coord m x = (D.coords x) m := rfl

/-- The coordinates are compatible with the right `A`-action. -/
theorem coord_smul (m : ℕ) (x : M.M) (a : A.A) :
    D.coord m (MulOpposite.op a • x) = MulOpposite.op a • D.coord m x :=
  D.coords_smul a x m

/-- Taking a coordinate commutes with taking a graded component. -/
theorem coord_decompose (m : ℕ) (n : ℤ) (x : M.M) :
    D.coord m ((DirectSum.decompose M.grading x n : M.M)) =
      ((DirectSum.decompose (D.layer m).grading (D.coord m x) n : (D.layer m).M)) :=
  (DirectSum.coe_decompose_apply_map (R := R) M.grading (D.layer m).grading (D.coord m)
    (fun p y hy => ((D.mem_grading_iff p y).1 hy) m) x n).symm

/-! ### The stages of the filtration -/

/-- The underlying submodule of the `k`-th stage: the elements whose coordinates in degrees at
least `k` vanish. -/
def carrier (k : ℕ) : Submodule (MulOpposite A.A) M.M where
  carrier := {x : M.M | ∀ m : ℕ, k ≤ m → D.coord m x = 0}
  add_mem' := by
    intro x y hx hy m hm
    rw [map_add, hx m hm, hy m hm, add_zero]
  zero_mem' := by
    intro m _
    rw [map_zero]
  smul_mem' := by
    intro c x hx m hm
    rw [show c = MulOpposite.op c.unop from rfl, D.coord_smul, hx m hm, smul_zero]

/-- An element lies in `D.carrier k` exactly when its coordinates in degrees at least `k`
vanish. -/
theorem mem_carrier {k : ℕ} {x : M.M} :
    x ∈ D.carrier k ↔ ∀ m : ℕ, k ≤ m → D.coord m x = 0 := Iff.rfl

/-- The underlying submodules of the stages increase with `k`. -/
theorem carrier_le_succ (k : ℕ) : D.carrier k ≤ D.carrier (k + 1) :=
  fun _ hx m hm => hx m (by omega)


/-- **The `k`-th stage of the filtration**, as a differential graded submodule of `M`. -/
def stage (k : ℕ) : GradedSub M where
  carrier := D.carrier k
  decompose_mem := by
    intro n x hx m hm
    have h : D.coord m ((DirectSum.decompose M.grading x n : M.M)) = 0 := by
      rw [D.coord_decompose m n x, hx m hm, DirectSum.decompose_zero]
      rfl
    exact h
  d_mem := fun x hx => D.d_coords_eq_zero k x hx

/-- The underlying submodule of the `k`-th stage is `D.carrier k`. -/
@[simp] theorem stage_carrier (k : ℕ) : (D.stage k).carrier = D.carrier k := rfl

/-- The ambient value of an element of the `k`-th stage. -/
def val (k : ℕ) : (D.stage k).obj.M →ₗ[R] M.M := ((D.stage k).ι).toFun

/-- The ambient value of an element of the `k`-th stage lies in `D.carrier k`. -/
theorem val_mem (k : ℕ) (x : (D.stage k).obj.M) : D.val k x ∈ D.carrier k :=
  GradedSub.ι_mem (D.stage k) x

/-- An element of the `k`-th stage is determined by its ambient value. -/
theorem val_injective (k : ℕ) : Function.Injective (D.val k) :=
  GradedSub.ι_injective (D.stage k)

/-- Taking the ambient value is compatible with the right `A`-action. -/
theorem val_smul (k : ℕ) (x : (D.stage k).obj.M) (a : A.A) :
    D.val k (MulOpposite.op a • x) = MulOpposite.op a • D.val k x :=
  ((D.stage k).ι).map_smul x a

/-- Taking the ambient value commutes with the differentials. -/
theorem val_d (k : ℕ) (x : (D.stage k).obj.M) :
    D.val k ((D.stage k).obj.d x) = M.d (D.val k x) := by
  have h := LinearMap.congr_fun ((D.stage k).ι).map_d x
  simpa [val] using h

/-- An element of the `k`-th stage is homogeneous of degree `n` exactly when its ambient value
is. -/
theorem mem_grading_val (k : ℕ) (n : ℤ) (x : (D.stage k).obj.M) :
    x ∈ (D.stage k).obj.grading n ↔ D.val k x ∈ M.grading n :=
  GradedSub.mem_obj_grading (D.stage k)

/-- An element of `M` lying in the `k`-th stage, as an element of that stage. -/
def ofMem (k : ℕ) (x : M.M) (hx : x ∈ D.carrier k) : (D.stage k).obj.M :=
  (⟨x, hx⟩ : ↥(D.carrier k))

/-- The ambient value of `D.ofMem k x hx` is `x`. -/
@[simp] theorem val_ofMem (k : ℕ) (x : M.M) (hx : x ∈ D.carrier k) :
    D.val k (D.ofMem k x hx) = x := rfl

/-- The inclusion of one stage into the next. -/
def stageIncl (k : ℕ) : (D.stage k).obj ⟶ (D.stage (k + 1)).obj :=
  GradedSub.incl (D.carrier_le_succ k)

/-- The inclusion of one stage into the next preserves ambient values. -/
@[simp] theorem val_stageIncl (k : ℕ) (x : (D.stage k).obj.M) :
    D.val (k + 1) ((D.stageIncl k).toFun x) = D.val k x := rfl

/-! ### The truncation of the coordinates -/

/-- Truncation of the coordinates below `k`, on the direct sum. -/
def truncMap (k : ℕ) :
    (⨁ (m : ℕ), (D.layer m).M) →ₗ[R] (⨁ (m : ℕ), (D.layer m).M) :=
  DirectSum.toModule R ℕ _
    fun m => if m < k then DirectSum.lof R ℕ (fun m => (D.layer m).M) m else 0

/-- The `m`-th component of the truncation below `k` is the `m`-th component if `m < k` and
zero otherwise. -/
theorem truncMap_apply (k m : ℕ) (y : ⨁ (m : ℕ), (D.layer m).M) :
    (D.truncMap k y) m = if m < k then y m else 0 := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of j b =>
      rw [← DirectSum.lof_eq_of R, truncMap, DirectSum.toModule_lof]
      by_cases hj : j < k
      · by_cases hm : m = j
        · subst hm
          simp [hj]
        · simp [hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hm]
      · by_cases hm : m = j
        · subst hm
          simp [hj]
        · simp [hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hm]
  | add y z hy hz =>
      rw [map_add, DirectSum.add_apply, hy, hz, DirectSum.add_apply]
      by_cases hm : m < k <;> simp [hm]

/-- Truncation of the coordinates below `k`, as an endomorphism of `M`. -/
def trunc (k : ℕ) : M.M →ₗ[R] M.M :=
  (D.coords.symm : (⨁ (m : ℕ), (D.layer m).M) →ₗ[R] M.M).comp
    ((D.truncMap k).comp (D.coords : M.M →ₗ[R] _))

/-- The `m`-th coordinate of the truncation below `k` is the `m`-th coordinate if `m < k` and
zero otherwise. -/
theorem coord_trunc (k m : ℕ) (x : M.M) :
    D.coord m (D.trunc k x) = if m < k then D.coord m x else 0 := by
  have h : D.coords (D.trunc k x) = D.truncMap k (D.coords x) := by
    simp only [trunc, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  rw [D.coord_apply, h, D.truncMap_apply k m (D.coords x), D.coord_apply]

/-- Two elements of `M` with the same coordinates are equal. -/
private theorem ext_coord {x y : M.M} (h : ∀ m : ℕ, D.coord m x = D.coord m y) : x = y :=
  D.coords.injective (DirectSum.ext h)

/-- Truncation of the coordinates is compatible with the right `A`-action. -/
theorem trunc_smul (k : ℕ) (x : M.M) (a : A.A) :
    D.trunc k (MulOpposite.op a • x) = MulOpposite.op a • D.trunc k x := by
  refine D.ext_coord fun m => ?_
  rw [D.coord_trunc, D.coord_smul, D.coord_smul, D.coord_trunc]
  by_cases hm : m < k <;> simp [hm]

/-- Truncation of the coordinates preserves homogeneity of degree `n`. -/
theorem trunc_mem_grading (k : ℕ) (n : ℤ) (x : M.M) (hx : x ∈ M.grading n) :
    D.trunc k x ∈ M.grading n := by
  refine (D.mem_grading_iff n _).2 fun m => ?_
  have h := D.coord_trunc k m x
  rw [D.coord_apply, D.coord_apply] at h
  rw [h]
  by_cases hm : m < k
  · simpa [hm] using ((D.mem_grading_iff n x).1 hx) m
  · simp [hm]

/-- Truncation below `k` maps the `(k+1)`-st stage into the `k`-th. -/
theorem trunc_mem_carrier (k : ℕ) (x : M.M) (_hx : x ∈ D.carrier (k + 1)) :
    D.trunc k x ∈ D.carrier k := by
  intro m hm
  rw [D.coord_trunc]
  simp [show ¬ m < k by omega]

/-- Truncation below `k` fixes every element of the `k`-th stage. -/
theorem trunc_eq_self (k : ℕ) (x : M.M) (hx : x ∈ D.carrier k) : D.trunc k x = x := by
  refine D.ext_coord fun m => ?_
  rw [D.coord_trunc]
  by_cases hm : m < k
  · simp [hm]
  · rw [(hx m (by omega)).symm]
    simp [hm]

/-- **The inclusion of one stage into the next is an admissible monomorphism**, with the
truncation of the coordinates as a graded retraction. -/
theorem isAdmissibleMono_stageIncl (k : ℕ) : IsAdmissibleMono (D.stageIncl k) :=
  GradedSub.isAdmissibleMono_incl (D.carrier_le_succ k) (D.trunc k)
    (fun x a => D.trunc_smul k x a) (fun n x hx => D.trunc_mem_grading k n x hx)
    (fun x hx => D.trunc_mem_carrier k x hx) fun x hx => D.trunc_eq_self k x hx

/-! ### The graded pieces -/

/-- **The `k`-th coordinate, as a homomorphism of differential graded modules** from the
`(k+1)`-st stage of the filtration to the `k`-th graded piece. -/
def layerHom (k : ℕ) : (D.stage (k + 1)).obj ⟶ D.layer k where
  toFun := (D.coord k).comp (D.val (k + 1))
  map_smul x a := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, D.val_smul, D.coord_smul]
  map_grading n x hx :=
    ((D.mem_grading_iff n (D.val (k + 1) x)).1 ((D.mem_grading_val (k + 1) n x).1 hx)) k
  map_d := by
    refine LinearMap.ext fun x => ?_
    have h : D.coord k (M.d (D.val (k + 1) x)) = (D.layer k).d (D.coord k (D.val (k + 1) x)) :=
      D.d_coords k (D.val (k + 1) x) fun m hm => D.val_mem (k + 1) x m hm
    simpa [D.val_d (k + 1) x] using h

/-- `D.layerHom k` sends an element to the `k`-th coordinate of its ambient value. -/
@[simp] theorem layerHom_apply (k : ℕ) (x : (D.stage (k + 1)).obj.M) :
    (D.layerHom k).toFun x = D.coord k (D.val (k + 1) x) := rfl

/-- The `k`-th coordinate map `F_{k+1} ⟶ L_k` is surjective. -/
theorem layerHom_surjective (k : ℕ) : Function.Surjective (D.layerHom k).toFun := by
  classical
  intro y
  set z := D.coords.symm (DirectSum.lof R ℕ (fun m => (D.layer m).M) k y) with hzdef
  have hco : ∀ m : ℕ, D.coord m z = (DirectSum.lof R ℕ (fun m => (D.layer m).M) k y) m := by
    intro m
    rw [D.coord_apply, hzdef, LinearEquiv.apply_symm_apply]
  have hmem : z ∈ D.carrier (k + 1) := by
    intro m hm
    rw [hco m, DirectSum.lof_eq_of]
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  refine ⟨D.ofMem (k + 1) z hmem, ?_⟩
  rw [D.layerHom_apply, D.val_ofMem, hco k, DirectSum.lof_eq_of, DirectSum.of_eq_same]

/-- The kernel of the `k`-th coordinate map `F_{k+1} ⟶ L_k` is the image of `F_k`. -/
theorem layerHom_ker (k : ℕ) :
    LinearMap.ker (D.layerHom k).toFun = LinearMap.range (D.stageIncl k).toFun := by
  apply le_antisymm
  · intro x hx
    have hx' : D.coord k (D.val (k + 1) x) = 0 := by
      have := LinearMap.mem_ker.1 hx
      rwa [D.layerHom_apply] at this
    have hmem : D.val (k + 1) x ∈ D.carrier k := by
      intro m hm
      rcases eq_or_lt_of_le hm with h | h
      · subst h
        exact hx'
      · exact D.val_mem (k + 1) x m (by omega)
    refine ⟨D.ofMem k (D.val (k + 1) x) hmem, D.val_injective (k + 1) ?_⟩
    rw [D.val_stageIncl, D.val_ofMem]
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, D.layerHom_apply, D.val_stageIncl]
    exact D.val_mem k y k (by omega)

/-- **Each step of the filtration is an admissible short exact sequence**
`F_k ⟶ F_{k+1} ⟶ L_k`. -/
theorem isAdmissibleShortExact_stageIncl_layerHom (k : ℕ) :
    IsAdmissibleShortExact (D.stageIncl k) (D.layerHom k) :=
  isAdmissibleShortExact_of_ker_eq_range (D.stageIncl k) (D.layerHom k)
    (D.isAdmissibleMono_stageIncl k) (D.layerHom_surjective k) (D.layerHom_ker k)

/-- The coordinates of an element determine it. -/
theorem eq_zero_of_coords_eq_zero {x : M.M} (hx : ∀ m : ℕ, (D.coords x) m = 0) : x = 0 := by
  exact D.ext_coord fun m => by rw [map_zero, coord_apply, hx m]

/-- The bottom stage of the filtration is the zeroth graded piece: the coordinate map
`F_1 ⟶ L_0` is an isomorphism, `F_0` being zero. -/
def stageOneIso : (D.stage 1).obj ≅ D.layer 0 :=
  Hom.isoOfBijective (D.layerHom 0) ⟨by
    intro x y hxy
    have hker : (x - y) ∈ LinearMap.ker (D.layerHom 0).toFun := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [D.layerHom_ker 0] at hker
    obtain ⟨z, hz⟩ := hker
    have hval : D.val 1 (x - y) = D.val 0 z := by
      rw [← hz, D.val_stageIncl]
    have hzero : D.val 0 z = 0 :=
      D.eq_zero_of_coords_eq_zero fun m => D.val_mem 0 z m (Nat.zero_le m)
    have hsub : D.val 1 x - D.val 1 y = 0 := by
      rw [← map_sub, hval, hzero]
    exact D.val_injective 1 (sub_eq_zero.1 hsub), D.layerHom_surjective 0⟩

end ExhaustiveCellData

/-- **A bounded triangular cell decomposition of a differential graded module.** An unbounded
cell decomposition in which one index bounds the vanishing of the coordinates of every element
at once: beyond `bound` every coordinate of every element of `M` is zero. -/
structure GradedCellData (M : DifferentialGradedModule.{u, u, u} A) extends
    ExhaustiveCellData M where
  /-- The index beyond which all coordinates vanish. -/
  bound : ℕ
  /-- All coordinates in degrees at least `bound` vanish. -/
  coords_eq_zero_of_bound_le : ∀ (x : M.M) (m : ℕ), bound ≤ m → (coords x) m = 0

namespace GradedCellData

variable {M : DifferentialGradedModule.{u, u, u} A} (D : GradedCellData M)

/-- Beyond `bound` the filtration is everything. -/
theorem carrier_eq_top : D.carrier (D.bound + 1) = ⊤ :=
  eq_top_iff.2 fun x _ m hm => D.coords_eq_zero_of_bound_le x m (by omega)

/-- The top stage of the filtration is all of `M`. -/
theorem val_bijective : Function.Bijective (D.val (D.bound + 1)) :=
  ⟨D.val_injective _, fun y =>
    ⟨D.ofMem (D.bound + 1) y (by rw [D.carrier_eq_top]; exact Submodule.mem_top), rfl⟩⟩

/-- The top stage of the filtration, as an isomorphism onto `M`. -/
def topStageIso : (D.stage (D.bound + 1)).obj ≅ M :=
  Hom.isoOfBijective ((D.stage (D.bound + 1)).ι) D.val_bijective

end GradedCellData

/-- **A differential graded module with a triangular cell decomposition is orthogonal on the
left to the acyclic modules.** The stages of the filtration cut out by the vanishing of the
coordinates in high degrees are differential graded submodules, their inclusions are admissible
monomorphisms with the coordinate truncations as graded retractions, and the successive
quotients are the graded pieces; orthogonality propagates up the filtration, which is exhausted
by one of its stages. -/
theorem leftOrthogonal_acyclic_of_gradedCellData {M : DifferentialGradedModule.{u, u, u} A}
    (D : GradedCellData M) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  have key : ∀ k : ℕ,
      (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (D.stage (k + 1)).obj) :=
    leftOrthogonal_acyclic_stage_of_admissibleFiltration A
      (fun k => (D.stage (k + 1)).obj) (fun k => D.layer (k + 1))
      (fun k => D.stageIncl (k + 1)) (fun k => D.layerHom (k + 1))
      (fun k => D.isAdmissibleShortExact_stageIncl_layerHom (k + 1))
      (leftOrthogonal_acyclic_of_iso A D.stageOneIso.symm (D.layer_leftOrthogonal 0))
      fun k => D.layer_leftOrthogonal (k + 1)
  exact leftOrthogonal_acyclic_of_iso A D.topStageIso (key D.bound)

/-! ### Cells given by direct sums of shifts of the algebra -/

/-- The differential of a direct sum of shifts of the algebra is computed componentwise: on the
`j`-th component it is the differential of the algebra with the sign of that summand's shift. -/
theorem directSumShifts_d_apply {ι : Type u} [DecidableEq ι] (k : ι → ℤ)
    (x : ⨁ (_ : ι), A.A) (j : ι) :
    DirectSum.component R ι (fun _ => A.A) j ((directSumShifts A k).d x)
      = ((-1 : ℤ) ^ (k j).natAbs) • A.d (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero =>
      refine ((congrArg (DirectSum.component R ι (fun _ => A.A) j)
        (map_zero ((directSumShifts A k).d))).trans (map_zero _)).trans ?_
      rw [DirectSum.zero_apply, map_zero, smul_zero]
  | of i b =>
      rw [← DirectSum.lof_eq_of R]
      refine (congrArg (DirectSum.component R ι (fun _ => A.A) j)
        (directSumShifts_d_lof k i b)).trans ?_
      rw [← DirectSum.apply_eq_component, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
      by_cases hj : j = i
      · subst hj
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
      · rw [DirectSum.of_eq_of_ne _ _ _ hj, DirectSum.of_eq_of_ne _ _ _ hj, map_zero, smul_zero]
  | add x y hx hy =>
      refine (congrArg (DirectSum.component R ι (fun _ => A.A) j)
        (map_add ((directSumShifts A k).d) x y)).trans ?_
      refine ((map_add (DirectSum.component R ι (fun _ => A.A) j)
        ((directSumShifts A k).d x) ((directSumShifts A k).d y)).trans
        (congr_arg₂ (· + ·) hx hy)).trans ?_
      rw [DirectSum.add_apply, map_add, smul_add]

/-- **A triangular cell decomposition with coordinates in direct sums of shifts of the
algebra.** This is the form in which a differential graded module with a graded basis, filtered
so that the differential is lower triangular, presents its cell decomposition: the `m`-th
coordinate is a direct sum of copies of the algebra, one for each cell of exterior degree `m`,
shifted by `sh m i`. The hypotheses mention only the grading and the differential of the algebra
itself. -/
def gradedCellDataOfCellCoords {M : DifferentialGradedModule.{u, u, u} A} {I : ℕ → Type u}
    [∀ m, DecidableEq (I m)] (sh : ∀ m, I m → ℤ) (bound : ℕ)
    (coords : M.M ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : I m), A.A))
    (coords_smul : ∀ (a : A.A) (x : M.M) (m : ℕ),
      (coords (MulOpposite.op a • x)) m = MulOpposite.op a • (coords x) m)
    (mem_grading_iff : ∀ (n : ℤ) (x : M.M),
      x ∈ M.grading n ↔ ∀ (m : ℕ) (i : I m), ((coords x) m) i ∈ A.grading (n + sh m i))
    (coords_eq_zero : ∀ (x : M.M) (m : ℕ), bound ≤ m → (coords x) m = 0)
    (d_coords_eq_zero : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k ≤ m → (coords x) m = 0) →
      ∀ m : ℕ, k ≤ m → (coords (M.d x)) m = 0)
    (d_coords : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k + 1 ≤ m → (coords x) m = 0) →
      ∀ i : I k, ((coords (M.d x)) k) i =
        ((-1 : ℤ) ^ (sh k i).natAbs) • A.d (((coords x) k) i)) :
    GradedCellData M where
  layer m := directSumShifts A (sh m)
  layer_leftOrthogonal m := leftOrthogonal_acyclic_directSumShifts A (sh m)
  coords := coords
  coords_smul := coords_smul
  mem_grading_iff n x := (mem_grading_iff n x).trans
    (forall_congr' fun m => (mem_directSumShifts_grading (sh m) n ((coords x) m)).symm)
  bound := bound
  coords_eq_zero_of_bound_le := coords_eq_zero
  d_coords_eq_zero := d_coords_eq_zero
  d_coords k x hx :=
    DirectSum.ext fun i => ((d_coords k x hx) i).trans
      (directSumShifts_d_apply (sh k) ((coords x) k) i).symm

/-- **A differential graded module with a triangular cell decomposition whose graded pieces are
direct sums of shifts of the algebra is orthogonal on the left to the acyclic modules.** This is
`DifferentialGradedModule.leftOrthogonal_acyclic_of_gradedCellData` with the graded pieces taken
in the form a graded basis provides them. -/
theorem leftOrthogonal_acyclic_of_cellCoords {M : DifferentialGradedModule.{u, u, u} A}
    {I : ℕ → Type u} (sh : ∀ m, I m → ℤ) (bound : ℕ)
    (coords : M.M ≃ₗ[R] ⨁ (m : ℕ), (⨁ (_ : I m), A.A))
    (coords_smul : ∀ (a : A.A) (x : M.M) (m : ℕ),
      (coords (MulOpposite.op a • x)) m = MulOpposite.op a • (coords x) m)
    (mem_grading_iff : ∀ (n : ℤ) (x : M.M),
      x ∈ M.grading n ↔ ∀ (m : ℕ) (i : I m), ((coords x) m) i ∈ A.grading (n + sh m i))
    (coords_eq_zero : ∀ (x : M.M) (m : ℕ), bound ≤ m → (coords x) m = 0)
    (d_coords_eq_zero : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k ≤ m → (coords x) m = 0) →
      ∀ m : ℕ, k ≤ m → (coords (M.d x)) m = 0)
    (d_coords : ∀ (k : ℕ) (x : M.M), (∀ m : ℕ, k + 1 ≤ m → (coords x) m = 0) →
      ∀ i : I k, ((coords (M.d x)) k) i =
        ((-1 : ℤ) ^ (sh k i).natAbs) • A.d (((coords x) k) i)) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  classical
  exact leftOrthogonal_acyclic_of_gradedCellData
    (gradedCellDataOfCellCoords sh bound coords coords_smul mem_grading_iff coords_eq_zero
      d_coords_eq_zero d_coords)

end DifferentialGradedModule

end
