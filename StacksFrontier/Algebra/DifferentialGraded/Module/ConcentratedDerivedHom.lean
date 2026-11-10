module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExhaustiveCellFiltration

/-!
# Homomorphisms out of a module concentrated in degree zero are not changed by localization

Let `(C, d)` be a differential graded algebra concentrated in degree zero — an ordinary ring,
read as a differential graded algebra — and let `M` and `N` be right differential graded
`C`-modules concentrated in degree zero. This file shows that the passage to the derived
category `D(C, d)` is *bijective* on the homomorphisms `M → N`.

The content is surjectivity; injectivity is the degree-zero cohomology functor. Surjectivity
needs a resolution of `M` by a differential graded module whose cells all sit in degrees `≤ 0`:
the free resolution

`⋯ ⟶ C^{(X₂)} ⟶ C^{(X₁)} ⟶ C^{(X₀)} ⟶ M ⟶ 0`

of `M` by free right `C`-modules, placed with `C^{(X_m)}` in degree `-m`. Its cells are the
elements of the iterated kernels, so its exactness is a matter of definition rather than of
proof, and its differential lowers the cell degree by exactly one, which makes it a triangular
cell decomposition in the sense of `DifferentialGradedModule.ExhaustiveCellData` and therefore
orthogonal on the left to the acyclic modules.

With such a resolution `P → M` the morphisms `M → N` of the derived category are the homotopy
classes of homomorphisms `P → N`, by Tag 09KY's mechanism; and a homomorphism `P → N` is a
homomorphism `M → N` precomposed with the resolution, because `P` has nothing in positive
degrees: its degree-zero part is a free module on the elements of `M`, its degree `-1` part maps
onto the relations, and `N` is concentrated in degree zero, so there is no room either for a
correction term or for a homotopy.

## Main definitions

* `DifferentialGradedModule.freeCover`: the free right `C`-module on the elements of a module,
  with its evaluation onto that module.
* `DifferentialGradedModule.cellTower`: the tower `M, ker, ker, …` of iterated kernels of the
  free covers, which indexes the cells of the resolution.
* `DifferentialGradedModule.freeResolution`: the resolution itself, as a differential graded
  `C`-module.
* `DifferentialGradedModule.concentratedAug`: the augmentation `P ⟶ M`.

## Main results

* `DifferentialGradedModule.concentratedAug_isQuasiIsomorphism`: the augmentation is a
  quasi-isomorphism.
* `DifferentialGradedModule.leftOrthogonal_acyclic_freeResolution`: the resolution is orthogonal
  on the left to the acyclic modules.
* `DifferentialGradedModule.exists_concentratedAug_comp_eq`: every homomorphism `P ⟶ N` is the
  augmentation followed by a homomorphism `M ⟶ N`.
* `DifferentialGradedModule.concentrated_q_map_surjective`: the passage to the derived category
  is surjective on the homomorphisms between modules concentrated in degree zero.

## Implementation notes

The cells of the resolution are indexed by `(m : ℕ) × cellTower m`, and its underlying graded
module is `DifferentialGradedModule.directSumShifts` for the shift sending a cell of level `m`
to `m`; only the differential is replaced, so the grading, its direct-sum decomposition and the
module structures are inherited and need no proof. The differential is built on the curried
form `⨁_m ⨁_{cells m} C` of that direct sum, where the level of a cell is an index of the outer
sum, since every statement about it is a statement about levels.

The tower is a family of *bundled* modules, `CategoryTheory.ModuleCat C.Aᵐᵒᵖ`, because its
stages are iterated kernels: each stage is a submodule of the free module on the previous one,
so the recursion is on objects carrying their own module structure. Only the underlying types of
the stages enter the resolution, as its cell index sets.

Everything is stated for right modules over `C.A`, encoded as left modules over `C.Aᵐᵒᵖ` as the
differential graded interface of Tag 09JI does, and the maps of the tower are `C.Aᵐᵒᵖ`-linear;
the `R`-linearity the differential graded structure asks for is the restriction of scalars along
`R → C.Aᵐᵒᵖ`.

## References

* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), orthogonality to the
  acyclic modules.
* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), morphisms of the derived
  category computed by a resolution.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

attribute [local instance] Classical.decEq

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {C : DifferentialGradedAlgebra.{u, u} R}

/-! ### Modules concentrated in degree zero -/

/-- Every element of a decomposed module whose pieces vanish outside degree zero lies in
degree zero. -/
private theorem mem_grading_zero_of_forall_ne_bot {A : Type*} [AddCommGroup A] [Module R A]
    (g : ℤ → Submodule R A) [DirectSum.Decomposition g] (hg : ∀ n : ℤ, n ≠ 0 → g n = ⊥)
    (x : A) : x ∈ g 0 := by
  induction x using DirectSum.Decomposition.inductionOn g with
  | zero => exact (g 0).zero_mem
  | @homogeneous n x =>
    by_cases hn : n = 0
    · subst n
      exact x.property
    · have hx : (x : A) = 0 := by
        have hx : (x : A) ∈ (⊥ : Submodule R A) := by
          simpa only [hg n hn] using x.property
        exact (Submodule.mem_bot R).mp hx
      simpa only [hx] using (g 0).zero_mem
  | add x y hx hy => exact (g 0).add_mem hx hy

/-- Every element of a differential graded algebra concentrated in degree zero is homogeneous of
degree zero. -/
theorem mem_grading_zero_of_concentrated (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥) (x : C.A) :
    x ∈ C.grading 0 :=
  mem_grading_zero_of_forall_ne_bot C.grading hC x

/-- The differential of a differential graded algebra concentrated in degree zero vanishes. -/
theorem d_eq_zero_of_concentrated (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥) (x : C.A) :
    C.d x = 0 := by
  have h := C.d_mem 0 x (mem_grading_zero_of_concentrated hC x)
  rwa [zero_add, hC 1 (by decide), Submodule.mem_bot] at h

/-- Every element of a differential graded module concentrated in degree zero is homogeneous of
degree zero. -/
theorem module_mem_grading_zero_of_concentrated (M : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) (x : M.M) : x ∈ M.grading 0 :=
  mem_grading_zero_of_forall_ne_bot M.grading hM x

/-- The differential of a differential graded module concentrated in degree zero vanishes. -/
theorem module_d_eq_zero_of_concentrated (M : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) (x : M.M) : M.d x = 0 := by
  have h := M.d_mem 0 x (module_mem_grading_zero_of_concentrated M hM x)
  rwa [zero_add, hM 1 (by decide), Submodule.mem_bot] at h

/-- An element of a differential graded module concentrated in degree zero and homogeneous of a
nonzero degree vanishes. -/
theorem module_eq_zero_of_mem_grading_ne (M : DifferentialGradedModule C)
    (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥) {n : ℤ} (hn : n ≠ 0) {x : M.M}
    (hx : x ∈ M.grading n) : x = 0 := by
  have hx : x ∈ (⊥ : Submodule R M.M) := by rwa [← hM n hn]
  exact (Submodule.mem_bot R).mp hx

/-! ### The free module on the elements of a module -/

/-- Scaling a fixed element on the right, as a map of right `C.A`-modules out of `C.A`: this is
the universal property of the free right module of rank one. -/
def rightScalingHom (C : DifferentialGradedAlgebra.{u, u} R) {N : Type u} [AddCommGroup N]
    [Module C.Aᵐᵒᵖ N] (y : N) : C.A →ₗ[C.Aᵐᵒᵖ] N where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' b a := by
    change MulOpposite.op (a * b.unop) • y = b • (MulOpposite.op a • y)
    rw [smul_smul, MulOpposite.op_mul, MulOpposite.op_unop]

/-- **The free right `C.A`-module on the elements of `N`**, mapped onto `N`: the free module is
`⨁_{y ∈ N} C.A` and the map sends the generator at `y` to `y`. -/
def freeCover (C : DifferentialGradedAlgebra.{u, u} R) (N : ModuleCat.{u} C.Aᵐᵒᵖ) :
    (⨁ (_ : N), C.A) →ₗ[C.Aᵐᵒᵖ] N :=
  DirectSum.toModule C.Aᵐᵒᵖ (↥N) (↥N) (fun y => rightScalingHom C y)

/-- The free cover sends the generator at `y` with coefficient `a` to `y` scaled by `a`. -/
@[simp] theorem freeCover_lof (N : ModuleCat.{u} C.Aᵐᵒᵖ) (y : ↥N) (a : C.A) :
    freeCover C N (DirectSum.lof C.Aᵐᵒᵖ (↥N) (fun _ => C.A) y a) = MulOpposite.op a • y :=
  DirectSum.toModule_lof (R := C.Aᵐᵒᵖ) (M := fun _ : ↥N => C.A) (N := ↥N) y a

/-- The free cover sends the generator at `y` with coefficient `1` to `y`. -/
private theorem freeCover_lof_one (N : ModuleCat.{u} C.Aᵐᵒᵖ) (y : ↥N) :
    freeCover C N (DirectSum.lof C.Aᵐᵒᵖ (↥N) (fun _ => C.A) y 1) = y := by
  rw [freeCover_lof, MulOpposite.op_one, one_smul]

/-- The free cover of a module is surjective. -/
theorem freeCover_surjective (N : ModuleCat.{u} C.Aᵐᵒᵖ) :
    Function.Surjective (freeCover C N) := fun y =>
  ⟨DirectSum.lof C.Aᵐᵒᵖ (↥N) (fun _ => C.A) y 1, freeCover_lof_one N y⟩

/-- Scaling the free generator at `y`: the generator with coefficient `1` scaled by `a` on the
right is the generator with coefficient `a`. -/
theorem lof_op_smul {X : Type u} (y : X) (a : C.A) :
    MulOpposite.op a • DirectSum.lof C.Aᵐᵒᵖ X (fun _ => C.A) y 1 =
      DirectSum.lof C.Aᵐᵒᵖ X (fun _ => C.A) y a := by
  refine DirectSum.ext fun i => ?_
  rw [DirectSum.smul_apply, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  by_cases hi : i = y
  · subst hi
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    change MulOpposite.op a • (1 : C.A) = a
    rw [show MulOpposite.op a • (1 : C.A) = 1 * a from rfl, one_mul]
  · rw [DirectSum.of_eq_of_ne _ _ _ hi, DirectSum.of_eq_of_ne _ _ _ hi, smul_zero]

/-- **The tower of iterated kernels.** The zeroth stage is `M` itself and the `(m + 1)`-st is
the kernel of the free cover of the `m`-th: the elements of the `(m + 1)`-st stage are the
relations among the generators of the `m`-th, so they index the cells of the resolution in
degree `-(m + 1)`. -/
def cellTower (C : DifferentialGradedAlgebra.{u, u} R) (M₀ : ModuleCat.{u} C.Aᵐᵒᵖ) :
    ℕ → ModuleCat.{u} C.Aᵐᵒᵖ
  | 0 => M₀
  | (m + 1) => ModuleCat.of _ (LinearMap.ker (freeCover C (cellTower C M₀ m)))

variable (C) (M₀ : ModuleCat.{u} C.Aᵐᵒᵖ)

/-- The cells of the resolution in degree `-m`: the elements of the `m`-th stage of the tower. -/
abbrev cellIndex (m : ℕ) : Type u := ↥(cellTower C M₀ m)

/-- The degree-`-m` part of the resolution: the free right `C.A`-module on the cells of
level `m`. -/
abbrev cellBlock (m : ℕ) : Type u := ⨁ (_ : cellIndex C M₀ m), C.A

/-- A cell of level `m + 1` is an element of the free module on the cells of level `m`, namely a
relation among them; this is the element it is. -/
def cellAttach (m : ℕ) : cellIndex C M₀ (m + 1) →ₗ[C.Aᵐᵒᵖ] cellBlock C M₀ m :=
  (LinearMap.ker (freeCover C (cellTower C M₀ m))).subtype

/-- A cell of level `m + 1` is killed by the free cover of the `m`-th stage of the tower. -/
theorem freeCover_cellAttach (m : ℕ) (y : cellIndex C M₀ (m + 1)) :
    freeCover C (cellTower C M₀ m) (cellAttach C M₀ m y) = 0 := y.property

/-- Distinct cells of level `m + 1` are distinct relations among the cells of level `m`. -/
theorem cellAttach_injective (m : ℕ) : Function.Injective (cellAttach C M₀ m) :=
  Subtype.val_injective

/-- An element of the free module on the cells of level `m` killed by the free cover is a cell of
level `m + 1`. -/
theorem exists_cellAttach_eq (m : ℕ) {z : cellBlock C M₀ m}
    (hz : freeCover C (cellTower C M₀ m) z = 0) :
    ∃ y : cellIndex C M₀ (m + 1), cellAttach C M₀ m y = z :=
  ⟨⟨z, hz⟩, rfl⟩

/-! ### The differential of the resolution -/

/-- The differential of the resolution from level `m + 1` to level `m`: the generator at a cell
goes to the relation that cell is. -/
def cellDiff (m : ℕ) : cellBlock C M₀ (m + 1) →ₗ[C.Aᵐᵒᵖ] cellBlock C M₀ m :=
  DirectSum.toModule C.Aᵐᵒᵖ _ _ (fun y => rightScalingHom C (cellAttach C M₀ m y))

/-- The differential of the resolution is the free cover followed by the inclusion of the
relations: that is what makes the resolution exact. -/
theorem cellDiff_eq (m : ℕ) :
    cellDiff C M₀ m = (cellAttach C M₀ m).comp (freeCover C (cellTower C M₀ (m + 1))) := by
  refine DirectSum.linearMap_ext _ fun y => ?_
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, freeCover_lof, LinearMap.map_smul]
  exact DirectSum.toModule_lof (R := C.Aᵐᵒᵖ)
    (M := fun _ : cellIndex C M₀ (m + 1) => C.A) (N := cellBlock C M₀ m) y a

/-- The free cover of the `m`-th stage kills every boundary of the resolution in level `m`. -/
theorem freeCover_cellDiff (m : ℕ) (z : cellBlock C M₀ (m + 1)) :
    freeCover C (cellTower C M₀ m) (cellDiff C M₀ m z) = 0 := by
  rw [cellDiff_eq]
  exact freeCover_cellAttach C M₀ m _

/-- **Exactness of the resolution.** An element of the free module on the cells of level `m` is
killed by the free cover exactly when it is a boundary. -/
theorem freeCover_eq_zero_iff (m : ℕ) (z : cellBlock C M₀ m) :
    freeCover C (cellTower C M₀ m) z = 0 ↔ ∃ w, cellDiff C M₀ m w = z := by
  refine ⟨fun hz => ?_, fun ⟨w, hw⟩ => hw ▸ freeCover_cellDiff C M₀ m w⟩
  obtain ⟨y, hy⟩ := exists_cellAttach_eq C M₀ m hz
  refine ⟨DirectSum.lof C.Aᵐᵒᵖ (cellIndex C M₀ (m + 1)) (fun _ => C.A) y 1, ?_⟩
  rw [cellDiff_eq, LinearMap.comp_apply, freeCover_lof_one, hy]

/-- An element of level `m + 1` is a cycle of the resolution exactly when it is a boundary. -/
theorem cellDiff_eq_zero_iff (m : ℕ) (z : cellBlock C M₀ (m + 1)) :
    cellDiff C M₀ m z = 0 ↔ ∃ w, cellDiff C M₀ (m + 1) w = z := by
  rw [← freeCover_eq_zero_iff, cellDiff_eq, LinearMap.comp_apply,
    ← LinearMap.map_zero (cellAttach C M₀ m)]
  exact ⟨fun h => cellAttach_injective C M₀ m h, fun h => by rw [h, map_zero]⟩

/-! ### The resolution as a differential graded module -/

/-- The cells of the resolution: a level together with a cell of that level. -/
abbrev resolutionIndex : Type u := (m : ℕ) × cellIndex C M₀ m

/-- A cell of level `m` sits in degree `-m`, that is, it is a shift of the algebra by `m`. -/
def resolutionShift : resolutionIndex C M₀ → ℤ := fun i => (i.1 : ℤ)

/-- The cells of the resolution, sorted by level: the underlying graded module of the resolution
is the direct sum over the cells, and this is its presentation as a direct sum over the levels of
the free modules on the cells of each level. -/
def resolutionCurry :
    (⨁ (_ : resolutionIndex C M₀), C.A) ≃ₗ[C.Aᵐᵒᵖ] ⨁ (m : ℕ), cellBlock C M₀ m :=
  DirectSum.sigmaLcurryEquiv C.Aᵐᵒᵖ (δ := fun (_ : ℕ) (_ : _) => C.A)

/-- The coordinate of `resolutionCurry C M₀ x` at level `m` and cell `y` is the coordinate of
`x` at the cell `⟨m, y⟩`. -/
@[simp] theorem resolutionCurry_apply (x : ⨁ (_ : resolutionIndex C M₀), C.A) (m : ℕ)
    (y : cellIndex C M₀ m) : (resolutionCurry C M₀ x) m y = x ⟨m, y⟩ := rfl

/-- The coordinate of the inverse of `resolutionCurry C M₀` at the cell `i` is the coordinate of
`w` at the level and cell of `i`. -/
@[simp] theorem resolutionCurry_symm_apply (w : ⨁ (m : ℕ), cellBlock C M₀ m)
    (i : resolutionIndex C M₀) : ((resolutionCurry C M₀).symm w) i = w i.1 i.2 := rfl

/-- The inclusion of the level-`m` part into the direct sum over all cells. -/
def cellBlockEmbed (m : ℕ) : cellBlock C M₀ m →ₗ[C.Aᵐᵒᵖ] (⨁ (_ : resolutionIndex C M₀), C.A) :=
  (resolutionCurry C M₀).symm.toLinearMap.comp
    (DirectSum.lof C.Aᵐᵒᵖ ℕ (cellBlock C M₀) m)

/-- On a cell of level `m`, the inclusion of the level-`m` part has the original coordinate. -/
theorem cellBlockEmbed_apply_same (m : ℕ) (z : cellBlock C M₀ m) (y : cellIndex C M₀ m) :
    (cellBlockEmbed C M₀ m z) ⟨m, y⟩ = z y := by
  rw [cellBlockEmbed]
  change ((DirectSum.lof C.Aᵐᵒᵖ ℕ (cellBlock C M₀) m z) m) y = z y
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]

/-- The inclusion of the level-`m` part vanishes on the cells of every other level. -/
theorem cellBlockEmbed_apply_ne (m m' : ℕ) (hm : m' ≠ m) (z : cellBlock C M₀ m)
    (y : cellIndex C M₀ m') : (cellBlockEmbed C M₀ m z) ⟨m', y⟩ = 0 := by
  rw [cellBlockEmbed]
  change ((DirectSum.lof C.Aᵐᵒᵖ ℕ (cellBlock C M₀) m z) m') y = 0
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hm, DirectSum.zero_apply]

/-- The inclusion of the level-`m` part is injective. -/
theorem cellBlockEmbed_injective (m : ℕ) : Function.Injective (cellBlockEmbed C M₀ m) := by
  intro z z' h
  refine DirectSum.ext fun y => ?_
  rw [← cellBlockEmbed_apply_same C M₀ m z y, ← cellBlockEmbed_apply_same C M₀ m z' y, h]

/-- The inclusion of the level-`m` part commutes with right multiplication by `C.A`. -/
theorem cellBlockEmbed_op_smul (m : ℕ) (a : C.A) (z : cellBlock C M₀ m) :
    cellBlockEmbed C M₀ m (MulOpposite.op a • z) =
      MulOpposite.op a • cellBlockEmbed C M₀ m z :=
  (cellBlockEmbed C M₀ m).map_smul (MulOpposite.op a) z

/-- The inclusion of the level-`m` part commutes with scalar multiplication by `R`. -/
theorem cellBlockEmbed_smul (m : ℕ) (r : R) (z : cellBlock C M₀ m) :
    cellBlockEmbed C M₀ m (r • z) = r • cellBlockEmbed C M₀ m z :=
  ((cellBlockEmbed C M₀ m).restrictScalars R).map_smul r z

/-- The generator at the cell `⟨m, y⟩` is the inclusion of the generator at `y` in level `m`. -/
theorem lof_eq_cellBlockEmbed (m : ℕ) (y : cellIndex C M₀ m) (a : C.A) :
    DirectSum.lof C.Aᵐᵒᵖ (resolutionIndex C M₀) (fun _ => C.A) ⟨m, y⟩ a =
      cellBlockEmbed C M₀ m
        (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C M₀ m) (fun _ => C.A) y a) := by
  refine DirectSum.ext fun i => ?_
  obtain ⟨m', y'⟩ := i
  by_cases hm : m' = m
  · subst hm
    rw [cellBlockEmbed_apply_same, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    by_cases hy : y' = y
    · subst hy; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · have hne : (⟨m', y'⟩ : resolutionIndex C M₀) ≠ ⟨m', y⟩ := by
        simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, true_and]
        exact hy
      rw [DirectSum.of_eq_of_ne _ _ _ hne, DirectSum.of_eq_of_ne _ _ _ hy]
  · rw [cellBlockEmbed_apply_ne C M₀ m m' hm, DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne _ _ _ (fun h => hm (congrArg Sigma.fst h))]

/-- The differential of the resolution, on the presentation by levels: the level-`m` component of
the differential of `w` is the differential of the level-`(m + 1)` component of `w`. -/
def resolutionDiffCurried :
    (⨁ (m : ℕ), cellBlock C M₀ m) →ₗ[C.Aᵐᵒᵖ] (⨁ (m : ℕ), cellBlock C M₀ m) :=
  DirectSum.toModule C.Aᵐᵒᵖ ℕ _ (fun m =>
    match m with
    | 0 => 0
    | (m + 1) => (DirectSum.lof C.Aᵐᵒᵖ ℕ (cellBlock C M₀) m).comp (cellDiff C M₀ m))

/-- The level-`m` component of `resolutionDiffCurried C M₀ w` is the differential of the
level-`(m + 1)` component of `w`. -/
theorem resolutionDiffCurried_apply (w : ⨁ (m : ℕ), cellBlock C M₀ m) (m : ℕ) :
    (resolutionDiffCurried C M₀ w) m = cellDiff C M₀ m (w (m + 1)) := by
  induction w using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of j z =>
    rw [← DirectSum.lof_eq_of C.Aᵐᵒᵖ, resolutionDiffCurried,
      DirectSum.toModule_lof (R := C.Aᵐᵒᵖ)]
    match j with
    | 0 =>
      change (0 : ⨁ (m : ℕ), cellBlock C M₀ m) m = _
      rw [DirectSum.zero_apply, DirectSum.lof_eq_of,
        DirectSum.of_eq_of_ne _ _ _ (by omega : m + 1 ≠ 0), map_zero]
    | (j + 1) =>
      change ((DirectSum.lof C.Aᵐᵒᵖ ℕ (cellBlock C M₀) j) (cellDiff C M₀ j z)) m = _
      by_cases hj : j = m
      · subst hj
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.lof_eq_of,
          DirectSum.of_eq_same]
      · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj), DirectSum.lof_eq_of,
          DirectSum.of_eq_of_ne _ _ _ (by omega : m + 1 ≠ j + 1), map_zero]
  | add w w' hw hw' =>
    rw [map_add, DirectSum.add_apply, hw, hw', DirectSum.add_apply, map_add]

/-- The differential of the resolution. -/
def resolutionDiff :
    (⨁ (_ : resolutionIndex C M₀), C.A) →ₗ[C.Aᵐᵒᵖ] (⨁ (_ : resolutionIndex C M₀), C.A) :=
  ((resolutionCurry C M₀).symm.toLinearMap.comp (resolutionDiffCurried C M₀)).comp
    (resolutionCurry C M₀).toLinearMap

/-- The differential of the resolution vanishes on the cells of level zero. -/
theorem resolutionDiff_cellBlockEmbed_zero (z : cellBlock C M₀ 0) :
    resolutionDiff C M₀ (cellBlockEmbed C M₀ 0 z) = 0 := by
  rw [resolutionDiff, cellBlockEmbed]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [resolutionDiffCurried, DirectSum.toModule_lof (R := C.Aᵐᵒᵖ)]
  change (resolutionCurry C M₀).symm (0 : ⨁ (m : ℕ), cellBlock C M₀ m) = 0
  rw [map_zero]

/-- On the level-`(m + 1)` part, the differential of the resolution is `cellDiff C M₀ m`, landing
in the level-`m` part. -/
theorem resolutionDiff_cellBlockEmbed_succ (m : ℕ) (z : cellBlock C M₀ (m + 1)) :
    resolutionDiff C M₀ (cellBlockEmbed C M₀ (m + 1) z) =
      cellBlockEmbed C M₀ m (cellDiff C M₀ m z) := by
  rw [resolutionDiff, cellBlockEmbed, cellBlockEmbed]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [resolutionDiffCurried, DirectSum.toModule_lof (R := C.Aᵐᵒᵖ)]
  rfl

/-- The differential of the resolution squares to zero. -/
theorem resolutionDiff_comp_resolutionDiff (x : ⨁ (_ : resolutionIndex C M₀), C.A) :
    resolutionDiff C M₀ (resolutionDiff C M₀ x) = 0 := by
  have key : ∀ w : ⨁ (m : ℕ), cellBlock C M₀ m,
      resolutionDiffCurried C M₀ (resolutionDiffCurried C M₀ w) = 0 := by
    intro w
    refine DirectSum.ext fun m => ?_
    rw [resolutionDiffCurried_apply, resolutionDiffCurried_apply, DirectSum.zero_apply]
    exact (cellDiff_eq_zero_iff C M₀ m _).mpr ⟨w (m + 1 + 1), rfl⟩
  rw [resolutionDiff]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [key, map_zero]

/-! ### The grading of the resolution -/

/-- An element of the direct sum over the cells is homogeneous of degree `-m` exactly when it is
supported on the cells of level `m`. -/
theorem mem_directSumShifts_grading_neg (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥) (m : ℕ)
    (x : ⨁ (_ : resolutionIndex C M₀), C.A) :
    x ∈ (directSumShifts C (resolutionShift C M₀)).grading (-(m : ℤ)) ↔
      ∃ z, x = cellBlockEmbed C M₀ m z := by
  rw [mem_directSumShifts_grading]
  constructor
  · intro hx
    have hzero : ∀ (m' : ℕ) (y : cellIndex C M₀ m'), m' ≠ m → x ⟨m', y⟩ = 0 := by
      intro m' y hm'
      have h := hx ⟨m', y⟩
      rwa [hC (-(m : ℤ) + resolutionShift C M₀ ⟨m', y⟩)
        (by simp only [resolutionShift]; omega), Submodule.mem_bot] at h
    refine ⟨resolutionCurry C M₀ x m, DirectSum.ext fun i => ?_⟩
    obtain ⟨m', y⟩ := i
    by_cases hm' : m' = m
    · subst hm'
      rw [cellBlockEmbed_apply_same, resolutionCurry_apply]
    · rw [cellBlockEmbed_apply_ne C M₀ m m' hm', hzero m' y hm']
  · rintro ⟨z, rfl⟩ i
    obtain ⟨m', y⟩ := i
    by_cases hm' : m' = m
    · subst hm'
      rw [cellBlockEmbed_apply_same,
        show -(m' : ℤ) + resolutionShift C M₀ (⟨m', y⟩ : resolutionIndex C M₀) = 0 by
          simp only [resolutionShift]; omega]
      exact mem_grading_zero_of_concentrated hC (z y)
    · rw [cellBlockEmbed_apply_ne C M₀ m m' hm']
      exact Submodule.zero_mem _

/-- The direct sum over the cells has nothing in positive degrees: every cell sits in a degree
`≤ 0`. -/
theorem mem_directSumShifts_grading_pos (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥) {n : ℤ}
    (hn : 0 < n) (x : ⨁ (_ : resolutionIndex C M₀), C.A) :
    x ∈ (directSumShifts C (resolutionShift C M₀)).grading n ↔ x = 0 := by
  rw [mem_directSumShifts_grading]
  refine ⟨fun hx => DirectSum.ext fun i => ?_, fun hx i => ?_⟩
  · have h := hx i
    rw [hC (n + resolutionShift C M₀ i) (by simp only [resolutionShift]; omega),
      Submodule.mem_bot] at h
    rw [h, DirectSum.zero_apply]
  · rw [hx, DirectSum.zero_apply]
    exact Submodule.zero_mem _

/-! ### The resolution as a differential graded module -/

/-- **The free resolution of a module concentrated in degree zero**, as a differential graded
module: its underlying graded module is the direct sum of shifts of `C` over the cells, a cell of
level `m` contributing in degree `-m`, and its differential takes a cell of level `m + 1` to the
relation among the cells of level `m` that it is. -/
def freeResolution (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥) :
    DifferentialGradedModule.{u, u, u} C :=
  { directSumShifts C (resolutionShift C M₀) with
    d := (resolutionDiff C M₀).restrictScalars R
    d_comp_d := LinearMap.ext fun x => resolutionDiff_comp_resolutionDiff C M₀ x
    d_mem := by
      intro n x hx
      change resolutionDiff C M₀ x ∈
        (directSumShifts C (resolutionShift C M₀)).grading (n + 1)
      rcases le_or_gt n 0 with hn | hn
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
        obtain ⟨z, rfl⟩ := (mem_directSumShifts_grading_neg C M₀ hC m x).mp hx
        match m with
        | 0 =>
          rw [resolutionDiff_cellBlockEmbed_zero]
          exact Submodule.zero_mem _
        | (m + 1) =>
          rw [resolutionDiff_cellBlockEmbed_succ]
          refine mem_grading_congr (A := C) (M := directSumShifts C (resolutionShift C M₀))
            (show -(m : ℤ) = -((m + 1 : ℕ) : ℤ) + 1 by push_cast; omega)
            ((mem_directSumShifts_grading_neg C M₀ hC m _).mpr ⟨_, rfl⟩)
      · rw [(mem_directSumShifts_grading_pos C M₀ hC hn x).mp hx, map_zero]
        exact Submodule.zero_mem _
    leibniz := by
      intro n m x a _ _
      have h3 : (MulOpposite.op (C.d a)) • x = 0 := by
        rw [d_eq_zero_of_concentrated hC a, MulOpposite.op_zero, zero_smul]
      rw [h3, smul_zero, add_zero]
      exact (resolutionDiff C M₀).map_smul (MulOpposite.op a) x }

variable (hC : ∀ n : ℤ, n ≠ 0 → C.grading n = ⊥)

/-- The differential of `freeResolution C M₀ hC` is `resolutionDiff C M₀`. -/
@[simp] theorem freeResolution_d (x : (freeResolution C M₀ hC).M) :
    (freeResolution C M₀ hC).d x = resolutionDiff C M₀ x := rfl

/-- An element of the resolution is homogeneous of degree `-m` exactly when it is supported on the
cells of level `m`. -/
theorem freeResolution_mem_grading_neg (m : ℕ) (x : (freeResolution C M₀ hC).M) :
    x ∈ (freeResolution C M₀ hC).grading (-(m : ℤ)) ↔ ∃ z, x = cellBlockEmbed C M₀ m z :=
  mem_directSumShifts_grading_neg C M₀ hC m x

/-- The resolution has nothing in positive degrees. -/
theorem freeResolution_mem_grading_pos {n : ℤ} (hn : 0 < n) (x : (freeResolution C M₀ hC).M) :
    x ∈ (freeResolution C M₀ hC).grading n ↔ x = 0 :=
  mem_directSumShifts_grading_pos C M₀ hC hn x

/-- The level-`m` part of the resolution is homogeneous of degree `-m`. -/
theorem cellBlockEmbed_mem_grading (m : ℕ) (z : cellBlock C M₀ m) :
    cellBlockEmbed C M₀ m z ∈ (freeResolution C M₀ hC).grading (-(m : ℤ)) :=
  (freeResolution_mem_grading_neg C M₀ hC m _).mpr ⟨z, rfl⟩

/-- The level-`m` part of the resolution is homogeneous of any degree equal to `-m`. -/
private theorem cellBlockEmbed_mem_grading_of_eq {m : ℕ} {n : ℤ} (hmn : -(m : ℤ) = n)
    (z : cellBlock C M₀ m) : cellBlockEmbed C M₀ m z ∈ (freeResolution C M₀ hC).grading n :=
  mem_grading_congr (A := C) (M := freeResolution C M₀ hC) hmn
    (cellBlockEmbed_mem_grading C M₀ hC m z)

/-! ### The resolution is orthogonal on the left to the acyclic modules -/

/-- The level-`m` component of the differential of `x` is the differential of the
level-`(m + 1)` component of `x`. -/
theorem resolutionCurry_resolutionDiff (x : ⨁ (_ : resolutionIndex C M₀), C.A) (m : ℕ) :
    (resolutionCurry C M₀ (resolutionDiff C M₀ x)) m =
      cellDiff C M₀ m ((resolutionCurry C M₀ x) (m + 1)) := by
  rw [resolutionDiff]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [resolutionDiffCurried_apply]

/-- The coordinates of the differential of the resolution, in the form the cell-decomposition
criterion asks for: the level-`m` coordinate of the differential is the differential of the
level-`(m + 1)` coordinate. -/
theorem restrictScalars_resolutionCurry_freeResolution_d (x : (freeResolution C M₀ hC).M)
    (m : ℕ) :
    ((((resolutionCurry C M₀).restrictScalars R) ((freeResolution C M₀ hC).d x)) m) =
      cellDiff C M₀ m ((((resolutionCurry C M₀).restrictScalars R) x) (m + 1)) :=
  resolutionCurry_resolutionDiff C M₀ x m

/-- **The resolution is orthogonal on the left to the acyclic modules.** Its cells, sorted by
level, are a triangular cell decomposition in the sense of
`DifferentialGradedModule.ExhaustiveCellData`: the graded pieces are the free modules on the
cells of each level, which are direct sums of shifts of `C`, and the differential lowers the
level by exactly one. -/
theorem leftOrthogonal_acyclic_freeResolution :
    (acyclic' C).leftOrthogonal ((toHomotopyCategory C).obj (freeResolution C M₀ hC)) := by
  refine leftOrthogonal_acyclic_of_exhaustiveCellCoords (I := fun m => cellIndex C M₀ m)
    (fun m _ => (m : ℤ)) ((resolutionCurry C M₀).restrictScalars R) (fun a x m => ?_)
    (fun n x => ?_) (fun k x hx m hm => ?_) (fun k x hx i => ?_)
  · exact congrArg (fun w => w m) ((resolutionCurry C M₀).map_smul (MulOpposite.op a) x)
  · exact (mem_directSumShifts_grading (resolutionShift C M₀) n x).trans
      ⟨fun h m i => h ⟨m, i⟩, fun h i => h i.1 i.2⟩
  · have h0 : (((resolutionCurry C M₀).restrictScalars R) x) (m + 1) = 0 :=
      hx (m + 1) (by omega)
    exact (restrictScalars_resolutionCurry_freeResolution_d C M₀ hC x m).trans
      (by rw [h0, map_zero])
  · have h0 : (((resolutionCurry C M₀).restrictScalars R) x) (k + 1) = 0 :=
      hx (k + 1) (by omega)
    have hlhs : ((((resolutionCurry C M₀).restrictScalars R)
        ((freeResolution C M₀ hC).d x)) k) i = 0 := by
      rw [restrictScalars_resolutionCurry_freeResolution_d, h0, map_zero, DirectSum.zero_apply]
    refine hlhs.trans ?_
    rw [d_eq_zero_of_concentrated hC, smul_zero]

/-! ### The augmentation of the resolution -/

section Augmentation

variable (M : DifferentialGradedModule.{u, u, u} C)

/-- The module underlying a differential graded module, bundled: the free resolution of `M` is
built on the elements of `M`. -/
abbrev moduleObj : ModuleCat.{u} C.Aᵐᵒᵖ := ModuleCat.of C.Aᵐᵒᵖ M.M

/-- **The free resolution of a differential graded module concentrated in degree zero.** -/
abbrev concentratedResolution : DifferentialGradedModule.{u, u, u} C :=
  freeResolution C (moduleObj C M) hC

/-- The free cover of `M` by the cells of level zero of the resolution. -/
def resolutionCover : cellBlock C (moduleObj C M) 0 →ₗ[C.Aᵐᵒᵖ] M.M :=
  freeCover C (cellTower C (moduleObj C M) 0)

/-- The free cover of `M` sends the generator at `y` with coefficient `a` to `y` scaled by `a`. -/
theorem resolutionCover_lof (y : M.M) (a : C.A) :
    resolutionCover C M
        (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y a) =
      MulOpposite.op a • y :=
  freeCover_lof (cellTower C (moduleObj C M) 0) y a

/-- The free cover of `M` sends the generator at `y` with coefficient `1` to `y`. -/
private theorem resolutionCover_lof_one (y : M.M) :
    resolutionCover C M (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1) =
      y :=
  freeCover_lof_one (cellTower C (moduleObj C M) 0) y

/-- The free cover of `M` commutes with scalar multiplication by `R`. -/
theorem resolutionCover_smul (r : R) (z : cellBlock C (moduleObj C M) 0) :
    resolutionCover C M (r • z) = r • resolutionCover C M z :=
  ((resolutionCover C M).restrictScalars R).map_smul r z

/-- An element of level zero is killed by the free cover of `M` exactly when it is a boundary. -/
theorem resolutionCover_eq_zero_iff (z : cellBlock C (moduleObj C M) 0) :
    resolutionCover C M z = 0 ↔ ∃ w, cellDiff C (moduleObj C M) 0 w = z :=
  freeCover_eq_zero_iff C (moduleObj C M) 0 z

/-- The free cover of `M` kills the boundaries of level zero. -/
theorem resolutionCover_cellDiff (z : cellBlock C (moduleObj C M) 1) :
    resolutionCover C M (cellDiff C (moduleObj C M) 0 z) = 0 :=
  freeCover_cellDiff C (moduleObj C M) 0 z

/-- The augmentation of the free resolution, as a map of right `C.A`-modules: on the cells of
level zero it is the free cover of `M`, and it kills the cells of the higher levels. -/
def resolutionAugMap :
    (⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) →ₗ[C.Aᵐᵒᵖ] M.M :=
  (resolutionCover C M).comp
    ((DirectSum.component C.Aᵐᵒᵖ ℕ (cellBlock C (moduleObj C M)) 0).comp
      (resolutionCurry C (moduleObj C M)).toLinearMap)

/-- The augmentation is the free cover of `M` applied to the level-zero component. -/
theorem resolutionAugMap_apply (x : ⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) :
    resolutionAugMap C M x =
      resolutionCover C M ((resolutionCurry C (moduleObj C M) x) 0) := rfl

/-- On the level-zero part, the augmentation is the free cover of `M`. -/
theorem resolutionAugMap_cellBlockEmbed_zero (z : cellBlock C (moduleObj C M) 0) :
    resolutionAugMap C M (cellBlockEmbed C (moduleObj C M) 0 z) =
      resolutionCover C M z := by
  rw [resolutionAugMap_apply, cellBlockEmbed]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]

/-- The augmentation kills the cells of positive level. -/
theorem resolutionAugMap_cellBlockEmbed_succ (m : ℕ) (z : cellBlock C (moduleObj C M) (m + 1)) :
    resolutionAugMap C M (cellBlockEmbed C (moduleObj C M) (m + 1) z) = 0 := by
  rw [resolutionAugMap_apply, cellBlockEmbed]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (by omega : (0 : ℕ) ≠ m + 1)]
  exact map_zero _

/-- The augmentation kills the boundaries of the resolution. -/
theorem resolutionAugMap_resolutionDiff (x : ⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) :
    resolutionAugMap C M (resolutionDiff C (moduleObj C M) x) = 0 := by
  rw [resolutionAugMap_apply, resolutionCurry_resolutionDiff]
  exact resolutionCover_cellDiff C M _

variable (hM : ∀ n : ℤ, n ≠ 0 → M.grading n = ⊥)

/-- **The augmentation of the free resolution**, as a homomorphism of differential graded
modules. It preserves the grading because the resolution has nothing in positive degrees and the
augmentation kills the cells of positive level, and it commutes with the differentials because
both composites vanish: the differential of `M` is zero and the augmentation kills the
boundaries. -/
def concentratedAug : concentratedResolution C hC M ⟶ M where
  toFun := (resolutionAugMap C M).restrictScalars R
  map_smul x a := (resolutionAugMap C M).map_smul (MulOpposite.op a) x
  map_grading := by
    intro n x hx
    by_cases hn : n = 0
    · subst hn
      exact module_mem_grading_zero_of_concentrated M hM _
    · have hzero : resolutionAugMap C M x = 0 := by
        rcases le_or_gt n 0 with hle | hlt
        · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
          obtain ⟨z, rfl⟩ := (freeResolution_mem_grading_neg C (moduleObj C M) hC m x).mp hx
          match m with
          | 0 => exact absurd rfl hn
          | (m + 1) => exact resolutionAugMap_cellBlockEmbed_succ C M m z
        · rw [(freeResolution_mem_grading_pos C (moduleObj C M) hC hlt x).mp hx]
          exact map_zero _
      rw [hM n hn]
      exact (Submodule.mem_bot R).mpr hzero
  map_d := by
    refine LinearMap.ext fun x => ?_
    change resolutionAugMap C M (resolutionDiff C (moduleObj C M) x) =
      M.d (resolutionAugMap C M x)
    rw [module_d_eq_zero_of_concentrated M hM]
    exact resolutionAugMap_resolutionDiff C M x

/-- The underlying map of `concentratedAug C hC M hM` is `resolutionAugMap C M`. -/
@[simp] theorem concentratedAug_toFun (x : (concentratedResolution C hC M).M) :
    (concentratedAug C hC M hM).toFun x = resolutionAugMap C M x := rfl

/-- **The augmentation is a quasi-isomorphism.** In degree zero every element of `M` is the image
of the generator attached to it and every cocycle of the resolution killed by the augmentation is
a relation, hence a boundary; in the negative degrees the exactness of the resolution is the
definition of its cells; and in the positive degrees both modules vanish. -/
theorem concentratedAug_isQuasiIsomorphism :
    IsQuasiIsomorphism (concentratedAug C hC M hM) := by
  intro n
  constructor
  · intro y hy _
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨cellBlockEmbed C (moduleObj C M) 0
        (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1), ?_, ?_, 0,
        Submodule.zero_mem _, ?_⟩
      · exact cellBlockEmbed_mem_grading_of_eq C (moduleObj C M) hC (by norm_num) _
      · exact resolutionDiff_cellBlockEmbed_zero C (moduleObj C M) _
      · have hfx : (concentratedAug C hC M hM).toFun
            (cellBlockEmbed C (moduleObj C M) 0
              (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1)) = y :=
          (resolutionAugMap_cellBlockEmbed_zero C M _).trans (resolutionCover_lof_one C M y)
        rw [module_d_eq_zero_of_concentrated M hM, hfx, sub_self]
    · refine ⟨0, Submodule.zero_mem _, map_zero _, 0, Submodule.zero_mem _, ?_⟩
      rw [module_d_eq_zero_of_concentrated M hM, module_eq_zero_of_mem_grading_ne M hM hn hy,
        map_zero, sub_self]
  · intro x hx hdx hfx
    obtain ⟨w, hw, hdw⟩ := hfx
    have hzero : resolutionAugMap C M x = 0 :=
      hdw.symm.trans (module_d_eq_zero_of_concentrated M hM w)
    rcases le_or_gt n 0 with hle | hlt
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hle
      obtain ⟨z, rfl⟩ := (freeResolution_mem_grading_neg C (moduleObj C M) hC m x).mp hx
      match m with
      | 0 =>
        rw [resolutionAugMap_cellBlockEmbed_zero] at hzero
        obtain ⟨v, hv⟩ := (freeCover_eq_zero_iff C (moduleObj C M) 0 z).mp hzero
        refine ⟨cellBlockEmbed C (moduleObj C M) 1 v, ?_, ?_⟩
        · exact cellBlockEmbed_mem_grading_of_eq C (moduleObj C M) hC (by norm_num) v
        · change resolutionDiff C (moduleObj C M) (cellBlockEmbed C (moduleObj C M) 1 v) = _
          rw [resolutionDiff_cellBlockEmbed_succ, hv]
      | (m + 1) =>
        have hdz : cellDiff C (moduleObj C M) m z = 0 := by
          refine cellBlockEmbed_injective C (moduleObj C M) m ?_
          rwa [map_zero, ← resolutionDiff_cellBlockEmbed_succ]
        obtain ⟨v, hv⟩ := (cellDiff_eq_zero_iff C (moduleObj C M) m z).mp hdz
        refine ⟨cellBlockEmbed C (moduleObj C M) (m + 2) v, ?_, ?_⟩
        · exact cellBlockEmbed_mem_grading_of_eq C (moduleObj C M) hC (by push_cast; omega) v
        · change resolutionDiff C (moduleObj C M) (cellBlockEmbed C (moduleObj C M) (m + 2) v) = _
          rw [resolutionDiff_cellBlockEmbed_succ, hv]
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [(freeResolution_mem_grading_pos C (moduleObj C M) hC hlt x).mp hx, map_zero]

/-! ### Homomorphisms out of the resolution -/

/-- The base ring acts on a right `C.A`-module through the opposite algebra: the opposite of
`r • 1` acts as `r` does. -/
theorem op_smul_one_smul {X : Type u} [AddCommGroup X] [Module R X] [Module C.Aᵐᵒᵖ X]
    [IsScalarTower R C.Aᵐᵒᵖ X] (r : R) (y : X) :
    MulOpposite.op (r • (1 : C.A)) • y = r • y := by
  rw [← Algebra.algebraMap_eq_smul_one,
    show MulOpposite.op (algebraMap R C.A r) = algebraMap R C.Aᵐᵒᵖ r from rfl,
    IsScalarTower.algebraMap_smul]

/-- The cell of level zero attached to an element of `M`: the free generator at that element. -/
def resolutionGen (y : M.M) : (concentratedResolution C hC M).M :=
  cellBlockEmbed C (moduleObj C M) 0
    (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1)

/-- The augmentation sends the generator attached to `y` to `y`. -/
theorem resolutionAugMap_resolutionGen (y : M.M) :
    resolutionAugMap C M (resolutionGen C hC M y) = y :=
  (resolutionAugMap_cellBlockEmbed_zero C M _).trans (resolutionCover_lof_one C M y)

variable (N : DifferentialGradedModule.{u, u, u} C)
  (hN : ∀ n : ℤ, n ≠ 0 → N.grading n = ⊥)

/-- A homomorphism out of the resolution preserves subtraction. -/
theorem hom_toFun_sub (h : concentratedResolution C hC M ⟶ N)
    (x y : ⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) :
    h.toFun (x - y) = h.toFun x - h.toFun y := h.toFun.map_sub x y

/-- A homomorphism out of the resolution preserves addition. -/
theorem hom_toFun_add (h : concentratedResolution C hC M ⟶ N)
    (x y : ⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) :
    h.toFun (x + y) = h.toFun x + h.toFun y := h.toFun.map_add x y

/-- A homomorphism out of the resolution commutes with scalar multiplication by `R`. -/
theorem hom_toFun_smul (h : concentratedResolution C hC M ⟶ N) (r : R)
    (x : ⨁ (_ : resolutionIndex C (moduleObj C M)), C.A) :
    h.toFun (r • x) = r • h.toFun x := h.toFun.map_smul r x

include hC hN

/-- **A homomorphism out of the resolution kills the relations.** A cell combination of level
zero killed by the augmentation is a boundary, and the differential of a target concentrated in
degree zero vanishes, so a homomorphism into such a target kills it. -/
theorem hom_cellBlockEmbed_eq_zero (h : concentratedResolution C hC M ⟶ N)
    (z : cellBlock C (moduleObj C M) 0) (hz : resolutionCover C M z = 0) :
    h.toFun (cellBlockEmbed C (moduleObj C M) 0 z) = 0 := by
  obtain ⟨w, hw⟩ := (freeCover_eq_zero_iff C (moduleObj C M) 0 z).mp hz
  have hx : (concentratedResolution C hC M).d (cellBlockEmbed C (moduleObj C M) 1 w)
      = cellBlockEmbed C (moduleObj C M) 0 z :=
    (resolutionDiff_cellBlockEmbed_succ C (moduleObj C M) 0 w).trans (by rw [hw])
  rw [← hx]
  exact (LinearMap.congr_fun h.map_d _).trans (module_d_eq_zero_of_concentrated N hN _)

/-- A homomorphism out of the resolution into a module concentrated in degree zero takes the same
value on two cell combinations of level zero with the same image under the augmentation. -/
theorem hom_cellBlockEmbed_congr (h : concentratedResolution C hC M ⟶ N)
    (z z' : cellBlock C (moduleObj C M) 0)
    (hzz' : resolutionCover C M z = resolutionCover C M z') :
    h.toFun (cellBlockEmbed C (moduleObj C M) 0 z) =
      h.toFun (cellBlockEmbed C (moduleObj C M) 0 z') := by
  have h0 : resolutionCover C M (z - z') = 0 := by rw [map_sub, hzz', sub_self]
  have hzero := hom_cellBlockEmbed_eq_zero C hC M N hN h (z - z') h0
  rw [map_sub, hom_toFun_sub, sub_eq_zero] at hzero
  exact hzero

/-- The value of a homomorphism out of the resolution on a cell combination of level zero is its
value on the generator attached to the image of that combination. -/
theorem hom_cellBlockEmbed_eq_resolutionGen (h : concentratedResolution C hC M ⟶ N)
    (y : M.M) (z : cellBlock C (moduleObj C M) 0) (hz : resolutionCover C M z = y) :
    h.toFun (cellBlockEmbed C (moduleObj C M) 0 z) = h.toFun (resolutionGen C hC M y) :=
  hom_cellBlockEmbed_congr C hC M N hN h z _ (by rw [hz, resolutionCover_lof_one])

/-- **Every homomorphism out of the resolution is the augmentation followed by a homomorphism
`M ⟶ N`.** The homomorphism is read off the cells of level zero: its value on the generator
attached to an element of `M` depends only on that element, since the relations are boundaries,
and it kills the cells of the higher levels for want of room in the target. -/
theorem exists_concentratedAug_comp_eq (h : concentratedResolution C hC M ⟶ N) :
    ∃ z : M ⟶ N, h = concentratedAug C hC M hM ≫ z := by
  have hgen : ∀ (y : M.M) (z : cellBlock C (moduleObj C M) 0),
      resolutionCover C M z = y →
      h.toFun (cellBlockEmbed C (moduleObj C M) 0 z) = h.toFun (resolutionGen C hC M y) :=
    fun y z hz => hom_cellBlockEmbed_eq_resolutionGen C hC M N hN h y z hz
  let zfun : M.M →ₗ[R] N.M :=
    { toFun := fun y => h.toFun (resolutionGen C hC M y)
      map_add' := by
        intro y y'
        rw [← hgen (y + y')
          (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1 +
            DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y' 1)
          (by rw [map_add, resolutionCover_lof_one, resolutionCover_lof_one])]
        rw [map_add, hom_toFun_add]
        rfl
      map_smul' := by
        intro r y
        rw [← hgen (r • y)
          (r • DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y 1)
          (by rw [resolutionCover_smul, resolutionCover_lof_one])]
        rw [cellBlockEmbed_smul, hom_toFun_smul]
        rfl }
  have hz : ∀ y : M.M, zfun y = h.toFun (resolutionGen C hC M y) := fun _ => rfl
  refine ⟨{ toFun := zfun
            map_smul := ?_
            map_grading := ?_
            map_d := ?_ }, ?_⟩
  · intro y a
    have hlof := lof_op_smul (C := C) (X := cellIndex C (moduleObj C M) 0) y a
    have h1 : zfun (MulOpposite.op a • y) = h.toFun (cellBlockEmbed C (moduleObj C M) 0
        (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y a)) :=
      (hgen (MulOpposite.op a • y) _ (resolutionCover_lof C M y a)).symm
    have h2 : MulOpposite.op a • zfun y =
        h.toFun (MulOpposite.op a • resolutionGen C hC M y) :=
      (h.map_smul (resolutionGen C hC M y) a).symm
    have h3 : MulOpposite.op a • resolutionGen C hC M y =
        cellBlockEmbed C (moduleObj C M) 0
          (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y a) :=
      ((cellBlockEmbed_op_smul C (moduleObj C M) 0 a _).symm).trans
        (congrArg (cellBlockEmbed C (moduleObj C M) 0) hlof)
    rw [h1, ← h3, h2]
  · intro n y hy
    by_cases hn : n = 0
    · subst hn
      exact module_mem_grading_zero_of_concentrated N hN _
    · rw [hz, module_eq_zero_of_mem_grading_ne M hM hn hy, hN n hn]
      refine (Submodule.mem_bot R).mpr ?_
      refine hom_cellBlockEmbed_eq_zero C hC M N hN h _ ?_
      rw [resolutionCover_lof, smul_zero]
  · refine LinearMap.ext fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, module_d_eq_zero_of_concentrated M hM,
      module_d_eq_zero_of_concentrated N hN, map_zero]
  · refine DifferentialGradedModule.Hom.ext (DirectSum.linearMap_ext R
      (ι := resolutionIndex C (moduleObj C M)) (M := fun _ => C.A) fun i => ?_)
    obtain ⟨m, y⟩ := i
    refine LinearMap.ext fun a => ?_
    have e1 : DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m, y⟩ a
        = cellBlockEmbed C (moduleObj C M) m
            (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) m) (fun _ => C.A) y a) :=
      lof_eq_cellBlockEmbed C (moduleObj C M) m y a
    change h.toFun (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m, y⟩ a)
      = zfun (resolutionAugMap C M
          (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m, y⟩ a))
    match m with
    | 0 =>
      have e2 : resolutionAugMap C M
          (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨0, y⟩ a) =
          MulOpposite.op a • y :=
        (congrArg (fun t => resolutionAugMap C M t) e1).trans
          ((resolutionAugMap_cellBlockEmbed_zero C M _).trans (resolutionCover_lof C M y a))
      calc h.toFun (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨0, y⟩ a)
          = h.toFun (cellBlockEmbed C (moduleObj C M) 0
              (DirectSum.lof C.Aᵐᵒᵖ (cellIndex C (moduleObj C M) 0) (fun _ => C.A) y a)) :=
            congrArg (fun t => h.toFun t) e1
        _ = h.toFun (resolutionGen C hC M (MulOpposite.op a • y)) :=
            hgen (MulOpposite.op a • y) _ (resolutionCover_lof C M y a)
        _ = zfun (MulOpposite.op a • y) := (hz _).symm
        _ = zfun (resolutionAugMap C M
              (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨0, y⟩ a)) :=
            congrArg (fun t => zfun t) e2.symm
    | (m + 1) =>
      have e2 : resolutionAugMap C M
          (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m + 1, y⟩ a) = 0 :=
        (congrArg (fun t => resolutionAugMap C M t) e1).trans
          (resolutionAugMap_cellBlockEmbed_succ C M m _)
      have e3 : h.toFun
          (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m + 1, y⟩ a)
          = 0 :=
        module_eq_zero_of_mem_grading_ne N hN
          (show -((m + 1 : ℕ) : ℤ) ≠ 0 by push_cast; omega)
          (h.map_grading _ _
            ((freeResolution_mem_grading_neg C (moduleObj C M) hC (m + 1) _).mpr ⟨_, e1⟩))
      calc h.toFun
            (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A) ⟨m + 1, y⟩ a)
          = 0 := e3
        _ = zfun 0 := (map_zero zfun).symm
        _ = zfun (resolutionAugMap C M
              (DirectSum.lof R (resolutionIndex C (moduleObj C M)) (fun _ => C.A)
                ⟨m + 1, y⟩ a)) := congrArg (fun t => zfun t) e2.symm

/-! ### The passage to the derived category is bijective on these homomorphisms -/

include hM in
/-- **Homomorphisms between modules concentrated in degree zero are not changed by the passage to
the derived category.** For a differential graded algebra concentrated in degree zero, every
morphism `M → N` of `D(C, d)` between differential graded modules concentrated in degree zero is
the image of a homomorphism of differential graded modules.

The free resolution `P → M` is orthogonal on the left to the acyclic modules, so the morphisms
out of `M` in the derived category are the homotopy classes of homomorphisms out of `P`, by the
mechanism of Tag 09KY; and every homomorphism `P ⟶ N` is the augmentation followed by a
homomorphism `M ⟶ N`. -/
theorem concentrated_q_map_surjective :
    Function.Surjective ((toHomotopyCategory C ⋙ (quasiIsomorphisms' C).Q).map (X := M)
      (Y := N)) := by
  intro g
  have hquasi : QuasiIso ((forgetToCochainComplex C).map (concentratedAug C hC M hM)) :=
    quasiIso_of_isQuasiIsomorphism _ (concentratedAug_isQuasiIsomorphism C hC M hM)
  have hiso := isIso_q_map_toHomotopyCategory_map (concentratedAug C hC M hM) hquasi
  obtain ⟨α, hα⟩ := (bijective_q_map_of_leftOrthogonal
    (leftOrthogonal_acyclic_freeResolution C (moduleObj C M) hC)
      ((toHomotopyCategory C).obj N)).surjective
    ((quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map (concentratedAug C hC M hM)) ≫ g)
  obtain ⟨h, rfl⟩ := (toHomotopyCategory C).map_surjective α
  obtain ⟨z, rfl⟩ := exists_concentratedAug_comp_eq C hC M hM N hN h
  refine ⟨z, ?_⟩
  rw [Functor.map_comp, Functor.map_comp] at hα
  exact (cancel_epi ((quasiIsomorphisms' C).Q.map
    ((toHomotopyCategory C).map (concentratedAug C hC M hM)))).1 hα

end Augmentation

end DifferentialGradedModule

end
