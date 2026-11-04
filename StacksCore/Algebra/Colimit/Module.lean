module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.Quotient.Basic
import StacksCore.Tactic.StacksAttribute

/-! ## Colimits in the Category of Modules -/

add_to_stacks 00D5 Module.DirectLimit
add_to_stacks 00D5 DirectLimit.Module.of
add_to_stacks 00D5 DirectLimit.Module.lift
add_to_stacks 00D7 DirectLimit.exists_eq_zero
add_to_stacks 00D9 Module.DirectLimit.map
add_to_stacks 00DA Module.DirectLimit.map

variable {R : Type*} [Ring R] {ι : Type*} [Preorder ι] [DecidableEq ι] {L : ι → Type*}
  [(i : ι) → AddCommGroup (L i)] [(i : ι) → Module R (L i)] {f : (i j : ι) → i ≤ j → L i →ₗ[R] L j}
  {M : ι → Type*} [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)]
  {f' : (i j : ι) → i ≤ j → M i →ₗ[R] M j} (g : (i : ι) → L i →ₗ[R] M i)
  (hg : ∀ (i j : ι) (h : i ≤ j), g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
  {N : ι → Type*} [(i : ι) → AddCommGroup (N i)] [(i : ι) → Module R (N i)]
  {l : (i j : ι) → i ≤ j → N i →ₗ[R] N j} (g' : (i : ι) → M i →ₗ[R] N i)
  (hg' : ∀ (i j : ι) (h : i ≤ j), g' j ∘ₗ f' i j h = l i j h ∘ₗ g' i)
  (h : ∀ i : ι, g' i ∘ₗ g i = 0)

include h in
@[stacks 00DB "part 1"]
public lemma Module.DirectLimit.comp_eq_zero :
    Module.DirectLimit.map g' hg' ∘ₗ Module.DirectLimit.map g hg = 0 := by
  ext i xi
  simp [show g' i (g i xi) = 0 by simpa using LinearMap.ext_iff.1 (h i) xi]

noncomputable section

/-- The homology of the direct limits. -/
public abbrev homologyLimit := (Module.DirectLimit.map g' hg').ker ⧸
  (Module.DirectLimit.map g hg).range.submoduleOf (Module.DirectLimit.map g' hg').ker

/-- The homology at each index `i`. -/
public abbrev hObj (i : ι) := (g' i).ker ⧸ (g i).range.submoduleOf (g' i).ker

/-- Membership in the image of `F` viewed inside a submodule `K`. -/
private theorem mem_range_submoduleOf_iff {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (F : A →ₗ[R] B) (K : Submodule R B) (x : K) :
    x ∈ F.range.submoduleOf K ↔ ∃ y, F y = x := by
  simp [Submodule.submoduleOf]

/-- The map induced from degree `i` to degree `j` by the direct system. -/
public abbrev hMap (i j : ι) (h : i ≤ j) : hObj g g' i →ₗ[R] hObj g g' j :=
  Submodule.mapQ _ _ ((f' i j h).restrict fun x ↦ by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← LinearMap.comp_apply]
    simp +contextual [hg']) <| fun ⟨x, hx1⟩ hx2 ↦ by
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range, LinearMap.coe_restrict_apply] at hx2 ⊢
  obtain ⟨y, hy⟩ := hx2
  use f i j h y
  rw [← LinearMap.comp_apply, hg, ← hy, LinearMap.comp_apply]

/-- The natural inclusion map from homology in each degree to the homology of direct limits. -/
public abbrev hlift (i : ι) : hObj g g' i →ₗ[R] homologyLimit g hg g' hg' :=
  Submodule.mapQ _ _ ((Module.DirectLimit.of _ _ _ f' i).restrict fun x ↦ by simp +contextual)
  fun ⟨x, hx1⟩ hx2 ↦ by
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.mem_range, LinearMap.coe_restrict_apply] at hx2 ⊢
    obtain ⟨y, hy⟩ := hx2
    use (Module.DirectLimit.of R ι L f i) y
    simp [hy]

lemma hlift_hMap_apply (i j : ι) (h : i ≤ j) (x : hObj g g' i) :
    hlift g hg g' hg' j (hMap g hg g' hg' i j h x) = hlift g hg g' hg' i x := by
  induction x using Submodule.Quotient.induction_on with | H x =>
  simp only [Submodule.mapQ_apply, Submodule.Quotient.eq]
  simp [Submodule.submoduleOf]

/-- The induced map from the limit of homology to the homology of limits. -/
abbrev hMapToLimit :
    Module.DirectLimit (hObj g g') (hMap g hg g' hg') →ₗ[R] homologyLimit g hg g' hg' :=
  Module.DirectLimit.lift _ _ _ _ _ (hlift_hMap_apply g hg g' hg')

lemma hMapToLimit_surjective [Nonempty ι] [IsDirectedOrder ι]
    [DirectedSystem N fun x1 x2 x3 ↦ ⇑(l x1 x2 x3)] :
    Function.Surjective (hMapToLimit g hg g' hg') := fun x ↦ by
  induction x using Submodule.Quotient.induction_on with | H x =>
  obtain ⟨x, hx⟩ := x
  induction x using Module.DirectLimit.induction_on with | ih i x =>
  simp only [LinearMap.mem_ker, Module.DirectLimit.map_apply_of] at hx ⊢
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hx
  rw [← LinearMap.comp_apply, ← hg', LinearMap.comp_apply] at hj
  use Module.DirectLimit.of R ι _ _ _ (Submodule.Quotient.mk
    ⟨f' i j hij x, LinearMap.mem_ker.2 hj⟩)
  simp only [Module.DirectLimit.lift_of, Submodule.mapQ_apply, Submodule.Quotient.eq]
  simp [Submodule.submoduleOf]

theorem hMapToLimit_bijective [Nonempty ι] [IsDirectedOrder ι]
    [DirectedSystem M fun i j h ↦ ⇑(f' i j h)]
    [DirectedSystem N fun x1 x2 x3 ↦ ⇑(l x1 x2 x3)] :
    Function.Bijective (hMapToLimit g hg g' hg') := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, hMapToLimit_surjective g hg g' hg'⟩
  obtain ⟨i, xh, rfl⟩ := Module.DirectLimit.exists_of z
  induction xh using Submodule.Quotient.induction_on with | H x =>
  -- A homology class `[x]` at level `i` mapping to `0` means `of_i x` is a boundary in the colimit.
  simp only [Module.DirectLimit.lift_of, hlift, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero, mem_range_submoduleOf_iff, LinearMap.coe_restrict_apply] at hz
  obtain ⟨w, hw⟩ := hz
  obtain ⟨k, u, rfl⟩ := Module.DirectLimit.exists_of w
  rw [Module.DirectLimit.map_apply_of] at hw
  -- `hw : of_k (g k u) = of_i x`. Pick a common upper bound `j` of `i` and `k`.
  obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
  -- The cycle `f' x - g (f u)` becomes `0` in the colimit of `M`, hence at some level `j'`.
  have hm0 : Module.DirectLimit.of R ι M f' j (f' i j hij x - g j (f k j hkj u)) = 0 := by
    have e1 : g j (f k j hkj u) = f' k j hkj (g k u) := LinearMap.congr_fun (hg k j hkj) u
    rw [map_sub, e1, Module.DirectLimit.of_f, Module.DirectLimit.of_f, hw, sub_self]
  obtain ⟨j', hjj', hj'⟩ := Module.DirectLimit.of.zero_exact hm0
  rw [map_sub, sub_eq_zero] at hj'
  -- Then `[x]` already dies at level `j'`, so `of_i [x] = 0` in the colimit of homologies.
  suffices hMap g hg g' hg' i j' (hij.trans hjj') (Submodule.Quotient.mk x) = 0 by
    rw [← Module.DirectLimit.of_f (f := hMap g hg g' hg') (i := i) (j := j')
      (hij := hij.trans hjj') (x := Submodule.Quotient.mk x), this, map_zero]
  simp only [hMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_range_submoduleOf_iff]
  refine ⟨f j j' hjj' (f k j hkj u), ?_⟩
  rw [← LinearMap.comp_apply, hg, LinearMap.comp_apply, ← hj']
  exact DirectedSystem.map_map' f' hij hjj' x

/-- Homology intertwines with direct limits. -/
@[stacks 00DB "part 2"]
public def Module.DirectLimit.homologyColimitEquiv
    [Nonempty ι] [IsDirectedOrder ι]
    [DirectedSystem M fun i j h ↦ ⇑(f' i j h)]
    [DirectedSystem N fun x1 x2 x3 ↦ ⇑(l x1 x2 x3)] :
    Module.DirectLimit (hObj g g') (hMap g hg g' hg') ≃ₗ[R] homologyLimit g hg g' hg' :=
  LinearEquiv.ofBijective (hMapToLimit g hg g' hg') (hMapToLimit_bijective g hg g' hg')

end
