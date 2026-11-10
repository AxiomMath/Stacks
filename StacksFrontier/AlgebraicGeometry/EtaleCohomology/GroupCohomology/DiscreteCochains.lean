module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Separation.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally constant cochains of a profinite group on a discrete module

For a topological group `G` acting on an abelian group `M` the continuous cochains are the
locally constant ones, `M` carrying the discrete topology. This file defines the differentials of
such cochains in degrees zero and one and the vanishing statements for locally constant cocycles
in degrees one and two. On a profinite group a locally constant function is *uniformly* locally
constant, i.e. invariant under right translation by an open subgroup.

## Main definitions

* `Stacks.GroupCohomology.dZero`, `Stacks.GroupCohomology.dOne`: the differentials
  `M → (G → M)` and `(G → M) → (G × G → M)` of the inhomogeneous cochain complex, written out in
  the conventions of Mathlib's `groupCohomology.IsCocycle₁` and `groupCohomology.IsCocycle₂`.
* `Stacks.GroupCohomology.VanishesOne`, `Stacks.GroupCohomology.VanishesTwo`: the statements
  "every locally constant `1`-cocycle is a coboundary" and "every locally constant `2`-cocycle is
  the coboundary of a locally constant `1`-cochain", which is the cochain-level form of
  `H ¹(G, M) = 0` and `H ²(G, M) = 0`.
* `Stacks.GroupCohomology.HasOpenStabilizers`: every stabilizer of the action on `M` is open.

## Main results

* `Stacks.GroupCohomology.exists_openSubgroup_forall_mul_right_eq`: **a locally constant function
  on a profinite group is right invariant under an open subgroup.**
* `Stacks.GroupCohomology.exists_openSubgroup_forall_mul_right_eq₂`: the same for a function of
  two variables.
* `Stacks.GroupCohomology.isCocycle₂_dOne`: the coboundary of a `1`-cochain is a `2`-cocycle.
* `Stacks.GroupCohomology.isLocallyConstant_dOne`: the coboundary of a locally constant
  `1`-cochain is locally constant, the module having open stabilizers.

## References

* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the continuous
  cohomology whose cochains these are.
-/

@[expose] public section

open groupCohomology

universe u v

namespace Stacks.GroupCohomology

/-! ### Uniform local constancy on a profinite group -/

section Uniform

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **A locally constant function on a profinite group is right invariant under an open
subgroup.** -/
theorem exists_openSubgroup_forall_mul_right_eq [CompactSpace H] [TotallyDisconnectedSpace H]
    {B : Type v} {f : H → B} (hf : IsLocallyConstant f) :
    ∃ N : OpenSubgroup H, ∀ x n : H, n ∈ N → f (x * n) = f x := by
  have : T2Space H := IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  have key : ∀ x : H, ∃ N : OpenNormalSubgroup H, ∀ n ∈ N, f (x * n) = f x := by
    intro x
    have hopen : IsOpen ((fun u : H ↦ x * u) ⁻¹' (f ⁻¹' {f x})) :=
      (hf {f x}).preimage (by fun_prop)
    have hmem : (1 : H) ∈ (fun u : H ↦ x * u) ⁻¹' (f ⁻¹' {f x}) := by simp
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hmem
    exact ⟨N, fun n hn ↦ by simpa using hN hn⟩
  choose N hN using key
  set V : H → Set H := fun x ↦ (fun y : H ↦ x⁻¹ * y) ⁻¹' ((N x).toSubgroup : Set H) with hV
  have hVopen : ∀ x, IsOpen (V x) := fun x ↦ (N x).isOpen'.preimage (by fun_prop)
  have hVmem : ∀ x, x ∈ V x := fun x ↦ by simp [hV]
  obtain ⟨t, ht⟩ := (isCompact_univ (X := H)).elim_finite_subcover V hVopen
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hVmem x⟩)
  refine ⟨t.inf fun x ↦ (N x).toOpenSubgroup, fun y n hn ↦ ?_⟩
  obtain ⟨x, hxt, hxy⟩ := by simpa using ht (Set.mem_univ y)
  have hmem : x⁻¹ * y ∈ (N x).toSubgroup := hxy
  have hnx : n ∈ (N x).toSubgroup :=
    (Finset.inf_le hxt : (t.inf fun x ↦ (N x).toOpenSubgroup) ≤ (N x).toOpenSubgroup) hn
  have h1 : f (x * ((x⁻¹ * y) * n)) = f x := hN x _ (mul_mem hmem hnx)
  have h2 : f (x * (x⁻¹ * y)) = f x := hN x _ hmem
  rw [show y * n = x * ((x⁻¹ * y) * n) by group, h1, ← h2]
  group

/-- **A locally constant function of two variables on a profinite group is right invariant under
an open subgroup in each variable.** -/
theorem exists_openSubgroup_forall_mul_right_eq₂ [CompactSpace H] [TotallyDisconnectedSpace H]
    {B : Type v} {f : H × H → B} (hf : IsLocallyConstant f) :
    ∃ N : OpenSubgroup H, ∀ x y n m : H, n ∈ N → m ∈ N → f (x * n, y * m) = f (x, y) := by
  obtain ⟨M, hM⟩ := exists_openSubgroup_forall_mul_right_eq (H := H × H) hf
  have hinl : Continuous (MonoidHom.inl H H) := by
    change Continuous fun h : H ↦ ((h, 1) : H × H)
    fun_prop
  have hinr : Continuous (MonoidHom.inr H H) := by
    change Continuous fun h : H ↦ ((1, h) : H × H)
    fun_prop
  refine ⟨M.comap (MonoidHom.inl H H) hinl ⊓
    M.comap (MonoidHom.inr H H) hinr, fun x y n m hn hm ↦ ?_⟩
  have hn' : ((n, 1) : H × H) ∈ M := hn.1
  have hm' : ((1, m) : H × H) ∈ M := hm.2
  simpa using hM (x, y) ((n, 1) * (1, m)) (mul_mem hn' hm')

end Uniform

/-! ### Cochains in degrees zero, one and two -/

section Cochains

variable {G : Type u} [Group G] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

/-- The differential from `0`-cochains to `1`-cochains: `x ↦ (g ↦ g • x - x)`. This is the
coboundary appearing in `groupCohomology.IsCoboundary₁`. -/
def dZero (x : M) : G → M := fun g ↦ g • x - x

/-- The differential from `1`-cochains to `2`-cochains:
`x ↦ ((g₁, g₂) ↦ g₁ • x g₂ - x (g₁ * g₂) + x g₁)`. This is the coboundary appearing in
`groupCohomology.IsCoboundary₂`. -/
def dOne (x : G → M) : G × G → M := fun p ↦ p.1 • x p.2 - x (p.1 * p.2) + x p.1

/-- The value of `dZero x` at `g` is `g • x - x`. -/
@[simp] lemma dZero_apply (x : M) (g : G) : dZero x g = g • x - x := rfl

/-- The value of `dOne x` at `(g₁, g₂)` is `g₁ • x g₂ - x (g₁ * g₂) + x g₁`. -/
@[simp] lemma dOne_apply (x : G → M) (g₁ g₂ : G) :
    dOne x (g₁, g₂) = g₁ • x g₂ - x (g₁ * g₂) + x g₁ := rfl

/-- A `1`-cochain is a coboundary exactly when it is `dZero x` for some `x`. -/
lemma isCoboundary₁_iff {c : G → M} : IsCoboundary₁ c ↔ ∃ x : M, dZero x = c :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x, funext hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, fun g ↦ congrFun hx g⟩⟩

/-- A `2`-cochain is a coboundary exactly when it is `dOne x` for some `1`-cochain `x`. -/
lemma isCoboundary₂_iff {f : G × G → M} : IsCoboundary₂ f ↔ ∃ x : G → M, dOne x = f :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x, funext fun p ↦ hx p.1 p.2⟩,
    fun ⟨x, hx⟩ ↦ ⟨x, fun g₁ g₂ ↦ congrFun hx (g₁, g₂)⟩⟩

/-- The coboundary of a `0`-cochain is a `1`-cocycle. -/
lemma isCocycle₁_dZero (x : M) : IsCocycle₁ (dZero (G := G) x) := by
  intro g h
  simp only [dZero_apply, mul_smul, smul_sub]
  abel

/-- **The coboundary of a `1`-cochain is a `2`-cocycle.** -/
lemma isCocycle₂_dOne (x : G → M) : IsCocycle₂ (dOne x) := by
  intro g h j
  simp only [dOne_apply, mul_smul, smul_sub, smul_add, mul_assoc]
  abel

/-- The image of a `1`-cocycle under an equivariant additive map is a `1`-cocycle. -/
lemma isCocycle₁_comp {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) {c : G → M} (hc : IsCocycle₁ c) :
    IsCocycle₁ (φ ∘ c) := by
  intro g h
  simp only [Function.comp_apply, hc g h, map_add, hφ]

/-- The image of a `2`-cocycle under an equivariant additive map is a `2`-cocycle. -/
lemma isCocycle₂_comp {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) {f : G × G → M} (hf : IsCocycle₂ f) :
    IsCocycle₂ (φ ∘ f) := by
  intro g h j
  simp only [Function.comp_apply]
  simpa only [map_add, hφ] using congrArg φ (hf g h j)

/-- An equivariant additive map commutes with `dZero`. -/
lemma dZero_map {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (x : M) :
    φ ∘ dZero (G := G) x = dZero (φ x) := by
  funext g
  simp [hφ]

/-- An equivariant additive map commutes with `dOne`. -/
lemma dOne_map {N : Type*} [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (x : G → M) :
    φ ∘ dOne x = dOne (fun g ↦ φ (x g)) := by
  funext p
  simp only [Function.comp_apply, dOne, map_add, map_sub, hφ]

end Cochains

/-! ### The cochain-level vanishing statements -/

section Vanishes

variable (G : Type u) [Group G] [TopologicalSpace G] (M : Type v) [AddCommGroup M]
  [DistribMulAction G M]

/-- **The discreteness condition on a module**: every stabiliser is open. For a module carrying
the discrete topology this is exactly continuity of the action. -/
@[sga "3 VIIB 2.5" "special case", sga "3 X 1.2"]
def HasOpenStabilizers : Prop := ∀ m : M, IsOpen {g : G | g • m = m}

variable {G M}

/-- Locally, `f z • x z` is `f z • x z₀`, which is constant when stabilizers are open. -/
private theorem isLocallyConstant_smul_comp_aux [IsTopologicalGroup G]
    (h : HasOpenStabilizers G M) {X : Type*} [TopologicalSpace X] {f : X → G}
    (hf : Continuous f) {x : X → M} (hx : IsLocallyConstant x) :
    IsLocallyConstant fun z ↦ f z • x z := by
  rw [IsLocallyConstant.iff_exists_open]
  intro z₀
  refine ⟨{z | x z = x z₀} ∩ f ⁻¹' ((fun g : G ↦ (f z₀)⁻¹ * g) ⁻¹' {g : G | g • x z₀ = x z₀}),
    (hx {x z₀}).inter (((h (x z₀)).preimage (by fun_prop)).preimage hf), ⟨rfl, by simp⟩,
    fun z hz ↦ ?_⟩
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Set.mem_ofPred_eq] at hz1
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz2
  rw [hz1]
  calc f z • x z₀ = (f z₀ * ((f z₀)⁻¹ * f z)) • x z₀ := by rw [mul_inv_cancel_left]
    _ = f z₀ • (((f z₀)⁻¹ * f z) • x z₀) := mul_smul _ _ _
    _ = f z₀ • x z₀ := by rw [hz2]

/-- The orbit map of an element of a module with open stabilizers is locally constant. -/
theorem HasOpenStabilizers.isLocallyConstant_smul [IsTopologicalGroup G]
    (h : HasOpenStabilizers G M) (m : M) : IsLocallyConstant fun g : G ↦ g • m := by
  simpa using isLocallyConstant_smul_comp_aux h continuous_id (IsLocallyConstant.const m)

/-- A product of a continuous function into the group and a locally constant function into a
module with open stabilizers is locally constant. -/
theorem HasOpenStabilizers.isLocallyConstant_smul_comp [IsTopologicalGroup G]
    (h : HasOpenStabilizers G M) {X : Type*} [TopologicalSpace X] {f : X → G}
    (hf : Continuous f) {x : X → M} (hx : IsLocallyConstant x) :
    IsLocallyConstant fun z ↦ f z • x z :=
  isLocallyConstant_smul_comp_aux h hf hx

/-- The coboundary of a locally constant `0`-cochain is locally constant. -/
theorem isLocallyConstant_dZero [IsTopologicalGroup G] (h : HasOpenStabilizers G M) (m : M) :
    IsLocallyConstant (dZero (G := G) m) :=
  (h.isLocallyConstant_smul m).comp₂ (IsLocallyConstant.const m) (· - ·)

/-- The coboundary of a locally constant `1`-cochain is locally constant. -/
theorem isLocallyConstant_dOne [IsTopologicalGroup G] (h : HasOpenStabilizers G M)
    {x : G → M} (hx : IsLocallyConstant x) : IsLocallyConstant (dOne x) := by
  have h1 : IsLocallyConstant fun p : G × G ↦ p.1 • x p.2 :=
    h.isLocallyConstant_smul_comp continuous_fst (hx.comp_continuous continuous_snd)
  have h2 : IsLocallyConstant fun p : G × G ↦ x (p.1 * p.2) :=
    hx.comp_continuous (continuous_fst.mul continuous_snd)
  have h3 : IsLocallyConstant fun p : G × G ↦ x p.1 := hx.comp_continuous continuous_fst
  exact (h1.comp₂ h2 (· - ·)).comp₂ h3 (· + ·)

variable (G M)

/-- **`H ¹(G, M) = 0` at the level of cochains**: every locally constant `1`-cocycle of `G` with
values in the discrete module `M` is a coboundary. -/
def VanishesOne : Prop :=
  ∀ c : G → M, IsLocallyConstant c → IsCocycle₁ c → ∃ x : M, dZero x = c

/-- **`H ²(G, M) = 0` at the level of cochains**: every locally constant `2`-cocycle of `G` with
values in the discrete module `M` is the coboundary of a locally constant `1`-cochain. -/
def VanishesTwo : Prop :=
  ∀ f : G × G → M, IsLocallyConstant f → IsCocycle₂ f →
    ∃ x : G → M, IsLocallyConstant x ∧ dOne x = f

end Vanishes

end Stacks.GroupCohomology

end
