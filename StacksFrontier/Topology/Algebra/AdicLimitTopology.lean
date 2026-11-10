module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The limit topology on the inverse limit of a tower of modules

Let `R` be a commutative ring, `I ⊆ R` an ideal and `… → D₂ → D₁ → D₀` a tower of
`R`-modules.  Its inverse limit `M = lim Dₙ` carries the *limit topology*: the topology induced
from the product of the discrete `Dₙ`.  This file compares that topology with the `I`-adic
topology on `M`.

Both comparisons reduce to a statement about the descending filtration of `M` by the kernels
`Fⁿ = Ker(M → Dₙ)`.  The `I`-adic topology is coarser than the limit topology as soon as some
power of `I` annihilates each `Dₙ`, and finer as soon as each `Fⁿ` contains a power of `I`.
The second inclusion is the substantial one; `proj_ker_le_pow_smul` derives it from a
*successive approximation* hypothesis: a fixed finite family `a : ι → I` such that every
element of `Fⁿ⁺¹` agrees modulo `Fⁿ⁺²` with an `a`-combination of elements of `Fⁿ`.  The
inverse limit is complete for the limit topology, so the approximations can be summed, which
replaces the appeal to the open mapping lemma in the source of [Stacks, Tag 0GYS].

## Main definitions

* `Stacks.AdicLimit.towerLimit`: the inverse limit of a tower of modules, as the submodule of
  compatible sequences.
* `Stacks.AdicLimit.towerLimit.proj`: the projection to a term of the tower.
* `Stacks.AdicLimit.towerLimit.limitTopology`: the inverse-limit topology.

## Main results

* `Stacks.AdicLimit.exists_smul_sum`: successive approximations can be summed in the inverse
  limit, producing an exact `a`-combination.
* `Stacks.AdicLimit.proj_ker_le_pow_smul`: consequently `Ker(M → D_{c+k}) ⊆ IᵏM`.
* `Stacks.AdicLimit.pow_smul_le_proj_ker`: conversely `I^(n+1)M ⊆ Ker(M → Dₙ)` when
  `I^(n+1)D_{n+1} ⊆ Ker(D_{n+1} → Dₙ)`.
* `Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology`: a topology given as an infimum of
  topologies induced from discrete quotients is the `I`-adic topology as soon as the kernels and
  the powers of `I` interleave.
* `Stacks.AdicLimit.limitTopology_eq_iInf_induced_proj`: the limit topology is such an infimum.

## References

* [Stacks Project, Tag 0GYS](https://stacks.math.columbia.edu/tag/0GYS)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.AdicLimit

variable {R : Type u} [CommRing R]

/-- The inverse limit of a tower of modules `… → D₁ → D₀`, as the submodule of compatible
sequences. -/
def towerLimit (D : ℕ → Type v) [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (f : ∀ n, D (n + 1) →ₗ[R] D n) : Submodule R (∀ n, D n) where
  carrier := {x | ∀ n, f n (x (n + 1)) = x n}
  zero_mem' n := by simp
  add_mem' hx hy n := by simp [hx n, hy n]
  smul_mem' a x hx n := by simp [hx n]

/-- The projection from the inverse limit to a term of the tower. -/
def towerLimit.proj (D : ℕ → Type v) [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (f : ∀ n, D (n + 1) →ₗ[R] D n) (n : ℕ) : towerLimit D f →ₗ[R] D n :=
  LinearMap.comp (LinearMap.proj n) (towerLimit D f).subtype

/-- The inverse-limit topology: every term of the tower is discrete and the limit carries the
topology induced from their product. -/
@[instance_reducible]
def towerLimit.limitTopology (D : ℕ → Type v) [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (f : ∀ n, D (n + 1) →ₗ[R] D n) : TopologicalSpace (towerLimit D f) :=
  @TopologicalSpace.induced (towerLimit D f) (∀ n, D n) (fun x ↦ x.1)
    (@Pi.topologicalSpace ℕ D (fun _ ↦ ⊥))

variable {D : ℕ → Type v} [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
  (f : ∀ n, D (n + 1) →ₗ[R] D n)

/-- The kernels of the projections out of the inverse limit are antitone. -/
theorem towerLimit_proj_ker_antitone (i j : ℕ) (hij : i ≤ j) :
    LinearMap.ker (towerLimit.proj D f j) ≤ LinearMap.ker (towerLimit.proj D f i) := by
  intro x hx
  refine LinearMap.mem_ker.mpr ?_
  change x.1 i = 0
  change x.1 j = 0 at hx
  induction j, hij using Nat.le_induction with
  | base => exact hx
  | succ j hij ih =>
    refine ih ?_
    rw [← x.2 j, hx, map_zero]

/-- If `I^(n+1)` kills `Dₙ₊₁` modulo the kernel of the transition map, then `I^(n+1)M` lies in
the kernel of the projection to `Dₙ`. -/
theorem pow_smul_le_proj_ker (I : Ideal R)
    (hkill : ∀ n, (I ^ (n + 1) • (⊤ : Submodule R (D (n + 1))) : Submodule R (D (n + 1))) ≤
      LinearMap.ker (f n)) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (towerLimit D f)) ≤
      LinearMap.ker (towerLimit.proj D f n) := by
  refine Submodule.smul_le.mpr fun a ha x _ ↦ LinearMap.mem_ker.mpr ?_
  change a • x.1 n = 0
  rw [← x.2 n, ← map_smul]
  exact LinearMap.mem_ker.mp (Submodule.smul_le.mp (hkill n) a ha (x.1 (n + 1)) (by simp))

/-- A sequence of elements of the inverse limit, each killed by one further projection, can be
summed: the partial sums are compatible, hence define an element of the limit. -/
theorem exists_mem_towerLimit_sum (a : ℕ → towerLimit D f)
    (ha : ∀ i, a i ∈ LinearMap.ker (towerLimit.proj D f i)) :
    ∃ s : towerLimit D f, ∀ j, s.1 j = ∑ i ∈ Finset.range (j + 1), (a i).1 j := by
  refine ⟨⟨fun j ↦ ∑ i ∈ Finset.range (j + 1), (a i).1 j, fun j ↦ ?_⟩, fun _ ↦ rfl⟩
  change f j (∑ i ∈ Finset.range (j + 1 + 1), (a i).1 (j + 1)) =
    ∑ i ∈ Finset.range (j + 1), (a i).1 j
  rw [map_sum]
  simp only [(a _).2 j]
  rw [Finset.sum_range_succ]
  have hz : (a (j + 1)).1 j = 0 :=
    towerLimit_proj_ker_antitone f j (j + 1) (Nat.le_succ j) (ha (j + 1))
  rw [hz, add_zero]

/-- Completeness of the inverse limit upgrades successive approximations by a fixed finite
family of scalars to an exact decomposition. -/
theorem exists_smul_sum {ι : Type w} [Fintype ι] (a : ι → R) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : towerLimit D f,
      x ∈ LinearMap.ker (towerLimit.proj D f (n + 1)) →
      ∃ y : ι → towerLimit D f,
        (∀ i, y i ∈ LinearMap.ker (towerLimit.proj D f n)) ∧
        x - ∑ i, a i • y i ∈ LinearMap.ker (towerLimit.proj D f (n + 2)))
    (n : ℕ) (hn : c ≤ n) (x : towerLimit D f)
    (hx : x ∈ LinearMap.ker (towerLimit.proj D f (n + 1))) :
    ∃ y : ι → towerLimit D f,
      (∀ i, y i ∈ LinearMap.ker (towerLimit.proj D f n)) ∧ x = ∑ i, a i • y i := by
  classical
  let K := fun j ↦ LinearMap.ker (towerLimit.proj D f j)
  let chooseTerms : ∀ j, K (n + j + 1) → (ι → towerLimit D f) :=
    fun j z ↦ (happrox (n + j) (hn.trans (Nat.le_add_right n j)) z.1 z.2).choose
  have hterms (j : ℕ) (z : K (n + j + 1)) :
      (∀ i, chooseTerms j z i ∈ K (n + j)) ∧
      z.1 - ∑ i, a i • chooseTerms j z i ∈ K (n + j + 2) :=
    (happrox (n + j) (hn.trans (Nat.le_add_right n j)) z.1 z.2).choose_spec
  let residual : ∀ j, K (n + j + 1) := fun j ↦ Nat.rec
    (motive := fun j ↦ K (n + j + 1)) ⟨x, hx⟩
    (fun j z ↦ ⟨z.1 - ∑ i, a i • chooseTerms j z i, (hterms j z).2⟩) j
  let b : ℕ → ι → towerLimit D f := fun j ↦ chooseTerms j (residual j)
  have hb (j : ℕ) (i : ι) : b j i ∈ K (n + j) := (hterms j (residual j)).1 i
  have hres (j : ℕ) : (residual j).1 = x - ∑ k ∈ Finset.range j, ∑ i, a i • b k i := by
    induction j with
    | zero => simp [residual]
    | succ j ih =>
      change (residual j).1 - ∑ i, a i • b j i = _
      rw [ih, Finset.sum_range_succ, sub_sub]
  have hs (i : ι) := exists_mem_towerLimit_sum f (fun j ↦ b j i)
    (fun j ↦ towerLimit_proj_ker_antitone f j (n + j) (Nat.le_add_left j n) (hb j i))
  choose s hs using hs
  refine ⟨s, fun i ↦ ?_, ?_⟩
  · change (s i).1 n = 0
    rw [hs]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    exact towerLimit_proj_ker_antitone f n (n + j) (Nat.le_add_right n j) (hb j i)
  · refine Subtype.ext (funext fun j ↦ ?_)
    have hz : (residual (j + 1)).1.1 j = 0 :=
      towerLimit_proj_ker_antitone f j (n + (j + 1) + 1) (by omega) (residual (j + 1)).2
    rw [hres] at hz
    have hz' : x.1 j = ∑ k ∈ Finset.range (j + 1), ∑ i, a i • (b k i).1 j := by
      simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
        Finset.sum_apply, Pi.smul_apply, sub_eq_zero] using hz
    change x.1 j = (∑ i, a i • s i).1 j
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    simp_rw [hs, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact hz'

/-- Successive approximation by a fixed finite family of elements of `I` places the kernel of
the projection to `D_{c+k}` inside `IᵏM`. -/
theorem proj_ker_le_pow_smul (I : Ideal R) {ι : Type w} [Fintype ι] (a : ι → R)
    (ha : ∀ i, a i ∈ I) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : towerLimit D f,
      x ∈ LinearMap.ker (towerLimit.proj D f (n + 1)) →
      ∃ y : ι → towerLimit D f,
        (∀ i, y i ∈ LinearMap.ker (towerLimit.proj D f n)) ∧
        x - ∑ i, a i • y i ∈ LinearMap.ker (towerLimit.proj D f (n + 2)))
    (k : ℕ) :
    LinearMap.ker (towerLimit.proj D f (c + k)) ≤
      I ^ k • (⊤ : Submodule R (towerLimit D f)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_smul_sum f a c happrox (c + k) (Nat.le_add_right c k) x hx
    rw [pow_succ', ← Ideal.smul_eq_mul, Submodule.smul_assoc]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (ha i) (ih (hy i))

/-- The limit topology is the infimum of the topologies induced from the discrete terms of the
tower. -/
theorem limitTopology_eq_iInf_induced_proj :
    towerLimit.limitTopology D f =
      ⨅ n, TopologicalSpace.induced (fun x ↦ towerLimit.proj D f n x) ⊥ := by
  simp [towerLimit.limitTopology, Pi.topologicalSpace, towerLimit.proj, induced_iInf,
    induced_compose, Function.comp_def]

/-- A topology presented as an infimum of topologies induced from discrete quotients is the
`I`-adic topology as soon as the kernels of the quotient maps and the powers of `I` interleave
cofinally. -/
theorem iInf_induced_eq_adicModuleTopology {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
    (g : ∀ n, M →ₗ[R] N n)
    (hmono : ∀ i j, i ≤ j → (g j).ker ≤ (g i).ker)
    (hpow : ∀ n, ∃ k, I ^ k • (⊤ : Submodule R M) ≤ (g n).ker)
    (hker : ∀ k, ∃ n, (g n).ker ≤ I ^ k • (⊤ : Submodule R M)) :
    (⨅ n, TopologicalSpace.induced (fun x : M ↦ g n x) ⊥) = I.adicModuleTopology M := by
  classical
  let T₁ : TopologicalSpace M := ⨅ n, TopologicalSpace.induced (fun x : M ↦ g n x) ⊥
  let T₂ : TopologicalSpace M := I.adicModuleTopology M
  have hker_nhds (n : ℕ) (y : N n) :
      @nhds (N n) (⊥ : TopologicalSpace (N n)) y = pure y := by
    let : TopologicalSpace (N n) := ⊥
    let : DiscreteTopology (N n) := ⟨rfl⟩
    exact congrFun (nhds_discrete (N n)) y
  have h₁basis (x : M) : (@nhds M T₁ x).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (fun y : M ↦ x + y) '' ((g n).ker : Set M)) := by
    have hcoset (n : ℕ) : ((fun y : M ↦ g n y) ⁻¹' {g n x}) =
        (fun y : M ↦ x + y) '' ((g n).ker : Set M) := by
      ext y
      constructor
      · intro hy
        change g n y = g n x at hy
        exact ⟨y - x, by simp [hy], by simp⟩
      · rintro ⟨z, hz, rfl⟩
        simp [LinearMap.mem_ker.mp hz]
    have hfilter : @nhds M T₁ x = ⨅ n, Filter.principal
        ((fun y : M ↦ x + y) '' ((g n).ker : Set M)) := by
      change @nhds M (⨅ n, TopologicalSpace.induced (fun y : M ↦ g n y) ⊥) x = _
      rw [nhds_iInf]
      refine congrArg _ (funext fun n ↦ ?_)
      let : TopologicalSpace (N n) := ⊥
      rw [nhds_induced, hker_nhds n (g n x), Filter.comap_pure, hcoset]
    rw [hfilter]
    exact Filter.hasBasis_iInf_principal fun i j ↦
      ⟨max i j, Set.image_mono (hmono i (max i j) (le_max_left _ _)),
        Set.image_mono (hmono j (max i j) (le_max_right _ _))⟩
  let : TopologicalSpace R := I.adicTopology
  let b : ModuleFilterBasis R M := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  have h₂basis (x : M) : (@nhds M T₂ x).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (fun y : M ↦ x + y) ''
        ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
    have hb := b.toAddGroupFilterBasis.nhds_hasBasis x
    change (@nhds M (I.adicModuleTopology M) x).HasBasis _ _
    refine hb.to_hasBasis ?_ ?_
    · intro U hU
      change (∃ n, U = ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) at hU
      obtain ⟨n, rfl⟩ := hU
      exact ⟨n, trivial, Set.Subset.rfl⟩
    · intro n _
      exact ⟨((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M), ⟨n, rfl⟩, Set.Subset.rfl⟩
  refine TopologicalSpace.ext_nhds fun x ↦ (h₁basis x).ext (h₂basis x) ?_ ?_
  · intro n _
    obtain ⟨k, hk⟩ := hpow n
    exact ⟨k, trivial, Set.image_mono hk⟩
  · intro k _
    obtain ⟨n, hn⟩ := hker k
    exact ⟨n, trivial, Set.image_mono hn⟩

end Stacks.AdicLimit

end
