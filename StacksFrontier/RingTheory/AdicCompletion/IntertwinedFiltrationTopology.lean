module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltration
public import StacksFrontier.Topology.Algebra.AdicLimitTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Intertwined filtrations have the same completion, topologically

`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit` identifies the `I`-adic completion
`M ^∧_I` of an `A`-module `M` with the limit `lim_n P n` of a tower of `A`-modules carrying
compatible maps `π n : M → P n` whose kernels are intertwined with the `I`-adic filtration.  This
file upgrades that isomorphism of `A`-modules to a homeomorphism: the `I`-adic topology on
`M ^∧_I` is carried to the inverse-limit topology on `lim_n P n`, the topology induced from the
product of the *discrete* modules `P n`.

The two topologies are compared through
`Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology`, which turns an infimum of topologies
induced from discrete quotients into an `I`-adic topology as soon as the kernels of the quotient
maps and the powers of `I` are cofinal in one another.  Here the comparison is pulled back along
the isomorphism, so both filtrations live on `M ^∧_I`:

* the `n`-th kernel is `ker (M ^∧_I → P n)`, and `proj_adicCompletionEquivTowerLimit` computes
  that map as `M ^∧_I → M ⧸ I ^ n M → M ⧸ ker (π n) ↪ P n`, so an element of the kernel is one
  whose `n`-th component is represented by some `a ∈ ker (π n)`;
* `I ^ n M ^∧_I` lies in that kernel because it already lies in `ker (M ^∧_I → M ⧸ I ^ n M)`;
* conversely, with `a ∈ ker (π n) ⊆ I ^ (n - c) M` for `n ≥ c`, the `(n - c)`-th component of
  the element is the class of `a`, hence zero, which places it in `I ^ (n - c) M ^∧_I`.

The last step is where `I` is assumed finitely generated: it is Mathlib's
`AdicCompletion.pow_smul_top_eq_ker_eval`, the identification of `I ^ k M ^∧_I` with
`ker (M ^∧_I → M ⧸ I ^ k M)`, which is the only direction of the comparison needing more than
the definitions.  Over a Noetherian ring the hypothesis is automatic.

## Main definitions

* `Stacks.IntertwinedFiltration.towerLimit.limitTopology` — the inverse-limit topology on
  `lim_n P n`: every `P n` is discrete and the limit is a subspace of their product.
* `Stacks.IntertwinedFiltration.adicCompletionModuleLimitTopology` — the same construction for
  `M ^∧_I = lim_n M ⧸ I ^ n M`.

## Main results

* `Stacks.IntertwinedFiltration.limitTopology_eq_iInf_induced_proj` — the limit topology is the
  infimum of the topologies induced from the projections.
* `Stacks.IntertwinedFiltration.adicCompletionModuleLimitTopology_eq_adicModuleTopology` — the
  limit topology on `M ^∧_I` is its `I`-adic topology.
* `Stacks.IntertwinedFiltration.induced_limitTopology_adicCompletionEquivTowerLimit` — the limit
  topology pulls back along the comparison isomorphism to the `I`-adic topology on `M ^∧_I`.
* `Stacks.IntertwinedFiltration.isHomeomorph_adicCompletionEquivTowerLimit` and
  `Stacks.IntertwinedFiltration.isHomeomorph_adicCompletionEquivTowerLimit_limitTopology` —
  hence the comparison isomorphism is a homeomorphism, for the `I`-adic topology on `M ^∧_I`
  and equivalently for its limit topology.

## References

* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0GYS](https://stacks.math.columbia.edu/tag/0GYS)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.IntertwinedFiltration

variable {A : Type u} [CommRing A]

/-! ### The inverse-limit topology on the limit of a tower -/

section Tower

variable (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m)

/-- Induced from a product of discrete spaces is the infimum of the topologies induced from the
components. -/
private theorem induced_pi_bot_eq_iInf {X : Type*} {Q : ℕ → Type*} (f : ∀ n, X → Q n) :
    @TopologicalSpace.induced X (∀ n, Q n) (fun x n ↦ f n x)
        (@Pi.topologicalSpace ℕ Q fun _ ↦ ⊥) =
      ⨅ n, TopologicalSpace.induced (f n) ⊥ := by
  simp [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]

/-- The inverse-limit topology on `lim_n P n`: every term of the tower is discrete and the limit
carries the topology induced from their product. -/
@[instance_reducible]
def towerLimit.limitTopology : TopologicalSpace (towerLimit P T) :=
  @TopologicalSpace.induced (towerLimit P T) (∀ n, P n) (fun x ↦ x.1)
    (@Pi.topologicalSpace ℕ P (fun _ ↦ ⊥))

/-- The inverse-limit topology is the infimum of the topologies induced from the projections to
the discrete terms of the tower. -/
theorem limitTopology_eq_iInf_induced_proj :
    towerLimit.limitTopology P T =
      ⨅ n, TopologicalSpace.induced (fun x : towerLimit P T ↦ towerLimit.proj n x) ⊥ := by
  exact induced_pi_bot_eq_iInf fun n (x : towerLimit P T) ↦ towerLimit.proj n x

end Tower

/-! ### The limit topology on an adic completion -/

section Completion

variable {M : Type v} [AddCommGroup M] [Module A M] (I : Ideal A)

/-- The limit topology on `M ^∧_I = lim_n M ⧸ I ^ n M`: every quotient `M ⧸ I ^ n M` is discrete
and the completion carries the topology induced from their product. -/
@[instance_reducible]
def adicCompletionModuleLimitTopology : TopologicalSpace (AdicCompletion I M) :=
  @TopologicalSpace.induced (AdicCompletion I M)
    (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule A M)) (fun x ↦ x.1)
    (@Pi.topologicalSpace ℕ _ (fun _ ↦ ⊥))

/-- **The limit topology on `M ^∧_I` is its `I`-adic topology**, for `I` finitely generated.
The two filtrations of `M ^∧_I` at stake coincide outright: `I ^ n M ^∧_I` is the kernel of
`M ^∧_I → M ⧸ I ^ n M` by `AdicCompletion.pow_smul_top_eq_ker_eval`. -/
theorem adicCompletionModuleLimitTopology_eq_adicModuleTopology (hIfg : I.FG) :
    adicCompletionModuleLimitTopology (M := M) I =
      I.adicModuleTopology (AdicCompletion I M) := by
  have hpres : adicCompletionModuleLimitTopology (M := M) I =
      ⨅ n, TopologicalSpace.induced
        (fun x : AdicCompletion I M ↦ AdicCompletion.eval I M n x) ⊥ := by
    exact induced_pi_bot_eq_iInf fun n x ↦ AdicCompletion.eval I M n x
  rw [hpres]
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology I (AdicCompletion.eval I M)
    (fun i j hij ↦ ?_) (fun n ↦ ⟨n, AdicCompletion.pow_smul_top_le_ker_eval I n⟩)
    fun k ↦ ⟨k, (AdicCompletion.pow_smul_top_eq_ker_eval hIfg).ge⟩
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hIfg,
    ← AdicCompletion.pow_smul_top_eq_ker_eval hIfg]
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

end Completion

/-! ### The comparison isomorphism is a homeomorphism -/

section TowerOfMaps

variable {M : Type v} [AddCommGroup M] [Module A M]
  (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n)
  (I : Ideal A) (c : ℕ)
  (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
  (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (π n))
  (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
  (hrange : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
    LinearMap.range (T n k h) = LinearMap.range (π n))

/-- The `n`-th component of the comparison isomorphism `M ^∧_I ≅ lim_n P n` is the `n`-th
component of the completion, pushed to `M ⧸ ker (π n)` and injected into `P n`. -/
theorem proj_adicCompletionEquivTowerLimit (n : ℕ) (z : AdicCompletion I M) :
    towerLimit.proj n (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange z) =
      quotKerEmbed P π n (Submodule.factor (hker n) (z.val n)) :=
  rfl

/-- An element of `M ^∧_I` dies in `P n` exactly when its `n`-th component already dies in
`M ⧸ ker (π n)`, since `M ⧸ ker (π n) → P n` is injective. -/
theorem proj_adicCompletionEquivTowerLimit_eq_zero_iff (n : ℕ) (z : AdicCompletion I M) :
    towerLimit.proj n (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange z) = 0 ↔
      Submodule.factor (hker n) (z.val n) = 0 := by
  rw [proj_adicCompletionEquivTowerLimit]
  refine ⟨fun h ↦ quotKerEmbed_injective P π n ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [h, map_zero]

/-- **The comparison isomorphism of an intertwined filtration is a homeomorphism.**  The
inverse-limit topology on `lim_n P n` pulls back along
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimit` to the `I`-adic topology on
`M ^∧_I`. -/
theorem induced_limitTopology_adicCompletionEquivTowerLimit (hIfg : I.FG) :
    TopologicalSpace.induced
        (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange)
        (towerLimit.limitTopology P T) =
      I.adicModuleTopology (AdicCompletion I M) := by
  set e := adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange with he
  set g : ∀ n, AdicCompletion I M →ₗ[A] P n :=
    fun n ↦ (towerLimit.proj n).comp (e : AdicCompletion I M →ₗ[A] towerLimit P T) with hg
  have hzero (n : ℕ) (z : AdicCompletion I M) :
      g n z = 0 ↔ Submodule.factor (hker n) (z.val n) = 0 := by
    exact proj_adicCompletionEquivTowerLimit_eq_zero_iff P T π I c hπ hker hker' hrange n z
  have hmono : ∀ i j, i ≤ j → LinearMap.ker (g j) ≤ LinearMap.ker (g i) := by
    intro i j hij z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hc := towerLimit_compat (e z) i j hij
    change ((e z : ∀ k, P k)) j = 0 at hz
    change ((e z : ∀ k, P k)) i = 0
    rw [← hc, hz, map_zero]
  have hpow : ∀ n, ∃ k,
      I ^ k • (⊤ : Submodule A (AdicCompletion I M)) ≤ LinearMap.ker (g n) := by
    intro n
    refine ⟨n, fun z hz ↦ LinearMap.mem_ker.2 ((hzero n z).2 ?_)⟩
    have h0 : z.val n = 0 :=
      LinearMap.mem_ker.1 (AdicCompletion.pow_smul_top_le_ker_eval
        (I := I) (M := M) n hz)
    rw [h0, map_zero]
  have hcof : ∀ k, ∃ n,
      LinearMap.ker (g n) ≤ I ^ k • (⊤ : Submodule A (AdicCompletion I M)) := by
    intro k
    refine ⟨k + c, fun z hz ↦ ?_⟩
    have hfac := (hzero (k + c) z).1 (LinearMap.mem_ker.1 hz)
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
      (I ^ (k + c) • (⊤ : Submodule A M)) (z.val (k + c))
    rw [← ha, factor_quotient_mk] at hfac
    have hmem : a ∈ LinearMap.ker (π (k + c)) := (Submodule.Quotient.mk_eq_zero _).1 hfac
    have hak : a ∈ I ^ k • (⊤ : Submodule A M) := by
      have h := hker' (k + c) (Nat.le_add_left c k) hmem
      rwa [Nat.add_sub_cancel] at h
    have hzk : z.val k = 0 := by
      rw [← z.property (Nat.le_add_right k c), ← ha]
      exact (Submodule.Quotient.mk_eq_zero _).2 hak
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := M) (n := k) hIfg]
    exact LinearMap.mem_ker.2 hzk
  rw [← Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology I g hmono hpow hcof,
    limitTopology_eq_iInf_induced_proj, induced_iInf]
  exact congrArg _ (funext fun n ↦ induced_compose)

/-- **The comparison isomorphism of an intertwined filtration is a homeomorphism**, as a
statement about the map: it is continuous, open and bijective from `M ^∧_I` with its `I`-adic
topology to `lim_n P n` with its inverse-limit topology. -/
theorem isHomeomorph_adicCompletionEquivTowerLimit (hIfg : I.FG) :
    @IsHomeomorph (AdicCompletion I M) (towerLimit P T)
      (I.adicModuleTopology (AdicCompletion I M)) (towerLimit.limitTopology P T)
      (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange) := by
  let : TopologicalSpace (AdicCompletion I M) := I.adicModuleTopology (AdicCompletion I M)
  let : TopologicalSpace (towerLimit P T) := towerLimit.limitTopology P T
  refine isHomeomorph_iff_isEmbedding_surjective.2 ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · exact (induced_limitTopology_adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange
      hIfg).symm
  · exact (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange).injective
  · exact (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange).surjective

/-- **The comparison isomorphism of an intertwined filtration is a homeomorphism for the limit
topologies.**  This is the statement with the limit topology on `M ^∧_I = lim_n M ⧸ I ^ n M`
rather than its `I`-adic topology; the two agree, by
`adicCompletionModuleLimitTopology_eq_adicModuleTopology`. -/
@[ega "III 4.1.7.21" "more general"]
theorem isHomeomorph_adicCompletionEquivTowerLimit_limitTopology (hIfg : I.FG) :
    @IsHomeomorph (AdicCompletion I M) (towerLimit P T)
      (adicCompletionModuleLimitTopology I) (towerLimit.limitTopology P T)
      (adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange) := by
  rw [adicCompletionModuleLimitTopology_eq_adicModuleTopology I hIfg]
  exact isHomeomorph_adicCompletionEquivTowerLimit P T π I c hπ hker hker' hrange hIfg

end TowerOfMaps

end Stacks.IntertwinedFiltration

end
