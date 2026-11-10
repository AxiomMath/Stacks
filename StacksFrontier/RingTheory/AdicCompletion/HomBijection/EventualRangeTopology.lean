module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.RingTheory.AdicCompletion.IntertwinedFiltrationEventualRange

/-!
# The eventual-range comparison: components, topology and complete modules

For a tower of maps `π n : M → P n` satisfying the per-`n` range condition, the comparison
`M^∧_I ≃ₗ[A] lim_n P n` of
`Stacks.IntertwinedFiltration.adicCompletionEquivTowerLimitOfEventualRange` is induced by the
system of maps `M ⧸ Iⁿ M ⟶ P n`, it is a homeomorphism for the limit topologies, and for `M`
`I`-adically complete `M` itself maps isomorphically onto `lim_n P n`.

## Main results

* `Stacks.IntertwinedFiltration.C1573.adicCompletionEquivTowerLimitOfEventualRange_apply` — the
  comparison is the map induced by the system of maps `M ⧸ Iⁿ M ⟶ P n`.
* `Stacks.IntertwinedFiltration.C1573.isHomeomorph_adicCompletionEquivTowerLimitOfEventualRange` —
  it is a homeomorphism for the limit topologies.
* `Stacks.IntertwinedFiltration.C1573.bijective_towerLimitLift_of_isAdicComplete` — for `M`
  `I`-adically complete, `M ⟶ lim_n P n` is bijective.
-/

@[expose] public section

namespace Stacks.IntertwinedFiltration.C1573

open Stacks.IntertwinedFiltration

variable {A : Type*} [CommRing A]

section TowerOfMaps

variable {M : Type*} [AddCommGroup M] [Module A M]
  (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n)

section Components

variable (I : Ideal A) (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (π n))

/-- The map `M ⧸ Iⁿ M ⟶ P n` induced by `π n`. -/
public def adicQuotientMap (n : ℕ) : M ⧸ (I ^ n • ⊤ : Submodule A M) →ₗ[A] P n :=
  (I ^ n • ⊤ : Submodule A M).liftQ (π n) (hker n)

/-- The map `M ⧸ Iⁿ M ⟶ P n` sends the class of `x` to `π n x`. -/
@[simp]
public theorem adicQuotientMap_mk (n : ℕ) (x : M) :
    adicQuotientMap P π I hker n (Submodule.Quotient.mk x) = π n x :=
  rfl

variable (c : ℕ) (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
  (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
  (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n))

/-- **The comparison is defined by the system of maps `M ⧸ Iⁿ M ⟶ P n`**: the `n`-th component
of the image of `w ∈ M^∧_I` is the image of the `n`-th component of `w`. -/
public theorem adicCompletionEquivTowerLimitOfEventualRange_apply (w : AdicCompletion I M)
    (n : ℕ) :
    ((adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange w :
      towerLimit P T) : ∀ k, P k) n = adicQuotientMap P π I hker n (w.val n) := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (w.val n)
  change quotKerEmbed P π n (Submodule.factor (hker n) (w.val n)) = _
  rw [← hm]
  rfl

/-- The `n`-th component of the image of `x ∈ M` is `π n x`. -/
public theorem adicCompletionEquivTowerLimitOfEventualRange_of (x : M) (n : ℕ) :
    ((adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange
      (AdicCompletion.of I M x) : towerLimit P T) : ∀ k, P k) n = π n x :=
  adicCompletionEquivTowerLimitOfEventualRange_apply P T π I hker c hπ hker' hrange _ n

/-- The `n`-th component of the inverse comparison depends only on the component of level
`n + c` of its argument. -/
public theorem adicCompletionEquivTowerLimitOfEventualRange_symm_val_eq (x x' : towerLimit P T)
    (n : ℕ) (h : (x : ∀ k, P k) (n + c) = (x' : ∀ k, P k) (n + c)) :
    ((adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange).symm x).val n =
      ((adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange).symm
        x').val n := by
  set e := adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange
  set w := e.symm x
  set w' := e.symm x'
  have hw : ((e w : towerLimit P T) : ∀ k, P k) (n + c) =
      ((e w' : towerLimit P T) : ∀ k, P k) (n + c) := by
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]; exact h
  rw [adicCompletionEquivTowerLimitOfEventualRange_apply,
    adicCompletionEquivTowerLimitOfEventualRange_apply, ← sub_eq_zero, ← map_sub] at hw
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (w.val (n + c) - w'.val (n + c))
  rw [← hm, adicQuotientMap_mk] at hw
  have hmem : m ∈ I ^ n • (⊤ : Submodule A M) := by
    have := hker' (n + c) (Nat.le_add_left c n) hw
    rwa [Nat.add_sub_cancel] at this
  have hn : w.val n - w'.val n =
      AdicCompletion.transitionMap I M (Nat.le_add_right n c)
        (w.val (n + c) - w'.val (n + c)) := by
    rw [map_sub, w.property, w'.property]
  rw [← sub_eq_zero, hn, ← hm]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

end Components

end TowerOfMaps

section Topology

/-- The limit topology on a family of elements of a product of types: the topology induced along
`f` from the product of the discrete topologies. -/
public abbrev limitTopology {X : Type*} {Q : ℕ → Type*} (f : X → ∀ n, Q n) : TopologicalSpace X :=
  TopologicalSpace.induced f (@Pi.topologicalSpace ℕ Q fun _ => ⊥)

/-- **A map between limits for the limit topologies is continuous as soon as each component of
its value depends only on one component of its argument.** -/
public theorem continuous_limitTopology {X Y : Type*} {Q : ℕ → Type*} {R : ℕ → Type*}
    (f : X → ∀ n, Q n) (f' : Y → ∀ n, R n) (g : X → Y)
    (hg : ∀ n, ∃ k, ∀ x x', f x k = f x' k → f' (g x) n = f' (g x') n) :
    @Continuous X Y (limitTopology f) (limitTopology f') g := by
  let : ∀ n, TopologicalSpace (Q n) := fun _ => ⊥
  let : ∀ n, TopologicalSpace (R n) := fun _ => ⊥
  have : ∀ n, DiscreteTopology (Q n) := fun _ => ⟨rfl⟩
  let : TopologicalSpace X := TopologicalSpace.induced f inferInstance
  let : TopologicalSpace Y := TopologicalSpace.induced f' inferInstance
  refine continuous_induced_rng.2 (continuous_pi fun n => ?_)
  obtain ⟨k, hk⟩ := hg n
  refine continuous_def.2 fun U _ => ?_
  have e : (fun x => f' (g x) n) ⁻¹' U =
      f ⁻¹' ((fun q => q k) ⁻¹' ((fun x => f x k) '' ((fun x => f' (g x) n) ⁻¹' U))) := by
    ext x
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨x₀, hx₀, he⟩
      change f' (g x) n ∈ U
      rw [← hk x₀ x he]
      exact hx₀
  change IsOpen ((fun x => f' (g x) n) ⁻¹' U)
  rw [e]
  exact isOpen_induced ((isOpen_discrete _).preimage (continuous_apply k))

/-- The limit topology on `M^∧_I`, induced from the product of the discrete topologies on the
`M ⧸ Iⁿ M`. -/
public abbrev adicCompletionLimitTopology (I : Ideal A) (M : Type*) [AddCommGroup M]
    [Module A M] : TopologicalSpace (AdicCompletion I M) :=
  limitTopology fun w : AdicCompletion I M => w.val

/-- The limit topology on `lim_n P n`, induced from the product of the discrete topologies on
the `P n`. -/
public abbrev towerLimitTopology (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
    (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) : TopologicalSpace (towerLimit P T) :=
  limitTopology fun x : towerLimit P T => (x : ∀ n, P n)

variable {M : Type*} [AddCommGroup M] [Module A M]
  (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m) (π : ∀ n, M →ₗ[A] P n) (I : Ideal A)
  (hker : ∀ n, I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker (π n)) (c : ℕ)
  (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
  (hker' : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M))
  (hrange : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n))

/-- **The comparison `M^∧_I ≃ lim_n P n` is a homeomorphism for the limit topologies.**  Its
`n`-th component reads the `n`-th component of its argument, and the `n`-th component of its
inverse reads the component of level `n + c`. -/
public theorem isHomeomorph_adicCompletionEquivTowerLimitOfEventualRange :
    @IsHomeomorph _ _ (adicCompletionLimitTopology I M) (towerLimitTopology P T)
      (adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange) := by
  let := adicCompletionLimitTopology I M
  let := towerLimitTopology P T
  set e := adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange
  have h₁ : Continuous e := continuous_limitTopology _ _ _ fun n => ⟨n, fun w w' h => by
    rw [adicCompletionEquivTowerLimitOfEventualRange_apply,
      adicCompletionEquivTowerLimitOfEventualRange_apply]
    exact congrArg _ h⟩
  have h₂ : Continuous e.symm := continuous_limitTopology _ _ _ fun n => ⟨n + c, fun x x' h =>
    adicCompletionEquivTowerLimitOfEventualRange_symm_val_eq P T π I hker c hπ hker' hrange
      x x' n h⟩
  exact (Homeomorph.mk e.toEquiv h₁ h₂).isHomeomorph

/-- The map `M ⟶ lim_n P n` assembled from the compatible maps `π n`. -/
public def towerLimitLift : M →ₗ[A] towerLimit P T :=
  LinearMap.codRestrict _ (LinearMap.pi π) fun x m n h => by
    simpa using LinearMap.congr_fun (hπ m n h) x

/-- The `n`-th component of the image of `x` in `lim_n P n` is `π n x`. -/
@[simp]
public theorem towerLimitLift_apply (x : M) (n : ℕ) :
    ((towerLimitLift P T π hπ x : towerLimit P T) : ∀ k, P k) n = π n x :=
  rfl

include hker hker' hrange in
/-- **For `M` complete, `M` itself is the limit**: if `M` is `I`-adically complete then
`M ⟶ lim_n P n` is bijective. -/
public theorem bijective_towerLimitLift_of_isAdicComplete [IsAdicComplete I M] :
    Function.Bijective (towerLimitLift P T π hπ) := by
  have e : towerLimitLift P T π hπ =
      (adicCompletionEquivTowerLimitOfEventualRange P T π I c hπ hker hker' hrange).toLinearMap ∘ₗ
        AdicCompletion.of I M :=
    LinearMap.ext fun x => towerLimit_ext fun n =>
      (adicCompletionEquivTowerLimitOfEventualRange_of P T π I hker c hπ hker' hrange x n).symm
  rw [e, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp (AdicCompletion.of_bijective I M)

end Topology

end Stacks.IntertwinedFiltration.C1573

end
