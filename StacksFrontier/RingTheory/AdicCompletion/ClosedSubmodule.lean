module

public import Mathlib
public import StacksFrontier.RingTheory.AdicCompletion.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Closed submodules of an adically complete module

Let `I ⊆ R` be an ideal of a commutative ring and `M` an `I`-adically complete `R`-module,
carrying the `I`-adic topology `Ideal.adicModuleTopology`. For a submodule `N ⊆ M` the following
are equivalent:

1. `N` is closed in `M`;
2. `N = ⋂ₙ (N + IⁿM)`;
3. `M ⧸ N` is `I`-adically complete.

If moreover `I` is finitely generated, these conditions imply that `N` is `I`-adically complete.

## Main results

* `Stacks.AdicClosedSubmodule.mem_closure_iff_forall_mem_sup`: the closure of `N` for the
  `I`-adic topology is `⋂ₙ (N + IⁿM)` (for any module `M`).
* `Stacks.AdicClosedSubmodule.isClosed_iff_eq_iInf_sup`: `N` is closed iff `N = ⋂ₙ (N + IⁿM)`.
* `Stacks.AdicClosedSubmodule.isAdicComplete_of_fg_of_eq_iInf_sup`: for `I` finitely generated
  and `M` complete, a submodule with `N = ⋂ₙ (N + IⁿM)` is `I`-adically complete.
* `Stacks.AdicClosedSubmodule.tfae_isClosed_eq_iInf_sup_isAdicComplete_quotient`: the full
  statement.

## Implementation notes

The submodule `IⁿM` is `I ^ n • ⊤` and `N + IⁿM` is `N ⊔ I ^ n • ⊤`. The equivalence of (2) and
(3) is `main_theorem_031a` (Stacks 031A). For the last assertion we follow Stacks: the inclusion
`N → M` extends to `N^∧ → M` because `M` is complete, this map lands in `N` because `N` is closed,
so `N` is a retract of `N^∧`, which is complete because `I` is finitely generated (Stacks 05GG).

## References

* [The Stacks Project, Tag 0HB3](https://stacks.math.columbia.edu/tag/0HB3)
-/

@[expose] public section

open Submodule AdicCompletion

namespace Stacks.AdicClosedSubmodule

variable {R : Type*} [CommRing R] (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

/-- A linear map preserves congruence modulo `IⁿM`. -/
theorem smodEq_pow_smul_top_map {P : Type*} [AddCommGroup P] [Module R P] (φ : M →ₗ[R] P)
    {n : ℕ} {x y : M} (h : x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]) :
    φ x ≡ φ y [SMOD (I ^ n • ⊤ : Submodule R P)] :=
  (h.map φ).mono (by rw [map_smul'']; exact smul_mono_right _ le_top)

/-- For the `I`-adic topology on `M`, a point lies in the closure of a submodule `N` if and only
if it lies in `N + IⁿM` for every `n`. -/
theorem mem_closure_iff_forall_mem_sup (N : Submodule R M) (x : M) :
    x ∈ @closure M (I.adicModuleTopology M) (N : Set M) ↔
      ∀ n : ℕ, x ∈ N ⊔ (I ^ n • ⊤ : Submodule R M) := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let B := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
  have hb : (nhds x).HasBasis (fun U => U ∈ B) fun U => (fun y => x + y) '' U :=
    B.nhds_hasBasis x
  rw [mem_closure_iff_nhds_basis' hb]
  constructor
  · intro h n
    obtain ⟨_, ⟨u, hu, rfl⟩, hN⟩ := h _
      (show ((I ^ n • ⊤ : Submodule R M) : Set M) ∈ B from ⟨n, rfl⟩)
    have hx : x = (x + u) - u := by abel
    rw [hx]
    exact sub_mem (mem_sup_left hN) (mem_sup_right hu)
  · intro h U hU
    obtain ⟨n, rfl⟩ : ∃ n, U = ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) := hU
    obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup.mp (h n)
    refine ⟨y, ⟨-z, neg_mem hz, ?_⟩, hy⟩
    change x + -z = y
    rw [← hyz]
    abel

/-- For the `I`-adic topology on `M`, a submodule `N` is closed if and only if
`N = ⋂ₙ (N + IⁿM)`. -/
theorem isClosed_iff_eq_iInf_sup (N : Submodule R M) :
    @IsClosed M (I.adicModuleTopology M) (N : Set M) ↔
      N = ⨅ n : ℕ, (N ⊔ (I ^ n • ⊤ : Submodule R M)) := by
  let : TopologicalSpace M := I.adicModuleTopology M
  rw [← closure_subset_iff_isClosed]
  constructor
  · intro h
    refine le_antisymm (le_iInf fun n => le_sup_left) fun x hx => h ?_
    rw [mem_closure_iff_forall_mem_sup]
    exact fun n => (mem_iInf _).mp hx n
  · intro h x hx
    rw [mem_closure_iff_forall_mem_sup] at hx
    rw [SetLike.mem_coe, h, mem_iInf]
    exact hx

/-- Let `M` be `I`-adically complete and `N ⊆ M` a submodule with `N = ⋂ₙ (N + IⁿM)`. The map
`N^∧ → M` induced by the inclusion lands in `N`; this is the resulting retraction
`N^∧ → N` of `N → N^∧`. -/
noncomputable def retraction [IsAdicComplete I M] (N : Submodule R M)
    (hN : N = ⨅ n : ℕ, (N ⊔ (I ^ n • ⊤ : Submodule R M))) :
    AdicCompletion I N →ₗ[R] N :=
  LinearMap.codRestrict N
    ((ofLinearEquiv I M).symm.toLinearMap ∘ₗ (map I N.subtype).restrictScalars R) fun ξ => by
      refine hN.ge (mem_iInf _ |>.mpr fun n => ?_)
      set m := (ofLinearEquiv I M).symm (map I N.subtype ξ)
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (ξ.val n)
      have hm : of I M m = map I N.subtype ξ := of_ofLinearEquiv_symm I _
      have hlev := congrArg (fun η : AdicCompletion I M => η.val n) hm
      simp only [of_apply, map_val_apply, ← hx, LinearMap.reduceModIdeal_apply,
        Submodule.mkQ_apply, Submodule.subtype_apply] at hlev
      have hsub : m - (x : M) ∈ (I ^ n • ⊤ : Submodule R M) :=
        (Submodule.Quotient.eq _).mp hlev
      have hmx : m = (m - (x : M)) + (x : M) := by abel
      change m ∈ N ⊔ (I ^ n • ⊤ : Submodule R M)
      rw [hmx]
      exact add_mem (mem_sup_right hsub) (mem_sup_left x.2)

theorem retraction_of [IsAdicComplete I M] (N : Submodule R M)
    (hN : N = ⨅ n : ℕ, (N ⊔ (I ^ n • ⊤ : Submodule R M))) (x : N) :
    retraction I N hN (of I N x) = x := by
  ext
  simp [retraction, map_of]

/-- Let `I` be finitely generated, `M` an `I`-adically complete module and `N ⊆ M` a submodule
with `N = ⋂ₙ (N + IⁿM)`. Then `N` is `I`-adically complete. -/
theorem isAdicComplete_of_fg_of_eq_iInf_sup (hI : I.FG) [IsAdicComplete I M]
    (N : Submodule R M) (hN : N = ⨅ n : ℕ, (N ⊔ (I ^ n • ⊤ : Submodule R M))) :
    IsAdicComplete I N := by
  have : IsAdicComplete I (AdicCompletion I N) := AdicCompletion.isAdicComplete hI
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply Subtype.ext
    refine IsHausdorff.haus' (I := I) (x : M) fun n => ?_
    simpa using smodEq_pow_smul_top_map I N.subtype (hx n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => of I N (f n))
      fun {m n} hmn => smodEq_pow_smul_top_map I (of I N) (hf hmn)
    refine ⟨retraction I N hN L, fun n => ?_⟩
    simpa [retraction_of] using smodEq_pow_smul_top_map I (retraction I N hN) (hL n)

/-- **Stacks 0HB3.** Let `I ⊆ R` be an ideal of a ring, `M` an `I`-adically complete
`R`-module and `N ⊆ M` a submodule. The following are equivalent: (1) `N` is closed in `M` (for
the `I`-adic topology), (2) `N = ⋂_{n ≥ 1} (N + IⁿM)`, (3) `M ⧸ N` is `I`-adically complete.
If `I` is finitely generated, these conditions imply that `N` is `I`-adically complete. -/
@[stacks 0HB3 "Complete statement: the three equivalent conditions, and completeness of `N` for
finitely generated `I`. The intersection in (2) is over all `n`; the `n = 0` term is `M`."]
theorem tfae_isClosed_eq_iInf_sup_isAdicComplete_quotient [IsAdicComplete I M]
    (N : Submodule R M) :
    List.TFAE [@IsClosed M (I.adicModuleTopology M) (N : Set M),
      N = ⨅ n : ℕ, (N ⊔ (I ^ n • ⊤ : Submodule R M)),
      IsAdicComplete I (M ⧸ N)] ∧
    (I.FG → @IsClosed M (I.adicModuleTopology M) (N : Set M) → IsAdicComplete I N) := by
  refine ⟨?_, fun hI hN =>
    isAdicComplete_of_fg_of_eq_iInf_sup I hI N ((isClosed_iff_eq_iInf_sup I N).mp hN)⟩
  tfae_have 1 ↔ 2 := isClosed_iff_eq_iInf_sup I N
  tfae_have 2 ↔ 3 := main_theorem_031a I M N
  tfae_finish

end Stacks.AdicClosedSubmodule
