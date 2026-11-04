module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Invariants of a transitive permutation on a free module

Let `σ` be a permutation of a finite nonempty set `T` acting transitively (every point is reached
from every other by iterating `σ`), and let `K` be a field. The free module `T →₀ K` has
dimension `#T`, and the kernel of `σ_* - 1` — the `σ`-invariant vectors — is the line of
constant functions.

This is the fibre of the free sheaf on a torsor under `ℤ/ℓ` with its translation, used for the
cyclic-cover argument in the duality of the first cohomology of a curve.

## Main results

* `Finsupp.mem_ker_lmapDomain_sub_id_iff`: `f` is invariant iff `f (σ t) = f t` for all `t`.
* `Finsupp.finrank_ker_lmapDomain_sub_id_eq_one`: the invariants form a line.
-/

@[expose] public section

namespace Finsupp

variable {K T : Type*} [Field K] (σ : T ≃ T)

/-- `σ_* f = f` exactly when `f` is constant along `σ`. -/
theorem mem_ker_lmapDomain_sub_id_iff (f : T →₀ K) :
    f ∈ LinearMap.ker (Finsupp.lmapDomain K K σ - LinearMap.id) ↔ ∀ t, f (σ t) = f t := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    Finsupp.lmapDomain_apply]
  constructor
  · intro h t
    simpa [Finsupp.mapDomain_apply σ.injective] using (DFunLike.congr_fun h (σ t)).symm
  · intro h
    ext t
    obtain ⟨t', rfl⟩ := σ.surjective t
    rw [Finsupp.mapDomain_apply σ.injective, h]

/-- **The invariants of a transitive permutation on the free module on a finite nonempty set
form a line.** -/
theorem finrank_ker_lmapDomain_sub_id_eq_one [Finite T] [Nonempty T]
    (htrans : ∀ t t' : T, ∃ k : ℕ, (σ^[k]) t = t') :
    Module.finrank K (LinearMap.ker (Finsupp.lmapDomain K K σ - LinearMap.id)) = 1 := by
  classical
  have := Fintype.ofFinite T
  obtain ⟨t₀⟩ : Nonempty T := inferInstance
  let c : T →₀ K := Finsupp.equivFunOnFinite.symm (fun _ => 1)
  have hc : c ∈ LinearMap.ker (Finsupp.lmapDomain K K σ - LinearMap.id) :=
    (mem_ker_lmapDomain_sub_id_iff σ c).2 fun t => by simp [c]
  have hconst : ∀ f ∈ LinearMap.ker (Finsupp.lmapDomain K K σ - LinearMap.id),
      ∀ t, f t = f t₀ := by
    intro f hf t
    rw [mem_ker_lmapDomain_sub_id_iff] at hf
    obtain ⟨k, rfl⟩ := htrans t₀ t
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hf, ih]
  refine finrank_eq_one_iff_of_nonzero' (⟨c, hc⟩ : LinearMap.ker _) ?_ |>.2 ?_
  · intro h
    simpa [c] using DFunLike.congr_fun (congrArg Subtype.val h) t₀
  · rintro ⟨f, hf⟩
    refine ⟨f t₀, Subtype.ext ?_⟩
    ext t
    simp [c, hconst f hf t]

end Finsupp

end
