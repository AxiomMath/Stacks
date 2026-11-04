module

public import StacksFrontier.RingTheory.FormsTrace.Defs

/-!
# Kernels of pull-backs of exterior powers along surjections

Two kernel computations for pull-backs along a surjective ring map.

Let `φ : S → T` be a surjective ring map and `u : M → N` a surjective `φ`-semilinear map from an
`S`-module to a `T`-module. The semilinear map `⋀^{n+1}_S M → ⋀^{n+1}_T N` induced by `u` is
surjective, and its kernel is spanned over `S` by the wedges `m ∧ y` with `u m = 0` and
`y ∈ ⋀^n_S M`. This is the right exactness of the exterior power, in semilinear form.

The second computation is the kernel of `Q → T ⊗_S Q`, `q ↦ 1 ⊗ q`, for a surjective algebra
`S → T`: it is `ker(S → T) • Q`.

## Main results

* `Stacks.FormsTrace.ker_powMapₛₗ_le_span_wedgeLeft`: the kernel of `⋀^{n+1}` of a surjective
  semilinear map along a surjective ring map is spanned by the wedges `m ∧ y` with `u m = 0`.
* `Stacks.FormsTrace.powMapₛₗ_surjective`: that map is surjective.
* `Stacks.FormsTrace.ker_tensorProductMk_of_surjective`: `ker (Q → T ⊗_S Q) = ker(S → T) • Q`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.FormsTrace

section ExteriorKernel

variable {S T : Type*} [CommRing S] [CommRing T] {φ : S →+* T}
  {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]

/-- The `S`-submodule of `⋀^{n+1}_S M` spanned by the wedges `m ∧ y` with `u m = 0`. -/
abbrev wedgeKerSpan (u : M →ₛₗ[φ] N) (n : ℕ) : Submodule S (⋀[S]^(n + 1) M) :=
  Submodule.span S {z | ∃ (m : M) (y : ⋀[S]^n M), u m = 0 ∧ z = exteriorPower.wedgeLeft m n y}

/-- A wedge of vectors one of which is killed by `u` lies in `wedgeKerSpan u n`. -/
theorem ιMulti_mem_wedgeKerSpan (u : M →ₛₗ[φ] N) {n : ℕ} (v : Fin (n + 1) → M)
    (i : Fin (n + 1)) (hi : u (v i) = 0) :
    exteriorPower.ιMulti S (n + 1) v ∈ wedgeKerSpan u n := by
  have front : ∀ w : Fin (n + 1) → M, u (w 0) = 0 →
      exteriorPower.ιMulti S (n + 1) w ∈ wedgeKerSpan u n := by
    intro w hw
    have h := Submodule.subset_span (R := S)
      (s := {z | ∃ (m : M) (y : ⋀[S]^n M), u m = 0 ∧ z = exteriorPower.wedgeLeft m n y})
      ⟨w 0, exteriorPower.ιMulti S n (Fin.tail w), hw, rfl⟩
    rwa [exteriorPower.wedgeLeft_ιMulti, Fin.cons_self_tail] at h
  obtain rfl | h0 := eq_or_ne i 0
  · exact front v hi
  · have hs := (exteriorPower.ιMulti S (n + 1)).map_swap v h0.symm
    have hmem := front (v ∘ Equiv.swap 0 i) (by simpa [Equiv.swap_apply_left] using hi)
    rw [hs] at hmem
    exact (Submodule.neg_mem_iff _).mp hmem

/-- For a surjective ring map `φ : S → T` and a surjective `φ`-semilinear map `u : M → N`, the
kernel of the induced map `⋀^{n+1}_S M → ⋀^{n+1}_T N` is spanned over `S` by the wedges `m ∧ y`
with `u m = 0`. -/
theorem ker_powMapₛₗ_le_span_wedgeLeft (hφ : Function.Surjective φ) (u : M →ₛₗ[φ] N)
    (hu : Function.Surjective u) (n : ℕ) :
    LinearMap.ker (ExteriorAlgebra.powMapₛₗ (n + 1) φ u) ≤ wedgeKerSpan u n := by
  classical
  set P := wedgeKerSpan u n with hP
  have hJ : ∀ s : S, φ s = 0 → ∀ z : ⋀[S]^(n + 1) M, s • z ∈ P := by
    intro s hs z
    have hz : z ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S (n + 1))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have e : s • exteriorPower.ιMulti S (n + 1) v =
          exteriorPower.ιMulti S (n + 1) (Function.update v 0 (s • v 0)) := by
        rw [AlternatingMap.map_update_smul, Function.update_eq_self]
      rw [e]
      exact ιMulti_mem_wedgeKerSpan u _ 0 (by rw [Function.update_self, map_smulₛₗ, hs, zero_smul])
    | zero => rw [smul_zero]; exact P.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact P.add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact P.smul_mem c hx
  have hdep : ∀ a a' : Fin (n + 1) → M, (∀ i, u (a i) = u (a' i)) →
      exteriorPower.ιMulti S (n + 1) a - exteriorPower.ιMulti S (n + 1) a' ∈ P := by
    intro a a' h
    have hsum := (exteriorPower.ιMulti S (n + 1)).toMultilinearMap.map_add_univ a' (a - a')
    simp only [add_sub_cancel, AlternatingMap.coe_multilinearMap] at hsum
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), Finset.piecewise_univ,
      add_sub_cancel_left]
    refine P.sum_mem fun s hs => ?_
    obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ s, Finset.ne_of_mem_erase hs⟩)
    refine ιMulti_mem_wedgeKerSpan u _ i ?_
    rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Pi.sub_apply, map_sub, h i, sub_self]
  have hq : ∀ a a' : Fin (n + 1) → M, (∀ i, u (a i) = u (a' i)) →
      (Submodule.Quotient.mk (p := P) (exteriorPower.ιMulti S (n + 1) a)) =
        Submodule.Quotient.mk (exteriorPower.ιMulti S (n + 1) a') := by
    intro a a' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact hdep a a' h
  set sφ := Function.surjInv hφ
  have hsφ : ∀ t, φ (sφ t) = t := Function.surjInv_eq hφ
  let : SMul T (↥(⋀[S]^(n + 1) M) ⧸ P) := ⟨fun t (q : (⋀[S]^(n + 1) M) ⧸ P) => sφ t • q⟩
  have hsmul : ∀ (c : S) (x : (⋀[S]^(n + 1) M) ⧸ P), φ c • x = c • x := by
    intro c x
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
      show sφ (φ c) • Submodule.Quotient.mk (p := P) z = c • Submodule.Quotient.mk (p := P) z
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← sub_eq_zero,
        ← Submodule.Quotient.mk_sub, ← sub_smul, Submodule.Quotient.mk_eq_zero]
      exact hJ _ (by rw [map_sub, hsφ, sub_self]) z
  let : Module T (↥(⋀[S]^(n + 1) M) ⧸ P) := hφ.moduleLeft φ hsmul
  set su := Function.surjInv hu
  have hsu : ∀ x, u (su x) = x := Function.surjInv_eq hu
  have hupd : ∀ (w : Fin (n + 1) → N) (i : Fin (n + 1)) (x : N) (m : M), u m = x →
      ∀ j, u (su (Function.update w i x j)) = u (Function.update (fun k => su (w k)) i m j) := by
    intro w i x m hm j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self, Function.update_self, hsu, hm]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  let F : N [⋀^Fin (n + 1)]→ₗ[T] (↥(⋀[S]^(n + 1) M) ⧸ P) :=
    { toFun := fun w => Submodule.Quotient.mk (exteriorPower.ιMulti S (n + 1) fun i => su (w i))
      map_update_add' := by
        intro inst w i x y
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        rw [hq _ _ (hupd w i (x + y) (su x + su y) (by rw [map_add, hsu, hsu])),
          AlternatingMap.map_update_add, Submodule.Quotient.mk_add,
          hq _ _ (hupd w i x (su x) (hsu x)), hq _ _ (hupd w i y (su y) (hsu y))]
      map_update_smul' := by
        intro inst w i c x
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        rw [hq _ _ (hupd w i (c • x) (sφ c • su x) (by rw [map_smulₛₗ, hsφ, hsu])),
          AlternatingMap.map_update_smul, Submodule.Quotient.mk_smul,
          hq (fun j => su (Function.update w i x j)) _ (hupd w i x (su x) (hsu x))]
        rfl
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        rw [(exteriorPower.ιMulti S (n + 1)).map_eq_zero_of_eq _ (congrArg su hij) hne]
        rfl }
  set g := exteriorPower.alternatingMapLinearEquiv F
  have key : ∀ x : ⋀[S]^(n + 1) M,
      g (ExteriorAlgebra.powMapₛₗ (n + 1) φ u x) = Submodule.Quotient.mk x := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range (exteriorPower.ιMulti S (n + 1))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      rw [ExteriorAlgebra.powMapₛₗ_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      exact hq _ _ fun i => hsu _
    | zero => rw [map_zero, map_zero, Submodule.Quotient.mk_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, Submodule.Quotient.mk_add]
    | smul c x _ hx => rw [map_smulₛₗ, map_smul, hsmul, hx, Submodule.Quotient.mk_smul]
  intro x hx
  have h := key x
  rw [LinearMap.mem_ker.1 hx, map_zero] at h
  exact (Submodule.Quotient.mk_eq_zero P).1 h.symm

/-- The semilinear map `⋀^n_S M → ⋀^n_T N` induced by a surjective semilinear map along a
surjective ring map is surjective. -/
theorem powMapₛₗ_surjective (hφ : Function.Surjective φ) (u : M →ₛₗ[φ] N)
    (hu : Function.Surjective u) (n : ℕ) :
    Function.Surjective (ExteriorAlgebra.powMapₛₗ n φ u) := by
  intro x
  have hx : x ∈ Submodule.span T (Set.range (exteriorPower.ιMulti T n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    exact ⟨exteriorPower.ιMulti S n fun i => Function.surjInv hu (v i), by
      simp only [ExteriorAlgebra.powMapₛₗ_ιMulti, Function.surjInv_eq hu]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ a b⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := hφ c
    exact ⟨c • a, map_smulₛₗ _ c a⟩

end ExteriorKernel

section TensorKernel

/-- If `S → T` is surjective, the kernel of `Q → T ⊗_S Q`, `q ↦ 1 ⊗ q`, is `ker(S → T) • Q`. -/
theorem ker_tensorProductMk_of_surjective {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (h : Function.Surjective (algebraMap S T)) (Q : Type*) [AddCommGroup Q] [Module S Q] :
    LinearMap.ker (TensorProduct.mk S T Q 1) = RingHom.ker (algebraMap S T) • ⊤ := by
  set f : S →ₐ[S] T := Algebra.ofId S T
  have hker : RingHom.ker f = RingHom.ker (algebraMap S T) := rfl
  set e : (S ⧸ RingHom.ker f) ≃ₐ[S] T := Ideal.quotientKerAlgEquivOfSurjective (f := f) h
  have hcomp : TensorProduct.mk S T Q 1 =
      (e.toLinearEquiv.rTensor Q).toLinearMap ∘ₗ TensorProduct.mk S (S ⧸ RingHom.ker f) Q 1 := by
    ext q
    simp only [TensorProduct.mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_one]
  rw [hcomp, LinearEquiv.ker_comp, LinearMap.ker_tensorProductMk, hker]

end TensorKernel

end Stacks.FormsTrace

end
