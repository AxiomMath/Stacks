module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Exterior powers and the torsion-free quotient

Over a principal ideal domain the `r`-th exterior power of the torsion-free quotient of a finite
module is the torsion-free quotient of its `r`-th exterior power: the map `⋀^r M → ⋀^r (M ⧸ tors)`
induced by the projection is surjective with kernel exactly the torsion submodule of `⋀^r M`.

## Main results

* `exteriorPower.ker_map_mkQ_eq_torsion`: the kernel of `⋀^r` of the projection to the
  torsion-free quotient is the torsion submodule.
* `exteriorPower.torsionQuotientEquiv`: **`(⋀^r M) ⧸ tors ≃ ⋀^r (M ⧸ tors)`.**

## Implementation notes

Injectivity is not a base change: Mathlib has no localization of exterior powers. Instead the
projection `M → M ⧸ tors` splits, the quotient being finite and torsion-free over a principal
ideal domain hence free; expanding a wedge of `r` vectors along `m = s (m mod tors) +
(m - s (m mod tors))` writes `⋀^r M` as the range of `⋀^r s` plus torsion, and `⋀^r` of the
projection is injective on that range.
-/

@[expose] public noncomputable section

namespace exteriorPower

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] {r : ℕ}
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The torsion-free quotient of a finite module over a principal ideal domain is free. -/
public instance free_quotient_torsion : Module.Free A (M ⧸ Submodule.torsion A M) :=
  Module.free_of_finite_type_torsion_free'

/-- The exterior powers of the torsion-free quotient are torsion free. -/
public theorem torsion_exteriorPower_quotient_eq_bot :
    Submodule.torsion A (⋀[A]^r (M ⧸ Submodule.torsion A M)) = ⊥ :=
  Submodule.isTorsionFree_iff_torsion_eq_bot.1 (Module.Free.instIsTorsionFree A _)

/-- `⋀^r` of the projection to the torsion-free quotient kills the torsion. -/
public theorem map_mkQ_eq_zero_of_mem_torsion {x : ⋀[A]^r M}
    (hx : x ∈ Submodule.torsion A (⋀[A]^r M)) :
    exteriorPower.map r (Submodule.torsion A M).mkQ x = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  have hsm : (a : A) • exteriorPower.map r (Submodule.torsion A M).mkQ x = 0 := by
    rw [← map_smul, show (a : A) • x = 0 from ha, map_zero]
  have hmem : exteriorPower.map r (Submodule.torsion A M).mkQ x
      ∈ Submodule.torsion A (⋀[A]^r (M ⧸ Submodule.torsion A M)) :=
    (Submodule.mem_torsion_iff _).mpr ⟨a, hsm⟩
  rwa [torsion_exteriorPower_quotient_eq_bot, Submodule.mem_bot] at hmem

omit [IsDomain A] [IsPrincipalIdealRing A] [Module.Finite A M] in
/-- **A splitting of the projection splits `⋀^r M` into its range and the torsion.** Expanding a
wedge of `r` vectors along `m = s (m mod tors) + (m - s (m mod tors))` leaves one term with no
torsion entry, which lies in the range of `⋀^r s`. -/
public theorem top_le_range_map_sup_torsion (s : (M ⧸ Submodule.torsion A M) →ₗ[A] M)
    (hs : (Submodule.torsion A M).mkQ ∘ₗ s = LinearMap.id) :
    (⊤ : Submodule A (⋀[A]^r M)) ≤
      LinearMap.range (exteriorPower.map r s) ⊔ Submodule.torsion A (⋀[A]^r M) := by
  classical
  rw [← exteriorPower.ιMulti_span A r M, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  obtain ⟨g, h, hgh, hgs, htor⟩ :
      ∃ g h : Fin r → M, g + h = m ∧ (∀ i, g i = s ((Submodule.torsion A M).mkQ (m i)))
        ∧ ∀ i, h i ∈ Submodule.torsion A M := by
    refine ⟨fun i => s ((Submodule.torsion A M).mkQ (m i)),
      fun i => m i - s ((Submodule.torsion A M).mkQ (m i)), funext fun i => by simp,
      fun _ => rfl, fun i => ?_⟩
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    have hid := LinearMap.congr_fun hs ((Submodule.torsion A M).mkQ (m i))
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hid
    change (Submodule.torsion A M).mkQ (m i - s ((Submodule.torsion A M).mkQ (m i))) = 0
    rw [map_sub, hid, sub_self]
  have hexp : (exteriorPower.ιMulti A r) m
      = ∑ S : Finset (Fin r), (exteriorPower.ιMulti A r).toMultilinearMap (S.piecewise g h) := by
    rw [← hgh]
    exact (exteriorPower.ιMulti A r).toMultilinearMap.map_add_univ g h
  rw [SetLike.mem_coe, hexp]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : S = Finset.univ
  · subst hS
    refine Submodule.mem_sup_left ⟨(exteriorPower.ιMulti A r)
      (fun i => (Submodule.torsion A M).mkQ (m i)), ?_⟩
    rw [exteriorPower.map_apply_ιMulti, Finset.piecewise_univ,
      show (⇑s ∘ fun i => (Submodule.torsion A M).mkQ (m i)) = g from
        funext fun i => (hgs i).symm]
    rfl
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hc
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 hc i))
    refine Submodule.mem_sup_right ?_
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (h i)).mp (htor i)
    refine (Submodule.mem_torsion_iff _).mpr ⟨a, ?_⟩
    have hv : (S.piecewise g h) i = h i := Finset.piecewise_eq_of_notMem _ _ _ hi
    have hu : Function.update (S.piecewise g h) i (h i) = S.piecewise g h := by
      rw [← hv]; exact Function.update_eq_self i _
    have key := (exteriorPower.ιMulti A r).toMultilinearMap.map_update_smul
      (S.piecewise g h) i (a : A) (h i)
    rw [show (a : A) • h i = 0 from ha, MultilinearMap.map_update_zero, hu] at key
    exact key.symm

/-- **The kernel of `⋀^r` of the projection to the torsion-free quotient is the torsion.** -/
public theorem ker_map_mkQ_eq_torsion :
    LinearMap.ker (exteriorPower.map r (Submodule.torsion A M).mkQ)
      = Submodule.torsion A (⋀[A]^r M) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    (Submodule.torsion A M).mkQ (Submodule.range_mkQ _)
  refine le_antisymm (fun x hx => ?_) fun x hx =>
    LinearMap.mem_ker.2 (map_mkQ_eq_zero_of_mem_torsion hx)
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Submodule.mem_sup.1 (top_le_range_map_sup_torsion s hs (Submodule.mem_top (x := x)))
  obtain ⟨w, hw⟩ := hy
  have h0 : exteriorPower.map r (Submodule.torsion A M).mkQ y = 0 := by
    have hx0 : exteriorPower.map r (Submodule.torsion A M).mkQ x = 0 := LinearMap.mem_ker.1 hx
    rw [← hyz, map_add, map_mkQ_eq_zero_of_mem_torsion hz, add_zero] at hx0
    exact hx0
  have hw0 : w = 0 := by
    rw [← hw, ← LinearMap.comp_apply, ← exteriorPower.map_comp, hs, exteriorPower.map_id] at h0
    simpa using h0
  rw [← hyz, ← hw, hw0, map_zero, zero_add]
  exact hz

/-- **The exterior power of the torsion-free quotient is the torsion-free quotient of the
exterior power**, for a finite module over a principal ideal domain. -/
public def torsionQuotientEquiv :
    (⋀[A]^r M ⧸ Submodule.torsion A (⋀[A]^r M)) ≃ₗ[A] ⋀[A]^r (M ⧸ Submodule.torsion A M) :=
  (Submodule.quotEquivOfEq _ _ ker_map_mkQ_eq_torsion.symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (exteriorPower.map_surjective (Submodule.mkQ_surjective _)))

/-- The identification sends the class of `x` to `⋀^r` of the projection applied to `x`. -/
public theorem torsionQuotientEquiv_mk (x : ⋀[A]^r M) :
    torsionQuotientEquiv (Submodule.Quotient.mk x : ⋀[A]^r M ⧸ Submodule.torsion A (⋀[A]^r M))
      = exteriorPower.map r (Submodule.torsion A M).mkQ x := rfl

end exteriorPower

end
