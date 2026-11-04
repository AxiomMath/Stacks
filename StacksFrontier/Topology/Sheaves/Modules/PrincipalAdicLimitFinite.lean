module

public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.Noetherian.Basic
public import StacksFrontier.Topology.Sheaves.Modules.PrincipalAdicLimitImage
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the limit of a principal-adic inverse system

For a principal-adic inverse system (`Stacks.Modules.PrincipalAdicInverseSystem`), the inverse
limit `M` of the modules of global sections is a finite module over the complete Noetherian base
ring `A`.

## Main results

* `Stacks.Modules.PrincipalAdicInverseSystem.finite_limitGlobalSections`: the limit module is
  finite over the base ring.

## References

* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped IsMulCommutative

universe u w

namespace Stacks.Modules.PrincipalAdicInverseSystem

/-- The limit of global sections of a principal-adic inverse system is finite over its base
ring. -/
@[stacks 0BLB "finite"]
lemma finite_limitGlobalSections (S : PrincipalAdicInverseSystem.{u, w}) :
    Module.Finite S.A S.M := by
  classical
  let I : Ideal S.A := Ideal.span {S.f}
  let : IsNoetherianRing S.A := S.noetherian
  let : ∀ U, IsMulCommutative (S.R.obj.obj U) := S.mulCommutative
  have hsep : ⨅ n : ℕ, I ^ n • (⊤ : Submodule S.A S.M) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    simp only [Submodule.mem_iInf, I, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and] at hx
    refine Concrete.limit_ext S.globalSectionsSystem x 0 fun n ↦ ?_
    show (limit.π S.globalSectionsSystem n).hom x = (limit.π S.globalSectionsSystem n).hom 0
    rw [map_zero]
    obtain ⟨y, hy⟩ := hx (n.unop + 1)
    apply LinearMap.mem_ker.mp
    rw [← range_pow_eq_ker_projection S n.unop]
    exact ⟨y, by simpa only [LinearMap.lsmul_apply] using hy⟩
  let : IsPrecomplete I S.A := S.complete.toIsPrecomplete
  have hfin : Module.Finite (S.A ⧸ I)
      (S.M ⧸ I • (⊤ : Submodule S.A S.M)) := by
    have hIrange :
        (LinearMap.lsmul S.A S.M S.f).range = I • (⊤ : Submodule S.A S.M) := by
      ext x
      simp only [I, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
        LinearMap.lsmul_apply, Submodule.mem_smul_pointwise_iff_exists,
        Submodule.mem_top, true_and, eq_comm]
    have hfin0 : Module.Finite S.A (S.globalSectionsSystem.obj (op 0)) := S.finite_first
    have : IsNoetherian S.A (S.globalSectionsSystem.obj (op 0)) :=
      isNoetherian_of_isNoetherianRing_of_finite S.A _
    have : Module.Finite S.A
        (LinearMap.range ((limit.π S.globalSectionsSystem (op 0)).hom)) :=
      Module.Finite.of_fg (IsNoetherian.noetherian _)
    have : Module.Finite S.A (S.M ⧸ I • (⊤ : Submodule S.A S.M)) := by
      rw [← hIrange]
      exact Module.Finite.equiv (quotientEquivRange_firstProjection S).symm
    exact Module.Finite.of_restrictScalars_finite S.A (S.A ⧸ I) _
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top
    I hsep hfin

end Stacks.Modules.PrincipalAdicInverseSystem

end
