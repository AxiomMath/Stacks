module

public import StacksFrontier.Topology.Sheaves.Modules.PrincipalAdicInverseSystem
public import StacksFrontier.Topology.Sheaves.Modules.PrincipalAdicLimitKernel
import StacksCore.Tactic.StacksAttribute

/-!
# The image of the inverse limit in the first sheaf

In the principal-adic inverse-system situation of Stacks 0BLB, the submodule of
`f^(n+1)`-multiples of the inverse limit `M` of global sections is the kernel of the
projection `M → Γ(X, 𝓕ₙ₊₁)`. In particular the quotient `M/fM` is carried isomorphically
onto the image of `M → Γ(X, 𝓕₁)` by the map the first projection induces, and that
isomorphism sends the class of a section to its own first projection.

## Main definitions

* `Stacks.Modules.PrincipalAdicInverseSystem.quotientEquivRange_firstProjection`: the
  canonical linear equivalence from `M/fM` to the image of the first projection.

## Main results

* `Stacks.Modules.PrincipalAdicInverseSystem.range_pow_eq_ker_projection`: the
  `f^(n+1)`-multiples in `M` are exactly the sections vanishing in `𝓕ₙ₊₁`.
* `Stacks.Modules.PrincipalAdicInverseSystem.range_lsmul_eq_ker_firstProjection`: the case
  `n = 0`: the `f`-multiples in `M` are the sections vanishing in `𝓕₁`.
* `Stacks.Modules.PrincipalAdicInverseSystem.quotientEquivRange_firstProjection_mk`: the
  equivalence sends the class of `x` to the first projection of `x`.

## References

* [Stacks Project, Tag 0BLB](https://stacks.math.columbia.edu/tag/0BLB)
* [Stacks Project, Tag 0EHA](https://stacks.math.columbia.edu/tag/0EHA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped IsMulCommutative

universe u w

namespace Stacks.Modules.PrincipalAdicInverseSystem

/-- The `f^(n+1)`-multiples in the inverse limit of global sections are exactly the sections
whose image in `𝓕ₙ₊₁` vanishes. -/
theorem range_pow_eq_ker_projection (S : PrincipalAdicInverseSystem.{u, w}) (n : ℕ) :
    (LinearMap.lsmul S.A S.M (S.f ^ (n + 1))).range =
      (limit.π S.globalSectionsSystem (op n)).hom.ker := by
  let : ∀ U, IsMulCommutative (S.R.obj.obj U) := S.mulCommutative
  exact range_pow_eq_ker_limitProjection_terminalSections S.R (⊤ : Opens S.X) isTerminalTop
    S.scalarMap S.f S.F S.map S.condition S.globalSectionsSystem rfl n

/-- The `f`-multiples in the inverse limit of global sections are exactly the sections whose
image in `𝓕₁` vanishes. -/
theorem range_lsmul_eq_ker_firstProjection (S : PrincipalAdicInverseSystem.{u, w}) :
    (LinearMap.lsmul S.A S.M S.f).range =
      (limit.π S.globalSectionsSystem (op 0)).hom.ker := by
  simpa using range_pow_eq_ker_projection S 0

/-- The quotient of the inverse limit by `f` maps isomorphically onto its image in the first
term, by the map induced by the first projection. -/
@[stacks 0BLB "image"]
def quotientEquivRange_firstProjection (S : PrincipalAdicInverseSystem.{u, w}) :
    (S.M ⧸ (LinearMap.lsmul S.A S.M S.f).range) ≃ₗ[S.A]
      LinearMap.range ((limit.π S.globalSectionsSystem (op 0)).hom) := by
  refine (Submodule.quotEquivOfEq _ _ ?_).trans
    ((limit.π S.globalSectionsSystem (op 0)).hom).quotKerEquivRange
  exact range_lsmul_eq_ker_firstProjection S

/-- The canonical equivalence sends a class to the first projection of a representative. -/
@[stacks 0BLB "image"]
theorem quotientEquivRange_firstProjection_mk (S : PrincipalAdicInverseSystem.{u, w})
    (x : S.M) :
    quotientEquivRange_firstProjection S (Submodule.Quotient.mk x) =
      ⟨(limit.π S.globalSectionsSystem (op 0)).hom x,
        LinearMap.mem_range_self _ x⟩ :=
  Subtype.ext rfl

end Stacks.Modules.PrincipalAdicInverseSystem

end
