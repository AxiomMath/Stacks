module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoherentFibreStalk
public import StacksFrontier.Topology.Sober.Generization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic points of the support and finite length of the stalk

Let `X` be a locally Noetherian scheme and let `F` be a quasi-coherent `𝒪_X`-module of finite
type.  A point `ξ` of `X` is a generic point of an irreducible component of `Supp(F)` exactly
when the stalk `F_ξ` has finite, nonzero length over the local ring `𝒪_{X, ξ}`.

This is the scheme-level content of the proof of Stacks 0EE4: the support of `F_ξ` is the
pullback of the support of `F` along `Spec 𝒪_{X, ξ} → X`, whose image is the set of
generizations of `ξ`, so `ξ` is a generic point of a component of `Supp(F)` if and only if the
support of `F_ξ` is the closed point alone, and that is finite nonzero length by Stacks 00L5.
The direction from generic points to finite length is Stacks 02QW (2),
`Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp`, for a coherent module.

## Main results

* `Stacks.Chow.exists_isGenericPoint_component_supp_iff_length`: a point is a generic point of
  an irreducible component of the support of a quasi-coherent module of finite type on a
  locally Noetherian scheme exactly when the length of the stalk there is finite and nonzero.

## References

* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **Generic points of the support are the points of finite nonzero stalk length.**  On a
locally Noetherian scheme, a point `ξ` is a generic point of an irreducible component of the
support of a quasi-coherent module `F` of finite type exactly when the stalk `F_ξ` has finite
and nonzero length over `𝒪_{X, ξ}`.

The points of `Supp(F)` generizing `ξ` are the primes of `𝒪_{X, ξ}` in the support of `F_ξ`
(`Stacks.Chow.mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp`), so `ξ` has no proper
generization in `Supp(F)` exactly when the support of the finite module `F_ξ` is contained in
the closed point; Stacks 00L5 (`support_point`) makes that, for a nonzero stalk, finiteness of
the length. -/
@[ega "IV 3.1.4", ega "IV 4.7.7" "more general"]
theorem exists_isGenericPoint_component_supp_iff_length [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (ξ : X) :
    (∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint ξ (Subtype.val '' Z.1 : Set X)) ↔
      Module.length (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) ≠ ⊤ ∧
        0 < Module.length (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) := by
  have hfin : Module.Finite (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F ξ
  rw [TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff
    (SheafOfModules.isClosed_supp F) ξ, Module.length_ne_top_iff, Module.length_pos_iff]
  have hsupp : ξ ∈ SheafOfModules.supp F ↔ Nontrivial (F.presheaf.stalk ξ) :=
    SheafOfModules.mem_supp_iff_nontrivial_stalk F ξ
  constructor
  · rintro ⟨hξ, hmin⟩
    have : Nontrivial (F.presheaf.stalk ξ) := hsupp.mp hξ
    refine ⟨(support_point (R := X.presheaf.stalk ξ) (M := F.presheaf.stalk ξ)).mp
      (Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)), this⟩
    · have hpξ : X.fromSpecStalk ξ p ⤳ ξ := by
        have hr : X.fromSpecStalk ξ p ∈ Set.range (X.fromSpecStalk ξ) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at hr
      have hpeq : X.fromSpecStalk ξ p = X.fromSpecStalk ξ (IsLocalRing.closedPoint _) := by
        rw [Scheme.fromSpecStalk_closedPoint]
        exact hmin _ ((mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp F p).mp hp) hpξ
      exact Set.mem_singleton_iff.mpr ((X.fromSpecStalk ξ).isEmbedding.injective hpeq)
    · rw [Set.mem_singleton_iff.mp hp]
      exact IsLocalRing.closedPoint_mem_support _ _
  · rintro ⟨hlen, hnt⟩
    have hpt := (support_point (R := X.presheaf.stalk ξ) (M := F.presheaf.stalk ξ)).mpr hlen
    refine ⟨hsupp.mpr hnt, fun y hy hyξ => ?_⟩
    obtain ⟨q, rfl⟩ : y ∈ Set.range (X.fromSpecStalk ξ) := by
      rwa [Scheme.range_fromSpecStalk]
    have hq : q ∈ Module.support (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) :=
      (mem_moduleSupport_stalk_iff_fromSpecStalk_mem_supp F q).mpr hy
    have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk ξ) := by
      rwa [hpt] at hq
    rw [hq', Scheme.fromSpecStalk_closedPoint]

end Stacks.Chow

end
