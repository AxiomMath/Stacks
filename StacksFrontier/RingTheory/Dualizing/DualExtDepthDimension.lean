module

public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound

import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds

/-!
# Finiteness, support dimension and depth for the dual Ext modules

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, and let
`M` be a finite `A`-module. The modules

`Eⁱ = Ext_A^{-i}(M, ω_A^•)`

are the cohomology of the dual of `M`. This file records three of their basic properties:
each `Eⁱ` is a finite `A`-module and vanishes outside the range `0 ≤ i ≤ dim Supp(M)`; the
support of `Eⁱ` has dimension at most `i`; and the depth of `M` is the least `i` with
`Eⁱ ≠ 0`.

## Main results

* `Dualizing.moduleExtInto_finite` — each `Eⁱ` is a finite `A`-module.
* `Dualizing.moduleExtInto_degree_range` — `Eⁱ` vanishes unless `0 ≤ i ≤ dim Supp(M)`.
* `Dualizing.supportDim_moduleExtInto_le` — `dim Supp(Eⁱ) ≤ i`, and `Eⁱ = 0` for `i < 0`.
* `Dualizing.depth_eq_iInf_nontrivial_moduleExtInto` — the depth of `M` is the least `i`
  with `Eⁱ ≠ 0`.

## Implementation notes

The module `Eⁱ` is `Dualizing.moduleExtInto M ω (-i)`, the spelling used throughout the
surrounding files. The dimension of a support takes values in `WithBot ℕ∞`, the dimension
of the empty support being `⊥`; the support-dimension bound therefore reads as a vanishing
statement in negative degrees. Depth takes values in `ℕ∞`, the depth of the zero module
being `⊤`; the description of the depth as an infimum over the degrees of nonvanishing
covers that case as well, both sides then being `⊤`.

## References

* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The dual Ext modules of a subsingleton module are subsingletons. -/
private theorem subsingleton_moduleExtInto_of_subsingleton {A : Type u} [CommRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Subsingleton M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (n : ℤ) :
    Subsingleton (moduleExtInto M K n) := by
  have hzero : Limits.IsZero
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of A M))
  exact ⟨fun x y => hzero.eq_of_src x y⟩

/-- **Stacks Project, Tag 0DWZ, part (1): finiteness.** For a finite module `M` over a
Noetherian local ring with normalized dualizing complex `ω`, every module
`Eⁱ = Ext_A^{-i}(M, ω)` is a finite `A`-module. -/
@[stacks 0DWZ "part (1): each Ext^{-i}(M, ω) is a finite A-module"]
theorem moduleExtInto_finite {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (i : ℤ) :
    Module.Finite A (moduleExtInto M K (-i)) :=
  moduleFinite_ext (A := A) (M := M) K hK.1 (-i)

/-- **Stacks Project, Tag 0DWZ, part (1): degree range.** For a finite module `M` over a
Noetherian local ring with normalized dualizing complex `ω`, the module
`Eⁱ = Ext_A^{-i}(M, ω)` can be nonzero only for `0 ≤ i ≤ dim Supp(M)`; in particular the
dimension of the support of `M` is then a natural number. -/
@[stacks 0DWZ "part (1): Ext^{-i}(M, ω) vanishes outside 0 ≤ i ≤ dim Supp(M)"]
theorem moduleExtInto_degree_range {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (i : ℤ)
    (hi : Nontrivial (moduleExtInto M K (-i))) :
    ∃ d : ℕ, Module.supportDim A M = (d : WithBot ℕ∞) ∧ i ∈ Set.Icc 0 (d : ℤ) := by
  have hM : Nontrivial M := by
    by_contra h
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    exact (not_subsingleton_iff_nontrivial.mpr hi)
      (subsingleton_moduleExtInto_of_subsingleton K (-i))
  obtain ⟨d, hd⟩ := exists_supportDim_eq_nat (A := A) M
  refine ⟨d, hd, ?_⟩
  obtain ⟨hlo, hhi⟩ := ext_degree_mem_Icc_of_nontrivial (A := A) (M := M) K hK d hd (-i) hi
  exact ⟨by omega, by omega⟩

/-- **Stacks Project, Tag 0DWZ, part (2).** For a finite module `M` over a Noetherian local
ring with normalized dualizing complex `ω`, the support of `Eⁱ = Ext_A^{-i}(M, ω)` has
dimension at most `i`; for `i < 0` the module `Eⁱ` vanishes, so its support is empty. -/
@[stacks 0DWZ "part (2): dim Supp(Ext^{-i}(M, ω)) ≤ i"]
theorem supportDim_moduleExtInto_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) (i : ℤ) :
    Module.supportDim A (moduleExtInto M K (-i)) ≤
      if 0 ≤ i then ((i.toNat : ℕ∞) : WithBot ℕ∞) else ⊥ := by
  classical
  by_cases hM : Subsingleton M
  · have := subsingleton_moduleExtInto_of_subsingleton (M := M) K (-i)
    rw [Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    simpa using supportDim_ext_le_neg_degree (A := A) K M hK (-i)

/-- **Stacks Project, Tag 0DWZ, part (3).** For a finite module `M` over a Noetherian local
ring with normalized dualizing complex `ω`, the depth of `M` is the least `i ≥ 0` for which
`Eⁱ = Ext_A^{-i}(M, ω)` is nonzero. If all these modules vanish, both sides are `⊤`. -/
@[stacks 0DWZ "part (3): depth(M) is the least i with Ext^{-i}(M, ω) ≠ 0"]
theorem depth_eq_iInf_nontrivial_moduleExtInto {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) :
    Module.depth A (IsLocalRing.maximalIdeal A) M =
      ⨅ (i : ℕ) (_ : Nontrivial (moduleExtInto M K (-(i : ℤ)))), (i : ℕ∞) := by
  by_cases hM : Nontrivial M
  · obtain ⟨delta, hleast, hdepth⟩ := depth_eq_least_nonzero_negative_ext K hK hM
    rw [hdepth]
    refine le_antisymm (le_iInf fun i => le_iInf fun hi => ?_)
      ((iInf_le _ delta).trans (iInf_le _ hleast.1))
    exact_mod_cast hleast.2 hi
  · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    rw [show Module.depth A (IsLocalRing.maximalIdeal A) M = ⊤ by
      simp [Module.depth, Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule A M))]]
    refine (top_unique (le_iInf fun i => le_iInf fun hi => ?_)).symm
    exact ((not_nontrivial_iff_subsingleton.mpr
      (subsingleton_moduleExtInto_of_subsingleton K (-(i : ℤ)))) hi).elim

end Dualizing

end
