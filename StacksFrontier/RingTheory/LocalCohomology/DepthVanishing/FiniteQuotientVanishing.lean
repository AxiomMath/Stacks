module

public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthTwo

/-!
# Local cohomology that is finite and unchanged by a regular element vanishes

Let `A` be a Noetherian local ring, `I ⊆ A` an ideal, `f ∈ 𝔪` an element and `M` a module on
which `f` is a nonzerodivisor. If `H^i_{V(I)}(M)` is a finite `A`-module and
`H^i_{V(I)}(M/fM)` vanishes, then `H^i_{V(I)}(M)` vanishes.

The long exact sequence of `0 → M →^f M → M/fM → 0` has

`H^i_{V(I)}(M) →^f H^i_{V(I)}(M) → H^i_{V(I)}(M/fM)`

exact in the middle, and multiplication by `f` on the module induces multiplication by `f` on
local cohomology
(`Stacks.LocalCohomology.localCohomologyMap_smul_id`). When the third term vanishes the second
map is zero, so multiplication by `f` is surjective on `H^i_{V(I)}(M)`, that is
`f • H^i_{V(I)}(M) = H^i_{V(I)}(M)`. Nakayama's lemma then kills a finite module over a local
ring.

This is the step that converts finiteness of a local cohomology module into its vanishing, and
it is the mechanism behind the depth bound for the global sections of an invertible module on a
punctured spectrum.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomology_of_finite_of_isZero_quotSMulTop`

## Implementation notes

The companion statements `Stacks.LocalCohomology.isZero_localCohomology_zero_of_isSMulRegular`
and `Stacks.LocalCohomology.isZero_localCohomology_one_of_isSMulRegular` run the *injective* half
of the same long exact sequence: there the connecting map vanishes, multiplication by `f` is a
monomorphism, and `Stacks.LocalCohomology.isZero_of_mono_smul_id` concludes from supportedness.
Here the surjective half is used instead, and the input is finiteness rather than a vanishing one
degree down.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

omit [IsNoetherianRing A] in
/-- **A finite local cohomology module that is divisible by a regular element vanishes.** Let `A`
be a local ring, `I ⊆ A` an ideal, `f ∈ 𝔪` and `M` an `A`-module on which `f` is a
nonzerodivisor. If `H^i_{V(I)}(M)` is a finite `A`-module and `H^i_{V(I)}(M/fM) = 0`, then
`H^i_{V(I)}(M) = 0`.

Exactness of `H^i_{V(I)}(M) →^f H^i_{V(I)}(M) → H^i_{V(I)}(M/fM)` makes multiplication by `f`
surjective once the third term vanishes, and a finite module over a local ring with
`f • N = N` for `f` in the maximal ideal is zero by Nakayama. -/
theorem isZero_localCohomology_of_finite_of_isZero_quotSMulTop (I : Ideal A) {f : A}
    (hf : f ∈ IsLocalRing.maximalIdeal A) (M : ModuleCat.{u} A)
    (hreg : IsSMulRegular (M : Type u) f) (i : ℤ)
    (hfin : Module.Finite A (localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i))
    (hquot : IsZero (localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (QuotSMulTop f (M : Type u)))) i)) :
    IsZero (localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) := by
  set T := PrimeSpectrum.zeroLocus (I : Set A) with hT
  set N := localCohomologyWithSupportIn.{u, 0} A T
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i with hNdef
  have hS := smulShortComplex_shortExact.{u, 0} hreg
  have hex := localCohomology_exact₂.{u, 0} T hS i
  -- the second map of the exact sequence is zero, its target being zero
  have hg0 : localCohomologyMap.{u, 0} A T i (smulShortComplex.{u, 0} f M).g = 0 :=
    hquot.eq_of_tgt _ _
  have hrange := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hex
  have hker : LinearMap.ker
      (localCohomologyMap.{u, 0} A T i (smulShortComplex.{u, 0} f M).g).hom = ⊤ := by
    rw [hg0]
    simp
  -- hence the first map, multiplication by `f`, is surjective
  have hsurj : Function.Surjective
      (localCohomologyMap.{u, 0} A T i (smulShortComplex.{u, 0} f M).f).hom :=
    LinearMap.range_eq_top.mp (hrange.trans hker)
  have hval : localCohomologyMap.{u, 0} A T i (smulShortComplex.{u, 0} f M).f = f • 𝟙 N :=
    localCohomologyMap_smul_id A T i M f
  rw [hval] at hsurj
  -- so `f • N = N`
  have htop : f • (⊤ : Submodule A (N : Type u)) = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    obtain ⟨y, hy⟩ := hsurj x
    exact (Submodule.mem_smul_pointwise_iff_exists x f ⊤).mpr ⟨y, Submodule.mem_top, hy⟩
  have hfg : (⊤ : Submodule A (N : Type u)).FG := Module.finite_def.mp hfin
  have hbot : (⊤ : Submodule A (N : Type u)) = ⊥ :=
    Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator hfg htop.symm
      (IsLocalRing.maximalIdeal_le_jacobson _ hf)
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ ?_⟩
  have hz : ∀ x : (N : Type u), x = 0 := fun x ↦ by
    have hx : x ∈ (⊥ : Submodule A (N : Type u)) := hbot ▸ Submodule.mem_top
    simpa using hx
  rw [hz a, hz b]

end Stacks.LocalCohomology

end
