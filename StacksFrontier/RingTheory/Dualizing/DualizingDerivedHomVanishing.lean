module

public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# `Ext` into a dualizing complex vanishes outside a fixed window

Let `ω` be a dualizing complex over a Noetherian ring `A`. Then `ω` has finite injective
dimension: it has injective amplitude `[a, b]` for some integers `a ≤ b`. For a module `N` in
degree `0`, derived Hom `RHom_A(N, ω)` is then concentrated in degrees `[a, b]`. So
`Ext^j_A(N, ω) = H^j RHom_A(N, ω)` vanishes for every `j` outside `[a, b]`, and the window does not
depend on `N`.

This is the finiteness of the set of degrees `j` used in the uniformity step of the proof of
Stacks 0EFX (local duality at the primes of `T`), which in turn feeds Theorem 0EIE.

## Main results

* `Dualizing.exists_isZero_homology_dualizingDerivedHom_of_lt_or_gt`: there are `a, b` such that
  `Ext^j_A(N, ω) = 0` for every `A`-module `N` and every `j < a` or `j > b`.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

universe u

/-- **`Ext` into a dualizing complex vanishes outside a fixed window.** If `ω` is a dualizing
complex over a Noetherian ring `A`, there are integers `a` and `b` such that
`Ext^j_A(N, ω) = H^j RHom_A(N, ω)` vanishes for every `A`-module `N` and every `j < a` or
`j > b`. One can take for `[a, b]` any injective amplitude of `ω`; `N`, placed in degree `0`, is
cohomologically both `≥ 0` and `≤ 0`. -/
theorem exists_isZero_homology_dualizingDerivedHom_of_lt_or_gt {A : Type u} [CommRing A]
    [IsNoetherianRing A] (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) :
    ∃ a b : ℤ, ∀ (N : ModuleCat.{u} A) (j : ℤ), (j < a ∨ b < j) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) := by
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  refine ⟨a, b, fun N j hj => ?_⟩
  have hGE := dualizingDerivedHom_isGE_of_isLE.{u, u} A ω
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 0 a b inferInstance hamp
  have hLE := dualizingDerivedHom_isLE_of_isGE.{u, u} A ω
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) 0 a b inferInstance hamp
  rw [sub_zero] at hGE hLE
  rcases hj with hj | hj
  · exact DerivedCategory.isZero_of_isGE _ a j hj
  · exact DerivedCategory.isZero_of_isLE _ b j hj

end Dualizing

end
