module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ComplementTildeAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAlgebraizationInput
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternative

/-!
# Condition (2) of Stacks 0EIF at the associated points of the sheaf

Condition (2) of Stacks 0EIF is a condition on the associated points of the coherent module `F`
on `U = Spec(A) ∖ V(𝔞)`; the library's Stacks 0EFL, and therefore
`Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement`, takes it at
the associated primes of a finite `A`-module. For `F = M̃|_U` the two are the same condition, and
this file says so and then restates the first half of the source's proof with condition (2) in
the source's own form.

The only thing needed beyond
`Stacks.LocalCohomology.mem_associatedPoints_complementTilde_iff` is that a prime satisfying the
hypotheses of condition (2) automatically lies in `U`: the condition is only invoked at primes
`𝔭` whose closure meets `V(I)` outside `V(𝔞)`, so there is a prime `𝔮 ⊇ 𝔭` with `𝔞 ⊄ 𝔮`, and
`𝔞 ⊆ 𝔭` would force `𝔞 ⊆ 𝔮`. So no confinement hypothesis has to be added on the ring side.

## Main results

* `Stacks.Algebraization.closureLocalDimension_associatedPrimes_of_associatedPointsDimension` —
  condition (2) of Stacks 0EIF for `M̃|_U` gives the dimension bound of Stacks 0EFL at the
  associated primes of `M`.
* `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf` —
  **the first half of the source's proof of Stacks 0EIF, with condition (2) in the source's
  form**: for a finite module `M` over an `I`-adically complete Noetherian ring with a dualizing
  complex, condition (2) read at the associated points of `M̃|_U` together with condition (3) in
  its ring-theoretic form produces the ideal `J₀ ⊆ 𝔞` of Stacks 0EFL with
  `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` for which `Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)` is an isomorphism, where
  `V = Spec(A) ∖ V(J₀)`.

## Implementation notes

The cohomological-dimension bound `d` of Stacks 0EFL is instantiated at `cd(A, I)` itself rather
than at an arbitrary upper bound. Condition (2) of Stacks 0EIF is the strict inequality
`cd(A, I) + 1 < dim(𝒪_{closure {𝔭}, 𝔮})`, and the hypothesis Stacks 0EFL wants is the same
inequality with `d` in place of `cd(A, I)`; those agree when `d = cd(A, I)` and the implication
runs the wrong way for a strictly larger `d`, so the bound is not left free here.

Condition (3) is still taken in its ring-theoretic form, as is the pair of extreme values of the
dimension function. Translating condition (3)(a) — Serre's `(S₁)` for the restriction of `F` to
`U ∖ V(I)` — into the vanishing of `Module.supportDim` of the localizations `M_𝔭` is a separate
bridge, and under condition (3)(a) the existence of the extreme values is the boundedness of a
dimension function on the spectrum of a Noetherian ring with a dualizing complex, which this
library has only for the maximum and only on a Noetherian scheme
(`Stacks.Algebraization.exists_max_dimensionFunction_on_closed`).

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Condition (2) of Stacks 0EIF for `M̃|_U` is the dimension bound of Stacks 0EFL at the
associated primes of `M`.** The associated points of `M̃|_U` are the associated primes of `M`
lying in `U`, and a prime at which condition (2) is invoked lies in `U` automatically: its
closure is required to meet `V(I)` outside `V(𝔞)`, so some larger prime avoids `𝔞`, which `𝔞 ⊆ 𝔭`
would make impossible. -/
theorem closureLocalDimension_associatedPrimes_of_associatedPointsDimension
    (I a : Ideal A) (M : ModuleCat.{u} A)
    (h : AssociatedPointsClosureDimensionBound A I a
      (complementTilde A a M : (complementZeroLocus A a : Scheme).Modules))
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M) (hpI : ¬ I ≤ p.asIdeal)
    (hmeet : ∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal)
    (z : PrimeSpectrum A) (hpz : p.asIdeal ≤ z.asIdeal) (haz : a ≤ z.asIdeal) :
    ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
      krullDimToEInt (closureLocalDimension A p z) := by
  -- the prime lies in `U`, because a prime above it avoids `𝔞`
  obtain ⟨y, hpy, hyI, hya⟩ := hmeet
  have hpa : ¬ a ≤ p.asIdeal := fun hle => hya (hle.trans hpy)
  exact h ⟨p, hpa⟩ ((mem_associatedPoints_complementTilde_iff A a M ⟨p, hpa⟩).2 hp) hpI
    ⟨y, hpy, hyI, hya⟩ z hpz haz

/-- **The first half of the source's proof of Stacks 0EIF, with condition (2) in the source's
form.** Let `I` and `𝔞` be ideals of a Noetherian ring `A` which is `I`-adically complete and
admits a dualizing complex, let `M` be a finite `A`-module and let `δ` be a dimension function
with greatest value `δmax` and least value `δmin` on `V(𝔞) ∩ V(I)`. Assume

* condition (2) of Stacks 0EIF, read at the associated points of the coherent module `M̃|_U` on
  `U = Spec(A) ∖ V(𝔞)` exactly as the source states it, and
* condition (3) of Stacks 0EIF in its ring-theoretic form.

Then there is an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` such that, for every
localization triangle datum of `J₀`, the unit of derived `I`-adic completion is invertible on
`H⁰` of the derived sections of `M̃` on `V = Spec(A) ∖ V(J₀)`:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism.

This is `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement` with
its dimension bound discharged from the sheaf-level condition (2), and with the cohomological
dimension taken at `cd(A, I)` itself. What stands between it and Stacks 0EIF is named in the
coverage note of `Stacks.Algebraization.isIso_comparisonMap_iff_realized`: the identification of
`H⁰(RΓ(V, M̃)^∧)` with `lim H⁰(U, M̃/Iⁿ M̃)`, which is Stacks 0BLX. -/
theorem exists_ideal_isIso_homology_zero_completionUnit_complement_of_sheaf
    (I a : Ideal A)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hδ : IsDimensionFunctionProp δ)
    (hmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (hdim : AssociatedPointsClosureDimensionBound A I a
      (complementTilde A a (ModuleCat.of A M) :
        (complementZeroLocus A a : Scheme).Modules))
    (hthird :
      (∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → ¬ I ≤ p.asIdeal →
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞)) ∨
      δmax ≤ δmin + 2) :
    ∃ J₀ : Ideal A, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
        ∀ D : Stacks.LocalCohomology.LocalizationTriangleData.{u, u} A J₀
          J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj (ModuleCat.of A M)))) :=
  exists_ideal_isIso_homology_zero_completionUnit_complement I a
    (cohomologicalDimension A I I.fg_of_isNoetherianRing) (M := M) omega δ δmax δmin hcomplete
    hdualizing le_rfl hδ hmax hmin
    (fun p hp hpI hmeet z hpz haz =>
      closureLocalDimension_associatedPrimes_of_associatedPointsDimension I a
        (ModuleCat.of A M) hdim p hp hpI hmeet z hpz haz)
    hthird

end Stacks.Algebraization

end
