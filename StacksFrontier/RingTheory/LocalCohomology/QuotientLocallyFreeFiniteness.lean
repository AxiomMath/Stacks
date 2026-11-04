module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.SupportReduction
public import StacksFrontier.RingTheory.LocalCohomology.FiniteLocallyFreeFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of local cohomology of generically locally free modules over a quotient

Let `A` be a Noetherian ring, `a, J ⊆ A` ideals, `Z = V(a)` and `n ≥ 0`. Write `B = A ⧸ J` and
`q : A ⟶ B` for the quotient map. A `B`-module `N` is also an `A`-module, and the two local
cohomology modules one can form from it agree:

$$ H^i_{V(a)}(N_A) \;=\; H^i_{V(aB)}(N)_A, $$

which is [Stacks, Tag 0BJB]. This file transports [Stacks, Tag 0BPY] across that identification.
The outcome is that `H^i_{V(a)}(N)` is a finite `A`-module for `0 ≤ i ≤ n` as soon as

* the `A`-modules `H^i_{V(a)}(A ⧸ J)` are finite for `0 ≤ i ≤ n`, and
* `N` is a finite `B`-module whose localization `N_g` is a finite locally free `B_g`-module for
  every `g ∈ aB`.

The hypothesis on `A ⧸ J` is exactly the hypothesis of Tag 0BPY over the ring `B` applied to `B`
itself, again read across Tag 0BJB; so the proof is: move the hypothesis from `A` to `B`, apply
Tag 0BPY over `B`, and move the conclusion from `B` back to `A`.

Finiteness itself moves between the two rings in both directions, because a finite module over a
quotient of `A` is a finite `A`-module and conversely — the content of
`Stacks.LocalCohomology.finite_restrictScalars_quotient_iff` below.

## Main results

* `Stacks.LocalCohomology.finite_restrictScalars_quotient_iff` — a `A ⧸ J`-module is finite over
  `A ⧸ J` exactly when it is finite over `A`.
* **[Stacks, Tag 0BPY] across a quotient map:**
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_restrictScalars_of_isFiniteLocallyFree`

## Implementation notes

Local cohomology appears in two models. The statements use the supported-sections model
`Stacks.LocalCohomology.localCohomologyWithSupportIn`, applied to a module placed in degree zero
with support the closed set `V(a)`, which is the model in which Tag 0BPY is phrased. Tag 0BJB is
available in the coreflection model `Stacks.LocalCohomology.localCohomologyModule`, so the
comparison `Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`, which is
an isomorphism over a Noetherian ring, is inserted over `A` and over `A ⧸ J`.

Degree zero needs none of this: `H^0_T(M)` is the submodule of `T`-supported sections of `M`, so
its finiteness for `M` finite over a Noetherian ring is
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_zero`, for an arbitrary subset `T` of
the prime spectrum and with no locally-free hypothesis.

## References

* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 0BJB](https://stacks.math.columbia.edu/tag/0BJB)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- A module over a quotient `A ⧸ J` is finite over `A ⧸ J` exactly when it is finite after
restriction of scalars to `A`.

A finite `A`-generating set of the restriction generates over the larger ring `A ⧸ J`; conversely
`A ⧸ J` is a finite `A`-module, so finiteness composes along `A ⟶ A ⧸ J`. -/
@[ega "0 7.2.12" "more general"]
theorem finite_restrictScalars_quotient_iff {A : Type u} [CommRing A] (J : Ideal A)
    (N : ModuleCat.{u} (A ⧸ J)) :
    Module.Finite A ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N) ↔
      Module.Finite (A ⧸ J) N := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact _root_.Dualizing.finite_of_restrictScalars_finite (Ideal.Quotient.mk J) N
  · let : Module A (N : Type u) := Module.compHom _ (Ideal.Quotient.mk J)
    have : IsScalarTower A (A ⧸ J) (N : Type u) := ⟨fun r s x ↦ by
      show (Ideal.Quotient.mk J r * s) • x = Ideal.Quotient.mk J r • s • x
      exact mul_smul _ _ _⟩
    have : Module.Finite A (N : Type u) := Module.Finite.trans (R := A) (A ⧸ J) _
    exact inferInstanceAs (Module.Finite A (N : Type u))

/-- **[Stacks, Tag 0BJB] in the supported-sections model, degreewise.** For ideals `a, J` of a
Noetherian ring `A` and a module `N` over `A ⧸ J`, the degree-`i` local cohomology with support
in `V(a)` of `N` viewed as an `A`-module is the restriction to `A` of the degree-`i` local
cohomology of `N` with support in `V(a(A ⧸ J))`.

Both sides are compared with the coreflection model, where Tag 0BJB is available. -/
private def localCohomologyWithSupportInRestrictScalarsQuotientIso {A : Type u} [CommRing A]
    [IsNoetherianRing A] (a J : Ideal A) (N : ModuleCat.{u} (A ⧸ J)) (i : ℤ) :
    localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N)) i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj
        (localCohomologyWithSupportIn.{u, u} (A ⧸ J)
          (PrimeSpectrum.zeroLocus ((a.map (Ideal.Quotient.mk J) : Ideal (A ⧸ J)) : Set (A ⧸ J)))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ J)) 0).obj N) i) :=
  letI ha : a.FG := Ideal.fg_of_isNoetherianRing a
  localCohomologyWithSupportInIsoLocalCohomologyModule A a ha
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N) i ≪≫
    localCohomologyModuleRestrictScalarsIso (Ideal.Quotient.mk J) a ha N i ≪≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).mapIso
        (localCohomologyWithSupportInIsoLocalCohomologyModule (A ⧸ J)
          (a.map (Ideal.Quotient.mk J)) (ha.map _) N i).symm

/-- Finiteness of the local cohomology of a module over a quotient is the same question over `A`
and over `A ⧸ J`: the two local cohomology modules correspond under [Stacks, Tag 0BJB], and
finiteness passes both ways along `A ⟶ A ⧸ J`. -/
private lemma finite_localCohomologyWithSupportIn_restrictScalars_iff {A : Type u} [CommRing A]
    [IsNoetherianRing A] (a J : Ideal A) (N : ModuleCat.{u} (A ⧸ J)) (i : ℤ) :
    Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N)) i) ↔
      Module.Finite (A ⧸ J)
        (localCohomologyWithSupportIn.{u, u} (A ⧸ J)
          (PrimeSpectrum.zeroLocus ((a.map (Ideal.Quotient.mk J) : Ideal (A ⧸ J)) : Set (A ⧸ J)))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ J)) 0).obj N) i) :=
  (Module.Finite.equiv_iff
      (localCohomologyWithSupportInRestrictScalarsQuotientIso a J N i).toLinearEquiv).trans
    (finite_restrictScalars_quotient_iff J _)

/-- **[Stacks, Tag 0BPY] across a quotient map.** Let `A` be a Noetherian ring, `a, J ⊆ A` ideals,
`Z = V(a)` and `n ≥ 0`. If the `A`-modules `H^i_Z(A ⧸ J)` are finite for `0 ≤ i ≤ n`, then
`H^i_Z(N)` is a finite `A`-module for `0 ≤ i ≤ n`, for every finite `A ⧸ J`-module `N` such that
`N_g` is a finite locally free `(A ⧸ J)_g`-module for every `g ∈ a(A ⧸ J)`.

The quotient `A ⧸ J` is again Noetherian, and by [Stacks, Tag 0BJB] the local cohomology of a
module over `A ⧸ J` with support in `V(a)` is its local cohomology with support in `V(a(A ⧸ J))`,
restricted to `A`. This carries the hypothesis on `A ⧸ J`, which is a module over itself, to the
hypothesis of Tag 0BPY over the ring `A ⧸ J`; the conclusion of that tag over `A ⧸ J` then
travels back along the same identification. -/
theorem finite_localCohomologyWithSupportIn_restrictScalars_of_isFiniteLocallyFree
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a J : Ideal A) (n : ℕ)
    (hA : ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ J))) (i : ℤ)))
    (N : ModuleCat.{u} (A ⧸ J)) [Module.Finite (A ⧸ J) N]
    (hN : ∀ g ∈ a.map (Ideal.Quotient.mk J),
      Module.IsFiniteLocallyFree (Localization.Away g) (LocalizedModule.Away g (N : Type u))) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N)) (i : ℤ)) := by
  have hquot : ∀ i : ℕ, i ≤ n → Module.Finite (A ⧸ J)
      (localCohomologyWithSupportIn.{u, u} (A ⧸ J)
        (PrimeSpectrum.zeroLocus ((a.map (Ideal.Quotient.mk J) : Ideal (A ⧸ J)) : Set (A ⧸ J)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ J)) 0).obj
          (ModuleCat.of (A ⧸ J) (A ⧸ J))) (i : ℤ)) := fun i hi ↦
    (finite_localCohomologyWithSupportIn_restrictScalars_iff a J
      (ModuleCat.of (A ⧸ J) (A ⧸ J)) (i : ℤ)).mp (hA i hi)
  intro i hi
  exact (finite_localCohomologyWithSupportIn_restrictScalars_iff a J N (i : ℤ)).mpr
    (localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away (A ⧸ J)
      (a.map (Ideal.Quotient.mk J)) n hquot N hN i hi)

end Stacks.LocalCohomology

end
