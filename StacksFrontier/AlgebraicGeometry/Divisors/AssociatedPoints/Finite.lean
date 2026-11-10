module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the associated points on a quasi-compact open

A coherent module on a locally Noetherian scheme has only finitely many associated points in
any quasi-compact open subset.

## Main results

* `AlgebraicGeometry.associatedPoints_inter_finite` is that finiteness statement.

## Implementation notes

Quasi-compactness of an open `U` is expressed as `IsCompact (U : Set X)`. On an affine open the
associated points of the sheaf correspond injectively to the associated primes of the module of
sections (Stacks tag 02OK), which are finitely many because that module is finite over a
Noetherian ring; a quasi-compact open is covered by finitely many affine opens.

## References

* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A coherent module on a locally Noetherian scheme has finitely many associated points in an
affine open. -/
private lemma associatedPoints_inter_affine_finite {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hU : IsAffineOpen U) :
    (Stacks.Divisors.associatedPoints F ∩ (U : Set X)).Finite := by
  classical
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfin : Module.Finite Γ(X, U) Γ(F, U) := moduleFinite_sections_on_affine F U hU
  let p : U → Ideal Γ(X, U) := fun x => (hU.primeIdealOf x).asIdeal
  have hp_inj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    calc
      (x : X) = hU.fromSpec (hU.primeIdealOf x) := (hU.fromSpec_primeIdealOf x).symm
      _ = hU.fromSpec (hU.primeIdealOf y) := congrArg hU.fromSpec (PrimeSpectrum.ext hxy)
      _ = (y : X) := hU.fromSpec_primeIdealOf y
  have hpre : (p ⁻¹' associatedPrimes Γ(X, U) Γ(F, U)).Finite :=
    (associatedPrimes.finite Γ(X, U) Γ(F, U)).preimage hp_inj.injOn
  refine (hpre.image Subtype.val).subset ?_
  rintro x ⟨hxAss, hxU⟩
  refine ⟨⟨x, hxU⟩, ?_, rfl⟩
  change p ⟨x, hxU⟩ ∈ associatedPrimes Γ(X, U) Γ(F, U)
  rw [← isAssociatedPrimeStacks_iff_mem_associatedPrimes]
  exact (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian F U hU hxU).mpr
    ((Stacks.Divisors.mem_associatedPoints_iff F x).mp hxAss)

/-- **Stacks Project, Tag 05AF.** A coherent module on a locally Noetherian scheme has only
finitely many associated points in a quasi-compact open subset. -/
@[stacks 05AF]
theorem associatedPoints_inter_finite {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    (Stacks.Divisors.associatedPoints F ∩ (U : Set X)).Finite := by
  classical
  obtain ⟨Us, hUs, hUs_finite, hUs_sup⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact hU
  have : Fintype Us := hUs_finite.fintype
  refine (Set.finite_iUnion fun i : Us =>
    associatedPoints_inter_affine_finite F i.1 (hUs i.2)).subset ?_
  rintro x ⟨hxAss, hxU⟩
  rw [hUs_sup, sSup_eq_iSup] at hxU
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨h, hxi⟩ := Opens.mem_iSup.mp hi
  exact Set.mem_iUnion.mpr ⟨⟨i, h⟩, hxAss, hxi⟩

end AlgebraicGeometry
