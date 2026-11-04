module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.CatenaryHeight
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCutoff
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthFiniteExtension
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-!
# The local cohomology cutoff under a finite ring map

For a finite homomorphism of Noetherian rings `A → B`, extension of the ideal from `A` to `B`
does not change the local cohomology finiteness cutoff of a finite `B`-module, provided `A` is
universally catenary.

## Main results

* `Module.localCohomologyCutoff_map_eq` identifies the cutoff over `B` with the cutoff of the
  same module over `A`.

## Implementation notes

The `A`-module structure on `M`, together with `IsScalarTower A B M`, records restriction of
scalars along the given algebra structure. The extended ideal is `Ideal.map (algebraMap A B) I`.

`A`, `B` and `M` live in three independent universes, as the statement has no universe content,
and this costs no work: `Ideal.quotient_height_eq_of_finite_integral` already holds for `A` and
`B` in independent universes, because the dimension formula `height_add_trdeg_residue_eq` behind
it does. The hypothesis `Ring.IsUniversallyCatenary A` is consumed in exactly the one-universe
form in which it is stated — the finite-type `A`-algebra it is applied to is a quotient of `A`,
which lives in `A`'s universe.

## References

* [Stacks Project, Tag 0BJS](https://stacks.math.columbia.edu/tag/0BJS)
-/

@[expose] public section

universe u v w

namespace Module

/-- Extending an ideal along a finite map does not increase the local cohomology cutoff. -/
private theorem localCohomologyCutoff_map_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]
    (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (hA : Ring.IsUniversallyCatenary A) :
    Stacks.LocalCohomology.localCohomologyCutoff B (Ideal.map (algebraMap A B) I) M ≤
      Stacks.LocalCohomology.localCohomologyCutoff A I M := by
  classical
  let J := Ideal.map (algebraMap A B) I
  have : Algebra.IsIntegral A B := .of_finite A B
  have hBterms := (Stacks.LocalCohomology.le_localCohomologyCutoff_iff B J M
    (Stacks.LocalCohomology.localCohomologyCutoff B J M)).mp le_rfl
  refine (Stacks.LocalCohomology.le_localCohomologyCutoff_iff A I M _).2 ?_
  intro p q hp hq hpq
  rw [depth_eq_iInf_depth_localized_algebra (A := A) (B := B) (M := M) p.asIdeal,
    ENat.iInf_add]
  refine le_iInf fun Pm => ?_
  let P := Pm.asIdeal.under B
  have hPprime : P.IsPrime := inferInstance
  have hPover : P.comap (algebraMap A B) = p.asIdeal :=
    localized_maximal_contracts_to_prime p.asIdeal Pm
  obtain ⟨Q, hPQ, hQprime, hQover⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q.asIdeal P
      (by simpa [hPover] using hpq)
  have : P.LiesOver p.asIdeal := ⟨hPover.symm⟩
  have : Q.LiesOver q.asIdeal := ⟨hQover.symm⟩
  have hJP : ¬ J ≤ P := fun h => hp (by simpa [hPover] using Ideal.map_le_iff_le_comap.mp h)
  have hJQ : J ≤ Q := Ideal.map_le_iff_le_comap.mpr (by simpa [hQover] using hq)
  have htermB := hBterms ⟨P, hPprime⟩ ⟨Q, hQprime⟩ hJP hJQ hPQ
  have hheight := Ideal.quotient_height_eq_of_finite_integral hA hpq hPQ
  have hdepth := depth_localized_maximal_eq (A := A) (B := B) (M := M) p.asIdeal Pm
  have htermEq :
      Module.depth (Localization.AtPrime Pm.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Pm.asIdeal))
        (LocalizedModule Pm.asIdeal.primeCompl
          (LocalizedModule (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) M)) =
      Module.depth (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl M) := by
    simpa only [P] using hdepth
  rwa [← htermEq, hheight] at htermB

/-- Extending an ideal along a finite map does not decrease the local cohomology cutoff. -/
private theorem le_localCohomologyCutoff_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]
    (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (hA : Ring.IsUniversallyCatenary A) :
    Stacks.LocalCohomology.localCohomologyCutoff A I M ≤
      Stacks.LocalCohomology.localCohomologyCutoff B (Ideal.map (algebraMap A B) I) M := by
  classical
  have : Algebra.IsIntegral A B := .of_finite A B
  refine (Stacks.LocalCohomology.le_localCohomologyCutoff_iff B _ M _).2 ?_
  intro P Q hJP hJQ hPQ
  let p := P.asIdeal.comap (algebraMap A B)
  let q := Q.asIdeal.comap (algebraMap A B)
  have hpprime : p.IsPrime := Ideal.comap_isPrime _ _
  have hqprime : q.IsPrime := Ideal.comap_isPrime _ _
  have hp : ¬ I ≤ p := fun h => hJP (Ideal.map_le_iff_le_comap.mpr h)
  have hq : I ≤ q := by simpa [p, q] using Ideal.map_le_iff_le_comap.mp hJQ
  have hpq' : p ≤ q := Ideal.comap_mono hPQ
  have : P.asIdeal.LiesOver p := ⟨rfl⟩
  have : Q.asIdeal.LiesOver q := ⟨rfl⟩
  calc
    Stacks.LocalCohomology.localCohomologyCutoff A I M ≤
        Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (LocalizedModule p.primeCompl M) +
          (q.map (Ideal.Quotient.mk p)).height :=
      Stacks.LocalCohomology.localCohomologyCutoff_le A I M ⟨p, hpprime⟩ ⟨q, hqprime⟩ hp hq hpq'
    _ ≤ Module.depth (Localization.AtPrime P.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal))
            (LocalizedModule P.asIdeal.primeCompl M) +
          (Q.asIdeal.map (Ideal.Quotient.mk P.asIdeal)).height :=
      add_le_add (depth_le_depth_at_prime_over (A := A) (B := B) (M := M) p P.asIdeal rfl)
        (Ideal.quotient_height_eq_of_finite_integral hA hpq' hPQ).symm.le

/-- For a finite homomorphism of Noetherian rings, extension of an ideal does not change the
local cohomology finiteness cutoff of a finite module if the source is universally catenary. -/
@[stacks 0BJS]
theorem localCohomologyCutoff_map_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]
    (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (hA : Ring.IsUniversallyCatenary A) :
    Stacks.LocalCohomology.localCohomologyCutoff B (Ideal.map (algebraMap A B) I) M =
      Stacks.LocalCohomology.localCohomologyCutoff A I M :=
  le_antisymm (localCohomologyCutoff_map_le I M hA) (le_localCohomologyCutoff_map I M hA)

end Module
