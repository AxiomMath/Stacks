module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppTheorem

/-!
# Tag 09II from Epp's theorem

Tag 09II — an extension of discrete valuation rings `A → B` with `B` essentially of finite type
over `A` admits a finite extension of the base fraction field which is a *solution* — is assembled
in `EliminateRamificationSolution.lean` as
`Stacks.EliminateRamification.exists_finite_extension_isSolution_of_eppTheorem`, parameterized by
  Epp's theorem
(Tag 09F9) at two universe profiles. This file instantiates that assembly with the unconditional
09F9 provider and records the tagged endpoint.

## What this adds over the assembly it wraps

Not generality: the theorem below is *weaker* than the assembly, since a monomorphic instance at
`max …` implies the four-universe one (`Stacks.EppTheorem.eppTheorem_of_monomorphic`) and not
  conversely.
It is an **interface pin**. The provider is monomorphic, because the family induction that
proves 09F9 is universe-monomorphic by design, and the two
profiles 09II consumes are `.{uA, uB, uK, uL}` and `.{uK, max uL uK, uK, max uL uK}` — so the two
monomorphic instances they reduce to sit at **different** universes, `max uA uB uK uL` and
`max uK uL`. Naming those two is the error-prone step, and stating them as hypotheses makes the
handoff checkable.

It also follows that 09F9 must be a universe-polymorphic *theorem* — one instance for
every `u` — and not as a hypothesis at some chosen `u`, which no single Lean hypothesis can cover.

## Main results

* `Stacks.EliminateRamification.exists_finite_extension_isSolution_of_eppTheorem_monomorphic` —
  **Tag 09II from
  monomorphic Epp instances.**
* `Stacks.EliminateRamification.exists_finite_extension_isSolution` — the unconditional tagged
  endpoint.

## References

* [The Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

universe uA uB uK uL v

namespace Stacks.EliminateRamification

open IsDiscreteValuationRing

/-- **Tag 09II, run off monomorphic Epp instances alone.**

`Stacks.EliminateRamification.exists_finite_extension_isSolution_of_eppTheorem` needs Epp's theorem
  at *two* universe
profiles, and it is the consumer the universe layer was built for. This says both are covered by
monomorphic instances, so a universe-polymorphic monomorphic theorem — one instance of
`EppTheorem.{u, u, u, u}` for every `u`, which is what the family induction produces — discharges
the endpoint outright.

The two monomorphic profiles are *different*: `max uA uB uK uL` for `EppTheorem.{uA, uB, uK, uL}`
and `max uK uL` for `EppTheorem.{uK, max uL uK, uK, max uL uK}`, since the second's own four
universes are `uK` and `max uL uK`. One instance at one fixed `u` does not give both and cannot,
which is why this takes two hypotheses rather than one.

An interface pin rather than a strengthening — see the module docstring — and untagged, because it
is conditional on Epp's theorem. -/
theorem exists_finite_extension_isSolution_of_eppTheorem_monomorphic
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B]
    (hMono : EppTheorem.{max uA uB uK uL, max uA uB uK uL, max uA uB uK uL, max uA uB uK uL})
    (hMonoLocal : EppTheorem.{max uK uL, max uK uL, max uK uL, max uK uL}) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK} A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} :=
  exists_finite_extension_isSolution_of_eppTheorem A B K L
    (Stacks.EppTheorem.eppTheorem_of_monomorphic hMono)
    (Stacks.EppTheorem.eppTheorem_of_monomorphic hMonoLocal)

/-- **Tag 09II.** An essentially finite type extension of discrete valuation rings admits a
finite base-field extension which is a solution. -/
@[stacks 09II]
theorem exists_finite_extension_isSolution
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Algebra.EssFiniteType A B] :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK}
        A B K L K₁,
        D.IsSolution.{uA, uB, uK, uL, uK, max uL uK, uK, max uL uK, v} :=
  exists_finite_extension_isSolution_of_eppTheorem_monomorphic A B K L
    Stacks.EppTheorem.eppTheorem_monomorphic Stacks.EppTheorem.eppTheorem_monomorphic

end Stacks.EliminateRamification

end
