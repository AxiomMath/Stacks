module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBoundUpper
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionVariableCount
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingFiniteTorDimension

/-!
# Tor amplitude of a relative dualizing complex, bounded by the number of variables

Let `R → A` be a flat finite type homomorphism of Noetherian rings and let
`R → P = R[x_1, …, x_n] → A` be a polynomial presentation of it.  Then the relative dualizing
complex `ω^•_{A/R} = f^!(R)` has Tor amplitude in `[-n, 0]` as a complex of `R`-modules.

This is the Tor-amplitude clause of [Stacks, Tag 0E9Q] at the bound `d = n`; every fibre of
`Spec(A) → Spec(R)` has dimension at most `n`, being cut out in `n`-dimensional affine space over
a residue field (`Dualizing.PolynomialPresentation.relativeDimension_le_variableCount` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionVariableCount`).  The clause for an
arbitrary bound `d` on the fibre dimensions is
`Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitude`; the statements here
are its special cases `d ≥ n`, proved by a route that performs no base change.

## Main results

In the namespace `Dualizing.PolynomialPresentation`:

* `relativeDualizingComplex_hasTorAmplitude_neg_variableCount` — `ω^•_{A/R}` has Tor amplitude in
  `[-n, 0]` over `R`.
* `relativeDualizingComplex_hasTorAmplitude_of_variableCount_le` — the same read at any bound
  `d ≥ n`.
* `relativeDualizingComplex_relativeDimension_le_and_hasTorAmplitude_of_variableCount_le` — for
  any bound `d ≥ n`, every fibre of `Spec(A) → Spec(R)` has dimension at most `d`, and
  `ω^•_{A/R}` has Tor amplitude in `[-d, 0]` over `R`.

## Implementation notes

The route is the first half of the source's proof of [Stacks, Tag 0E9Q], run with the
cohomological window tracked throughout rather than existentially quantified.  Flatness of
`R → A` and [Stacks, Tag 068X] make `A`, read in `D(P)`, a pseudo-coherent object of Tor
amplitude in `[-n, 0]` over `P` — this is
`Dualizing.isPerfect_and_hasFlatRepresentative_single_restrictScalars_ulift_of_flat`.  By
[Stacks, Tag 0658] it therefore has a representative by finite projective `P`-modules in degrees
`[-n, 0]`, whose `P`-linear dual represents `RHom_P(A, P)` in degrees `[0, n]`; the `n`-fold
shift that is `f^!(R)` puts that back in `[-n, 0]`, and `P` is free over `R`, so restriction of
scalars turns it into a complex of flat `R`-modules in `[-n, 0]`.  By [Stacks, Tag 0654] that is
Tor amplitude in `[-n, 0]` over `R`.  The two tracked steps are, in the namespace
`Dualizing.PolynomialPresentation`,
`relativeDualizingComplex_restrictScalars_exists_finiteProjectiveRepresentative` and
`relativeDualizingComplex_hasTorAmplitude`.

As everywhere in `StacksDraft.RingTheory.Dualizing.UpperShriek` the relative dualizing complex is
read at an arbitrary polynomial presentation, `f^!` being defined only up to isomorphism; the
bound `n` is that presentation's number of variables.

The module `A` carried by [Stacks, Tag 068X] at the presentation is `ULift A`, so that the
statement stays inside one universe; the two transports below move pseudo-coherence and the flat
representative from there to `A` itself read in `D(P)`, which is the form the tracked steps take
their hypotheses in.

## References

* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Pseudo-coherence only depends on the isomorphism class of an object of `D(R)`. -/
private theorem isPseudoCoherent_of_iso {S : Type u} [Ring S]
    {X Y : DerivedCategory (ModuleCat.{u} S)} (e : X ≅ Y)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent X) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent Y := by
  obtain ⟨E, hE, ⟨f⟩⟩ := h
  exact ⟨E, hE, ⟨f ≪≫ e⟩⟩

/-- Having a flat representative in `[a, b]` only depends on the isomorphism class of an object
of `D(S)`. -/
private theorem perfect_hasFlatRepresentative_of_iso {S : Type u} [CommRing S]
    {X Y : DerivedCategory (ModuleCat.{u} S)} (e : X ≅ Y) {a b : ℤ}
    (h : StacksDraft.Perfect.HasFlatRepresentative.{u, u} X a b) :
    StacksDraft.Perfect.HasFlatRepresentative.{u, u} Y a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨f⟩⟩ := h
  exact ⟨E, hflat, hGE, hLE, ⟨e.symm ≪≫ f⟩⟩

/-- A flat representative in `[a, b]` is one in any wider window. -/
private theorem torAmplitude_hasFlatRepresentative_of_subset {S : Type u} [CommRing S]
    {X : DerivedCategory (ModuleCat.{u} S)} {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : StacksDraft.TorAmplitude.HasFlatRepresentative X a b) :
    StacksDraft.TorAmplitude.HasFlatRepresentative X a' b' := by
  obtain ⟨E, hflat, hGE, hLE, hiso⟩ := h
  let : E.IsStrictlyGE a := hGE
  let : E.IsStrictlyLE b := hLE
  exact ⟨E, hflat, E.isStrictlyGE_of_ge a' a ha, E.isStrictlyLE_of_le b b' hb, hiso⟩

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
  [Algebra R A] [Module.Flat R A]

/-- `A` itself, read in `D(P)` along the presenting surjection, is isomorphic to `ULift A` read
there: the two differ by the `A`-linear equivalence `A ≃ ULift A`. -/
private noncomputable def singleRestrictScalarsULiftIso (p : PolynomialPresentation
    (algebraMap R A)) :
    (ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) :=
  ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).mapIso
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapIso
        (LinearEquiv.toModuleIso (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).symm))

/-- **The Tor amplitude of `ω^•_{A/R}` is in `[-n, 0]`.**  Let `R → A` be a flat
finite type homomorphism of Noetherian rings and let `R → P = R[x_1, …, x_n] → A` be a polynomial
presentation.  Then `ω^•_{A/R} = f^!(R)` has Tor amplitude in `[-n, 0]` as a complex of
`R`-modules.

The route is the first half of the source's proof of [Stacks, Tag 0E9Q], with the window tracked:
by [Stacks, Tag 068X] `A` read in `D(P)` is pseudo-coherent of Tor amplitude in `[-n, 0]` over
`P`, so by [Stacks, Tag 0658] it has a finite projective representative in those degrees, whose
dual represents `RHom_P(A, P)` in `[0, n]`; the `n`-fold shift that is `f^!(R)` returns to
`[-n, 0]`, and `P` is free over `R`, so restriction of scalars gives a complex of flat
`R`-modules in `[-n, 0]`, which is Tor amplitude in `[-n, 0]` by [Stacks, Tag 0654]. -/
theorem relativeDualizingComplex_hasTorAmplitude_neg_variableCount
    (p : PolynomialPresentation (algebraMap R A)) :
    StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
      (-(p.variableCount : ℤ)) 0 := by
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let instM₀ : Module p.Poly (M₀ : Type u) := M₀.isModule
  have hM₀ : Module.Finite p.Poly (M₀ : Type u) := finite_restrictScalars_ulift p
  have hpc := isPseudoCoherent_of_iso (p.singleRestrictScalarsULiftIso).symm
    (isPseudoCoherent_single_of_finite M₀)
  have hamp := perfect_hasFlatRepresentative_of_iso (p.singleRestrictScalarsULiftIso).symm
    (isPerfect_and_hasFlatRepresentative_single_restrictScalars_ulift_of_flat p).2
  simpa only [neg_zero, zero_sub, neg_neg, sub_self] using
    p.relativeDualizingComplex_hasTorAmplitude (-(p.variableCount : ℤ)) 0 hpc hamp

/-- **The Tor amplitude of `ω^•_{A/R}` at any bound at least the number of variables.**  Let
`R → A` be a flat finite type homomorphism of Noetherian rings presented in `n`
variables, and let `d ≥ n`.  Then `ω^•_{A/R} = f^!(R)` has Tor amplitude in `[-d, 0]` as a
complex of `R`-modules.

A flat representative in `[-n, 0]` is one in the wider window `[-d, 0]`, so this is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_hasTorAmplitude_neg_variableCount`
read through [Stacks, Tag 0654].  The hypothesis `n ≤ d` implies that every fibre of
`Spec(A) → Spec(R)` has dimension at most `d`
(`Dualizing.PolynomialPresentation.relativeDimension_le_of_variableCount_le`), so this is a
special case of the Tor-amplitude clause of [Stacks, Tag 0E9Q],
`Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le`. -/
theorem relativeDualizingComplex_hasTorAmplitude_of_variableCount_le
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ) (hd : p.variableCount ≤ d) :
    StacksDraft.TorAmplitude.HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
      (-(d : ℤ)) 0 := by
  have h := p.relativeDualizingComplex_hasTorAmplitude_neg_variableCount
  rw [StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)] at h ⊢
  exact torAmplitude_hasFlatRepresentative_of_subset (by omega) le_rfl h

/-- **The fibre-dimension bound and the Tor amplitude at any bound at least the number of
variables.**  Let `R → A` be a flat finite type homomorphism of Noetherian rings presented in `n`
variables, and let `d ≥ n`.  Then every fibre of `Spec(A) → Spec(R)` has dimension at most `d`,
read as `Algebra.relativeDimension R A ≤ d`, and `ω^•_{A/R} = f^!(R)` has Tor amplitude in
`[-d, 0]` as a complex of `R`-modules.  The first component is
`Dualizing.PolynomialPresentation.relativeDimension_le_of_variableCount_le` and the second is
`Dualizing.PolynomialPresentation.relativeDualizingComplex_hasTorAmplitude_of_variableCount_le`;
the Tor-amplitude clause of [Stacks, Tag 0E9Q] for an arbitrary bound is
`Dualizing.upperShriekFunctor_hasTorAmplitude_of_fiber_dimension_le`. -/
theorem relativeDualizingComplex_relativeDimension_le_and_hasTorAmplitude_of_variableCount_le
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ) (hd : p.variableCount ≤ d) :
    Algebra.relativeDimension R A ≤ (d : WithBot ℕ∞) ∧
      StacksDraft.TorAmplitude.HasTorAmplitude
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison R)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
        (-(d : ℤ)) 0 :=
  ⟨p.relativeDimension_le_of_variableCount_le d hd,
    p.relativeDualizingComplex_hasTorAmplitude_of_variableCount_le d hd⟩

end PolynomialPresentation

end Dualizing

end
