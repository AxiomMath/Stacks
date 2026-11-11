module

public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.Homology.Perfect.Regular
public import StacksFrontier.RingTheory.PseudoCoherentMap.Noetherian
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

@[expose] public section

/-!
# Finite type maps from regular rings are perfect

Let `A` be a regular ring. Every finite-type `A`-algebra `B` is a perfect ring map: it is
pseudo-coherent, and `B` has finite Tor dimension as an `A`-module.

## Main results

* `Algebra.Perfect.of_finiteType_of_isRegularRing` (Stacks 067K).

## Implementation notes

`B` is isomorphic to the quotient `A[x_1, …, x_n]/I` of a presentation, which lives in the
universe of `A`; the argument runs on that quotient, and `Algebra.Perfect.equiv` carries it back to
`B`, as for Stacks 067J.

Pseudo-coherence is Stacks 067I: a regular ring is Noetherian, so a finite-type ring map out of
it is pseudo-coherent.

The rest is a finite resolution of `A[x_1, …, x_n]/I` by finite projective
`A[x_1, …, x_n]`-modules, which together with pseudo-coherence is perfectness
(`Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution`, the form of Stacks
068Y with pseudo-coherence on the right-hand side). The polynomial ring over a regular ring is
regular (`MvPolynomial.isRegularRing_of_isRegularRing`), and over a regular ring the perfect
modules are exactly the finite ones, which is Stacks 066Z
(`StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology`); the
quotient is finite over `A[x_1, …, x_n]`, and Stacks 066Q turns perfectness into the resolution.

This is why the source's hypothesis that `A` have finite Krull dimension is not needed: the
uniform bound on the length of the resolution comes from quasi-compactness of
`Spec A[x_1, …, x_n]`, inside the proof of Stacks 066Z, and not from a global dimension bound. A
regular ring of infinite Krull dimension has infinite global dimension, but each of its local
rings is a regular local ring and hence of finite global dimension, which is all 066Z uses.

The statement mentions no derived category; the proof reads Stacks 066Z and 066Q, which are stated
in the standard model.

## References

* [The Stacks Project, Lemma 15.83.5 (067K)](https://stacks.math.columbia.edu/tag/067K)
* [The Stacks Project, Tag 067I](https://stacks.math.columbia.edu/tag/067I)
* [The Stacks Project, Lemma 15.74.16 (066Z)](https://stacks.math.columbia.edu/tag/066Z)
* [The Stacks Project, Lemma 15.83.2 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
-/

open CategoryTheory CategoryTheory.Limits

namespace Algebra.Perfect

universe u v

/-! ### The theorem -/

/-- **Stacks 067K.** A finite-type algebra over a regular ring is perfect. It is a theorem and not
an instance: with Stacks 0682 (a perfect algebra is of finite presentation) it would close an
instance cycle.

The source assumes in addition that the regular ring has finite Krull dimension; that hypothesis
is not needed, because the bound on the length of the resolution is produced from
quasi-compactness of the prime spectrum of the polynomial ring rather than from a bound on its
global dimension. -/
@[stacks 067K]
public theorem of_finiteType_of_isRegularRing (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] [IsRegularRing A] [Algebra.FiniteType A B] :
    Algebra.Perfect A B := by
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  refine .equiv ?_ (Ideal.quotientKerAlgEquivOfSurjective hα)
  let Q := MvPolynomial (Fin n) A ⧸ RingHom.ker α
  let β := Ideal.Quotient.mkₐ A (RingHom.ker α)
  have : Algebra.FiniteType A Q := .of_surjective β (Ideal.Quotient.mkₐ_surjective A _)
  refine Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution.mpr
    ⟨.of_finiteType A Q, n, β, Ideal.Quotient.mkₐ_surjective A _, ?_⟩
  let : Module (MvPolynomial (Fin n) A) Q := Module.compHom _ β.toRingHom
  let βₗ : MvPolynomial (Fin n) A →ₗ[MvPolynomial (Fin n) A] Q :=
    { toFun := β
      map_add' := fun p q => map_add β p q
      map_smul' := fun p q => map_mul β p q }
  have : Module.Finite (MvPolynomial (Fin n) A) Q :=
    Module.Finite.of_surjective βₗ (Ideal.Quotient.mkₐ_surjective A _)
  rw [← StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution]
  exact (StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology
    (R := MvPolynomial (Fin n) A)).1 _ |>.2 inferInstance

end Algebra.Perfect
