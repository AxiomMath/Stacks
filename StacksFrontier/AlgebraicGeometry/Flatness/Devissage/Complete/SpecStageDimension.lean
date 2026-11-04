module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecFiberSupportDimension
public import StacksFrontier.RingTheory.Support.Fiber
public import StacksFrontier.Topology.Dimension.Krull

/-!
# What one stage of a complete dévissage says about the fibre-support dimension

A stage of an algebraic complete dévissage of a finite module `N` over an `R`-algebra `S` at a
prime `r` of `R` (Stacks 05HZ) presents `N` as a finite module `M` over an `R`-algebra `A` which
is a quotient of `S`, with `A` finite over a smooth `R`-algebra `B`, and names a prime `lp` of `B`
in the fibre support of `M` over `r` which has a *unique* prime `up` of `A` above it; the prime
`q = up ∩ S` is then the point of `Spec S` that the stage is about. This file records two
consequences of such a stage.

The first is bookkeeping: the primes named by the stage really do lie in the fibre supports they
are supposed to. A prime in the fibre support over `B` is always the contraction of a prime in the
fibre support over `A`, by lifting along the finite map `B → A` a prime containing the annihilator
of `M`; uniqueness then identifies that lift with `up`, and contracting it to `S` lands in the
fibre support of `N` over `S`, which is exactly the image of the fibre support over `A` under
contraction along the surjection `S → A`.

The second is the dimension count that Stacks 05I0 (2) rests on. The fibre support over `B` sits
inside the whole fibre of `Spec B → Spec R` over `r`, and a local dimension never exceeds a global
one; so if the fibre of `Spec B → Spec R` has exactly the dimension that the fibre support over
`B` has *at* `lp`, those two inequalities close into equalities and the fibre support over `B` has
one and the same dimension globally and locally at `lp`. Neither the surjection `S → A` nor the
finite map `B → A` moves the dimension of the fibre support, so the fibre support of `N` over `S`
inherits both statements.

## Main results

* `Module.exists_mem_fiberSupport_comap_eq`: **along a finite map of algebras, a prime in the
  fibre support downstairs is the contraction of a prime in the fibre support upstairs.**
* `Module.mem_fiberSupport_of_unique_comap`: **the unique prime of `A` over a prime in the fibre
  support of `M` over `B` lies in the fibre support of `M` over `A`, and its contraction to `S`
  lies in the fibre support of `N` over `S`.**
* `Module.topologicalKrullDim_fiberSupport_eq_of_fiber_eq`: **if the fibre of `Spec B → Spec R`
  over `r` has the dimension that the fibre support of `M` over `B` has at `lp`, then the fibre
  support of `N` over `S` has that dimension, and has it locally at `q`.**

## Implementation notes

The lifting of a prime along the finite map is the argument internal to the proof of
`Module.topologicalKrullDim_fiberSupport_eq_of_finite`, stated here on its own:
`Ideal.exists_ideal_over_prime_of_isIntegral` applied to the contraction of the annihilator of
`M`, which is the annihilator over the lower ring by
`Module.annihilator_eq_comap_annihilator`, together with the fact that membership in the support
of a finite module is containment of the annihilator.

The two algebra maps of a stage are taken as `Algebra` instances together with the scalar towers
they satisfy, as in `Module.topologicalKrullDimAt_fiberSupport_eq_of_stage`, whose binders these
declarations copy.

The hypothesis that `up` contracts to `lp` is *not* needed for
`Module.mem_fiberSupport_of_unique_comap`: uniqueness alone pins the lifted prime down to `up`,
and the hypothesis would be an unused binder. It reappears in
`Module.topologicalKrullDim_fiberSupport_eq_of_fiber_eq`, which feeds it to
`Module.topologicalKrullDimAt_fiberSupport_eq_of_stage`.

The dimensions live in `WithBot ℕ∞`, a complete linear order, so the sandwich of inequalities is
closed by `le_antisymm`.

## References

* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

namespace Module

/-- **Along a finite map of algebras, a prime in the fibre support downstairs is the contraction
of a prime in the fibre support upstairs.** A prime `lp` of `B` in the support of the finite
module `M` contains the annihilator of `M` over `B`, which is the contraction of the annihilator
over `A`; so an integral extension has a prime of `A` above `lp` containing the annihilator over
`A`, and such a prime lies in the support of `M` over `A` and over `r`. -/
public theorem exists_mem_fiberSupport_comap_eq (R B A M : Type*) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower B A M] [Module.Finite B M] [Module.Finite A M]
    [Module.Finite B A] (r : Ideal R) [r.IsPrime] {lp : PrimeSpectrum B}
    (hlp : lp ∈ Module.fiberSupport R B M r) :
    ∃ up : PrimeSpectrum A, up ∈ Module.fiberSupport R A M r ∧
      PrimeSpectrum.comap (algebraMap B A) up = lp := by
  have hann : (Module.annihilator A M).comap (algebraMap B A) ≤ lp.asIdeal := by
    rw [← Module.annihilator_eq_comap_annihilator (R := B) (S := A) (M := M)]
    exact Module.mem_support_iff_of_finite.mp hlp.1
  obtain ⟨P, hPge, hPprime, hPcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral lp.asIdeal (Module.annihilator A M) hann
  have hP : PrimeSpectrum.comap (algebraMap B A) (⟨P, hPprime⟩ : PrimeSpectrum A) = lp :=
    PrimeSpectrum.ext hPcomap
  refine ⟨⟨P, hPprime⟩, ⟨Module.mem_support_iff_of_finite.mpr hPge, ?_⟩, hP⟩
  rw [Set.mem_preimage, ← PrimeSpectrum.comap_comap_algebraMap (B := B), hP]
  exact hlp.2

/-- **The prime of `S` under the unique prime of `A` over a prime in the fibre support of `M` over
`B` lies in the fibre support of `N` over `S`.**

Lifting `lp` along the finite map `B → A` produces a prime of `A` in the fibre support of `M` over
`r` contracting to `lp`; uniqueness identifies it with `up`, which therefore lies in that fibre
support. Contraction along the surjection `S → A` carries the fibre support of `M` over `A` onto
the fibre support of `N` over `S`, so the contraction `q` of `up` lies in the latter. -/
public theorem mem_fiberSupport_of_unique_comap {R S A B N M : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A]
    [Algebra B A] [IsScalarTower R S A] [IsScalarTower R B A] [AddCommGroup N] [Module S N]
    [AddCommGroup M] [Module S M] [Module A M] [Module B M] [IsScalarTower S A M]
    [IsScalarTower B A M] [Module.Finite A M] [Module.Finite B M] [Module.Finite B A]
    (hsurj : Function.Surjective (algebraMap S A)) (e : N ≃ₗ[S] M) (r : Ideal R) [r.IsPrime]
    {up : PrimeSpectrum A} {lp : PrimeSpectrum B} {q : PrimeSpectrum S}
    (hlpmem : lp ∈ Module.fiberSupport R B M r)
    (huniq : ∀ p' : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) p' = lp → p' = up)
    (hq : PrimeSpectrum.comap (algebraMap S A) up = q) :
    up ∈ Module.fiberSupport R A M r ∧ q ∈ Module.fiberSupport R S N r := by
  obtain ⟨up', hup'mem, hup'⟩ := Module.exists_mem_fiberSupport_comap_eq R B A M r hlpmem
  obtain rfl := huniq up' hup'
  refine ⟨hup'mem, ?_⟩
  rw [← Module.image_comap_fiberSupport_of_surjective hsurj e r, ← hq]
  exact ⟨up', hup'mem, rfl⟩

/-- **If every fibre of `Spec B → Spec R` has the local dimension of the fibre support of `M` over
`B` at `lp`, then the fibre support of `N` over `S` has that dimension, and has it locally at
`q`.**

The fibre support of `M` over `B` lies in the fibre of `Spec B → Spec R` over `r`, and its local
dimension at `lp` is at most its global dimension; the hypothesis closes the resulting chain of
inequalities, so the fibre support over `B` has the same dimension globally and locally at `lp`.
The surjection `S → A` and the finite map `B → A` leave the global dimension of the fibre support
unchanged, and the local dimension at `q` is the local dimension at `lp` through the stage. -/
public theorem topologicalKrullDim_fiberSupport_eq_of_fiber_eq {R S A B N M : Type*} [CommRing R]
    [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S A] [Algebra B A] [IsScalarTower R S A] [IsScalarTower R B A] [AddCommGroup N]
    [Module S N] [AddCommGroup M] [Module S M] [Module A M] [Module B M] [IsScalarTower S A M]
    [IsScalarTower B A M] [Module.Finite A M] [Module.Finite B M] [Module.Finite B A]
    (hsurj : Function.Surjective (algebraMap S A)) (e : N ≃ₗ[S] M) (r : Ideal R) [r.IsPrime]
    {up : PrimeSpectrum A} {lp : PrimeSpectrum B} {q : PrimeSpectrum S}
    (hlpmem : lp ∈ Module.fiberSupport R B M r)
    (hlp : PrimeSpectrum.comap (algebraMap B A) up = lp)
    (huniq : ∀ p' : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) p' = lp → p' = up)
    (hq : PrimeSpectrum.comap (algebraMap S A) up = q)
    (hqmem : q ∈ Module.fiberSupport R S N r)
    (hfib : topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹'
        {(⟨r, ‹r.IsPrime›⟩ : PrimeSpectrum R)})
      = topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩) :
    topologicalKrullDim ↥(Module.fiberSupport R S N r)
        = topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩
      ∧ topologicalKrullDimAt ↥(Module.fiberSupport R S N r) ⟨q, hqmem⟩
        = topologicalKrullDim ↥(Module.fiberSupport R S N r) := by
  have hBeq : topologicalKrullDim ↥(Module.fiberSupport R B M r)
      = topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩ :=
    le_antisymm ((Module.topologicalKrullDim_fiberSupport_le_fiber R B M r).trans hfib.le)
      (topologicalKrullDimAt_le_topologicalKrullDim _)
  have hSB : topologicalKrullDim ↥(Module.fiberSupport R S N r)
      = topologicalKrullDimAt ↥(Module.fiberSupport R B M r) ⟨lp, hlpmem⟩ :=
    ((Module.topologicalKrullDim_fiberSupport_eq_of_surjective hsurj e r).trans
      (Module.topologicalKrullDim_fiberSupport_eq_of_finite R B A M r)).trans hBeq
  exact ⟨hSB, (Module.topologicalKrullDimAt_fiberSupport_eq_of_stage hsurj e r hq hlp huniq
    hqmem hlpmem).trans hSB.symm⟩

end Module

end
