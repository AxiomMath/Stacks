module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecCokernel
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecDevissageStage
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecFiberSupportDimension
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecStageDimension
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.RingTheory.Flat.CompleteDevissageFibreDimension
public import StacksFrontier.RingTheory.Flat.CompleteDevissagePointedTail

/-!
# The pointed data of a stage, read on the spectrum

One stage of an algebraic complete dévissage of `N/S/R` at a prime `q` of `S`, together with
pointed data — a prime `lp` of the smooth algebra `B` lying over `r`, the unique prime `up` of the
finite algebra `A` above it, and the identification of `q` with the contraction of `up` — gives
the membership of `q` in the fibre support of `N` and the dimension conditions on that fibre
support, with the fibre supports read as subspaces of `Spec B` and `Spec S`.

## Main definitions

* `Module.DevissageStage.toData`: a stage of a complete dévissage with the presentation of the
  algebra being dévissed forgotten.

## Main results

* `Module.DevissageStage.lowerPrimeMem` and `Module.DevissageStage.fiberDim`: the two conditions
  of the pointed datum, with the support of the fibre module read as a subspace of `Spec B`
  rather than of the spectrum of the fibre ring.
* `Module.DevissageStage.memFiberSupport`: the prime `q` lies in the fibre support of `N`.
* `Module.DevissageStage.dimFacts`: the fibre support of `N` has the dimension recorded by the
  stage, and has it locally at `q`.
* `AlgebraicGeometry.topologicalKrullDim_fiber_specMap`: the dimension of the scheme-theoretic
  fibre of `Spec` of a ring map is the dimension of the subspace of primes lying over the point.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat TopologicalSpace

universe u

/-- **The dimension of the fibre of `Spec B → Spec R` over a point is the dimension of the
subspace of `Spec B` lying over it.** -/
public theorem AlgebraicGeometry.topologicalKrullDim_fiber_specMap (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] (t : Spec (CommRingCat.of R)) :
    topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber t) =
      topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹' {t}) :=
  IsHomeomorph.topologicalKrullDim_eq _
    ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberHomeo t).isHomeomorph

namespace Module.DevissageStage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
  (st : Module.DevissageStage R S N r)

/-- A stage of a complete dévissage, with the presentation of the algebra being dévissed and the
identification of the module forgotten. -/
public abbrev toData : Module.DevissageStageData.{u, u} R r where
  A := st.A
  B := st.B
  M := st.M
  toLeft := st.toLeft
  multiplicity := st.multiplicity
  alpha := st.alpha
  finiteM := st.finiteM
  finite_toLeft := st.left_finite
  smooth := st.smooth
  geometricallyIrreducibleFibers := st.geometricallyIrreducibleFibers
  map_isPrime := st.map_isPrime
  fiber_bijective := st.fiber_bijective

variable (P : st.toData.Pointed)

/-- The chosen prime of the smooth algebra lies in the fibre support of the stage module, read as a
subspace of `Spec B`. -/
public theorem lowerPrimeMem :
    (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : PrimeSpectrum st.B) ∈
      Module.fiberSupport R st.B st.M r := by
  have := P.lowerPrime_isPrime
  exact ⟨(Module.primesOverOrderIsoFiber_mem_support_iff R st.B st.M r P.lowerPrime
      P.lowerPrime_liesOver).1 P.lowerPrime_mem_fiberSupport,
    PrimeSpectrum.ext P.lowerPrime_liesOver.over.symm⟩

/-- If every fibre of `Spec B → Spec R` has the relative dimension of `R → B`, then every fibre has
the local dimension at the chosen prime of the fibre support of the stage module, read as a
subspace of `Spec B`. -/
public theorem fiberDim (hst : st.toData.FibresHaveRelativeDimension) (t : PrimeSpectrum R) :
    topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R st.B) ⁻¹' {t}) =
      topologicalKrullDimAt ↥(Module.fiberSupport R st.B st.M r)
        ⟨⟨P.lowerPrime, P.lowerPrime_isPrime⟩, st.lowerPrimeMem P⟩ := by
  have := P.lowerPrime_isPrime
  exact (P.topologicalKrullDim_fiber_eq_support hst t).trans
    ((Module.topologicalKrullDimAt_support_fiber R st.B st.M r
        P.lowerPrime_mem_fiberSupport).trans
      (congrArg _ (Subtype.ext (PrimeSpectrum.comap_primesOverOrderIsoFiber R st.B r
        P.lowerPrime P.lowerPrime_liesOver))))

section Pointed

variable {q : Ideal S} [hqp : q.IsPrime]

/-- The membership of `q` in the fibre support of `N` and, given the dimension hypothesis, the
dimension facts about it, both obtained from the unique chosen upper prime above `q`. -/
private theorem exists_memFiberSupport_dimFacts (hinit : P.upperPrime.comap st.toA₀.toRingHom = q) :
    ∃ hmem : (⟨q, hqp⟩ : PrimeSpectrum S) ∈ Module.fiberSupport R S N r,
      st.toData.FibresHaveRelativeDimension →
        topologicalKrullDim ↥(Module.fiberSupport R S N r)
            = topologicalKrullDimAt ↥(Module.fiberSupport R st.B st.M r)
              ⟨⟨P.lowerPrime, P.lowerPrime_isPrime⟩, st.lowerPrimeMem P⟩
          ∧ topologicalKrullDimAt ↥(Module.fiberSupport R S N r) ⟨⟨q, hqp⟩, hmem⟩
              = topologicalKrullDim ↥(Module.fiberSupport R S N r) := by
  have := P.lowerPrime_isPrime
  have := P.upperPrime_isPrime
  let : Algebra S st.A := st.toA₀.toRingHom.toAlgebra
  let : Module S st.M := Module.compHom st.M st.toA₀.toRingHom
  have : IsScalarTower R S st.A :=
    IsScalarTower.of_algebraMap_eq fun x => (st.toA₀.commutes x).symm
  have : IsScalarTower S st.A st.M :=
    ⟨fun x y m => by
      change (st.toA₀ x * y) • m = st.toA₀ x • y • m
      rw [mul_smul]⟩
  have huniq : ∀ p' : PrimeSpectrum st.A,
      PrimeSpectrum.comap (algebraMap st.B st.A) p' = ⟨P.lowerPrime, P.lowerPrime_isPrime⟩ →
        p' = ⟨P.upperPrime, P.upperPrime_isPrime⟩ := fun p' hp' =>
    PrimeSpectrum.ext
      (P.upperPrime_unique p'.asIdeal p'.isPrime (congrArg PrimeSpectrum.asIdeal hp'))
  have hmem := (Module.mem_fiberSupport_of_unique_comap
    (up := (⟨P.upperPrime, P.upperPrime_isPrime⟩ : PrimeSpectrum st.A))
    (lp := (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : PrimeSpectrum st.B))
    (q := (⟨q, hqp⟩ : PrimeSpectrum S))
    st.initial_surjective st.initialEquiv r (st.lowerPrimeMem P) huniq (PrimeSpectrum.ext hinit)).2
  exact ⟨hmem, fun hst => Module.topologicalKrullDim_fiberSupport_eq_of_fiber_eq
    (up := (⟨P.upperPrime, P.upperPrime_isPrime⟩ : PrimeSpectrum st.A))
    (lp := (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : PrimeSpectrum st.B))
    (q := (⟨q, hqp⟩ : PrimeSpectrum S))
    st.initial_surjective st.initialEquiv r (st.lowerPrimeMem P)
    (PrimeSpectrum.ext P.upperPrime_under) huniq (PrimeSpectrum.ext hinit)
    hmem (st.fiberDim P hst _)⟩

/-- If `q` is the contraction of the chosen upper prime, then `q` lies in the fibre support of `N`.
-/
public theorem memFiberSupport (hinit : P.upperPrime.comap st.toA₀.toRingHom = q) :
    (⟨q, hqp⟩ : PrimeSpectrum S) ∈ Module.fiberSupport R S N r :=
  (exists_memFiberSupport_dimFacts st P hinit).1

/-- If the fibres of the stage have the relative dimension of `R → B` and `q` is the contraction of
the chosen upper prime, then the fibre support of `N` has the local dimension at the chosen prime
of the fibre support of the stage module, and has that dimension locally at `q`. -/
public theorem dimFacts (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q) :
    topologicalKrullDim ↥(Module.fiberSupport R S N r)
        = topologicalKrullDimAt ↥(Module.fiberSupport R st.B st.M r)
          ⟨⟨P.lowerPrime, P.lowerPrime_isPrime⟩, st.lowerPrimeMem P⟩
      ∧ topologicalKrullDimAt ↥(Module.fiberSupport R S N r)
            ⟨⟨q, hqp⟩, st.memFiberSupport P hinit⟩
          = topologicalKrullDim ↥(Module.fiberSupport R S N r) :=
  (exists_memFiberSupport_dimFacts st P hinit).2 hst

end Pointed

end Module.DevissageStage

end
