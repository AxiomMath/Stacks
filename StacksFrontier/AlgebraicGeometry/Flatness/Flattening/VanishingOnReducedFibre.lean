module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAlongClosure

/-!
# Vanishing on a reduced algebra all of whose points lie over the closure

Let `R'` be a commutative ring and let `f : M →ₗ[R'] N` be a map of `R'`-modules whose target is
projective.  The fibrewise vanishing locus of `f` is the zero locus of the flattening ideal of
Stacks 083L, so if `f` vanishes at every point of `\Spec R'` in the image of `\Spec A` for a
**reduced** `R'`-algebra `A`, then the base change of `f` to `A` itself vanishes: the flattening
ideal lies in every prime of `A`, hence in its nilradical, hence is zero.

## Main results

* `Module.exists_ideal_rTensor_eq_zero_iff_le_and_map_eq_bot`: one ideal detecting both the
  fibrewise vanishing of `f` at the points of `\Spec R'` and its vanishing after an arbitrary base
  change.
* `Module.rTensor_eq_zero_of_isReduced_of_forall_prime`: vanishing on a reduced algebra follows
  from fibrewise vanishing at the image points.
* `Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure`: the same with the fibrewise vanishing
  supplied by a closure argument downstairs, as in Stacks 0CWB.

## Implementation notes

The test ring in `Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot` ranges over one universe,
fixed when that statement is instantiated, while the two readings needed here — the residue fields
of `\Spec R'` and the algebra `A` — must be instances of **one** ideal.  The residue fields live in
the universe of `R'`, so `A` is asked to live there too; that is no restriction in the geometric
application, where every ring is at the universe of the schemes.

`IsReduced A` is used only through `nilradical_eq_sInf`: an ideal of `A` contained in every prime
is contained in the nilradical, which vanishes.  Geometrically it is the reducedness of the fibre
of an étale morphism over a point, which is what makes the fibrewise criterion of Stacks 083L
enough to conclude on the whole fibre rather than only at its points.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
-/

@[expose] public section

namespace Module

universe u v w x

variable {R' : Type u} [CommRing R']
variable {M : Type v} [AddCommGroup M] [Module R' M]
variable {N : Type w} [AddCommGroup N] [Module R' N]

/-- For `f : M →ₗ[R'] N` with projective target there is an ideal `I` of `R'` such that the base
change of `f` to the residue field of a prime `p` vanishes exactly when `I ⊆ p`, and the base
change of `f` to an arbitrary `R'`-algebra `A` in the universe of `R'` vanishes exactly when the
image of `I` in `A` is zero. -/
theorem exists_ideal_rTensor_eq_zero_iff_le_and_map_eq_bot
    (f : M →ₗ[R'] N) (hN : Module.Projective R' N) :
    ∃ I : Ideal R',
      (∀ p : PrimeSpectrum R',
          LinearMap.rTensor p.asIdeal.ResidueField f = 0 ↔ I ≤ p.asIdeal) ∧
        ∀ (A : Type u) [CommRing A] [Algebra R' A],
          LinearMap.rTensor A f = 0 ↔ Ideal.map (algebraMap R' A) I = ⊥ := by
  obtain ⟨I, hI⟩ := exists_ideal_rTensor_eq_zero_iff_map_eq_bot.{u, v, w, u} f hN
  have key : ∀ (A : Type u) [CommRing A] [Algebra R' A],
      LinearMap.rTensor A f = 0 ↔ Ideal.map (algebraMap R' A) I = ⊥ := by
    intro A _ _
    have h := hI A (algebraMap R' A)
    rwa [show (algebraMap R' A).toAlgebra = _ from toAlgebra_algebraMap] at h
  refine ⟨I, fun p => ?_, key⟩
  rw [key p.asIdeal.ResidueField, Ideal.map_eq_bot_iff_le_ker,
    Ideal.ker_algebraMap_residueField]

/-- Let `f : M →ₗ[R'] N` have projective target and let `A` be a reduced `R'`-algebra. If the base
change of `f` to the residue field of every prime of `R'` in the image of `\Spec A ⟶ \Spec R'`
vanishes, then the base change of `f` to `A` vanishes. -/
theorem rTensor_eq_zero_of_isReduced_of_forall_prime
    (f : M →ₗ[R'] N) (hN : Module.Projective R' N)
    (A : Type u) [CommRing A] [Algebra R' A] [IsReduced A]
    (hvan : ∀ q : PrimeSpectrum A,
      LinearMap.rTensor
        (PrimeSpectrum.comap (algebraMap R' A) q).asIdeal.ResidueField f = 0) :
    LinearMap.rTensor A f = 0 := by
  obtain ⟨I, hres, hbase⟩ := exists_ideal_rTensor_eq_zero_iff_le_and_map_eq_bot f hN
  refine (hbase A).mpr (le_bot_iff.mp ?_)
  rw [← nilradical_eq_bot_iff.mpr ‹IsReduced A›, nilradical_eq_sInf A]
  refine le_sInf fun J hJ => ?_
  have : J.IsPrime := hJ
  refine Ideal.map_le_iff_le_comap.mpr ?_
  exact (hres (PrimeSpectrum.comap (algebraMap R' A) ⟨J, hJ⟩)).mp
    (hvan ⟨J, hJ⟩)

/-- Let `φ : R →+* R'` induce an open map on prime spectra, let `f : M →ₗ[R'] N` be a map of
`R'`-modules with projective target, let `T` be a subset of `\Spec R` and let `A` be a reduced
`R'`-algebra each of whose points lies over a point of `\Spec R'` whose image in `\Spec R` is in
the closure of `T`. If the base change of `f` to `κ(t')` vanishes at every point `t'` of `\Spec R'`
lying over `T`, then the base change of `f` to `A` vanishes. -/
theorem rTensor_eq_zero_of_isReduced_of_comap_mem_closure
    {R : Type x} [CommRing R] (φ : R →+* R')
    (hopen : IsOpenMap (PrimeSpectrum.comap φ))
    (f : M →ₗ[R'] N) (hN : Module.Projective R' N)
    (T : Set (PrimeSpectrum R))
    (A : Type u) [CommRing A] [Algebra R' A] [IsReduced A]
    (hA : ∀ q : PrimeSpectrum A,
      PrimeSpectrum.comap φ (PrimeSpectrum.comap (algebraMap R' A) q) ∈ closure T)
    (hT : ∀ t' : PrimeSpectrum R', PrimeSpectrum.comap φ t' ∈ T →
      LinearMap.rTensor t'.asIdeal.ResidueField f = 0) :
    LinearMap.rTensor A f = 0 :=
  rTensor_eq_zero_of_isReduced_of_forall_prime f hN A fun q =>
    rTensor_residueField_eq_zero_of_comap_mem_closure φ hopen f hN T
      (PrimeSpectrum.comap (algebraMap R' A) q) (hA q) hT

end Module

end
