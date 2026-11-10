module

public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumSerreAlgebraization
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesUnwindingCriterion
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenCriterion

/-!
# The `(2, 3)`-inequalities from Serre's condition on the completed stalks

Let `(A, 𝔪)` be a Noetherian local ring with a dualizing complex, let `f ∈ 𝔪`, let `U` be the
punctured spectrum of `A` and let `(ℱₙ)` be an object of `Coh(U, f𝒪_U)`. Assume that at every
point `y ∈ U ∩ V(f)` with `dim({y}‾) = 1` the completed stalk `ℱ_y^∧` satisfies the two
conditions of [Stacks, Tag 0EJC]:

1. `ℱ_y^∧[1/f]` is `(S₂)` as an `𝒪_{X,y}^∧[1/f]`-module, and
2. `dim(𝒪_{X,y}^∧/𝔭) ≥ 3` for every `𝔭 ∈ Ass(ℱ_y^∧[1/f])`.

Then `(ℱₙ)` satisfies the `(2, 3)`-inequalities of [Stacks, Tag 0EJ3]. This is the half of the
argument of [Stacks, Tag 0EJC] that comes before [Stacks, Tag 0EJ9].

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_of_completedStalk_serre` — the
  `(2, 3)`-inequalities from the two conditions, with no further hypothesis.

## Proof outline

The two conditions give the pointwise bound `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` at the
points of `U ∩ Y` of dimension one, by
`Stacks.Algebraization.two_lt_depth_add_ringKrullDim_completedStalk_of_serre`. A principal ideal
has `cd(A, (f)) ≤ 1` ([Stacks, Tag 0DX9]), and there are two cases.

* `cd(A, (f)) = 1`. Then [Stacks, Tag 0EJA], in the form proved for a base with a dualizing
  complex,
  `satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex`,
  turns the pointwise bound into the `(2, 3)`-inequalities.
* `cd(A, (f)) ≤ 0`. Then `V(f)` is open and closed ([Stacks, Tag 0DX7]). It contains the closed
  point, and an open subset of the spectrum of a local ring that contains the closed point is
  everything. So `f` lies in every prime of `A` and is nilpotent. Its image in each completed
  local ring `𝒪_{X,y}^∧` is then nilpotent as well, so every prime of `𝒪_{X,y}^∧` contains
  `I𝒪_{X,y}^∧`. The `(2, 3)`-inequalities only constrain primes not containing `I𝒪_{X,y}^∧`,
  so they hold vacuously.

## References

* [Stacks Project, Tag 0EJC](https://stacks.math.columbia.edu/tag/0EJC)
* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9), the bound on `cd`.
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7), `cd ≤ 0`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- If `cd(A, I) ≤ 0` for an ideal `I` of a Noetherian local ring contained in the maximal ideal,
then every element of `I` is nilpotent. The zero locus `V(I)` is open and closed, it contains the
closed point, and every prime specializes to the closed point, so every prime lies in the open
set `V(I)`. -/
private theorem isNilpotent_of_cohomologicalDimension_nonpos {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A) (hIm : I ≤ IsLocalRing.maximalIdeal A)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) ≤ 0)
    {x : A} (hx : x ∈ I) : IsNilpotent x := by
  have hopen := ((Stacks.LocalCohomology.isClopen_zeroLocus_iff_cohomologicalDimension_le_zero
    A I _).1 hcd).isOpen
  have hall : ∀ q : PrimeSpectrum A, x ∈ q.asIdeal := fun q => by
    have hmem : IsLocalRing.closedPoint A ∈ PrimeSpectrum.zeroLocus (I : Set A) := hIm
    have hspec : q ⤳ IsLocalRing.closedPoint A :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
    exact hspec.mem_open hopen hmem hx
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  exact fun J hJ => hall ⟨J, hJ⟩

/-- **The `(2, 3)`-inequalities from the conditions of [Stacks, Tag 0EJC].** Let `(A, 𝔪)` be a
Noetherian local ring with a dualizing complex, `I = (f)`, `𝔞 = 𝔪`, and `(ℱₙ)` an object of
`Coh(U, I𝒪_U)`. If at every point `y` of `U ∩ Y` whose closure has dimension one

1. `ℱ_y^∧[1/f]` is `(S₂)` as an `𝒪_{X,y}^∧[1/f]`-module, and
2. `dim(𝒪_{X,y}^∧/𝔭) ≥ 3` for every `𝔭 ∈ Ass(ℱ_y^∧[1/f])`,

then `(ℱₙ)` satisfies the `(2, 3)`-inequalities.

When `cd(A, (f)) = 1` this is [Stacks, Tag 0EJA] for a base with a dualizing complex, applied to
the pointwise bound that the two conditions give. Otherwise `cd(A, (f)) ≤ 0`, `f` is nilpotent,
and the inequalities hold vacuously because every prime of every completed local ring contains
`I𝒪_{X,y}^∧`. -/
public theorem satisfiesDepthInequalities_of_completedStalk_serre
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (ha : S.a = IsLocalRing.maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hI : S.I = Ideal.span {f})
    (hserre : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      Order.height (S.U.ι.base y) = 1 → HasSerreCompletedStalkConditions S F f y) :
    SatisfiesDepthInequalities S F 2 3 := by
  have hle : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) ≤ 1 := by
    have h := Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one S.A f
    rw [← hI] at h
    exact h
  by_cases hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1
  · exact (satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex
      S ha hdual hcd F).2 fun y z hyz hdim p hp =>
        two_lt_depth_add_ringKrullDim_completedStalk_of_serre S F f hdual hI y z hyz
          (hserre y z hyz hdim) p hp
  · have hnil : ∀ x ∈ S.I, IsNilpotent x := fun x hx =>
      isNilpotent_of_cohomologicalDimension_nonpos S.I (ha ▸ S.I_le_a) (by omega) hx
    intro y z hyz p hp
    refine absurd ?_ hp
    refine Ideal.map_le_iff_le_comap.mpr ((stalk_idealOnOpen_eq_map S y).le.trans ?_)
    refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    change _ ∈ p.asIdeal
    obtain ⟨n, hn⟩ := (hnil x hx).map
      ((algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)).comp
        (baseToPointStalk S y))
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

end Stacks.Algebraization

end
