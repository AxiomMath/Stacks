module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Support.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite length of a quotient by an injective endomorphism

Let `A` be a Noetherian local ring and let `M` be a finite `A`-module whose support has
dimension one. The quotient of `M` by the image of any injective endomorphism has finite
length.

## Main results

* `Module.isFiniteLength_quotient_range_of_injective` states the finite-length conclusion for
  the quotient by an injective endomorphism.

## Implementation notes

The source applies this result to the injective composite of its two endomorphisms. Thus the
commutation-of-images hypothesis in the source is not needed for this finite-length conclusion.
Finiteness of length is expressed by Mathlib's `IsFiniteLength` predicate.

## References

* [Stacks Project, Tag 02PX](https://stacks.math.columbia.edu/tag/02PX)
-/

@[expose] public section

namespace Module

variable {A M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A nontrivial finite module over a Noetherian local ring whose support consists only of the
closed point has finite length. -/
@[ega "0 16.1.10" "special case"]
private lemma finiteLength_of_forall_mem_support_eq
    {R W : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup W] [Module R W] [Module.Finite R W] [Nontrivial W]
    (h : ∀ q ∈ Module.support R W,
      q.asIdeal = IsLocalRing.maximalIdeal R) : IsFiniteLength R W := by
  refine support_point.mp (Set.Subset.antisymm (fun q hq ↦ PrimeSpectrum.ext (h q hq)) ?_)
  simpa using IsLocalRing.closedPoint_mem_support R W

/-- If `p` is the only prime below itself that contains the annihilator of `W`, then the
localization of `W` at `p` has finite length. -/
private lemma finiteLength_localizedModule
    {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (W : Type*)
    [AddCommGroup W] [Module R W] [Module.Finite R W]
    [Nontrivial (LocalizedModule p.primeCompl W)]
    (h : ∀ q : Ideal R, q.IsPrime → q ≤ p → Module.annihilator R W ≤ q → q = p) :
    IsFiniteLength (Localization.AtPrime p) (LocalizedModule p.primeCompl W) := by
  refine finiteLength_of_forall_mem_support_eq fun q hq ↦ ?_
  have hqprime := q.2
  have hann : Module.annihilator (Localization.AtPrime p)
      (LocalizedModule p.primeCompl W) ≤ q.asIdeal :=
    Module.annihilator_le_of_mem_support hq
  have hcomap : Module.annihilator R W ≤
      q.asIdeal.comap (algebraMap R (Localization.AtPrime p)) := by
    intro a ha
    refine Ideal.mem_comap.mpr (hann (Module.mem_annihilator.mpr fun x ↦ ?_))
    induction x using LocalizedModule.induction_on with
    | _ w s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, Module.mem_annihilator.mp ha w]
      exact LocalizedModule.zero_mk s
  have hunit : ∀ s : p.primeCompl, algebraMap R (Localization.AtPrime p) s ∉ q.asIdeal :=
    fun s hs ↦ hqprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs
      (IsLocalization.map_units (Localization.AtPrime p) s))
  have hle : q.asIdeal.comap (algebraMap R (Localization.AtPrime p)) ≤ p := fun s hs ↦
    by_contra fun hsp ↦ hunit ⟨s, hsp⟩ hs
  have heq : q.asIdeal.comap (algebraMap R (Localization.AtPrime p)) = p :=
    h _ (Ideal.comap_isPrime _ _) hle hcomap
  refine le_antisymm (IsLocalRing.le_maximalIdeal hqprime.ne_top) fun x hx ↦ ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  have ha : a ∈ p :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p) p a s).mp hx
  have hain : IsLocalization.mk' (Localization.AtPrime p) a s *
      algebraMap R (Localization.AtPrime p) (s : R) ∈ q.asIdeal := by
    rw [IsLocalization.mk'_spec]
    exact Ideal.mem_comap.mp (heq.ge ha)
  exact (hqprime.mem_or_mem hain).resolve_right (hunit s)

/-- The quotient of a finite module of support dimension one by an injective endomorphism has
finite length. -/
@[stacks 02PX "finite_length"]
theorem isFiniteLength_quotient_range_of_injective
    (f : M →ₗ[A] M) (hf : Function.Injective f)
    (hdim : Module.supportDim A M = 1) :
    IsFiniteLength A (M ⧸ LinearMap.range f) := by
  by_cases hQ : Subsingleton (M ⧸ LinearMap.range f)
  · exact IsFiniteLength.of_subsingleton
  have : Nontrivial (M ⧸ LinearMap.range f) := not_subsingleton_iff_nontrivial.mp hQ
  have : Nontrivial M := (Submodule.mkQ_surjective (LinearMap.range f)).nontrivial
  refine finiteLength_of_forall_mem_support_eq fun p hp ↦ ?_
  have hpM : p ∈ Module.support A M :=
    Module.support_subset_of_surjective (Submodule.mkQ (LinearMap.range f))
      (Submodule.mkQ_surjective _) hp
  have hdim_le : Order.krullDim (Module.support A M) ≤ 1 := by
    simpa [Module.supportDim] using hdim.le
  rcases Order.krullDim_le_one_iff.mp hdim_le ⟨p, hpM⟩ with hmin | hmax
  · have : Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := Module.mem_support_iff.mp hpM
    have hfinite : IsFiniteLength (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := by
      refine finiteLength_localizedModule p.asIdeal M fun q hq hqp hann ↦ ?_
      have hqM : (⟨q, hq⟩ : PrimeSpectrum A) ∈ Module.support A M :=
        Module.mem_support_iff_of_finite.mpr hann
      have hqp' : (⟨⟨q, hq⟩, hqM⟩ : Module.support A M) ≤ ⟨p, hpM⟩ := hqp
      exact congrArg PrimeSpectrum.asIdeal (Subtype.ext_iff.mp (hmin.eq_of_le hqp'))
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2
    exact (Module.notMem_support_iff.mpr
      ((LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker
        p.asIdeal.primeCompl f).mp (IsArtinian.surjective_of_injective_endomorphism _
          (LocalizedModule.map_injective p.asIdeal.primeCompl f hf))) hp).elim
  · have hle : (⟨p, hpM⟩ : Module.support A M) ≤
        ⟨IsLocalRing.closedPoint A, IsLocalRing.closedPoint_mem_support A M⟩ :=
      IsLocalRing.le_maximalIdeal p.isPrime.ne_top
    exact congrArg (fun x : Module.support A M ↦ x.1.asIdeal) (hmax.eq_of_le hle)

end Module
