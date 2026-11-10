module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Examples.Geometric.HenselizationDifferential
public import StacksFrontier.Deformation.Examples.Geometric.HenselizationSmooth
public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularities
public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularitiesCompletionComparison
public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularitiesHenselizationComparison
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationSmooth
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationTangentSpace
public import StacksFrontier.Deformation.Examples.Geometric.RingDeformationPiFullyFaithful
public import StacksFrontier.Deformation.Examples.Geometric.RingsHull
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivTangent
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceFinite
public import StacksFrontier.Deformation.Smooth.FullyFaithful
public import StacksFrontier.Deformation.LiftsOfObjects.Smoothness.Criterion
public import StacksFrontier.Deformation.Smooth.PiRimSchlessinger
public import StacksFrontier.Deformation.TangentSpace.DifferentialLinear

/-!
# The chain of deformation categories at the isolated singularities

This file assembles the conclusions of **Stacks 0DZF** for each of the three maps of the chain

`Def_P → ∏ Def_{P_{𝔪 i}} → ∏ Def_{P^h_{𝔪 i}} → ∏ Def_{P^∧_{𝔪 i}}`.

## Main results

* `Deformation.Examples.exists_principal_neighborhood`: prime avoidance at the singular points.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
-/

@[expose] public section

open CategoryTheory

universe uι u w v₁ u₁ v₂ u₂

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {P : Type w} [CommRing P] [Algebra k P]

/-! ### Reading the tag's smoothness hypothesis at the intersection of the singular points -/

/-- **A prime not containing `J = 𝔪 1 ∩ … ∩ 𝔪 n` is a smooth point.** This is how the tag's own
hypothesis — smooth except at the maximal ideals `𝔪 1, …, 𝔪 n` — supplies the hypothesis of
**Stacks 0DZ5** and **Stacks 0DZD** at the pair `(P, J)`: a prime equal to some `𝔪 i` does
contain `J`. -/
public theorem isSmoothAt_of_not_iInf_le {ι : Type uι} (m : ι → PrimeSpectrum P)
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (q : PrimeSpectrum P) (hq : ¬ (⨅ i, (m i).asIdeal) ≤ q.asIdeal) :
    Algebra.IsSmoothAt k q.asIdeal := by
  by_contra hn
  obtain ⟨i, rfl⟩ := hsm q hn
  exact hq (iInf_le (fun i => (m i).asIdeal) i)

/-! ### Prime avoidance at the singular points -/

/-- **Prime avoidance at the singular points.** For a finite family of distinct maximal ideals
there is an element lying in every member of the family except the `i`-th. Inverting it makes
`𝔪 i` the only member of the family that survives, which is the reduction the source's last step
performs before applying **Stacks 0DZ9**.

The proof is the Chinese remainder theorem: the family is pairwise coprime because its members
are distinct maximal ideals, so the tuple which is `1` at `i` and `0` elsewhere is hit. -/
public theorem exists_principal_neighborhood {ι : Type uι} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m) (i : ι) :
    ∃ s : P, s ∉ (m i).asIdeal ∧ ∀ j, j ≠ i → s ∈ (m j).asIdeal := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => (m i).asIdeal)) := by
    intro a b hab
    let := hmax a
    let := hmax b
    exact Ideal.isCoprime_of_isMaximal fun h => hab (hinj (PrimeSpectrum.ext h))
  obtain ⟨x, hx⟩ := (Ideal.quotientInfRingEquivPiQuotient (fun i => (m i).asIdeal) hcop).surjective
    (fun j => if j = i then 1 else 0)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs (j : ι) : Ideal.Quotient.mk (m j).asIdeal s = if j = i then 1 else 0 :=
    congrFun hx j
  refine ⟨s, ?_, ?_⟩
  · intro hi
    have hone : (1 : P ⧸ (m i).asIdeal) = 0 := by
      simpa [hs i] using Ideal.Quotient.eq_zero_iff_mem.mpr hi
    let := hmax i
    exact one_ne_zero hone
  · intro j hji
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [ite_eq_right hji] using hs j

/-! ### Cancelling along a smooth or bijective first factor -/

/-- Smoothness of a composite descends to the second factor along a smooth first factor, which is
essentially surjective. -/
private theorem isSmooth_of_isSmooth_comp_of_isSmooth
    {𝓕 𝓖 𝓗 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsPredeformationCategory 𝓕.p) (h𝓖 : IsPredeformationCategory 𝓖.p)
    {φ : BasedFunctor 𝓕 𝓖} (ψ : BasedFunctor 𝓖 𝓗) (hφ : IsSmooth φ)
    (h : IsSmooth (BasedFunctor.comp φ ψ)) : IsSmooth ψ := by
  have := essSurj_of_isSmooth h𝓕 h𝓖 φ hφ
  exact isSmooth_of_essSurj_comp φ ψ h

/-- If a square of based functors commutes up to isomorphism and its top `F` and right `G` maps
are bijective on isomorphism classes, so is the composite of the other two. -/
private theorem bijective_comp_mapIsomorphismClasses_of_iso
    {𝓐 𝓑 𝓒 𝓓 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓐 : IsCofiberedInGroupoids 𝓐.p) (h𝓑 : IsCofiberedInGroupoids 𝓑.p)
    (h𝓒 : IsCofiberedInGroupoids 𝓒.p) (h𝓓 : IsCofiberedInGroupoids 𝓓.p)
    {F : BasedFunctor 𝓐 𝓑} {G : BasedFunctor 𝓑 𝓓} {F' : BasedFunctor 𝓐 𝓒}
    {G' : BasedFunctor 𝓒 𝓓} (hcmp : BasedFunctor.comp F G ≅ BasedFunctor.comp F' G')
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hF : Function.Bijective (mapIsomorphismClasses h𝓐 h𝓑 F A))
    (hG : Function.Bijective (mapIsomorphismClasses h𝓑 h𝓓 G A)) :
    Function.Bijective
      ((mapIsomorphismClasses h𝓒 h𝓓 G' A) ∘ (mapIsomorphismClasses h𝓐 h𝓒 F' A)) := by
  rw [Function.comp_def, ← mapIsomorphismClasses_comp,
    ← mapIsomorphismClasses_eq_of_iso h𝓐 h𝓓 _ _ hcmp A, mapIsomorphismClasses_comp]
  exact hG.comp hF

/-! ### The source's last step, at a single singular point

The source's last step treats one index `i` at a time: it replaces `P` by a principal
localization in which `𝔪 i` is the only singular point — still of finite type over `k` — and
applies **Stacks 0DZ9** with `S = P \ 𝔪`. What 0DZ9 gives is the *first* map `Def_Q → Def_{Q_𝔪}`
of the chain at that localization `Q`; the *second* map there, `Def_{Q_𝔪} → Def_{Q^h_𝔪}`, is then
left-cancelled out of **Stacks 0DZD** at the pair `(Q, 𝔪)`, using that the henselization of `Q`
along the maximal ideal `𝔪` is the henselization of the local ring `Q_𝔪`.

Left cancellation is legitimate here because the first map is smooth, hence essentially
surjective (`Deformation.essSurj_of_isSmooth`), and
`Deformation.isSmooth_of_essSurj_comp` cancels a composite along an essentially surjective first
factor. -/

section SingleSingularPoint

variable (Q : Type w) [CommRing Q] [Algebra k Q]

attribute [local instance 100] henselizationAlgebra

variable {Q}

/-- With `𝔪` the only singular point, **Stacks 0DZ9** applies at `S = Q \ 𝔪`: every prime
containing an element outside `𝔪` is a smooth point. -/
public theorem isSmoothAt_of_mem_of_primeCompl (n : Ideal Q) [n.IsMaximal]
    (hsing : ∀ q : PrimeSpectrum Q, ¬ Algebra.IsSmoothAt k q.asIdeal → q.asIdeal = n)
    (g : Q) (hg : g ∈ n.primeCompl) (q : PrimeSpectrum Q) (hgq : g ∈ q.asIdeal) :
    Algebra.IsSmoothAt k q.asIdeal := by
  by_contra hc
  exact hg (hsing q hc ▸ hgq)

/-- With `𝔪` the only singular point, **Stacks 0DZD** applies at the pair `(Q, 𝔪)`: every prime
not containing `𝔪` is a smooth point. -/
public theorem isSmoothAt_of_not_le_of_singleSingular (n : Ideal Q) [n.IsMaximal]
    (hsing : ∀ q : PrimeSpectrum Q, ¬ Algebra.IsSmoothAt k q.asIdeal → q.asIdeal = n)
    (q : PrimeSpectrum Q) (hq : ¬ n ≤ q.asIdeal) : Algebra.IsSmoothAt k q.asIdeal := by
  by_contra hc
  exact hq (le_of_eq (hsing q hc).symm)

/-- **Smoothness of the second map of the chain at a single singular point.** For `Q` of finite
type over `k` whose only singular point is the maximal ideal `𝔪`, the henselization functor of
the local ring `Q_𝔪` along its maximal ideal is smooth.

This is the source's last step: **Stacks 0DZD** at `(Q, 𝔪)` composed with the transport along
`Q^h_𝔪 ≅ (Q_𝔪)^h`, compared with the composite of the localization functor of **Stacks 0DZ9**
and the functor in question, and then left-cancelled along the localization functor, which is
essentially surjective because it is smooth. -/
public theorem isSmooth_henselizationFunctor_localizationAtPrime [Algebra.FiniteType k Q]
    (n : Ideal Q) [n.IsMaximal]
    (hsing : ∀ q : PrimeSpectrum Q, ¬ Algebra.IsSmoothAt k q.asIdeal → q.asIdeal = n)
    (e : (henselization Q n : Type w) ≃+*
      (henselization (Localization n.primeCompl)
        (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w))
    (he : ∀ a : k, e (algebraMap k (henselization Q n : Type w) a) =
      algebraMap k (henselization (Localization n.primeCompl)
        (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w) a)
    (hcmp : BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) n).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctor (Λ := Λ) (k := k) n.primeCompl).functor
          (henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (Localization n.primeCompl))).functor) :
    IsSmooth (henselizationFunctor (Λ := Λ) (k := k)
      (IsLocalRing.maximalIdeal (Localization n.primeCompl))).functor := by
  have hL : IsSmooth (localizationFunctor (Λ := Λ) (k := k) n.primeCompl).functor :=
    isSmooth_localizationFunctor Q n.primeCompl
      (isSmoothAt_of_mem_of_primeCompl (k := k) n hsing)
  have hHT : IsSmooth (BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) n).functor
      (ringDeformationTransport e he)) :=
    isSmooth_comp _ _
      (isSmooth_henselizationFunctor Q n (isSmoothAt_of_not_le_of_singleSingular (k := k) n hsing))
      (isSmooth_ringDeformationTransport e he)
  exact isSmooth_of_isSmooth_comp_of_isSmooth
    (ringDeformationCategory_isDeformationCategory Q).predeformation
    (ringDeformationCategory_isDeformationCategory (Localization n.primeCompl)).predeformation _ hL
    (isSmooth_of_iso hcmp.symm hHT)

/-- **The tangent-space conclusion for the second map of the chain at a single singular point.**
Same route as `Deformation.Examples.isSmooth_henselizationFunctor_localizationAtPrime`, with the
cancellation performed on maps of isomorphism classes rather than on lifting problems. -/
public theorem bijective_differential_henselizationFunctor_localizationAtPrime
    [Algebra.FiniteType k Q]
    (n : Ideal Q) [n.IsMaximal]
    (hsing : ∀ q : PrimeSpectrum Q, ¬ Algebra.IsSmoothAt k q.asIdeal → q.asIdeal = n)
    (e : (henselization Q n : Type w) ≃+*
      (henselization (Localization n.primeCompl)
        (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w))
    (he : ∀ a : k, e (algebraMap k (henselization Q n : Type w) a) =
      algebraMap k (henselization (Localization n.primeCompl)
        (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w) a)
    (hcmp : BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) n).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctor (Λ := Λ) (k := k) n.primeCompl).functor
          (henselizationFunctor (Λ := Λ) (k := k)
            (IsLocalRing.maximalIdeal (Localization n.primeCompl))).functor) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := Localization n.primeCompl))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := (henselization (Localization n.primeCompl)
          (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w)))
      (henselizationFunctor (Λ := Λ) (k := k)
        (IsLocalRing.maximalIdeal (Localization n.primeCompl))).functor) := by
  let hQ := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := Q)
  let hHn := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := (henselization Q n : Type w))
  let hLn := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := Localization n.primeCompl)
  let hKn := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := (henselization (Localization n.primeCompl)
      (IsLocalRing.maximalIdeal (Localization n.primeCompl)) : Type w))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let H := (henselizationFunctor (Λ := Λ) (k := k) n).functor
  let T := ringDeformationTransport (Λ := Λ) e he
  let L := (localizationFunctor (Λ := Λ) (k := k) n.primeCompl).functor
  let K := (henselizationFunctor (Λ := Λ) (k := k)
    (IsLocalRing.maximalIdeal (Localization n.primeCompl))).functor
  have hdL : Function.Bijective (mapIsomorphismClasses hQ hLn L A) :=
    bijective_differential_localizationFunctor (Λ := Λ) Q n.primeCompl
      (isSmoothAt_of_mem_of_primeCompl (k := k) n hsing)
  have hdH : Function.Bijective (mapIsomorphismClasses hQ hHn H A) :=
    bijective_differential_henselizationFunctor (Λ := Λ) Q n
      (isSmoothAt_of_not_le_of_singleSingular (k := k) n hsing)
  have hdT : Function.Bijective (mapIsomorphismClasses hHn hKn T A) :=
    bijective_differential_ringDeformationTransport (Λ := Λ) e he
  exact (hdL.of_comp_iff _).mp
    (bijective_comp_mapIsomorphismClasses_of_iso hQ hHn hLn hKn hcmp A hdH hdT)

end SingleSingularPoint

/-! ### Reading the henselization functor at an isomorphic presentation of the ring -/

section Congr

variable {R S : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]

attribute [local instance 100] henselizationAlgebra

/-- **Smoothness of the henselization functor is invariant under an isomorphism of the ring.**
An isomorphism `R ≅ S` carrying `I` to `J` induces an isomorphism of henselizations, and the
square of functors it fills commutes; the transport along `R ≅ S` is smooth, hence essentially
surjective, so smoothness of the composite descends to the henselization functor at `J`. -/
public theorem isSmooth_henselizationFunctor_of_ringEquiv
    (eRS : R ≃+* S) (heRS : ∀ a : k, eRS (algebraMap k R a) = algebraMap k S a)
    (I : Ideal R) (J : Ideal S)
    (d : (henselization R I : Type w) ≃+* (henselization S J : Type w))
    (hd : ∀ a : k, d (algebraMap k (henselization R I : Type w) a) =
      algebraMap k (henselization S J : Type w) a)
    (hcmp : BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) I).functor
          (ringDeformationTransport d hd) ≅
        BasedFunctor.comp (ringDeformationTransport eRS heRS)
          (henselizationFunctor (Λ := Λ) (k := k) J).functor)
    (hH : IsSmooth (henselizationFunctor (Λ := Λ) (k := k) I).functor) :
    IsSmooth (henselizationFunctor (Λ := Λ) (k := k) J).functor := by
  exact isSmooth_of_isSmooth_comp_of_isSmooth
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) R).predeformation
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) S).predeformation _
    (isSmooth_ringDeformationTransport eRS heRS)
    (isSmooth_of_iso hcmp.symm (isSmooth_comp _ _ hH (isSmooth_ringDeformationTransport d hd)))

/-- **The tangent-space conclusion for the henselization functor is invariant under an
isomorphism of the ring.** Same square as
`Deformation.Examples.isSmooth_henselizationFunctor_of_ringEquiv`, cancelled on the maps of
isomorphism classes. -/
public theorem bijective_differential_henselizationFunctor_of_ringEquiv
    (eRS : R ≃+* S) (heRS : ∀ a : k, eRS (algebraMap k R a) = algebraMap k S a)
    (I : Ideal R) (J : Ideal S)
    (d : (henselization R I : Type w) ≃+* (henselization S J : Type w))
    (hd : ∀ a : k, d (algebraMap k (henselization R I : Type w) a) =
      algebraMap k (henselization S J : Type w) a)
    (hcmp : BasedFunctor.comp (henselizationFunctor (Λ := Λ) (k := k) I).functor
          (ringDeformationTransport d hd) ≅
        BasedFunctor.comp (ringDeformationTransport eRS heRS)
          (henselizationFunctor (Λ := Λ) (k := k) J).functor)
    (hdH : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := (henselization R I : Type w)))
      (henselizationFunctor (Λ := Λ) (k := k) I).functor)) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := (henselization S J : Type w)))
      (henselizationFunctor (Λ := Λ) (k := k) J).functor) := by
  let hR := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := R)
  let hS := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := S)
  let hHI := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := (henselization R I : Type w))
  let hHJ := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := (henselization S J : Type w))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let H := (henselizationFunctor (Λ := Λ) (k := k) I).functor
  let K := (henselizationFunctor (Λ := Λ) (k := k) J).functor
  let Td := ringDeformationTransport (Λ := Λ) d hd
  let Te := ringDeformationTransport (Λ := Λ) eRS heRS
  have hdD : Function.Bijective (mapIsomorphismClasses hHI hHJ Td A) :=
    bijective_differential_ringDeformationTransport (Λ := Λ) d hd
  have hdT : Function.Bijective (mapIsomorphismClasses hR hS Te A) :=
    bijective_differential_ringDeformationTransport (Λ := Λ) eRS heRS
  exact (hdT.of_comp_iff _).mp
    (bijective_comp_mapIsomorphismClasses_of_iso hR hHI hS hHJ hcmp A hdH hdD)

end Congr

/-! ### Inverting an element to isolate one singular point -/

section AwayLocalization

variable {ι : Type uι} (m : ι → PrimeSpectrum P)

/-- The image of `𝔪 i` in a principal localization in which `𝔪 i` survives is maximal. -/
public theorem isMaximal_map_awayLocalization (hmax : ∀ i, (m i).asIdeal.IsMaximal)
    {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) :
    ((m i).asIdeal.map (algebraMap P (Localization.Away s))).IsMaximal := by
  let := hmax i
  refine IsLocalization.isMaximal_of_isMaximal_disjoint (Submonoid.powers s)
    (Localization.Away s) (m i).asIdeal (Set.disjoint_left.mpr ?_)
  rintro z ⟨r, rfl⟩ hz
  exact hs ((m i).isPrime.mem_of_pow_mem r hz)

/-- The image of `𝔪 i` in a principal localization in which `𝔪 i` survives contracts back to
`𝔪 i`. -/
public theorem comap_map_awayLocalization {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) :
    ((m i).asIdeal.map (algebraMap P (Localization.Away s))).comap
        (algebraMap P (Localization.Away s)) = (m i).asIdeal := by
  refine IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s)
    (Localization.Away s) (m i).isPrime (Set.disjoint_left.mpr ?_)
  rintro z ⟨r, rfl⟩ hz
  exact hs ((m i).isPrime.mem_of_pow_mem r hz)

/-- **Inverting an element of every `𝔪 j` but `𝔪 i` leaves the image of `𝔪 i` as the only
singular point.** This is the reduction the source performs before its last step: a prime of the
principal localization which is not a smooth point contracts to a prime of `P` which is not a
smooth point, hence to one of the `𝔪 j`; the inverted element lies in every `𝔪 j` with `j ≠ i`
and in no prime of the localization, so `j = i`. -/
public theorem asIdeal_eq_map_of_not_isSmoothAt_awayLocalization
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ j, m j = q)
    {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) (hs' : ∀ j, j ≠ i → s ∈ (m j).asIdeal)
    (q : PrimeSpectrum (Localization.Away s))
    (hq : ¬ Algebra.IsSmoothAt k q.asIdeal) :
    q.asIdeal = (m i).asIdeal.map (algebraMap P (Localization.Away s)) := by
  have hp : ¬ Algebra.IsSmoothAt k
      (PrimeSpectrum.comap (algebraMap P (Localization.Away s)) q).asIdeal := by
    intro hp
    exact hq ((Algebra.FormallySmooth.iff_of_equiv
      ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers s) q.asIdeal).restrictScalars k)).mp hp)
  obtain ⟨j, hj⟩ := hsm _ hp
  have hnot : s ∉ (PrimeSpectrum.comap (algebraMap P (Localization.Away s)) q).asIdeal := by
    have hd := ((IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers s)
      (Localization.Away s) q.asIdeal).mp q.isPrime).2
    exact fun hx => Set.disjoint_left.mp hd (show s ∈ Submonoid.powers s from ⟨1, pow_one s⟩) hx
  have hji : j = i := by
    by_contra hne
    exact hnot (hj ▸ hs' j hne)
  have hqeq : q.asIdeal.comap (algebraMap P (Localization.Away s)) =
      ((m i).asIdeal.map (algebraMap P (Localization.Away s))).comap
        (algebraMap P (Localization.Away s)) := by
    rw [comap_map_awayLocalization m hs]
    exact congrArg PrimeSpectrum.asIdeal (hji ▸ hj).symm
  exact le_antisymm
    ((IsLocalization.under_le_under_iff (Submonoid.powers s) (Localization.Away s)).mp hqeq.le)
    ((IsLocalization.under_le_under_iff (Submonoid.powers s) (Localization.Away s)).mp hqeq.ge)

/-- The local ring at a prime, transported along an equality of primes. -/
public noncomputable def localizationPrimeComplEquivOfEq {p q : Ideal P} [p.IsPrime] [q.IsPrime]
    (h : p = q) : Localization p.primeCompl ≃ₐ[P] Localization q.primeCompl := by
  subst h
  exact AlgEquiv.refl

/-- **The local ring of a principal localization at the image of `𝔪 i` is the local ring of `P`
at `𝔪 i`.** Localizing twice localizes once, by
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and the prime being contracted
to is `𝔪 i` by `Deformation.Examples.comap_map_awayLocalization`. -/
public noncomputable def localRingAwayEquiv (hmax : ∀ i, (m i).asIdeal.IsMaximal)
    {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) :
    letI := isMaximal_map_awayLocalization m hmax hs
    Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl ≃ₐ[P]
      localRingAt (m i) := by
  letI := isMaximal_map_awayLocalization m hmax hs
  letI := hmax i
  exact (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers s)
      ((m i).asIdeal.map (algebraMap P (Localization.Away s)))).symm.trans
    (localizationPrimeComplEquivOfEq (comap_map_awayLocalization m hs))

/-- `Deformation.Examples.localRingAwayEquiv` is `k`-linear. -/
public theorem algebraMap_localRingAwayEquiv (hmax : ∀ i, (m i).asIdeal.IsMaximal)
    {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) (a : k) :
    letI := isMaximal_map_awayLocalization m hmax hs
    (localRingAwayEquiv m hmax hs)
        (algebraMap k
          (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl) a) =
      algebraMap k (localRingAt (m i)) a := by
  let := isMaximal_map_awayLocalization m hmax hs
  rw [IsScalarTower.algebraMap_apply k P
      (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl),
    (localRingAwayEquiv m hmax hs).commutes,
    ← IsScalarTower.algebraMap_apply k P (localRingAt (m i))]

/-- `Deformation.Examples.localRingAwayEquiv` carries the maximal ideal to the maximal ideal. -/
public theorem map_maximalIdeal_localRingAwayEquiv (hmax : ∀ i, (m i).asIdeal.IsMaximal)
    {i : ι} {s : P} (hs : s ∉ (m i).asIdeal) :
    letI := isMaximal_map_awayLocalization m hmax hs
    (IsLocalRing.maximalIdeal
          (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl)).map
        (localRingAwayEquiv m hmax hs).toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal (localRingAt (m i)) := by
  let := isMaximal_map_awayLocalization m hmax hs
  let := hmax i
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.map_isMaximal_of_equiv (localRingAwayEquiv m hmax hs).toRingEquiv)

end AwayLocalization

/-! ### The third map of the chain at the tag's own target

The chain of the tag ends in the deformation categories of the completions `P^∧_{𝔪 i}` of the
*local rings*, while the functor out of `∏ 𝓓_{P^h_{𝔪 i}}` completes the *henselizations*. The two
rings agree by `Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing`, and
transporting along that isomorphism in each factor puts the third map of the chain at the tag's
own target. -/

section CompletedLocalRing

attribute [local instance 100] henselizationAlgebra

/-- The identification of the completion of the local ring with the completion of its
henselization is `k`-linear. -/
public theorem algebraMap_adicCompletionHenselizedLocalRingEquiv (q : PrimeSpectrum P) (a : k) :
    adicCompletionHenselizedLocalRingEquiv q
        (algebraMap k
          (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q)) a) =
      algebraMap k
        (AdicCompletion (henselizedMaximalIdealAt q) (henselizedLocalRingAt q)) a := by
  have h := DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap
      (algebraMap (localRingAt q) (henselizedLocalRingAt q))
      (IsLocalRing.maximalIdeal (localRingAt q)) (henselizedMaximalIdealAt q) le_rfl)
    (algebraMap k (localRingAt q) a)
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  change adicCompletionMap (algebraMap (localRingAt q) (henselizedLocalRingAt q))
      (IsLocalRing.maximalIdeal (localRingAt q)) (henselizedMaximalIdealAt q) le_rfl
      (algebraMap k
        (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q)) a) = _
  rw [IsScalarTower.algebraMap_apply k (localRingAt q)
    (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q)), h,
    IsScalarTower.algebraMap_apply k (henselizedLocalRingAt q)
      (AdicCompletion (henselizedMaximalIdealAt q) (henselizedLocalRingAt q))]
  rfl

/-- The inverse identification, from the completion of the henselization back to the completion
of the local ring, is `k`-linear. -/
public theorem algebraMap_adicCompletionHenselizedLocalRingEquiv_symm
    (q : PrimeSpectrum P) (a : k) :
    (adicCompletionHenselizedLocalRingEquiv q).symm
        (algebraMap k
          (AdicCompletion (henselizedMaximalIdealAt q) (henselizedLocalRingAt q)) a) =
      algebraMap k
        (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q)) a := by
  apply (adicCompletionHenselizedLocalRingEquiv q).injective
  rw [RingEquiv.apply_symm_apply, algebraMap_adicCompletionHenselizedLocalRingEquiv]

/-- **The third map of the chain of Stacks 0DZF**, at the tag's own target: complete each
henselized local ring and read the result as the completion `P^∧_{𝔪 i}` of the local ring
itself. -/
public noncomputable def completedLocalRingFunctors {ι : Type uι} (m : ι → PrimeSpectrum P)
    [Algebra.FiniteType k P] :
    BasedFunctor
      (piBasedCategory fun i =>
        ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i)))) :=
  BasedFunctor.comp (completionFunctors (Λ := Λ) (k := k) m)
    (piMap fun i => ringDeformationTransport
      (adicCompletionHenselizedLocalRingEquiv (m i)).symm
      (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (m i)))

end CompletedLocalRing

/-- Smoothness of a functor into a product of ring deformation categories can be checked after
composing with the fully faithful comparison `Deformation.Examples.piDeformationFunctor`. -/
private theorem isSmooth_of_comp_piDeformationFunctor {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (F : BasedFunctor 𝓕 (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i)))
    (h : IsSmooth (BasedFunctor.comp F (piDeformationFunctor (Λ := Λ) (k := k) R))) :
    IsSmooth F :=
  have := piDeformationFunctor_full (Λ := Λ) (k := k) R
  have := piDeformationFunctor_faithful (Λ := Λ) (k := k) R
  isSmooth_of_comp_fullyFaithful F _ h

/-- The comparison `Deformation.Examples.piDeformationFunctor` is injective on isomorphism
classes. -/
private theorem injective_mapIsomorphismClasses_piDeformationFunctor {ι : Type w} [Finite ι]
    (R : ι → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)]
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k) :
    Function.Injective (mapIsomorphismClasses (isCofiberedInGroupoids_pi_ringDeformation R)
      isCofiberedInGroupoids_ringDeformationProjection
      (piDeformationFunctor (Λ := Λ) (k := k) R) A) :=
  have := piDeformationFunctor_full (Λ := Λ) (k := k) R
  have := piDeformationFunctor_faithful (Λ := Λ) (k := k) R
  mapIsomorphismClasses_injective _ _ _ A

/-! ### The two legs: a composite of the chain descends to its first factors

Both legs have the same shape. The source proves a conclusion about a functor
`𝓓_P ⟶ 𝓓_{R}` for a single ring `R` -- `R = P^h_J` for the henselization leg, `R = P^∧_J` for
the completion leg -- and then transports it along a ring isomorphism `R ≅ ∏ R i`. What results
is a conclusion about the composite of the leg of the chain with the comparison
`Deformation.Examples.piDeformationFunctor`, and the conclusion for the leg itself follows
because that comparison is fully faithful.
-/

section Legs

variable {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)

attribute [local instance 100] henselizationAlgebra

/-- **Smoothness of the composite of the first two maps of the chain.** This is the source's
third step: **Stacks 0DZD** applied to `P` itself with `J = 𝔪 1 ∩ … ∩ 𝔪 n`, transported along
`P^h_J ≅ ∏ P^h_{𝔪 i}`, and then read at the product of the deformation categories through the
fully faithful comparison `Deformation.Examples.piDeformationFunctor`. -/
public theorem isSmooth_comp_firstTwoMapsOfChain
    [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
      (∀ i, henselizedLocalRingAt (m i)))
    (he : ∀ a : k, e (algebraMap k (henselization P (⨅ i, (m i).asIdeal) : Type w) a) =
      algebraMap k (∀ i, henselizedLocalRingAt (m i)) a)
    (hcmp : BasedFunctor.comp
          (henselizationFunctor (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal)).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
            (piDeformationFunctor (Λ := Λ) (k := k)
              fun i => henselizedLocalRingAt (m i)))) :
    IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (henselizationFunctors (Λ := Λ) (k := k) m)) := by
  refine isSmooth_of_comp_piDeformationFunctor _ _ ?_
  exact isSmooth_of_iso hcmp.symm
    (isSmooth_comp _ _
      (isSmooth_henselizationFunctor P (⨅ i, (m i).asIdeal) (isSmoothAt_of_not_iInf_le m hsm))
      (isSmooth_ringDeformationTransport e he))

/-- **The tangent-space conclusion for the composite of the first two maps of the chain.** Same
route as `Deformation.Examples.isSmooth_comp_firstTwoMapsOfChain`, with
the descent along the comparison performed by its injectivity on isomorphism classes. -/
public theorem bijective_differential_comp_firstTwoMapsOfChain
    [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (e : (henselization P (⨅ i, (m i).asIdeal) : Type w) ≃+*
      (∀ i, henselizedLocalRingAt (m i)))
    (he : ∀ a : k, e (algebraMap k (henselization P (⨅ i, (m i).asIdeal) : Type w) a) =
      algebraMap k (∀ i, henselizedLocalRingAt (m i)) a)
    (hcmp : BasedFunctor.comp
          (henselizationFunctor (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal)).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
            (piDeformationFunctor (Λ := Λ) (k := k)
              fun i => henselizedLocalRingAt (m i)))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (henselizationFunctors (Λ := Λ) (k := k) m))) := by
  let hP := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P)
  let hJ := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := (henselization P (⨅ i, (m i).asIdeal) : Type w))
  let hPi := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  let hProd := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := ∀ i, henselizedLocalRingAt (m i))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let H := (henselizationFunctor (Λ := Λ) (k := k) (⨅ i, (m i).asIdeal)).functor
  let T := ringDeformationTransport (Λ := Λ) e he
  let F := BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
    (henselizationFunctors (Λ := Λ) (k := k) m)
  let E := piDeformationFunctor (Λ := Λ) (k := k) fun i => henselizedLocalRingAt (m i)
  have hdH : Function.Bijective (mapIsomorphismClasses hP hJ H A) :=
    bijective_differential_henselizationFunctor P (⨅ i, (m i).asIdeal)
      (isSmoothAt_of_not_iInf_le m hsm)
  have hdT : Function.Bijective (mapIsomorphismClasses hJ hProd T A) :=
    bijective_differential_ringDeformationTransport (Λ := Λ) e he
  exact (bijective_comp_mapIsomorphismClasses_of_iso hP hJ hPi hProd hcmp A hdH hdT).of_comp_left
    (injective_mapIsomorphismClasses_piDeformationFunctor _ A)

/-- **Smoothness of the composite of all three maps of the chain.** This is the source's second
step: **Stacks 0DZ5** applied to `P` itself with `J = 𝔪 1 ∩ … ∩ 𝔪 n`, transported along
`P^∧_J ≅ ∏ (P^h_{𝔪 i})^∧`, and then read at the product of the deformation categories through
the fully faithful comparison `Deformation.Examples.piDeformationFunctor`. -/
public theorem isSmooth_comp_allThreeMapsOfChain
    [Algebra.FiniteType k P] [IsNoetherianRing P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (e : AdicCompletion (⨅ i, (m i).asIdeal) P ≃+*
      (∀ i, AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))))
    (he : ∀ a : k, e (algebraMap k (AdicCompletion (⨅ i, (m i).asIdeal) P) a) =
      algebraMap k
        (∀ i, AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))) a)
    (hcmp : BasedFunctor.comp
          (adicCompletionFunctor (Λ := Λ) (k := k) P (⨅ i, (m i).asIdeal)).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
            (BasedFunctor.comp (completionFunctors (Λ := Λ) (k := k) m)
              (piDeformationFunctor (Λ := Λ) (k := k) fun i =>
                AdicCompletion (henselizedMaximalIdealAt (m i))
                  (henselizedLocalRingAt (m i)))))) :
    IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
        (completionFunctors (Λ := Λ) (k := k) m))) := by
  refine isSmooth_of_comp_piDeformationFunctor _ _ ?_
  exact isSmooth_of_iso hcmp.symm
    (isSmooth_comp _ _
      (isSmooth_adicCompletionFunctor P (⨅ i, (m i).asIdeal)
        (isSmoothAt_of_not_iInf_le m hsm))
      (isSmooth_ringDeformationTransport e he))

/-- **The tangent-space conclusion for the composite of all three maps of the chain.** Same route
as `Deformation.Examples.isSmooth_comp_allThreeMapsOfChain`. -/
public theorem bijective_differential_comp_allThreeMapsOfChain
    [Algebra.FiniteType k P] [IsNoetherianRing P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (e : AdicCompletion (⨅ i, (m i).asIdeal) P ≃+*
      (∀ i, AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))))
    (he : ∀ a : k, e (algebraMap k (AdicCompletion (⨅ i, (m i).asIdeal) P) a) =
      algebraMap k
        (∀ i, AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))) a)
    (hcmp : BasedFunctor.comp
          (adicCompletionFunctor (Λ := Λ) (k := k) P (⨅ i, (m i).asIdeal)).functor
          (ringDeformationTransport e he) ≅
        BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
            (BasedFunctor.comp (completionFunctors (Λ := Λ) (k := k) m)
              (piDeformationFunctor (Λ := Λ) (k := k) fun i =>
                AdicCompletion (henselizedMaximalIdealAt (m i))
                  (henselizedLocalRingAt (m i)))))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
          (completionFunctors (Λ := Λ) (k := k) m)))) := by
  let hP := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P)
  let hJ := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := AdicCompletion (⨅ i, (m i).asIdeal) P)
  let hPi := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
    AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))
  let hProd := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
    (P := ∀ i, AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let D := (adicCompletionFunctor (Λ := Λ) (k := k) P (⨅ i, (m i).asIdeal)).functor
  let T := ringDeformationTransport (Λ := Λ) e he
  let F := BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
    (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
      (completionFunctors (Λ := Λ) (k := k) m))
  let E := piDeformationFunctor (Λ := Λ) (k := k) fun i =>
    AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))
  have hdD : Function.Bijective (mapIsomorphismClasses hP hJ D A) :=
    bijective_differential_adicCompletionFunctor P (⨅ i, (m i).asIdeal)
      (isSmoothAt_of_not_iInf_le m hsm)
  have hdT : Function.Bijective (mapIsomorphismClasses hJ hProd T A) :=
    bijective_differential_ringDeformationTransport (Λ := Λ) e he
  exact (bijective_comp_mapIsomorphismClasses_of_iso hP hJ hPi hProd hcmp A hdD hdT).of_comp_left
    (injective_mapIsomorphismClasses_piDeformationFunctor _ A)

end Legs

/-! ### The source's last step at one singular point, at the ring the chain is stated at -/

section PerFactor

variable {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
  (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
  (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)

attribute [local instance 100] henselizationAlgebra

include hmax hinj hsm in
/-- **The source's last step at the factor `i`**, both conclusions: the henselization functor of
the local ring `P_{𝔪 i}` along its maximal ideal is smooth and induces an isomorphism on tangent
spaces.

Invert an element lying in every `𝔪 j` with `j ≠ i` and in no `𝔪 i`
(`Deformation.Examples.exists_principal_neighborhood`). In the resulting principal localization,
still of finite type over `k`, the image of `𝔪 i` is the only singular point
(`Deformation.Examples.asIdeal_eq_map_of_not_isSmoothAt_awayLocalization`), so **Stacks 0DZ9** and
**Stacks 0DZD** both apply there and
`Deformation.Examples.isSmooth_henselizationFunctor_localizationAtPrime` concludes; transport back
to `P_{𝔪 i}` along `Deformation.Examples.localRingAwayEquiv`. -/
public theorem henselizationFunctor_localRingAt_conclusions [Algebra.FiniteType k P] (i : ι) :
    IsSmooth (henselizationFunctor (Λ := Λ) (k := k)
        (IsLocalRing.maximalIdeal (localRingAt (m i)))).functor ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
          (P := localRingAt (m i)))
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
          (P := henselizedLocalRingAt (m i)))
        (henselizationFunctor (Λ := Λ) (k := k)
          (IsLocalRing.maximalIdeal (localRingAt (m i)))).functor) := by
  obtain ⟨s, hs, hs'⟩ := exists_principal_neighborhood m hmax hinj i
  let := isMaximal_map_awayLocalization m hmax hs
  obtain ⟨e₁, hchar₁⟩ := exists_ringEquiv_henselization_localization_atMaximalIdeal
    ((m i).asIdeal.map (algebraMap P (Localization.Away s)))
  obtain ⟨cmp₁⟩ := nonempty_basedIso_henselizationLocalization (Λ := Λ) (k := k)
    ((m i).asIdeal.map (algebraMap P (Localization.Away s))) e₁
    (algebraMap_comm_of_henselizationLocalizationEquiv (k := k)
      ((m i).asIdeal.map (algebraMap P (Localization.Away s))) e₁ hchar₁) hchar₁
  have hsing := asIdeal_eq_map_of_not_isSmoothAt_awayLocalization m hsm hs hs'
  have hstepS := isSmooth_henselizationFunctor_localizationAtPrime (Λ := Λ) (k := k)
    ((m i).asIdeal.map (algebraMap P (Localization.Away s))) hsing e₁
    (algebraMap_comm_of_henselizationLocalizationEquiv (k := k)
      ((m i).asIdeal.map (algebraMap P (Localization.Away s))) e₁ hchar₁) cmp₁
  have hstepD := bijective_differential_henselizationFunctor_localizationAtPrime
    (Λ := Λ) (k := k) ((m i).asIdeal.map (algebraMap P (Localization.Away s))) hsing e₁
    (algebraMap_comm_of_henselizationLocalizationEquiv (k := k)
      ((m i).asIdeal.map (algebraMap P (Localization.Away s))) e₁ hchar₁) cmp₁
  obtain ⟨d, hchar₂⟩ := exists_ringEquiv_henselization_of_ringEquiv
    (localRingAwayEquiv m hmax hs).toRingEquiv
    (IsLocalRing.maximalIdeal
      (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl))
    (IsLocalRing.maximalIdeal (localRingAt (m i)))
    (map_maximalIdeal_localRingAwayEquiv m hmax hs)
  have hd := algebraMap_comm_of_henselizationCongrEquiv (k := k)
    (localRingAwayEquiv m hmax hs).toRingEquiv (algebraMap_localRingAwayEquiv m hmax hs)
    (IsLocalRing.maximalIdeal
      (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl))
    (IsLocalRing.maximalIdeal (localRingAt (m i))) d hchar₂
  obtain ⟨cmp₂⟩ := nonempty_basedIso_henselizationFunctor_congr (Λ := Λ) (k := k)
    (localRingAwayEquiv m hmax hs).toRingEquiv (algebraMap_localRingAwayEquiv m hmax hs)
    (IsLocalRing.maximalIdeal
      (Localization ((m i).asIdeal.map (algebraMap P (Localization.Away s))).primeCompl))
    (IsLocalRing.maximalIdeal (localRingAt (m i))) d
    (map_maximalIdeal_localRingAwayEquiv m hmax hs) hd hchar₂
  exact ⟨isSmooth_henselizationFunctor_of_ringEquiv _ _ _ _ d hd cmp₂ hstepS,
    bijective_differential_henselizationFunctor_of_ringEquiv _ _ _ _ d hd cmp₂ hstepD⟩

end PerFactor

/-! ### The vector-space structure on the tangent space of a product -/

/-- A finite product of ring deformation categories is a deformation category: it satisfies
Rim–Schlessinger factorwise. -/
public theorem isDeformationCategory_pi_ringDeformation {ι : Type uι} (R : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    IsDeformationCategory
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i)).p :=
  piBasedCategory_isDeformationCategory _
    fun i => ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) (R i)

/-- **Schlessinger's condition (S2) for a product of ring deformation categories**, which is
what exposes the canonical `k`-vector-space structure of **Stacks 06IH** on its tangent space.
It comes from the product being a deformation category, hence satisfying (RS). -/
public theorem schlessingerConditionS2_pi_ringDeformation {ι : Type uι} (R : ι → Type w)
    [∀ i, CommRing (R i)] [∀ i, Algebra k (R i)] :
    SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i => ringDeformationBasedCategory Λ k (R i))
        (isCofiberedInGroupoids_pi_ringDeformation R))) :=
  schlessingerConditionS2_of_isIsomorphismClasses _ _
    (schlessingerConditionS2_of_satisfiesRS
      (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) R).satisfiesRS)
    (.inl (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) R).predeformation)

/-! ### Recovering the individual maps of the chain from the composites -/

section Cancellation

variable {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)

attribute [local instance 100] henselizationAlgebra

omit [Finite ι] in
/-- **The tangent-space conclusion for the first map of the chain**, from the same conclusion for
the composite of the first two and for the second map factor by factor. -/
public theorem bijective_differential_localizationFunctors_aux
    (hdK : ∀ i, Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := localRingAt (m i)))
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
        (P := henselizedLocalRingAt (m i)))
      (henselizationFunctor (Λ := Λ) (k := k)
        (IsLocalRing.maximalIdeal (localRingAt (m i)))).functor))
    (hcomp : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (henselizationFunctors (Λ := Λ) (k := k) m)))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (localizationFunctors (Λ := Λ) (k := k) m)) := by
  let hP := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P)
  let hLoc := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => localRingAt (m i)
  let hHen := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let L := localizationFunctors (Λ := Λ) (k := k) m
  let H := henselizationFunctors (Λ := Λ) (k := k) m
  have hdH : Function.Bijective (mapIsomorphismClasses hLoc hHen H A) :=
    piMap_mapIsomorphismClasses_bijective _ _ _ A hdK
  have hcomp' : Function.Bijective
      ((mapIsomorphismClasses hLoc hHen H A) ∘ (mapIsomorphismClasses hP hLoc L A)) := by
    rw [Function.comp_def, ← mapIsomorphismClasses_comp hP hLoc hHen L H A]
    exact hcomp
  exact hcomp'.of_comp_left hdH.injective

omit [Finite ι] in
/-- **Smoothness of the first map of the chain**, from the criterion of **Stacks 0DYP**: its
differential is surjective, and a deformation of `P` lifts along a small extension whenever its
image under the composite of the first two maps does, which is smoothness of that composite. -/
public theorem isSmooth_localizationFunctors_aux
    (hdL : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (localizationFunctors (Λ := Λ) (k := k) m)))
    (hcomp : IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (henselizationFunctors (Λ := Λ) (k := k) m))) :
    IsSmooth (localizationFunctors (Λ := Λ) (k := k) m) := by
  refine (isSmooth_iff_differential_surjective_and_lifts
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P)
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
    (localizationFunctors (Λ := Λ) (k := k) m)).mpr ⟨hdL.surjective, ?_⟩
  intro B A f hf x hx
  obtain ⟨y, g, hg⟩ := hx
  let := hg
  have hHg : (piBasedCategory fun i =>
      ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i))).p.IsHomLift f
      ((henselizationFunctors (Λ := Λ) (k := k) m).map g) :=
    Functor.isHomLift_map_of_comp_eq (henselizationFunctors (Λ := Λ) (k := k) m).w f g
  obtain ⟨x', h, _, hh, -⟩ := hcomp f hf.2.2.2.2.1
    ((henselizationFunctors (Λ := Λ) (k := k) m).obj y) x.val
    ((henselizationFunctors (Λ := Λ) (k := k) m).map g) hHg
  exact ⟨x', h, hh⟩

omit [Finite ι] in
/-- **Smoothness of the second map of the chain**, by cancelling the first out of the composite:
the first map is smooth, hence essentially surjective. -/
public theorem isSmooth_henselizationFunctors_aux
    (hL : IsSmooth (localizationFunctors (Λ := Λ) (k := k) m))
    (hcomp : IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (henselizationFunctors (Λ := Λ) (k := k) m))) :
    IsSmooth (henselizationFunctors (Λ := Λ) (k := k) m) := by
  exact isSmooth_of_isSmooth_comp_of_isSmooth
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation
    (piBasedCategory_isPredeformationCategory _
      fun i => (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k)
        (localRingAt (m i))).predeformation) _ hL hcomp

omit [Finite ι] in
/-- **The tangent-space conclusion for the second map of the chain**, by cancelling the first out
of the composite, which for the differential needs nothing but bijectivity of the first. -/
public theorem bijective_differential_henselizationFunctors_aux
    (hdL : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (localizationFunctors (Λ := Λ) (k := k) m)))
    (hcomp : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (henselizationFunctors (Λ := Λ) (k := k) m)))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (henselizationFunctors (Λ := Λ) (k := k) m)) := by
  let hP := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P)
  let hLoc := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => localRingAt (m i)
  let hHen := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let L := localizationFunctors (Λ := Λ) (k := k) m
  let H := henselizationFunctors (Λ := Λ) (k := k) m
  have hcomp' : Function.Bijective
      ((mapIsomorphismClasses hLoc hHen H A) ∘ (mapIsomorphismClasses hP hLoc L A)) := by
    rw [Function.comp_def, ← mapIsomorphismClasses_comp hP hLoc hHen L H A]
    exact hcomp
  exact (hdL.of_comp_iff _).mp hcomp'

omit [Finite ι] in
/-- **Smoothness of the third map of the chain**, by cancelling the composite of the first two
out of the composite of all three; the former is smooth, hence essentially surjective. -/
public theorem isSmooth_completionFunctors_aux [Algebra.FiniteType k P]
    (hcomp₂ : IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (henselizationFunctors (Λ := Λ) (k := k) m)))
    (hcomp₃ : IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
      (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
        (completionFunctors (Λ := Λ) (k := k) m)))) :
    IsSmooth (completionFunctors (Λ := Λ) (k := k) m) := by
  exact isSmooth_of_isSmooth_comp_of_isSmooth
    (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P).predeformation
    (piBasedCategory_isPredeformationCategory _
      fun i => (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k)
        (henselizedLocalRingAt (m i))).predeformation) _ hcomp₂ hcomp₃

omit [Finite ι] in
/-- **The tangent-space conclusion for the third map of the chain**, by cancelling the composite
of the first two out of the composite of all three. -/
public theorem bijective_differential_completionFunctors_aux [Algebra.FiniteType k P]
    (hcomp₂ : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (henselizationFunctors (Λ := Λ) (k := k) m))))
    (hcomp₃ : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
      (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
          (completionFunctors (Λ := Λ) (k := k) m))))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
      (completionFunctors (Λ := Λ) (k := k) m)) := by
  let hP := isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P)
  let hHen := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  let hCom := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
    AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let F := BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
    (henselizationFunctors (Λ := Λ) (k := k) m)
  let C := completionFunctors (Λ := Λ) (k := k) m
  have hcomp₃' : Function.Bijective
      ((mapIsomorphismClasses hHen hCom C A) ∘ (mapIsomorphismClasses hP hHen F A)) := by
    rw [Function.comp_def, ← mapIsomorphismClasses_comp hP hHen hCom F C A]
    exact hcomp₃
  exact (hcomp₂.of_comp_iff _).mp hcomp₃'

omit [Finite ι] in
/-- **Smoothness of the third map of the chain at the tag's own target**, from smoothness at the
completion of the henselization: the two differ by the transport along the identification
`(P_{𝔪 i})^∧ ≅ (P^h_{𝔪 i})^∧` in each factor, and the transport is smooth. -/
public theorem isSmooth_completedLocalRingFunctors_aux [Algebra.FiniteType k P]
    (hC : IsSmooth (completionFunctors (Λ := Λ) (k := k) m)) :
    IsSmooth (completedLocalRingFunctors (Λ := Λ) (k := k) m) :=
  isSmooth_comp _ _ hC
    (piMap_isSmooth_of_components _ fun i =>
      isSmooth_ringDeformationTransport (adicCompletionHenselizedLocalRingEquiv (m i)).symm
        (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (m i)))

omit [Finite ι] in
/-- **The tangent-space conclusion for the third map of the chain at the tag's own target.** -/
public theorem bijective_differential_completedLocalRingFunctors_aux [Algebra.FiniteType k P]
    (hdC : Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
      (completionFunctors (Λ := Λ) (k := k) m))) :
    Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i)))
      (completedLocalRingFunctors (Λ := Λ) (k := k) m)) := by
  let hHen := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  let hCom := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
    AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i))
  let hLoc := isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
    AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let C := completionFunctors (Λ := Λ) (k := k) m
  let T := piMap fun i => ringDeformationTransport (Λ := Λ) (k := k)
    (adicCompletionHenselizedLocalRingEquiv (m i)).symm
    (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (k := k) (m i))
  have hdT : Function.Bijective (mapIsomorphismClasses hCom hLoc T A) :=
    piMap_mapIsomorphismClasses_bijective _ _ _ A fun i =>
      bijective_differential_ringDeformationTransport (Λ := Λ) (k := k)
        (adicCompletionHenselizedLocalRingEquiv (m i)).symm
        (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (k := k) (m i))
  change Function.Bijective (mapIsomorphismClasses hHen hLoc (BasedFunctor.comp C T) A)
  rw [mapIsomorphismClasses_comp hHen hCom hLoc C T A]
  exact hdT.comp hdC

end Cancellation

/-! ### Finite-dimensionality of the tangent spaces along the chain -/

section FiniteDimensional

open Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] moduleBaseNaiveCotangentExtOne isScalarTowerBaseNaiveCotangentExtOne

attribute [local instance 100] henselizationAlgebra

/-- **Finite-dimensionality travels along a tangent-space isomorphism.** A based functor of
predeformation categories whose associated functors of isomorphism classes satisfy (S2) has a
`k`-linear differential by **Stacks 06IJ**; if it is moreover bijective and the source tangent
space is finite dimensional, so is the target's. -/
public theorem finiteDimensional_artinianTangentSpace_of_bijective_differential
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsPredeformationCategory 𝓕.p) (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2𝓕 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (hS2𝓖 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (φ : BasedFunctor 𝓕 𝓖)
    (hbij : Function.Bijective (differential h𝓕.cofibered h𝓖.cofibered φ)) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
    ∀ _ : FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)),
      FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2𝓖⟩
  intro hfd
  exact (LinearEquiv.ofBijective
    (IsLinearMap.mk' _ (differential_isLinearMap 𝓕 𝓖 h𝓕 h𝓖 hS2𝓕 hS2𝓖 φ)) hbij).finiteDimensional

/-- **Finite-dimensionality of all four tangent spaces of the chain of Stacks 0DZF**, given that
the three maps induce isomorphisms on them. The source tangent space is finite dimensional by
**Stacks 0DY4(2)** read through **Stacks 0DY3**, and finite-dimensionality then travels along the
chain because each differential is a `k`-linear bijection. -/
public theorem finiteDimensional_artinianTangentSpace_chain_aux
    {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P) [Algebra.FiniteType k P]
    (hfinite : {q : PrimeSpectrum P | ¬ Algebra.IsSmoothAt k q.asIdeal}.Finite)
    (hd₁ : Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (localizationFunctors (Λ := Λ) (k := k) m)))
    (hd₂ : Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (henselizationFunctors (Λ := Λ) (k := k) m)))
    (hd₃ : Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i)))
      (completedLocalRingFunctors (Λ := Λ) (k := k) m))) :
    letI : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
      ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection))) :=
      ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i => ringDeformationBasedCategory Λ k (localRingAt (m i))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => localRingAt (m i)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (localRingAt (m i)))
        (isCofiberedInGroupoids_pi_ringDeformation fun i => localRingAt (m i))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i)⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
        (isCofiberedInGroupoids_pi_ringDeformation fun i => henselizedLocalRingAt (m i))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i)⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i => ringDeformationBasedCategory Λ k
          (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
            (localRingAt (m i)))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
          (localRingAt (m i))).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i => ringDeformationBasedCategory Λ k
          (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))))
        (isCofiberedInGroupoids_pi_ringDeformation fun i =>
          AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
            (localRingAt (m i)))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))⟩
    FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection)) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i =>
            ringDeformationBasedCategory Λ k (localRingAt (m i)))
          (isCofiberedInGroupoids_pi_ringDeformation fun i => localRingAt (m i)))) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i =>
            ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
          (isCofiberedInGroupoids_pi_ringDeformation fun i => henselizedLocalRingAt (m i)))) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i => ringDeformationBasedCategory Λ k
            (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))))
          (isCofiberedInGroupoids_pi_ringDeformation fun i =>
            AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
              (localRingAt (m i))))) := by
  have h₁ := finiteDimensional_artinianTangentSpace_ringDeformation (Λ := Λ) (k := k)
    (P := P) hfinite
  have h₂ := finiteDimensional_artinianTangentSpace_of_bijective_differential
    (ringDeformationCategory_isDeformationCategory P).predeformation
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => localRingAt (m i)).predeformation
    (schlessingerConditionS2_ringDeformation Λ k P)
    (schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
    (localizationFunctors (Λ := Λ) (k := k) m) hd₁ h₁
  have h₃ := finiteDimensional_artinianTangentSpace_of_bijective_differential
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => localRingAt (m i)).predeformation
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => henselizedLocalRingAt (m i)).predeformation
    (schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
    (schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => henselizedLocalRingAt (m i))
    (henselizationFunctors (Λ := Λ) (k := k) m) hd₂ h₂
  have h₄ := finiteDimensional_artinianTangentSpace_of_bijective_differential
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => henselizedLocalRingAt (m i)).predeformation
    (isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
      AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
        (localRingAt (m i))).predeformation
    (schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k)
      fun i => henselizedLocalRingAt (m i))
    (schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
      AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i)))
    (completedLocalRingFunctors (Λ := Λ) (k := k) m) hd₃ h₃
  exact ⟨h₁, h₂, h₃, h₄⟩

end FiniteDimensional


/-! ### The seven clauses of Stacks 0DZF -/

section Clauses

variable {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
  (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
  (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)

attribute [local instance 100] henselizationAlgebra

include hmax hinj hsm in
/-- **The composite of the first two maps of the chain**, both conclusions, assembled from
**Stacks 0DZD** at `(P, J)` and the comparison of
`Deformation.Examples.nonempty_basedIso_henselizationPi`. -/
private theorem legTwoMaps_conclusions [Algebra.FiniteType k P] :
    IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (henselizationFunctors (Λ := Λ) (k := k) m)) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => henselizedLocalRingAt (m i))
        (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (henselizationFunctors (Λ := Λ) (k := k) m))) := by
  obtain ⟨e, hchar⟩ := exists_ringEquiv_henselization_iInf_pi_henselizedLocalRing m hmax hinj
  have he := algebraMap_comm_of_henselizationPiRingEquiv (k := k) m e hchar
  obtain ⟨cmp⟩ := nonempty_basedIso_henselizationPi (Λ := Λ) (k := k) m hmax hinj e he hchar
  exact ⟨isSmooth_comp_firstTwoMapsOfChain m hsm e he cmp,
    bijective_differential_comp_firstTwoMapsOfChain m hsm e he cmp⟩

include hmax hinj hsm in
/-- **The composite of all three maps of the chain**, both conclusions, assembled from
**Stacks 0DZ5** at `(P, J)` and the comparison of
`Deformation.Examples.nonempty_basedIso_adicCompletionFunctor_completionFunctors`. -/
private theorem legThreeMaps_conclusions [Algebra.FiniteType k P] :
    IsSmooth (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
        (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
          (completionFunctors (Λ := Λ) (k := k) m))) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
          AdicCompletion (henselizedMaximalIdealAt (m i)) (henselizedLocalRingAt (m i)))
        (BasedFunctor.comp (localizationFunctors (Λ := Λ) (k := k) m)
          (BasedFunctor.comp (henselizationFunctors (Λ := Λ) (k := k) m)
            (completionFunctors (Λ := Λ) (k := k) m)))) := by
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  obtain ⟨cmp⟩ := nonempty_basedIso_adicCompletionFunctor_completionFunctors
    (Λ := Λ) (k := k) m hmax hinj (adicCompletionPiHenselizedEquiv m hmax hinj)
    (algebraMap_adicCompletionPiHenselizedEquiv m hmax hinj)
    (apply_algebraMap_adicCompletionPiHenselizedEquiv m hmax hinj)
  exact ⟨isSmooth_comp_allThreeMapsOfChain m hsm _ _ cmp,
    bijective_differential_comp_allThreeMapsOfChain
      m hsm _ _ cmp⟩

/-! #### Clause 2: the first map induces an isomorphism on tangent spaces -/

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 2.** The first map `Def_P → ∏ Def_{P_{𝔪 i}}` of the chain induces an
isomorphism on tangent spaces. -/
@[stacks 0DZF "clause 2 of seven: the first map of the chain, `Def_P -> ∏ Def_{P_{𝔪 i}}`, \
induces an isomorphism on tangent spaces. Under the tag's own hypotheses and no others: `P` of \
finite type over `k`, the `𝔪 i` maximal and pairwise distinct, and every prime at which `P` is \
not smooth one of the `𝔪 i`. The product of deformation categories is the product over \
`𝒞_Λ`, which is the reading the proof of Stacks 0DZN records. The index type is required to \
live in the universe of `P`; any finite family can be reindexed into it"]
public theorem bijective_differential_localizationFunctors [Algebra.FiniteType k P] :
    Function.Bijective (differential
      (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := P))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (localizationFunctors (Λ := Λ) (k := k) m)) :=
  bijective_differential_localizationFunctors_aux m
    (fun i => (henselizationFunctor_localRingAt_conclusions m hmax hinj hsm i).2)
    (legTwoMaps_conclusions m hmax hinj hsm).2

/-! #### Clause 1: the first map is smooth -/

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 1.** The first map `Def_P → ∏ Def_{P_{𝔪 i}}` of the chain is smooth. -/
@[stacks 0DZF "clause 1 of seven: the first map of the chain, `Def_P -> ∏ Def_{P_{𝔪 i}}`, is \
smooth. Under the tag's own hypotheses and no others. Obtained from the criterion of \
Stacks 0DYP: its differential is surjective by clause 2, and a deformation of `P` lifts along a \
small extension whenever its image under the composite of the first two maps does, which is \
smoothness of that composite"]
public theorem isSmooth_localizationFunctors [Algebra.FiniteType k P] :
    IsSmooth (localizationFunctors (Λ := Λ) (k := k) m) :=
  isSmooth_localizationFunctors_aux m
    (bijective_differential_localizationFunctors m hmax hinj hsm)
    (legTwoMaps_conclusions m hmax hinj hsm).1

/-! #### Clauses 3 and 4: the second map -/

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 3.** The second map `∏ Def_{P_{𝔪 i}} → ∏ Def_{P^h_{𝔪 i}}` of the chain
is smooth. -/
@[stacks 0DZF "clause 3 of seven: the second map of the chain, \
`∏ Def_{P_{𝔪 i}} -> ∏ Def_{P^h_{𝔪 i}}`, is smooth. Under the tag's own hypotheses and no \
others. Obtained by cancelling the first map out of the composite of the first two: the first \
map is smooth by clause 1, hence essentially surjective"]
public theorem isSmooth_henselizationFunctors [Algebra.FiniteType k P] :
    IsSmooth (henselizationFunctors (Λ := Λ) (k := k) m) :=
  isSmooth_henselizationFunctors_aux m
    (isSmooth_localizationFunctors m hmax hinj hsm)
    (legTwoMaps_conclusions m hmax hinj hsm).1

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 4.** The second map `∏ Def_{P_{𝔪 i}} → ∏ Def_{P^h_{𝔪 i}}` of the chain
induces an isomorphism on tangent spaces. -/
@[stacks 0DZF "clause 4 of seven: the second map of the chain, \
`∏ Def_{P_{𝔪 i}} -> ∏ Def_{P^h_{𝔪 i}}`, induces an isomorphism on tangent spaces. Under the \
tag's own hypotheses and no others. Obtained by cancelling the first map, which is bijective on \
tangent spaces by clause 2, out of the composite of the first two"]
public theorem bijective_differential_henselizationFunctors [Algebra.FiniteType k P] :
    Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (henselizationFunctors (Λ := Λ) (k := k) m)) :=
  bijective_differential_henselizationFunctors_aux m
    (bijective_differential_localizationFunctors m hmax hinj hsm)
    (legTwoMaps_conclusions m hmax hinj hsm).2

/-! #### Clauses 5 and 6: the third map -/

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 5.** The third map `∏ Def_{P^h_{𝔪 i}} → ∏ Def_{P^∧_{𝔪 i}}` of the
chain is smooth. The target is the tag's own: the deformation categories of the completions of
the *local rings*, which the completions of the henselizations are by
`Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing`. -/
@[stacks 0DZF "clause 5 of seven: the third map of the chain, \
`∏ Def_{P^h_{𝔪 i}} -> ∏ Def_{P^∧_{𝔪 i}}`, is smooth, with the target the tag's own -- the \
completions of the local rings, not of the henselizations, the two being identified by \
`Deformation.Examples.bijective_adicCompletionMap_henselizedLocalRing`, which is the source's \
parenthetical `the completion of the henselization is the completion`. Under the tag's own \
hypotheses and no others. Obtained by cancelling the composite of the first two maps, which is \
smooth, out of the composite of all three"]
public theorem isSmooth_completedLocalRingFunctors [Algebra.FiniteType k P] :
    IsSmooth (completedLocalRingFunctors (Λ := Λ) (k := k) m) :=
  isSmooth_completedLocalRingFunctors_aux m
    (isSmooth_completionFunctors_aux m (legTwoMaps_conclusions m hmax hinj hsm).1
      (legThreeMaps_conclusions m hmax hinj hsm).1)

include hmax hinj hsm in
/-- **Stacks 0DZF, clause 6.** The third map `∏ Def_{P^h_{𝔪 i}} → ∏ Def_{P^∧_{𝔪 i}}` of the
chain induces an isomorphism on tangent spaces. -/
@[stacks 0DZF "clause 6 of seven: the third map of the chain, \
`∏ Def_{P^h_{𝔪 i}} -> ∏ Def_{P^∧_{𝔪 i}}`, induces an isomorphism on tangent spaces, with the \
target the tag's own -- the completions of the local rings. Under the tag's own hypotheses and \
no others. Obtained by cancelling the composite of the first two maps out of the composite of \
all three"]
public theorem bijective_differential_completedLocalRingFunctors [Algebra.FiniteType k P] :
    Function.Bijective (differential
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i))
      (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i)))
      (completedLocalRingFunctors (Λ := Λ) (k := k) m)) :=
  bijective_differential_completedLocalRingFunctors_aux m
    (bijective_differential_completionFunctors_aux m
      (legTwoMaps_conclusions m hmax hinj hsm).2
      (legThreeMaps_conclusions m hmax hinj hsm).2)

/-! #### Clause 7: the four tangent spaces are finite dimensional -/

/-- **Stacks 0DZF, clause 7.** All four tangent spaces along the chain are finite dimensional
over `k`. The source's is `Ext¹_P(NL_{P/k}, P)` by **Stacks 0DY3** and is finite dimensional by
**Stacks 0DY4(2)**; the other three are carried along by the tangent-space isomorphisms of
clauses 2, 4 and 6, each of which is `k`-linear by **Stacks 06IJ**. -/
@[stacks 0DZF "clause 7 of seven: the tangent spaces of all four terms of the chain are \
finite dimensional over `k`, which is the tag's `finite dimensional tangent spaces`. Under the \
tag's own hypotheses and no others -- in particular the finiteness of the non-smooth locus that \
Stacks 0DY4 wants is derived here from the tag's `smooth except at 𝔪 1, ..., 𝔪 n`. The source's \
tangent space is `Ext¹_P(NL_{P/k}, P)` by Stacks 0DY3; the other three are carried along by \
clauses 2, 4 and 6, each differential being `k`-linear by Stacks 06IJ"]
public theorem finiteDimensional_artinianTangentSpace_chain
    {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P) [Algebra.FiniteType k P]
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q) :
    letI : Fact (IsPredeformationCategory (ringDeformationBasedCategory Λ k P).p) :=
      ⟨(ringDeformationCategory_isDeformationCategory P).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (ringDeformationBasedCategory Λ k P)
        isCofiberedInGroupoids_ringDeformationProjection))) :=
      ⟨schlessingerConditionS2_ringDeformation Λ k P⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i => ringDeformationBasedCategory Λ k (localRingAt (m i))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => localRingAt (m i)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (localRingAt (m i)))
        (isCofiberedInGroupoids_pi_ringDeformation fun i => localRingAt (m i))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i => localRingAt (m i)⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i)).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i =>
          ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
        (isCofiberedInGroupoids_pi_ringDeformation fun i => henselizedLocalRingAt (m i))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k)
        fun i => henselizedLocalRingAt (m i)⟩
    letI : Fact (IsPredeformationCategory
        (piBasedCategory fun i => ringDeformationBasedCategory Λ k
          (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
            (localRingAt (m i)))).p) :=
      ⟨(isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
          (localRingAt (m i))).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (piBasedCategory fun i => ringDeformationBasedCategory Λ k
          (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))))
        (isCofiberedInGroupoids_pi_ringDeformation fun i =>
          AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
            (localRingAt (m i)))))) :=
      ⟨schlessingerConditionS2_pi_ringDeformation (Λ := Λ) (k := k) fun i =>
        AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))⟩
    FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (ringDeformationBasedCategory Λ k P)
          isCofiberedInGroupoids_ringDeformationProjection)) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i =>
            ringDeformationBasedCategory Λ k (localRingAt (m i)))
          (isCofiberedInGroupoids_pi_ringDeformation fun i => localRingAt (m i)))) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i =>
            ringDeformationBasedCategory Λ k (henselizedLocalRingAt (m i)))
          (isCofiberedInGroupoids_pi_ringDeformation fun i => henselizedLocalRingAt (m i)))) ∧
      FiniteDimensional k (artinianTangentSpace Λ k
        (isomorphismClasses (piBasedCategory fun i => ringDeformationBasedCategory Λ k
            (AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i))) (localRingAt (m i))))
          (isCofiberedInGroupoids_pi_ringDeformation fun i =>
            AdicCompletion (IsLocalRing.maximalIdeal (localRingAt (m i)))
              (localRingAt (m i))))) :=
  finiteDimensional_artinianTangentSpace_chain_aux m
    (Set.Finite.subset (Set.finite_range m) fun q hq => hsm q hq)
    (bijective_differential_localizationFunctors m hmax hinj hsm)
    (bijective_differential_henselizationFunctors m hmax hinj hsm)
    (bijective_differential_completedLocalRingFunctors m hmax hinj hsm)

end Clauses

end Deformation.Examples
