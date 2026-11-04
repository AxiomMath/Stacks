module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresCriterion
public import StacksFrontier.RingTheory.Serre.LocalizationDepthCodimension
public import StacksFrontier.RingTheory.Serre.CohenMacaulay
public import StacksFrontier.RingTheory.Serre.RingEquiv
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.Flat.SliceNonZeroDivisor
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Catenary.Universes
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)`

Let `A` be a Noetherian ring, let `𝔞 ⊆ A` be an ideal and let `f ∈ 𝔞` be a nonzerodivisor — the
setting of Stacks 0DXW, whose third hypothesis is that `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` be finite
`A`-modules. Stacks 0EHI identifies that hypothesis, and gives a sufficient condition for it.

Over a universally catenary `A` whose local rings have Cohen--Macaulay formal fibres, Faltings'
theorem 0BJV says that `H^i_{V(𝔞)}(M)` is finite exactly in the degrees below the cutoff
`s_{A,𝔞}(M)` of 0BJR. For `M = A/fA` the cutoff is the infimum of `depth((A/f)_𝔭) + dim((A/𝔭)_𝔮)`
over the pairs of primes `𝔭 ⊆ 𝔮` with `𝔭 ∉ V(𝔞)` and `𝔮 ∈ V(𝔞)`, and the pairs with `𝔭 ∉ V(f)`
contribute nothing because `(A/fA)_𝔭` then vanishes and has infinite depth. So the two modules
are finite exactly when that sum exceeds `2` for all `𝔭 ∈ V(f) \ V(𝔞)` and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`.

The source's sufficient condition for this is that `A/fA` satisfy Serre's condition `(S₂)` and
that every irreducible component of `Z = V(𝔞)` have codimension at least `3` in
`Y = Spec(A/fA)`. Indeed `𝔮` contains a minimal prime of `𝔞`, so the image `𝔮̄` of `𝔮` in `A/fA`
has height at least `3`; Serre's condition makes `Spec` of the local ring `(A/fA)_𝔮̄`
equidimensional (0FIW), so in the universally catenary ring `A/fA` the height of `𝔮̄` splits as
`height 𝔭̄ + dim((A/𝔭)_𝔮)`; and `(S₂)` at `𝔭̄` bounds `depth((A/f)_𝔭)` below by
`min(2, height 𝔭̄)`. Since `dim((A/𝔭)_𝔮) ≥ 1`, those two bounds add up to more than `2`.

Finally, a Noetherian ring with a dualizing complex is universally catenary (0A80), and its
localizations again have dualizing complexes (0A7G), hence Gorenstein — so Cohen--Macaulay —
formal fibres (0AWY). This is the source's parenthetical.

## Main results

* `Stacks.LocalCohomology.finite_localCohomology_quotient_span_iff_two_lt_depth_add_height` —
  **Stacks 0EHI**, the three assertions of the remark conjoined.

## Implementation notes

The local cohomology modules are `Stacks.LocalCohomology.localCohomologyWithSupportIn` along
`PrimeSpectrum.zeroLocus 𝔞`, applied to `A/fA` placed in degree zero: the spelling of Stacks
0BJV. The quantities `depth((A/f)_𝔭)` and `dim((A/𝔭)_𝔮)` are spelled as in the cutoff
`Stacks.LocalCohomology.localCohomologyCutoff` of Stacks 0BJR, namely as `Module.depth` of
`(A/fA)_𝔭` over `A_𝔭` at its maximal ideal and as `Ideal.height` of the image of `𝔮` in `A/𝔭`.
Serre's condition is `PropertySkRing` of Definition 031P. The irreducible components of
`Z = V(𝔞)` are the minimal primes of `𝔞`, and the codimension in `Y` of the component cut out by
such a prime is the height of its image in `A/fA` — the same `height`-of-a-quotient spelling
that `Stacks.Algebraization.HasLocallyFreeCodimensionThreeCondition` uses for the codimension
bound of Stacks 0EJT.

Two auxiliary statements proved on the way are of independent interest: Serre's condition passes
to a localization at a prime, and in a Noetherian universally catenary ring satisfying `(S₂)` the
height is additive, `height 𝔮 = height 𝔭 + height(𝔮/𝔭)` for `𝔭 ≤ 𝔮`. Both are public.

## References

* [Stacks Project, Tag 0EHI](https://stacks.math.columbia.edu/tag/0EHI)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW), the lemma the remark
  comments on
* [Stacks Project, Tag 0BJV](https://stacks.math.columbia.edu/tag/0BJV), Faltings' finiteness
  theorem
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR), the cutoff
* [Stacks Project, Tag 0FIW](https://stacks.math.columbia.edu/tag/0FIW), catenary and `(S₂)`
  gives equidimensional
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P), the Serre conditions
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), a dualizing complex
  gives universal catenarity
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY), a dualizing complex
  gives Gorenstein formal fibres
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **Away from `V(f)` the module `A ⧸ fA` vanishes.** Multiplication by `f` kills `A ⧸ fA`, and
`f` becomes invertible in the localization at a prime not containing it. -/
public lemma subsingleton_localizedModule_quotient_span (f : A) (p : Ideal A) [p.IsPrime]
    (hfp : f ∉ p) :
    Subsingleton (LocalizedModule p.primeCompl (A ⧸ Ideal.span {f})) := by
  have hkill : ∀ x : A ⧸ Ideal.span {f}, f • x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.eq_zero_iff_mem (a := f * c)).mpr
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | _ m s =>
    induction b using LocalizedModule.induction_on with
    | _ n t =>
      refine LocalizedModule.mk_eq.mpr ⟨⟨f, hfp⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rw [smul_comm, hkill, smul_zero, smul_comm, hkill, smul_zero]

/-- **The depth of `(A/f)_𝔭` is infinite off `V(f)`.** -/
public lemma depth_localizedModule_quotient_span_eq_top (f : A) (p : Ideal A) [p.IsPrime]
    (hfp : f ∉ p) :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl (A ⧸ Ideal.span {f})) = ⊤ :=
  have := subsingleton_localizedModule_quotient_span f p hfp
  Module.depth_eq_top_of_subsingleton _

/-- `(A/fA)_𝔭` is the quotient `A_𝔭 ⧸ fA_𝔭`, linearly over `A_𝔭`.

The identification itself is `Stacks.Flatness.localizedModuleQuotientSpanEquiv`, which is
`A`-linear and writes the ideal of the localization as generated by the image of `f`; here it is
read over `A_𝔭` and with the ideal written as the pushforward `fA_𝔭`, the spelling
`isLocalization_atPrime_quotient` and `Module.depth` want. -/
public noncomputable def localizedModuleQuotientSpanEquiv (f : A) (p : Ideal A) [p.IsPrime] :
    LocalizedModule p.primeCompl (A ⧸ Ideal.span {f}) ≃ₗ[Localization.AtPrime p]
      (Localization.AtPrime p ⧸
        (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) :=
  have he : Ideal.span {algebraMap A (Localization.AtPrime p) f} =
      (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p)) := by
    rw [Ideal.map_span, Set.image_singleton]
  (((Stacks.Flatness.localizedModuleQuotientSpanEquiv (A := A) (B := A)
        p.primeCompl f).symm.trans
      ((Submodule.quotEquivOfEq _ _ he).restrictScalars A)).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p))

/-- **The depth of `(A/f)_𝔭` is the depth of the local ring of `A/fA` at `𝔭`.** The localization
`(A/fA)_𝔭` is the quotient `A_𝔭 ⧸ fA_𝔭`, which is the local ring of `A/fA` at the image of `𝔭`;
the depth of a module killed by `fA` is the same over `A_𝔭` as over that quotient. -/
@[ega "IV 10.8.2" "(ii), special case"]
public lemma ringDepth_eq_depth_localizedModule_quotient_span (f : A) (p : Ideal A) [p.IsPrime]
    (pb : Ideal (A ⧸ Ideal.span {f})) [pb.IsPrime]
    (hpb : pb.comap (Ideal.Quotient.mk (Ideal.span {f})) = p) :
    ringDepth (Localization.AtPrime pb) =
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl (A ⧸ Ideal.span {f})) := by
  classical
  set Ap := Localization.AtPrime p with hAp
  set J : Ideal Ap := (Ideal.span {f}).map (algebraMap A Ap) with hJdef
  have hlocq : IsLocalization.AtPrime (Ap ⧸ J) pb :=
    isLocalization_atPrime_quotient p Ap (Ideal.span {f}) pb hpb
  have : IsLocalRing (Ap ⧸ J) := IsLocalization.AtPrime.isLocalRing (Ap ⧸ J) pb
  have he : ringDepth (Localization.AtPrime pb) = ringDepth (Ap ⧸ J) :=
    ringDepth_eq_of_ringEquiv
      (IsLocalization.algEquiv pb.primeCompl (Localization.AtPrime pb) (Ap ⧸ J)).toRingEquiv
  rw [he, ringDepth_eq_depth_maximalIdeal,
    ← Module.depth_eq_depth_self_of_surjective_algebraMap
      (A := Ap) (B := Ap ⧸ J) Ideal.Quotient.mk_surjective,
    Module.depth_eq_depth_of_linearEquiv (maximalIdeal Ap)
      (localizedModuleQuotientSpanEquiv f p)]

/-! ### Additivity of the height in a catenary ring satisfying `(S₂)` -/

/-- **Serre's condition `(Sₖ)` passes to a localization at a prime.** A localization of `R_𝔮` at
a prime is a localization of `R` itself, so the dimension-against-depth inequality at a prime of
`R_𝔮` is the one at its contraction to `R`. -/
public lemma propertySkRing_localizationAtPrime (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : Ideal R) [q.IsPrime] (k : ℕ) (h : PropertySkRing R k) :
    PropertySkRing (Localization.AtPrime q) k := by
  intro P hP
  have : P.IsPrime := hP
  have : (P.comap (algebraMap R (Localization.AtPrime q))).IsPrime := Ideal.IsPrime.comap _
  have hq := h (P.comap (algebraMap R (Localization.AtPrime q)))
  have e : Localization.AtPrime (P.comap (algebraMap R (Localization.AtPrime q))) ≃+*
      Localization.AtPrime P :=
    (IsLocalization.algEquiv (P.comap (algebraMap R (Localization.AtPrime q))).primeCompl
      (Localization.AtPrime (P.comap (algebraMap R (Localization.AtPrime q))))
      (Localization.AtPrime P)).toRingEquiv
  rwa [e.ringKrullDim, ringDepth_eq_of_ringEquiv e] at hq

/-- **The height is additive in a Noetherian universally catenary ring satisfying `(S₂)`:**
`height 𝔮 = height 𝔭 + dim((R/𝔭)_𝔮)` for primes `𝔭 ≤ 𝔮`.

Catenarity and `(S₂)` both pass to the local ring `R_𝔮`, whose dimension is `height 𝔮` and in
which they make the dimension split at the prime `𝔭R_𝔮` as its height plus the dimension of the
quotient. That height is `height 𝔭`, and the quotient `R_𝔮 ⧸ 𝔭R_𝔮` is the local ring of `R/𝔭`
at `𝔮/𝔭`, of dimension the height of `𝔮/𝔭`. -/
public lemma height_eq_height_add_height_map_quotientMk (R : Type u) [CommRing R]
    [IsNoetherianRing R] (hcat : Ring.IsUniversallyCatenary R) (hS₂ : PropertySkRing R 2)
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  classical
  set S := Localization.AtPrime q with hS
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  have hP : (p.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl S p inferInstance hdisj
  have hqp := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have : IsLocalization.AtPrime (S ⧸ p.map (algebraMap R S)) (q.map (Ideal.Quotient.mk p)) :=
    isLocalization_atPrime_quotient q S p (q.map (Ideal.Quotient.mk p))
      (Ideal.comap_map_mk hpq)
  have hcatS : Ring.IsCatenary S :=
    Ring.IsUniversallyCatenary.isCatenary_of_finiteType
      (Ring.IsUniversallyCatenary.localization q.primeCompl S hcat) S
  have hS₂S : PropertySkRing S 2 := propertySkRing_localizationAtPrime R q 2 hS₂
  have hsplit := Stacks.Serre.LocalizationDepth.ringKrullDim_eq_height_add_ringKrullDim_quotient
    S hcatS hS₂S (p.map (algebraMap R S))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q S,
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.map (Ideal.Quotient.mk p))
      (S ⧸ p.map (algebraMap R S)),
    IsLocalization.height_map_of_disjoint q.primeCompl p hdisj] at hsplit
  exact_mod_cast hsplit

/-! ### Rings with a dualizing complex -/

/-- **A Noetherian ring with a dualizing complex is universally catenary and its local rings have
Cohen--Macaulay formal fibres.** Universal catenarity is Stacks 0A80. For the formal fibres, a
localization of `A` at a prime again has a dualizing complex (Stacks 0A7G), so its formal fibres
are Gorenstein by Stacks 0AWY, and a Gorenstein ring is Cohen--Macaulay. -/
public lemma isUniversallyCatenary_and_formalFibresAreCohenMacaulay_of_isDualizingComplex
    (R : Type u) [CommRing R] [IsNoetherianRing R] {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : Dualizing.IsDualizingComplex K) :
    Ring.IsUniversallyCatenary R ∧
      ∀ p : PrimeSpectrum R,
        FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal) := by
  refine ⟨Dualizing.isUniversallyCatenary_of_isDualizingComplex hK, fun p q hq => ?_⟩
  have : q.IsPrime := hq
  obtain ⟨hN, hG⟩ := Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex
    (Localization.AtPrime p.asIdeal) _
    (Dualizing.isDualizingComplex_localizationAtPrime.{u, u} K hK p) q
  exact ⟨hN, @Dualizing.IsGorensteinRing.isCohenMacaulayRing _ _ hN hG⟩

/-! ### The cutoff of `A/fA` along `𝔞` -/

/-- **The source's inequality is `2 < s_{A,𝔞}(A/fA)`.** The cutoff of Tag 0BJR for the module
`A/fA` is an infimum over pairs of primes `𝔭 ⊆ 𝔮` with `𝔭 ∉ V(𝔞)` and `𝔮 ∈ V(𝔞)`; the pairs with
`𝔭 ∉ V(f)` contribute nothing, because `(A/fA)_𝔭` then vanishes and has infinite depth. So the
cutoff exceeds `2` exactly when `depth((A/f)_𝔭) + dim((A/𝔭)_𝔮) > 2` for all `𝔭 ∈ V(f) \ V(𝔞)`
and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`. -/
public lemma two_lt_localCohomologyCutoff_iff (a : Ideal A) (f : A) :
    (2 : ℕ∞) < localCohomologyCutoff A a (A ⧸ Ideal.span {f}) ↔
      ∀ p q : PrimeSpectrum A, f ∈ p.asIdeal → ¬ a ≤ p.asIdeal → a ≤ q.asIdeal →
        p.asIdeal ≤ q.asIdeal →
          2 < Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl (A ⧸ Ideal.span {f})) +
              (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have hlt : ∀ x : ℕ∞, (2 : ℕ∞) < x ↔ (3 : ℕ∞) ≤ x := by
    intro x
    rw [← ENat.add_one_le_iff (by simp)]
    norm_num
  rw [hlt, le_localCohomologyCutoff_iff]
  refine ⟨fun h p q _ hp hq hpq => (hlt _).mpr (h p q hp hq hpq), fun h p q hp hq hpq => ?_⟩
  by_cases hf : f ∈ p.asIdeal
  · exact (hlt _).mp (h p q hf hp hq hpq)
  · rw [depth_localizedModule_quotient_span_eq_top f p.asIdeal hf, top_add]
    exact le_top

/-- **The finiteness of `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` is `2 < s_{A,𝔞}(A/fA)`.** This is the
cutoff criterion of Tag 0BJV at `n = 2`: a universally catenary Noetherian ring whose local
rings have Cohen--Macaulay formal fibres has those fibres `(S₂)`, and then `H^i_Z(M)` is finite
for every `i ≤ n` exactly when the cutoff exceeds `n`. -/
public lemma finite_localCohomology_one_and_two_iff_two_lt_localCohomologyCutoff
    [IsNoetherianRing A] (a : Ideal A) (f : A) (hcat : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal)) :
    (Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1) ∧
      Module.Finite A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2)) ↔
      (2 : ℕ∞) < localCohomologyCutoff A a (A ⧸ Ideal.span {f}) := by
  have hSk : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) 2 := by
    intro p r hr
    have : r.IsPrime := hr
    obtain ⟨hF, hCM⟩ := hformal p r
    exact ⟨hF, @propertySkRing_of_isCohenMacaulayRing _ _ hF hCM 2⟩
  have hmain := lt_localCohomologyCutoff_iff_forall_finite_succ A a (A ⧸ Ideal.span {f}) hcat 2 hSk
  simp only [Nat.cast_ofNat] at hmain
  rw [hmain]
  refine ⟨fun ⟨h₁, h₂⟩ n hn => ?_, fun h =>
    ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩⟩
  interval_cases n
  · simpa using h₁
  · simpa using h₂

/-! ### The sufficient condition: `(S₂)` and codimension at least three -/

/-- **`(S₂)` for `A/fA` and codimension `≥ 3` for the components of `V(𝔞)` give the source's
inequality.** Let `𝔭 ∈ V(f) \ V(𝔞)` and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`. The prime `𝔮` contains a minimal
prime of `𝔞`, whose image in `A/fA` has height at least `3`, so the image `𝔮̄` of `𝔮` has height
at least `3` too. In the universally catenary ring `A/fA`, Serre's condition splits that height
as `height 𝔭̄ + dim((A/𝔭)_𝔮)`, so `height 𝔭̄ + dim((A/𝔭)_𝔮) ≥ 3`; and `(S₂)` at `𝔭̄` bounds
`depth((A/f)_𝔭)` below by `min(2, height 𝔭̄)`. Since `dim((A/𝔭)_𝔮) ≥ 1`, the two bounds add up
to more than `2`. -/
public lemma two_lt_depth_add_height_of_propertySkRing_of_three_le_height
    [IsNoetherianRing A] (a : Ideal A) (f : A)
    (hcat : Ring.IsUniversallyCatenary A)
    (hS₂ : PropertySkRing (A ⧸ Ideal.span {f}) 2)
    (hcodim : ∀ z ∈ a.minimalPrimes, 3 ≤ (z.map (Ideal.Quotient.mk (Ideal.span {f}))).height)
    (p q : PrimeSpectrum A) (hfp : f ∈ p.asIdeal) (hp : ¬ a ≤ p.asIdeal)
    (hq : a ≤ q.asIdeal) (hpq : p.asIdeal ≤ q.asIdeal) :
    2 < Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl (A ⧸ Ideal.span {f})) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  classical
  have hfple : Ideal.span {f} ≤ p.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp)
  have hpb := Ideal.isPrime_map_quotientMk_of_isPrime hfple
  have hqb := Ideal.isPrime_map_quotientMk_of_isPrime (hfple.trans hpq)
  -- `(A/fA) ⧸ 𝔭̄` is `A ⧸ 𝔭`, so the two readings of `dim((A/𝔭)_𝔮)` agree.
  have hcomp : (((DoubleQuot.quotQuotEquivQuotOfLE hfple) :
        ((A ⧸ Ideal.span {f}) ⧸ p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))) →+*
          A ⧸ p.asIdeal).comp
      (Ideal.Quotient.mk (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))))).comp
        (Ideal.Quotient.mk (Ideal.span {f})) = Ideal.Quotient.mk p.asIdeal := by
    ext x
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hfple
  have hmapeq : Ideal.map ((DoubleQuot.quotQuotEquivQuotOfLE hfple) :
        ((A ⧸ Ideal.span {f}) ⧸ p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))) →+*
          A ⧸ p.asIdeal)
      ((q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))).map
        (Ideal.Quotient.mk (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))))) =
      q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  have hheight : ((q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))).map
        (Ideal.Quotient.mk (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))))).height =
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    rw [← RingEquiv.height_map (DoubleQuot.quotQuotEquivQuotOfLE hfple)
      ((q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))).map
        (Ideal.Quotient.mk (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))))]
    exact congrArg Ideal.height hmapeq
  -- the height of `𝔮̄` is at least three
  obtain ⟨z, hz, hzq⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := q.asIdeal) hq
  have h3q : (3 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))).height :=
    (hcodim z hz).trans (Ideal.height_mono (Ideal.map_mono hzq))
  rw [height_eq_height_add_height_map_quotientMk (A ⧸ Ideal.span {f})
      (Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hcat) hS₂
      (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))
      (q.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))) (Ideal.map_mono hpq),
    hheight] at h3q
  -- `dim((A/𝔭)_𝔮) ≥ 1`
  have hne : p.asIdeal ≠ q.asIdeal := fun h => hp (h ▸ hq)
  have : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  have hd1 : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    refine Order.one_le_iff_ne_zero.mpr fun h0 => ?_
    have hbot := Ideal.height_eq_zero_iff_eq_bot.mp h0
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot
    exact hne (le_antisymm hpq hbot)
  -- Serre's condition at `𝔭̄`
  have hS := hS₂ (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))
      (Localization.AtPrime (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))),
    ringDepth_eq_depth_localizedModule_quotient_span f p.asIdeal
      (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f})))
      (Ideal.comap_map_mk hfple)] at hS
  simp only [WithBot.unbotD_coe, Nat.cast_ofNat] at hS
  refine lt_of_lt_of_le ?_ (add_le_add hS (le_refl _))
  rcases le_total (2 : ℕ∞) (p.asIdeal.map (Ideal.Quotient.mk (Ideal.span {f}))).height with h2 | h2
  · rw [min_eq_left h2]
    calc (2 : ℕ∞) < 2 + 1 := by norm_num
      _ ≤ 2 + (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
          add_le_add (le_refl (2 : ℕ∞)) hd1
  · rw [min_eq_right h2]
    exact lt_of_lt_of_le (by norm_num) h3q

/-! ### Stacks 0EHI -/

/-- **Stacks Project, Tag 0EHI.** In Situation 0EHC, let `I = (f)` be principal for a
nonzerodivisor `f ∈ 𝔞`, as in Tag 0DXW. The remark has three assertions, conjoined here into one
statement because they are one remark; the first is quantified over the dualizing complexes of
`A`, and the other two carry the remark's own hypotheses as antecedents, exactly as the source
states them.

* The parenthetical: if `A` has a dualizing complex, then `A` is universally catenary and the
  formal fibres of its local rings are Cohen--Macaulay. (Tags 0A80, 0A7G, 0AWY.)

* The equivalence: if `A` is universally catenary with Cohen--Macaulay formal fibres, then
  `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules if and only if

    `depth((A/f)_𝔭) + dim((A/𝔭)_𝔮) > 2`

  for all `𝔭 ∈ V(f) \ V(𝔞)` and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`. This is the Local Cohomology Theorem 0BJV at
  the cutoff `s_{A,𝔞}(A/fA)` of Tag 0BJR: the displayed inequality says exactly that the cutoff
  exceeds `2`, the pairs with `𝔭 ∉ V(f)` contributing nothing because `(A/fA)_𝔭` vanishes there.

* The example: if moreover `A/fA` satisfies Serre's condition `(S₂)` and every irreducible
  component of `Z = V(𝔞)` has codimension at least `3` in `Y = Spec(A/fA)`, then `H¹_𝔞(A/fA)`
  and `H²_𝔞(A/fA)` are finite.

The two cohomology modules are the local cohomology of `A/fA` with support in `V(𝔞)`, in the
spelling Tag 0BJV uses. `depth((A/f)_𝔭)` and `dim((A/𝔭)_𝔮)` are spelled as in the cutoff of Tag
0BJR, namely as `Module.depth` of `(A/fA)_𝔭` over `A_𝔭` and as the height of the image of `𝔮` in
`A/𝔭`. The irreducible components of `Z` are the minimal primes of `𝔞`, and the codimension in
`Y` of the component cut out by such a prime `𝔷` is the height of the image of `𝔷` in
`A/fA`.

The two hypotheses `_hfa : f ∈ 𝔞` and `_hf : f ∈ nonZeroDivisors A` are the situation the source
places the remark in — Tag 0DXW's `I = (f)` principal, generated by a nonzerodivisor of `𝔞`. They
are recorded so the statement has the source's scope and no more; the argument itself never uses
them, which is why they are underscored. -/
@[stacks 0EHI]
public theorem finite_localCohomology_quotient_span_iff_two_lt_depth_add_height
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A) (_hfa : f ∈ a)
    (_hf : f ∈ nonZeroDivisors A) :
    (∀ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K →
        Ring.IsUniversallyCatenary A ∧
          ∀ p : PrimeSpectrum A,
            FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal)) ∧
      (Ring.IsUniversallyCatenary A →
        (∀ p : PrimeSpectrum A,
            FormalFibersAreCohenMacaulay (Localization.AtPrime p.asIdeal)) →
        ((Module.Finite A
              (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1) ∧
            Module.Finite A
              (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2) ↔
            ∀ p q : PrimeSpectrum A, f ∈ p.asIdeal → ¬ a ≤ p.asIdeal → a ≤ q.asIdeal →
              p.asIdeal ≤ q.asIdeal →
                2 < Module.depth (Localization.AtPrime p.asIdeal)
                      (maximalIdeal (Localization.AtPrime p.asIdeal))
                      (LocalizedModule p.asIdeal.primeCompl (A ⧸ Ideal.span {f})) +
                    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height) ∧
          (PropertySkRing (A ⧸ Ideal.span {f}) 2 →
            (∀ z ∈ a.minimalPrimes,
              3 ≤ (z.map (Ideal.Quotient.mk (Ideal.span {f}))).height) →
            Module.Finite A
                (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A (A ⧸ Ideal.span {f}))) 1) ∧
              Module.Finite A
                (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A))
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A (A ⧸ Ideal.span {f}))) 2)))) := by
  refine ⟨fun K hK =>
      isUniversallyCatenary_and_formalFibresAreCohenMacaulay_of_isDualizingComplex A hK,
    fun hcat hformal => ⟨?_, fun hS₂ hcodim => ?_⟩⟩
  · rw [finite_localCohomology_one_and_two_iff_two_lt_localCohomologyCutoff a f hcat hformal]
    exact two_lt_localCohomologyCutoff_iff a f
  · rw [finite_localCohomology_one_and_two_iff_two_lt_localCohomologyCutoff a f hcat hformal,
      two_lt_localCohomologyCutoff_iff a f]
    exact two_lt_depth_add_height_of_propertySkRing_of_three_le_height a f hcat hS₂ hcodim

end Stacks.LocalCohomology

end
