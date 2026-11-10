module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.AffineDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageValuativeDiagram
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Specialization
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced

/-!
# Codimension-one points of a relative normalization

Let `f : Y ⟶ X` be a morphism of finite type with `Y` reduced and `X` Nagata, and let `X'` be the
normalization of `X` in `Y`. If a point `x'` of `X'` has a one-dimensional local ring and the
fibre of `Y ⟶ X'` over `x'` is empty, then that local ring is a discrete valuation ring.

## Main results

* `AlgebraicGeometry.isDiscreteValuationRing_stalk_normalization_of_isEmpty_fiber` is Tag 0BXB.

## Implementation notes

Finite type is expressed by `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.QuasiCompact`. A Nagata scheme is locally Noetherian, which is what makes the
morphism quasi-separated and so lets Mathlib's relative normalization be formed; since
`IsNagataScheme` is not a class, that instance is introduced in the statement itself. The
conclusion packages the `IsDomain` instance existentially because `IsDiscreteValuationRing` takes
one as input.

The source's proof reduces to the affine case twice over, first by Tag 03GR and then by Tag 0BXA.
Here no reduction is performed on the schemes; the argument is run at the point `x'` instead, in
the following shape.

The local ring `R = 𝒪_{X', x'}` is the localization of the sections `A = Γ(X', U)` on an affine
chart `U` around `x'` at the prime `p` of `x'`, and `p` has height one, so it is not a minimal
prime. Prime avoidance produces `a ∈ p` lying in no minimal prime of `A`. The closed subscheme
`V(a)` of the chart has empty preimage in `Y` near `x'`: a point of that preimage would make `x'`
lie in the closure of the image of `Y ×_{X'} V(a) ⟶ X'`, and by Tag 02JQ that closure consists of
specializations of images of points of the source; but the only proper generalizations of `x'` are
generic points of irreducible components, because the local ring at `x'` has dimension one, and
those correspond to minimal primes of `A`, which `a` avoids, while `x'` itself is excluded by the
fibre being empty. So after shrinking the chart to an affine open `U'` on which this preimage is
empty, `a` restricts to an invertible function on `g ⁻¹ᵁ U'`, where `g = f.toNormalization`.

Writing `A' = Γ(X', U')` and `B = Γ(Y, g ⁻¹ᵁ U')`, Tag 0BXA says that `A'` is its own integral
closure in `B`, that is, `A'` is integrally closed in `B` in the sense of Mathlib's
`IsIntegrallyClosedIn`. Localizing preserves this: `R` is integrally closed in the localization
`S` of `B` at the image of the complement of `p'`, by clearing denominators. The image of `a` in
`R` lies in the maximal ideal and is a unit in `S`, and so therefore is the parameter `h`
furnished by Tag 0C3R, the maximal ideal being the radical of `(h)`.

That is the input to the ring-theoretic half: a reduced Noetherian local ring `R` of dimension one
which is integrally closed in an algebra `S` where a parameter `h` becomes invertible. Tag 0C3R
identifies `R[1/h]` with the product of the residue fields at the minimal primes of `R`, and since
`R` is integrally closed in `S` every idempotent of `R[1/h]` comes from `R`, hence is `0` or `1`
as `R` is local. A product of fields with no nontrivial idempotent has one factor, so `R` has a
single minimal prime, which is `⊥` because `R` is reduced: `R` is a domain. Tag 0C3R then
identifies `R[1/h]` with the fraction field of `R`, and integral closedness in `S` transports
along `R[1/h] ↪ S` and across that identification, so `R` is a normal domain. The
Noetherian-local-normal-dimension-one characterization of a discrete valuation ring is item (5)
of `isDiscreteValuationRing_tfae` (Tag 00PD).

## References

* [Stacks Project, Tag 0BXB](https://stacks.math.columbia.edu/tag/0BXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

/-! ### Integral closedness in a localization away from one element -/

/-- If `R` is integrally closed in `S` and `h : R` becomes a unit in `S`, then `R` is integrally
closed in the localization of `R` away from `h`, because that localization maps injectively into
`S` over `R`. -/
private theorem isIntegrallyClosedIn_localizationAway {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : R) (hh : IsUnit (algebraMap R S h)) [IsIntegrallyClosedIn R S] :
    IsIntegrallyClosedIn R (Localization.Away h) := by
  have hinj : Function.Injective (algebraMap R S) :=
    IsIntegralClosure.algebraMap_injective R R S
  have : IsLocalization.Away (algebraMap R S h) S :=
    IsLocalization.away_of_isUnit_of_bijective S hh Function.bijective_id
  let g : Localization.Away h →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom (R := R) (S := Localization.Away h) (P := S) (A := R)
      (f := Algebra.ofId R S) h hh
  have hg : Function.Injective (g : Localization.Away h → S) := by
    change Function.Injective
      (IsLocalization.Away.map (Localization.Away h) S (algebraMap R S) h)
    rw [IsLocalization.Away.map_injective_iff]
    intro a ha
    obtain rfl : a = 0 := hinj (by simpa using ha)
    exact ⟨0, by simp⟩
  exact g.isIntegrallyClosedIn hg inferInstance

/-- If `R` is integrally closed in `S`, if `h : R` becomes a unit in `S`, and if the localization
of `R` away from `h` is a ring of fractions of `R`, then `R` is integrally closed. -/
private theorem isIntegrallyClosed_of_localizationAway_equiv {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (h : R) (hh : IsUnit (algebraMap R S h))
    [IsIntegrallyClosedIn R S] (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (e : Localization.Away h ≃ₐ[R] K) : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr
    (e.isIntegrallyClosedIn.mp (isIntegrallyClosedIn_localizationAway h hh))

/-- A reduced Noetherian local ring of Krull dimension one which is integrally closed in an
algebra where some element of its maximal ideal lying in no minimal prime becomes invertible is a
normal domain.

By Tag 0C3R that element exhibits the localization away from it as the product of the residue
fields at the minimal primes; integral closedness forces that product to have no nontrivial
idempotent, hence a single factor, and the ring being reduced its unique minimal prime is `⊥`. -/
private theorem isDomain_and_isIntegrallyClosed_of_isUnit_of_notMem_minimalPrimes
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosedIn R S]
    (hdim : ringKrullDim R = 1) {h : R} (hh : h ∈ IsLocalRing.maximalIdeal R)
    (hav : ∀ p ∈ minimalPrimes R, h ∉ p) (hhu : IsUnit (algebraMap R S h)) :
    ∃ _ : IsDomain R, IsIntegrallyClosed R := by
  classical
  have hclosed : IsIntegrallyClosedIn R (Localization.Away h) :=
    isIntegrallyClosedIn_localizationAway h hhu
  have hinj : Function.Injective (algebraMap R (Localization.Away h)) :=
    IsIntegralClosure.algebraMap_injective R R (Localization.Away h)
  have hIdemR : ∀ r : R, r * r = r → r = 0 ∨ r = 1 := by
    intro r hr
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hu | hu
    · refine Or.inr (hu.mul_right_inj.mp ?_)
      rw [hr, mul_one]
    · refine Or.inl (hu.mul_right_inj.mp ?_)
      rw [mul_zero, sub_mul, one_mul, hr, sub_self]
  -- An idempotent of `R[1/h]` is integral over `R`, hence comes from `R`, hence is `0` or `1`.
  have hNoIdem : ∀ x : Localization.Away h, x * x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have hint : IsIntegral R x :=
      ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by norm_num), by
        simpa [pow_two, sub_eq_zero] using hx⟩
    obtain ⟨r, hr⟩ := hclosed.isIntegral_iff.mp hint
    have hrr : r * r = r := hinj (by rw [map_mul, hr, hx])
    rcases hIdemR r hrr with h0 | h1
    · exact Or.inl (by rw [← hr, h0, map_zero])
    · exact Or.inr (by rw [← hr, h1, map_one])
  -- `R[1/h]` is the product of the residue fields at the minimal primes of `R`.
  obtain ⟨e⟩ :=
    (IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_pi_residueField_of_isReduced
      hdim hh).mp hav
  have hsub : Subsingleton (minimalPrimes R) := by
    refine ⟨fun p q => ?_⟩
    by_contra hpq
    let a : ∀ j : minimalPrimes R, @Ideal.ResidueField R _ j.1 j.2.1.1 :=
      fun j => if j = p then 1 else 0
    have hidem : e.symm a * e.symm a = e.symm a := by
      apply e.injective
      funext j
      by_cases hj : j = p <;> simp [a, hj]
    rcases hNoIdem _ hidem with h0 | h1
    · have ha0 : a = 0 := by simpa using congrArg e h0
      have : (1 : @Ideal.ResidueField R _ p.1 p.2.1.1) = 0 := by
        simpa [a] using congrFun ha0 p
      exact one_ne_zero this
    · have ha1 : a = 1 := by simpa using congrArg e h1
      have : (0 : @Ideal.ResidueField R _ q.1 q.2.1.1) = 1 := by
        simpa [a, Ne.symm hpq] using congrFun ha1 q
      exact one_ne_zero this.symm
  -- A single minimal prime, which is `⊥` since `R` is reduced, so `R` is a domain.
  obtain ⟨⟨p₀, hp₀⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
  have hp₀' : p₀ ∈ minimalPrimes R := hp₀
  have hmins : minimalPrimes R = {p₀} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp₀', fun t ht =>
      congrArg Subtype.val (hsub.elim (⟨t, ht⟩ : minimalPrimes R) ⟨p₀, hp₀'⟩)⟩
  have hbot : (⊥ : Ideal R) = p₀ := by
    rw [← sInf_minimalPrimes_eq_bot R, hmins, sInf_singleton]
  have : (⊥ : Ideal R).IsPrime := hbot ▸ hp₀'.1.1
  have : IsDomain R := IsDomain.of_bot_isPrime R
  -- `R` has depth one, so `R[1/h]` is its fraction field.
  obtain ⟨e'⟩ :=
    (IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_fractionRing_of_depth_eq_one
      hdim (IsLocalRing.depth_eq_one_of_isReduced hdim) hh).mp hav
  exact ⟨inferInstance, isIntegrallyClosed_of_localizationAway_equiv h hhu (FractionRing R) e'⟩

/-! ### Prime avoidance away from the minimal primes -/

/-- In a Noetherian ring a prime that is not minimal contains an element lying in no minimal
prime: no minimal prime contains it, there are only finitely many of them, and prime avoidance
applies. This is Tag 00DS together with Tag 00FR. -/
private theorem Ideal.exists_mem_forall_notMem_minimalPrimes {A : Type u} [CommRing A]
    [IsNoetherianRing A] (p : Ideal A) [hp : p.IsPrime] (hmin : p ∉ minimalPrimes A) :
    ∃ a ∈ p, ∀ q ∈ minimalPrimes A, a ∉ q := by
  have hnotle : ∀ q ∈ minimalPrimes A, ¬ p ≤ q := fun q hq hpq =>
    hmin (le_antisymm hpq (hq.2 ⟨hp, bot_le⟩ hpq) ▸ hq)
  have hnotSub : ¬ (p : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := by
    intro hsub
    obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing A) (a := p) (b := ⊤)
      (f := fun q : Ideal A => q) (fun q hq _ _ => hq.1.1) (I := p)).mp hsub
    exact hnotle q hq hpq
  obtain ⟨a, ha, ha'⟩ := Set.not_subset.mp hnotSub
  exact ⟨a, ha, fun t ht hat => ha' (Set.mem_biUnion ht hat)⟩

namespace AlgebraicGeometry

/-! ### Generalizations of a point of codimension one -/

/-- On a locally Noetherian scheme a proper generalization of a point whose local ring has Krull
dimension one is the generic point of an irreducible component: coheight drops strictly along a
nontrivial specialization, and coheight is the Krull dimension of the local ring. -/
private lemma mem_genericPoints_of_specializes_of_ringKrullDim_stalk_eq_one {T : Scheme.{u}}
    [IsLocallyNoetherian T] {x y : T} (hdim : ringKrullDim (T.presheaf.stalk x) = 1)
    (hyx : y ⤳ x) (hne : y ≠ x) : y ∈ genericPoints T := by
  have hx : Order.coheight x = 1 := by
    have h : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = 1 := by
      rw [← ringKrullDim_stalk_eq_coheight x]
      exact hdim
    exact_mod_cast h
  have hy : Order.coheight y = 0 :=
    Order.lt_one_iff.mp (hx ▸ coheight_lt_coheight_of_specializes T hyx hne)
  exact (mem_genericPoints_iff_isMax T y).mpr (Order.coheight_eq_zero.mp hy)

/-! ### The local ring at a codimension-one point of the relative normalization -/

/-- **Stacks Project, Tag 0BXB.** Let `f : Y ⟶ X` be of finite type with `Y` reduced and `X`
Nagata, and let `X'` be the normalization of `X` in `Y`. If the local ring of `X'` at a point `x'`
has Krull dimension one and the fibre of `Y ⟶ X'` over `x'` is empty, then that local ring is a
discrete valuation ring. -/
@[stacks 0BXB]
theorem isDiscreteValuationRing_stalk_normalization_of_isEmpty_fiber {X Y : Scheme.{u}}
    (f : Y ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced Y] (hX : IsNagataScheme X) :
    haveI : IsLocallyNoetherian X :=
      ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp hX).1
    ∀ x' : f.normalization,
      ringKrullDim (f.normalization.presheaf.stalk x') = 1 →
      IsEmpty (f.toNormalization.fiber x') →
      ∃ _ : IsDomain (f.normalization.presheaf.stalk x'),
        IsDiscreteValuationRing (f.normalization.presheaf.stalk x') := by
  have : IsLocallyNoetherian X :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp hX).1
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_of_locallyOfFiniteType f hX
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  intro x' hdim hempty
  -- An affine chart `U` around `x'`, its sections `A`, the prime `p` of `x'` and the stalk `R`.
  let U : f.normalization.affineOpens :=
    ⟨(f.normalization.affineCover.f (f.normalization.affineCover.idx x')).opensRange,
      isAffineOpen_opensRange (f.normalization.affineCover.f
        (f.normalization.affineCover.idx x'))⟩
  let xU : U.1 := ⟨x', f.normalization.affineCover.covers x'⟩
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let R := f.normalization.presheaf.stalk x'
  let A := Γ(f.normalization, U.1)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  let p := (U.2.primeIdealOf xU).asIdeal
  have : (U.2.primeIdealOf xU).asIdeal.IsPrime := (U.2.primeIdealOf xU).isPrime
  let _ : Algebra A R := TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf xU
  have : IsLocalization.AtPrime R p := U.2.isLocalization_stalk xU
  have hpheight : p.height = 1 := by
    have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height p R
    rw [hdim] at hloc
    exact_mod_cast hloc.symm
  have hpnot : p ∉ minimalPrimes A := fun hpmin => by
    rw [Ideal.height_eq_zero_iff.mpr hpmin] at hpheight
    norm_num at hpheight
  obtain ⟨a, ha, hav⟩ := Ideal.exists_mem_forall_notMem_minimalPrimes p hpnot
  -- The closed subscheme `V(a)` of the chart and the part of `Y` lying over it.
  let I : Ideal A := Ideal.span {a}
  let jA : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j : Spec (.of (A ⧸ I)) ⟶ f.normalization := jA ≫ U.2.fromSpec
  let g : Y ⟶ f.normalization := f.toNormalization
  let q : pullback g j ⟶ f.normalization := pullback.snd g j ≫ j
  have : QuasiCompact q := by infer_instance
  -- `x'` is not in the closure of the image of that part.
  have hxnotcl : x' ∉ closure (Set.range q) := by
    intro hxcl
    have hxrange : x' ∈ Set.range q.imageι := by
      change x' ∈ Set.range q.ker.subschemeι
      rw [Scheme.IdealSheafData.range_subschemeι]
      simpa [q.support_ker] using hxcl
    obtain ⟨z, hz⟩ := hxrange
    obtain ⟨w, hw⟩ := exists_specializes_of_image_point q z
    have htarget : g (pullback.fst g j w) = q w := by
      change (pullback.fst g j ≫ g) w = (pullback.snd g j ≫ j) w
      rw [pullback.condition]
    let y : f.normalization := g (pullback.fst g j w)
    have hyx : y ⤳ x' := by
      simpa [y, htarget] using hz ▸ hw
    by_cases hy : y = x'
    · exact hempty.false ((g.fiberHomeo x').symm ⟨pullback.fst g j w, by simp [hy, y]⟩)
    · -- a proper generalization of `x'` is a generic point, whose prime is minimal, so avoids `a`
      have hgen : y ∈ genericPoints f.normalization :=
        mem_genericPoints_of_specializes_of_ringKrullDim_stalk_eq_one hdim hyx hy
      have hyU : y ∈ U.1 := hyx.mem_open U.1.2 xU.2
      let yU : U.1 := ⟨y, hyU⟩
      let ySpec : PrimeSpectrum A := U.2.primeIdealOf yU
      let zSpec : PrimeSpectrum A := jA (pullback.snd g j w)
      have hfromq : U.2.fromSpec zSpec = y := by
        change (jA ≫ U.2.fromSpec) (pullback.snd g j w) = y
        exact htarget.symm
      have hzspec : zSpec = ySpec :=
        U.2.fromSpec.isOpenEmbedding.injective
          (hfromq.trans (U.2.fromSpec_primeIdealOf yU).symm)
      have hza : a ∈ zSpec.asIdeal := by
        change a ∈ Ideal.comap (Ideal.Quotient.mk I) (pullback.snd g j w).asIdeal
        rw [Ideal.mem_comap]
        have haI : Ideal.Quotient.mk I a = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        rw [haI]
        exact Ideal.zero_mem _
      exact hav ySpec.asIdeal
        (Stacks.AlgebraicGeometry.GenericPointGluing.primeIdealOf_mem_minimalPrimes U.2
          ⟨⟨y, hgen⟩, hyU⟩) (hzspec ▸ hza)
  -- Shrink the chart to an affine open `U'` around `x'` missing that closure.
  let W : f.normalization.Opens := ⟨(closure (Set.range q))ᶜ, isClosed_closure.isOpen_compl⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ :=
    f.normalization.isBasis_affineOpens.exists_subset_of_mem_open
      (show x' ∈ W ⊓ U.1 from ⟨hxnotcl, xU.2⟩) (W ⊓ U.1).2
  let U' : f.normalization.affineOpens := ⟨V, hV⟩
  have hU'W : (U'.1 : Set f.normalization) ≤ W := fun z hz => (hVO hz).1
  have hU'U : (U'.1 : Set f.normalization) ≤ U.1 := fun z hz => (hVO hz).2
  let V' : Y.Opens := g ⁻¹ᵁ U'.1
  have hV'U : V' ≤ g ⁻¹ᵁ U.1 := g.preimage_mono hU'U
  -- On `V'` the function `a` does not vanish, hence is invertible there.
  let b : Γ(Y, V') := (g.appLE U.1 V' hV'U) a
  have hrangeJA : Set.range jA = PrimeSpectrum.zeroLocus {a} := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker, I, PrimeSpectrum.zeroLocus_span]
  have hbasic : V' ≤ g ⁻¹ᵁ f.normalization.basicOpen a := by
    intro z hz
    by_contra hnot
    have hgzU' : g z ∈ U'.1 := hz
    let zU : U.1 := ⟨g z, hU'U hgzU'⟩
    have hzSpec0 : U.2.primeIdealOf zU ∈ PrimeSpectrum.zeroLocus {a} := by
      rw [← U.2.fromSpec_preimage_zeroLocus {a}]
      change U.2.fromSpec (U.2.primeIdealOf zU) ∈ f.normalization.zeroLocus {a}
      rw [U.2.fromSpec_primeIdealOf, Scheme.zeroLocus_singleton]
      exact hnot
    obtain ⟨wSpec, hwSpec⟩ := Set.mem_range.mp (hrangeJA.symm ▸ hzSpec0)
    have hzRange : z ∈ Set.range (pullback.fst g j) := by
      rw [Scheme.Pullback.range_fst]
      refine Set.mem_preimage.mpr ⟨wSpec, ?_⟩
      change U.2.fromSpec (jA wSpec) = g z
      rw [hwSpec]
      exact U.2.fromSpec_primeIdealOf zU
    obtain ⟨w, hw⟩ := hzRange
    have hqw : q w = g z := by
      calc q w = (pullback.snd g j ≫ j) w := rfl
        _ = (pullback.fst g j ≫ g) w := by rw [← pullback.condition]
        _ = g z := congrArg g hw
    exact (by simpa [W] using hU'W (hqw ▸ hgzU' : q w ∈ U'.1) :
      q w ∉ closure (Set.range q)) (subset_closure ⟨w, rfl⟩)
  have hbunit : IsUnit b := by
    apply RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace V' b
    intro z hz
    refine (Scheme.mem_basicOpen Y b z hz).mp ?_
    rw [Scheme.basicOpen_appLE g V' U.1 hV'U a]
    exact ⟨hz, hbasic hz⟩
  -- `A'` is integrally closed in `B` by Tag 0BXA.
  let A' := Γ(f.normalization, U'.1)
  let B := Γ(Y, V')
  let _ : Algebra A' B := (g.app U'.1).hom.toAlgebra
  let C := integralClosure A' B
  have : IsIso g.fromNormalization := Scheme.Hom.normalization_fromNormalization_isIso f
  have : IsIso (g.fromNormalization.app U'.1) :=
    Scheme.Hom.isIso_app g.fromNormalization U'.1 (by
      rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hnormComp : IsIso
      (g.fromNormalization.app U'.1 ≫ (g.normalizationObjIso U'.2).hom) := inferInstance
  have hnormMap : IsIso (CommRingCat.ofHom (algebraMap A' C)) := by
    have heq : g.fromNormalization.app U'.1 ≫ (g.normalizationObjIso U'.2).hom =
        CommRingCat.ofHom (algebraMap A' C) := by
      rw [Scheme.Hom.fromNormalization_app g U'.2]
      simp [A', B, C]
    rw [← heq]
    exact hnormComp
  have hbijC : Function.Bijective (algebraMap A' C) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hnormMap
  have hinjAB : Function.Injective (algebraMap A' B) :=
    fun r s hrs => hbijC.1 (Subtype.ext hrs)
  have hclAB : ∀ {x : B}, _root_.IsIntegral A' x → ∃ y, algebraMap A' B y = x := by
    intro x hx
    obtain ⟨r, hr⟩ := hbijC.2 ⟨x, hx⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  have : IsIntegrallyClosedIn A' B := isIntegrallyClosedIn_iff.mpr ⟨hinjAB, hclAB⟩
  let xU' : U'.1 := ⟨x', hxV⟩
  let p' : Ideal A' := (U'.2.primeIdealOf xU').asIdeal
  have : p'.IsPrime := (U'.2.primeIdealOf xU').isPrime
  let _ : Algebra A' R := f.normalization.presheaf.algebra_section_stalk xU'
  have : IsLocalization.AtPrime R p' := U'.2.isLocalization_stalk xU'
  -- The restriction `a'` of `a` to `U'` lies in `p'` and is a unit in `B`.
  let idN : f.normalization ⟶ f.normalization := 𝟙 _
  let ρ : A →+* A' :=
    (idN.appLE U.1 U'.1 (fun z hz => by simpa [idN] using hU'U hz)).hom
  let a' : A' := ρ a
  have hpcomap : p'.comap ρ = p := by
    have hp := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := idN) U.1 U.2 U'.1 U'.2
        (fun z hz => by simpa [idN] using hU'U hz) hxV)
    have hidpoint : idN x' = x' := rfl
    simpa [p', p, ρ, xU, xU', A, hidpoint] using hp
  have ha'mem : a' ∈ p' := by
    change ρ a ∈ p'
    rw [← Ideal.mem_comap, hpcomap]
    exact ha
  have hba' : (g.app U'.1).hom a' = b := by
    rw [Scheme.Hom.app_eq_appLE]
    have hcomp := Scheme.Hom.appLE_comp_appLE g idN U.1 U'.1 V'
      (fun z hz => by simpa [idN] using hU'U hz) le_rfl
    simpa [idN, ρ, b] using congrArg (fun k : A →+* B => k a)
      (congrArg CommRingCat.Hom.hom hcomp)
  have ha'unitB : IsUnit ((g.app U'.1).hom a') := hba' ▸ hbunit
  -- Localize `B` at the image of the complement of `p'`; `R` stays integrally closed in it.
  let M : Submonoid A' := p'.primeCompl
  let S := Localization (Algebra.algebraMapSubmonoid B M)
  have : IsLocalization (Algebra.algebraMapSubmonoid B M) S := Localization.isLocalization
  have : IsLocalization (Submonoid.map (algebraMap A' B) M) S := by
    change IsLocalization (Algebra.algebraMapSubmonoid B M) S
    exact Localization.isLocalization
  have hM : M ≤ Submonoid.comap (algebraMap A' B) (Algebra.algebraMapSubmonoid B M) :=
    fun m hm => Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)
  let ϕ : R →+* S := IsLocalization.map S (algebraMap A' B) hM
  let _ : Algebra R S := Algebra.compHom S ϕ
  have hscalar : algebraMap A' S = (algebraMap R S).comp (algebraMap A' R) := by
    change (algebraMap B S).comp (algebraMap A' B) = ϕ.comp (algebraMap A' R)
    exact (IsLocalization.map_comp (M := M) (S := R) (g := algebraMap A' B)
      (T := Algebra.algebraMapSubmonoid B M) (Q := S) hM).symm
  have : IsScalarTower A' R S := IsScalarTower.of_algebraMap_eq' hscalar
  have ha'unitS : IsUnit (algebraMap R S (algebraMap A' R a')) := by
    rw [← IsScalarTower.algebraMap_apply A' R S]
    change IsUnit (algebraMap B S ((g.app U'.1).hom a'))
    exact ha'unitB.map (algebraMap B S)
  have hinjRS : Function.Injective (algebraMap R S) := by
    change Function.Injective ϕ
    exact IsLocalization.map_injective_of_injective
      (M := M) (S := R) (g := algebraMap A' B) (Q := S) hinjAB
  have hclRS : ∀ {x : S}, _root_.IsIntegral R x → ∃ y, algebraMap R S y = x := by
    intro x hx
    obtain ⟨m, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := A') M x hx
    obtain ⟨w, hxd⟩ := IsLocalization.surj (M := Algebra.algebraMapSubmonoid B M) (S := S) (m • x)
    obtain ⟨m₀, hm₀, hd⟩ := Submonoid.mem_map.mp w.2.2
    have hdscalar : algebraMap B S (w.2 : B) = algebraMap A' S m₀ := by
      rw [← hd]
      exact (IsScalarTower.algebraMap_apply A' B S m₀).symm
    have hxd' : algebraMap B S w.1 = (m • x) * algebraMap A' S m₀ := by rw [← hxd, hdscalar]
    have hyint : _root_.IsIntegral A' (algebraMap B S w.1) :=
      hxd' ▸ hmx.mul (isIntegral_algebraMap (x := m₀))
    obtain ⟨m₁, hm₁, hm₁y⟩ :=
      IsLocalization.exists_isIntegral_smul_of_isIntegral_map M hyint
    obtain ⟨c, hc⟩ := hclAB hm₁y
    have hfinal : algebraMap A' S c = algebraMap A' S (m₁ * m * m₀) * x := by
      calc algebraMap A' S c = algebraMap B S (m₁ • w.1) := by
            rw [IsScalarTower.algebraMap_apply A' B S, hc]
        _ = algebraMap A' S m₁ * algebraMap B S w.1 := by
            rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply A' B S m₁]
        _ = algebraMap A' S m₁ * ((m • x) * algebraMap A' S m₀) := by rw [hxd']
        _ = algebraMap A' S (m₁ * m * m₀) * x := by
            simp only [Submonoid.smul_def, Algebra.smul_def, map_mul]
            ac_rfl
    obtain ⟨u, hu⟩ : IsUnit (algebraMap A' R (m₁ * m * m₀)) :=
      IsLocalization.map_units R ⟨_, mul_mem (mul_mem hm₁ m.2) hm₀⟩
    have hmul : algebraMap R S (algebraMap A' R (m₁ * m * m₀)) * x =
        algebraMap R S (algebraMap A' R c) := by
      rw [← IsScalarTower.algebraMap_apply A' R S (m₁ * m * m₀),
        ← IsScalarTower.algebraMap_apply A' R S c]
      exact hfinal.symm
    refine ⟨((u⁻¹ : Rˣ) : R) * algebraMap A' R c, ?_⟩
    calc algebraMap R S (((u⁻¹ : Rˣ) : R) * algebraMap A' R c)
        = algebraMap R S ((u⁻¹ : Rˣ) : R) * algebraMap R S (algebraMap A' R c) := map_mul _ _ _
      _ = algebraMap R S ((u⁻¹ : Rˣ) : R) *
            (algebraMap R S (algebraMap A' R (m₁ * m * m₀)) * x) := by rw [← hmul]
      _ = algebraMap R S ((u⁻¹ : Rˣ) : R) * algebraMap R S ((u : Rˣ) : R) * x := by
            rw [← hu, mul_assoc]
      _ = x := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
  have : IsIntegrallyClosedIn R S := isIntegrallyClosedIn_iff.mpr ⟨hinjRS, hclRS⟩
  -- The ring-theoretic half, and the characterization of a discrete valuation ring.
  obtain ⟨h, hh, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal (A := R) hdim
  have havR : ∀ t ∈ minimalPrimes R, h ∉ t :=
    (IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes (A := R) hdim hh).mp hrad
  have hhunit : IsUnit (algebraMap R S h) := by
    have ha'Rad : algebraMap A' R a' ∈ (Ideal.span {h}).radical := by
      rw [hrad]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R p' a').2 ha'mem
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha'Rad
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hn
    refine isUnit_of_mul_isUnit_left (y := algebraMap R S r) ?_
    rw [← map_mul, ← hr, map_pow]
    exact ha'unitS.pow n
  obtain ⟨hdom, hIC⟩ := isDomain_and_isIntegrallyClosed_of_isUnit_of_notMem_minimalPrimes
    (R := R) (S := S) hdim hh havR hhunit
  have : IsDomain R := hdom
  have : IsIntegrallyClosed R := hIC
  have hcrit : IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧
      ringKrullDim R = 1 := ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim⟩
  exact ((isDiscreteValuationRing_tfae R).out 5 1).mp hcrit

end AlgebraicGeometry

end
