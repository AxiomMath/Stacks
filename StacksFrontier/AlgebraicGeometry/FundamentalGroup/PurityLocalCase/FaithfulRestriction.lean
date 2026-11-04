module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleMorphisms.Restriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LocalLefschetz

/-!
# Faithfulness of restriction in the local Lefschetz situation

In the local Lefschetz situation `(A, f)`, restriction of finite étale covers from the
punctured spectrum `U` of `A` to the punctured spectrum `U₀` of `A / fA` is faithful as soon as
every connected component of `U` meets `U₀`. That happens in particular when `dim (A / 𝔭) ≥ 2`
for every minimal prime `𝔭` of `A` not containing `f`: such a `𝔭` then admits a prime strictly
between `𝔭` and the maximal ideal which contains `f`, so the irreducible component of `U` cut
out by `𝔭` already meets `U₀`.

The same argument applies to an open `U'` with `U₀ ⊆ U' ⊆ U` once the dimension bound is only
required of the minimal primes lying in `U'`. Such a `U'` exists — delete from `U` the
one-dimensional irreducible components of `X` that miss `U₀` — and the hypothesis survives
shrinking, so the faithful `U'` are cofinal among the opens between `U₀` and `U`.

## Main definitions

* `AlgebraicGeometry.LocalLefschetzSituation.HasLargeMissingComponents` — the dimension
  condition on an open of `X`.
* `AlgebraicGeometry.LocalLefschetzSituation.homToOpen` — the factorization of `U₀ ⟶ U`
  through an open of `X` containing `U₀`.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.faithful_finiteEtaleRestriction` — faithfulness of
  the base-change functor `FÉt_U ⟶ FÉt_{U₀}` under either hypothesis.
* `AlgebraicGeometry.LocalLefschetzSituation`
  `.faithful_finiteEtaleBaseChange_of_hasLargeMissingComponents` — faithfulness of
  `FÉt_{U'} ⟶ FÉt_{U₀}` for an open `U'` between `U₀` and `U` satisfying the dimension condition.
* `AlgebraicGeometry.LocalLefschetzSituation.exists_hasLargeMissingComponents` and
  `AlgebraicGeometry.LocalLefschetzSituation.HasLargeMissingComponents.mono` — existence of such
  a `U'`, and stability of the condition under shrinking.
* `AlgebraicGeometry.LocalLefschetzSituation.exists_le_faithful_finiteEtaleBaseChange` and
  `AlgebraicGeometry.LocalLefschetzSituation.exists_le_finiteEtaleBaseChange_map_eq` — the
  faithful opens are cofinal, so two morphisms of finite étale covers of `U'` agreeing on `U₀`
  agree on a smaller open.

## Implementation notes

The component condition is phrased as surjectivity of `ConnectedComponents S.U₀ToU` on
connected components, which is the form in which
`Stacks.FundamentalGroup.faithful_finiteEtaleRestriction_of_components_meet` consumes it.
Reducing the dimension hypothesis to it goes through the closure of a minimal prime: every
point of `U` lies in the component of the minimal prime below it, and so does the prime
containing `f` produced from the dimension bound.

An open `U' ⊆ U` is represented by an open `W` of `X` with `W ≤ UOpen`, and the condition
`U₀ ⊆ U'` by `U₀Open ≤ X₀ToX ⁻¹ᵁ W`. A minimal prime of `A` lying in `U` is outside `U₀`
exactly when it does not contain `f`.

## References

* [Stacks Project, Tag 0BLG](https://stacks.math.columbia.edu/tag/0BLG)
* [Stacks Project, Tag 0BLN](https://stacks.math.columbia.edu/tag/0BLN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.LocalLefschetzSituation

/-- Let `R` be a Noetherian local ring, let `f` be in its maximal ideal and let `p` be a prime
not containing `f` with `dim (R / p) ≥ 2`. Then there is a non-closed prime above `p` which
does contain `f`: in `R / p` the element `f` is a nonzerodivisor in the maximal ideal, so
cutting it out drops the dimension by exactly one and leaves a ring of positive dimension,
whose non-maximal primes pull back to the primes sought. -/
private theorem exists_nonclosed_prime_over_prime
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (f : R) (hfmax : f ∈ IsLocalRing.maximalIdeal R)
    (p : Ideal R) (hp : p.IsPrime) (hf : f ∉ p)
    (hdim : 2 ≤ ringKrullDim (R ⧸ p)) :
    ∃ q : PrimeSpectrum R, p ≤ q.asIdeal ∧ f ∈ q.asIdeal ∧
      q ≠ IsLocalRing.closedPoint R := by
  have : p.IsPrime := hp
  let B := R ⧸ p
  let fb : B := Ideal.Quotient.mk p f
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hfbMax : fb ∈ IsLocalRing.maximalIdeal B := by
    show f ∈ (IsLocalRing.maximalIdeal B).comap (Ideal.Quotient.mk p)
    rw [IsLocalRing.maximalIdeal_comap]
    exact hfmax
  have hdimEq : ringKrullDim (B ⧸ Ideal.span {fb}) + 1 = ringKrullDim B :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr
        (fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h))) hfbMax
  have hspanNe : Ideal.span {fb} ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (Ideal.span_le.mpr (by simpa using hfbMax))
  let T := B ⧸ Ideal.span {fb}
  have : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hspanNe
  have : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {fb}))
      Ideal.Quotient.mk_surjective
  have hdimT : 0 < ringKrullDim T := by
    have hTle : 1 + 1 ≤ ringKrullDim T + 1 := by
      show 1 + 1 ≤ ringKrullDim (B ⧸ Ideal.span {fb}) + 1
      simpa only [one_add_one_eq_two, hdimEq] using hdim
    exact lt_of_lt_of_le (by norm_num)
      (ENat.WithBot.add_le_add_one_right_iff.mp hTle)
  obtain ⟨q, r, hqr⟩ := Order.krullDim_pos_iff.mp (by
    simpa [ringKrullDim] using hdimT : 0 < Order.krullDim (PrimeSpectrum T))
  let g : R →+* T := (Ideal.Quotient.mk (Ideal.span {fb})).comp (Ideal.Quotient.mk p)
  have hgSurj : Function.Surjective g :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  let qa : PrimeSpectrum R := PrimeSpectrum.comap g q
  have : IsLocalHom g := IsLocalHom.of_surjective g hgSurj
  have hqNotClosed : q ≠ IsLocalRing.closedPoint T := by
    intro hq
    have hrle : r ≤ IsLocalRing.closedPoint T :=
      (PrimeSpectrum.asIdeal_le_asIdeal r _).mp (IsLocalRing.le_maximalIdeal r.2.1)
    exact (not_lt_of_ge hrle) (by simpa [hq] using hqr)
  have hqaNotClosed : qa ≠ IsLocalRing.closedPoint R := by
    intro h
    exact hqNotClosed (PrimeSpectrum.comap_injective_of_surjective g hgSurj
      (h.trans (IsLocalRing.comap_closedPoint g).symm))
  refine ⟨qa, ?_, ?_, hqaNotClosed⟩
  · intro a ha
    show g a ∈ q.asIdeal
    show Ideal.Quotient.mk (Ideal.span {fb}) (Ideal.Quotient.mk p a) ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _
  · show g f ∈ q.asIdeal
    show Ideal.Quotient.mk (Ideal.span {fb}) fb ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton fb))]
    exact Ideal.zero_mem _

/-- A point of a subspace that specializes to another one in the ambient space already
specializes to it inside the subspace. -/
private theorem specializes_subtype {T : Type*} [TopologicalSpace T] {P : T → Prop}
    {x y : {t : T // P t}} (h : (x : T) ⤳ (y : T)) : x ⤳ y := by
  rw [specializes_iff_mem_closure, closure_subtype]
  simpa using h.mem_closure

/-- The subspace form of `specializes_subtype`, with the ambient image of the target given by an
equation. -/
private theorem specializes_subtype_of_eq {T : Type*} [TopologicalSpace T] {P : T → Prop}
    {x y : {t : T // P t}} {z : T} (hz : (y : T) = z) (h : (x : T) ⤳ z) : x ⤳ y :=
  specializes_subtype (by rwa [hz])

/-- A point and a specialization of it lie in the same connected component. -/
private theorem connectedComponents_eq_of_specializes {T : Type*} [TopologicalSpace T]
    {x y : T} (h : x ⤳ y) : (x : ConnectedComponents T) = y := by
  have hy : y ∈ connectedComponent x :=
    isPreconnected_singleton.closure.subset_connectedComponent
      (subset_closure (Set.mem_singleton x)) h.mem_closure
  exact ((ConnectedComponents.coe_eq_coe').2 hy).symm

/-- The restriction `U₀ ⟶ U` is a closed immersion. -/
private theorem isClosedImmersion_U₀ToU (S : LocalLefschetzSituation.{u}) :
    IsClosedImmersion S.U₀ToU := by
  have : IsClosedImmersion S.X₀ToX :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk S.principalIdeal))
      Ideal.Quotient.mk_surjective
  show IsClosedImmersion (S.X₀ToX ∣_ S.UOpen)
  infer_instance

/-- Given a non-closed point `x` of `Spec A` such that every minimal prime specializing to `x` and
not containing `f` has `dim (A / 𝔭) ≥ 2`, there is a non-closed minimal prime `𝔭` specializing to
`x` and a point of `U₀` whose image in `Spec A` is a specialization of `𝔭`. -/
private theorem exists_specializes_point_over_U₀ (S : LocalLefschetzSituation.{u})
    {x : PrimeSpectrum S.A} (hxne : x ≠ IsLocalRing.closedPoint S.A)
    (hdim : ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → p ⤳ x → S.f ∉ p.asIdeal →
      2 ≤ ringKrullDim (S.A ⧸ p.asIdeal)) :
    ∃ (p : PrimeSpectrum S.A) (y : S.U₀), p ≠ IsLocalRing.closedPoint S.A ∧ p ⤳ x ∧
      p ⤳ S.UOpen.ι (S.U₀ToU y) := by
  obtain ⟨p, hpMem, hpx⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S.A)) (J := x.asIdeal) bot_le
  have hp : IsMinimalPrime p := by simpa [Ideal.IsMinimalPrime] using hpMem
  let pPoint : PrimeSpectrum S.A := ⟨p, hp.isPrime⟩
  have hspecpx : pPoint ⤳ x :=
    (PrimeSpectrum.le_iff_specializes pPoint x).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal pPoint x).2 hpx)
  have hpNotClosed : pPoint ≠ IsLocalRing.closedPoint S.A := by
    intro e
    have ep : p = IsLocalRing.maximalIdeal S.A := by
      simpa [pPoint, IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal e
    apply hxne
    apply PrimeSpectrum.ext
    show x.asIdeal = IsLocalRing.maximalIdeal S.A
    exact le_antisymm (IsLocalRing.le_maximalIdeal x.isPrime.ne_top')
      (by simpa [ep] using hpx)
  obtain ⟨qPoint, hpq, hqf, hqNotClosed⟩ :
      ∃ q : PrimeSpectrum S.A, p ≤ q.asIdeal ∧ S.f ∈ q.asIdeal ∧
        q ≠ IsLocalRing.closedPoint S.A := by
    by_cases hf : S.f ∈ p
    · exact ⟨pPoint, le_refl _, hf, hpNotClosed⟩
    · exact exists_nonclosed_prime_over_prime S.f S.f_mem_maximalIdeal p hp.isPrime hf
        (hdim pPoint hp hspecpx hf)
  let fquot : S.A →+* S.quotientRing := Ideal.Quotient.mk S.principalIdeal
  have hqrange : qPoint ∈ Set.range (PrimeSpectrum.comap fquot) := by
    rw [range_comap_of_surjective _ fquot Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus]
    intro a ha
    have hspan : S.principalIdeal ≤ qPoint.asIdeal :=
      Ideal.span_le.mpr (by rintro z rfl; exact hqf)
    exact hspan (by simpa [fquot, RingHom.mem_ker] using ha)
  obtain ⟨q0, hq0⟩ := hqrange
  have hq0NotClosed : q0 ≠ IsLocalRing.closedPoint S.quotientRing := fun e =>
    hqNotClosed (by rw [← hq0, e, IsLocalRing.comap_closedPoint])
  let y : S.U₀ := ⟨q0, by
    rw [S.U₀Open_eq_puncturedSpectrumOpen]
    exact hq0NotClosed⟩
  have hqy : S.UOpen.ι (S.U₀ToU y) = qPoint :=
    Eq.trans (congrArg (fun g : S.U₀ ⟶ S.X => g y) S.U₀ToU_comp_immersion) hq0
  exact ⟨pPoint, y, hpNotClosed, hspecpx, hqy ▸ (PrimeSpectrum.le_iff_specializes pPoint qPoint).mp
    ((PrimeSpectrum.asIdeal_le_asIdeal pPoint qPoint).2 hpq)⟩

/-- **Stacks Project, Tag 0BLG.** In the local Lefschetz situation, base change of finite étale
covers from the punctured spectrum of `A` to the punctured spectrum of `A / fA` is faithful,
provided either that `dim (A / 𝔭) ≥ 2` for every minimal prime `𝔭` of `A` with `f ∉ 𝔭`, or
that every connected component of `U` meets `U₀`. -/
@[stacks 0BLG]
lemma faithful_finiteEtaleRestriction (S : LocalLefschetzSituation.{u})
    (h :
      (∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal →
        S.f ∉ p.asIdeal → 2 ≤ ringKrullDim (S.A ⧸ p.asIdeal)) ∨
      (∀ c : ConnectedComponents S.U,
        ∃ x : S.U₀, ConnectedComponents.mk (S.U₀ToU.base x) = c)) :
    (finiteEtaleBaseChange S.U₀ToU).Faithful := by
  have := isClosedImmersion_U₀ToU S
  apply Stacks.FundamentalGroup.faithful_finiteEtaleRestriction_of_components_meet
    (X := S.U) (Y := S.U₀) S.U₀ToU
  rcases h with hdim | hcomp
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨p, y, hpne, hpx, hpy⟩ := exists_specializes_point_over_U₀ S x.property
      fun p hp _ hf => hdim p hp hf
    let pU : S.U := ⟨p, hpne⟩
    exact ⟨y, (connectedComponents_eq_of_specializes
        (specializes_subtype_of_eq (x := pU) (y := S.U₀ToU y) rfl hpy)).symm.trans
      (connectedComponents_eq_of_specializes (specializes_subtype (x := pU) hpx))⟩
  · exact hcomp

/-- The dimension condition on an open `W` of `X`: every minimal prime of `A` lying in `W` but
not in `U₀` has `dim (A / 𝔭) ≥ 2`. A minimal prime lies outside `U₀` exactly when it does not
contain `f`. -/
def HasLargeMissingComponents (S : LocalLefschetzSituation.{u}) (W : S.X.Opens) : Prop :=
  ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → p ∈ W → S.f ∉ p.asIdeal →
    2 ≤ ringKrullDim (S.A ⧸ p.asIdeal)

/-- The dimension condition passes to smaller opens: a minimal prime in the smaller open lies in
the larger one. -/
@[stacks 0BLN "stability of the dimension hypothesis under shrinking `U'`"]
theorem HasLargeMissingComponents.mono {S : LocalLefschetzSituation.{u}} {W W' : S.X.Opens}
    (hWW' : W' ≤ W) (hW : S.HasLargeMissingComponents W) :
    S.HasLargeMissingComponents W' :=
  fun p hp hpW' hf => hW p hp (hWW' hpW') hf

/-- The factorization of `U₀ ⟶ X` through an open `W` of `X` whose inverse image in `X₀`
contains `U₀`. -/
noncomputable def homToOpen (S : LocalLefschetzSituation.{u}) {W : S.X.Opens}
    (h : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W) : S.U₀ ⟶ W.toScheme :=
  S.X₀.homOfLE h ≫ S.X₀ToX ∣_ W

/-- The factorization through an open of `X` is compatible with the two open immersions. -/
@[reassoc]
lemma homToOpen_comp_ι (S : LocalLefschetzSituation.{u}) {W : S.X.Opens}
    (h : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W) :
    S.homToOpen h ≫ W.ι = S.U₀ToU ≫ S.UOpen.ι := by
  rw [homToOpen, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι,
    S.U₀ToU_comp_immersion]

/-- **Stacks Project, Tag 0BLN.** In the local Lefschetz situation let `U'` be an open of `X`
with `U₀ ⊆ U' ⊆ U`. If every minimal prime of `A` lying in `U'` but not in `U₀` has
`dim (A / 𝔭) ≥ 2`, then base change of finite étale covers along `U₀ ⟶ U'` is faithful. -/
@[stacks 0BLN "faithfulness of restriction from an open `U'` with `U₀ ⊆ U' ⊆ U`"]
theorem faithful_finiteEtaleBaseChange_of_hasLargeMissingComponents
    (S : LocalLefschetzSituation.{u}) {W : S.X.Opens} (hW : W ≤ S.UOpen)
    (r : S.U₀ ⟶ W.toScheme) (hr : r ≫ W.ι = S.U₀ToU ≫ S.UOpen.ι)
    (hdim : S.HasLargeMissingComponents W) :
    (finiteEtaleBaseChange r).Faithful := by
  have := isClosedImmersion_U₀ToU S
  have hfactor : r ≫ S.X.homOfLE hW = S.U₀ToU :=
    (cancel_mono S.UOpen.ι).1 (by rwa [Category.assoc, Scheme.homOfLE_ι])
  have : IsClosedImmersion (r ≫ S.X.homOfLE hW) := hfactor ▸ inferInstance
  have : IsClosedImmersion r := IsClosedImmersion.of_comp r (S.X.homOfLE hW)
  apply Stacks.FundamentalGroup.faithful_finiteEtaleRestriction_of_components_meet r
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨p, y, hpne, hpx, hpy⟩ := exists_specializes_point_over_U₀ S (hW x.2)
    fun p hp hsp hf => hdim p hp (hsp.mem_open W.isOpen x.2) hf
  have himage : W.ι (r y) = S.UOpen.ι (S.U₀ToU y) :=
    congrArg (fun g : S.U₀ ⟶ S.X => g y) hr
  let pW : W.toScheme := ⟨p, hpx.mem_open W.isOpen x.2⟩
  exact ⟨y, (connectedComponents_eq_of_specializes
      (specializes_subtype_of_eq (x := pW) (y := r y) himage hpy)).symm.trans
    (connectedComponents_eq_of_specializes (specializes_subtype (x := pW) hpx))⟩

/-- In a Noetherian local ring, a prime `𝔭` with `f ∉ 𝔭` and `dim (A / 𝔭) = 1` has no
non-closed prime above it containing `f`: such a prime would be neither the generic nor the
closed point of the one-dimensional local ring `A / 𝔭`. -/
private theorem not_exists_nonclosed_prime_over_prime_of_dim_eq_one
    (S : LocalLefschetzSituation.{u}) {p : Ideal S.A} [hp : p.IsPrime] (hfp : S.f ∉ p)
    (hdim : ringKrullDim (S.A ⧸ p) = 1) {q : PrimeSpectrum S.A} (hpq : p ≤ q.asIdeal)
    (hqf : S.f ∈ q.asIdeal) (hqne : q ≠ IsLocalRing.closedPoint S.A) : False := by
  let R := S.A ⧸ p
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  have : IsLocalRing R :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hrange : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p)) := by
    rw [range_comap_of_surjective R (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.mpr hpq
  obtain ⟨qR, hqR⟩ := hrange
  have hqRneBot : qR ≠ (⊥ : PrimeSpectrum R) := by
    intro h
    refine hfp ?_
    have hqIdeal : q.asIdeal = p := by
      rw [← hqR, h]
      show RingHom.ker (Ideal.Quotient.mk p) = p
      exact Ideal.mk_ker
    exact hqIdeal ▸ hqf
  have hqRneTop : qR ≠ (⊤ : PrimeSpectrum R) := by
    intro h
    exact hqne (by rw [← hqR, show qR = IsLocalRing.closedPoint R from h,
      IsLocalRing.comap_closedPoint])
  exact (Order.krullDim_le_one_iff_of_boundedOrder.mp
    (by simpa [ringKrullDim, R] using hdim.le) qR).elim hqRneBot hqRneTop

/-- **Stacks Project, Tag 0BLN.** In the local Lefschetz situation there is an open `U'` of `X`
with `U₀ ⊆ U' ⊆ U` satisfying the dimension hypothesis: remove from `U` the one-dimensional
irreducible components of `X` that do not meet `U₀`. -/
@[stacks 0BLN "existence of an open `U'` with `U₀ ⊆ U' ⊆ U` satisfying the dimension hypothesis"]
theorem exists_hasLargeMissingComponents (S : LocalLefschetzSituation.{u}) :
    ∃ W : S.X.Opens, W ≤ S.UOpen ∧ S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W ∧
      S.HasLargeMissingComponents W := by
  classical
  let M : Set (Ideal S.A) :=
    {p | IsMinimalPrime p ∧ ringKrullDim (S.A ⧸ p) = 1 ∧ S.f ∉ p}
  have hMfinite : M.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing S.A).subset fun p hp => hp.1
  let bad : Set (PrimeSpectrum S.A) := ⋃ p ∈ M, PrimeSpectrum.zeroLocus (p : Set S.A)
  have hbadclosed : IsClosed bad :=
    hMfinite.isClosed_biUnion fun p _ => PrimeSpectrum.isClosed_zeroLocus _
  let W : S.X.Opens := ⟨(S.UOpen : Set S.X) \ bad, S.UOpen.isOpen.sdiff hbadclosed⟩
  have hW : W ≤ S.UOpen := fun _ hx => hx.1
  have havoid {q : PrimeSpectrum S.A} (hqf : S.f ∈ q.asIdeal)
      (hqne : q ≠ IsLocalRing.closedPoint S.A) : q ∉ bad := by
    intro hqbad
    obtain ⟨p, hpM, hqzero⟩ := Set.mem_iUnion₂.mp hqbad
    obtain ⟨hpmin, hpdim, hpf⟩ : IsMinimalPrime p ∧ ringKrullDim (S.A ⧸ p) = 1 ∧ S.f ∉ p := hpM
    have := hpmin.isPrime
    exact not_exists_nonclosed_prime_over_prime_of_dim_eq_one S hpf hpdim
      (SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus q _).mp hqzero)) hqf hqne
  refine ⟨W, hW, ?_, ?_⟩
  · intro z hz
    have hqU : S.X₀ToX.base z ∈ S.UOpen := hz
    have hqne : S.X₀ToX.base z ≠ IsLocalRing.closedPoint S.A := hqU
    have hqf : S.f ∈ (S.X₀ToX.base z).asIdeal := by
      show S.f ∈ Ideal.comap (Ideal.Quotient.mk S.principalIdeal) z.asIdeal
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton S.f))]
      exact z.asIdeal.zero_mem
    exact ⟨hqU, havoid hqf hqne⟩
  · intro x hxmin hxW hxf
    let R := S.A ⧸ x.asIdeal
    have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hxmin.isPrime.ne_top
    have : IsLocalRing R :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk x.asIdeal) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk x.asIdeal) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hxU : x ∈ S.UOpen := hW hxW
    have hxne : x ≠ IsLocalRing.closedPoint S.A := hxU
    have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
    have hdimNeZero : ringKrullDim R ≠ 0 := by
      intro hzero
      have : Ring.KrullDimLE 0 R := ⟨by change ringKrullDim R ≤ 0; rw [hzero]⟩
      have : x.asIdeal.IsPrime := x.isPrime
      refine hxne (PrimeSpectrum.ext ?_)
      calc
        x.asIdeal = (⊥ : Ideal R).comap (Ideal.Quotient.mk x.asIdeal) :=
          (Ideal.mk_ker (I := x.asIdeal)).symm
        _ = (IsLocalRing.maximalIdeal R).comap (Ideal.Quotient.mk x.asIdeal) := by
          rw [Ring.KrullDimLE.eq_maximalIdeal_of_isPrime (⊥ : Ideal R)]
        _ = IsLocalRing.maximalIdeal S.A := IsLocalRing.maximalIdeal_comap _
    have hdimNeOne : ringKrullDim R ≠ 1 := by
      intro hdimone
      refine hxW.2 (Set.mem_iUnion.mpr ⟨x.asIdeal, Set.mem_iUnion.mpr
        ⟨⟨hxmin, hdimone, hxf⟩, ?_⟩⟩)
      exact (PrimeSpectrum.mem_zeroLocus x _).mpr (SetLike.coe_subset_coe.mpr le_rfl)
    by_contra hnotlarge
    have hlt : ringKrullDim R < 2 := lt_of_not_ge hnotlarge
    cases hdimval : ringKrullDim R with
    | bot =>
        rw [hdimval] at hnonneg
        simp at hnonneg
    | coe d =>
        cases d with
        | top => exact absurd hlt (not_lt_of_ge (by simp [hdimval]))
        | coe n =>
            have hn : n < 2 := by simpa [hdimval] using hlt
            rcases (by omega : n = 0 ∨ n = 1) with hn0 | hn1
            · exact hdimNeZero (by simp [hdimval, hn0])
            · exact hdimNeOne (by simp [hdimval, hn1])

/-- **Stacks Project, Tag 0BLN.** The opens `U'` with `U₀ ⊆ U' ⊆ U` for which restriction of
finite étale covers to `U₀` is faithful are cofinal among all opens between `U₀` and `U`: this
is what makes restriction from `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'}` to `FÉt_{U₀}` faithful. -/
@[stacks 0BLN "cofinality of the faithful neighbourhoods of `U₀` in `U`, the criterion for \
faithfulness of restriction from the colimit over all such neighbourhoods"]
theorem exists_le_faithful_finiteEtaleBaseChange (S : LocalLefschetzSituation.{u})
    {V : S.X.Opens} (hV : V ≤ S.UOpen) (hVU₀ : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ V) :
    ∃ (W : S.X.Opens) (hWU₀ : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W),
      W ≤ V ∧ (finiteEtaleBaseChange (S.homToOpen hWU₀)).Faithful := by
  obtain ⟨U', hU', hU'₀, hdim⟩ := S.exists_hasLargeMissingComponents
  refine ⟨V ⊓ U', fun z hz => ⟨hVU₀ hz, hU'₀ hz⟩, inf_le_left,
    S.faithful_finiteEtaleBaseChange_of_hasLargeMissingComponents
      (inf_le_left.trans hV) _ (S.homToOpen_comp_ι _) (hdim.mono inf_le_right)⟩

/-- **Stacks Project, Tag 0BLN.** Two morphisms of finite étale covers of an open `U'` with
`U₀ ⊆ U' ⊆ U` which agree after base change to `U₀` already agree after base change to some
smaller open `U''` with `U₀ ⊆ U'' ⊆ U'`. This is faithfulness of the restriction functor
`colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` written out on representatives. -/
@[stacks 0BLN "faithfulness of restriction from the colimit over the opens between `U₀` and `U`, \
written out on representatives of the filtered colimit"]
theorem exists_le_finiteEtaleBaseChange_map_eq (S : LocalLefschetzSituation.{u})
    {V : S.X.Opens} (hV : V ≤ S.UOpen) (hVU₀ : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ V)
    {A B : FiniteEtaleOver V.toScheme} (a b : A ⟶ B)
    (hab : (finiteEtaleBaseChange (S.homToOpen hVU₀)).map a =
      (finiteEtaleBaseChange (S.homToOpen hVU₀)).map b) :
    ∃ (W : S.X.Opens) (_ : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W) (hWV : W ≤ V),
      (finiteEtaleBaseChange (S.X.homOfLE hWV)).map a =
        (finiteEtaleBaseChange (S.X.homOfLE hWV)).map b := by
  obtain ⟨W, hWU₀, hWV, hfaithful⟩ := S.exists_le_faithful_finiteEtaleBaseChange hV hVU₀
  refine ⟨W, hWU₀, hWV, ?_⟩
  have hfg : S.homToOpen hVU₀ = S.homToOpen hWU₀ ≫ S.X.homOfLE hWV := by
    apply (cancel_mono V.ι).1
    rw [S.homToOpen_comp_ι, Category.assoc, Scheme.homOfLE_ι, S.homToOpen_comp_ι]
  let F := finiteEtaleBaseChange (S.homToOpen hWU₀)
  let G := finiteEtaleBaseChange (S.X.homOfLE hWV)
  let α : finiteEtaleBaseChange (S.homToOpen hVU₀) ≅ G ⋙ F :=
    MorphismProperty.Over.pullbackComp (P := finiteEtale) (Q := ⊤)
      (S.homToOpen hWU₀) (S.X.homOfLE hWV) (S.homToOpen hVU₀) hfg
  have h1 := α.hom.naturality a
  have h2 := α.hom.naturality b
  rw [hab] at h1
  exact hfaithful.map_injective ((cancel_epi (α.hom.app A)).1 (h1.symm.trans h2))

end AlgebraicGeometry.LocalLefschetzSituation

end
