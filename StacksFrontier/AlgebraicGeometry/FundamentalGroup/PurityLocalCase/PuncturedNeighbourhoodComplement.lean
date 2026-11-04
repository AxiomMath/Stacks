module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.HypersurfacePurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.NeighbourhoodRestrictionEquivalence

/-!
# The complement of a neighbourhood of the punctured closed fibre

In the local Lefschetz situation `(A, f)` write `X = Spec A`, let `U = X ∖ {𝔪}` be the punctured
spectrum of `A` and let `U₀` be the punctured spectrum of `A / fA`, a closed subscheme of `U`. An
open `U'` with `U₀ ⊆ U' ⊆ U` can omit only points of `U` at which `f` does not vanish, and each
omitted prime `𝔭` is a maximal ideal of `A_f`: the maximal ideal `𝔪` is the only prime containing
`𝔭 + fA`, hence a minimal prime over it, so Krull's principal ideal theorem bounds the height of
the maximal ideal of `A / 𝔭` by one and no prime lies strictly between `𝔭` and `𝔪`.

Consequently, if purity holds for `(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`, then every finite
étale cover of `U'` is the restriction of a finite étale cover of `U`.

## Main results

* `AlgebraicGeometry.exists_isMaximal_away_comap_eq` — a prime of `A` not containing `g` and
  maximal among such primes is the contraction of a maximal ideal of `A_g`.
* `AlgebraicGeometry.LocalLefschetzSituation.mem_of_mem_principalIdeal` — a point of `U` at which
  `f` vanishes lies in every open between `U₀` and `U`.
* `AlgebraicGeometry.LocalLefschetzSituation.eq_closedPoint_of_le_of_mem_principalIdeal` — for a
  prime `𝔭` outside such an open, the maximal ideal is the only prime containing both `𝔭` and `f`.
* `AlgebraicGeometry.LocalLefschetzSituation.closedPoint_mem_minimalPrimes` — the maximal ideal is
  then a minimal prime over `𝔭 + fA`.
* `AlgebraicGeometry.LocalLefschetzSituation.eq_of_le_of_notMem_principalIdeal` — such a `𝔭` is
  maximal among the primes of `A` not containing `f`, that is, it is a maximal ideal of `A_f`.
* `AlgebraicGeometry.LocalLefschetzSituation.essSurj_restriction_of_hasPurity` and
  `AlgebraicGeometry.LocalLefschetzSituation.essSurj_restriction_of_hasPurity_away` —
  restriction of finite étale covers from `U` to an open between `U₀` and `U` is essentially
  surjective, under purity at the local rings of the omitted points and under purity for
  `(A_f)_𝔭` at the maximal ideals of `A_f` respectively.

## Implementation notes

The opens `U'` with `U₀ ⊆ U' ⊆ U` are
`AlgebraicGeometry.LocalLefschetzSituation.IsNeighbourhood`, and restriction of finite étale
covers from `U` to such a neighbourhood is base change along the inclusion `U' ⟶ U`, which is
`AlgebraicGeometry.Scheme.homOfLE`. The extension of a cover of `U'` across the omitted points is
`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_hasPurity`, whose hypothesis is purity for the
local rings of `U` at the points outside `U'`; it needs `U` to be a Noetherian scheme, which is
the instance `AlgebraicGeometry.LocalLefschetzSituation.isNoetherian_U`.

Passing from purity for `(A_f)_𝔭` to purity for the local rings `𝒪_{U, 𝔭}` of the punctured
spectrum uses `AlgebraicGeometry.hasPurity_stalk_puncturedSpectrum` and
`AlgebraicGeometry.hasPurity_atPrime_of_eq_comap`, which identify both with `A_𝔭`. Their input is
a maximal ideal of `A_f` together with the statement that `𝔭` is its contraction, which is what
`AlgebraicGeometry.exists_isMaximal_away_comap_eq` extracts from the maximality of `𝔭` among the
primes of `A` avoiding `f`.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0EY7](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Tag 00KZ](https://stacks.math.columbia.edu/tag/00KZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A point of an open subscheme `V` lies in the image of a smaller open `W` exactly when it lies
in `W`. -/
theorem mem_opensRange_homOfLE {X : Scheme.{u}} {W V : X.Opens} (h : W ≤ V) (x : V.toScheme) :
    x ∈ (X.homOfLE h).opensRange ↔ x.val ∈ W := by
  constructor
  · rintro ⟨y, hy⟩
    have hxy : x.1 = y.1 := by
      rw [← hy]
      exact Scheme.homOfLE_apply h y
    exact hxy.symm ▸ y.2
  · intro hx
    exact ⟨⟨x.val, hx⟩, Subtype.ext (Scheme.homOfLE_apply h ⟨x.val, hx⟩)⟩

/-- A prime of `A` that does not contain `g` and is maximal among the primes not containing `g`
is the contraction of a maximal ideal of `A_g`, namely of its own image there. -/
theorem exists_isMaximal_away_comap_eq {A : Type u} [CommRing A] (g : A) (q : PrimeSpectrum A)
    (hg : g ∉ q.asIdeal)
    (hmax : ∀ r : PrimeSpectrum A, q.asIdeal ≤ r.asIdeal → g ∉ r.asIdeal → r = q) :
    ∃ (p : Ideal (Localization.Away g)) (_ : p.IsMaximal),
      q.asIdeal = p.comap (algebraMap A (Localization.Away g)) := by
  have hdisj : Disjoint (Submonoid.powers g : Set A) (q.asIdeal : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨n, rfl⟩ haq
    exact hg (q.isPrime.mem_of_pow_mem n haq)
  have hpprime : (q.asIdeal.map (algebraMap A (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g)
      q.asIdeal q.isPrime hdisj
  have hcomap : (q.asIdeal.map (algebraMap A (Localization.Away g))).comap
      (algebraMap A (Localization.Away g)) = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g)
      q.isPrime hdisj
  have hunit : IsUnit (algebraMap A (Localization.Away g) g) :=
    IsLocalization.map_units (Localization.Away g)
      (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
  refine ⟨q.asIdeal.map (algebraMap A (Localization.Away g)), ⟨⟨hpprime.ne_top, ?_⟩⟩, hcomap.symm⟩
  intro I hI
  by_contra hItop
  obtain ⟨m, hmmax, hIm⟩ := Ideal.exists_le_maximal I hItop
  have hgm : g ∉ m.comap (algebraMap A (Localization.Away g)) := fun h =>
    hmmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.1 h) hunit)
  have hle : q.asIdeal ≤ m.comap (algebraMap A (Localization.Away g)) := by
    rw [← hcomap]
    exact Ideal.comap_mono (hI.le.trans hIm)
  have heq := hmax ⟨m.comap (algebraMap A (Localization.Away g)),
    hmmax.isPrime.comap (algebraMap A (Localization.Away g))⟩ hle hgm
  have h1 : m.comap (algebraMap A (Localization.Away g)) = q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal heq
  have hmp : m ≤ q.asIdeal.map (algebraMap A (Localization.Away g)) := by
    rw [← h1, IsLocalization.map_under (Submonoid.powers g) (Localization.Away g) m]
  exact (hI.trans_le (hIm.trans hmp)).false

namespace LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-! ### The points of `U` that a neighbourhood of `U₀` omits -/

/-- A point of the punctured spectrum of `A` at which `f` vanishes is a point of `U₀`, hence lies
in every open between `U₀` and `U`. -/
theorem mem_of_mem_principalIdeal {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    {p : PrimeSpectrum S.A} (hfp : S.f ∈ p.asIdeal)
    (hp : p ≠ IsLocalRing.closedPoint S.A) : p ∈ W := by
  have hspan : S.principalIdeal ≤ p.asIdeal := Ideal.span_le.2 (by simpa using hfp)
  have hker : RingHom.ker (Ideal.Quotient.mk S.principalIdeal) ≤ p.asIdeal := by
    rwa [Ideal.mk_ker]
  have hprime : (p.asIdeal.map (Ideal.Quotient.mk S.principalIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : PrimeSpectrum.comap (Ideal.Quotient.mk S.principalIdeal)
      ⟨p.asIdeal.map (Ideal.Quotient.mk S.principalIdeal), hprime⟩ = p := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap _ (p.asIdeal.map (Ideal.Quotient.mk S.principalIdeal)) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hspan]
  have hyU : (⟨p.asIdeal.map (Ideal.Quotient.mk S.principalIdeal), hprime⟩ :
      PrimeSpectrum S.quotientRing) ∈ S.U₀Open := by
    show PrimeSpectrum.comap (Ideal.Quotient.mk S.principalIdeal) _ ∈ S.UOpen
    rw [hcomap]
    exact hp
  rw [← hcomap]
  exact hW.2 hyU

/-- Let `𝔭` lie outside an open between `U₀` and `U`. The maximal ideal is the only prime
containing both `𝔭` and `f`: any other one would be a point of that open lying in the closure of
`𝔭`, which would put `𝔭` in the open as well. -/
theorem eq_closedPoint_of_le_of_mem_principalIdeal {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    {p : PrimeSpectrum S.A} (hpW : p ∉ W) {q : PrimeSpectrum S.A}
    (hle : p.asIdeal ≤ q.asIdeal) (hfq : S.f ∈ q.asIdeal) :
    q = IsLocalRing.closedPoint S.A := by
  by_contra hq
  refine hpW ?_
  have hqW : q ∈ W := S.mem_of_mem_principalIdeal hW hfq hq
  have hmem : q ∈ closure ({p} : Set (PrimeSpectrum S.A)) := by
    rw [PrimeSpectrum.closure_singleton]
    exact hle
  have hopen : IsOpen {x : PrimeSpectrum S.A | x ∈ W} := W.2
  obtain ⟨z, hzW, hzp⟩ := mem_closure_iff.1 hmem _ hopen hqW
  rw [Set.mem_singleton_iff] at hzp
  exact hzp ▸ hzW

/-- For a prime `𝔭` outside an open between `U₀` and `U`, the maximal ideal is a minimal prime
over `𝔭 + fA`: it contains `𝔭 + fA` and is the only prime that does. -/
theorem closedPoint_mem_minimalPrimes {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    {p : PrimeSpectrum S.A} (hpW : p ∉ W) :
    IsLocalRing.maximalIdeal S.A ∈ (p.asIdeal ⊔ Ideal.span {S.f}).minimalPrimes := by
  refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal S.A).isPrime, sup_le
    (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
    (Ideal.span_le.2 (by simpa using S.f_mem_maximalIdeal))⟩, ?_⟩
  intro q hq _
  exact (congrArg PrimeSpectrum.asIdeal
    (S.eq_closedPoint_of_le_of_mem_principalIdeal hW hpW (q := ⟨q, hq.1⟩)
      (le_sup_left.trans hq.2)
      (le_sup_right.trans hq.2 (Ideal.mem_span_singleton_self S.f)))).ge

/-- A prime `𝔭` outside an open between `U₀` and `U` is maximal among the primes of `A` not
containing `f`, that is, it is a maximal ideal of `A_f`. Krull's principal ideal theorem bounds
the height of the maximal ideal of `A / 𝔭` by one, leaving no room for a prime strictly between
`𝔭` and the maximal ideal. -/
theorem eq_of_le_of_notMem_principalIdeal {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    {p : PrimeSpectrum S.A} (hpW : p ∉ W) {q : PrimeSpectrum S.A}
    (hle : p.asIdeal ≤ q.asIdeal) (hfq : S.f ∉ q.asIdeal) : q = p := by
  by_contra hne
  have hlt : p.asIdeal < q.asIdeal :=
    lt_of_le_of_ne hle fun h => hne (PrimeSpectrum.ext h.symm)
  have hqm : q.asIdeal < IsLocalRing.maximalIdeal S.A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
      fun h => hfq (h ▸ S.f_mem_maximalIdeal)
  have hpprime : p.asIdeal.IsPrime := p.isPrime
  have hdom : IsDomain (S.A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  have hkerq : RingHom.ker (Ideal.Quotient.mk p.asIdeal) ≤ q.asIdeal := by
    rwa [Ideal.mk_ker]
  have hkerm : RingHom.ker (Ideal.Quotient.mk p.asIdeal) ≤ IsLocalRing.maximalIdeal S.A := by
    rw [Ideal.mk_ker]
    exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  have hqprime : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerq
  have hmprime :
      ((IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerm
  have hmheight :
      ((IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk p.asIdeal)).height ≤ 1 :=
    Ideal.map_height_le_one_of_mem_minimalPrimes (S.closedPoint_mem_minimalPrimes hW hpW)
  have hqne : q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) ≠ ⊥ := by
    obtain ⟨a, haq, hap⟩ := SetLike.exists_of_lt hlt
    intro hbot
    exact hap ((Ideal.Quotient.eq_zero_iff_mem).1
      (by simpa [hbot] using Ideal.mem_map_of_mem (Ideal.Quotient.mk p.asIdeal) haq))
  have hqbot : (⊥ : Ideal (S.A ⧸ p.asIdeal)) <
      q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) := hqne.bot_lt
  have hqlt : q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) <
      (IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk p.asIdeal) := by
    refine lt_of_le_of_ne (Ideal.map_mono hqm.le) fun h => hqm.ne ?_
    have hback := congrArg (Ideal.comap (Ideal.Quotient.mk p.asIdeal)) h
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle,
      sup_eq_left.2 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)] at hback
  have hone : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    have hbot := Ideal.height_add_one_le_of_lt_of_isPrime hqbot
    rwa [Ideal.height_bot, zero_add] at hbot
  have hcontra : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height + 1 := by gcongr
      _ ≤ ((IsLocalRing.maximalIdeal S.A).map (Ideal.Quotient.mk p.asIdeal)).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hqlt
      _ ≤ 1 := hmheight
  simp at hcontra

/-! ### Extension of finite étale covers to the punctured spectrum -/

/-- If purity holds for the local ring of `U` at every point outside an open `U'` between `U₀` and
`U`, then every finite étale cover of `U'` is the restriction of a finite étale cover of `U`. -/
theorem essSurj_restriction_of_hasPurity {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    (h : ∀ x : S.U, x.val ∉ W → HasPurity (S.U.presheaf.stalk x)) :
    (finiteEtaleBaseChange (S.X.homOfLE hW.1)).EssSurj :=
  essSurj_finiteEtaleBaseChange_of_hasPurity (S.X.homOfLE hW.1)
    fun x hx => h x fun hxW => hx ((mem_opensRange_homOfLE hW.1 x).2 hxW)

/-- If purity holds for `(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`, then every finite étale cover
of an open `U'` between `U₀` and `U` is the restriction of a finite étale cover of `U`: the points
that `U'` omits are exactly contractions of maximal ideals of `A_f`, and purity for `(A_f)_𝔭` is
purity for the local ring of `U` there. -/
theorem essSurj_restriction_of_hasPurity_away {W : S.X.Opens} (hW : S.IsNeighbourhood W)
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p)) :
    (finiteEtaleBaseChange (S.X.homOfLE hW.1)).EssSurj := by
  refine S.essSurj_restriction_of_hasPurity hW fun x hx => ?_
  have hf : S.f ∉ (x.1 : PrimeSpectrum S.A).asIdeal := fun hfm =>
    hx (S.mem_of_mem_principalIdeal hW hfm x.2)
  obtain ⟨p, hpmax, hpc⟩ := exists_isMaximal_away_comap_eq S.f x.1 hf
    fun r hr hfr => S.eq_of_le_of_notMem_principalIdeal hW hx hr hfr
  have hprime : (x.1 : PrimeSpectrum S.A).asIdeal.IsPrime := x.1.isPrime
  exact hasPurity_stalk_puncturedSpectrum x.1 x.2
    (hasPurity_atPrime_of_eq_comap S.f p x.1.asIdeal hpc (haway p))

end LocalLefschetzSituation

end AlgebraicGeometry

end
