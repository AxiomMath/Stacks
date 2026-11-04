module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Stalk
public import StacksFrontier.RingTheory.CohenMacaulay.Catenary
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.Topology.Dimension.DimensionFunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen--Macaulay schemes as bases for Chow homology

A Cohen--Macaulay scheme is locally Noetherian and universally catenary, and the negative of
the dimension of its local ring is a dimension function on it. These are exactly the three data
of a base situation for Chow homology, so every Cohen--Macaulay scheme carries one.

## Main definitions

* `AlgebraicGeometry.negativeLocalRingDimension` is the integer-valued negative of the
  dimension of the local ring of a scheme at a point.

## Main results

* `Ring.IsUniversallyCatenary.of_isCohenMacaulayLocalRing` — a Noetherian local
  Cohen--Macaulay ring is universally catenary.
* `AlgebraicGeometry.IsCohenMacaulay.isLocallyNoetherian` — local Noetherianity.
* `AlgebraicGeometry.IsCohenMacaulay.isUniversallyCatenary` — universal catenarity.
* `AlgebraicGeometry.IsCohenMacaulay.negativeLocalRingDimension_isDimensionFunction` — the
  negative local-ring dimension is a dimension function.

## Implementation notes

The Krull dimension in the library takes values in `WithBot ℕ∞`. For the Noetherian nonzero
local rings occurring here it is a finite natural number; `WithBot.unbotD 0` and `ENat.toNat`
express that natural number before coercion to the integers.

The dimension-function axioms are checked through a single local computation: for a
specialization `x ⤳ y` on a Cohen--Macaulay scheme there is a prime `𝔭` of the local ring at
`y` with `dim 𝒪_y = height 𝔭 + dim (𝒪_y / 𝔭)` and `dim 𝒪_x = height 𝔭`, where `𝔭` is the prime
cut out by `x` in an affine neighbourhood of `y`. The first equation is the dimension formula
for a maximal Cohen--Macaulay module, and the quotient term is the coheight of `𝔭`, which is
positive for a nontrivial specialization and equal to one for an immediate one.

Universal catenarity is reduced to the local rings by Stacks 02JA, and a Noetherian local
Cohen--Macaulay ring is universally catenary by Stacks 00NM applied to the ring as a module
over itself.

## References

* [Stacks Project, Tag 0F91](https://stacks.math.columbia.edu/tag/0F91)
-/

@[expose] public section

open TopologicalSpace

universe u

/-! ### Universal catenarity of a Cohen--Macaulay local ring -/

/-- A Noetherian local Cohen--Macaulay ring is universally catenary: it is a Cohen--Macaulay
module over itself of full support, so Stacks 00NM applies. -/
@[ega "0 16.5.12" "more general"]
theorem Ring.IsUniversallyCatenary.of_isCohenMacaulayLocalRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : IsCohenMacaulayLocalRing R) :
    Ring.IsUniversallyCatenary R := by
  have hmax : Module.IsMaximalCohenMacaulay R R :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay R).mp hR
  refine Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ (M := R) ?_ ?_
  · intro p _
    have e : LocalizedModule p.asIdeal.primeCompl R ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal :=
      (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
        (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
          p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    rw [Module.depth_eq_depth_of_linearEquiv _ e, Module.supportDim_eq_of_equiv e,
      Module.supportDim_self_eq_ringKrullDim]
    exact hmax.of_isLocalization_atPrime p.asIdeal (Localization.AtPrime p.asIdeal)
  · rw [Module.support_eq_zeroLocus,
      Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R),
      PrimeSpectrum.zeroLocus_bot]

namespace AlgebraicGeometry

/-- The negative of the dimension of the local ring of a scheme at a point, as an integer. -/
@[stacks 0F91 "the function"]
noncomputable def negativeLocalRingDimension (S : Scheme.{u}) (s : S) : ℤ :=
  -(((ringKrullDim (S.presheaf.stalk s)).unbotD 0).toNat : ℤ)

/-! ### The base data of a Cohen--Macaulay scheme -/

/-- **Stacks Project, Tag 0F91.** A Cohen--Macaulay scheme is locally Noetherian. -/
@[stacks 0F91 "local Noetherianity"]
theorem IsCohenMacaulay.isLocallyNoetherian {S : Scheme.{u}} (hS : IsCohenMacaulay S) :
    IsLocallyNoetherian S :=
  (((isCohenMacaulay_tfae_stalk S).out 1 2 rfl rfl).mp hS).1

/-- **Stacks Project, Tag 0F91.** A Cohen--Macaulay scheme is universally catenary: each of its
local rings is a Noetherian Cohen--Macaulay local ring, hence universally catenary, and
universal catenarity of a locally Noetherian scheme is a condition on its local rings. -/
@[stacks 0F91 "universal catenarity", ega "IV 5.2.5" "more general", sga "6 X 1.5" "special case"]
theorem IsCohenMacaulay.isUniversallyCatenary {S : Scheme.{u}} (hS : IsCohenMacaulay S)
    [IsLocallyNoetherian S] : Scheme.IsUniversallyCatenary S := by
  refine (Scheme.isUniversallyCatenary_iff_stalk_isUniversallyCatenary S).mpr fun s => ?_
  obtain ⟨hNs, hCMs⟩ := (((isCohenMacaulay_tfae_stalk S).out 1 2 rfl rfl).mp hS).2 s
  have : IsNoetherianRing (S.presheaf.stalk s) := hNs
  exact Ring.IsUniversallyCatenary.of_isCohenMacaulayLocalRing hCMs

/-- The local rings of a Cohen--Macaulay scheme are Noetherian. -/
private theorem IsCohenMacaulay.isNoetherianRing_stalk {S : Scheme.{u}} (hS : IsCohenMacaulay S)
    (s : S) : IsNoetherianRing (S.presheaf.stalk s) :=
  ((((isCohenMacaulay_tfae_stalk S).out 1 2 rfl rfl).mp hS).2 s).1

/-! ### The dimension function -/

/-- In a Noetherian local ring, the quotient by a prime covered by the maximal ideal has
dimension one. -/
private theorem ringKrullDim_quotient_eq_one_of_covBy_top {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {p : Ideal R} (hp : p.IsPrime)
    (h : (⟨p, hp⟩ : PrimeSpectrum R) ⋖ ⊤) : ringKrullDim (R ⧸ p) = 1 := by
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hcohne : Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) ≠ ⊤ := by
    intro htop
    refine ringKrullDim_ne_top (R := R ⧸ p) ?_
    rw [← coheight_eq_ringKrullDim_quotient (⟨p, hp⟩ : PrimeSpectrum R), htop]
    simp
  have hcoh : Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) = ((0 : ℕ) : ℕ∞) + 1 := by
    rw [Order.coheight_eq_coe_add_one_iff]
    exact ⟨lt_top_iff_ne_top.mpr hcohne, ⟨⊤, h.1, by simp⟩, fun q hpq => by
      simp [(of_not_not fun hne => h.2 hpq (lt_of_le_of_ne le_top hne) :
        q = (⊤ : PrimeSpectrum R))]⟩
  rw [← coheight_eq_ringKrullDim_quotient (⟨p, hp⟩ : PrimeSpectrum R), hcoh]
  norm_num

/-- A nonzero Noetherian local ring, and more generally any ring of finite Krull dimension, has
Krull dimension a natural number. -/
private theorem exists_nat_eq_ringKrullDim {R : Type u} [CommSemiring R]
    [FiniteRingKrullDim R] : ∃ n : ℕ, ringKrullDim R = n := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have htop : d ≠ ⊤ := fun h => ringKrullDim_ne_top (R := R) (hd ▸ by simp [h])
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  exact ⟨n, by rw [← hd, ← hn]; simp⟩

/-- A specialization between two points of an affine open gives an inclusion between the
corresponding primes of its ring of sections. -/
private theorem IsAffineOpen.primeIdealOf_le_of_specializes {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (h : x ⤳ y) :
    hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨y, hy⟩ :=
  (PrimeSpectrum.le_iff_specializes _ _).2
    (hU.isoSpec.hom.base.hom.map_specializes ((subtype_specializes_iff ⟨x, hx⟩ ⟨y, hy⟩).2 h))

/-- An immediate specialization between two points of an affine open gives a covering relation
between the corresponding primes of its ring of sections. -/
private theorem IsAffineOpen.primeIdealOf_covBy_of_isImmediateSpecialization {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : IsImmediateSpecialization x y) :
    hU.primeIdealOf ⟨x, hx⟩ ⋖ hU.primeIdealOf ⟨y, hy⟩ := by
  have hxQ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hyP : hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) = y := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have hsp : ∀ {A B : PrimeSpectrum Γ(X, U)}, A ≤ B → hU.fromSpec A ⤳ hU.fromSpec B := fun hAB =>
    hU.fromSpec.base.hom.map_specializes ((PrimeSpectrum.le_iff_specializes _ _).mp hAB)
  let : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hinj : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
  refine ⟨lt_of_le_of_ne (hU.primeIdealOf_le_of_specializes hx hy h.1) fun heq =>
    h.2.1 (by rw [← hxQ, ← hyP, heq]), fun Z hQZ hZP => ?_⟩
  rcases h.2.2 _ (hxQ ▸ hsp hQZ.le) (hyP ▸ hsp hZP.le) with heq | heq
  · exact (ne_of_lt hQZ) (hinj (heq.trans hxQ.symm)).symm
  · exact (ne_of_lt hZP) (hinj (heq.trans hyP.symm))

/-- The local dimension formula at a specialization on a Cohen--Macaulay scheme. For `x ⤳ y`
there is a prime `𝔭` of the local ring at `y` — the one cut out by `x` in an affine
neighbourhood of `y` — with `dim 𝒪_y = height 𝔭 + dim (𝒪_y / 𝔭)` and `dim 𝒪_x = height 𝔭`.
The prime is proper for a nontrivial specialization, and covered by the maximal ideal for an
immediate one. -/
private theorem stalk_dimension_formula_of_specializes {S : Scheme.{u}} (hS : IsCohenMacaulay S)
    {x y : S} (hxy : x ⤳ y) :
    ∃ p : Ideal (S.presheaf.stalk y), p.IsPrime ∧
      (x ≠ y → p ≠ IsLocalRing.maximalIdeal (S.presheaf.stalk y)) ∧
      ringKrullDim (S.presheaf.stalk y) = p.height + ringKrullDim (S.presheaf.stalk y ⧸ p) ∧
      ringKrullDim (S.presheaf.stalk x) = p.height ∧
      (∀ (hp : p.IsPrime) (_ : IsImmediateSpecialization x y),
        (⟨p, hp⟩ : PrimeSpectrum (S.presheaf.stalk y)) ⋖ ⊤) := by
  classical
  obtain ⟨U, hyU, _, _⟩ := hS.exists_affineOpen y
  have hxU : x ∈ U.val := hxy.mem_open U.val.2 hyU
  let xU : U.val := ⟨x, hxU⟩
  let yU : U.val := ⟨y, hyU⟩
  let Q : PrimeSpectrum Γ(S, U.val) := U.2.primeIdealOf xU
  let P : PrimeSpectrum Γ(S, U.val) := U.2.primeIdealOf yU
  have hQP : Q.asIdeal ≤ P.asIdeal := U.2.primeIdealOf_le_of_specializes hxU hyU hxy
  obtain ⟨_, hCM⟩ := ((isCohenMacaulay_tfae_stalk S).out 1 2 rfl rfl).mp hS
  obtain ⟨hN, hCMloc⟩ := hCM y
  let R := S.presheaf.stalk y
  let : IsNoetherianRing R := hN
  let : Algebra Γ(S, U.val) R := S.presheaf.algebra_section_stalk yU
  let : IsLocalization.AtPrime R P.asIdeal := U.2.isLocalization_stalk yU
  let Q' : Ideal R := Q.asIdeal.map (algebraMap Γ(S, U.val) R)
  have hQ' : Q'.IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P.asIdeal (p := Q.asIdeal) hQP
  have hdisj : Disjoint (P.asIdeal.primeCompl : Set Γ(S, U.val)) Q.asIdeal := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hQP]
  have hheight := IsLocalization.height_map_of_disjoint
    (R := Γ(S, U.val)) (S := R) P.asIdeal.primeCompl Q.asIdeal hdisj
  let : Algebra Γ(S, U.val) (S.presheaf.stalk x) := S.presheaf.algebra_section_stalk xU
  let : IsLocalization.AtPrime (S.presheaf.stalk x) Q.asIdeal := U.2.isLocalization_stalk xU
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P.asIdeal
  have hformula := ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay R).mp
    hCMloc).ringKrullDim_eq_height_add_ringKrullDim_quotient Q'
  have hunderQ : Q'.under Γ(S, U.val) = Q.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime P.asIdeal (p := Q.asIdeal) hQP
  have hunderP : (IsLocalRing.maximalIdeal R).under Γ(S, U.val) = P.asIdeal :=
    IsLocalization.AtPrime.under_maximalIdeal R P.asIdeal
  have hQ'ne : x ≠ y → Q' ≠ IsLocalRing.maximalIdeal R := by
    intro hne heq
    have hh : U.2.fromSpec Q = U.2.fromSpec P := congrArg U.2.fromSpec (PrimeSpectrum.ext
      (hunderQ.symm.trans ((congrArg (fun I : Ideal R => I.under Γ(S, U.val)) heq).trans hunderP)))
    exact hne ((U.2.fromSpec_primeIdealOf xU).symm.trans (hh.trans (U.2.fromSpec_primeIdealOf yU)))
  refine ⟨Q', hQ', hQ'ne, by simpa [R] using hformula,
    by rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal (S.presheaf.stalk x),
      ← hheight], fun hp h => ?_⟩
  refine (apply_covBy_apply_iff (IsLocalization.AtPrime.primeSpectrumOrderIso R P.asIdeal)).mp ?_
  rw [show IsLocalization.AtPrime.primeSpectrumOrderIso R P.asIdeal ⟨Q', hp⟩ =
      ⟨Q, hQP⟩ from Subtype.ext (PrimeSpectrum.ext hunderQ),
    show IsLocalization.AtPrime.primeSpectrumOrderIso R P.asIdeal ⊤ =
        ⟨P, Set.mem_Iic.mpr le_rfl⟩ from
      Subtype.ext (PrimeSpectrum.ext hunderP)]
  exact covBy_top_iff.2 (Set.Iic.isCoatom_iff.2
    (U.2.primeIdealOf_covBy_of_isImmediateSpecialization hxU hyU h))

/-- Along a specialization `x ⤳ y` on a Cohen--Macaulay scheme, given the local dimension
formula at a prime `𝔭` of the local ring at `y`, the negative local-ring dimension at `x` exceeds
the one at `y` by the dimension of `𝒪_y / 𝔭`. -/
private theorem negativeLocalRingDimension_eq_add_of_dimension_formula {S : Scheme.{u}}
    (hS : IsCohenMacaulay S) {x y : S} (p : Ideal (S.presheaf.stalk y)) [p.IsPrime]
    (hformula : ringKrullDim (S.presheaf.stalk y) =
      p.height + ringKrullDim (S.presheaf.stalk y ⧸ p))
    (hdimx : ringKrullDim (S.presheaf.stalk x) = p.height) :
    ∃ nq : ℕ, ringKrullDim (S.presheaf.stalk y ⧸ p) = nq ∧
      negativeLocalRingDimension S x = negativeLocalRingDimension S y + nq := by
  have := hS.isNoetherianRing_stalk x
  have := hS.isNoetherianRing_stalk y
  have : IsLocalRing (S.presheaf.stalk y ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨nx, hnx⟩ := exists_nat_eq_ringKrullDim (R := S.presheaf.stalk x)
  obtain ⟨ny, hny⟩ := exists_nat_eq_ringKrullDim (R := S.presheaf.stalk y)
  obtain ⟨nq, hnq⟩ := exists_nat_eq_ringKrullDim (R := S.presheaf.stalk y ⧸ p)
  rw [hny, ← hdimx, hnx, hnq] at hformula
  have hsum : ny = nx + nq := by exact_mod_cast hformula
  refine ⟨nq, hnq, ?_⟩
  simp [negativeLocalRingDimension, hnx, hny]
  omega

/-- **Stacks Project, Tag 0F91.** On a Cohen--Macaulay scheme the negative of the dimension of
the local ring is a dimension function: it strictly increases along a nontrivial generization,
and drops by exactly one along an immediate specialization. -/
@[stacks 0F91 "the dimension function", sga "6 X 1.5" "CM S, (1.5.1) on S"]
theorem IsCohenMacaulay.negativeLocalRingDimension_isDimensionFunction {S : Scheme.{u}}
    (hS : IsCohenMacaulay S) :
    ∃ d : DimensionFunction S, ∀ s : S, d s = negativeLocalRingDimension S s := by
  refine (TopologicalSpace.exists_dimensionFunction_iff (negativeLocalRingDimension S)).2
    ⟨fun x y hxy hne => ?_, fun x y hxy => ?_⟩
  · obtain ⟨p, hp, hpne, hformula, hdimx, _⟩ := stalk_dimension_formula_of_specializes hS hxy
    obtain ⟨nq, hnq, hδ⟩ :=
      negativeLocalRingDimension_eq_add_of_dimension_formula hS p hformula hdimx
    have hpSpecTop : (⟨p, hp⟩ : PrimeSpectrum (S.presheaf.stalk y)) < ⊤ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      exact lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) (hpne hne)
    have hqpos : 0 < ringKrullDim (S.presheaf.stalk y ⧸ p) := by
      rw [← coheight_eq_ringKrullDim_quotient (⟨p, hp⟩ : PrimeSpectrum (S.presheaf.stalk y))]
      exact_mod_cast Order.coheight_pos_of_lt_top hpSpecTop
    rw [hnq] at hqpos
    have hnqpos : 0 < nq := by exact_mod_cast hqpos
    omega
  · obtain ⟨p, hp, _, hformula, hdimx, hcover⟩ :=
      stalk_dimension_formula_of_specializes hS hxy.1
    obtain ⟨nq, hnq, hδ⟩ :=
      negativeLocalRingDimension_eq_add_of_dimension_formula hS p hformula hdimx
    have := hS.isNoetherianRing_stalk y
    have hq := ringKrullDim_quotient_eq_one_of_covBy_top hp (hcover hp hxy)
    rw [hnq] at hq
    have hnq' : nq = 1 := by exact_mod_cast hq
    omega

end AlgebraicGeometry
