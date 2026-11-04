module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceLocalRing
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.CohenMacaulayRegular
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FinitenessLocalCohomology.DepthDimAdicCompletion
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Serre.Defs
import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactSequences
import StacksFrontier.RingTheory.Depth.RingEquiv
import StacksFrontier.RingTheory.Equidimensional.FlatLocal
import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectednessHenselian
import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectednessHenselian

/-!
# The `(2, 3)`-inequalities for a formal module free off the adic locus

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume

1. `A` is local with maximal ideal `𝔞 = 𝔪`,
2. `A` has a dualizing complex,
3. `cd(A, I) = 1`,
4. for `y ∈ U ∩ Y` the module `ℱ_y^∧` is finite locally free outside `V(I𝒪_{X,y}^∧)`, and
5. one of the two conditions
   * (a) `X \ Y` is `(S₂)` and every irreducible component of `X` not contained in `Y` has
     dimension `≥ 4`, or
   * (b) for every prime `𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) ≠ {𝔪}` one has
     `depth(A_𝔭) + dim(A/𝔭) > 3`.

Then `(ℱ_n)` satisfies the `(2, 3)`-inequalities. This is Stacks 0EJB.

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_of_finiteLocallyFreeOutside`: under the
  assumptions above, `(ℱ_n)` satisfies the `(2, 3)`-inequalities.
* `Stacks.Algebraization.exists_depth_add_dim_le_completedStalkDepth_of_free`: at a prime `𝔭` of
  `𝒪_{X,y}^∧` where `(ℱ_y^∧)_𝔭` is free, its contraction `𝔓 ⊆ A` satisfies
  `depth(A_𝔓) + dim(A/𝔓) ≤ depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + dim(A/𝔮)`.
* `Stacks.Algebraization.distanceToZEqCoheight_of_isCatenary_quotient`: for `A` local with
  `𝔞 = 𝔪` and `A/I` catenary, `δ^Y_Z` is the coheight in `Spec(A/I)`.
* `Stacks.Algebraization.coheight_eq_ringKrullDim_quotient_underlyingPrime`: at `y ∈ U ∩ Y` this
  coheight is `dim(A/𝔮)`, for `𝔮` the prime under `y`.

## Implementation notes

Assumption (4) is stated as the freeness it is used through: at every `y ∈ U ∩ Y` and every prime
`𝔭` of `𝒪_{X,y}^∧` not containing `I𝒪_{X,y}^∧`, the localization of `ℱ_y^∧` at `𝔭` is a free
module. Finiteness of `ℱ_y^∧` over `𝒪_{X,y}^∧` is automatic from coherence of the adic system
(Stacks 0EJE) and is not assumed.

The `(S₂)` half of (5a) is `PropertySkRing (Localization.AtPrime 𝔭) 2` for every prime `𝔭` of `A`
not containing `I`, which is the Serre condition of Stacks 031P at the points of `X \ Y`; an
irreducible component of `X` not contained in `Y` is a minimal prime of `A` not containing `I`.
The set `V(𝔭) ∩ V(I)` of (5b) is written as an intersection of two subsets of `Spec(A)`.

The source writes `A_f` and `V(f)` in clause (5), but Situation 0EHC fixes no element `f`.
Clause (5) is read with `V(f) = V(I)` and "`A_f` is `(S₂)`" = "`X \ Y` is `(S₂)`".

## References

* [Stacks Project, Tag 0EJB](https://stacks.math.columbia.edu/tag/0EJB)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EKW](https://stacks.math.columbia.edu/tag/0EKW), cohomological
  dimension one.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth under completion.
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P), the Serre conditions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open IrreducibleClosedsCodim

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Depth along a linear equivalence and of a free module -/

/-- The localization of a ring at a prime, as a module, has the depth of that local ring. -/
private lemma depth_localizedRing_eq {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl R) =
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) :=
  Module.depth_eq_depth_of_linearEquiv _ ((LocalizedModule.equivTensorProduct p.primeCompl R).trans
    (Algebra.TensorProduct.rid R _ (Localization.AtPrime p)).toLinearEquiv)

/-! ### The Serre condition `(S₂)` and the depth of a local ring -/

/-- A local ring is its own localization at its maximal ideal. -/
private def atMaxEquiv (R : Type*) [CommRing R] [IsLocalRing R] :
    Localization.AtPrime (maximalIdeal R) ≃+* R := by
  have hM : (maximalIdeal R).primeCompl ≤ IsUnit.submonoid R := fun _ hx =>
    notMem_maximalIdeal.mp hx
  let _ : IsLocalization (maximalIdeal R).primeCompl R := IsLocalization.self hM
  exact (IsLocalization.algEquiv (maximalIdeal R).primeCompl
    (Localization.AtPrime (maximalIdeal R)) R).toRingEquiv

/-- A Noetherian local ring with property `(S₂)` has depth at least `min(2, dim)`. -/
private lemma depth_ge_min_two_dimension_of_propertySkRing
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : PropertySkRing R 2) :
    min (2 : ℕ∞) ((ringKrullDim R).unbotD 0) ≤
      Module.depth R (maximalIdeal R) R := by
  have hm := h (maximalIdeal R)
  let e := atMaxEquiv R
  have hdim : ringKrullDim (Localization.AtPrime (maximalIdeal R)) =
      ringKrullDim R := ringKrullDim_eq_of_ringEquiv e
  have hdepth : ringDepth (Localization.AtPrime (maximalIdeal R)) =
      Module.depth R (maximalIdeal R) R := by
    rw [ringDepth_eq_depth_maximalIdeal]
    exact Module.depth_self_eq_of_ringEquiv e
  simpa only [hdim, hdepth, Nat.cast_ofNat] using hm

/-! ### Transport along the identification of the stalk with a localization -/

/-- The identification of the stalk with a localization is compatible with the maps from `A`. -/
private alias pointStalkRingEquiv_comp_base := pointStalkRingEquiv_comp_baseToPointStalk

/-- A localization of a ring identified with a localization of `A` at a prime is a localization
of `A` at the contracted prime. -/
private def localRingEquivOfLocalizationRingEquiv
    {A : Type*} {T : Type*} [CommRing A] [CommRing T]
    (q : Ideal A) [q.IsPrime]
    (e : T ≃+* Localization.AtPrime q)
    (f : A →+* T)
    (hf : e.toRingHom.comp f = algebraMap A (Localization.AtPrime q))
    (p : Ideal T) [p.IsPrime] :
    Localization.AtPrime (p.comap f) ≃+* Localization.AtPrime p := by
  let _ : Algebra A T := f.toAlgebra
  let eAlg : Localization.AtPrime q ≃ₐ[A] T :=
    { e.symm with
      commutes' := fun a => e.symm_apply_eq.mpr (RingHom.congr_fun hf a).symm }
  have _ : IsLocalization q.primeCompl T :=
    IsLocalization.isLocalization_of_algEquiv q.primeCompl eAlg
  have _ : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap f) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := q.primeCompl) (Localization.AtPrime p) p
  exact (IsLocalization.algEquiv (p.comap f).primeCompl
    (Localization.AtPrime (p.comap f)) (Localization.AtPrime p)).toRingEquiv

/-- The quotient of a ring identified with a localization of `A` at a prime, by a prime, is the
quotient of that localization by the extension of the contracted prime. -/
private def quotientRingEquivOfLocalizationRingEquiv
    {A : Type*} {T : Type*} [CommRing A] [CommRing T]
    (q : Ideal A) [q.IsPrime]
    (e : T ≃+* Localization.AtPrime q)
    (f : A →+* T)
    (hf : e.toRingHom.comp f = algebraMap A (Localization.AtPrime q))
    (p : Ideal T) :
    T ⧸ p ≃+* Localization.AtPrime q ⧸
      (p.comap f).map (algebraMap A (Localization.AtPrime q)) := by
  let Q : Ideal (Localization.AtPrime q) := p.map e.toRingHom
  have hQcomap : Q.comap (algebraMap A (Localization.AtPrime q)) = p.comap f := by
    rw [← hf]
    change (Q.comap e.toRingHom).comap f = _
    rw [show Q.comap e.toRingHom = p from
      p.comap_map_of_bijective e.toRingHom e.bijective]
  have hQmap : (p.comap f).map (algebraMap A (Localization.AtPrime q)) = Q := by
    rw [← hQcomap]
    exact IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q
  exact Ideal.quotientEquiv p _ e hQmap

/-! ### Dualizing complexes and completions of the stalk -/

/-- A dualizing complex stays dualizing after transport along a ring isomorphism. -/
private theorem isDualizingComplexOfRingEquiv
    {R : Type u} {T : Type u} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T]
    (e : R ≃+* T) (K : DerivedCategory (ModuleCat.{u} R))
    (hK : Dualizing.IsDualizingComplex K) :
    Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars e.toRingHom).obj K) := by
  let _ : Algebra R T := e.toRingHom.toAlgebra
  let M₀ : Submonoid T := IsUnit.submonoid T
  have _ : IsLocalization M₀ T := inferInstance
  let M : Submonoid R := M₀.map e.symm.toRingHom
  have _ : IsLocalization M T := IsLocalization.isLocalization_of_base_ringEquiv M₀ T e.symm
  exact Dualizing.isDualizingComplex_localization M K hK

/-! ### Dimension bookkeeping -/

/-- Localizing a quotient at the image of the maximal ideal does not change its dimension. -/
private theorem ringKrullDimLocalizationAtQuotientMaximal
    {A : Type*} [CommRing A] [IsLocalRing A]
    (P : Ideal A) [P.IsPrime]
    [((maximalIdeal A).map (Ideal.Quotient.mk P)).IsPrime] :
    ringKrullDim
        (Localization.AtPrime ((maximalIdeal A).map (Ideal.Quotient.mk P))) =
      ringKrullDim (A ⧸ P) := by
  have _ : Nontrivial (A ⧸ P) :=
    Ideal.Quotient.nontrivial_iff.mpr (inferInstance : P.IsPrime).ne_top
  have _ : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal A).map (Ideal.Quotient.mk P) = maximalIdeal (A ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective
  let e : Localization.AtPrime ((maximalIdeal A).map (Ideal.Quotient.mk P)) ≃+*
      Localization.AtPrime (maximalIdeal (A ⧸ P)) :=
    Localization.localRingEquiv
      ((maximalIdeal A).map (Ideal.Quotient.mk P)) (maximalIdeal (A ⧸ P))
      (RingEquiv.refl (A ⧸ P)) hmax
  calc
    ringKrullDim (Localization.AtPrime ((maximalIdeal A).map (Ideal.Quotient.mk P))) =
        ringKrullDim (Localization.AtPrime (maximalIdeal (A ⧸ P))) :=
      ringKrullDim_eq_of_ringEquiv e
    _ = ringKrullDim (A ⧸ P) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height
        (maximalIdeal (A ⧸ P)) (Localization.AtPrime (maximalIdeal (A ⧸ P)))]
      exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- Equal primes have localizations of equal dimension. -/
private lemma ringKrullDimLocalizationAtPrimeCongr
    {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (h : p = q) :
    ringKrullDim (Localization.AtPrime p) =
      ringKrullDim (Localization.AtPrime q) :=
  ringKrullDim_eq_of_ringEquiv
    (Localization.localRingEquiv p q (RingEquiv.refl R) h)

/-- A strict chain `𝔭 < 𝔮 < 𝔪` of primes forces `dim(A/𝔭) ≥ 2`. -/
private lemma twoLeQuotientDimensionOfStrictChain
    {A : Type*} [CommRing A]
    (p q m : PrimeSpectrum A) (hpq : p < q) (hqm : q < m) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) := by
  have hq : (1 : ℕ∞) ≤ Order.coheight q := by
    calc
      (1 : ℕ∞) = 0 + 1 := by norm_num
      _ ≤ Order.coheight m + 1 := by simp
      _ ≤ Order.coheight q := Order.coheight_add_one_le hqm
  have hp : (2 : ℕ∞) ≤ Order.coheight p := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight q + 1 := by
        simpa [add_comm] using add_le_add_right hq 1
      _ ≤ Order.coheight p := Order.coheight_add_one_le hpq
  rw [← coheight_eq_ringKrullDim_quotient p]
  exact WithBot.coe_le_coe.mpr hp

/-- From `min(2, a) ≤ d`, `2 ≤ b` and `4 ≤ a + b` one gets `3 < d + b`. -/
private lemma strictThreeOfMinDepthAndDimension
    (a d : ℕ∞) (b : WithBot ℕ∞)
    (hd : min (2 : ℕ∞) a ≤ d)
    (hb : (2 : WithBot ℕ∞) ≤ b)
    (hfour : (4 : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + b) :
    (3 : WithBot ℕ∞) < (d : WithBot ℕ∞) + b := by
  have h34 : (3 : WithBot ℕ∞) < 4 := by norm_num
  rcases lt_or_ge a 2 with ha | ha
  · have hda : a ≤ d := by simpa [min_eq_right (le_of_lt ha)] using hd
    have hmono : (a : WithBot ℕ∞) + b ≤ (d : WithBot ℕ∞) + b := by
      simpa [add_comm] using add_le_add_right (WithBot.coe_le_coe.mpr hda) b
    exact h34.trans_le (hfour.trans hmono)
  · have h2d : (2 : ℕ∞) ≤ d := by simpa [min_eq_left ha] using hd
    have h4db : (4 : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) + b := by
      calc
        (4 : WithBot ℕ∞) = 2 + 2 := by norm_num
        _ ≤ (d : WithBot ℕ∞) + b :=
          add_le_add (WithBot.coe_le_coe.mpr h2d) hb
    exact h34.trans_le h4db

/-- The strict inequality `3 < d + c + e` transported from `WithBot ℕ∞` to the extended
integers. -/
private lemma strictThreeEIntOfWithBot
    (d e : ℕ∞) (c : WithBot ℕ∞)
    (h : (3 : WithBot ℕ∞) <
      (d : WithBot ℕ∞) + c + (e : WithBot ℕ∞)) :
    ((3 : ℤ) : EInt) < enatToEInt d + krullDimToEInt c + enatToEInt e := by
  cases d with
  | top =>
    cases c with
    | bot => simp at h
    | coe c =>
      cases c with
      | top =>
        cases e <;> change ((3 : ℤ) : EInt) < ⊤ <;>
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
      | coe n =>
        cases e <;> change ((3 : ℤ) : EInt) < ⊤ <;>
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  | coe d =>
    cases c with
    | bot => simp at h
    | coe c =>
      cases c with
      | top =>
        cases e <;> change ((3 : ℤ) : EInt) < ⊤ <;>
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
      | coe n =>
        cases e with
        | top =>
          change ((3 : ℤ) : EInt) < ⊤
          exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
        | coe e =>
          have hnat : 3 < d + n + e := by
            have henat : (3 : ℕ∞) <
                (d : ℕ∞) + (n : ℕ∞) + (e : ℕ∞) := by
              simp only [← WithBot.coe_add] at h
              exact WithBot.coe_lt_coe.mp h
            exact_mod_cast henat
          change ((3 : ℤ) : EInt) < (((d + n + e : ℕ) : ℤ) : EInt)
          exact WithBotTop.coe_lt_coe.mpr (by exact_mod_cast hnat)

/-! ### Catenarity and the additivity of dimensions -/

/-- The two spellings of universal catenarity agree on a Noetherian ring. -/
private theorem universallyCatenaryOfRingUniversallyCatenary
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (h : Ring.IsUniversallyCatenary A) : IsUniversallyCatenary A := by
  intro C _ _ hC
  let _ : Algebra.FiniteType A C := hC
  exact AlgebraicGeometry.catenarySpace_of_order
    ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum C).mp
      (AlgebraicGeometry.catenaryOrder_of_ringIsCatenary (h C)))

/-- The two spellings of universal catenarity agree on a Noetherian ring. -/
public alias universallyCatenaryOfRingUniversallyCatenary' :=
  universallyCatenaryOfRingUniversallyCatenary

/-- A quotient of a localization at a prime is a localization of the quotient, at the image of
that prime. -/
private theorem isLocalizationAtPrimeQuotient {B : Type*} [CommRing B]
    (n : Ideal B) [n.IsPrime] (Bq : Type*) [CommRing Bq] [Algebra B Bq]
    [IsLocalization.AtPrime Bq n] (J : Ideal B) (qbar : Ideal (B ⧸ J))
    [qbar.IsPrime] (hqbar : qbar.comap (Ideal.Quotient.mk J) = n) :
    IsLocalization.AtPrime (Bq ⧸ J.map (algebraMap B Bq)) qbar := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ J) n.primeCompl = qbar.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      subst hqbar
      intro hmem
      refine hz ?_
      have hzz : Ideal.Quotient.mk J z = Ideal.Quotient.mk J y := by
        simpa [Ideal.Quotient.algebraMap_eq] using hzy
      simpa [Ideal.mem_comap, hzz] using hmem
    · intro hx
      exact ⟨y, by subst hqbar; exact hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (M := n.primeCompl) (S := Bq) J
  rwa [hsub] at h

/-- In a Noetherian universally catenary local ring, the dimension of `A/𝔓` splits along a prime
`𝔮 ≥ 𝔓` as the dimension of `A_𝔮/𝔓A_𝔮` plus the dimension of `A/𝔮`. -/
private theorem localQuotientDimAddGlobalQuotientDim
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcat : Ring.IsUniversallyCatenary A) (P q : Ideal A) [P.IsPrime] [q.IsPrime]
    (hPq : P ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ P.map (algebraMap A (Localization.AtPrime q))) +
      ringKrullDim (A ⧸ q) =
      ringKrullDim (A ⧸ P) := by
  classical
  let B := A ⧸ P
  let qbar : Ideal B := q.map (Ideal.Quotient.mk P)
  have hqbarPrime : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPq
  let _ : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr ‹P.IsPrime›.ne_top
  let _ : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective
  have hqbarMax : qbar ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hqbarPrime.ne_top
  have hcatB : Ring.IsUniversallyCatenary B :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hcat
  have hcatBLegacy : IsUniversallyCatenary B :=
    universallyCatenaryOfRingUniversallyCatenary hcatB
  have hsum := catenary_height_add hcatBLegacy qbar (maximalIdeal B) hqbarMax
  have _ : Nontrivial (B ⧸ qbar) :=
    Ideal.Quotient.nontrivial_iff.mpr hqbarPrime.ne_top
  have _ : IsLocalRing (B ⧸ qbar) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk qbar) Ideal.Quotient.mk_surjective
  have hdimqbar :
      ((Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal B)).height : WithBot ℕ∞) =
      ringKrullDim (A ⧸ q) := by
    calc
      ((Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal B)).height : WithBot ℕ∞) =
          ringKrullDim (B ⧸ qbar) := by
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B ⧸ qbar),
          IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk qbar)
            Ideal.Quotient.mk_surjective]
      _ = ringKrullDim (A ⧸ q) :=
        ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPq)
  have hdimGlobal : ringKrullDim B =
      (qbar.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q) := by
    calc
      ringKrullDim B = ((maximalIdeal B).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
      _ = ((qbar.height +
            (Ideal.map (Ideal.Quotient.mk qbar) (maximalIdeal B)).height : ℕ∞) :
              WithBot ℕ∞) :=
        congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hsum
      _ = (qbar.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q) := by
        rw [WithBot.coe_add, hdimqbar]
  have hqbarComap : qbar.comap (Ideal.Quotient.mk P) = q := Ideal.comap_map_mk hPq
  let _ : IsLocalization.AtPrime
      (Localization.AtPrime q ⧸ P.map (algebraMap A (Localization.AtPrime q))) qbar :=
    isLocalizationAtPrimeQuotient q (Localization.AtPrime q) P qbar hqbarComap
  have hdimLocal :
      ringKrullDim (Localization.AtPrime q ⧸
          P.map (algebraMap A (Localization.AtPrime q))) =
        (qbar.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height qbar _
  rw [hdimGlobal, hdimLocal]

/-! ### The distance to `Z` in the local situation -/

/-- A quotient of a universally catenary ring is catenary. -/
private theorem isCatenary_quotient_of_isUniversallyCatenary {A : Type u} [CommRing A]
    (hcat : Ring.IsUniversallyCatenary A) (I : Ideal A) : Ring.IsCatenary (A ⧸ I) :=
  (Ring.IsUniversallyCatenary.of_surjective (Ideal.Quotient.mk_surjective (I := I)) hcat) (A ⧸ I)

/-- The prime under a point `y ∈ U ∩ Y` contains `I`. -/
private theorem le_underlyingPrime_of_base_eq
    (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) : S.I ≤ (underlyingPrime S y).asIdeal := by
  rw [show (underlyingPrime S y).asIdeal = z.asIdeal.comap (Ideal.Quotient.mk S.I) from
    congrArg PrimeSpectrum.asIdeal hyz, ← Ideal.map_le_iff_le_comap, Ideal.map_quotient_self]
  exact bot_le

/-- In a local algebraization situation with `𝔞 = 𝔪` the distance `δ^Y_Z` is the coheight of
the corresponding prime of `A/I`, as soon as `A/I` is catenary. -/
public theorem distanceToZEqCoheight_of_isCatenary_quotient
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (hmax : S.a = maximalIdeal S.A)
    (hcat : Ring.IsCatenary (S.A ⧸ S.I)) (z : S.Y) :
    (S.distanceToZ z : ℕ∞) =
      @Order.coheight (PrimeSpectrum (S.A ⧸ S.I))
        PrimeSpectrum.instPartialOrder.toPreorder z := by
  let B := S.A ⧸ S.I
  have hImax : S.I ≤ maximalIdeal S.A := S.I_le_a.trans hmax.le
  have hIne : S.I ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S.A).ne_top (top_le_iff.mp (h ▸ hImax))
  have _ : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIne
  have _ : IsLocalRing B := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk S.I) Ideal.Quotient.mk_surjective
  have hcatB : Ring.IsCatenary B := hcat
  have hZ : S.closedSubsetZ =
      (⟨{IsLocalRing.closedPoint B}, IsLocalRing.isClosed_singleton_closedPoint B⟩ :
        Closeds S.Y) := by
    apply Closeds.ext
    change PrimeSpectrum.zeroLocus (S.a.map (Ideal.Quotient.mk S.I) : Set B) =
      ({IsLocalRing.closedPoint B} : Set S.Y)
    rw [hmax, IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk S.I) Ideal.Quotient.mk_surjective]
    change PrimeSpectrum.zeroLocus (maximalIdeal B : Set B) =
      ({IsLocalRing.closedPoint B} : Set (PrimeSpectrum B))
    simpa only [IsLocalRing.closedPoint] using
      PrimeSpectrum.zeroLocus_eq_singleton (maximalIdeal B)
  change distanceFunction S.Y S.closedSubsetZ z = _
  rw [hZ]
  exact distanceFunction_closedPoint_eq_coheight B hcatB z

/-- In a local algebraization situation with `𝔞 = 𝔪` and `A` universally catenary the distance
`δ^Y_Z` is the coheight of the corresponding prime of `A/I`. -/
private theorem distanceToZEqCoheight
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (hmax : S.a = maximalIdeal S.A)
    (hcat : Ring.IsUniversallyCatenary S.A) (z : S.Y) :
    (S.distanceToZ z : ℕ∞) =
      @Order.coheight (PrimeSpectrum (S.A ⧸ S.I))
        PrimeSpectrum.instPartialOrder.toPreorder z := by
  exact distanceToZEqCoheight_of_isCatenary_quotient S hmax
    (isCatenary_quotient_of_isUniversallyCatenary hcat S.I) z

/-- The dimension of `(A/I)/𝔷` equals the dimension of `A/𝔮` for `𝔮` the prime under `y`. -/
private theorem quotientDimensionAtPoint
    (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    ringKrullDim ((S.A ⧸ S.I) ⧸ z.asIdeal) =
      ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) := by
  let q := underlyingPrime S y
  have hcomap : q.asIdeal = z.asIdeal.comap (Ideal.Quotient.mk S.I) :=
    congrArg PrimeSpectrum.asIdeal hyz
  have hIle : S.I ≤ q.asIdeal := le_underlyingPrime_of_base_eq S y z hyz
  have hmap : q.asIdeal.map (Ideal.Quotient.mk S.I) = z.asIdeal := by
    rw [hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [← hmap]
  exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIle)

/-- At a point `y ∈ U ∩ Y`, given by `y ∈ U` and `z ∈ Y` over the same point of `X`, the coheight
of `z` in `Spec(A/I)` is the dimension `dim(A/𝔮)` of the closure of the prime `𝔮` under `y`. -/
public theorem coheight_eq_ringKrullDim_quotient_underlyingPrime
    (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    ((@Order.coheight (PrimeSpectrum (S.A ⧸ S.I)) PrimeSpectrum.instPartialOrder.toPreorder z :
        ℕ∞) : WithBot ℕ∞) = ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) :=
  (coheight_eq_ringKrullDim_quotient (z : PrimeSpectrum (S.A ⧸ S.I))).trans
    (quotientDimensionAtPoint S y z hyz)

/-! ### Depth plus dimension of a free completed stalk, read at a prime of `A` -/

/-- **The depth bound of a free completed stalk, read on `A`.** Let `A` be a Noetherian local ring
with a dualizing complex, `y ∈ U ∩ Y` (a point `y` of `U` and a point `z` of `Y` over the same
point of `X`), with `𝔮 ⊂ A` the prime under `y`, and let `𝔭` be a prime of `𝒪_{X,y}^∧` not
containing `I𝒪_{X,y}^∧` at which `(ℱ_y^∧)_𝔭` is free. Then the contraction `𝔓 ⊂ A` of `𝔭`
satisfies `𝔓 ∉ V(I)`, `𝔓 ⊆ 𝔮` and

`depth(A_𝔓) + dim(A/𝔓) ≤ depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + dim(A/𝔮)`. -/
public theorem exists_depth_add_dim_le_completedStalkDepth_of_free
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hpJ : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal)
    (hfree : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y))) :
    ∃ P : PrimeSpectrum S.A, ¬ S.I ≤ P.asIdeal ∧ P ≤ underlyingPrime S y ∧
      (Module.depth (Localization.AtPrime P.asIdeal)
            (maximalIdeal (Localization.AtPrime P.asIdeal))
            (Localization.AtPrime P.asIdeal) : WithBot ℕ∞) + ringKrullDim (S.A ⧸ P.asIdeal) ≤
        ((completedStalkDepth (idealOnOpen S) F y p : WithBot ℕ∞) +
          ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
          ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) := by
  classical
  obtain ⟨K, hK⟩ := hdual
  have hcatA : Ring.IsUniversallyCatenary S.A :=
    Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
  have _ : IsNoetherian S.U.toScheme := by
    have _ : IsLocallyNoetherian S.U.toScheme :=
      isLocallyNoetherian_of_isOpenImmersion S.U.ι
    have _ : CompactSpace S.U :=
      isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (S.U : Set S.X))
    exact (isNoetherian_iff S.U.toScheme).2 ⟨inferInstance, inferInstance⟩
  have hI0max : IdealSheafData.stalk (idealOnOpen S) y ≤
      maximalIdeal (S.U.toScheme.presheaf.stalk y) := stalk_idealOnOpen_le_maximalIdeal S y z hyz
  have hlocRhat : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal _ hI0max
  let _ := hlocRhat
  let q := underlyingPrime S y
  let e := pointStalkRingEquiv S y
  have hdualT : ∃ KT : DerivedCategory (ModuleCat.{u} (S.U.toScheme.presheaf.stalk y)),
      Dualizing.IsDualizingComplex KT :=
    ⟨_, isDualizingComplexOfRingEquiv e.symm _
      (Dualizing.isDualizingComplex_localizationAtPrime.{u, u} K hK q)⟩
  let pT := p.asIdeal.comap
    (algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y))
  have _ : pT.IsPrime := Ideal.IsPrime.comap _
  have _ : p.asIdeal.LiesOver pT := ⟨rfl⟩
  have hmhatEq : (maximalIdeal (S.U.toScheme.presheaf.stalk y)).map
        (algebraMap (S.U.toScheme.presheaf.stalk y)
          (completedLocalRing (idealOnOpen S) y)) =
      maximalIdeal (completedLocalRing (idealOnOpen S) y) :=
    IsLocalRing.eq_maximalIdeal
      (AdicCompletion.isMaximal_map_of_le _ (maximalIdeal (S.U.toScheme.presheaf.stalk y))
        hI0max (Ideal.fg_of_isNoetherianRing _))
  have _ : Module.Finite (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) :=
    finite_completedStalk_of_isNoetherian (idealOnOpen S) F y
  have _ : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  have _ : Module.Finite (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y)) :=
    inferInstance
  have _ : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y)) :=
    hfree
  have hdepthFree :
      Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) ≤
        completedStalkDepth (idealOnOpen S) F y p :=
    AlgebraicGeometry.depth_le_depth_of_free _ _
  have hI0eq : IdealSheafData.stalk (idealOnOpen S) y = S.I.map (baseToPointStalk S y) :=
    stalk_idealOnOpen_eq_map S y
  let P : Ideal S.A := pT.comap (baseToPointStalk S y)
  have _ : P.IsPrime := Ideal.IsPrime.comap _
  have hI0notpT : ¬ IdealSheafData.stalk (idealOnOpen S) y ≤ pT := fun h =>
    hpJ (Ideal.map_le_iff_le_comap.2 h)
  have hPnot : ¬ S.I ≤ P := fun hIP =>
    hI0notpT (by rw [hI0eq, Ideal.map_le_iff_le_comap]; exact hIP)
  have hqcomap : q.asIdeal =
      (maximalIdeal (S.U.toScheme.presheaf.stalk y)).comap (baseToPointStalk S y) := by
    calc
      q.asIdeal = (maximalIdeal (Localization.AtPrime q.asIdeal)).comap
          (algebraMap S.A (Localization.AtPrime q.asIdeal)) :=
        (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal)).symm
      _ = ((maximalIdeal (Localization.AtPrime q.asIdeal)).comap e.toRingHom).comap
          (baseToPointStalk S y) := by
        rw [← pointStalkRingEquiv_comp_base S y]; rfl
      _ = (maximalIdeal (S.U.toScheme.presheaf.stalk y)).comap (baseToPointStalk S y) := by
        rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
        exact congrArg (fun J : Ideal (S.U.toScheme.presheaf.stalk y) =>
          J.comap (baseToPointStalk S y))
          ((maximalIdeal (S.U.toScheme.presheaf.stalk y)).comap_map_of_bijective
            e.toRingHom e.bijective)
  have hPq : P ≤ q.asIdeal := by
    rw [hqcomap]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal (inferInstance : pT.IsPrime).ne_top)
  have hdepthP :
      Module.depth (Localization.AtPrime pT)
          (maximalIdeal (Localization.AtPrime pT)) (Localization.AtPrime pT) =
        Module.depth (Localization.AtPrime P)
          (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) :=
    (Module.depth_self_eq_of_ringEquiv
      (localRingEquivOfLocalizationRingEquiv q.asIdeal e (baseToPointStalk S y)
        (pointStalkRingEquiv_comp_base S y) pT)).symm
  have hdimQuot : ringKrullDim (S.U.toScheme.presheaf.stalk y ⧸ pT) =
      ringKrullDim (Localization.AtPrime q.asIdeal ⧸
        P.map (algebraMap S.A (Localization.AtPrime q.asIdeal))) :=
    ringKrullDim_eq_of_ringEquiv
      (quotientRingEquivOfLocalizationRingEquiv q.asIdeal e (baseToPointStalk S y)
        (pointStalkRingEquiv_comp_base S y) pT)
  have hdimGlobal :
      ringKrullDim (S.U.toScheme.presheaf.stalk y ⧸ pT) +
          ringKrullDim (S.A ⧸ q.asIdeal) = ringKrullDim (S.A ⧸ P) := by
    rw [hdimQuot]
    exact localQuotientDimAddGlobalQuotientDim hcatA P q.asIdeal hPq
  have hsumStalk := Module.depth_add_ringKrullDim_quotient_adicCompletion
    (S.U.toScheme.presheaf.stalk y) hdualT
    (IdealSheafData.stalk (idealOnOpen S) y) hI0max
    (S.U.toScheme.presheaf.stalk y) pT p.asIdeal
  have hsumSimple :
      (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
          ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal) =
        (Module.depth (Localization.AtPrime P)
            (maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P) : WithBot ℕ∞) +
          ringKrullDim (S.U.toScheme.presheaf.stalk y ⧸ pT) := by
    rw [← hdepthP, ← depth_localizedRing_eq p.asIdeal, ← depth_localizedRing_eq pT]
    exact hsumStalk
  refine ⟨⟨P, inferInstance⟩, hPnot, hPq, ?_⟩
  calc (Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P) : WithBot ℕ∞) + ringKrullDim (S.A ⧸ P)
      = ((Module.depth (Localization.AtPrime P)
            (maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P) : WithBot ℕ∞) +
            ringKrullDim (S.U.toScheme.presheaf.stalk y ⧸ pT)) +
            ringKrullDim (S.A ⧸ q.asIdeal) := by
        rw [add_assoc, hdimGlobal]
    _ = ((Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
          ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
          ringKrullDim (S.A ⧸ q.asIdeal) := by rw [hsumSimple]
    _ ≤ _ :=
      add_le_add_left
        (add_le_add_left (WithBot.coe_le_coe.mpr hdepthFree)
          (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)))
        (ringKrullDim (S.A ⧸ q.asIdeal))


/-! ### Stacks 0EJB -/

/-- In Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`. Assume (1) `A` is local with
`𝔞 = 𝔪`, (2) `A` has a dualizing complex, (3) `cd(A, I) = 1`, (4) for `y ∈ U ∩ Y` the module
`ℱ_y^∧` is finite locally free outside `V(I𝒪_{X,y}^∧)`, and (5) either (a) `X \ Y` is `(S₂)` and
every irreducible component of `X` not contained in `Y` has dimension `≥ 4`, or (b) for every prime
`𝔭 ∉ V(I)` with `V(𝔭) ∩ V(I) ≠ {𝔪}` one has `depth(A_𝔭) + dim(A/𝔭) > 3`. Then `(ℱ_n)`
satisfies the `(2, 3)`-inequalities. -/
@[stacks 0EJB]
public theorem satisfiesDepthInequalities_of_finiteLocallyFreeOutside
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (hmax : S.a = maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hfree : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
        ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl (completedStalk (idealOnOpen S) F y)))
    (hcondition :
      ((∀ p : PrimeSpectrum S.A, ¬ S.I ≤ p.asIdeal →
          PropertySkRing (Localization.AtPrime p.asIdeal) 2) ∧
        (∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal →
          ¬ S.I ≤ p.asIdeal →
          (4 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ p.asIdeal))) ∨
      (∀ p : PrimeSpectrum S.A, ¬ S.I ≤ p.asIdeal →
        ({q : PrimeSpectrum S.A | p.asIdeal ≤ q.asIdeal} ∩
          {q : PrimeSpectrum S.A | S.I ≤ q.asIdeal}) ≠
          {⟨maximalIdeal S.A, (IsLocalRing.maximalIdeal.isMaximal S.A).isPrime⟩} →
        (3 : WithBot ℕ∞) <
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
            ringKrullDim (S.A ⧸ p.asIdeal))) :
    SatisfiesDepthInequalities S F 2 3 := by
  classical
  apply (satisfiesDepthInequalities_two_three_iff S F hcd).2
  intro y z hyz p hpJ
  obtain ⟨⟨P, _⟩, hPnot, hPq, hle⟩ :=
    exists_depth_add_dim_le_completedStalkDepth_of_free S hdual F y z hyz p hpJ
      (hfree y z hyz p hpJ)
  change P ≤ (underlyingPrime S y).asIdeal at hPq
  change ¬ S.I ≤ P at hPnot
  obtain ⟨K, hK⟩ := hdual
  have hcatA : Ring.IsUniversallyCatenary S.A :=
    Dualizing.isUniversallyCatenary_of_isDualizingComplex hK
  let q := underlyingPrime S y
  have hqI : S.I ≤ q.asIdeal := le_underlyingPrime_of_base_eq S y z hyz
  let m : PrimeSpectrum S.A :=
    ⟨maximalIdeal S.A, (IsLocalRing.maximalIdeal.isMaximal S.A).isPrime⟩
  have hqnota : ¬ S.a ≤ q.asIdeal := by
    have h := y.property
    change q ∉ PrimeSpectrum.zeroLocus (S.a : Set S.A) at h
    exact fun ha => h ((PrimeSpectrum.mem_zeroLocus q (S.a : Set S.A)).mpr ha)
  have hqne : q ≠ m := fun h => hqnota (by rw [hmax, h])
  have hsetne :
      ({r : PrimeSpectrum S.A | P ≤ r.asIdeal} ∩
        {r : PrimeSpectrum S.A | S.I ≤ r.asIdeal}) ≠ {m} := fun h =>
    hqne (Set.mem_singleton_iff.mp (h ▸ (⟨hPq, hqI⟩ :
      q ∈ ({r : PrimeSpectrum S.A | P ≤ r.asIdeal} ∩
        {r : PrimeSpectrum S.A | S.I ≤ r.asIdeal}))))
  let Ppoint : PrimeSpectrum S.A := ⟨P, inferInstance⟩
  have hPqStrict : Ppoint < q := by
    change P < q.asIdeal
    exact lt_of_le_of_ne hPq fun h => hPnot (h ▸ hqI)
  have hqmStrict : q < m := by
    change q.asIdeal < maximalIdeal S.A
    exact lt_of_le_of_ne
      (IsLocalRing.le_maximalIdeal (inferInstance : q.asIdeal.IsPrime).ne_top)
      fun h => hqne (PrimeSpectrum.ext h)
  have hdimTwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ P) :=
    twoLeQuotientDimensionOfStrictChain Ppoint q m hPqStrict hqmStrict
  have hglobal :
      (3 : WithBot ℕ∞) <
        (Module.depth (Localization.AtPrime P)
          (maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P) : WithBot ℕ∞) + ringKrullDim (S.A ⧸ P) := by
    rcases hcondition with ⟨hS2, hcomponents⟩ | hdirect
    · have hheight : ringKrullDim (Localization.AtPrime P) = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
      have hminDepth : min (2 : ℕ∞) P.height ≤
          Module.depth (Localization.AtPrime P)
            (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) := by
        simpa only [hheight, WithBot.unbotD_coe] using
          depth_ge_min_two_dimension_of_propertySkRing (Localization.AtPrime P)
            (hS2 Ppoint hPnot)
      obtain ⟨n, hnmin, hnP⟩ :=
        Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S.A)) (J := P) bot_le
      have hn : IsMinimalPrime n := hnmin
      have _ : n.IsPrime := hn.isPrime
      have hfour : (4 : WithBot ℕ∞) ≤
          ringKrullDim (Localization.AtPrime P) + ringKrullDim (S.A ⧸ P) := by
        calc
          (4 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ n) :=
            hcomponents ⟨n, inferInstance⟩ hn (fun h => hPnot (h.trans hnP))
          _ = ringKrullDim (Localization.AtPrime P ⧸
                n.map (algebraMap S.A (Localization.AtPrime P))) +
                ringKrullDim (S.A ⧸ P) :=
            (localQuotientDimAddGlobalQuotientDim hcatA n P hnP).symm
          _ ≤ ringKrullDim (Localization.AtPrime P) + ringKrullDim (S.A ⧸ P) :=
            add_le_add_left
              (ringKrullDim_quotient_le
                (n.map (algebraMap S.A (Localization.AtPrime P))))
              (ringKrullDim (S.A ⧸ P))
      exact strictThreeOfMinDepthAndDimension P.height
        (Module.depth (Localization.AtPrime P)
          (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
        (ringKrullDim (S.A ⧸ P)) hminDepth hdimTwo (by simpa only [hheight] using hfour)
    · exact hdirect Ppoint hPnot hsetne
  have hdistance : (S.distanceToZ z : WithBot ℕ∞) = ringKrullDim (S.A ⧸ q.asIdeal) := by
    rw [distanceToZEqCoheight_of_isCatenary_quotient S hmax
      (isCatenary_quotient_of_isUniversallyCatenary hcatA S.I) z]
    exact coheight_eq_ringKrullDim_quotient_underlyingPrime S y z hyz
  have hfinal :
      (3 : WithBot ℕ∞) <
        ((completedStalkDepth (idealOnOpen S) F y p : WithBot ℕ∞) +
          ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
          (S.distanceToZ z : WithBot ℕ∞) := by
    rw [hdistance]
    exact hglobal.trans_le hle
  exact strictThreeEIntOfWithBot (completedStalkDepth (idealOnOpen S) F y p)
    (S.distanceToZ z) (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal))
    hfinal

end Stacks.Algebraization

end
