module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ScaledPole
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitPolynomial
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitExtension
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ScaledPole

/-!
# Eliminating degree-prime ramification: weak-solution criteria

Weak unramifiedness of an Artin--Schreier layer with integral parameter, ramification index `p`
for a pole of order prime to `p`, weak solutions from field-factor ramification and from a
constant parameter, and integral closures of base changes of discrete valuation rings.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- **An Artin--Schreier layer whose parameter is integral in the base ring is weakly
unramified.**

`M = L(z)` with `z ^ p - z = ξ` and `ξ` the image of an element of `B`: the ramification case
analysis of `isGalois_and_ramification_cases_of_adjoin_root_artinSchreier` then leaves only the
trivial and the unramified alternative, and both have ramification index one.

Public because it is the second of the two steps the split-class solver composes; see
`Stacks.EppTheorem.SplitConstantClassSolvable` in `EppConstantNumeratorFamily.lean`. Nothing about
  it
changed when it stopped being private. -/
theorem isWeaklyUnramified_of_artinSchreier_parameter_integral
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : Algebra.adjoin L {z} = ⊤) (hξ : ∃ b : B, ξ = algebraMap B L b) :
    IsWeaklyUnramified B C := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨hfin, hgal, -, hA, -, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier B L M p hp ξ z hz
      hgen π hπ
  let := hfin
  let := hgal
  apply isWeaklyUnramified_of_ramificationIdx'_eq_one B C L M
  intro m hm
  let := hm
  rcases hA hξ with htriv | ⟨-, hunr⟩
  · let e : M ≃ₐ[L] L := (AlgEquiv.ofBijective (Algebra.ofId L M)
      ⟨(algebraMap L M).injective, htriv⟩).symm
    have hcomp : e.toRingHom.comp (algebraMap B M) = algebraMap B L := by
      ext b
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B L M]
      exact e.commutes (algebraMap B L b)
    have hsurj := algebraMap_integralClosure_surjective_of_embedding e.toRingHom e.injective hcomp
    let S := integralClosure B M
    let : IsDedekindDomain S := integralClosure.isDedekindDomain B L M
    let : Module.IsTorsionFree B M := Module.IsTorsionFree.trans L
    let : Module.IsTorsionFree B S := IsIntegralClosure.isTorsionFree B M
    rw [← ramificationIdx_eq_ramificationIdx'_maximalIdeal m]
    exact ramificationIdx_eq_one_of_surjective hsurj m
  · obtain ⟨_, he, -⟩ := hunr m hm
    exact he

/-- Adding a multiple of a power of a nonunit to a unit of a local ring gives a unit. -/
private theorem isUnit_add_pow_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : ¬IsUnit x) {a : R} (ha : IsUnit a) {n : ℕ} (hn : 0 < n) (c : R) :
    IsUnit (a + x ^ n * c) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  simpa only [map_add, map_mul, map_pow, (IsLocalRing.residue_eq_zero_iff x).mpr hx,
    zero_pow hn.ne', zero_mul, add_zero] using (IsLocalRing.residue_ne_zero_iff_isUnit a).mpr ha

/-- A local map of discrete valuation rings that is injective makes the target an extension. -/
private theorem isExtension_of_injective_of_under_eq {A B : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B))
    (hmax : (IsLocalRing.maximalIdeal B).under A = IsLocalRing.maximalIdeal A) :
    IsExtension A B where
  toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  toIsLocalHom := ((IsLocalRing.local_hom_TFAE _).out 5 1).mp hmax

private theorem ramificationIndex_eq_prime_of_artinSchreier_pole
    (B C L M : Type*) [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C] [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M] [IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (π : B) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hpn : ¬p ∣ n)
    (a b : B) (ha : IsUnit a)
    (hξ : ξ = (algebraMap B L π)⁻¹ ^ n * algebraMap B L a + algebraMap B L b) :
    ramificationIndex B C = p := by
  obtain ⟨hfin, hgal, -, -, hB, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier B L M p hp ξ z hz
      hgen π hπ
  let := hfin
  let := hgal
  have hab := isUnit_add_pow_mul_of_not_isUnit hπ.not_isUnit ha hn b
  have ht : algebraMap B L π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hπ.ne_zero
  have hξ' : ξ = (algebraMap B L π)⁻¹ ^ n * algebraMap B L (a + π ^ n * b) := by
    rw [hξ, map_add, map_mul, map_pow, inv_pow]
    field_simp [ht]
  obtain ⟨-, hind⟩ := hB n (a + π ^ n * b) hn hpn hab hξ'
  apply ramificationIndex_eq_of_ramificationIdx'_eq B C L M p
  intro m hm
  let := hm
  let : m.LiesOver (IsLocalRing.maximalIdeal B) :=
    ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) m)).symm⟩
  exact hind m hm inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem adjoin_range_eq_adjoin_singleton_of_adjoin_eq_top
    {K M E F : Type*} [CommRing K] [CommRing M] [CommRing E] [CommRing F]
    [Algebra K M] [Algebra K E] [Algebra K F] [Algebra M F] [IsScalarTower K M F]
    (ι : E →ₐ[K] F) (w : E) (hw : Algebra.adjoin K {w} = ⊤) :
    Algebra.adjoin M (Set.range ι) = Algebra.adjoin M {ι w} := by
  have h : Set.range ι = Algebra.adjoin K {ι w} := by
    rw [← AlgHom.coe_range, ← Algebra.map_top, ← hw, AlgHom.map_adjoin, Set.image_singleton]
  rw [h, Algebra.adjoin_adjoin_of_tower]


set_option maxHeartbeats 2000000 in
-- The base-change, Artin--Schreier and Laurent-expansion constructions assembled here
-- elaborate far more terms than the default budget allows.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A weak solution from a ramification statement at every field factor.**

Reduces `∃ D : IntegralClosureBaseChange A C K M E, D.IsWeakSolution` to: for every localization
`Q` of `integralClosure C ((M ⊗[K] E) ⧸ nilradical)` at a maximal ideal, with fraction field `F`
and the structure map `ι : E →ₐ[K] F` making the base square commute and generating `F` over `M`,
the ramification index of `Q`'s maximal ideal over `integralClosure A E` is one.

This is the entry point every constant-numerator solver in this development uses, and it is what
carries the universe reconciliation: the factors land in `Type (max uM uK)`, which is where the
package's `L₁` and `B₁` live.

Public because `Stacks.EppTheorem.SplitConstantClassSolvable`'s discharge needs it at the middle
  layer
`(B, C, L, M, E)` as well as at `(A, C, K, M, E)`, where
`isWeakSolution_of_constant_artinSchreier_parameter` already used it. Nothing about it changed when
it stopped being private. -/
theorem exists_isWeakSolution_of_fieldFactor_ramification
    (A : Type uA) (C : Type uC) (K : Type uK) (M : Type uM) (E : Type uK)
    [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Field K] [Field M] [Field E]
    [Algebra A C] [IsExtension A C]
    [Algebra A K] [Algebra C M] [Algebra A M] [Algebra K M]
    [IsFractionRing A K] [IsFractionRing C M]
    [IsScalarTower A C M] [IsScalarTower A K M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    (hlocal : ∀ (Q F : Type (max uM uK))
      [CommRing Q] [IsDomain Q] [IsDiscreteValuationRing Q] [Field F]
      [Algebra C Q] [IsExtension C Q]
      [Algebra Q F] [IsFractionRing Q F] [Algebra C F] [IsScalarTower C Q F]
      [Algebra M F] [IsScalarTower C M F] [Module.Finite M F]
      [Algebra K F] [IsScalarTower K M F]
      [Algebra (integralClosure A E) Q] [Algebra A Q]
      [IsScalarTower A C Q] [IsScalarTower A (integralClosure A E) Q]
      (ι : E →ₐ[K] F),
      (∀ a : integralClosure A E,
        algebraMap Q F (algebraMap (integralClosure A E) Q a) = ι (a : E)) →
      Algebra.adjoin M (Set.range ι) = ⊤ →
      (IsLocalRing.maximalIdeal Q).ramificationIdx (integralClosure A E) = 1) :
    ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
        max uM uK, uK, max uM uK} A C K M E, D.IsWeakSolution := by
  classical
  let T := M ⊗[K] E
  let R := T ⧸ nilradical T
  let S := integralClosure C R
  let A₁ := integralClosure A E
  let D := integralClosureBaseChangeOfFinite A C K M E
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower K E R := D.isScalarTowerKK₁L₁
  let : Algebra A S := ((algebraMap C S).comp (algebraMap A C)).toAlgebra
  let : Algebra A₁ S := D.algebraA₁B₁
  let : IsScalarTower A C S := D.isScalarTowerABB₁
  let : IsScalarTower A A₁ S := D.isScalarTowerAA₁B₁
  have hem := integralClosures_after_finite_fraction_field_extension
    A C K M E R A₁ S (AlgEquiv.refl) (AlgEquiv.refl) (AlgEquiv.refl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun x => by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    (fun _ => rfl)
  rcases hem with ⟨hfields, -, -, -, -, -, -, -, -, hloc, -, -, -, -, -, hsep, -, -⟩
  obtain ⟨-, -, -, hfinite⟩ := hsep inferInstance
  let : Module.Finite C S := hfinite
  let : Module.Finite M R := by
    change Module.Finite M ((M ⊗[K] E) ⧸ nilradical (M ⊗[K] E))
    infer_instance
  refine ⟨D, ?_⟩
  change ∀ (q : Ideal S), q.IsMaximal → q.ramificationIdx A₁ = 1
  intro q hq
  let := hq
  obtain ⟨-, _, _, -, hdvr, -⟩ := hloc q hq
  obtain ⟨hdom, hv⟩ := hdvr
  let Q := Localization.AtPrime q
  let : IsDomain Q := hdom
  let : IsDiscreteValuationRing Q := hv
  have hCQ : Function.Injective (algebraMap C Q) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    by_contra hx0
    rw [IsScalarTower.algebraMap_apply C S Q] at hx
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl Q _).mp hx
    have hu : IsUnit (algebraMap C R x) := by
      rw [IsScalarTower.algebraMap_apply C M R]
      apply IsUnit.map
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_zero] using (IsFractionRing.injective C M).ne hx0
    have hs0 : (s : S) = 0 := by
      apply Subtype.val_injective
      change algebraMap S R (s : S) = algebraMap S R (0 : S)
      apply hu.mul_right_cancel
      simpa only [map_mul, map_zero, zero_mul, ← IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap S R) hs
    exact s.2 (hs0 ▸ q.zero_mem)
  have hcontr : (IsLocalRing.maximalIdeal Q).under C = IsLocalRing.maximalIdeal C := by
    rw [← Ideal.under_under (B := S), IsLocalization.AtPrime.under_maximalIdeal Q q]
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) q)
  let : IsExtension C Q := isExtension_of_injective_of_under_eq hCQ hcontr
  obtain ⟨algMF, towerCMF, f, hf, hfs, hfinF⟩ :=
    exists_fieldFactor_of_integralClosure_localization C M R S Q q.primeCompl hCQ
  let F := FractionRing Q
  let : Field F := inferInstanceAs (Field (FractionRing Q))
  let : Algebra Q F := inferInstanceAs (Algebra Q (FractionRing Q))
  let : IsFractionRing Q F := inferInstanceAs (IsFractionRing Q (FractionRing Q))
  let : Algebra M F := algMF
  let : IsScalarTower C M F := towerCMF
  let : Module.Finite M F := hfinF
  let : Algebra K F := ((algebraMap M F).comp (algebraMap K M)).toAlgebra
  let : IsScalarTower K M F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι : E →ₐ[K] F := (f.restrictScalars K).comp (IsScalarTower.toAlgHom K E R)
  have hsquare : ∀ a : integralClosure A E,
      algebraMap Q F (algebraMap (integralClosure A E) Q a) = ι (a : E) := by
    intro a
    change algebraMap Q F (algebraMap S Q (algebraMap A₁ S a)) =
      f (algebraMap E R (a : E))
    rw [← IsScalarTower.algebraMap_apply, ← hfs]
    rfl
  have hgen : Algebra.adjoin M (Set.range ι) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨t, rfl⟩ := hf x
    clear hx
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective t
    induction v using TensorProduct.inductionOn with
    | tmul m e =>
      have he : ι e ∈ Algebra.adjoin M (Set.range ι) := Algebra.subset_adjoin ⟨e, rfl⟩
      have eq : f (Ideal.Quotient.mk _ (m ⊗ₜ[K] e)) = algebraMap M F m * ι e := by
        have heq : Ideal.Quotient.mk _ (m ⊗ₜ[K] e) =
            algebraMap M R m * algebraMap E R e := by
          change Ideal.Quotient.mk _ (m ⊗ₜ[K] e) =
            Ideal.Quotient.mk _ (m ⊗ₜ[K] (1 : E)) * Ideal.Quotient.mk _ ((1 : M) ⊗ₜ[K] e)
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [heq]
        rw [map_mul, f.commutes]
        rfl
      rw [eq]
      exact (Algebra.adjoin M (Set.range ι)).mul_mem
        ((Algebra.adjoin M (Set.range ι)).algebraMap_mem m) he
    | add x y hx hy => simpa only [map_add] using (Algebra.adjoin M (Set.range ι)).add_mem hx hy
  have hi := hlocal Q F ι hsquare hgen
  rw [ramificationIdx_localization_atPrime A₁ S q] at hi
  exact hi

private theorem ramificationIndex_tower
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsExtension A B] [IsExtension B C] [IsExtension A C] :
    ramificationIndex A C =
      ramificationIndex A B * ramificationIndex B C := by
  let : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective B C)
  let : (IsLocalRing.maximalIdeal C).LiesOver (IsLocalRing.maximalIdeal B) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap B C)).symm⟩
  rw [ramificationIndex_eq_ramificationIdx A C, ramificationIndex_eq_ramificationIdx A B,
    ramificationIndex_eq_ramificationIdx B C]
  exact Ideal.ramificationIdx_tower (R := A) (IsLocalRing.maximalIdeal B)
    (IsLocalRing.maximalIdeal C)

/-- Let `π` be a uniformizer of `A`, `a ∈ A` a unit and `n > 0` prime to `p`. Let `E = K(w)` with
`w ^ p - w = π⁻¹ ^ n * a` be totally ramified with respect to `A`, and suppose `M` contains `z`
with `z ^ p - z = π⁻¹ ^ n * a + b` for some `b ∈ C`, where `e(C / A) = p`. Then `E / K` is a
weak solution for `A → C`. -/
theorem isWeakSolution_of_constant_artinSchreier_parameter
    (A : Type uA) (C : Type uC) (K : Type uK) (M : Type uM) (E : Type uK)
    [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Field K] [Field M] [Field E]
    [Algebra A C] [IsExtension A C]
    [Algebra A K] [Algebra C M] [Algebra A M] [Algebra K M]
    [IsFractionRing A K] [IsFractionRing C M]
    [IsScalarTower A C M] [IsScalarTower A K M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hpn : ¬p ∣ n)
    (a : A) (ha : IsUnit a) (b : C) (z : M) (w : E)
    (hz : z ^ p - z = algebraMap K M ((algebraMap A K π)⁻¹ ^ n * algebraMap A K a) +
      algebraMap C M b)
    (hw : w ^ p - w = algebraMap K E ((algebraMap A K π)⁻¹ ^ n * algebraMap A K a))
    (hwgen : Algebra.adjoin K {w} = ⊤)
    (htot : IsTotallyRamifiedWithRespectTo A K E)
    (hind : ramificationIndex A C = p) :
    ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
        max uM uK, uK, max uM uK} A C K M E, D.IsWeakSolution := by
  let : Fact p.Prime := ⟨hp⟩
  let : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  let A₁ := integralClosure A E
  let : IsDiscreteValuationRing A₁ :=
    isDiscreteValuationRing_integralClosure_of_totallyRamified A K E htot
  let : IsFractionRing A₁ E := integralClosure.isFractionRing_of_finite_extension K E
  have hAA : Function.Injective (algebraMap A A₁) := by
    intro x y h
    apply IsFractionRing.injective A K
    apply (algebraMap K E).injective
    have he := congrArg Subtype.val h
    change algebraMap A E x = algebraMap A E y at he
    simpa only [IsScalarTower.algebraMap_apply A K E] using he
  let : IsExtension A A₁ := isExtension_of_injective_of_under_eq hAA
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (IsLocalRing.maximalIdeal A₁)))
  have hAindex : ramificationIndex A A₁ = p :=
    ramificationIndex_eq_prime_of_artinSchreier_pole A A₁ K E p hp _ w hw hwgen
      π hπ n hn hpn a 0 ha (by rw [map_zero, add_zero])
  apply exists_isWeakSolution_of_fieldFactor_ramification A C K M E
  intro Q F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι hsquare hgen
  let : CharP F p := charP_of_injective_algebraMap (algebraMap M F).injective p
  have hg : Algebra.adjoin M {ι w - algebraMap M F z} = ⊤ := by
    rw [adjoin_singleton_sub_algebraMap,
      ← adjoin_range_eq_adjoin_singleton_of_adjoin_eq_top ι w hwgen]
    exact hgen
  have heq : (ι w - algebraMap M F z) ^ p - (ι w - algebraMap M F z) =
      algebraMap M F (algebraMap C M (-b)) := by
    have hw' := congrArg ι hw
    have hz' := congrArg (algebraMap M F) hz
    simp only [map_sub, map_pow, map_add, ι.commutes,
      ← IsScalarTower.algebraMap_apply] at hw' hz'
    simp only [sub_pow_char, map_neg, ← IsScalarTower.algebraMap_apply]
    linear_combination hw' - hz'
  have hCQ : IsWeaklyUnramified C Q :=
    isWeaklyUnramified_of_artinSchreier_parameter_integral C Q M F p hp _
      (ι w - algebraMap M F z) heq hg ⟨-b, rfl⟩
  let : IsLocalHom (algebraMap A Q) := by
    rw [IsScalarTower.algebraMap_eq A C Q]
    infer_instance
  let : FaithfulSMul A Q := (faithfulSMul_iff_algebraMap_injective A Q).mpr (by
    rw [IsScalarTower.algebraMap_eq A C Q]
    exact (FaithfulSMul.algebraMap_injective C Q).comp
      (FaithfulSMul.algebraMap_injective A C))
  let : IsExtension A Q := {}
  have hQindex : (IsLocalRing.maximalIdeal Q).ramificationIdx A = p := by
    rw [← ramificationIndex_eq_ramificationIdx A Q,
      ramificationIndex_tower A C Q, hind, show ramificationIndex C Q = 1 from hCQ,
      mul_one]
  have hinj : Function.Injective (algebraMap A₁ Q) := by
    intro x y h
    apply Subtype.ext
    apply ι.injective
    change ι (x : E) = ι (y : E)
    rw [← hsquare x, ← hsquare y, h]
  let : Module.IsTorsionFree A₁ Q := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hcontr : (IsLocalRing.maximalIdeal Q).under A₁ = IsLocalRing.maximalIdeal A₁ := by
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := A)
    change ((IsLocalRing.maximalIdeal Q).under A₁ |>.under A).IsMaximal
    rw [Ideal.under_under, Ideal.under_def, IsLocalRing.maximalIdeal_comap]
    infer_instance
  let : (IsLocalRing.maximalIdeal Q).LiesOver (IsLocalRing.maximalIdeal A₁) := ⟨hcontr.symm⟩
  have h := Ideal.ramificationIdx_tower (R := A)
    (IsLocalRing.maximalIdeal A₁) (IsLocalRing.maximalIdeal Q)
  rw [hQindex,
    (ramificationIndex_eq_ramificationIdx A A₁).symm.trans hAindex] at h
  exact Nat.eq_of_mul_eq_mul_left hp.pos (by simpa only [mul_one] using h.symm)


private theorem inv_pow_sub_mem_range_of_pow_eq_mul
    {R F : Type*} [CommRing R] [Field F] [Algebra R F]
    (π : R) (hπ : algebraMap R F π ≠ 0) (u : Rˣ) (α : F) (q N i : ℕ)
    (hα : α ^ q = algebraMap R F π * algebraMap R F (u : R))
    (hN : u.val - 1 ∈ Ideal.span {π ^ N}) (hi : i ≤ N) :
    (algebraMap R F π)⁻¹ ^ i - α⁻¹ ^ (q * i) ∈ (algebraMap R F).range := by
  have hdiv : π ^ N ∣ u.val ^ i - 1 := by
    have hd := (sub_dvd_pow_sub_pow u.val 1 i)
    rw [one_pow] at hd
    exact (Ideal.mem_span_singleton.mp hN).trans hd
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨π ^ (N - i) * c * (↑(u⁻¹) : R) ^ i, ?_⟩
  have hu : algebraMap R F u.val ≠ 0 := (u.isUnit.map (algebraMap R F)).ne_zero
  have hinv : algebraMap R F (↑(u⁻¹) : R) = (algebraMap R F u.val)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  have hc' := congrArg (algebraMap R F) hc
  simp only [map_sub, map_pow, map_one, map_mul] at hc'
  have hpow : (algebraMap R F π) ^ N =
      (algebraMap R F π) ^ (N - i) * (algebraMap R F π) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hpow] at hc'
  simp only [map_mul, map_pow, hinv, inv_pow, pow_mul, hα, mul_pow, mul_inv_rev]
  field_simp [hπ, hu]
  linear_combination -hc'

private theorem artinSchreier_sub_sum_pow
    {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    {ι : Type*} (s : Finset ι) (x : ι → R) (r : ι → ℕ) (z b : R)
    (hz : z ^ p - z = (∑ i ∈ s, x i ^ (p ^ r i)) + b) :
    (z - ∑ i ∈ s, ∑ k ∈ Finset.range (r i), x i ^ (p ^ k)) ^ p -
        (z - ∑ i ∈ s, ∑ k ∈ Finset.range (r i), x i ^ (p ^ k)) =
      (∑ i ∈ s, x i) + b := by
  have ht : (∑ i ∈ s, ∑ k ∈ Finset.range (r i), x i ^ (p ^ k)) ^ p -
      (∑ i ∈ s, ∑ k ∈ Finset.range (r i), x i ^ (p ^ k)) =
      (∑ i ∈ s, x i ^ (p ^ r i)) - ∑ i ∈ s, x i := by
    rw [sum_pow_char, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => artinSchreier_sum_pow p (x i) (r i))
  rw [sub_pow_char]
  linear_combination hz - ht

/-- Let `ξ = ∑ i ∈ s, aᵢ * π⁻¹ ^ eᵢ + b` in the fraction field of a discrete valuation ring `R`,
where `e j > 0` is strictly larger than every other exponent `eᵢ`. Then `ξ = π⁻¹ ^ e j * c` for
some `c ∈ R` with the same residue as `a j`. -/
theorem exists_laurent_numerator_residue_of_unique_max
    {R F ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (π : R) (hπ : Irreducible π) (s : Finset ι) (a : ι → R) (e : ι → ℕ)
    (j : ι) (hj : j ∈ s) (hm : 0 < e j) (he : ∀ i ∈ s, i ≠ j → e i < e j)
    (b : R) (ξ : F)
    (hξ : ξ = (∑ i ∈ s, algebraMap R F (a i) * (algebraMap R F π)⁻¹ ^ (e i)) +
      algebraMap R F b) :
    ∃ c : R, ξ = (algebraMap R F π)⁻¹ ^ (e j) * algebraMap R F c ∧
      IsLocalRing.residue R c = IsLocalRing.residue R (a j) := by
  classical
  have ht : algebraMap R F π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hπ.ne_zero
  refine ⟨(∑ i ∈ s, a i * π ^ (e j - e i)) + π ^ (e j) * b, ?_, ?_⟩
  · apply (mul_left_cancel₀ (pow_ne_zero (e j) ht))
    rw [hξ, mul_add, Finset.mul_sum]
    have hcancel : algebraMap R F π ^ e j * (algebraMap R F π)⁻¹ ^ e j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
    rw [← mul_assoc, hcancel, one_mul, map_add, map_sum, map_mul, map_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : e i ≤ e j := by
      by_cases h : i = j
      · subst i; rfl
      · exact (he i hi h).le
    rw [map_mul, map_pow, mul_left_comm,
      inv_pow, ← pow_sub₀ _ ht hij]
  · have hzero : IsLocalRing.residue R π = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hπ.not_isUnit
    simp only [map_add, map_sum, map_mul, map_pow, hzero, zero_pow hm.ne', zero_mul, add_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hne
      rw [zero_pow (Nat.sub_pos_of_lt (he i hi hne)).ne', mul_zero]
    · exact fun h => (h hj).elim

private theorem irreducible_of_pow_sub_mem_span_pow
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (π : A) (hπ : Irreducible π) (α : B) (q n : ℕ) (hq : 0 < q) (hn : 0 < n)
    (he : ramificationIndex A B = q)
    (hα : α ^ q - algebraMap A B π ∈ Ideal.span {algebraMap A B π ^ (n + 1)}) :
    Irreducible α ∧ ∃ u : Bˣ,
      α ^ q = algebraMap A B π * (u : B) ∧ u.val - 1 ∈ Ideal.span {algebraMap A B π ^ n} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hα
  obtain ⟨u, hu⟩ := isUnit_add_pow_mul_of_not_isUnit
    (map_nonunit (algebraMap A B) π hπ.not_isUnit) isUnit_one hn c
  have hroot : α ^ q = algebraMap A B π * (u : B) := by
    rw [hu]
    rw [pow_succ] at hc
    linear_combination hc
  obtain ⟨β, hβ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨v, hv⟩ := (ramificationIndex_characterization A B).2.2.2 π hπ β hβ
  rw [he] at hv
  have hassoc : Associated (α ^ q) (β ^ q) := by
    rw [hroot, hv]
    exact (associated_mul_unit_left _ _ u.isUnit).trans
      (associated_unit_mul_left _ _ v.isUnit)
  refine ⟨((Associated.pow_iff hq.ne').mp hassoc).irreducible_iff.mpr hβ, u, hroot, ?_⟩
  rw [hu, add_sub_cancel_left]
  exact Ideal.mem_span_singleton.mpr ⟨c, rfl⟩

private theorem exists_integralClosure_baseChange_dvr
    (A B K L E : Type*) [CommRing A] [CommRing B] [Field K] [Field L] [Field E]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hweak : IsWeaklyUnramified A B)
    (htot : IsTotallyRamifiedWithRespectTo A K E) :
    ∃ hL : IsField (L ⊗[K] E),
      letI := hL.toField
      ∃ hA : IsDiscreteValuationRing (integralClosure A E),
        letI := hA
        ∃ hR : IsDiscreteValuationRing (integralClosure B (L ⊗[K] E)),
          letI := hR
          ∃ _ : IsFractionRing (integralClosure B (L ⊗[K] E)) (L ⊗[K] E),
          ∃ f : integralClosure A E →ₐ[A] integralClosure B (L ⊗[K] E),
            Function.Injective f ∧
            Ideal.map f.toRingHom (IsLocalRing.maximalIdeal (integralClosure A E)) =
              IsLocalRing.maximalIdeal (integralClosure B (L ⊗[K] E)) ∧
            ∀ a : integralClosure A E,
              (f a : L ⊗[K] E) =
                (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) (a : E) := by
  have hmap : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B := by
    simpa only [show ramificationIndex A B = 1 from hweak, pow_one] using
      (ramificationIndex_characterization A B).2.1
  obtain ⟨hL, hA, hdom, hT, hinj, hmax, hRdom, hR, hfrac, e, hsquare, hinj', hmax'⟩ :=
    isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified A B K L E hmap htot
  let := hL.toField
  let := hA
  let := hdom
  let := hT
  let := hRdom
  let := hR
  let := hfrac
  let f : integralClosure A E →ₐ[A] integralClosure B (L ⊗[K] E) :=
    (e.restrictScalars A).toAlgHom.comp Algebra.TensorProduct.includeRight
  exact ⟨hL, hA, hR, hfrac, f, hinj', hmax', hsquare⟩

private theorem exists_integralClosure_embedding_into_dvr
    (B R L Q F : Type*) [CommRing B] [CommRing R] [CommRing Q]
    [IsDomain B] [IsDomain R] [IsDomain Q]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing R] [IsDiscreteValuationRing Q]
    [Field L] [Field F]
    [Algebra B R] [Algebra R L] [Algebra B L] [IsScalarTower B R L]
    [IsIntegralClosure R B L]
    [Algebra B Q] [IsExtension B Q]
    [Algebra Q F] [Algebra B F] [IsScalarTower B Q F] [IsFractionRing Q F]
    (ι : L →ₐ[B] F) :
    ∃ f : R →ₐ[B] Q, Function.Injective f ∧ IsLocalHom f.toRingHom ∧
      ∀ r : R, algebraMap Q F (f r) = ι (algebraMap R L r) := by
  let : Algebra.IsIntegral B R := IsIntegralClosure.isIntegral_algebra B L
  have hQF := IsFractionRing.injective Q F
  have hi (r : R) : IsIntegral Q (ι (algebraMap R L r)) :=
    (((Algebra.IsIntegral.isIntegral (R := B) r).map
      (IsScalarTower.toAlgHom B R L)).map ι).tower_top
  let f : R →ₐ[B] Q :=
    { toFun := fun r => IsIntegralClosure.mk' Q _ (hi r)
      map_zero' := by apply hQF; simp
      map_one' := by apply hQF; simp
      map_add' := fun x y => by apply hQF; simp
      map_mul' := fun x y => by apply hQF; simp
      commutes' := fun b => by
        apply hQF
        simp only [IsIntegralClosure.algebraMap_mk', ← IsScalarTower.algebraMap_apply,
          ι.commutes] }
  have hf : ∀ r : R, algebraMap Q F (f r) = ι (algebraMap R L r) := fun r =>
    IsIntegralClosure.algebraMap_mk' Q _ (hi r)
  have hinj : Function.Injective f := by
    intro x y h
    apply IsIntegralClosure.algebraMap_injective R B L
    apply ι.injective
    change ι (algebraMap R L x) = ι (algebraMap R L y)
    rw [← hf, ← hf, h]
  have hc : ((IsLocalRing.maximalIdeal Q).comap f.toRingHom).IsMaximal := by
    apply Ideal.IsIntegral.isMaximal_of_isMaximal_under (R := B)
    have hcomp : f.toRingHom.comp (algebraMap B R) = algebraMap B Q := f.comp_algebraMap
    change (Ideal.comap (f.toRingHom.comp (algebraMap B R)) (IsLocalRing.maximalIdeal Q)).IsMaximal
    rw [hcomp, IsLocalRing.maximalIdeal_comap]
    infer_instance
  have hlocal : IsLocalHom f.toRingHom :=
    ((IsLocalRing.local_hom_TFAE _).out 5 1).mp (IsLocalRing.eq_maximalIdeal hc)
  exact ⟨f, hinj, hlocal, hf⟩

private theorem adjoin_singleton_eq_top_of_adjoin_range_eq_top
    {L M S F E : Type*} [CommRing L] [CommRing M] [CommRing S] [CommRing F]
    [Algebra L M] [Algebra M F] [Algebra L F] [IsScalarTower L M F] [Algebra S F]
    (z : M) (ι : E → F) (hz : Algebra.adjoin L {z} = ⊤)
    (hF : Algebra.adjoin M (Set.range ι) = ⊤)
    (hL : ∀ l : L, algebraMap L F l ∈ (algebraMap S F).range)
    (hE : ∀ e : E, ι e ∈ (algebraMap S F).range) :
    Algebra.adjoin S {algebraMap M F z} = ⊤ := by
  have hM : ∀ m : M, algebraMap M F m ∈ Algebra.adjoin S {algebraMap M F z} := by
    intro m
    have hm : m ∈ Algebra.adjoin L {z} := by rw [hz]; trivial
    induction hm using Algebra.adjoin_induction with
    | mem x hx => obtain rfl : x = z := hx; exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap l =>
      rw [← IsScalarTower.algebraMap_apply]
      obtain ⟨s, hs⟩ := hL l
      rw [← hs]
      exact (Algebra.adjoin S {algebraMap M F z}).algebraMap_mem s
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (Algebra.adjoin S {algebraMap M F z}).add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact (Algebra.adjoin S {algebraMap M F z}).mul_mem hx hy
  apply top_unique
  intro x htop
  clear htop
  have hx : x ∈ Algebra.adjoin M (Set.range ι) := by rw [hF]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    obtain ⟨s, hs⟩ := hE e
    rw [← hs]
    exact (Algebra.adjoin S {algebraMap M F z}).algebraMap_mem s
  | algebraMap m => exact hM m
  | add x y _ _ hx hy => exact (Algebra.adjoin S {algebraMap M F z}).add_mem hx hy
  | mul x y _ _ hx hy => exact (Algebra.adjoin S {algebraMap M F z}).mul_mem hx hy

end IsDiscreteValuationRing
