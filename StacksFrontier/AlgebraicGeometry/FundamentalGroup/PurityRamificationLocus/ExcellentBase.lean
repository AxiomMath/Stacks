module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.CutByParameter
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Serre.Criterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normality and dimension over an excellent regular local base

Two results are collected here, both needed to run the induction of purity of the ramification
locus over a base which has been completed.

The first is a normality criterion along a flat ring map: a flat algebra over a normal ring is
normal as soon as its localizations at the primes lying over height-`≤ 1` primes are regular.
This is Serre's criterion, `(R_1)` and `(S_2)`: flatness carries `(R_1)` from the hypothesis and
`(S_2)` from the base, depth being additive along a flat local homomorphism. Its geometric form
says that a flat morphism whose source is regular over the codimension-`≤ 1` part of a normal
target has normal local rings.

The second is the dimension formula: a quasi-finite, essentially-finite-type, injective local
homomorphism out of an excellent regular local domain does not change the dimension. The residue
field extension is algebraic, so its transcendence degree vanishes, and Zariski's main theorem
makes the essentially-finite-type subalgebra algebraic over the base, so the other transcendence
degree in the dimension formula vanishes too.

## Main results

* `AlgebraicGeometry.isNormalRing_of_flat_of_isRegularLocalRing_height_le_one` and
  `AlgebraicGeometry.isNormalRing_stalk_of_flat_of_isRegularLocalRing_codimension_le_one`: the
  normality criterion, algebraically and at a stalk.
* `AlgebraicGeometry.ringKrullDim_eq_of_local_quasiFinite`: the dimension formula.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_quasiFiniteAt_over_excellent`: its geometric form
  at a point over the closed point of an excellent regular local base.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Normality along a flat map -/

/-- **Serre's criterion along a flat ring map.** A flat algebra `S` over a Noetherian normal ring
`R` is normal as soon as `S_𝔮` is regular for every prime `𝔮` of `S` whose contraction to `R` has
height at most one.

Both of Serre's conditions are checked. Condition `(R_1)` follows from the hypothesis, flatness
giving going down and hence `height (𝔮 ∩ R) ≤ height 𝔮`. Condition `(S_2)` splits by the height
of `𝔭 = 𝔮 ∩ R`: when that height is at most one, `S_𝔮` is regular, hence Cohen-Macaulay, so its
depth is its dimension; otherwise `dim R_𝔭 ≥ 2`, so `depth R_𝔭 ≥ 2` by the criterion applied
to `R`, and depth is additive along the flat local homomorphism `R_𝔭 → S_𝔮`. -/
theorem isNormalRing_of_flat_of_isRegularLocalRing_height_le_one {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsNormalRing R)
    (hregular : ∀ (q : Ideal S) [q.IsPrime], (q.under R).height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime q)) : IsNormalRing S := by
  have hR' :=
    isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp hR
  apply isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mpr
  refine ⟨fun q hq hdim ↦ ?_, fun q hq ↦ ?_⟩
  · have _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
    exact hregular q
      ((Ideal.height_le_height_of_liesOver_of_hasGoingDown (q.under R) q).trans hdim)
  · by_cases hp : (q.under R).height ≤ 1
    · have _ := hregular q hp
      have hCM :=
        (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
          (Localization.AtPrime q)).2
      change (Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal _) _ : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime q) at hCM
      rw [hCM]
      exact min_le_right _ _
    · let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      have hdepth := Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
        (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
      have h2 : (2 : ℕ∞) ≤ (q.under R).height := by
        simpa only [one_add_one_eq_two] using
          (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr (lt_of_not_ge hp)
      have hpdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (q.under R)) := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R)
          (Localization.AtPrime (q.under R))]
        exact WithBot.coe_le_coe.mpr h2
      have htwo := hR'.2 (q.under R)
      rw [min_eq_left hpdim] at htwo
      refine (min_le_left _ _).trans (htwo.trans ?_)
      exact_mod_cast (show Module.depth (Localization.AtPrime (q.under R))
        (IsLocalRing.maximalIdeal _) _ ≤
          Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal _) _ from
        hdepth.symm ▸ le_self_add)

/-- **Serre's criterion along a flat morphism, at a stalk.** Let `j : X' ⟶ X` be flat and let
`x'` be a point of `X'` whose image has normal local ring. If `𝒪_{X',z}` is regular at every
generization `z` of `x'` whose image in `X` has local dimension at most one, then `𝒪_{X',x'}` is
normal. -/
theorem isNormalRing_stalk_of_flat_of_isRegularLocalRing_codimension_le_one {X' X : Scheme.{u}}
    [IsLocallyNoetherian X'] [IsLocallyNoetherian X] (j : X' ⟶ X) [Flat j] (x' : X')
    (hX : IsNormalRing (X.presheaf.stalk (j x')))
    (hregular : ∀ z : X', z ⤳ x' → ringKrullDim (X.presheaf.stalk (j z)) ≤ 1 →
      IsRegularLocalRing (X'.presheaf.stalk z)) :
    IsNormalRing (X'.presheaf.stalk x') := by
  let R := X.presheaf.stalk (j x')
  let S := X'.presheaf.stalk x'
  let _ : Algebra R S := (j.stalkMap x').hom.toAlgebra
  have _ : Module.Flat R S := Flat.stalkMap j x'
  apply isNormalRing_of_flat_of_isRegularLocalRing_height_le_one hX
  intro q hq hdim
  let q' : Spec (.of S) := ⟨q, hq⟩
  let z := X'.fromSpecStalk x' q'
  have hz : z ⤳ x' := by
    simpa only [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using
      (Set.mem_range_self (f := X'.fromSpecStalk x') q')
  have hp : X.fromSpecStalk (j x') (Spec.map (j.stalkMap x') q') = j z :=
    congrArg (fun k : Spec (.of S) ⟶ X ↦ k q') (Scheme.SpecMap_stalkMap_fromSpecStalk j)
  have hdim' : ringKrullDim (X.presheaf.stalk (j z)) ≤ 1 := by
    rw [← hp, ringKrullDim_stalk_fromSpecStalk]
    exact WithBot.coe_le_coe.mpr hdim
  have _ := hregular z hz hdim'
  have _ := isIso_stalkMap_of_flat_isPreimmersion (X'.fromSpecStalk x') q'
  exact IsRegularLocalRing.of_ringEquiv
    ((asIso ((X'.fromSpecStalk x').stalkMap q')).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso (.of S) q').commRingCatIsoToRingEquiv)

/-! ### The dimension formula -/

/-- **The dimension formula for a quasi-finite local homomorphism.** A quasi-finite,
essentially-finite-type, injective local homomorphism from a Noetherian universally catenary
local domain `A` to a local domain `B` preserves the dimension.

The essentially-finite-type subalgebra `C ⊆ B` is of finite type over `A` and `B` is its
localization at the prime `P` under the maximal ideal of `B`; Zariski's main theorem supplies an
`s ∉ P` with every element of `C` algebraic over `A` after multiplication by a power of `s`, so
`C` is algebraic over `A` and the transcendence degree of `C` over `A` vanishes. Quasi-finiteness
makes the residue field extension finite, so its transcendence degree vanishes too, and the
dimension formula for a universally catenary base then reads `height P = dim A`. -/
@[ega "IV 13.2.3" "converse, special case",
  ega "IV 13.2.5" "(iv), special case",
  ega "IV 13.2.7" "special case",
  ega "IV 13.3.4" "special case",
  ega "IV 5.5.8" "special case",
  ega "IV 5.6.1" "special case",
  ega "IV 5.6.10" "more general"]
theorem ringKrullDim_eq_of_local_quasiFinite {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [FaithfulSMul A B] [Algebra.EssFiniteType A B]
    [Algebra.QuasiFinite A B] (hcat : IsUniversallyCatenary A) :
    ringKrullDim B = ringKrullDim A := by
  let C := Algebra.EssFiniteType.subalgebra A B
  let P := (IsLocalRing.maximalIdeal B).under C
  have hM : Algebra.EssFiniteType.submonoid A B = P.primeCompl := by
    ext c
    show IsUnit (algebraMap C B c) ↔ algebraMap C B c ∉ IsLocalRing.maximalIdeal B
    exact IsLocalRing.notMem_maximalIdeal.symm
  have _ : IsLocalization.AtPrime B P := by
    show IsLocalization P.primeCompl B
    rw [← hM]
    exact Algebra.EssFiniteType.isLocalization A B
  let e := (IsLocalization.algEquiv P.primeCompl B (Localization.AtPrime P)).restrictScalars A
  have _ : Algebra.QuasiFiniteAt A P := (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have hlie : P.under A = IsLocalRing.maximalIdeal A := by
    simp only [P, Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A C B,
      IsLocalRing.maximalIdeal_comap]
  have _ : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hlie.symm⟩
  obtain ⟨s, hsP, hs, Hs⟩ := Algebra.zariskisMainProperty_iff.mp
    (Algebra.ZariskisMainProperty.of_finiteType (R := A) P)
  have _ : Algebra.IsAlgebraic A C := by
    refine ⟨fun c ↦ ?_⟩
    obtain ⟨m, hm⟩ := Hs c
    refine IsAlgebraic.of_mul ?_ (hs.pow m).isAlgebraic hm.isAlgebraic
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero m (fun hzero ↦ hsP (hzero ▸ Ideal.zero_mem P)))
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [IsScalarTower.algebraMap_apply A C B] using congrArg (algebraMap C B) hab
  let _ := Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal A) P
  have _ : Module.Finite (IsLocalRing.maximalIdeal A).ResidueField P.ResidueField := inferInstance
  have _ : Algebra.IsAlgebraic (IsLocalRing.maximalIdeal A).ResidueField P.ResidueField :=
    ⟨fun a ↦ (IsIntegral.of_finite (IsLocalRing.maximalIdeal A).ResidueField a).isAlgebraic⟩
  have halg : Ideal.ResidueField.algebraOfLiesOver (IsLocalRing.maximalIdeal A) P =
      (inferInstance : Algebra (IsLocalRing.maximalIdeal A).ResidueField P.ResidueField) := by
    refine Algebra.algebra_ext _ _ fun a ↦ ?_
    obtain ⟨a, rfl⟩ := (IsLocalRing.maximalIdeal A).algebraMap_residueField_surjective a
    show Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) P (algebraMap A C)
      Ideal.LiesOver.over (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a) = _
    rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply A
      (IsLocalRing.maximalIdeal A).ResidueField P.ResidueField,
      IsScalarTower.algebraMap_apply A C P.ResidueField]
  have hd := height_add_trdeg_residue_eq hinj hcat (IsLocalRing.maximalIdeal A) P
  rw [halg] at hd
  simp only [trdeg_eq_zero, map_zero, Nat.cast_zero, add_zero] at hd
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P B,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hd

/-- **The dimension formula at a point of quasi-finiteness over an excellent regular local
base.** Let `A` be an excellent regular local ring, let `f : X ⟶ Spec A` be locally of finite
type, and let `x` be a point over the closed point whose local ring is normal, at which `f` is
quasi-finite and whose structure map from `A` is injective. Then `dim 𝒪_{X,x} = dim 𝒪_{Spec A, f
x}`. -/
theorem ringKrullDim_stalk_eq_of_quasiFiniteAt_over_excellent {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X) (hx : f x = IsLocalRing.closedPoint A)
    (hX : IsNormalRing (X.presheaf.stalk x)) (hinj : Function.Injective (toStalkStalkMap f x))
    (hqf : f.QuasiFiniteAt x) :
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) := by
  let R : Type u := (Spec (.of A)).presheaf.stalk (f x)
  let S : Type u := X.presheaf.stalk x
  have _ : IsDomain S := hX.of_isLocalRing.1
  have _ : IsRegularLocalRing R := isRegularLocalRing_stalk_spec A (f x)
  have _ : IsDomain R := IsRegularLocalRing.isDomain R
  let _ : Algebra A R := (StructureSheaf.toStalk A (f x)).hom.toAlgebra
  have _ : (f x).asIdeal.IsPrime := (f x).isPrime
  have _ : IsLocalization.AtPrime R (f x).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f x)
  have _ : Algebra.EssFiniteType A R := .of_isLocalization R (f x).asIdeal.primeCompl
  have hR := (isQuasiExcellent_and_isExcellent_of_essFiniteType (R := A) (S := R)).2 hA
  have hsurj : Function.Surjective (StructureSheaf.toStalk A (f x)).hom := by
    rw [hx, ← stalkClosedPointIso_inv (CommRingCat.of A)]
    exact (stalkClosedPointIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.surjective
  have hi : Function.Injective (f.stalkMap x).hom := by
    intro a b hab
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    exact congrArg (StructureSheaf.toStalk A (f x)).hom (hinj hab)
  let _ : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have _ : IsLocalHom (algebraMap R S) := f.prop x
  have _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hi
  have _ : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f x
  have _ : Algebra.QuasiFinite R S := hqf
  exact ringKrullDim_eq_of_local_quasiFinite
    (Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp hR.2)

end AlgebraicGeometry

end
