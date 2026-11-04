module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.IntegralMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.PuncturedStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishing
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomological dimension of affine schemes of finite type over a field

Let `K` be a field and `X` an affine scheme of finite type over `K`. Then
`cd(X) ≤ dim(X) + cd(K)` (Stacks 0F0V).

The proof is the source's induction on `d = dim X`. By Noether normalization it suffices to treat
`𝔸^d_K = Spec A[X]`, `A = K[t₁, …, t_{d-1}]`, which is the first chart `j` of the projective line
`g : ℙ¹_A ⟶ Spec A`, whose complement is the section at infinity `i`. For a torsion sheaf `𝓕` on
`𝔸^d_K` and `f = j ≫ g : 𝔸^d_K ⟶ 𝔸^{d-1}_K`, Leray for `f` reduces the claim to the vanishing of
`H^p(𝔸^{d-1}_K, R^qf_*𝓕)` for `p + q > d + cd(K)`:

* for `q ≤ 1` this is the induction hypothesis on `𝔸^{d-1}_K`;
* for `q ≥ 3` the relative Leray sequence for `j` and `g` shows that the stalk of `R^qf_*𝓕` at a
  point `z` vanishes unless that of `g_*R^qj_*𝓕` does not: `R^pg_*j_*𝓕 = 0` for `p > 2` (Stacks
  095U, `g` being proper of relative dimension one), and `R^qj_*𝓕 = i_*i⁻¹R^qj_*𝓕` for `q > 0`
  (Stacks 04CA), on which the higher direct images of `g` vanish. Interlude I bounds the stalks of
  `R^qj_*𝓕` at infinity, so `R^qf_*𝓕` is supported in transcendence degree `≤ d - q`;
* for `q = 2` the stalk at the generic point is `H²` of an affine curve over a separably closed
  field (Stacks 03Q9 and 03SC), which vanishes;

and Interlude II (`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound`, the
conditional form of Stacks 0F0W) gives the vanishing for `q ≥ 2`.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_polynomial_le`: the inductive step.

## Implementation notes

The vanishing of `R^p g_* 𝒢` for `p > 2` along `g : ℙ¹_A ⟶ Spec A` is the case of Stacks 095U
for `ℙ¹_A`, `AlgebraicGeometry.isZero_rightDerived_etaleAbelianDirectImage_projectiveLine`; the
stalks of higher direct images are computed by Stacks 03Q9
(`AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`).

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

section Algebra

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A]

/-- The structure morphism `Spec A ⟶ Spec K` of a finite type `K`-algebra is of finite type. -/
private theorem locallyOfFiniteType_spec_map_algebraMap :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **The transcendence degree of a point of an affine scheme of finite type over a field is the
dimension of its closure** (Stacks 0A21), that is, of the quotient by its prime. -/
@[ega "IV 5.6.5" "special case"]
public theorem toENat_trdeg_residueField_spec_eq_ringKrullDim (z : Spec (.of A)) :
    letI : Algebra K ((Spec (.of A)).residueField z) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
        (Spec (.of A)).Γevaluation z).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg K ((Spec (.of A)).residueField z)) : WithBot ℕ∞) =
      ringKrullDim (A ⧸ z.asIdeal) := by
  have := locallyOfFiniteType_spec_map_algebraMap K A
  rw [← topologicalKrullDim_closure_singleton_eq_trdeg K (Spec (.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap K A))) z]
  have h : closure ({z} : Set (Spec (.of A))) =
      (PrimeSpectrum.zeroLocus (z.asIdeal : Set A) : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.closure_singleton (R := A) z
  rw [h]
  exact _root_.topologicalKrullDim_zeroLocus z.asIdeal

/-- **A prime of `K[t₁, …, tₙ]` whose quotient has dimension `n` is zero.** -/
public theorem eq_bot_of_le_ringKrullDim_quotient (n : ℕ) (z : Ideal (MvPolynomial (Fin n) K))
    (h : (n : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ z)) : z = ⊥ := by
  by_contra hz
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk z) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.2 hr)
  rw [Stacks.MvPolynomial.ringKrullDim_mvPolynomial K (Fin n), Nat.card_eq_fintype_card,
    Fintype.card_fin] at h1
  have h2 := (add_le_add h (le_refl (1 : WithBot ℕ∞))).trans h1
  have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h2
  have h4 : n + 1 ≤ n := by exact_mod_cast h3
  omega

end Algebra

/-- **The inductive step of Stacks 0F0V.** If Stacks 0F0V holds for affine schemes of finite type
of every dimension `m ≤ n` over all fields (`hIH`), then `cd(𝔸^{n+1}_K) ≤ n + 1 + cd(K)` for every
field `K`, with `𝔸^{n+1}_K` written as `Spec K[t₁, …, tₙ][X]`. -/
public theorem etaleCohomologicalDimension_spec_polynomial_le
    (n : ℕ)
    (hIH : ∀ m : ℕ, m ≤ n → ∀ ⦃E : Type u⦄ [Field E] ⦃Z : Scheme.{u}⦄ [IsAffine Z]
      (g : Z ⟶ Spec (.of E)) [LocallyOfFiniteType g], topologicalKrullDim Z ≤ m →
        etaleCohomologicalDimension Z ≤ m + etaleCohomologicalDimension (Spec (.of E)))
    (K : Type u) [Field K] :
    etaleCohomologicalDimension (Spec (.of (MvPolynomial (Fin n) K)[X])) ≤
      ((n + 1 : ℕ) : ℕ∞) + etaleCohomologicalDimension (Spec (.of K)) := by
  classical
  let A := MvPolynomial (Fin n) K
  let g : projectiveLine A ⟶ Spec (.of A) := projectiveLine A ↘ Spec (.of A)
  let j := projectiveLineXChart A
  let i := projectiveLineInfinitySection A
  have hgA := locallyOfFiniteType_spec_map_algebraMap K A
  have hrkA : ringKrullDim A = n := by
    rw [Stacks.MvPolynomial.ringKrullDim_mvPolynomial K (Fin n)]
    simp
  have hquot : ∀ z : Ideal A, ringKrullDim (A ⧸ z) ≤ n := fun z =>
    (ringKrullDim_quotient_le z).trans hrkA.le
  have hdimA : topologicalKrullDim (Spec (.of A)) = n := by
    rw [show topologicalKrullDim (Spec (.of A)) = ringKrullDim A from
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A, hrkA]
  have hcdA : etaleCohomologicalDimension (Spec (.of A)) ≤
      (n : ℕ∞) + etaleCohomologicalDimension (Spec (.of K)) :=
    hIH n le_rfl (Spec.map (CommRingCat.ofHom (algebraMap K A))) hdimA.le
  induction hK : etaleCohomologicalDimension (Spec (.of K)) using ENat.recTopCoe with
  | top => simp
  | coe c =>
  rw [hK] at hcdA
  refine etaleCohomologicalDimension_le _ _ fun F hF N hN => ?_
  have hN' : n + 1 + c < N := by exact_mod_cast hN
  refine LerayVanishing.subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived (j ≫ g) F N
    fun q hq => ?_
  have hT := torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0} (j ≫ g) q F hF
  rcases lt_or_ge q 2 with hq2 | hq2
  · -- `q ≤ 1`: the induction hypothesis on `𝔸^n_K`
    refine isEtaleCohomologyBound_etaleCohomologicalDimension _ _ hT (N - q) ?_
    refine lt_of_le_of_lt hcdA ?_
    exact_mod_cast (by omega : n + c < N - q)
  · -- `q ≥ 2`: the support of `R^qf_*𝓕` has transcendence degree at most `n + 1 - q`
    have hdimq : ∀ z : Ideal A, z.IsPrime → ∃ t : ℕ, t ≤ n ∧ ringKrullDim (A ⧸ z) = t := by
      intro z hz
      have h1 := hquot z
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ z) := ringKrullDim_nonneg_of_nontrivial
      have hne : ringKrullDim (A ⧸ z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
      obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.1 hne
      rw [← hb] at h1
      have hb' : b ≤ n := by exact_mod_cast h1
      have hbt : b ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hb'
      obtain ⟨t, rfl⟩ := ENat.ne_top_iff_exists.1 hbt
      exact ⟨t, by exact_mod_cast hb', hb.symm⟩
    have hstalkq : ∀ (s : GeometricPoint (Spec (.of A))) (t : ℕ),
        ringKrullDim (A ⧸ (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal) = t →
          n + 1 < t + q →
            IsZero ((smallEtaleStalkAb s.hom).obj
              (((smallEtaleDirectImageAb.{u + 1} (j ≫ g)).rightDerived q).obj F)) := by
      intro s t ht hlt
      rcases Nat.lt_or_ge q 3 with hq3 | hq3
      · -- `q = 2`: the generic point
        have htn : t = n := by
          have h1 := hquot (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal
          rw [ht] at h1
          have : t ≤ n := by exact_mod_cast h1
          omega
        have hbot := eq_bot_of_le_ringKrullDim_quotient K n
          (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal (by rw [ht, htn])
        rw [show j ≫ g = projectiveLineAffineStructureMorphism A from
          projectiveLineXChart_comp_structureMorphism A]
        let B := BigEtaleSite.containing (Spec (.of A))
        have hS : B.Contains (Spec (.of A)) := BigEtaleSite.contains_containing _
        let f := projectiveLineAffineStructureMorphism A
        have : (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal.IsPrime :=
          (s.hom (IsLocalRing.closedPoint s.residueField)).isPrime
        have : LocallyOfFiniteType f := projectiveLineAffineStructureMorphism_locallyOfFiniteType A
        have : LocallyOfFiniteType (strictHenselizationBaseChangeToStrictHenselization B hS f s) :=
          inferInstanceAs (LocallyOfFiniteType (pullback.snd f _))
        refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS f s F q).2 ?_
        -- the strict henselization at the generic point is a separably closed field
        let : Algebra A
            ((Spec (.of A)).presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))) :=
          (StructureSheaf.toStalk A _).hom.toAlgebra
        have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk
            (s.hom (IsLocalRing.closedPoint s.residueField)))
            (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal :=
          StructureSheaf.IsLocalization.to_stalk A _
        have hst : IsField ((Spec (.of A)).presheaf.stalk
            (s.hom (IsLocalRing.closedPoint s.residueField))) := by
          rw [IsLocalRing.isField_iff_maximalIdeal_eq,
            ← IsLocalization.AtPrime.map_eq_maximalIdeal
              (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal, hbot, Ideal.map_bot]
        have hfield := isField_etaleLocalRing_of_isField_stalk B (Spec (.of A)) hS s hst
        let := hfield.toField
        have := isSepClosed_etaleLocalRing_of_isField B (Spec (.of A)) hS s hfield
        have hdim : topologicalKrullDim (strictHenselizationBaseChange B hS f s) ≤ 1 := by
          have e : strictHenselizationBaseChange B hS f s ≅
              pullback (Spec.map (CommRingCat.ofHom (C : A →+* A[X])))
                (Spec.map (Spec.preimage (strictHenselizationToBase B (Spec (.of A)) hS s))) :=
            pullback.congrHom rfl (Spec.map_preimage _).symm
          rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
          exact topologicalKrullDim_pullback_spec_C_le_one hfield _
        have : IsAffine (strictHenselizationBaseChange B hS f s) :=
          isAffine_of_isAffineHom (strictHenselizationBaseChangeToStrictHenselization B hS f s)
        have hcd := etaleCohomologicalDimension_le_one_of_isSepClosed
          (Ω := ↥(etaleLocalRing B (Spec (.of A)) hS s))
          (strictHenselizationBaseChangeToStrictHenselization B hS f s) hdim
        exact isEtaleCohomologyBound_etaleCohomologicalDimension _ _
          (Stacks.Torsion.torsionSheafProperty_of_iso _
            ((smallEtalePullbackAbIsoEtaleAbelianInverseImage
              (strictHenselizationBaseChangeToSource B hS f s)).app F).symm
            (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} _ F hF)) q
          (lt_of_le_of_lt hcd (by exact_mod_cast (by omega : 1 < q)))
      · -- `q ≥ 3`: the relative Leray sequence for `j` and `g`
        have hrange : ∀ s' : GeometricPoint (projectiveLine A),
            s'.hom (IsLocalRing.closedPoint s'.residueField) ∉ Set.range i →
              s'.hom (IsLocalRing.closedPoint s'.residueField) ∈ Set.range j := by
          intro s' hs'
          rw [range_projectiveLineInfinitySection] at hs'
          exact not_not.1 hs'
        have hig : i ≫ g = 𝟙 _ := projectiveLineInfinitySection_comp_structureMorphism A
        have : IsIntegralHom (i ≫ g) := by rw [hig]; infer_instance
        -- `R^rj_*𝓕` for `r > 0` is a direct image from the section at infinity
        have hsupp : ∀ r : ℕ, 0 < r → IsIso ((smallEtaleAdjunctionAb i).unit.app
            (((smallEtaleDirectImageAb.{u + 1} j).rightDerived r).obj F)) := fun r hr =>
          isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk i _ fun s' hs' =>
            isZero_stalk_rightDerived_smallEtalePushforwardAb_of_isOpenImmersion j s'
              (hrange s' hs') F r hr
        refine LerayVanishing.isZero_stalk_rightDerived_comp_of_forall_isZero j g s F q
          fun r hr => ?_
        rcases Nat.eq_zero_or_pos r with rfl | hr0
        · -- `r = 0`: Stacks 095U for the proper relative curve `g`
          have hjT := Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb.{0} j F hF
          have h0 := isZero_rightDerived_etaleAbelianDirectImage_projectiveLine A _ hjT q (by omega)
          refine Functor.map_isZero _ (h0.of_iso ?_)
          exact ((smallEtaleDirectImageAb.{u + 1} g).rightDerived (q - 0)).mapIso
            ((smallEtaleDirectImageAb.{u + 1} j).rightDerivedZeroIsoSelf.app F)
        rcases lt_or_eq_of_le hr with hrq | rfl
        · -- `0 < r < q`: higher direct images of a direct image from the section vanish
          have hz := isZero_rightDerived_smallEtaleDirectImageAb_obj_of_isIntegralHom i g
            ((smallEtalePullbackAb i).obj
              (((smallEtaleDirectImageAb.{u + 1} j).rightDerived r).obj F))
            (q - r) (by omega)
          exact Functor.map_isZero _ (hz.of_iso
            (((smallEtaleDirectImageAb.{u + 1} g).rightDerived (q - r)).mapIso
              (@asIso _ _ _ _ _ (hsupp r hr0))))
        · -- `r = q`: Interlude I at the point at infinity over `s`
          let G := ((smallEtaleDirectImageAb.{u + 1} j).rightDerived r).obj F
          let H := (smallEtalePullbackAb i).obj G
          have hu := hsupp r hr0
          let s' : GeometricPoint (projectiveLine A) := ⟨s.residueField, s.hom ≫ i⟩
          let z := s.hom (IsLocalRing.closedPoint s.residueField)
          let e0 : A[X] →+* A := Polynomial.evalRingHom 0
          let y' : Spec (.of A[X]) := Spec.map (CommRingCat.ofHom e0) z
          have hy : projectiveLineYChart A y' = s'.hom (IsLocalRing.closedPoint s'.residueField) :=
            rfl
          have hty : (Polynomial.X : A[X]) ∈ y'.asIdeal := by
            show Polynomial.X ∈ Ideal.comap e0 z.asIdeal
            simp [e0]
          have htn : t ≤ n := by
            have h1 := hquot z.asIdeal
            rw [ht] at h1
            exact_mod_cast h1
          have ha' : (t : WithBot ℕ∞) ≤ ringKrullDim (A[X] ⧸ y'.asIdeal) := by
            have hsurj : Function.Surjective ((Ideal.Quotient.mk z.asIdeal).comp e0) :=
              (Ideal.Quotient.mk_surjective).comp fun a => ⟨Polynomial.C a, by simp [e0]⟩
            have hker : RingHom.ker ((Ideal.Quotient.mk z.asIdeal).comp e0) = y'.asIdeal := by
              rw [← RingHom.comap_ker, Ideal.mk_ker]
              rfl
            let eq : A[X] ⧸ y'.asIdeal ≃+* A ⧸ z.asIdeal :=
              (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
            rw [ringKrullDim_eq_of_ringEquiv eq, ht]
          have hR : Algebra.trdeg K (CommRingCat.of A[X]) ≤ ((n + 1 : ℕ) : Cardinal) := by
            show Algebra.trdeg K A[X] ≤ _
            have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective K A).2
              (algebraMap K A).injective
            have : FaithfulSMul A A[X] := (faithfulSMul_iff_algebraMap_injective A A[X]).2
              (Polynomial.C_injective)
            have h := trdeg_add_eq (A := A[X]) K A
            rw [MvPolynomial.trdeg_of_isDomain, Polynomial.trdeg_of_isDomain] at h
            rw [← h]
            simp
          have hzI := isZero_stalk_rightDerived_smallEtalePushforwardAb_of_chart
            (K := K) (R := CommRingCat.of A[X]) (n + 1) hR j (projectiveLineYChart A) Polynomial.X
            Polynomial.X_ne_zero (projectiveLineYChart_mem_range_xChart_iff A) s' y' hy hty t
            (n - t) ha' (by omega)
            (fun E _ Z _ g' _ hZ => hIH (n - t) (by omega) g' hZ)
            F hF r (by omega)
          refine hzI.of_iso ?_
          rw [Nat.sub_self]
          exact (smallEtaleStalkAb s.hom).mapIso
              (((smallEtaleDirectImageAb.{u + 1} g).rightDerivedZeroIsoSelf.app G) ≪≫
                (smallEtaleDirectImageAb.{u + 1} g).mapIso (@asIso _ _ _ _ _ hu) ≪≫
                (smallEtalePushforwardAbCompIso i g).app H ≪≫
                (smallEtalePushforwardAbIdOf (i ≫ g) hig).app H) ≪≫
            (smallEtaleStalkPullbackAbIso i s.hom).app G
    by_cases hqn : n + 1 < q
    · have hz : IsZero (((smallEtaleDirectImageAb.{u + 1} (j ≫ g)).rightDerived q).obj F) := by
        refine isZero_of_forall_isZero_smallEtaleStalkAb _ fun s => ?_
        obtain ⟨t, -, ht⟩ := hdimq (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal
          (s.hom (IsLocalRing.closedPoint s.residueField)).isPrime
        exact hstalkq s t ht (by omega)
      exact Sheaf.subsingleton_H_of_isZero hz _
    · obtain ⟨a, ha⟩ : ∃ a, a + q = n + 1 := ⟨n + 1 - q, by omega⟩
      refine subsingleton_H_of_smallEtaleSupport_subset_of_cdBound K
        (Spec.map (CommRingCat.ofHom (algebraMap K A))) a
        (fun Z g' _ _ hZ => hIH a (by omega) g' hZ) _ hT
        ((Stacks.EtaleCohomology.smallEtaleSupport_subset_iff _ _).2 fun s hs => ?_) (N - q) ?_
      · obtain ⟨t, -, ht⟩ := hdimq (s.hom (IsLocalRing.closedPoint s.residueField)).asIdeal
          (s.hom (IsLocalRing.closedPoint s.residueField)).isPrime
        have h := toENat_trdeg_residueField_spec_eq_ringKrullDim K A
          (s.hom (IsLocalRing.closedPoint s.residueField))
        rw [ht] at h
        have hs' := Cardinal.natCast_lt_toENat.2 (not_le.mp hs)
        have h3 := WithBot.coe_lt_coe.2 hs'
        rw [h] at h3
        have h'' : a < t := by exact_mod_cast h3
        exact hstalkq s t ht (by omega)
      · rw [hK]
        exact_mod_cast (by omega : a + c < N - q)

end AlgebraicGeometry.Scheme

end
