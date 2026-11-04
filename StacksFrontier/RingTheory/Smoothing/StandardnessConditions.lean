module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation
public import StacksFrontier.RingTheory.Kaehler.Defs

/-!
# The six standardness conditions for an element of a finitely presented algebra

Let `R → A` be a ring map of finite presentation and let `a : A`. Stacks 16.3.7 compares six
conditions on `a`:

1. `A_a` is smooth over `R`;
2. `A_a` is smooth over `R` and `Ω[A_a⁄R]` is stably free;
3. `A_a` is smooth over `R` and `Ω[A_a⁄R]` is free;
4. `A_a` is standard smooth over `R`;
5. `a` is strictly standard in `A` over `R`;
6. `a` is elementary standard in `A` over `R`.

This file packages the standing data as `SixStandardnessConditions` and proves the
implications (6) ⇒ (4) ⇒ (3) ⇒ (2) ⇒ (1) and (6) ⇒ (5).

## Main definitions

* `Stacks.Smoothing.SixStandardnessConditions`: the standing context, i.e. a finitely presented
  ring map `R → A` together with a distinguished element `a : A`.

## Main results

* `Stacks.Smoothing.isStandardSmooth_localizationAway_of_isElementaryStandard`: (6) ⇒ (4).
* `Stacks.Smoothing.standardSmooth_localization_isSmooth_and_free`: (4) ⇒ (3).
* `Stacks.Smoothing.free_of_differentials_implies_stably_free`: (3) ⇒ (2).
* `Stacks.Smoothing.smooth_of_smooth_and_stablyFree_differentials`: (2) ⇒ (1).
* `Stacks.Smoothing.elementaryStandard_implies_strictlyStandard`: (6) ⇒ (5).

## Implementation notes

The localization `A_a` is `Localization.Away a` and the module of relative differentials is
Mathlib's `KaehlerDifferential`. Smoothness and standard smoothness are `Algebra.Smooth` and
`Algebra.IsStandardSmooth`; strict and elementary standardness are `IsStrictlyStandard` and
`IsElementaryStandard` from `StacksDraft.Ch16.Sec2.Tag07CC`.

## References

* [Stacks Project, Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v

/-- The standing data for the six standardness conditions of Stacks 16.3.7: a ring map
`R → A` of finite presentation together with a distinguished element `a : A`.

For an instance `S` of this structure, the six conditions are formed using
`Localization.Away S.a`, `KaehlerDifferential`, `Algebra.Smooth`,
`Algebra.IsStandardSmooth`, `IsStrictlyStandard` and `IsElementaryStandard`. -/
structure SixStandardnessConditions where
  /-- The base ring. -/
  R : Type u
  /-- The algebra over the base ring. -/
  A : Type v
  /-- The commutative-ring structure on the base. -/
  [commRingR : CommRing R]
  /-- The commutative-ring structure on the algebra. -/
  [commRingA : CommRing A]
  /-- The ring map `R → A`. -/
  [algebra : Algebra R A]
  /-- The ring map is of finite presentation. -/
  [finitePresentation : Algebra.FinitePresentation R A]
  /-- The distinguished element of `A`. -/
  a : A

attribute [instance] SixStandardnessConditions.commRingR
attribute [instance] SixStandardnessConditions.commRingA
attribute [instance] SixStandardnessConditions.algebra
attribute [instance] SixStandardnessConditions.finitePresentation

/-- Standard smoothness of `A_a` implies condition (3): `A_a` is smooth over `R` and its module
of relative differentials is free. -/
@[stacks 07EZ "clause (a), the implication (4) ⇒ (3): if `A_a` is standard smooth over `R` \
then `A_a` is smooth over `R` and `Ω_{A_a/R}` is free"]
theorem standardSmooth_localization_isSmooth_and_free
    (S : SixStandardnessConditions)
    (h : Algebra.IsStandardSmooth S.R (Localization.Away S.a)) :
      Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.Free (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a)) := by
  let := h
  exact ⟨inferInstance, inferInstance⟩

/-- Condition (3) implies condition (2): a free module of differentials is stably free. -/
@[stacks 07EZ "clause (a), the implication (3) ⇒ (2): if `A_a` is smooth over `R` and \
`Ω_{A_a/R}` is free then it is stably free"]
theorem free_of_differentials_implies_stably_free
    (S : SixStandardnessConditions)
    (h : Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.Free (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a))) :
    Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.IsStablyFree (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a)) := by
  let := h.2
  exact ⟨h.1, inferInstance⟩

/-- Condition (2) implies condition (1): smoothness of `A_a` over `R`. -/
@[stacks 07EZ "clause (a), the implication (2) ⇒ (1): if `A_a` is smooth over `R` and \
`Ω_{A_a/R}` is stably free then `A_a` is smooth over `R`"]
lemma smooth_of_smooth_and_stablyFree_differentials (S : SixStandardnessConditions)
    (h : Algebra.Smooth S.R (Localization.Away S.a) ∧
      Module.IsStablyFree (Localization.Away S.a)
        (KaehlerDifferential S.R (Localization.Away S.a))) :
    Algebra.Smooth S.R (Localization.Away S.a) :=
  h.1

/-- Condition (6) implies condition (5): an elementary standard element is strictly standard.
The single principal minor is the minor indexed by the first `c` variables. -/
@[stacks 07EZ "clause (b), the implication (6) ⇒ (5): an elementary standard element is \
strictly standard, the single principal minor being the one on the first `c` variables"]
theorem elementaryStandard_implies_strictlyStandard
    (S : SixStandardnessConditions)
    (h : IsElementaryStandard (R := S.R) (A := S.A) S.a) :
    IsStrictlyStandard (R := S.R) (A := S.A) S.a := by
  classical
  rcases h with ⟨P, c, hcn, hcm, ⟨⟨a', ha'⟩, hcond⟩⟩
  let e : Fin c ↪ Fin P.n := ⟨Fin.castLE hcn, Fin.castLE_injective hcn⟩
  let s₀ : Finset (Fin P.n) := Finset.univ.map e
  have hs₀ : s₀.card = c := by simp [s₀, e]
  have hs₀mem : s₀ ∈ Finset.powersetCard c (Finset.univ : Finset (Fin P.n)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs₀⟩
  have hjac : P.jacobianMinor c hcm s₀ hs₀ =
      P.jacobianMinorPrincipal c hcn hcm := by
    unfold Presentation.jacobianMinor Presentation.jacobianMinorPrincipal
    congr 2
    funext j i
    have he : (⟨e, by intro x y; simp [e]⟩ : Fin c ↪o Fin P.n) =
        s₀.orderEmbOfFin hs₀ := by
      apply Finset.orderEmbOfFin_unique'
      intro x
      simp [s₀, e]
    rw [Finset.coe_orderIsoOfFin_apply, congrArg (fun f => f i) he.symm]
    rfl
  refine ⟨P, c, hcn, hcm, ⟨?_, hcond⟩⟩
  refine ⟨fun s => if s = s₀ then a' else 0, ?_⟩
  rw [Finset.sum_eq_single s₀]
  · simpa [hs₀, hjac] using ha'
  · intro b hb hbs
    simp [hbs]
  · exact fun hnot => (hnot hs₀mem).elim

private noncomputable def firstRelations {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    Fin c → MvPolynomial (Fin P.n) R := fun j => P.f (Fin.castLE hcm j)

private abbrev firstQuotient {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :=
  MvPolynomial (Fin P.n) R ⧸ Ideal.span (Set.range (firstRelations P c hcm))

private noncomputable def firstPreSubmersivePresentation {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (P : Presentation R A) (c : ℕ) (hcn : c ≤ P.n)
    (hcm : c ≤ P.m) :
    Algebra.PreSubmersivePresentation R (firstQuotient P c hcm) (Fin P.n) (Fin c) where
  __ := Algebra.Presentation.naive
  map := Fin.castLE hcn
  map_inj := Fin.castLE_injective hcn

private theorem firstPreSubmersivePresentation_jacobian {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (P : Presentation R A) (c : ℕ) (hcn : c ≤ P.n)
    (hcm : c ≤ P.m) :
    (firstPreSubmersivePresentation P c hcn hcm).jacobian =
      Ideal.Quotient.mk _ (P.jacobianMinorPrincipal c hcn hcm) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  show _ = Ideal.Quotient.mk _ _
  rw [show (firstPreSubmersivePresentation P c hcn hcm).jacobiMatrix =
      Matrix.transpose (Matrix.of fun j i : Fin c =>
        MvPolynomial.pderiv (Fin.castLE hcn i) (P.f (Fin.castLE hcm j))) by
        ext i j
        simp [firstPreSubmersivePresentation, firstRelations,
          Algebra.PreSubmersivePresentation.jacobiMatrix_apply]]
  rw [Matrix.det_transpose]
  rfl

private noncomputable def firstToAlgebra {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    firstQuotient P c hcm →ₐ[R] A := by
  let I : Ideal (MvPolynomial (Fin P.n) R) := Ideal.span (Set.range P.f)
  let J := Ideal.span (Set.range (firstRelations P c hcm))
  have hJI : J ≤ I := Ideal.span_mono (Set.range_comp_subset_range (Fin.castLE hcm) P.f)
  let φ : firstQuotient P c hcm →ₐ[R] (MvPolynomial (Fin P.n) R ⧸ I) := {
    toRingHom := Ideal.Quotient.factor hJI
    commutes' := by
      intro r
      change Ideal.Quotient.factor hJI (Ideal.Quotient.mk J (MvPolynomial.C r)) =
        Ideal.Quotient.mk I (MvPolynomial.C r)
      rw [Ideal.Quotient.factor_mk] }
  exact P.iso.symm.toAlgHom.comp φ

private theorem firstToAlgebra_mk {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m)
    (p : MvPolynomial (Fin P.n) R) :
    firstToAlgebra P c hcm (Ideal.Quotient.mk _ p) =
      P.iso.symm (Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p) := by
  simp [firstToAlgebra, Ideal.Quotient.factor_mk]

private theorem firstToAlgebra_surjective {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    Function.Surjective (firstToAlgebra P c hcm) := by
  intro a
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (P.iso a)
  refine ⟨Ideal.Quotient.mk _ p, ?_⟩
  rw [firstToAlgebra_mk]
  simpa using congrArg P.iso.symm hp

private theorem firstToAlgebra_ker {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Presentation R A) (c : ℕ) (hcm : c ≤ P.m) :
    RingHom.ker (firstToAlgebra P c hcm).toRingHom =
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range (firstRelations P c hcm))))
        (Ideal.span (Set.range P.f)) := by
  classical
  let J := Ideal.span (Set.range (firstRelations P c hcm))
  ext z
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hzero : firstToAlgebra P c hcm (Ideal.Quotient.mk J p) = 0 := by
      simpa [RingHom.mem_ker] using hz
    rw [firstToAlgebra_mk] at hzero
    have hp : Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p = 0 := by
      simpa using congrArg P.iso hzero
    exact (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective).2 ⟨p, (Ideal.Quotient.eq_zero_iff_mem).mp hp, rfl⟩
  · intro hz
    obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective).mp hz
    have hp' : Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hp
    show firstToAlgebra P c hcm (Ideal.Quotient.mk J p) = 0
    rw [firstToAlgebra_mk, hp', map_zero]

/-- Condition (6) implies condition (4): an elementary standard element has a standard smooth
localization. -/
@[stacks 07EZ "clause (c), the implication (6) ⇒ (4): if `a` is elementary standard in `A` \
over `R` then `A_a` is *standard smooth* over `R` — condition (4), not merely smooth after \
some further localization"]
theorem isStandardSmooth_localizationAway_of_isElementaryStandard
    (S : SixStandardnessConditions)
    (ha : IsElementaryStandard (R := S.R) S.a) :
    Algebra.IsStandardSmooth S.R (Localization.Away S.a) := by
  classical
  rcases ha with ⟨P, c, hcn, hcm, ⟨⟨a', haeq⟩, hcond⟩⟩
  let Δ := P.jacobianMinorPrincipal c hcn hcm
  let J := Ideal.span (Set.range (firstRelations P c hcm))
  let I : Ideal (MvPolynomial (Fin P.n) S.R) := Ideal.span (Set.range P.f)
  obtain ⟨p, hpquot⟩ := Ideal.Quotient.mk_surjective (P.iso S.a)
  have hplift : P.IsLift S.a p := by
    unfold Presentation.IsLift Presentation.lift
    simpa using congrArg P.iso.symm hpquot
  let C := firstQuotient P c hcm
  let d : C := Ideal.Quotient.mk J p
  let ΔC : C := Ideal.Quotient.mk J Δ
  let q := firstToAlgebra P c hcm
  have hqd : q d = S.a := by
    rw [firstToAlgebra_mk]
    exact hplift
  have hqΔ : q ΔC = P.lift Δ := by
    rw [firstToAlgebra_mk]
    rfl
  let D := Localization.Away ΔC
  let E := Localization.Away (algebraMap C D d)
  let _ : IsLocalization.Away (d * ΔC) E :=
    IsLocalization.Away.mul (S := D) (T := E) ΔC d
  have hsub : IsUnit ((algebraMap C D) ΔC) := IsLocalization.Away.algebraMap_isUnit ΔC
  let P₀ := firstPreSubmersivePresentation P c hcn hcm
  let Q₀ := Algebra.PreSubmersivePresentation.localizationAway D ΔC
  let P₁ := Q₀.comp P₀
  have hP₁ : IsUnit P₁.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def,
      firstPreSubmersivePresentation_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact hsub.mul hsub
  let SP : Algebra.SubmersivePresentation S.R D (Unit ⊕ Fin P.n) (Unit ⊕ Fin c) :=
    { toPreSubmersivePresentation := P₁
      jacobian_isUnit := hP₁ }
  have hD : Algebra.IsStandardSmooth S.R D := SP.isStandardSmooth
  let _ : Algebra C S.A := q.toRingHom.toAlgebra
  let _ : IsScalarTower S.R C S.A := IsScalarTower.of_algebraMap_eq'
    (R := S.R) (S := C) (A := S.A) (by
    ext r
    show algebraMap S.R S.A r = q (algebraMap S.R C r)
    exact (q.commutes r).symm)
  have hΔA : IsUnit (algebraMap S.A (Localization.Away S.a) (P.lift Δ)) := by
    have hprod : IsUnit (algebraMap S.A (Localization.Away S.a) (a' * P.lift Δ)) := by
      rw [← haeq]
      exact IsLocalization.Away.algebraMap_isUnit S.a
    rw [map_mul] at hprod
    exact (IsUnit.mul_iff.mp hprod).2
  let _ : IsLocalization.Away (q (d * ΔC)) (Localization.Away S.a) := by
    rw [map_mul, hqd, hqΔ]
    exact IsLocalization.Away.mul_of_isUnit S.a (P.lift Δ) hΔA
  let qlocRing : E →+* Localization.Away S.a :=
    IsLocalization.Away.map E (Localization.Away S.a) q.toRingHom (d * ΔC)
  let qloc : E →ₐ[S.R] Localization.Away S.a := {
    toRingHom := qlocRing
    commutes' := by
      intro r
      show IsLocalization.Away.map E (Localization.Away S.a) q.toRingHom (d * ΔC)
        ((algebraMap C E) ((algebraMap S.R C) r)) = _
      rw [IsLocalization.Away.map, IsLocalization.map_eq]
      show (algebraMap S.A (Localization.Away S.a))
        (q ((algebraMap S.R C) r)) = _
      rw [q.commutes r]
      exact IsScalarTower.algebraMap_apply S.R S.A (Localization.Away S.a) r }
  have hqloc_surj : Function.Surjective qloc := by
    show Function.Surjective qlocRing
    rw [IsLocalization.Away.map_surjective_iff]
    intro a
    obtain ⟨b, hb⟩ := firstToAlgebra_surjective P c hcm a
    exact ⟨b, 0, by simpa using hb⟩
  have hkerloc : RingHom.ker qloc.toRingHom =
      Ideal.map (algebraMap C E) (RingHom.ker q.toRingHom) := by
    have hpow : Submonoid.map q.toRingHom (Submonoid.powers (d * ΔC)) =
        Submonoid.powers (q (d * ΔC)) := by
      ext x
      simp [Submonoid.map_powers]
    show RingHom.ker (IsLocalization.Away.map E (Localization.Away S.a)
      q.toRingHom (d * ΔC)) = _
    exact IsLocalization.ker_map (Localization.Away S.a) q.toRingHom hpow
  let K : Ideal E := RingHom.ker qloc.toRingHom
  let ψ : MvPolynomial (Fin P.n) S.R →+* E :=
    (algebraMap C E).comp (Ideal.Quotient.mk J)
  have hmapI : Ideal.map ψ I = K := by
    calc
      Ideal.map ψ I = Ideal.map (algebraMap C E) (Ideal.map (Ideal.Quotient.mk J) I) := by
        rw [Ideal.map_map]
      _ = Ideal.map (algebraMap C E) (RingHom.ker q.toRingHom) := by
        rw [firstToAlgebra_ker P c hcm]
      _ = K := hkerloc.symm
  have hJker : J ≤ RingHom.ker ψ := by
    intro x hx
    show algebraMap C E (Ideal.Quotient.mk J x) = 0
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 hx, map_zero]
  have hJbot : Ideal.map ψ J = ⊥ := (Ideal.map_eq_bot_iff_le_ker ψ).2 hJker
  have hKspan : K = Ideal.span (Set.range (fun j : Fin P.m => ψ (P.f j))) := by
    rw [← hmapI, show I = Ideal.span (Set.range P.f) by rfl, Ideal.map_span,
      ← Set.range_comp]
    rfl
  have hKfg : K.FG := by
    rw [hKspan]
    exact Submodule.fg_span (Set.finite_range _)
  have hK_le : K ≤ K ^ 2 := by
    rw [hKspan]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    show ψ (P.f j) ∈ (Ideal.span (Set.range (fun j : Fin P.m => ψ (P.f j)))) ^ 2
    by_cases hj : (j : ℕ) < c
    · let k : Fin c := ⟨j.1, hj⟩
      have hj' : Fin.castLE hcm k = j := by
        ext
        simp [k]
      have hmem : P.f j ∈ J := by
        rw [← hj']
        exact Ideal.subset_span ⟨k, rfl⟩
      rw [show ψ (P.f j) = 0 from hJker hmem]
      exact Ideal.zero_mem _
    · let k : Fin (P.m - c) := ⟨j.1 - c, by omega⟩
      have hj' : (⟨c + k.1, by omega⟩ : Fin P.m) = j := by
        ext
        simp [k]
        omega
      have htail := hcond k p hplift
      rw [hj'] at htail
      have htail' : p * P.f j ∈ J + I ^ 2 := by
        have hx : p * P.f j ∈ P.firstRelIdeal c hcm + I ^ 2 := by
          simpa [Presentation.relIdeal] using htail
        rw [show P.firstRelIdeal c hcm = J by rfl] at hx
        exact hx
      have hmaple : Ideal.map ψ (J + I ^ 2) ≤ K ^ 2 := by
        rw [show J + I ^ 2 = J ⊔ I ^ 2 by rfl, Ideal.map_sup, hJbot,
          Ideal.map_pow, hmapI]
        simp
      have hprod : ψ p * ψ (P.f j) ∈ K ^ 2 := by
        simpa [map_mul] using hmaple (Ideal.mem_map_of_mem ψ htail')
      have hunit : IsUnit (ψ p) := by
        show IsUnit (algebraMap C E d)
        exact IsLocalization.Away.isUnit_of_dvd (d * ΔC) (dvd_mul_right d ΔC)
      simpa only [hKspan, ← mul_assoc, hunit.val_inv_mul, one_mul] using
        Ideal.mul_mem_left (K ^ 2) (↑(hunit.unit⁻¹)) hprod
  have hK_idem : IsIdempotentElem K := by
    show K * K = K
    exact le_antisymm (Ideal.mul_le_left) (by simpa [pow_two] using hK_le)
  obtain ⟨e, he, hKe⟩ := (Ideal.isIdempotentElem_iff_of_fg K hKfg).mp hK_idem
  have hkerEq : RingHom.ker qloc.toRingHom = Ideal.span ({e} : Set E) := by
    show K = _
    simpa [Ideal.submodule_span_eq] using hKe
  let Q := E ⧸ (Ideal.span ({1 - (1 - e)} : Set E))
  let _ : IsLocalization.Away (1 - e) Q :=
    IsLocalization.Away.quotient_of_isIdempotentElem (he.one_sub)
  have hkerEq' : RingHom.ker qloc.toRingHom =
      Ideal.span ({1 - (1 - e)} : Set E) := by simpa using hkerEq
  have hEoverD : Algebra.IsStandardSmooth D E :=
    Algebra.IsStandardSmooth.localization_away (algebraMap C D d)
  have hE : Algebra.IsStandardSmooth S.R E := Algebra.IsStandardSmooth.trans S.R D E
  let F := Localization.Away (1 - e : E)
  have hFoverE : Algebra.IsStandardSmooth E F :=
    Algebra.IsStandardSmooth.localization_away (1 - e)
  have hF : Algebra.IsStandardSmooth S.R F := Algebra.IsStandardSmooth.trans S.R E F
  let equot : (E ⧸ RingHom.ker qloc.toRingHom) ≃ₐ[S.R] Q :=
    Ideal.quotientEquivAlgOfEq S.R hkerEq'
  let qtarget : (E ⧸ RingHom.ker qloc.toRingHom) ≃ₐ[S.R] Localization.Away S.a :=
    Ideal.quotientKerAlgEquivOfSurjective hqloc_surj
  let qequiv : Q ≃ₐ[S.R] Localization.Away S.a := equot.symm.trans qtarget
  let locEquiv : F ≃ₐ[S.R] Q :=
    (IsLocalization.algEquiv (Submonoid.powers (1 - e)) F Q).restrictScalars S.R
  let targetEquiv : F ≃ₐ[S.R] Localization.Away S.a := locEquiv.trans qequiv
  exact Algebra.IsStandardSmooth.of_algEquiv (R := S.R) (S := F)
    (T := Localization.Away S.a) targetEquiv

end Stacks.Smoothing

end
