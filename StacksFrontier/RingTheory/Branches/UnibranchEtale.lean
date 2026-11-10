module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra

/-!
# Geometrically unibranch local extensions are localizations of étale maps

Let `A → B` be a map of domains. If the map is a localization of a ring map of one of several
standard finite-fibre kinds, or if its fibres have no nontrivial specializations with the
stated generic-fibre condition, then every nonzero ideal of `B` has nonzero contraction to `A`.

Building on this, an injective local homomorphism from a geometrically unibranch local domain
which is essentially of finite type is a localization of an étale ring map, provided the maximal
ideal is extended from the source and the induced residue-field extension is separable.

## Main definitions

* `NoNontrivialSpecializationsInFibers` says that two comparable prime ideals in the same fibre
  are equal.

## Main results

* `comap_ne_bot_of_localization_or_discrete_fibers` (Stacks 0GS5): the contraction of every
  nonzero ideal is nonzero under any of the seven hypotheses of Stacks Tag 0GS5.
* `exists_etale_isLocalization_of_isGeometricallyUnibranch` (Stacks 0GS6): the stated local
  extension factors through an étale algebra of which the target is a localization.

## Implementation notes

The assertion that `B` is a localization of an `A`-algebra `T` includes a scalar-tower instance,
ensuring that the given map `A → B` is the composite `A → T → B`. The generic point of the
spectrum of a domain is represented by the zero ideal, and specialization of prime ideals is
represented by inclusion.

For Stacks 0GS6 the intermediate étale algebra carries a scalar-tower instance, so its composite
map to the target is the given algebra map. The equality saying that the maximal ideal of the
target is extended from the source is expressed using `Ideal.map`.

A standard étale presentation gives a surjection from a localization to the target. To show that
its source is a domain, base change along the normalization of the source domain: pure
inseparability makes the tensor product local, smoothness and localization make it normal, and
flatness gives an injection into it. The kernel then has zero contraction to the base, so the
discrete-fibre criterion of Stacks 0GS5 forces it to vanish.

## References

* [SGA 1, Exposé I, Theorem 9.5(ii)][Etale-coverings]
* [Stacks Project, Lemma 15.109.1 (0GS5)](https://stacks.math.columbia.edu/tag/0GS5)
* [Stacks Project, Tag 0GS6](https://stacks.math.columbia.edu/tag/0GS6)
-/

@[expose] public section

universe u v w x

section DiscreteGenericFibres

/-- There are no nontrivial specializations between points in any fiber of
`Spec(B) → Spec(A)`: comparable prime ideals of `B` with the same contraction are equal. -/
abbrev NoNontrivialSpecializationsInFibers
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ p q : Ideal B, p.IsPrime → q.IsPrime → p ≤ q →
    p.comap (algebraMap A B) = q.comap (algebraMap A B) → p = q

private lemma exists_ne_zero_dvd_algebraMap_of_unique_prime
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (h : ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = ⊥)
    (b : B) (hb : b ≠ 0) : ∃ a : A, a ≠ 0 ∧ b ∣ algebraMap A B a := by
  simp only [dvd_def, eq_comm, mul_comm b]
  by_contra! H
  obtain ⟨Q, hQ, hbQ, hQS⟩ := Ideal.exists_le_prime_disjoint (.span {b})
    (Algebra.algebraMapSubmonoid B (⊥ : Ideal A).primeCompl) (by
      simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
        Algebra.algebraMapSubmonoid, @forall_comm B])
  have hQ0 : Q.comap (algebraMap A B) = ⊥ := by
    refine le_antisymm (fun a ha ↦ ?_) bot_le
    by_contra ha0
    exact Set.subset_compl_iff_disjoint_right.mpr hQS
      (show algebraMap A B a ∈ Q from ha) ⟨a, ha0, rfl⟩
  have hinj : Function.Injective (algebraMap A B) := by
    obtain ⟨q, hq⟩ := h.exists
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact le_antisymm ((Ideal.comap_mono (show (⊥ : Ideal B) ≤ q from bot_le)).trans_eq hq.2)
      bot_le
  have hbot : (⊥ : Ideal B).IsPrime ∧
      (⊥ : Ideal B).comap (algebraMap A B) = ⊥ :=
    ⟨Ideal.isPrime_bot, Ideal.comap_bot_of_injective _ hinj⟩
  have hQB : Q = ⊥ := h.unique ⟨hQ, hQ0⟩ hbot
  exact hb (show b = 0 by simpa [hQB] using hbQ (Ideal.mem_span_singleton_self b))

private lemma unique_prime_over_bot_of_discrete
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (h : NoNontrivialSpecializationsInFibers A B) :
    ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = ⊥ :=
  ⟨⊥, ⟨Ideal.isPrime_bot, Ideal.comap_bot_of_injective _ hinj⟩, fun q hq ↦
    (h ⊥ q Ideal.isPrime_bot hq.1 bot_le
      ((Ideal.comap_bot_of_injective _ hinj).trans hq.2.symm)).symm⟩

private lemma discrete_of_quasiFinite
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.QuasiFinite A B] : NoNontrivialSpecializationsInFibers A B := by
  intro p q _ _ hpq heq
  exact Algebra.QuasiFinite.eq_of_le_of_under_eq p q hpq heq

private lemma discrete_of_integral
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : NoNontrivialSpecializationsInFibers A B := by
  intro p q _ _ hpq heq
  by_contra hpqne
  exact (Ideal.IsIntegral.under_lt_under (hpq.lt_of_ne hpqne)).ne heq

/-- Let `A → B` be a map of domains. Suppose that it is a localization of an étale
map; or that it is flat and a localization of an unramified, quasi-finite, or integral
map; or that it is flat and its fibers have no nontrivial specializations; or that it
maps the generic point to the generic point and its fibers have no nontrivial
specializations; or that exactly one point of `Spec(B)` maps to the generic point of
`Spec(A)`. Then every nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5]
theorem comap_ne_bot_of_localization_or_discrete_fibers
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (h :
      (∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra T B)
          (_ : IsScalarTower A T B), Algebra.Etale A T ∧
            ∃ M : Submonoid T, IsLocalization M B) ∨
      (Module.Flat A B ∧
        ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra T B)
          (_ : IsScalarTower A T B), Algebra.Unramified A T ∧
            ∃ M : Submonoid T, IsLocalization M B) ∨
      (Module.Flat A B ∧
        ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra T B)
          (_ : IsScalarTower A T B), Algebra.QuasiFinite A T ∧
            ∃ M : Submonoid T, IsLocalization M B) ∨
      (Module.Flat A B ∧
        ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra A T) (_ : Algebra T B)
          (_ : IsScalarTower A T B), Algebra.IsIntegral A T ∧
            ∃ M : Submonoid T, IsLocalization M B) ∨
      (Module.Flat A B ∧ NoNontrivialSpecializationsInFibers A B) ∨
      ((⊥ : Ideal B).comap (algebraMap A B) = ⊥ ∧
        NoNontrivialSpecializationsInFibers A B) ∨
      (∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = ⊥)) :
    ∀ J : Ideal B, J ≠ ⊥ → J.comap (algebraMap A B) ≠ ⊥ := by
  have hunique : ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = ⊥ := by
    have key (T : Type (max u v)) [CommRing T] [Algebra A T] [Algebra T B] [IsScalarTower A T B]
        [Algebra.QuasiFinite A T] (M : Submonoid T) [IsLocalization M B] [Module.Flat A B] :
        ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = ⊥ := by
      have : Algebra.QuasiFinite A B := Algebra.QuasiFinite.of_isLocalization M
      exact unique_prime_over_bot_of_discrete A B
        (FaithfulSMul.algebraMap_injective A B) (discrete_of_quasiFinite A B)
    rcases h with h | h | h | h | h | h | h
    · obtain ⟨T, _, _, _, _, _, M, _⟩ := h
      have : Module.Flat T B := IsLocalization.flat B M
      have : Module.Flat A B := Module.Flat.trans A T B
      exact key T M
    · obtain ⟨_, T, _, _, _, _, _, M, _⟩ := h
      exact key T M
    · obtain ⟨_, T, _, _, _, _, _, M, _⟩ := h
      exact key T M
    · obtain ⟨_, T, _, _, _, _, _, M, _⟩ := h
      have hdT := discrete_of_integral A T
      exact unique_prime_over_bot_of_discrete A B (FaithfulSMul.algebraMap_injective A B) (by
        intro p q hp hq hpq heq
        let e := IsLocalization.orderIsoOfPrime M B
        suffices e ⟨p, hp⟩ = e ⟨q, hq⟩ from congrArg Subtype.val (e.injective this)
        refine Subtype.ext ?_
        change p.comap (algebraMap T B) = q.comap (algebraMap T B)
        refine hdT _ _ (Ideal.IsPrime.comap _) (Ideal.IsPrime.comap _) (Ideal.comap_mono hpq) ?_
        rwa [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A T B])
    · have : Module.Flat A B := h.1
      exact unique_prime_over_bot_of_discrete A B
        (FaithfulSMul.algebraMap_injective A B) h.2
    · exact unique_prime_over_bot_of_discrete A B
        ((RingHom.injective_iff_ker_eq_bot _).2 h.1) h.2
    · exact h
  intro J hJ
  obtain ⟨b, hbJ, hb0⟩ := J.ne_bot_iff.mp hJ
  obtain ⟨a, ha0, b', hb'⟩ :=
    exists_ne_zero_dvd_algebraMap_of_unique_prime A B hunique b hb0
  intro hcomap
  have haJ : a ∈ J.comap (algebraMap A B) := by
    rw [Ideal.mem_comap, hb']
    exact J.mul_mem_right b' hbJ
  exact ha0 (by simpa [hcomap] using haJ)

end DiscreteGenericFibres

section UnibranchEtale

open IsLocalRing
open scoped TensorProduct

/-- Base change to the local normalization embeds the target in a normal local domain. -/
private theorem isDomain_of_isGeometricallyUnibranch_of_normal_tensorProduct
    {R : Type u} {B : Type v} [CommRing R] [IsLocalRing R] [IsDomain R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Module.Flat R B] (hgeom : IsGeometricallyUnibranch R)
    (hn : ∀ (C : Type u) [CommRing C] [Algebra R C],
      IsNormalRing C → IsNormalRing (B ⊗[R] C)) : IsDomain B := by
  let Rred := R ⧸ nilradical R
  let C := integralClosure Rred (FractionRing Rred)
  have hred : IsDomain Rred := hgeom.1.1
  have hC : IsLocalRing C := hgeom.1.2
  have : IsLocalRing Rred :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap R Rred) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hCint : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing Rred)
  have hCnormal : IsNormalRing C := fun p _ =>
    ⟨IsLocalization.isDomain_of_local_atPrime ‹p.IsPrime›,
      isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
        p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  have hRredC : IsLocalHom (algebraMap Rred C) :=
    ((local_hom_TFAE (algebraMap Rred C)).out 5 1).mp <| (maximal_ideal_unique Rred).unique
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rred) (maximalIdeal C)) inferInstance
  have hRC : IsLocalHom (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R Rred C]
    exact RingHom.isLocalHom_comp _ _
  have hintegral : Algebra.IsIntegral R C := Algebra.IsIntegral.trans Rred
  have hins :
      @IsPurelyInseparable (ResidueField R) (ResidueField C) _ _
        (ResidueField.map (algebraMap R C)).toAlgebra ∨
      @IsPurelyInseparable (ResidueField R) (ResidueField B) _ _
        (ResidueField.map (algebraMap R B)).toAlgebra := Or.inl (hgeom.2 hred hC)
  have hlocal : IsLocalRing (B ⊗[R] C) := (isLocalRing_tensorProduct_of_isIntegral R B C hins).1
  have hdom : IsDomain (B ⊗[R] C) := (IsNormalRing.of_isLocalRing (hn C hCnormal)).1
  have hinjred : Function.Injective (algebraMap R Rred) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    change RingHom.ker (Ideal.Quotient.mk (nilradical R)) = ⊥
    rw [Ideal.mk_ker, nilradical_eq_zero]
    rfl
  have hinjC : Function.Injective (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R Rred C]
    exact (FaithfulSMul.algebraMap_injective Rred C).comp hinjred
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C))
    (Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := B) (B := C) hinjC)

/-- The surjection from the localized étale presentation has zero kernel. -/
private lemma isLocalization_of_etale_of_exists_fraction
    (A : Type u) (C : Type w) (B : Type v)
    [CommRing A] [IsLocalRing A] [IsDomain A]
    [CommRing C] [Algebra A C] [Algebra.Etale A C]
    [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra C B]
    [IsScalarTower A C B] [IsLocalHom (algebraMap A B)]
    (hinjective : Function.Injective (algebraMap A B))
    (hgeom : IsGeometricallyUnibranch A)
    (hfrac : ∀ b : B, ∃ x s : C, IsUnit (algebraMap C B s) ∧
      b * algebraMap C B s = algebraMap C B x) :
    IsLocalization ((IsUnit.submonoid B).comap (algebraMap C B)) B := by
  let p := (maximalIdeal B).comap (algebraMap C B)
  have : p.IsPrime := Ideal.IsPrime.comap _
  let S := Localization.AtPrime p
  have hu (s : p.primeCompl) : IsUnit (algebraMap C B s) := notMem_maximalIdeal.mp s.2
  let F : S →ₐ[A] B := IsLocalization.liftAlgHom (S := S)
    (f := IsScalarTower.toAlgHom A C B) hu
  have hF (c : C) : F (algebraMap C S c) = algebraMap C B c :=
    IsLocalization.lift_eq hu c
  have hsurj : Function.Surjective F := by
    refine (IsLocalization.lift_surjective_iff hu).mpr fun b ↦ ?_
    obtain ⟨x, s, hs, he⟩ := hfrac b
    exact ⟨⟨x, ⟨s, notMem_maximalIdeal.mpr hs⟩⟩, he⟩
  have : IsLocalHom (F.toRingHom.comp (algebraMap A S)) := by
    rw [show F.toRingHom.comp (algebraMap A S) = algebraMap A B from RingHom.ext F.commutes]
    infer_instance
  have : IsLocalHom (algebraMap A S) := isLocalHom_of_comp _ F.toRingHom
  have : Module.Flat C S := IsLocalization.flat S p.primeCompl
  have : Module.Flat A S := Module.Flat.trans A C S
  have : IsDomain S := by
    refine isDomain_of_isGeometricallyUnibranch_of_normal_tensorProduct hgeom fun N _ _ hN ↦ ?_
    exact IsNormalRing.congr (Algebra.TensorProduct.comm A N S).toRingEquiv
      (Algebra.isNormalRing_tensorProduct_of_smooth_of_isLocalization A N C S hN p.primeCompl)
  have : Algebra.QuasiFinite A S := Algebra.QuasiFinite.of_isLocalization p.primeCompl
  have hAS : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinjective
    simpa only [F.commutes] using congrArg F h
  have hker : (RingHom.ker F.toRingHom).comap (algebraMap A S) = ⊥ := by
    ext a
    change F (algebraMap A S a) = 0 ↔ a = 0
    rw [F.commutes, map_eq_zero_iff _ hinjective]
  have hinj : Function.Injective F := by
    change Function.Injective F.toRingHom
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    exact comap_ne_bot_of_localization_or_discrete_fibers A S
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨Ideal.comap_bot_of_injective _ hAS, discrete_of_quasiFinite A S⟩))))))
      (RingHom.ker F.toRingHom) h hker
  let e : S ≃ₐ[C] B := AlgEquiv.ofBijective
    { F.toRingHom with commutes' := hF } ⟨hinj, hsurj⟩
  have hmon : p.primeCompl = (IsUnit.submonoid B).comap (algebraMap C B) := by
    ext c
    exact notMem_maximalIdeal
  rw [← hmon]
  exact IsLocalization.isLocalization_of_algEquiv p.primeCompl e

/-- **Stacks 0GS6.** An injective, essentially finite type local map from a geometrically
unibranch local domain is a localization of an étale map when its target maximal ideal is
extended from the source and its residue-field extension is separable. -/
@[stacks 0GS6, ega "IV 18.10.1" "(i)+(ii) ⇒ étale", sga "1 I 9.5" "(ii)"]
theorem exists_etale_isLocalization_of_isGeometricallyUnibranch
    (A : Type u) (B : Type v)
    [CommRing A] [IsLocalRing A] [IsDomain A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    (hinjective : Function.Injective (algebraMap A B))
    (hunibranch : IsGeometricallyUnibranch A)
    (hmaximal : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (hseparable : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra C B) (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.Etale A C ∧ IsLocalization M B := by
  classical
  have : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmaximal
  let D := Algebra.EssFiniteType.subalgebra A B
  let q := (maximalIdeal B).comap (algebraMap D B)
  have : q.IsPrime := Ideal.IsPrime.comap _
  have hmon : q.primeCompl = Algebra.EssFiniteType.submonoid A B := by
    ext x
    exact notMem_maximalIdeal
  have : IsLocalization.AtPrime B q := by
    change IsLocalization q.primeCompl B
    rw [hmon]
    infer_instance
  have : Algebra.IsUnramifiedAt A q :=
    Algebra.FormallyUnramified.of_equiv
      ((IsLocalization.algEquiv q.primeCompl B (Localization.AtPrime q)).restrictScalars A)
  obtain ⟨g, hg, P, π, hπ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) q
  have hgunit : IsUnit (algebraMap D B g) := notMem_maximalIdeal.mp hg
  let j : Localization.Away g →ₐ[A] B := IsLocalization.Away.liftAlgHom g
    (f := IsScalarTower.toAlgHom A D B) hgunit
  have hj (d : D) : j (algebraMap D (Localization.Away g) d) = algebraMap D B d :=
    IsLocalization.Away.lift_eq g hgunit d
  let C := ULift.{v} P.Ring
  let e : C ≃ₐ[A] P.Ring := ULift.algEquiv
  have : Algebra.Etale A C := Algebra.Etale.of_equiv e.symm
  let f : C →ₐ[A] B := j.comp (π.comp e.toAlgHom)
  let : Algebra C B := f.toAlgebra
  have : IsScalarTower A C B := IsScalarTower.of_algHom f
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    (IsUnit.submonoid B).comap (algebraMap C B), inferInstance, ?_⟩
  apply isLocalization_of_etale_of_exists_fraction A C B hinjective hunibranch
  intro b
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid A B) b
  have hlift (d : D) : ∃ c : C, algebraMap C B c = algebraMap D B d := by
    obtain ⟨c, hc⟩ := hπ (algebraMap D (Localization.Away g) d)
    refine ⟨e.symm c, ?_⟩
    change j (π (e (e.symm c))) = _
    rw [e.apply_symm_apply, hc, hj]
  obtain ⟨x', hfx⟩ := hlift x
  obtain ⟨s', hfs⟩ := hlift s
  exact ⟨x', s', hfs ▸ s.2, by rwa [hfx, hfs]⟩

end UnibranchEtale
