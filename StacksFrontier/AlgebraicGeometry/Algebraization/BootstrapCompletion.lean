module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# Completion of a bootstrap situation

A bootstrap situation completes: for a situation `S` with ring `A`, ideal `I`, module `M` and
locus `T`, the `I`-adic completion `A^∧`, the extended ideal `I A^∧`, the completed module
`M^∧` and the preimage of `T` satisfy the bootstrap assumptions with the same bounds `s`
and `d`.

Each assumption transfers for its own reason. A dualizing complex survives derived base change
to the completion (Tag 0DWD). Cohomological dimension does not increase along a ring map
(Tag 0DXA). The locus conditions are preserved because the map of spectra is continuous and
carries the adic locus into the adic locus. The strict depth bound on completed localizations
transfers because the completion of a localization of `A^∧` is canonically the completion of
the corresponding localization of `A`, and depth is invariant along that isomorphism.

## Main results

* `Stacks.Algebraization.adicCompletionLocus` — the completed locus.
* `Stacks.Algebraization.finite_adicCompletion` — the completed module is finite over the
  completed ring.
* `Stacks.Algebraization.subset_adicLocus_adicCompletion`,
  `Stacks.Algebraization.stableUnderSpecialization_adicCompletion`,
  `Stacks.Algebraization.dualizing_adicCompletion`,
  `Stacks.Algebraization.cohomologicalDimension_le_adicCompletion`,
  `Stacks.Algebraization.completedLocalDepth_adicCompletion` — the assumptions, and the two
  conditions on the locus, after completion.

## Implementation notes

Finiteness of `M^∧` over `A^∧` is read off the identification of the completion of a finite
module with its base change along `A → A^∧`; the module lives in its own universe, so that
identification is obtained after shrinking `M` to the ring's universe, which a finite module
over a Noetherian ring admits.

The comparison of the two iterated completions is a ring isomorphism of adic completions
induced by a flat map inducing an isomorphism on the quotient, together with a compatible
semilinear equivalence of modules over it; the depth computation is transported along that
pair. Depth and dimension are compared in the extended integers through `enatToEInt`, as in
the situation itself.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-! ### Completion along a flat map inducing an isomorphism on the quotient -/

/-- A flat algebra inducing an isomorphism on the quotient by `I` induces an isomorphism on
`I`-adic completions. -/
private theorem adicCompletionMap_bijective_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    [Module.Flat R S]
    (hI : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective
      (adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl) := by
  have hpow' (n : ℕ) : Function.Bijective
      (Ideal.quotientMap ((I.map (algebraMap R S)) ^ n) (algebraMap R S)
        (by rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow])) := by
    let q := (Ideal.quotEquivOfEq (Ideal.map_pow (algebraMap R S) I n)).toRingHom.comp
      (Ideal.quotientMap ((I ^ n).map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)
    have hq : q = Ideal.quotientMap ((I.map (algebraMap R S)) ^ n)
        (algebraMap R S) (by rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow]) := by
      ext x
      rfl
    rw [← hq]
    exact (Ideal.quotEquivOfEq (Ideal.map_pow (algebraMap R S) I n)).bijective.comp
      (quotientMap_pow_bijective_of_flat I hI n)
  let e (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ (I.map (algebraMap R S)) ^ n :=
    RingEquiv.ofBijective _ (hpow' n)
  have he {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
      Ideal.Quotient.factorPow (I.map (algebraMap R S)) hmn (e n x) =
        e m (Ideal.Quotient.factorPow I hmn x) := by
    induction x using Quotient.inductionOn with
    | _ x => rfl
  have hlevel (n : ℕ) (x : AdicCompletion I R) :
      AdicCompletion.evalₐ (I.map (algebraMap R S)) n
          (adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl x) =
        e n (AdicCompletion.evalₐ I n x) := by
    unfold adicCompletionMap
    rw [AdicCompletion.evalₐ_liftRingHom]
    rfl
  let inv : AdicCompletion (I.map (algebraMap R S)) S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I
      (fun n => (e n).symm.toRingHom.comp
        (AdicCompletion.evalₐ (I.map (algebraMap R S)) n).toRingHom)
      (fun {m n} hmn => by
        refine RingHom.ext fun x => (e m).injective ?_
        show e m (Ideal.Quotient.factorPow I hmn
            ((e n).symm (AdicCompletion.evalₐ (I.map (algebraMap R S)) n x))) =
          e m ((e m).symm (AdicCompletion.evalₐ (I.map (algebraMap R S)) m x))
        rw [← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        induction x using AdicCompletion.induction_on with
        | h x =>
          simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
            Ideal.Quotient.factor_mk]
          rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
          simpa [Ideal.smul_top_eq_map, neg_sub] using
            Submodule.neg_mem _ (SModEq.sub_mem.mp (x.property hmn)))
  have hleft : inv.comp (adicCompletionMap (algebraMap R S) I
      (I.map (algebraMap R S)) le_rfl) = RingHom.id _ := by
    refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [RingHom.comp_apply, AdicCompletion.evalₐ_liftRingHom, inv, RingHom.id_apply]
    show (e n).symm
      (AdicCompletion.evalₐ (I.map (algebraMap R S)) n
        (adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl x)) = _
    rw [hlevel, RingEquiv.symm_apply_apply]
  have hright : (adicCompletionMap (algebraMap R S) I
      (I.map (algebraMap R S)) le_rfl).comp inv = RingHom.id _ := by
    refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hlevel, AdicCompletion.evalₐ_liftRingHom]
    show e n ((e n).symm (AdicCompletion.evalₐ (I.map (algebraMap R S)) n x)) = _
    rw [RingEquiv.apply_symm_apply]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨inv, DFunLike.congr_fun hleft, DFunLike.congr_fun hright⟩

/-- The previous statement with the ideal of the target named separately. -/
private theorem adicCompletionMap_bijective_of_flat_of_map_eq
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (J : Ideal S) (hJ : I.map (algebraMap R S) = J)
    (h : Function.Bijective
      (Ideal.quotientMap J (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hJ.le))) :
    Function.Bijective (adicCompletionMap (algebraMap R S) I J hJ.le) := by
  subst J
  exact adicCompletionMap_bijective_of_flat I h

/-! ### Depth along a ring isomorphism -/

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Depth is invariant under a semilinear equivalence of modules over a ring isomorphism, the
ideal being carried along the isomorphism. -/
private theorem depth_eq_of_semilinearEquiv {R S M N : Type*}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (e : R ≃+* S) (f : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (I : Ideal R) : Module.depth R I M = Module.depth S (I.map e.toRingHom) N := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R N := Module.compHom N e.toRingHom
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f' : M ≃ₗ[R] N := { __ := f.toAddEquiv, map_smul' := f.map_smul' }
  exact (Module.depth_eq_depth_of_linearEquiv I f').trans
    (Module.depth_eq_depth_map_algebraMap e.surjective I N)

/-- An isomorphism of `A`-algebras induces a semilinear equivalence of base changes of an
`A`-module. -/
private noncomputable def tensorProductSemilinearEquiv
    {A B C M : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module A M]
    (e : B ≃ₐ[A] C) : B ⊗[A] M ≃ₛₗ[RingHomClass.toRingHom e.toRingEquiv] C ⊗[A] M where
  __ := (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)).toAddEquiv
  map_smul' b x := by
    change (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)) (b • x) =
      e b • (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)) x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy

/-- A ring isomorphism carries the complement of the contraction of a prime to the complement of
that prime. -/
private theorem primeCompl_map_comap_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : Ideal S) [p.IsPrime] :
    (p.comap e.toRingHom).primeCompl.map e.toMonoidHom = p.primeCompl := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    show e (e.symm x) ∉ p
    rwa [e.apply_symm_apply]

/-- Two base changes of one module along isomorphic algebras have equal depth after localizing
at corresponding primes. -/
private theorem depth_localized_baseChange_eq
    {A B C M N P : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup P] [Module A P] [Module C P] [IsScalarTower A C P]
    {f : M →ₗ[A] N} {g : M →ₗ[A] P}
    (hf : IsBaseChange B f) (hg : IsBaseChange C g) (e : B ≃ₐ[A] C)
    (p : Ideal C) [p.IsPrime] :
    Module.depth (Localization.AtPrime (p.comap e.toRingHom))
        (maximalIdeal (Localization.AtPrime (p.comap e.toRingHom)))
        (LocalizedModule (p.comap e.toRingHom).primeCompl N) =
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl P) := by
  let p₀ := p.comap e.toRingHom
  let Bp := Localization.AtPrime p₀
  let Cp := Localization.AtPrime p
  let eLoc : Bp ≃ₐ[A] Cp := IsLocalization.algEquivOfAlgEquiv Bp Cp e
    (primeCompl_map_comap_equiv e.toRingEquiv p)
  have hf' := hf.comp (IsLocalizedModule.isBaseChange p₀.primeCompl Bp
    (LocalizedModule.mkLinearMap p₀.primeCompl N))
  have hg' := hg.comp (IsLocalizedModule.isBaseChange p.primeCompl Cp
    (LocalizedModule.mkLinearMap p.primeCompl P))
  let E := (hf'.equiv.symm.trans (tensorProductSemilinearEquiv eLoc)).trans hg'.equiv
  have h := depth_eq_of_semilinearEquiv eLoc.toRingEquiv E (maximalIdeal Bp)
  rwa [IsLocalRing.map_maximalIdeal_of_surjective eLoc.toRingEquiv.toRingHom
    eLoc.surjective] at h

/-! ### Primes and maximal ideals along a ring isomorphism -/

/-- A flat local homomorphism inducing a surjection on the quotients by an ideal contained in the
maximal ideal and its extension carries the maximal ideal onto the maximal ideal. -/
private theorem map_maximalIdeal_eq_of_quotientMap_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (J : Ideal S) (hJ : I.map (algebraMap R S) = J)
    (h : Function.Surjective
      (Ideal.quotientMap J (algebraMap R S) (Ideal.map_le_iff_le_comap.mp hJ.le))) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  subst J
  apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
  intro b hb
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hsub : algebraMap R S a - b ∈ I.map (algebraMap R S) := by
    rwa [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
  have hsub' := Ideal.map_mono hI hsub
  have hfa : algebraMap R S a ∈ maximalIdeal S := by
    simpa using (maximalIdeal S).add_mem (IsLocalRing.map_maximalIdeal_le _ hsub') hb
  have ha' : a ∈ maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)]
    exact hfa
  simpa using ((maximalIdeal R).map (algebraMap R S)).sub_mem
    (Ideal.mem_map_of_mem _ ha') hsub'

/-- The set of primes above two given ideals is a singleton if and only if its image under a
ring isomorphism is, the singleton being transported along the isomorphism. -/
private theorem primesAbove_eq_singleton_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (I m : Ideal R) (p : Ideal S)
    (h : {r : Ideal S | r.IsPrime ∧ p ≤ r ∧ I.map e.toRingHom ≤ r} = {m.map e.toRingHom}) :
    {r : Ideal R | r.IsPrime ∧ p.comap e.toRingHom ≤ r ∧ I ≤ r} = {m} := by
  have hmapcomap (J : Ideal S) : (J.comap e.toRingHom).map e.toRingHom = J :=
    Ideal.map_comap_of_surjective _ e.surjective J
  have hcomapmap (J : Ideal R) : (J.map e.toRingHom).comap e.toRingHom = J :=
    Ideal.comap_map_of_bijective _ e.bijective
  ext r
  constructor
  · rintro ⟨hr, hp, hI⟩
    have hmem : r.map e.toRingHom ∈
        {r : Ideal S | r.IsPrime ∧ p ≤ r ∧ I.map e.toRingHom ≤ r} := by
      refine ⟨?_, ?_, Ideal.map_mono hI⟩
      · show (r.map e).IsPrime
        rw [← Ideal.comap_symm e]
        exact hr.comap _
      · simpa only [hmapcomap] using Ideal.map_mono (f := e.toRingHom) hp
    rw [h] at hmem
    have heq := congrArg (Ideal.comap e.toRingHom) (Set.mem_singleton_iff.mp hmem)
    simpa only [hcomapmap, Set.mem_singleton_iff] using heq
  · intro hr
    have : r = m := hr
    subst r
    have hmem : m.map e.toRingHom ∈
        {r : Ideal S | r.IsPrime ∧ p ≤ r ∧ I.map e.toRingHom ≤ r} := by
      rw [h]
      exact Set.mem_singleton _
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcomapmap] using hmem.1.comap e.toRingHom
    · simpa only [hcomapmap] using Ideal.comap_mono (f := e.toRingHom) hmem.2.1
    · simpa only [hcomapmap] using Ideal.comap_mono (f := e.toRingHom) hmem.2.2

/-! ### The completed situation -/

/-- The completion of a finite module over a Noetherian ring is its base change along the
completion of the ring. -/
private theorem isBaseChange_adicCompletion {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsBaseChange (AdicCompletion I A) (AdicCompletion.of I M) := by
  let B := AdicCompletion I A
  let : Small.{u} M := Module.Finite.small A M
  let M₀ := Shrink.{u} M
  let eM : M₀ ≃ₗ[A] M := Shrink.linearEquiv A M
  let : Module A (AdicCompletion I M₀) :=
    Module.compHom (AdicCompletion I M₀) (algebraMap A B)
  let : IsScalarTower A B (AdicCompletion I M₀) :=
    ⟨fun a b x => mul_smul (algebraMap A B a) b x⟩
  have hsmall : IsBaseChange B (AdicCompletion.of I M₀) :=
    IsBaseChange.of_equiv
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀)
      (by
        intro x
        show (AdicCompletion.ofTensorProduct I M₀) (1 ⊗ₜ[A] x) = _
        rw [AdicCompletion.ofTensorProduct_tmul, one_smul])
  exact (IsBaseChange.iff_of_equiv_comm eM (AdicCompletion.congr I eM)
    (LinearMap.ext fun x => (AdicCompletion.map_of I eM.toLinearMap x).symm)).mp hsmall

/-- **Stacks Project, Tag 0EFV (completion).** The completed module of a bootstrap situation is
finite over the completed ring. -/
@[stacks 0EFV "completion"]
public theorem finite_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.M) :=
  (inferInstance :
      Module.Finite (AdicCompletion S.I S.A) (AdicCompletion S.I S.A ⊗[S.A] S.M)).equiv
    (isBaseChange_adicCompletion S.I S.M).equiv

/-- The locus of the completed situation: the preimage of `T` under the map of spectra. -/
public abbrev adicCompletionLocus (S : BootstrapSituation.{u, v, w}) :
    Set (PrimeSpectrum (AdicCompletion S.I S.A)) :=
  (PrimeSpectrum.comap (algebraMap S.A (AdicCompletion S.I S.A))) ⁻¹' S.T

/-- **Stacks Project, Tag 0EFV (completion).** The completed locus is contained in the adic
locus of the extended ideal. -/
@[stacks 0EFV "completion"]
public theorem subset_adicLocus_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    adicCompletionLocus S ⊆ PrimeSpectrum.zeroLocus
      ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))) :
        Set (AdicCompletion S.I S.A)) :=
  fun _ hp => (Ideal.map_le_iff_le_comap).2 (S.subset_adicLocus hp)

/-- **Stacks Project, Tag 0EFV (completion).** The completed locus is stable under
specialization. -/
@[stacks 0EFV "completion"]
public theorem stableUnderSpecialization_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    StableUnderSpecialization (adicCompletionLocus S) :=
  S.stableUnderSpecialization.preimage (PrimeSpectrum.continuous_comap _)

/-- **Stacks Project, Tag 0EFV (completion).** Assumption (1) completes: the adic completion of
a ring with a dualizing complex has one. -/
@[stacks 0EFV "completion"]
public theorem dualizing_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    ∃ K : DerivedCategory (ModuleCat.{max u w} (AdicCompletion S.I S.A)),
      Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := S.dualizing
  exact ⟨_, Dualizing.isDualizingComplex_adicCompletion S.I K hK⟩

/-- **Stacks Project, Tag 0EFV (completion).** Assumption (3) completes: cohomological dimension
does not increase. -/
@[stacks 0EFV "completion"]
public theorem cohomologicalDimension_le_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    Stacks.LocalCohomology.cohomologicalDimension (AdicCompletion S.I S.A)
      (S.I.map (algebraMap S.A (AdicCompletion S.I S.A)))
      (Ideal.fg_of_isNoetherianRing _) ≤ S.d :=
  (Stacks.LocalCohomology.cohomologicalDimension_map_le
    (algebraMap S.A (AdicCompletion S.I S.A)) S.I
    (Ideal.fg_of_isNoetherianRing S.I)).trans S.cohomologicalDimension_le

/-- **Stacks Project, Tag 0EFV (completion).** Assumption (6) completes: the strict depth bound
on completed localizations persists after adic completion. -/
@[stacks 0EFV "completion"]
public theorem completedLocalDepth_adicCompletion (S : BootstrapSituation.{u, v, w}) :
    ∀ q : PrimeSpectrum (AdicCompletion S.I S.A), q ∈ adicCompletionLocus S →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := (S.I.map (algebraMap S.A (AdicCompletion S.I S.A))).map
        (algebraMap (AdicCompletion S.I S.A) Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl (AdicCompletion S.I S.M)
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
        enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) >
          (S.s : EInt) := by
  intro q hq
  let A' := AdicCompletion S.I S.A
  let I' := S.I.map (algebraMap S.A A')
  let M' := AdicCompletion S.I S.M
  have : Module.Finite A' M' := finite_adicCompletion S
  change PrimeSpectrum.comap (algebraMap S.A A') q ∈ S.T at hq
  let q₀ := PrimeSpectrum.comap (algebraMap S.A A') q
  have hq₀ : q₀ ∈ S.T := hq
  have hI₀ : S.I ≤ q₀.asIdeal := S.subset_adicLocus hq₀
  have hI₁ : I' ≤ q.asIdeal := (Ideal.map_le_iff_le_comap).2 hI₀
  let R₀ := Localization.AtPrime q₀.asIdeal
  let R₁ := Localization.AtPrime q.asIdeal
  let I₀ := S.I.map (algebraMap S.A R₀)
  let I₁ := I'.map (algebraMap A' R₁)
  let M₀ := LocalizedModule q₀.asIdeal.primeCompl S.M
  let M₁ := LocalizedModule q.asIdeal.primeCompl M'
  let qbar₀ := q₀.asIdeal.map (Ideal.Quotient.mk S.I)
  let qbar₁ := q.asIdeal.map (Ideal.Quotient.mk I')
  let e₀ : S.A ⧸ S.I ≃+* A' ⧸ I' :=
    ((Ideal.quotEquivOfEq
        (AdicCompletion.ker_evalOneₐ_eq_map S.I
          (Ideal.fg_of_isNoetherianRing S.I)).symm).trans
      ((AdicCompletion.evalOneₐ S.I).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.evalOneₐ_surjective S.I))).symm
  have he₀ (a : S.A) :
      e₀ (Ideal.Quotient.mk S.I a) = Ideal.Quotient.mk I' (algebraMap S.A A' a) := by
    apply e₀.symm.injective
    rw [RingEquiv.symm_apply_apply]
    show Ideal.Quotient.mk S.I a = AdicCompletion.evalOneₐ S.I (algebraMap S.A A' a)
    exact (DFunLike.congr_fun (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk
      (I := S.I)) a).symm
  have hqbar₀ : qbar₀.comap (Ideal.Quotient.mk S.I) = q₀.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    apply sup_eq_left.mpr
    intro x hx
    change Ideal.Quotient.mk S.I x = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    exact (SetLike.le_def.mp hI₀) hx
  have hqbar₁ : qbar₁.comap (Ideal.Quotient.mk I') = q.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    apply sup_eq_left.mpr
    intro x hx
    change Ideal.Quotient.mk I' x = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    exact (SetLike.le_def.mp hI₁) hx
  have hqbar : qbar₁.comap e₀.toRingHom = qbar₀ := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show e₀ (Ideal.Quotient.mk S.I a) ∈ qbar₁ ↔ Ideal.Quotient.mk S.I a ∈ qbar₀
    rw [he₀]
    have hleft : Ideal.Quotient.mk I' (algebraMap S.A A' a) ∈ qbar₁ ↔
        algebraMap S.A A' a ∈ q.asIdeal := by
      rw [← Ideal.mem_comap, hqbar₁]
    have hright : Ideal.Quotient.mk S.I a ∈ qbar₀ ↔ a ∈ q₀.asIdeal := by
      rw [← Ideal.mem_comap, hqbar₀]
    rw [hleft, hright]
    rfl
  let : qbar₀.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hI₀
  let : qbar₁.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hI₁
  let : q.asIdeal.LiesOver q₀.asIdeal := ⟨rfl⟩
  let : Algebra R₀ R₁ := Localization.AtPrime.algebraOfLiesOver _ _
  let : IsLocalization.AtPrime (R₀ ⧸ I₀) qbar₀ :=
    isLocalization_atPrime_quotient q₀.asIdeal R₀ S.I qbar₀ hqbar₀
  let : IsLocalization.AtPrime (R₁ ⧸ I₁) qbar₁ :=
    isLocalization_atPrime_quotient q.asIdeal R₁ I' qbar₁ hqbar₁
  let : Algebra (S.A ⧸ S.I) (R₁ ⧸ I₁) :=
    ((algebraMap (A' ⧸ I') (R₁ ⧸ I₁)).comp e₀.toRingHom).toAlgebra
  have hsub : Submonoid.map e₀ qbar₀.primeCompl = qbar₁.primeCompl := by
    have hcompl : qbar₀.primeCompl = (qbar₁.comap e₀.toRingHom).primeCompl := by
      ext x
      show x ∉ qbar₀ ↔ x ∉ qbar₁.comap e₀.toRingHom
      rw [hqbar]
    rw [hcompl]
    exact primeCompl_map_comap_equiv e₀ qbar₁
  let : IsLocalization qbar₀.primeCompl (R₁ ⧸ I₁) :=
    IsLocalization.of_ringEquiv_left e₀ hsub (fun _ => rfl)
  let eLoc : (R₀ ⧸ I₀) ≃ₐ[S.A ⧸ S.I] (R₁ ⧸ I₁) :=
    IsLocalization.algEquiv qbar₀.primeCompl (R₀ ⧸ I₀) (R₁ ⧸ I₁)
  have hmaps : (algebraMap R₀ R₁).comp (algebraMap S.A R₀) =
      (algebraMap A' R₁).comp (algebraMap S.A A') := by
    apply RingHom.ext
    intro a
    show Localization.localRingHom q₀.asIdeal q.asIdeal
        (algebraMap S.A A') Ideal.LiesOver.over (algebraMap S.A R₀ a) = _
    rw [Localization.localRingHom_to_map]
    rfl
  have hle : I₀ ≤ I₁.comap (algebraMap R₀ R₁) := by
    rw [← Ideal.map_le_iff_le_comap]
    dsimp only [I₀, I₁, I']
    rw [Ideal.map_map, Ideal.map_map, hmaps]
  have hquot : Function.Bijective (Ideal.quotientMap I₁ (algebraMap R₀ R₁) hle) := by
    have heq : Ideal.quotientMap I₁ (algebraMap R₀ R₁) hle = eLoc.toRingHom := by
      apply IsLocalization.ringHom_ext qbar₀.primeCompl
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show (Ideal.quotientMap I₁ (algebraMap R₀ R₁) hle)
          (algebraMap (S.A ⧸ S.I) (R₀ ⧸ I₀) (Ideal.Quotient.mk S.I a)) =
        eLoc (algebraMap (S.A ⧸ S.I) (R₀ ⧸ I₀) (Ideal.Quotient.mk S.I a))
      rw [eLoc.commutes]
      show Ideal.Quotient.mk I₁ (algebraMap R₀ R₁ (algebraMap S.A R₀ a)) =
        algebraMap (A' ⧸ I') (R₁ ⧸ I₁) (e₀ (Ideal.Quotient.mk S.I a))
      rw [he₀]
      exact congrArg (Ideal.Quotient.mk I₁) (DFunLike.congr_fun hmaps a)
    rw [heq]
    exact eLoc.bijective
  have hIeq : I₀.map (algebraMap R₀ R₁) = I₁ := by
    dsimp only [I₀, I₁, I']
    rw [Ideal.map_map, Ideal.map_map, hmaps]
  have : Module.Flat S.A A' := AdicCompletion.flat_of_isNoetherian S.I
  have : Module.Flat S.A R₁ := Module.Flat.trans S.A A' R₁
  have : Module.Flat R₀ R₁ :=
    (Module.flat_iff_of_isLocalization R₀ q₀.asIdeal.primeCompl R₁).mpr inferInstance
  let C₀ := AdicCompletion I₀ R₀
  let C₁ := AdicCompletion I₁ R₁
  let fc : C₀ →+* C₁ := adicCompletionMap (algebraMap R₀ R₁) I₀ I₁ hIeq.le
  have hfc : Function.Bijective fc :=
    adicCompletionMap_bijective_of_flat_of_map_eq I₀ I₁ hIeq hquot
  let eC : C₀ ≃+* C₁ := RingEquiv.ofBijective fc hfc
  have hfccomp : fc.comp (algebraMap R₀ C₀) = (algebraMap R₁ C₁).comp (algebraMap R₀ R₁) :=
    adicCompletionMap_comp_algebraMap _ _ _ _
  let eCA : C₀ ≃ₐ[S.A] C₁ :=
    { __ := eC
      commutes' := by
        intro a
        show fc (algebraMap S.A C₀ a) = algebraMap S.A C₁ a
        have h := DFunLike.congr_fun hfccomp (algebraMap S.A R₀ a)
        simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply S.A R₀ C₀,
          ← IsScalarTower.algebraMap_apply S.A R₀ R₁,
          ← IsScalarTower.algebraMap_apply S.A R₁ C₁] using h }
  have hmapI : (I₀.map (algebraMap R₀ C₀)).map eC.toRingHom = I₁.map (algebraMap R₁ C₁) := by
    rw [Ideal.map_map]
    show I₀.map (fc.comp (algebraMap R₀ C₀)) = _
    rw [hfccomp, ← Ideal.map_map, hIeq]
  have hImax : I₀ ≤ maximalIdeal R₀ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q₀.asIdeal R₀]
    exact Ideal.map_mono hI₀
  have hmax : (maximalIdeal R₀).map (algebraMap R₀ R₁) = maximalIdeal R₁ :=
    map_maximalIdeal_eq_of_quotientMap_surjective I₀ hImax I₁ hIeq hquot.surjective
  have hmapm : ((maximalIdeal R₀).map (algebraMap R₀ C₀)).map eC.toRingHom =
      (maximalIdeal R₁).map (algebraMap R₁ C₁) := by
    rw [Ideal.map_map]
    show (maximalIdeal R₀).map (fc.comp (algebraMap R₀ C₀)) = _
    rw [hfccomp, ← Ideal.map_map, hmax]
  have : IsScalarTower S.A C₀ (AdicCompletion I₀ M₀) :=
    IsScalarTower.to₁₃₄ S.A R₀ C₀ (AdicCompletion I₀ M₀)
  have : IsScalarTower S.A C₁ (AdicCompletion I₁ M₁) :=
    IsScalarTower.to₁₃₄ S.A R₁ C₁ (AdicCompletion I₁ M₁)
  have hM₀ := (IsLocalizedModule.isBaseChange q₀.asIdeal.primeCompl R₀
    (LocalizedModule.mkLinearMap q₀.asIdeal.primeCompl S.M)).comp
      (isBaseChange_adicCompletion I₀ M₀)
  have hM₁ := ((isBaseChange_adicCompletion S.I S.M).comp
    (IsLocalizedModule.isBaseChange q.asIdeal.primeCompl R₁
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))).comp
        (isBaseChange_adicCompletion I₁ M₁)
  dsimp only
  intro p hp hprimes
  let p₀ : PrimeSpectrum C₀ := PrimeSpectrum.comap eC.toRingHom p
  have hp₀ : ¬ I₀.map (algebraMap R₀ C₀) ≤ p₀.asIdeal := by
    intro h
    apply hp
    rw [← hmapI]
    exact Ideal.map_le_iff_le_comap.mpr h
  have hprimes₀ :
      {r : Ideal C₀ | r.IsPrime ∧ p₀.asIdeal ≤ r ∧ I₀.map (algebraMap R₀ C₀) ≤ r} =
      {(maximalIdeal R₀).map (algebraMap R₀ C₀)} := by
    apply primesAbove_eq_singleton_of_ringEquiv eC
    simpa only [hmapI, hmapm] using hprimes
  have hdepth := S.completedLocalDepth q₀ hq₀ p₀ hp₀ hprimes₀
  have hdepthEq := depth_localized_baseChange_eq hM₀ hM₁ eCA p.asIdeal
  exact (congrArg enatToEInt hdepthEq) ▸ hdepth

end Stacks.Algebraization
