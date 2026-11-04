module

public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Data.Finset.Card
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuasiFinite.Weakly
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Nilpotent.Ideal
import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.MinimalPrimesDirectLimit
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.AnalyticallyUnramified
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.IntegralClosure
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

@[expose] public section

/-!
# Comparing the henselization and the completion of a local ring

Let `A` be a Noetherian local ring with completion `Â` and henselization `Aʰ`. This file builds
the comparison maps `Aʰ → Â` (local and flat), algebraizes ideals of `Â` along them, and shows
that every one-dimensional formal branch of `A` already appears on `Aʰ`.

## Main results

* `isLocalHom_of_isHenselization_algHom`: an algebra map from a henselization to a local ring is
  a local homomorphism.
* `exists_algHom_adicCompletion_of_map_le`: maps out of a henselization into the completion.
* `exists_minimalPrime_henselization_radical_map_eq_of_quotient_dimension_one`: a minimal prime
  of `Â` cutting out a one-dimensional component is the radical of the extension of a minimal
  prime of `Aʰ`.

## References

* [The Stacks Project, Tag 0C2B](https://stacks.math.columbia.edu/tag/0C2B)
-/

universe u v w x y

open Topology
open IsLocalRing
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

private theorem radical_ker_atPrime_eq {R : Type*} [CommRing R]
    (q : Ideal R) [q.IsPrime] (hq : q ∈ minimalPrimes R) :
    (RingHom.ker (algebraMap R (Localization.AtPrime q))).radical = q := by
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime q) q (⊥ : Ideal R) hq
  rw [Ideal.map_bot] at h
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, h]
  exact Ideal.under_map_of_isLocalizationAtPrime q le_rfl

private theorem eq_maximalIdeal_of_lt_of_quotient_dimension_le_one
    {R : Type*} [CommRing R] [IsLocalRing R]
    (q p : Ideal R) [q.IsPrime] [p.IsPrime]
    (hdim : ringKrullDim (R ⧸ q) ≤ 1) (hqp : q < p) :
    p = maximalIdeal R := by
  have : Ring.KrullDimLE 1 (R ⧸ q) := Ring.krullDimLE_iff.mpr hdim
  have hker : RingHom.ker (Ideal.Quotient.mk q) ≤ p := by
    simpa only [Ideal.mk_ker] using hqp.le
  have hp : (p.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hn : p.map (Ideal.Quotient.mk q) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact not_le_of_gt hqp
  have hm := hp.isMaximal_of_ne_bot hn
  have hcomap : (p.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqp.le]
  exact eq_maximalIdeal (hcomap ▸
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective)

/-- The conormal module of a minimal prime cutting out a one-dimensional component is
annihilated by a power of the maximal ideal: it is supported at the maximal ideal only. -/
private theorem exists_maximalIdeal_pow_smul_cotangent_eq_bot
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (q : Ideal R) [q.IsPrime] (hq : q ∈ minimalPrimes R)
    (hdim : ringKrullDim (R ⧸ q) ≤ 1) :
    let J := RingHom.ker (algebraMap R (Localization.AtPrime q))
    ∃ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R J.Cotangent) = ⊥ := by
  dsimp only
  let J := RingHom.ker (algebraMap R (Localization.AtPrime q))
  have : Module.Finite R J := Module.Finite.of_fg J.fg_of_isNoetherianRing
  have : Module.Finite R J.Cotangent :=
    Module.Finite.of_surjective J.toCotangent J.toCotangent_surjective
  have hrad : J.radical = q := radical_ker_atPrime_eq q hq
  have hJ : J ≤ Module.annihilator R J.Cotangent := by
    intro x hx
    exact Module.mem_annihilator.mpr (Ideal.Cotangent.smul_eq_zero_of_mem hx)
  have hsupport : (⟨q, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R J.Cotangent := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective z
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl
      (Localization.AtPrime q) (x : R)).mp x.property
    refine ⟨s, s.property, ?_⟩
    rw [← map_smul, Ideal.toCotangent_eq_zero]
    show (s : R) * (x : R) ∈ J ^ 2
    rw [hs]
    exact Ideal.zero_mem _
  have hle : maximalIdeal R ≤ (Module.annihilator R J.Cotangent).radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro p ⟨hap, hp⟩
    have hqp : q ≤ p := by
      rw [← hrad]
      exact hp.radical_le_iff.mpr (hJ.trans hap)
    have hne : q ≠ p := by
      rintro rfl
      exact hsupport (Module.mem_support_iff_of_finite.mpr hap)
    rw [eq_maximalIdeal_of_lt_of_quotient_dimension_le_one q p hdim
      (lt_of_le_of_ne hqp hne)]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (maximalIdeal R).fg_of_isNoetherianRing
  refine ⟨n, le_antisymm ?_ bot_le⟩
  rw [Submodule.smul_le]
  intro r hr z _
  exact (Module.mem_annihilator.mp (hn hr)) z

/-- If the conormal module of an ideal of the completion is annihilated by a power of the
maximal ideal, then the quotient is the completion of a finite-type algebra. -/
theorem exists_finiteType_completion_quotient
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (J : Ideal (AdicCompletion (maximalIdeal A) A)) (n : ℕ)
    (hn : maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n •
      (⊤ : Submodule (AdicCompletion (maximalIdeal A) A) J.Cotangent) = ⊥) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.FiniteType A D ∧
        Nonempty ((AdicCompletion (maximalIdeal A) A ⧸ J) ≃ₐ[A]
          AdicCompletion ((maximalIdeal A).map (algebraMap A D)) D) := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  have hn' : maximalIdeal A ^ n • (⊤ : Submodule A J.Cotangent) = ⊥ := by
    have hm := AdicCompletion.maximalIdeal_eq_map_of_fg
      (maximalIdeal A).fg_of_isNoetherianRing
    rw [hm, ← Ideal.map_pow] at hn
    simpa only [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top,
      Submodule.restrictScalars_bot] using congrArg (Submodule.restrictScalars A) hn
  have aux (I : Ideal A) (hI : I = maximalIdeal A) :
      ∃ φ : AdicCompletion I A →ₐ[A] Ahat ⧸ J,
        Function.Surjective φ ∧
          maximalIdeal A ^ n •
            (⊤ : Submodule A (RingHom.ker φ.toRingHom).Cotangent) = ⊥ := by
    subst I
    refine ⟨Ideal.Quotient.mkₐ A J, Ideal.Quotient.mk_surjective, ?_⟩
    show maximalIdeal A ^ n •
      (⊤ : Submodule A (RingHom.ker (Ideal.Quotient.mk J)).Cotangent) = ⊥
    have hcot (K : Ideal Ahat) (hK : K = J) :
        maximalIdeal A ^ n • (⊤ : Submodule A K.Cotangent) = ⊥ := by
      subst K
      exact hn'
    exact hcot _ (Ideal.mk_ker)
  obtain ⟨φ, hφ, hcot⟩ := aux ((maximalIdeal A).map (algebraMap A A)) (by simp)
  exact exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated
    A A (Ahat ⧸ J) (maximalIdeal A) φ hφ n hcot

private theorem exists_minimalPrime_radical_map_eq_of_extended_ideal
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (q J : Ideal S) (hq : q ∈ minimalPrimes S) (hJ : J.radical = q)
    (I : Ideal R) (hI : I.map f = J) :
    ∃ p ∈ minimalPrimes R, q = (p.map f).radical := by
  have : q.IsPrime := hq.isPrime
  have hIle : I ≤ q.comap f :=
    Ideal.map_le_iff_le_comap.mp (hI.le.trans (Ideal.le_radical.trans_eq hJ))
  refine ⟨q.comap f, comap_mem_minimalPrimes_of_flat f hf hq, le_antisymm ?_ ?_⟩
  · calc
      q = J.radical := hJ.symm
      _ ≤ ((q.comap f).map f).radical :=
        Ideal.radical_mono (hI ▸ Ideal.map_mono hIle)
  · exact hq.isPrime.radical_le_iff.mpr Ideal.map_comap_le

/-- An ind-étale algebra is formally étale. -/
private theorem formallyEtale_of_ind_etale (R : Type u) (S : Type (max u v))
    [CommRing R] [CommRing S]
    [Algebra R S] (h : (CommAlgCat.etale.{max u v} R).ind.{max u v} (CommAlgCat.of R S)) :
    Algebra.FormallyEtale R S := by
  obtain ⟨J, _, _, pres, het⟩ := h
  rw [Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth]
  constructor
  · rw [Algebra.FormallyUnramified.iff_comp_injective]
    intro B _ _ I hI g₁ g₂ hg
    have heq : CommAlgCat.ofHom g₁ = CommAlgCat.ofHom g₂ := by
      apply pres.isColimit.hom_ext
      intro i
      apply CommAlgCat.hom_ext
      apply Algebra.FormallyUnramified.lift_unique I ⟨2, by rw [hI]; rfl⟩
      exact congrArg (fun q => q.comp (pres.ι.app i).hom) hg
    exact congrArg CommAlgCat.Hom.hom heq
  · rw [Algebra.FormallySmooth.iff_comp_surjective]
    intro B _ _ I hI g
    have hnil : IsNilpotent I := ⟨2, by rw [hI]; rfl⟩
    have hfe (i : J) : Algebra.FormallyEtale R (pres.diag.obj i) :=
      (Algebra.formallyEtale_iff_etale R _ (het i).2).2 (het i)
    have hfs (i : J) : Algebra.FormallySmooth R (pres.diag.obj i) :=
      let _ := hfe i
      inferInstance
    choose f hf using fun i => by
      let : Algebra.FormallySmooth R (pres.diag.obj i) := hfs i
      exact Algebra.FormallySmooth.exists_lift I hnil (g.comp (pres.ι.app i).hom)
    let c : Cocone pres.diag :=
      { pt := CommAlgCat.of R B
        ι :=
          { app := fun i => CommAlgCat.ofHom (f i)
            naturality := by
              intro i j φ
              apply CommAlgCat.hom_ext
              simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, Functor.const_obj_obj,
                Functor.const_obj_map, CommAlgCat.hom_id]
              apply Algebra.FormallyUnramified.lift_unique (A := pres.diag.obj i) I hnil
              simp only [AlgHom.id_comp]
              rw [← AlgHom.comp_assoc, hf j, hf i, AlgHom.comp_assoc]
              exact congrArg (fun q => g.comp q)
                (congrArg CommAlgCat.Hom.hom (pres.ι.naturality φ)) } }
    refine ⟨(pres.isColimit.desc c).hom, ?_⟩
    have heq : CommAlgCat.ofHom ((Ideal.Quotient.mkₐ R I).comp (pres.isColimit.desc c).hom) =
        CommAlgCat.ofHom g := by
      apply pres.isColimit.hom_ext
      intro i
      apply CommAlgCat.hom_ext
      simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
      have hd : (pres.isColimit.desc c).hom.comp (pres.ι.app i).hom = f i :=
        congrArg CommAlgCat.Hom.hom (pres.isColimit.fac c i)
      rw [AlgHom.comp_assoc, hd, hf i]
    exact congrArg CommAlgCat.Hom.hom heq

/-- Every henselization of a local ring `A` admits an `A`-algebra map to the completion of
`A`. -/
theorem exists_algHom_adicCompletion_of_isHenselization
    (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    Nonempty (Ah →ₐ[A] AdicCompletion (maximalIdeal A) A) := by
  have : Algebra.FormallyEtale A (ULift.{u} Ah) :=
    formallyEtale_of_ind_etale A (ULift.{u} Ah)
      (IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah))
  have : Algebra.FormallyEtale A Ah :=
    Algebra.FormallyEtale.of_equiv (ULift.algEquiv : ULift.{u} Ah ≃ₐ[A] Ah)
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv
    (R := A) (L := ResidueField A) (Rh := Ah)
  let φ : Ah →ₐ[A] ResidueField A :=
    { __ := e.symm.toRingHom.comp (residue Ah)
      commutes' := fun x => by
        show e.symm (residue Ah (algebraMap A Ah x)) = residue A x
        rw [← he x]
        simp }
  obtain ⟨f, _⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq φ
  exact ⟨f⟩

private theorem surjective_algebraMap_of_surjective_adicCompletion
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) (hI : I.FG) (φ : AdicCompletion I A →ₐ[A] C)
    (hφ : Function.Surjective φ) (hzero : I.map (algebraMap A C) = ⊥) :
    Function.Surjective (algebraMap A C) := by
  have hker : I.map (algebraMap A (AdicCompletion I A)) ≤ RingHom.ker φ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show φ (algebraMap A (AdicCompletion I A) r) = 0
    rw [φ.commutes]
    exact (Ideal.map_eq_bot_iff_le_ker _).mp hzero hr
  intro c
  obtain ⟨x, rfl⟩ := hφ c
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
  refine ⟨a, ?_⟩
  have hx : x - algebraMap A (AdicCompletion I A) a ∈
      I.map (algebraMap A (AdicCompletion I A)) := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI, RingHom.mem_ker, map_sub]
    show AdicCompletion.evalOneₐ I x - Ideal.Quotient.mk I a = 0
    rw [ha, sub_self]
  have hz := hker hx
  change φ (x - algebraMap A (AdicCompletion I A) a) = 0 at hz
  rw [map_sub, φ.commutes, sub_eq_zero] at hz
  exact hz.symm

/-- An `A`-algebra map from a henselization of `A` to a local `A`-algebra whose structure map is
local is a local homomorphism. -/
public theorem isLocalHom_of_isHenselization_algHom
    {A : Type u} {Ah : Type v} {B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [CommRing B] [IsLocalRing B] [Algebra A Ah] [Algebra A B]
    [IsHenselization A (ResidueField A) Ah] [IsLocalHom (algebraMap A B)]
    (f : Ah →ₐ[A] B) : IsLocalHom f.toRingHom := by
  have hm : (maximalIdeal Ah).map f.toRingHom =
      (maximalIdeal A).map (algebraMap A B) := by
    rw [← IsHenselization.map_maximalIdeal (R := A) (L := ResidueField A), Ideal.map_map]
    exact congrArg (fun g : A →+* B => (maximalIdeal A).map g) f.comp_algebraMap
  have hle : (maximalIdeal Ah).map f.toRingHom ≤ maximalIdeal B := by
    rw [hm, Ideal.map_le_iff_le_comap, maximalIdeal_comap]
  exact ((local_hom_TFAE f.toRingHom).out 4 1).mp
    (fun x hx => hle (Ideal.mem_map_of_mem _ hx))

private theorem map_algebraMap_quotient_map_eq_bot {A D : Type*} [CommRing A] [CommRing D]
    [Algebra A D] (I : Ideal A) : I.map (algebraMap A (D ⧸ I.map (algebraMap A D))) = ⊥ := by
  rw [IsScalarTower.algebraMap_eq A D (D ⧸ I.map (algebraMap A D)), ← Ideal.map_map]
  exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by simp)

private theorem surjective_quotient_algebraMap_of_surjective_adicCompletion
    {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    (I : Ideal A) (hI : I.FG)
    (φ : AdicCompletion I A →ₐ[A] AdicCompletion (I.map (algebraMap A D)) D)
    (hφ : Function.Surjective φ) :
    Function.Surjective (algebraMap A (D ⧸ I.map (algebraMap A D))) := by
  apply surjective_algebraMap_of_surjective_adicCompletion I hI
    (((AdicCompletion.evalOneₐ (I.map (algebraMap A D))).restrictScalars A).comp φ)
    ((AdicCompletion.evalOneₐ_surjective _).comp hφ)
  exact map_algebraMap_quotient_map_eq_bot I

private theorem ne_top_of_nontrivial_adicCompletion
    {R : Type*} [CommRing R] (I : Ideal R) [Nontrivial (AdicCompletion I R)] : I ≠ ⊤ := by
  intro h
  subst I
  have : Subsingleton (AdicCompletion (⊤ : Ideal R) R) :=
    (AdicCompletion.isAdicComplete (M := R) (show (⊤ : Ideal R).FG by
      rw [← Ideal.span_singleton_one]
      exact Submodule.fg_span_singleton 1)).subsingleton
  exact zero_ne_one (Subsingleton.elim (0 : AdicCompletion (⊤ : Ideal R) R) 1)

private theorem isMaximal_map_of_surjective_quotient_algebraMap
    {A D : Type*} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]
    (hne : (maximalIdeal A).map (algebraMap A D) ≠ ⊤)
    (hres : Function.Surjective
      (algebraMap A (D ⧸ (maximalIdeal A).map (algebraMap A D)))) :
    ((maximalIdeal A).map (algebraMap A D)).IsMaximal := by
  let I := (maximalIdeal A).map (algebraMap A D)
  have : Nontrivial (D ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let g := algebraMap A (D ⧸ I)
  have hzero : (maximalIdeal A).map g = ⊥ := map_algebraMap_quotient_map_eq_bot _
  have hker : RingHom.ker g ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top g)
  have hb : (⊥ : Ideal (D ⧸ I)).IsMaximal := hzero ▸
    Ideal.IsMaximal.map_of_surjective_of_ker_le hres hker
  have hi := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (K := ⊥)
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hi

/-- An algebra flat over `A` which is also an algebra over an ind-étale `A`-algebra `R`,
compatibly, is flat over `R`. -/
theorem flat_restrictScalars_of_ind_etale (A : Type u) (R : Type v) (H : Type w)
    [CommRing A] [CommRing R]
    [CommRing H] [Algebra A R] [Algebra A H] [Algebra R H] [IsScalarTower A R H]
    [Module.Flat A H]
    (hind : (CommAlgCat.etale.{v} A).ind.{v} (CommAlgCat.of A R)) : Module.Flat R H := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  have hwe : Algebra.WeaklyEtale A R :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v} A).2.2
      J pres.diag pres.cocone pres.isColimit (fun j => by
        have : Algebra.Etale A (pres.diag.obj j) := hpres j
        exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v} A).2.1
          (pres.diag.obj j))
  exact flat_of_flat_of_mul_flat A R (Algebra.WeaklyEtale.flat_lmul' A R) H inferInstance

theorem flat_of_isHenselization_algHom
    {A : Type u} {Ah : Type v} {B : Type*}
    [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [CommRing B] [Algebra A Ah] [Algebra A B] [Module.Flat A B]
    [IsHenselization A (ResidueField A) Ah] (f : Ah →ₐ[A] B) : f.toRingHom.Flat := by
  let : Algebra Ah B := f.toRingHom.toAlgebra
  have : IsScalarTower A Ah B := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra (ULift.{u} Ah) B := ULift.algebra' Ah B
  have : IsScalarTower A (ULift.{u} Ah) B :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := ULift.{u} Ah) (A := B) fun x => by
      show algebraMap A B x = f (algebraMap A Ah x)
      exact (f.commutes x).symm
  exact Module.Flat.ulift_left_iff.mp (flat_restrictScalars_of_ind_etale A (ULift.{u} Ah) B
    (IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah)))

theorem algHom_ext_adicCompletion
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) [IsHausdorff I S]
    (f g : AdicCompletion I R →ₐ[R] S) : f = g := by
  apply AlgHom.ext
  intro x
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.sub_mem]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R R)) (x.val n)
  have hx : x - algebraMap R (AdicCompletion I R) r ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hr.symm
  have key (h : AdicCompletion I R →ₐ[R] S) :
      h (x - algebraMap R (AdicCompletion I R) r) ∈ I ^ n • (⊤ : Submodule R S) := by
    have := Submodule.mem_map_of_mem (f := h.toLinearMap) hx
    rw [Submodule.map_smul'', Submodule.map_top] at this
    exact Submodule.smul_mono le_rfl le_top this
  simpa only [map_sub, f.commutes, g.commutes, sub_sub_sub_cancel_right] using
    Submodule.sub_mem (I ^ n • ⊤) (key f) (key g)

/-- A map `f : R → S` into a `K`-adically complete ring which carries `I` into `K` extends to the
`I`-adic completion of `R`, compatibly with the canonical map `R → AdicCompletion I R`. -/
public theorem exists_algHom_adicCompletion_of_map_le
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (I : Ideal R) (K : Ideal S)
    [IsAdicComplete K S] (f : R →ₐ[A] S) (h : I.map f.toRingHom ≤ K) :
    ∃ F : AdicCompletion I R →ₐ[A] S,
      ∀ r : R, F (algebraMap R (AdicCompletion I R) r) = f r := by
  have hpow (n : ℕ) : (I ^ n).map f.toRingHom ≤ K ^ n := by
    rw [Ideal.map_pow]; exact pow_le_pow_left' h n
  let fam : (n : ℕ) → AdicCompletion I R →ₐ[A] S ⧸ K ^ n := fun n =>
    (Ideal.quotientMapₐ (K ^ n) f (Ideal.map_le_iff_le_comap.mp (hpow n))).comp
      ((AdicCompletion.evalₐ I n).restrictScalars A)
  have hfam : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (fam n) = fam m := by
    intro m n hmn
    apply AlgHom.ext
    intro x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simp only [fam, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AdicCompletion.evalₐ_mk, Ideal.quotient_map_mkₐ,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.factorₐ_apply,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      rw [← map_sub]
      apply Ideal.map_le_iff_le_comap.mp (hpow m)
      simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (x.property hmn).symm
  have : IsScalarTower A R (AdicCompletion I R) := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨IsAdicComplete.liftAlgHom K fam hfam, fun r => ?_⟩
  have key : (IsAdicComplete.liftAlgHom K fam hfam).comp
      (IsScalarTower.toAlgHom A R (AdicCompletion I R)) = f := by
    apply IsAdicComplete.algHom_ext (I := K)
    intro n
    rw [← AlgHom.comp_assoc, IsAdicComplete.mkₐ_comp_liftAlgHom]
    exact AlgHom.ext fun r => by simp [fam]
  exact congrArg (fun k : R →ₐ[A] S => k r) key

private theorem isUnramifiedAt_of_surjective_quotient
    {A D : Type*} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]
    [Algebra.FiniteType A D]
    (m : Ideal D) [m.IsMaximal] (hm : m = (maximalIdeal A).map (algebraMap A D))
    (hs : Function.Surjective (algebraMap A (D ⧸ m))) : Algebra.IsUnramifiedAt A m := by
  let L := Localization.AtPrime m
  have hmL : (maximalIdeal A).map (algebraMap A L) = maximalIdeal L := by
    rw [IsScalarTower.algebraMap_eq A D L, ← Ideal.map_map, ← hm]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal (Rₚ := L) m
  have : IsLocalHom (algebraMap A L) :=
    ((local_hom_TFAE (algebraMap A L)).out 4 1).mp fun x hx =>
      hmL ▸ Ideal.mem_map_of_mem _ hx
  have hres : Function.Surjective (algebraMap A (ResidueField L)) := by
    intro x
    obtain ⟨d, hd⟩ := hs ((IsLocalization.AtPrime.equivQuotMaximalIdeal m L).symm x)
    refine ⟨d, ?_⟩
    have := congrArg (IsLocalization.AtPrime.equivQuotMaximalIdeal m L) hd
    change (IsLocalization.AtPrime.equivQuotMaximalIdeal m L)
      (Ideal.Quotient.mk m (algebraMap A D d)) = _ at this
    exact this.trans (RingEquiv.apply_symm_apply _ _)
  have : Algebra.IsSeparable (ResidueField A) (ResidueField L) := by
    constructor
    intro x
    obtain ⟨a, rfl⟩ := hres x
    rw [IsScalarTower.algebraMap_apply A (ResidueField A) (ResidueField L)]
    exact isSeparable_algebraMap (residue A a)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmL

private theorem eq_of_isRoot_of_sub_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] (p : Polynomial R) (a b : R)
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hu : IsUnit (p.derivative.eval a)) (h : b - a ∈ maximalIdeal R) : a = b := by
  obtain ⟨k, hk⟩ := p.binomExpansion a (b - a)
  rw [add_sub_cancel, hb, ha, zero_add] at hk
  have hz : (b - a) * (p.derivative.eval a + k * (b - a)) = 0 := by
    rw [hk]; ring
  have hun : IsUnit (p.derivative.eval a + k * (b - a)) := by
    rw [← notMem_maximalIdeal] at hu ⊢
    intro hn
    exact hu (by simpa using ((maximalIdeal R).sub_mem hn
      ((maximalIdeal R).mul_mem_left k h)))
  exact (sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hun).mp hz)).symm

/-- A standard étale algebra maps into a henselian local ring through any local map with
surjective residue extension. -/
private theorem exists_standardEtale_lift
    {A H C : Type*} [CommRing A] [CommRing H] [HenselianLocalRing H]
    [CommRing C] [IsLocalRing C] [Algebra A H] [Algebra A C]
    (f : H →ₐ[A] C) [IsLocalHom f.toRingHom]
    (hres : Function.Surjective (ResidueField.map f.toRingHom))
    (P : StandardEtalePair A) (ψ : P.Ring →ₐ[A] C) :
    ∃ σ : P.Ring →ₐ[A] H, f.comp σ = ψ := by
  let p := P.f.map (algebraMap A H)
  let g := P.g.map (algebraMap A H)
  obtain ⟨a₀, ha₀⟩ := hres (residue C (ψ P.X))
  have hψ := P.hasMap_X.map ψ
  have hid (t : Polynomial A) :
      ResidueField.map f.toRingHom (Polynomial.aeval a₀ (t.map (algebraMap A H))) =
        residue C (Polynomial.aeval (ψ P.X) t) := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, ha₀]
    congr 1
    ext a
    simp [ResidueField.map_residue, f.commutes]
  have hf0 : Polynomial.aeval a₀ p = 0 := by
    apply (ResidueField.map f.toRingHom).injective
    simpa only [map_zero, hψ.1] using hid P.f
  have hder : Polynomial.aeval a₀ p.derivative ≠ 0 := by
    intro hzero
    have h' := hid P.f.derivative
    rw [← Polynomial.derivative_map] at h'
    rw [show Polynomial.aeval a₀ (Polynomial.derivative p) = 0 from hzero, map_zero] at h'
    exact (hψ.isUnit_derivative_f.map (residue C)).ne_zero h'.symm
  obtain ⟨a, ha, har⟩ := ((HenselianLocalRing.TFAE H).out 1 2 rfl rfl).mp
    (inferInstance : HenselianLocalRing H) p (P.monic_f.map _) a₀ hf0 hder
  have hgunit : IsUnit (Polynomial.aeval a P.g) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]
    intro hgzero
    have h' := hid P.g
    have heq : residue H (Polynomial.aeval a P.g) = Polynomial.aeval a₀ g := by
      rw [← har]
      simp [g, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    rw [← heq, hgzero, map_zero] at h'
    exact (hψ.2.map (residue C)).ne_zero h'.symm
  have ha' : Polynomial.aeval a P.f = 0 := by
    simpa [p, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using ha
  refine ⟨P.lift a ⟨ha', hgunit⟩, P.hom_ext ?_⟩
  simp only [AlgHom.comp_apply, StandardEtalePair.lift_X]
  apply eq_of_isRoot_of_sub_mem_maximalIdeal (P.f.map (algebraMap A C))
  · simpa [Polynomial.eval_map, Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply] using
      congrArg f ha'
  · simpa [Polynomial.eval_map, Polynomial.aeval_def] using hψ.1
  · simpa [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def,
      ← Polynomial.aeval_algHom_apply] using
        ((show P.HasMap a from ⟨ha', hgunit⟩).isUnit_derivative_f.map f)
  · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    show residue C (ψ P.X) = residue C (f.toRingHom a)
    rw [← ResidueField.map_residue f.toRingHom a, har, ha₀]

private theorem isAdicComplete_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I J : Ideal R)
    [IsAdicComplete I R] (hI : I ≤ (⊥ : Ideal R).jacobson) :
    IsAdicComplete I (R ⧸ J) := by
  have : IsHausdorff I (R ⧸ J) := IsHausdorff.of_le_jacobson I (R ⧸ J) hI
  have : IsPrecomplete I (R ⧸ J) := AdicCompletion.of_surjective_iff.mp (by
    intro z
    obtain ⟨x, hx⟩ := AdicCompletion.map_surjective (I := I)
      (f := (Ideal.Quotient.mkₐ R J).toLinearMap) Ideal.Quotient.mk_surjective z
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R x
    exact ⟨Ideal.Quotient.mk J r, (AdicCompletion.map_of I _ r).symm.trans hx⟩)
  exact {}

set_option backward.isDefEq.respectTransparency false in
/-- An ideal of the completion whose quotient is algebraizable is extended from the
henselization. -/
theorem exists_ideal_map_eq_of_algebraization
    (A : Type u) (Ah : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [HenselianLocalRing Ah] [Algebra A Ah]
    (f : Ah →ₐ[A] AdicCompletion (maximalIdeal A) A)
    [IsLocalHom f.toRingHom]
    (J : Ideal (AdicCompletion (maximalIdeal A) A)) (hJne : J ≠ ⊤)
    (D : Type u) (hD : CommRing D) (hAD : Algebra A D)
    (hfinite : Algebra.FiniteType A D)
    (he : Nonempty ((AdicCompletion (maximalIdeal A) A ⧸ J) ≃ₐ[A]
      AdicCompletion ((maximalIdeal A).map (algebraMap A D)) D)) :
    ∃ I : Ideal Ah, I.map f.toRingHom = J := by
  classical
  let : CommRing D := hD
  let : Algebra A D := hAD
  have : Algebra.FiniteType A D := hfinite
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  obtain ⟨e⟩ := he
  let φ := e.toAlgHom.comp (Ideal.Quotient.mkₐ A J)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hres := surjective_quotient_algebraMap_of_surjective_adicCompletion
    (maximalIdeal A) (maximalIdeal A).fg_of_isNoetherianRing φ hφ
  have : Nontrivial (AdicCompletion (maximalIdeal A) A ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have : Nontrivial (AdicCompletion ((maximalIdeal A).map (algebraMap A D)) D) :=
    e.symm.toEquiv.nontrivial
  have hmax := isMaximal_map_of_surjective_quotient_algebraMap
    (ne_top_of_nontrivial_adicCompletion _) hres
  let Ahat := AdicCompletion (maximalIdeal A) A
  let C := Ahat ⧸ J
  let Dhat := AdicCompletion ((maximalIdeal A).map (algebraMap A D)) D
  have : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have hquotlocal : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap A C) :=
    RingHom.isLocalHom_comp (Ideal.Quotient.mk J) (algebraMap A Ahat)
  have : IsLocalRing Dhat := IsLocalRing.of_surjective' e.toRingHom e.surjective
  let m := (maximalIdeal A).map (algebraMap A D)
  have : m.IsMaximal := hmax
  have : Algebra.IsUnramifiedAt A m :=
    isUnramifiedAt_of_surjective_quotient m rfl hres
  obtain ⟨s, hs, P, π, hπ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) m
  have hmhat : m.map (algebraMap D Dhat) = maximalIdeal Dhat :=
    eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le m m le_rfl m.fg_of_isNoetherianRing)
  have hus : IsUnit (algebraMap D Dhat s) := by
    rw [← notMem_maximalIdeal, ← hmhat,
      ← AdicCompletion.ker_evalOneₐ_eq_map m m.fg_of_isNoetherianRing, RingHom.mem_ker]
    show Ideal.Quotient.mk m s ≠ 0
    exact Ideal.Quotient.eq_zero_iff_mem.not.mpr hs
  let d : D →ₐ[A] C := e.symm.toAlgHom.comp (Algebra.algHom A D Dhat)
  let θ : Localization.Away s →ₐ[A] C :=
    IsLocalization.Away.liftAlgHom s (f := d) (hus.map e.symm.toRingHom)
  let fbar : Ah →ₐ[A] C := (Ideal.Quotient.mkₐ A J).comp f
  have : IsLocalHom fbar.toRingHom :=
    RingHom.isLocalHom_comp (Ideal.Quotient.mk J) f.toRingHom
  let resC : Ahat →ₐ[A] ResidueField C :=
    (Algebra.algHom A C (ResidueField C)).comp (Ideal.Quotient.mkₐ A J)
  have hresC : Function.Surjective (algebraMap A (ResidueField C)) := by
    apply surjective_algebraMap_of_surjective_adicCompletion (maximalIdeal A)
      (maximalIdeal A).fg_of_isNoetherianRing resC
      (residue_surjective.comp Ideal.Quotient.mk_surjective)
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    show residue C (algebraMap A C a) = 0
    rwa [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap]
  have hresf : Function.Surjective (ResidueField.map fbar.toRingHom) := by
    intro x
    obtain ⟨a, rfl⟩ := hresC x
    refine ⟨residue Ah (algebraMap A Ah a), ?_⟩
    rw [ResidueField.map_residue]
    show residue C (fbar (algebraMap A Ah a)) = residue C (algebraMap A C a)
    rw [fbar.commutes]
  obtain ⟨σ, hσ⟩ := exists_standardEtale_lift fbar hresf P (θ.comp π)
  let I : Ideal Ah := (RingHom.ker π.toRingHom).map σ.toRingHom
  let K : Ideal Ahat := I.map f.toRingHom
  have hKJ : K ≤ J := by
    dsimp only [K, I]
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro x hx
    show f (σ x) ∈ J
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show fbar (σ x) = 0
    rw [show fbar (σ x) = θ (π x) from congrArg (fun g => g x) hσ, show π x = 0 from hx, map_zero]
  let Q := Ahat ⧸ K
  have hcomplete : IsAdicComplete (maximalIdeal Ahat) Q :=
    isAdicComplete_quotient (maximalIdeal Ahat) K (by
      rw [jacobson_eq_maximalIdeal (⊥ : Ideal Ahat) bot_ne_top])
  have : IsAdicComplete (maximalIdeal A) Q := by
    apply (IsAdicComplete.map_algebraMap_iff (S := Ahat) _ Q).mp
    rwa [← AdicCompletion.maximalIdeal_eq_map]
  let mQ := (maximalIdeal A).map (algebraMap A Q)
  have : IsAdicComplete mQ Q := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  let η : P.Ring →ₐ[A] Q := ((Ideal.Quotient.mkₐ A K).comp f).comp σ
  have hη : RingHom.ker π.toRingHom ≤ RingHom.ker η.toRingHom := by
    intro x hx
    show Ideal.Quotient.mk K (f (σ x)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem f.toRingHom (Ideal.mem_map_of_mem σ.toRingHom hx))
  let δ : Localization.Away s →ₐ[A] Q := AlgHom.liftOfSurjective π hπ η hη
  let g : D →ₐ[A] Q := δ.comp (Algebra.algHom A D (Localization.Away s))
  have hgm : m.map g.toRingHom ≤ mQ := by
    dsimp only [m, mQ]
    rw [Ideal.map_map]
    exact le_of_eq (congrArg (fun h : A →+* Q => Ideal.map h (maximalIdeal A))
      (RingHom.ext g.commutes))
  obtain ⟨L, -⟩ := exists_algHom_adicCompletion_of_map_le m mQ g hgm
  have hcomp : (L.comp e.toAlgHom).comp (Ideal.Quotient.mkₐ A J) =
      Ideal.Quotient.mkₐ A K := algHom_ext_adicCompletion
        (maximalIdeal A) (maximalIdeal A).fg_of_isNoetherianRing _ _
  have hJK : J ≤ K := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have heq := congrArg (fun g => g x) hcomp
    change L (e (Ideal.Quotient.mk J x)) = Ideal.Quotient.mk K x at heq
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero] at heq
    exact heq.symm
  exact ⟨I, le_antisymm hKJ hJK⟩

/-- A minimal prime defining a one-dimensional component of the completion of a Noetherian local
ring is the radical of the extension of a minimal prime of its henselization. -/
@[stacks 0C2B]
theorem exists_minimalPrime_henselization_radical_map_eq_of_quotient_dimension_one
    (A : Type u) (Ah : Type v)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    ∃ f : Ah →+* Ahat,
      (∀ x : A, f (algebraMap A Ah x) = algebraMap A Ahat x) ∧
        ∀ q : Ideal Ahat, q ∈ minimalPrimes Ahat →
          ringKrullDim (Ahat ⧸ q) = 1 →
            ∃ qh : Ideal Ah, qh ∈ minimalPrimes Ah ∧ q = (Ideal.map f qh).radical := by
  classical
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  have hfLocal : IsLocalHom f.toRingHom := isLocalHom_of_isHenselization_algHom f
  have : HenselianLocalRing Ah := IsHenselization.henselian (R := A) (L := ResidueField A)
  refine ⟨f.toRingHom, f.commutes, ?_⟩
  intro q hq hdim
  have : q.IsPrime := hq.isPrime
  set J := RingHom.ker
    (algebraMap (AdicCompletion (maximalIdeal A) A) (Localization.AtPrime q)) with hJdef
  have hrad : J.radical = q := radical_ker_atPrime_eq q hq
  have hJne : J ≠ ⊤ := by
    intro h
    rw [h, Ideal.radical_top] at hrad
    exact hq.isPrime.ne_top hrad.symm
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_smul_cotangent_eq_bot q hq hdim.le
  obtain ⟨D, hD, hAD, hfinite, he⟩ := exists_finiteType_completion_quotient A J n hn
  obtain ⟨I, hI⟩ :=
    exists_ideal_map_eq_of_algebraization A Ah f J hJne D hD hAD hfinite he
  exact exists_minimalPrime_radical_map_eq_of_extended_ideal f.toRingHom
    (flat_of_isHenselization_algHom f) q J hq hrad I hI

end
