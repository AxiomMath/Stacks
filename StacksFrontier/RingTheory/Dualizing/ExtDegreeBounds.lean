module

public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Support.Finite

import all StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree bounds for Ext into a normalized dualizing complex

Let `A` be a Noetherian local ring, let `K` be a normalized dualizing complex over `A`,
and let `M` be a nonzero finite `A`-module. If the support of `M` has dimension `d`, then
`Ext^i_A(M, K)` can be nonzero only for `-d ≤ i ≤ 0`.

## Main results

* `Dualizing.ext_degree_mem_Icc_of_nontrivial` bounds every degree in
  which `Ext_A(M, K)` is nonzero.
* `Dualizing.subsingleton_ext_of_isFiniteLength_of_ne_zero` is the case of a module of finite
  length, where the bound collapses to degree zero; this is the cohomological form of the
  normalization convention of [Stacks, Tag 0A7M].

## Implementation notes

Normalization is expressed by `IsNormalizedDualizingComplex`. The equality
`d = dim(Supp(M))` is expressed by `Module.supportDim A M = (d : WithBot ℕ∞)`, and
nonvanishing of an Ext group by `Nontrivial`.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

private lemma subsingleton_hom_shift_pos
    {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    {X Y : C} (i : ℤ) (h : Subsingleton (X ⟶ Y⟦i - 1⟧)) :
    Subsingleton (X⟦(1 : ℤ)⟧ ⟶ Y⟦i⟧) := by
  let e := (shiftFunctorAdd' C (i - 1) 1 i (by omega)).app Y
  refine ⟨fun f g => (cancel_mono e.hom).1 ?_⟩
  obtain ⟨f', hf'⟩ := (shiftFunctor C (1 : ℤ)).map_surjective (f ≫ e.hom)
  obtain ⟨g', hg'⟩ := (shiftFunctor C (1 : ℤ)).map_surjective (g ≫ e.hom)
  rw [← hf', ← hg', h.elim f' g']

private lemma extComparison_surjective_of_torsion_vanishing
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (hnow : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) K i)) :
    Function.Surjective (extComparison M K i) := by
  intro x
  have hzero : extRestriction M K i x = 0 := hnow.elim _ _
  rw [extRestriction_apply] at hzero
  obtain ⟨y, hy⟩ := yoneda_exact_aux (A := A) M x hzero
  refine ⟨y, ?_⟩
  rw [extComparison_apply]
  exact hy.symm

private lemma extComparison_bijective_of_torsion_vanishing
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (hprev : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) K (i - 1)))
    (hnow : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) K i)) :
    Function.Bijective (extComparison M K i) := by
  let S := torsionShortComplex (A := A) M
  have hS := torsionShortComplex_shortExact (A := A) M
  let T := hS.singleTriangle
  refine ⟨fun x y hxy => ?_, extComparison_surjective_of_torsion_vanishing K i hnow⟩
  have hx : T.mor₂ ≫ (x - y) = 0 := by
    change (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map S.g ≫ (x - y) = 0
    have hker : extComparison M K i (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rwa [extComparison_apply] at hker
  obtain ⟨z, hz⟩ := T.yoneda_exact₃ hS.singleTriangle_distinguished (x - y) hx
  have hprev' : Subsingleton (T.obj₁ ⟶ K⟦i - 1⟧) := hprev
  rw [(subsingleton_hom_shift_pos (C := DerivedCategory (ModuleCat.{max v u} A)) i
    hprev').elim z 0, Limits.comp_zero] at hz
  exact sub_eq_zero.mp hz

private lemma finiteLength_ext_subsingleton_of_ne_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hM : IsFiniteLength A M) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) := by
  obtain ⟨E, j, hj, hHull⟩ := Module.exists_isInjectiveHull.{u, v} A
    ((ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)))
  have : Mono j := hj
  let N : FiniteLengthModules.{u, v} A := ⟨ModuleCat.of A M, hM⟩
  obtain ⟨e⟩ := derivedHomFiniteLengthIsoMatlisDual A K hK E j hHull
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)
  let D := (dualizingDerivedHomFunctor A K).obj (.op X)
  let H : ModuleCat.{max v u} A :=
    (MonoidalClosed.internalHom.obj (Opposite.op (ModuleCat.of A M))).obj E
  have eD : D ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj H :=
    e.app (Opposite.op N)
  have : D.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eD.symm 0
  have : D.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eD.symm 0
  have hzero : Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj D) := by
    rcases hi.lt_or_gt with hineg | hipos
    · exact DerivedCategory.isZero_of_isGE D 0 i hineg
    · exact DerivedCategory.isZero_of_isLE D 0 i hipos
  have hsub := ModuleCat.isZero_iff_subsingleton.1 hzero
  let eExt := extIntoOmegaAtLinearEquiv A K i (ModuleCat.of A M)
  exact ⟨fun x y => eExt.injective (hsub.elim (eExt x) (eExt y))⟩

/-- **Ext from a finite-length module into a normalized dualizing complex is concentrated in
degree zero.** For `K` a normalized dualizing complex over a Noetherian local ring `A` and `M`
an `A`-module of finite length, `Ext^i_A(M, K) = 0` for every `i ≠ 0`.

Matlis duality on finite-length modules identifies `RHom_A(M, K)` with `Hom_A(M, E)` placed in
degree zero, for `E` an injective hull of the residue field
(`Dualizing.derivedHomFiniteLengthIsoMatlisDual`), and an object of the derived category
isomorphic to a module in degree zero has no cohomology elsewhere. -/
alias subsingleton_ext_of_isFiniteLength_of_ne_zero := finiteLength_ext_subsingleton_of_ne_zero

private lemma moduleFinite_ext
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) (i : ℤ) :
    Module.Finite A (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)
  have hX : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · exact Module.Finite.equiv (M := M) ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0).app (ModuleCat.of A M)).toLinearEquiv.symm
    · have hz : Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) := by
        rcases hj.lt_or_gt with hjneg | hjpos
        · exact DerivedCategory.isZero_of_isGE X 0 j hjneg
        · exact DerivedCategory.isZero_of_isLE X 0 j hjpos
      have : Subsingleton
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  have := dualizingDerivedHom_finiteCohomology A K hK X hX i
  exact Module.Finite.equiv (extIntoOmegaAtLinearEquiv A K i (ModuleCat.of A M)).symm

private lemma finiteLength_of_supportDim_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] (hd : Module.supportDim A M = 0) : IsFiniteLength A M := by
  let m := IsLocalRing.maximalIdeal A
  let J := Module.annihilator A M
  have hJne : J ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have h1 : (1 : A) ∈ J := by rw [h]; trivial
    exact hx (by simpa using (Module.mem_annihilator.mp h1 x))
  have hJle : J ≤ m := IsLocalRing.le_maximalIdeal hJne
  have hsupp : Module.support A M = PrimeSpectrum.zeroLocus (m : Set A) := by
    simpa [hd] using (support_of_supportDim_eq_zero A M)
  have hrad : m ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    have hp : (⟨P, hP.2⟩ : PrimeSpectrum A) ∈ Module.support A M :=
      (Module.mem_support_iff_of_finite (R := A) (M := M)).2 hP.1
    rwa [hsupp, PrimeSpectrum.mem_zeroLocus] at hp
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian m)
  let T := maximalIdealPowerTorsion (A := A) M
  have hTtop : T = ⊤ := by
    apply top_unique
    intro x hx
    change x ∈ Ideal.primaryComponent M m
    rw [Ideal.primaryComponent_mem]
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    exact Module.mem_annihilator.mp (hn a.2) x
  exact (isFiniteLength_maximalIdealPowerTorsion A M).of_surjective (f := T.subtype)
    fun x => ⟨⟨x, by simp [hTtop]⟩, rfl⟩

private lemma exists_supportDim_eq_nat
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    ∃ d : ℕ, Module.supportDim A M = (d : WithBot ℕ∞) := by
  have hfinite : Module.supportDim A M < ⊤ :=
    (Module.supportDim_le_ringKrullDim A M).trans_lt ringKrullDim_lt_top
  cases hdim : Module.supportDim A M with
  | bot => exact False.elim ((Module.supportDim_ne_bot_of_nontrivial A M) hdim)
  | coe d =>
    have hfinite' : (d : WithBot ℕ∞) < ⊤ := by simpa [hdim] using hfinite
    have hd : d < ⊤ := WithBot.coe_lt_coe.mp hfinite'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hd)
    exact ⟨n, congrArg (fun z : ℕ∞ => (z : WithBot ℕ∞)) hn.symm⟩

private lemma exists_quotient_supportDim_eq_nat
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (d : ℕ) (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular M f) :
    ∃ d' : ℕ, d' < d ∧ Module.supportDim A (QuotSMulTop f M) = (d' : WithBot ℕ∞) ∧
      Nontrivial (QuotSMulTop f M) := by
  have hdrop := Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hf
  have hquot : Nontrivial (QuotSMulTop f M) := by
    by_contra h
    have : Subsingleton (QuotSMulTop f M) := not_nontrivial_iff_subsingleton.mp h
    have hb := Module.supportDim_eq_bot_of_subsingleton A (QuotSMulTop f M)
    have hMbot : Module.supportDim A M = ⊥ := by simpa [hb] using hdrop.symm
    exact (Module.supportDim_ne_bot_of_nontrivial A M) hMbot
  obtain ⟨d', hd'⟩ := exists_supportDim_eq_nat (A := A) (M := QuotSMulTop f M)
  have hdnum : d' + 1 = d := by
    rw [hd', hd] at hdrop
    exact_mod_cast hdrop
  exact ⟨d', by omega, hd', hquot⟩


private lemma exists_regular_of_depth_pos_universe
    {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hpos : 0 < Module.depth R (IsLocalRing.maximalIdeal R) M) :
    ∃ f ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M f := by
  rw [Module.depth_eq_iSup_isWeaklyRegular_length, lt_iSup_iff] at hpos
  obtain ⟨rs, hrs⟩ := hpos
  rw [lt_iSup_iff] at hrs
  obtain ⟨hmem, hlen⟩ := hrs
  have hlen' : 0 < rs.length := by exact_mod_cast hlen
  cases rs with
  | nil => simp at hlen'
  | cons f fs =>
      exact ⟨f, hmem.1 f (by simp),
        ((RingTheory.Sequence.isWeaklyRegular_cons_iff M f fs).mp hmem.2).1⟩

private lemma exists_regular_quotient_supportDim_lt
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (d : ℕ) (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (hpos : 0 < Module.depth A (IsLocalRing.maximalIdeal A) M) :
    ∃ f ∈ IsLocalRing.maximalIdeal A, IsSMulRegular M f ∧
      ∃ d' : ℕ, d' < d ∧ Module.supportDim A (QuotSMulTop f M) = (d' : WithBot ℕ∞) ∧
        Nontrivial (QuotSMulTop f M) := by
  obtain ⟨f, hf, hreg⟩ := exists_regular_of_depth_pos_universe hpos
  refine ⟨f, hf, hreg, ?_⟩
  have hdrop := Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hf
  have hquot : Nontrivial (QuotSMulTop f M) := by
    by_contra h
    have : Subsingleton (QuotSMulTop f M) := not_nontrivial_iff_subsingleton.mp h
    have hb := Module.supportDim_eq_bot_of_subsingleton A (QuotSMulTop f M)
    have hMbot : Module.supportDim A M = ⊥ := by simpa [hb] using hdrop.symm
    exact (Module.supportDim_ne_bot_of_nontrivial A M) hMbot
  obtain ⟨d', hd'⟩ := exists_supportDim_eq_nat (A := A) (M := QuotSMulTop f M)
  have hdnum : d' + 1 = d := by
    rw [hd', hd] at hdrop
    exact_mod_cast hdrop
  exact ⟨d', by omega, hd', hquot⟩

private lemma ext_subsingleton_of_regular_quotient_subsingleton
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular M f)
    (i : ℤ)
    (hQ : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (QuotSMulTop f M))) K (i + 1))) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) := by
  let X := DerivedCategory.Ext
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i
  by_contra hX
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp hX
  have : Module.Finite A X := moduleFinite_ext (A := A) (M := M) K hK.1 i
  have hle : (⊤ : Submodule A X) ≤ f • (⊤ : Submodule A X) := by
    intro x _
    obtain ⟨y, hy⟩ := (exact_lsmul_extConnecting M K f hreg i x).mp (hQ.elim _ _)
    rw [LinearMap.lsmul_apply] at hy
    rw [← hy]
    exact Submodule.smul_mem_pointwise_smul y f ⊤ (by simp)
  exact Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
    (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A X) hf) (le_antisymm hle le_top)

private lemma quotient_ext_nontrivial_of_ext_nontrivial
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) (hreg : IsSMulRegular M f)
    (i : ℤ)
    (hExt : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i)) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (QuotSMulTop f M))) K (i + 1)) := by
  by_contra h
  exact not_subsingleton_iff_nontrivial.mpr hExt
    (ext_subsingleton_of_regular_quotient_subsingleton K hK hf hreg i
      (not_nontrivial_iff_subsingleton.mp h))

/-- The torsion quotient of `M` of positive support dimension `d` has a regular element whose
quotient has smaller support dimension. -/
private lemma exists_regular_quotient_torsion_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (d : ℕ) (hd : Module.supportDim A M = (d : WithBot ℕ∞)) (hdpos : 0 < d) :
    ∃ f ∈ IsLocalRing.maximalIdeal A,
      IsSMulRegular (quotientMaximalIdealPowerTorsion (A := A) M) f ∧
      ∃ d' : ℕ, d' < d ∧ Module.supportDim A
        (QuotSMulTop f (quotientMaximalIdealPowerTorsion (A := A) M)) = (d' : WithBot ℕ∞) ∧
        Nontrivial (QuotSMulTop f (quotientMaximalIdealPowerTorsion (A := A) M)) := by
  let Q := quotientMaximalIdealPowerTorsion (A := A) M
  have hQdim : Module.supportDim A Q = (d : WithBot ℕ∞) :=
    (supportDim_quotientMaximalIdealPowerTorsion A M
      (by rw [hd]; exact_mod_cast hdpos)).trans hd
  have : Nontrivial Q := by
    by_contra h'
    have := not_nontrivial_iff_subsingleton.mp h'
    rw [Module.supportDim_eq_bot_of_subsingleton A Q] at hQdim
    exact (by simp : (d : WithBot ℕ∞) ≠ ⊥) hQdim.symm
  exact exists_regular_quotient_supportDim_lt Q d hQdim
    (depth_quotientMaximalIdealPowerTorsion_pos A M)

-- The dimension induction expands several exact Ext comparisons at once.
private theorem positive_ext_subsingleton
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (d : ℕ) (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M]
    (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) := by
  induction d using Nat.strong_induction_on generalizing M i with
  | h d ih =>
    by_cases hd0 : d = 0
    · subst d
      exact finiteLength_ext_subsingleton_of_ne_zero K hK
        (finiteLength_of_supportDim_zero (A := A) (M := M) (by simpa using hd)) (by omega)
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hdepth0 : Module.depth A (IsLocalRing.maximalIdeal A) M = 0
    · have hsurj : Function.Surjective (extComparison M K i) :=
        extComparison_surjective_of_torsion_vanishing K i
          (finiteLength_ext_subsingleton_of_ne_zero K hK
            (isFiniteLength_maximalIdealPowerTorsion A M) (by omega))
      obtain ⟨f, hf, hreg, d', hd', hQfDim, hQf⟩ :=
        exists_regular_quotient_torsion_quotient M d hd hdpos
      have := ext_subsingleton_of_regular_quotient_subsingleton
        (M := quotientMaximalIdealPowerTorsion (A := A) M) K hK hf hreg i
        (ih d' hd' _ hQfDim (i + 1) (by omega))
      exact hsurj.subsingleton
    · obtain ⟨f, hf, hreg, d', hd', hMfDim, hMf⟩ :=
        exists_regular_quotient_supportDim_lt M d hd (pos_iff_ne_zero.2 hdepth0)
      exact ext_subsingleton_of_regular_quotient_subsingleton (M := M) K hK hf hreg i
        (ih d' hd' (QuotSMulTop f M) hMfDim (i + 1) (by omega))

-- Strong induction combines finite-length comparisons with quotient Ext embeddings.
private theorem ext_lower_bound_of_nontrivial
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (d : ℕ) (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M]
    (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ≤ 0)
    (hExt : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i)) :
    -(d : ℤ) ≤ i := by
  induction d using Nat.strong_induction_on generalizing M i with
  | h d ih =>
    by_cases hi0 : i = 0
    · omega
    by_cases hd0 : d = 0
    · subst d
      have hzero := finiteLength_ext_subsingleton_of_ne_zero K hK
        (finiteLength_of_supportDim_zero (A := A) (M := M) (by simpa using hd)) hi0
      exact (not_subsingleton_iff_nontrivial.mpr hExt hzero).elim
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    by_cases hdepth0 : Module.depth A (IsLocalRing.maximalIdeal A) M = 0
    · have hTfl := isFiniteLength_maximalIdealPowerTorsion A M
      have hcmp : Function.Bijective (extComparison M K i) :=
        extComparison_bijective_of_torsion_vanishing K i
          (finiteLength_ext_subsingleton_of_ne_zero K hK hTfl (by omega))
          (finiteLength_ext_subsingleton_of_ne_zero K hK hTfl hi0)
      have hQext : Nontrivial (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A (quotientMaximalIdealPowerTorsion (A := A) M))) K i) :=
        (Equiv.ofBijective (extComparison M K i) hcmp).nontrivial
      obtain ⟨f, hf, hreg, d', hd', hQfDim, hQf⟩ :=
        exists_regular_quotient_torsion_quotient M d hd hdpos
      have := ih d' hd' _ hQfDim (i + 1) (by omega)
        (quotient_ext_nontrivial_of_ext_nontrivial K hK hf hreg i hQext)
      omega
    · obtain ⟨f, hf, hreg, d', hd', hMfDim, hMf⟩ :=
        exists_regular_quotient_supportDim_lt M d hd (pos_iff_ne_zero.2 hdepth0)
      have := ih d' hd' (QuotSMulTop f M) hMfDim (i + 1) (by omega)
        (quotient_ext_nontrivial_of_ext_nontrivial K hK hf hreg i hExt)
      omega

/-- **Stacks Project, Tag 0A7U.** For a nonzero finite module `M` of support dimension `d`,
Ext from `M` into a normalized dualizing complex can be nonzero only in the integer degrees
from `-d` through `0`. -/
@[stacks 0A7U "ext_degree_bounds", sga "2 V 3.1" "(i)"]
theorem ext_degree_mem_Icc_of_nontrivial
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (d : ℕ) (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (i : ℤ)
    (hi : Nontrivial
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) K i)) :
    i ∈ Set.Icc (-(d : ℤ)) 0 := by
  have hnonpos : i ≤ 0 := not_lt.1 fun hpos =>
    not_subsingleton_iff_nontrivial.mpr hi (positive_ext_subsingleton K hK d M hd i hpos)
  exact ⟨ext_lower_bound_of_nontrivial K hK d M hd i hnonpos hi, hnonpos⟩

end Dualizing
