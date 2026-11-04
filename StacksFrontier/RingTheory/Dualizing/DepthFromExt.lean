module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Regular.LinearMap
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.MatlisExtComparison

import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds

/-!
# Depth detected by a normalized dualizing complex

For a nonzero finite module over a Noetherian local ring, its depth is the least
nonnegative degree whose negative Ext into a normalized dualizing complex is nonzero.

## Main definitions

No new definitions are introduced.

## Main results

* `Dualizing.depth_eq_least_nonzero_negative_ext` characterizes depth by
  the first nonzero negative Ext into a normalized dualizing complex.

## Implementation notes

Normalization is expressed by `IsNormalizedDualizingComplex`, which uses a
universe lift of the residue field when the module universe is larger than the ring
universe. Nonnegative integers are represented by natural numbers, and the assertion
that the indicated degree is the smallest one is expressed by `IsLeast`.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

private lemma finite_supportDim_of_finite_nontrivial
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    ∃ d : ℕ, Module.supportDim A M = (d : WithBot ℕ∞) := by
  have hne_top : Module.supportDim A M ≠ ⊤ := fun h =>
    ringKrullDim_ne_top (top_le_iff.mp (h ▸ Module.supportDim_le_ringKrullDim A M))
  lift (Module.supportDim A M) to ℕ∞ using Module.supportDim_ne_bot_of_nontrivial A M with d hd
  have hd' : d ≠ ⊤ := by
    intro h
    apply hne_top
    simp [h] at hd ⊢
  lift d to ℕ using hd'
  exact ⟨d, rfl⟩

private lemma positive_ext_subsingleton_normalized
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max v u} A))
    (homega : IsNormalizedDualizingComplex omega) (i : ℤ) (hi : 0 < i) :
    Subsingleton (moduleExtInto M omega i) := by
  by_cases hM : Nontrivial M
  · obtain ⟨d, hd⟩ := finite_supportDim_of_finite_nontrivial (A := A) (M := M)
    exact not_nontrivial_iff_subsingleton.mp fun hExt =>
      (not_lt.mpr (ext_degree_mem_Icc_of_nontrivial omega homega d hd i hExt).2) hi
  · have : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      (ModuleCat.of A M)) := Functor.map_isZero _
      (ModuleCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp hM))
    exact ⟨fun x y => this.eq_of_src x y⟩

private lemma nontrivial_hom_to_injectiveHull
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    {E : Type (max v u)} [AddCommGroup E] [Module A E]
    (f : IsLocalRing.ResidueField A →ₗ[A] M)
    (hf : Function.Injective f)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶
        ModuleCat.of A E)
    [Mono i]
    [CategoryTheory.Injective (ModuleCat.of A E)] :
    Nontrivial
      ((maximalIdealPowerTorsion (A := A) M) →ₗ[A]
        E) := by
  let T := maximalIdealPowerTorsion (A := A) M
  have hmem : ∀ x : IsLocalRing.ResidueField A, f x ∈ T := by
    intro x
    change f x ∈ (IsLocalRing.maximalIdeal A).primaryComponent M
    rw [Ideal.primaryComponent_mem]
    refine ⟨1, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha' : (a : A) ∈ IsLocalRing.maximalIdeal A := by simpa using a.property
    have hs : (a : A) • x = 0 := by
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change (Submodule.Quotient.mk ((a : A) * r) : A ⧸ IsLocalRing.maximalIdeal A) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact (IsLocalRing.maximalIdeal A).mul_mem_right r ha'
    rw [← map_smul f (a : A) x, hs, map_zero]
  let fT : IsLocalRing.ResidueField A →ₗ[A] T := f.codRestrict T hmem
  have hfT : Function.Injective fT := fun x y hxy =>
    hf (by simpa [fT] using congrArg (fun z : T => (z : M)) hxy)
  let fi : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ ModuleCat.of A T :=
    ModuleCat.ofHom (fT.comp ULift.moduleEquiv.toLinearMap)
  have : Mono fi :=
    (ModuleCat.mono_iff_injective fi).mpr (hfT.comp ULift.moduleEquiv.injective)
  let g : ModuleCat.of A T ⟶ ModuleCat.of A E := CategoryTheory.Injective.factorThru i fi
  have hcomp : fi ≫ g = i := CategoryTheory.Injective.comp_factorThru i fi
  have hi_ne : i ≠ 0 := by
    intro hz
    have hinj : Function.Injective i.hom := ModuleCat.mono_iff_injective i |>.mp inferInstance
    have hmap : i.hom = 0 := by simpa using congrArg (fun j => j.hom) hz
    exact not_subsingleton (ULift.{v} (A ⧸ IsLocalRing.maximalIdeal A))
      ⟨fun x y => hinj (by rw [hmap]; rfl)⟩
  have hg : g ≠ 0 := fun hz => hi_ne (by rw [← hcomp, hz, comp_zero])
  exact nontrivial_of_ne g.hom 0 fun h => hg (ModuleCat.hom_ext h)

private lemma exists_residueField_mono_of_depth_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M]
    (hdepth : Module.depth A (IsLocalRing.maximalIdeal A) M = 0) :
    ∃ f : (A ⧸ IsLocalRing.maximalIdeal A) →ₗ[A] M, Function.Injective f := by
  have hdepthSup : Module.depthSup A (IsLocalRing.maximalIdeal A) M = 0 := by
    rwa [Module.depth, ite_eq_right (Module.maximalIdeal_smul_top_ne_top _),
      ← Module.depthSup_eq_iSup] at hdepth
  have hHom : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) →ₗ[A] M) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    obtain ⟨r, hrann, hreg⟩ :=
      (IsSMulRegular.subsingleton_linearMap_iff (R := A)
        (M := M) (N := A ⧸ IsLocalRing.maximalIdeal A)).mp hsub
    rw [Ideal.annihilator_quotient] at hrann
    have hregSeq : RingTheory.Sequence.IsRegular M [r] := by
      have : Nontrivial (QuotSMulTop r M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hrann
      rw [RingTheory.Sequence.isRegular_cons_iff]
      exact ⟨hreg, RingTheory.Sequence.IsRegular.nil A (QuotSMulTop r M)⟩
    have hle : (1 : ℕ∞) ≤ Module.depthSup A (IsLocalRing.maximalIdeal A) M := by
      simpa using Module.le_depthSup (R := A) (I := IsLocalRing.maximalIdeal A)
        (M := M) (rs := [r]) (hreg := hregSeq) (hmem := by simpa using hrann)
    simp [hdepthSup] at hle
  obtain ⟨f, hf⟩ := exists_ne (0 : (A ⧸ IsLocalRing.maximalIdeal A) →ₗ[A] M)
  have : IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A) := by
    rw [isSimpleModule_iff_quot_maximal]
    exact ⟨IsLocalRing.maximalIdeal A, IsLocalRing.maximalIdeal.isMaximal A,
      ⟨LinearEquiv.refl A _⟩⟩
  exact ⟨f, (LinearMap.injective_or_eq_zero f).resolve_right hf⟩

private lemma ext_zero_nontrivial_of_depth_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max v u} A))
    (homega : IsNormalizedDualizingComplex omega)
    (hM : Nontrivial M)
    (hdepth : Module.depth A (IsLocalRing.maximalIdeal A) M = 0) :
    Nontrivial (moduleExtInto M omega 0) := by
  obtain ⟨f, hf⟩ := exists_residueField_mono_of_depth_zero hdepth
  let kObj := (ModuleCat.uliftFunctor.{v} A).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A))
  obtain ⟨E, i, _, hiHull⟩ := Module.exists_isInjectiveHull A kObj
  obtain ⟨c⟩ := exists_naturalMatlisExtComparison
    (A := A) (ω := omega) (hω := homega) (E := E) (j := i) hiHull
  let T := maximalIdealPowerTorsion (A := A) M
  have : CategoryTheory.Injective (ModuleCat.of A E) := hiHull.1
  have : Nontrivial (T →ₗ[A] E) := nontrivial_hom_to_injectiveHull f hf i
  let e := c.equiv T (isFiniteLength_maximalIdealPowerTorsion A M)
  have : Subsingleton
      (moduleExtInto (quotientMaximalIdealPowerTorsion (A := A) M) omega 1) :=
    positive_ext_subsingleton_normalized omega homega 1 (by norm_num)
  have hsurj : Function.Surjective (e.toAddMonoidHom.comp (extRestriction M omega 0)) :=
    fun y => (exact_matlisRestriction_boundary A M E omega c y).mp (Subsingleton.elim _ _)
  exact hsurj.nontrivial

private lemma finite_module_subsingleton_of_surj_smul
    {A : Type u} [CommRing A] [IsLocalRing A]
    {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {r : A} (hr : r ∈ IsLocalRing.maximalIdeal A)
    (hsurj : Function.Surjective (r • · : N → N)) : Subsingleton N := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  open scoped Pointwise in
  refine Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator (M := N)
    (IsLocalRing.maximalIdeal_le_jacobson _ hr) (le_antisymm (fun y _ => ?_) le_top)
  rw [Submodule.mem_smul_pointwise_iff_exists]
  exact (hsurj y).imp fun z hz => ⟨Submodule.mem_top, hz⟩

private lemma exists_depth_eq_natCast
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    ∃ d : ℕ, Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞) := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (Module.depth_lt_top A
    (IsLocalRing.maximalIdeal A) M (Module.maximalIdeal_smul_top_ne_top (R := A) M)).ne
  exact ⟨d, hd.symm⟩

private lemma exists_regular_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] {d : ℕ}
    (hdepth : Module.depth A (IsLocalRing.maximalIdeal A) M = ((d + 1 : ℕ) : ℕ∞)) :
    ∃ r ∈ IsLocalRing.maximalIdeal A, IsSMulRegular M r := by
  have htop := Module.maximalIdeal_smul_top_ne_top (R := A) M
  obtain ⟨rs, hrs, hrsreg, hlen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (IsLocalRing.maximalIdeal A) M).2 htop [] (by simp)
      (RingTheory.Sequence.IsRegular.nil A M)
  have hrsne : rs ≠ [] := by
    rintro rfl
    simp only [List.append_nil, List.length_nil, CharP.cast_eq_zero, hdepth, Nat.cast_add,
      Nat.cast_one] at hlen
    exact absurd (by exact_mod_cast hlen : (0 : ℕ) = d + 1) (by omega)
  obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hrsne
  have hrsreg' : RingTheory.Sequence.IsRegular M (r :: rs') := by simpa using hrsreg
  have hrs' : ∀ s ∈ r :: rs', s ∈ IsLocalRing.maximalIdeal A := by simpa using hrs
  exact ⟨r, hrs' r (by simp), ((RingTheory.Sequence.isRegular_cons_iff M r rs').mp hrsreg').1⟩

/-- The induction bridge: the first nonzero negative Ext is exactly minus the depth. -/
private theorem ext_depth_induction
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max v u} A))
    (homega : IsNormalizedDualizingComplex omega) :
    ∀ d : ℕ, ∀ (M : Type (max v u)) [AddCommGroup M] [Module A M]
      [Module.Finite A M] [Nontrivial M],
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞) →
      (Nontrivial (moduleExtInto M omega (-(d : ℤ))) ∧
        ∀ i : ℤ, -(d : ℤ) < i → ¬ Nontrivial (moduleExtInto M omega i)) := by
  intro d
  induction d with
  | zero =>
    intro M _ _ _ _ hdepth
    exact ⟨ext_zero_nontrivial_of_depth_zero omega homega inferInstance hdepth, fun i hi =>
      not_nontrivial_iff_subsingleton.mpr
        (positive_ext_subsingleton_normalized (M := M) omega homega i (by simpa using hi))⟩
  | succ d ih =>
    intro M _ _ _ _ hdepth
    obtain ⟨r, hr, hreg⟩ := exists_regular_mem_maximalIdeal (M := M) hdepth
    have : Nontrivial (QuotSMulTop r M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hr
    have hrec := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (IsLocalRing.maximalIdeal A) M).1 r hr hreg
    have hqdepth : Module.depth A (IsLocalRing.maximalIdeal A) (QuotSMulTop r M) =
        (d : ℕ∞) := by
      rw [hdepth, Nat.cast_succ] at hrec
      exact WithTop.add_right_cancel (by exact_mod_cast (ENat.natCast_ne_top 1)) hrec
    obtain ⟨hqnontriv, hqvanish⟩ := ih (QuotSMulTop r M) hqdepth
    have hvanish : ∀ i : ℤ, -((d + 1 : ℕ) : ℤ) < i →
        ¬ Nontrivial (moduleExtInto M omega i) := fun i hi => by
      have := moduleFinite_ext (A := A) (M := M) omega homega.1 i
      have : Subsingleton (moduleExtInto (QuotSMulTop r M) omega (i + 1)) :=
        not_nontrivial_iff_subsingleton.mp (hqvanish (i + 1) (by omega))
      exact not_nontrivial_iff_subsingleton.mpr
        (finite_module_subsingleton_of_surj_smul hr fun y =>
          (exact_lsmul_extConnecting M omega r hreg i y).mp (Subsingleton.elim _ _))
    have hdegree : -((d + 1 : ℕ) : ℤ) + 1 = -(d : ℤ) := by omega
    have : Nontrivial
        (moduleExtInto (QuotSMulTop r M) omega
          (-((d + 1 : ℕ) : ℤ) + 1)) := by simpa [hdegree] using hqnontriv
    have : Subsingleton
        (moduleExtInto M omega (-((d + 1 : ℕ) : ℤ) + 1)) :=
      not_nontrivial_iff_subsingleton.mp (by simpa [hdegree] using hvanish (-(d : ℤ)) (by omega))
    have hconnSurj : Function.Surjective
        (extConnecting M omega r hreg (-((d + 1 : ℕ) : ℤ))) := fun y =>
      (exact_extConnecting_extFromQuotient M omega r hreg _ y).mp (Subsingleton.elim _ _)
    exact ⟨hconnSurj.nontrivial, hvanish⟩

/-- **Stacks Project, Tag 0A7U, part (3).** For a nonzero finite module over a
Noetherian local ring, depth is the least nonnegative integer `δ` for which
`Ext^(-δ)(M, ω_A^•)` is nonzero. -/
@[stacks 0A7U "depth_from_ext"]
public theorem depth_eq_least_nonzero_negative_ext
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max v u} A))
    (homega : IsNormalizedDualizingComplex omega)
    (hM : Nontrivial M) :
    ∃ delta : ℕ,
      IsLeast
          {i : ℕ |
            Nontrivial
              (DerivedCategory.Ext
                ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
                  (ModuleCat.of A M))
                omega (-(i : ℤ)))}
          delta ∧
        Module.depth A (IsLocalRing.maximalIdeal A) M = (delta : ℕ∞) := by
  obtain ⟨delta, hdepth⟩ := exists_depth_eq_natCast (A := A) (M := M)
  obtain ⟨hnt, hvanish⟩ := ext_depth_induction omega homega delta M hdepth
  exact ⟨delta, ⟨hnt, fun i hi => not_lt.mp fun h => hvanish (-(i : ℤ)) (by omega) hi⟩, hdepth⟩

end Dualizing
