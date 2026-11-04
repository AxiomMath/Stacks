module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.MatlisExtComparison

import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
import all StacksFrontier.RingTheory.Dualizing.MatlisExtComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Support dimension of Ext into a normalized dualizing complex

Let `A` be a Noetherian local ring and let `K` be a normalized dualizing complex.
For every nonzero finite `A`-module `M`, the support of `Ext^i_A(M, K)` has dimension
at most `-i`.

## Main results

* `Dualizing.supportDim_ext_le_neg_degree` bounds the dimension of
  the support of `Ext^i_A(M, K)` by `-i`.

## Implementation notes

We use `IsNormalizedDualizingComplex`, which expresses
normalization by the isomorphism `RHom_A(κ, K) ≅ κ[0]`.

The dimension `Module.supportDim` takes values in `WithBot ℕ∞`, where the zero
module has dimension `⊥`. Thus the signed bound `-i` is represented by
`Int.toNat (-i)` when `i ≤ 0`, and by `⊥` when `i > 0`; in the latter case the
inequality also records the required vanishing of Ext.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

private lemma extPrecomp_lsmul_zero
    {A : Type u} [CommRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (a : A)
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K 0) :
    extPrecomp (LinearMap.lsmul A M a) K 0 x = a • x := by
  have hmap : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
      (ModuleCat.ofHom (LinearMap.lsmul A M a)) = a • 𝟙 _ := by
    have hcat : ModuleCat.ofHom (LinearMap.lsmul A M a) =
        a • 𝟙 (ModuleCat.of A M) := by
      apply ModuleCat.hom_ext
      ext m
      simp [LinearMap.lsmul_apply]
    rw [hcat, Functor.map_smul, CategoryTheory.Functor.map_id]
  change (ShiftedHom.mk₀ 0 rfl
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
      (ModuleCat.ofHom (LinearMap.lsmul A M a)))).comp x (add_zero 0) = a • x
  rw [hmap, ShiftedHom.mk₀_smul, ShiftedHom.smul_comp, ShiftedHom.mk₀_id_comp]

private noncomputable def extRestrictionLinear
    {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i →ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A (maximalIdealPowerTorsion (A := A) M))) K i where
  toFun := extRestriction M K i
  map_add' := (extRestriction M K i).map_add
  map_smul' a x := by
    rw [RingHom.id_apply, extRestriction_apply, extRestriction_apply, Linear.comp_smul]

private noncomputable def extComparisonLinear
    {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A (quotientMaximalIdealPowerTorsion (A := A) M))) K i →ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i where
  toFun := extComparison M K i
  map_add' := (extComparison M K i).map_add
  map_smul' a x := by
    rw [RingHom.id_apply, extComparison_apply, extComparison_apply, Linear.comp_smul]

private lemma support_subset_of_finiteLength
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : IsFiniteLength A M) :
    Module.support A M ⊆ {IsLocalRing.closedPoint A} := by
  induction hM with
  | of_subsingleton =>
      rw [Module.support_eq_empty_iff.mpr ‹Subsingleton _›]
      simp
  | @of_simple_quotient M _ _ N hS _ ih =>
      let S := M ⧸ N
      have hSsimple : IsSimpleModule A S := hS
      have hSfinite : Module.Finite A S := by
        have : Nontrivial S := hSsimple.nontrivial
        obtain ⟨x, hx⟩ := exists_ne (0 : S)
        exact Module.Finite.of_surjective (LinearMap.toSpanSingleton A S x)
          (hSsimple.toSpanSingleton_surjective A hx)
      have hSsupport : Module.support A S ⊆ {IsLocalRing.closedPoint A} := by
        intro p hp
        have hple : IsLocalRing.maximalIdeal A ≤ p.asIdeal := by
          rw [← IsLocalRing.eq_maximalIdeal hSsimple.annihilator_isMaximal]
          exact (Module.mem_support_iff_of_finite (R := A) (M := S)).mp hp
        exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext
          (le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) hple))
      rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ N) (Submodule.subtype_injective N)
        (Submodule.mkQ_surjective N)]
      exact Set.union_subset ih hSsupport

private lemma supportDim_le_zero_of_finiteLength
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : IsFiniteLength A M) : Module.supportDim A M ≤ 0 := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact (Module.supportDim_eq_bot_of_subsingleton A M).trans_le bot_le
  · have hsupp : Module.support A M = {IsLocalRing.closedPoint A} :=
      (support_subset_of_finiteLength M hM).antisymm
        (Set.singleton_subset_iff.2 (IsLocalRing.closedPoint_mem_support A M))
    rw [Module.supportDim, hsupp]
    have : Nonempty ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) :=
      ⟨⟨IsLocalRing.closedPoint A, rfl⟩⟩
    exact (Order.krullDim_eq_zero : Order.krullDim ({IsLocalRing.closedPoint A} : Set _) = 0).le

private lemma support_subset_of_linearDual
    {A : Type u} [CommRing A] {M E : Type (max v u)}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup E] [Module A E] :
    Module.support A (M →ₗ[A] E) ⊆ Module.support A M := by
  intro p hp
  refine (Module.mem_support_iff_of_finite (R := A) (M := M)).2
    (le_trans ?_ (Module.annihilator_le_of_mem_support hp))
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro f
  ext x
  change a • f x = 0
  rw [← map_smul, ha x, map_zero]

private lemma support_subset_of_ext_zero
    {A : Type u} [CommRing A] {M : Type (max v u)} [AddCommGroup M]
    [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    Module.support A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K 0) ⊆
      Module.support A M := by
  intro p hp
  refine (Module.mem_support_iff_of_finite (R := A) (M := M)).2
    (le_trans ?_ (Module.annihilator_le_of_mem_support hp))
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  rw [← extPrecomp_lsmul_zero M K a x,
    show LinearMap.lsmul A M a = 0 from LinearMap.ext ha, extPrecomp_apply_comp]
  simp

private lemma ext_zero_subsingleton_of_depth_pos
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hdepth : 0 < Module.depth A (IsLocalRing.maximalIdeal A) M) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K 0) := by
  obtain ⟨δ, hleast, hdepthEq⟩ :=
    depth_eq_least_nonzero_negative_ext
      (A := A) (M := M) K hK ‹Nontrivial M›
  by_contra hsub
  have hzero : 0 ∈ {j : ℕ | Nontrivial
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M))
        K (-(j : ℤ)))} := by
    simpa using not_subsingleton_iff_nontrivial.mp hsub
  have hδpos : 0 < δ := by exact_mod_cast hdepthEq ▸ hdepth
  exact not_lt_of_ge (hleast.2 hzero) hδpos

private noncomputable def naturalMatlisLinearEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (c : NaturalMatlisExtComparison A K E)
    (hM : IsFiniteLength A M) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K 0 ≃ₗ[A]
      (M →ₗ[A] E) :=
  (c.equiv M hM).toLinearEquiv fun a x => by
    rw [← extPrecomp_lsmul_zero M K a x, c.naturality M M hM hM (LinearMap.lsmul A M a) x]
    ext y
    exact map_smul (c.equiv M hM x) a y

private lemma nontrivial_of_supportDim_eq_coe {A : Type u} [CommRing A] {N : Type v}
    [AddCommGroup N] [Module A N] {d : ℕ}
    (h : Module.supportDim A N = (d : WithBot ℕ∞)) : Nontrivial N := by
  rcases subsingleton_or_nontrivial N with _ | hN
  · rw [Module.supportDim_eq_bot_of_subsingleton A N] at h
    exact absurd h.symm (by simp)
  · exact hN

/-- If `M` has positive support dimension `d`, its quotient by the torsion submodule is
nontrivial of the same dimension and has positive depth. -/
private lemma quotientTorsion_nontrivial_depth_pos
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M] {d : ℕ}
    (hd : Module.supportDim A M = (d : WithBot ℕ∞)) (hd0 : d ≠ 0) :
    Module.supportDim A (quotientMaximalIdealPowerTorsion (A := A) M) = (d : WithBot ℕ∞) ∧
      Nontrivial (quotientMaximalIdealPowerTorsion (A := A) M) ∧
      0 < Module.depth A (IsLocalRing.maximalIdeal A)
        (quotientMaximalIdealPowerTorsion (A := A) M) := by
  have hMdimpos : 0 < Module.supportDim A M := by
    rw [hd]
    exact_mod_cast Nat.pos_of_ne_zero hd0
  have hQdim := (supportDim_quotientMaximalIdealPowerTorsion A M hMdimpos).trans hd
  exact ⟨hQdim, nontrivial_of_supportDim_eq_coe hQdim,
    depth_quotientMaximalIdealPowerTorsion_pos A M⟩

-- Finite length and Matlis exactness make this proof's elaboration larger than the default budget.
private lemma supportDim_ext_zero_le_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] :
    Module.supportDim A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) K 0) ≤ 0 := by
  obtain ⟨d, hd⟩ := exists_supportDim_eq_nat (A := A) M
  by_cases hd0 : d = 0
  · have hdim := supportDim_le_of_support_subset (A := A) (M := moduleExtInto M K 0)
      (N := M) (support_subset_of_ext_zero (A := A) (M := M) K)
    rwa [hd, hd0] at hdim
  · let T := maximalIdealPowerTorsion (A := A) M
    let Q := quotientMaximalIdealPowerTorsion (A := A) M
    have hTfinite : IsFiniteLength A T := by
      simpa [T] using isFiniteLength_maximalIdealPowerTorsion A M
    obtain ⟨-, _, hQdepth⟩ := quotientTorsion_nontrivial_depth_pos M hd hd0
    let κcat := (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))
    obtain ⟨Ecat, j, hj, hHull⟩ := Module.exists_isInjectiveHull.{u, v} A κcat
    have : Mono j := hj
    let E : Type (max v u) := Ecat
    obtain ⟨c⟩ := exists_naturalMatlisExtComparison.{u, v} A K hK E j hHull
    let e := naturalMatlisLinearEquiv (A := A) T E K c hTfinite
    let g := e.toLinearMap.comp (extRestrictionLinear (A := A) (M := M) K 0)
    let cmp := extComparisonLinear (A := A) (M := M) K 0
    have hexact : Function.Exact cmp g := by
      change Function.Exact (extComparison M K 0)
        (fun x => c.equiv T hTfinite (extRestriction M K 0 x))
      exact exact_extComparison_matlisRestriction A M E K c
    have : Subsingleton (moduleExtInto Q K 0) := ext_zero_subsingleton_of_depth_pos K hK hQdepth
    have hginj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun x hx => by
      obtain ⟨z, rfl⟩ := (hexact x).mp hx
      rw [Subsingleton.elim z 0, map_zero]
    exact (Module.supportDim_le_of_injective g hginj).trans
      ((supportDim_le_of_support_subset (A := A)
        (support_subset_of_linearDual (A := A) (M := T) (E := E))).trans
        (supportDim_le_zero_of_finiteLength T hTfinite))

private lemma intToNatNegSucc_add_one {i : ℤ} (hi : i < 0) :
    (((Int.toNat (-(i + 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1 =
      (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  exact_mod_cast (by omega : Int.toNat (-(i + 1)) + 1 = Int.toNat (-i))

-- Strong induction expands the Ext comparison and dimension arithmetic at each recursive step.
private lemma supportDim_ext_le_nonpos_of_neg
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (d : ℕ) (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M]
    (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (i : ℤ) (hiNeg : i < 0)
    (ih : ∀ m < d, ∀ (N : Type (max v u)) [AddCommGroup N] [Module A N] [Module.Finite A N]
      [Nontrivial N], Module.supportDim A N = (m : WithBot ℕ∞) → ∀ j : ℤ, j ≤ 0 →
      Module.supportDim A
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A N)) K j) ≤
        (((Int.toNat (-j) : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    Module.supportDim A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) ≤
      (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  let X := DerivedCategory.Ext
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i
  rcases subsingleton_or_nontrivial X with _ | _
  · exact (Module.supportDim_eq_bot_of_subsingleton A X).trans_le bot_le
  by_cases hd0 : d = 0
  · have : 0 ≤ i := by
      simpa using (ext_degree_mem_Icc_of_nontrivial K hK 0 (by simpa [hd0] using hd) i ‹_›).1
    omega
  let Q := quotientMaximalIdealPowerTorsion (A := A) M
  obtain ⟨hQdim, _, hQdepth⟩ := quotientTorsion_nontrivial_depth_pos M hd hd0
  obtain ⟨f, hf, hreg⟩ := exists_regular_of_depth_pos_universe hQdepth
  obtain ⟨d', hd', hQfDim, hQftriv⟩ :=
    exists_quotient_supportDim_eq_nat Q d hQdim hf hreg
  have : Nontrivial (QuotSMulTop f Q) := hQftriv
  let e := LinearEquiv.ofBijective (extComparisonLinear (A := A) (M := M) K i)
    (bijective_extComparison_quotientMaximalIdealPowerTorsion A M K hK i hiNeg)
  have : Nontrivial (moduleExtInto Q K i) := Equiv.nontrivial e.toEquiv
  let emb := quotientExtEmbedding Q K f hreg i
  calc
    Module.supportDim A X = Module.supportDim A (moduleExtInto Q K i) :=
      (Module.supportDim_eq_of_equiv e).symm
    _ ≤ Module.supportDim A (QuotSMulTop f (moduleExtInto Q K i)) + 1 :=
      supportDim_ext_quotient_add_one Q K hK.1 hf i
    _ ≤ Module.supportDim A (moduleExtInto (QuotSMulTop f Q) K (i + 1)) + 1 := by
      simpa [add_comm] using add_le_add_right
        (Module.supportDim_le_of_injective emb.1 emb.2.1) 1
    _ ≤ (((Int.toNat (-(i + 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1 := by
      simpa [add_comm] using
        add_le_add_right (ih d' hd' (QuotSMulTop f Q) hQfDim (i + 1) (by omega)) 1
    _ = (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) := intToNatNegSucc_add_one hiNeg

private theorem supportDim_ext_le_nonpos
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (d : ℕ) (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M]
    (hd : Module.supportDim A M = (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ≤ 0) :
    Module.supportDim A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i) ≤
      (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  induction d using Nat.strong_induction_on generalizing M i with
  | h d ih =>
      obtain rfl | hiNeg := hi.eq_or_lt
      · simpa using supportDim_ext_zero_le_zero K hK M
      · exact supportDim_ext_le_nonpos_of_neg K hK d M hd i hiNeg ih

/-- **Stacks Project, Tag 0A7U, support bound.** If `K` is a normalized dualizing
complex over a Noetherian local ring `A` and `M` is a nonzero finite `A`-module, then
the support of `Ext^i_A(M, K)` has dimension at most `-i` for every integer `i`. -/
@[stacks 0A7U "ext_support_bound", sga "2 V 3.1" "(ii)"]
public theorem supportDim_ext_le_neg_degree
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (M : Type (max v u))
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    (hK : IsNormalizedDualizingComplex K) (i : ℤ) :
    Module.supportDim A
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) K i) ≤
      if i ≤ 0 then (((Int.toNat (-i) : ℕ) : ℕ∞) : WithBot ℕ∞) else ⊥ := by
  obtain ⟨d, hd⟩ := exists_supportDim_eq_nat (A := A) M
  by_cases hi : i ≤ 0
  · simpa [hi] using supportDim_ext_le_nonpos K hK d M hd i hi
  · let X := DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i
    rcases subsingleton_or_nontrivial X with _ | _
    · rw [Module.supportDim_eq_bot_of_subsingleton]
      simp [hi]
    · exact absurd (ext_degree_mem_Icc_of_nontrivial K hK d hd i ‹_›).2 hi

end Dualizing
