module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiscriminantGroup
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import StacksCore.Tactic.StacksAttribute

/-!
# Torsion in the cokernel of a symmetric matrix, bounded by cycle rank

For a symmetric integer matrix with nonnegative off-diagonal entries, a
strictly positive kernel vector and connected support, the dimension of the
prime torsion in its cokernel is bounded by the cycle rank of its support
graph.

## Main results

* `Matrix.finrank_torsionBy_matrixCokernel_le_cycleRank`.

## Implementation notes

The indices form an arbitrary finite linearly ordered type rather than a finite
interval. The cokernel is the quotient by the range of `Matrix.mulVecLin`, and
its prime torsion is taken with `AddSubgroup.torsionBy`. To avoid truncated
subtraction the source inequality is written with the number of vertices added
to its left-hand side. Coprimality is required only for the positive edge
weights and the coordinates of the kernel vector, which are the integers the
source proof uses.

## References

* [Stacks Project, Tag 0C6X](https://stacks.math.columbia.edu/tag/0C6X)
-/

@[expose] public section

open Matrix
open LinearMap.BilinForm

namespace Matrix

private noncomputable def dotForm {κ : Type*} [Fintype κ] :
    LinearMap.BilinForm ℤ (κ → ℤ) :=
  ∑ i, LinearMap.BilinForm.linMulLin (LinearMap.proj i) (LinearMap.proj i)

private lemma dotForm_apply {κ : Type*} [Fintype κ] (x y : κ → ℤ) :
    dotForm x y = ∑ i, x i * y i := by
  simp [dotForm, LinearMap.BilinForm.linMulLin]

private lemma dotForm_isSymm {κ : Type*} [Fintype κ] :
    (dotForm (κ := κ)).IsSymm :=
  ⟨fun x y => by simp [dotForm_apply, mul_comm]⟩

private lemma dotForm_bijective {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Function.Bijective (dotForm (κ := κ)) :=
  ⟨fun x y h => funext fun i => by
      simpa [dotForm_apply, Pi.single_apply] using LinearMap.congr_fun h (Pi.single i 1),
    fun φ => ⟨fun i => φ (Pi.single i 1), (Pi.basisFun ℤ κ).ext fun i => by
      simp [dotForm_apply, Pi.single_apply]⟩⟩

private lemma dotForm_pos {κ : Type*} [Fintype κ] (x : κ → ℤ) (hx : x ≠ 0) :
    0 < dotForm x x := by
  rw [dotForm_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

private noncomputable def weightedDotForm {E : Type*} [Fintype E]
    (w : E → ℤ) : LinearMap.BilinForm ℤ (E → ℤ) :=
  ∑ e, w e • LinearMap.BilinForm.linMulLin (LinearMap.proj e) (LinearMap.proj e)

private lemma weightedDotForm_apply {E : Type*} [Fintype E] (w : E → ℤ)
    (x y : E → ℤ) : weightedDotForm w x y = ∑ e, w e * x e * y e := by
  simp [weightedDotForm, LinearMap.BilinForm.linMulLin, mul_assoc]

private lemma weightedDotForm_isSymm {E : Type*} [Fintype E] (w : E → ℤ) :
    (weightedDotForm w).IsSymm :=
  ⟨fun x y => by
    rw [weightedDotForm_apply, weightedDotForm_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_right_comm _ _ _⟩

private lemma weightedDotForm_pos {E : Type*} [Fintype E] (w : E → ℤ)
    (hw : ∀ e, 0 < w e) (x : E → ℤ) (hx : x ≠ 0) :
    0 < weightedDotForm w x x := by
  rw [weightedDotForm_apply]
  obtain ⟨e, he⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun j _ => ?_) ⟨e, Finset.mem_univ e, ?_⟩
  · simpa [mul_assoc] using mul_nonneg (hw j).le (mul_self_nonneg (x j))
  · simpa [mul_assoc] using mul_pos (hw e) (mul_self_pos.mpr he)

private def incidenceMap {V E : Type*} [DecidableEq E]
    (src tgt : E → V) : (V → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun x e := x (src e) - x (tgt e)
  map_add' x y := by
    ext e
    simp only [Pi.add_apply]
    abel
  map_smul' a x := by
    ext e
    simp only [Pi.smul_apply, smul_eq_mul]
    change a * x (src e) - a * x (tgt e) = a * (x (src e) - x (tgt e))
    rw [mul_sub]

private def incidenceColumn {V : Type*} [DecidableEq V] (s t : V) :
    ℤ →ₗ[ℤ] (V → ℤ) where
  toFun a i := (if s = i then a else 0) - (if t = i then a else 0)
  map_add' a b := by
    ext i
    by_cases hs : s = i <;> by_cases ht : t = i <;> simp [hs, ht]
    abel
  map_smul' a b := by
    ext i
    by_cases hs : s = i <;> by_cases ht : t = i <;> simp [hs, ht]

private noncomputable def weightedAdjoint {V E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq V] (src tgt : E → V) (w : E → ℤ) :
    (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  ∑ e, (incidenceColumn (src e) (tgt e)).comp
    (((LinearMap.lsmul ℤ ℤ) (w e)).comp (LinearMap.proj e))

private lemma weightedAdjoint_apply {V E : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq V] (src tgt : E → V) (w : E → ℤ) (y : E → ℤ) (i : V) :
    weightedAdjoint src tgt w y i = ∑ e,
      ((if src e = i then w e * y e else 0) -
       (if tgt e = i then w e * y e else 0)) := by
  simp [weightedAdjoint, incidenceColumn, LinearMap.lsmul_apply]

private lemma incidence_weighted_adjoint
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ) (y : E → ℤ) (x : V → ℤ) :
    dotForm (weightedAdjoint src tgt w y) x =
      weightedDotForm w y (incidenceMap src tgt x) := by
  rw [dotForm_apply, weightedDotForm_apply]
  simp_rw [weightedAdjoint_apply, incidenceMap, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i e =>
      if src e = i then w e * y e * x i else 0),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i e =>
      if tgt e = i then w e * y e * x i else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  show (∑ e, w e * y e * x (src e)) -
      (∑ e, w e * y e * x (tgt e)) =
    ∑ e, w e * y e * (x (src e) - x (tgt e))
  simp_rw [mul_sub]
  rw [← Finset.sum_sub_distrib]

private lemma incidence_range_quotient_torsionFree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (hV : Nonempty V)
    (hconn : ∀ I : Set V, I.Nonempty → I ≠ Set.univ →
      ∃ e, (src e ∈ I ∧ tgt e ∉ I) ∨ (tgt e ∈ I ∧ src e ∉ I)) :
    Module.IsTorsionFree ℤ
      ((E → ℤ) ⧸ LinearMap.range (incidenceMap src tgt)) := by
  classical
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro c q hq
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  obtain ⟨u, rfl⟩ := (LinearMap.range (incidenceMap src tgt)).mkQ_surjective q
  have hcu : c • u ∈ LinearMap.range (incidenceMap src tgt) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_zsmul]
    exact hq
  obtain ⟨y, hy⟩ := hcu
  obtain ⟨v₀⟩ := hV
  have hedge (e : E) : c ∣ y (src e) - y (tgt e) := ⟨u e, congrFun hy e⟩
  let I : Set V := {v | c ∣ y v - y v₀}
  have hIall : I = Set.univ := by
    by_contra hproper
    obtain ⟨e, he | he⟩ := hconn I ⟨v₀, by simp [I]⟩ hproper
    · refine he.2 ?_
      have h := dvd_sub (he.1 : c ∣ y (src e) - y v₀) (hedge e)
      rwa [sub_sub_sub_cancel_left] at h
    · refine he.2 ?_
      have h := dvd_add (he.1 : c ∣ y (tgt e) - y v₀) (hedge e)
      rwa [add_comm, sub_add_sub_cancel] at h
  have hdiv (v : V) : c ∣ y v - y v₀ := Set.eq_univ_iff_forall.mp hIall v
  let z : V → ℤ := fun v => (y v - y v₀) / c
  have hz (v : V) : c * z v = y v - y v₀ :=
    Int.mul_ediv_cancel_of_dvd (hdiv v)
  have heq : u = incidenceMap src tgt z := by
    funext e
    apply mul_left_cancel₀ hc
    show c * u e = c * (z (src e) - z (tgt e))
    have h : y (src e) - y (tgt e) = c * u e := congrFun hy e
    rw [mul_sub, hz, hz, ← h]
    ring
  rw [heq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨z, rfl⟩

private lemma finrank_ker_incidence_eq_one
    {V E K : Type*} [Fintype V] [Fintype E] [CommRing K] [IsDomain K]
    (src tgt : E → V) (hV : Nonempty V)
    (hconn : ∀ I : Set V, I.Nonempty → I ≠ Set.univ →
      ∃ e, (src e ∈ I ∧ tgt e ∉ I) ∨ (tgt e ∈ I ∧ src e ∉ I)) :
    let d : (V → K) →ₗ[K] (E → K) :=
      { toFun := fun x e => x (src e) - x (tgt e)
        map_add' := by intro x y; ext e; simp only [Pi.add_apply]; abel
        map_smul' := by
          intro a x
          ext e
          simp only [Pi.smul_apply, smul_eq_mul]
          change a * x (src e) - a * x (tgt e) = a * (x (src e) - x (tgt e))
          rw [mul_sub] }
    Module.finrank K (LinearMap.ker d) = 1 := by
  classical
  intro d
  let one : V → K := fun _ => 1
  have hone : one ≠ 0 := fun h => by
    obtain ⟨v⟩ := hV
    simpa [one] using congrFun h v
  have hker : LinearMap.ker d = Submodule.span K {one} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨v₀⟩ := hV
      have hedge (e : E) : x (src e) = x (tgt e) :=
        sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp hx) e)
      have hall (v : V) : x v = x v₀ := by
        by_contra hv
        obtain ⟨e, he | he⟩ := hconn {w | x w = x v₀} ⟨v₀, rfl⟩
          fun h => hv (Set.eq_univ_iff_forall.mp h v)
        · exact he.2 ((hedge e).symm.trans he.1)
        · exact he.2 ((hedge e).trans he.1)
      exact Submodule.mem_span_singleton.mpr ⟨x v₀, funext fun v => by simp [one, hall v]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr (funext fun e => by simp [d, one])
  rw [hker, ← LinearMap.range_toSpanSingleton,
    LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton K hone)),
    Module.finrank_self]

universe u

private lemma finrank_range_add_finrank_ker_int
    {M N : Type u} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    letI : Module ℤ (LinearMap.range f) := (LinearMap.range f).module
    letI : Module ℤ (LinearMap.ker f) := (LinearMap.ker f).module
    Module.finrank ℤ (LinearMap.range f) +
      Module.finrank ℤ (LinearMap.ker f) = Module.finrank ℤ M := by
  let : Module ℤ (LinearMap.range f) := (LinearMap.range f).module
  let : Module ℤ (LinearMap.ker f) := (LinearMap.ker f).module
  let : Module.Finite ℤ (LinearMap.range f) := Module.Finite.range f
  let : Module.Finite ℤ (LinearMap.ker f) :=
    Module.Finite.of_fg (Submodule.FG.of_le
      (Module.finite_def.mp inferInstance) le_top)
  have h := LinearMap.rank_range_add_rank_ker f
  rw [← Module.finrank_eq_rank ℤ (LinearMap.range f), ← Module.finrank_eq_rank ℤ (LinearMap.ker f),
    ← Module.finrank_eq_rank ℤ M] at h
  exact_mod_cast h

private def coordinateSum {V : Type*} [Fintype V] :
    (V → ℤ) →ₗ[ℤ] ℤ where
  toFun x := ∑ v, x v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by
    simp [Finset.mul_sum]

private def coordinateSumLift {V : Type u} [Fintype V] :
    (V → ℤ) →ₗ[ℤ] ULift.{u} ℤ where
  toFun x := ⟨∑ v, x v⟩
  map_add' x y := by
    apply ULift.ext
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    apply ULift.ext
    simp [Finset.mul_sum]

private lemma coordinateSum_surjective
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] :
    Function.Surjective (coordinateSum (V := V)) := by
  intro z
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨Pi.single v z, ?_⟩
  simp [coordinateSum, Pi.single_apply]

private lemma coordinateSum_weightedAdjoint_eq_zero
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ) (y : E → ℤ) :
    coordinateSum (weightedAdjoint src tgt w y) = 0 := by
  simp only [coordinateSum, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [weightedAdjoint_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun v e => if src e = v then w e * y e else 0),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun v e => if tgt e = v then w e * y e else 0)]
  simp

private lemma ker_weightedAdjoint_comp_incidenceMap
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ)
    (hw : ∀ e, 0 < w e) :
    LinearMap.ker ((weightedAdjoint src tgt w).comp (incidenceMap src tgt)) =
      LinearMap.ker (incidenceMap src tgt) := by
  refine le_antisymm (fun x hx => ?_) (LinearMap.ker_le_ker_comp _ _)
  by_contra hnot
  refine (weightedDotForm_pos w hw _ (by simpa only [LinearMap.mem_ker] using hnot)).ne' ?_
  rw [← incidence_weighted_adjoint,
    show weightedAdjoint src tgt w (incidenceMap src tgt x) = 0 from hx]
  simp

private lemma finrank_ker_weightedAdjoint
    {V E : Type u} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ)
    (hw : ∀ e, 0 < w e) (hV : Nonempty V)
    (hconn : ∀ I : Set V, I.Nonempty → I ≠ Set.univ →
      ∃ e, (src e ∈ I ∧ tgt e ∉ I) ∨ (tgt e ∈ I ∧ src e ∉ I)) :
    let ds := weightedAdjoint src tgt w
    letI : Module ℤ (LinearMap.ker ds) := (LinearMap.ker ds).module
    Module.finrank ℤ (LinearMap.ker ds) + Fintype.card V =
      1 + Fintype.card E := by
  classical
  intro ds
  let d := incidenceMap src tgt
  let c := coordinateSumLift (V := V)
  let : Module ℤ (LinearMap.range d) := (LinearMap.range d).module
  let : Module ℤ (LinearMap.ker d) := (LinearMap.ker d).module
  let : Module ℤ (LinearMap.range ds) := (LinearMap.range ds).module
  let : Module ℤ (LinearMap.ker ds) := (LinearMap.ker ds).module
  let : Module ℤ (LinearMap.range (ds.comp d)) :=
    (LinearMap.range (ds.comp d)).module
  let : Module ℤ (LinearMap.ker (ds.comp d)) :=
    (LinearMap.ker (ds.comp d)).module
  let : Module ℤ (LinearMap.range c) := (LinearMap.range c).module
  let : Module ℤ (LinearMap.ker c) := (LinearMap.ker c).module
  have hkerD : Module.finrank ℤ (LinearMap.ker d) = 1 :=
    finrank_ker_incidence_eq_one src tgt hV hconn
  have hkerComp : LinearMap.ker (ds.comp d) = LinearMap.ker d :=
    ker_weightedAdjoint_comp_incidenceMap src tgt w hw
  have hdimV : Module.finrank ℤ (V → ℤ) = Fintype.card V :=
    Module.finrank_fintype_fun_eq_card ℤ
  have hdimE : Module.finrank ℤ (E → ℤ) = Fintype.card E :=
    Module.finrank_fintype_fun_eq_card ℤ
  have hrankD := finrank_range_add_finrank_ker_int d
  have hrankComp := finrank_range_add_finrank_ker_int (ds.comp d)
  have hrankDS := finrank_range_add_finrank_ker_int ds
  have hrankC := finrank_range_add_finrank_ker_int c
  have hsumSurj : Function.Surjective c := fun z => by
    obtain ⟨x, hx⟩ := coordinateSum_surjective (V := V) z.down
    exact ⟨x, ULift.down_injective hx⟩
  have hsumRange : LinearMap.range c = ⊤ := LinearMap.range_eq_top.mpr hsumSurj
  have hsumRank : Module.finrank ℤ (LinearMap.ker c) + 1 =
      Fintype.card V := by
    rw [hsumRange] at hrankC
    simpa [hdimV, finrank_ulift, Module.finrank_self, add_comm] using hrankC
  have hcompLe : LinearMap.range (ds.comp d) ≤ LinearMap.range ds := by
    rintro _ ⟨x, rfl⟩
    exact ⟨d x, rfl⟩
  have hdsLe : LinearMap.range ds ≤ LinearMap.ker c := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr
      (ULift.down_injective (coordinateSum_weightedAdjoint_eq_zero src tgt w x))
  let : Module.Finite ℤ (LinearMap.range ds) := Module.Finite.range ds
  let : Module.Finite ℤ (LinearMap.ker c) :=
    Module.Finite.of_fg (Submodule.FG.of_le
      (Module.finite_def.mp inferInstance) le_top)
  have hlow := Submodule.finrank_mono hcompLe
  have hupp := Submodule.finrank_mono hdsLe
  rw [hkerComp] at hrankComp
  omega

private lemma range_incidenceMap_orthogonal_eq_ker_weightedAdjoint
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ) :
    (LinearMap.range (incidenceMap src tgt)).orthogonalBilin
      (weightedDotForm w) = LinearMap.ker (weightedAdjoint src tgt w) := by
  apply le_antisymm
  · intro y hy
    apply LinearMap.mem_ker.mpr
    by_contra hne
    have hzero : dotForm (weightedAdjoint src tgt w y)
        (weightedAdjoint src tgt w y) = 0 := by
      rw [incidence_weighted_adjoint]
      have horth := (Submodule.mem_orthogonalBilin.mp hy)
        (incidenceMap src tgt (weightedAdjoint src tgt w y))
        ⟨weightedAdjoint src tgt w y, rfl⟩
      simpa only [(weightedDotForm_isSymm w).eq] using horth
    exact (ne_of_gt (dotForm_pos _ hne)) hzero
  · intro y hy
    refine Submodule.mem_orthogonalBilin.mpr ?_
    rintro _ ⟨x, rfl⟩
    calc
      weightedDotForm w (incidenceMap src tgt x) y =
          weightedDotForm w y (incidenceMap src tgt x) :=
        (weightedDotForm_isSymm w).eq _ _
      _ = dotForm (weightedAdjoint src tgt w y) x :=
        (incidence_weighted_adjoint src tgt w y x).symm
      _ = 0 := by rw [LinearMap.mem_ker.mp hy]; simp

/-- The map on `ℓ`-torsion induced by a linear map of `ℤ`-modules. -/
private noncomputable def torsionByMap {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (ℓ : ℕ) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy M (ℓ : ℤ) →ₗ[ZMod ℓ] AddSubgroup.torsionBy N (ℓ : ℤ) :=
  letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  AddMonoidHom.toZModLinearMap ℓ
    { toFun := fun x => ⟨f x.1, by
        have hx := x.property
        change (ℓ : ℤ) • (x : M) = 0 at hx
        change (ℓ : ℤ) • f x.1 = 0
        simpa only [map_zsmul, map_zero] using congrArg f hx⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; exact f.map_add x.1 y.1 }

private lemma finrank_torsionBy_eq_of_coker_torsionFree
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (hf : Function.Injective f) {ℓ : ℕ}
    (hQ : ∀ x : N ⧸ LinearMap.range f,
      (ℓ : ℤ) • x = 0 → x = 0) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) =
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := by
  classical
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let gz := torsionByMap f ℓ
  have hgz : Function.Injective gz := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  have hsurj : Function.Surjective gz := by
    intro y
    have hkill : (ℓ : ℤ) • (y : N) = 0 := y.property
    have hqzero := hQ ((LinearMap.range f).mkQ (y : N)) (by rw [← map_zsmul, hkill, map_zero])
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hqzero
    obtain ⟨x, hx⟩ := hqzero
    have hxtors : (ℓ : ℤ) • x = 0 := hf (by rw [map_zsmul, hx, hkill, map_zero])
    exact ⟨⟨x, hxtors⟩, Subtype.ext hx⟩
  exact (LinearEquiv.ofBijective gz ⟨hgz, hsurj⟩).finrank_eq

private lemma finrank_torsionBy_le_of_injective
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [Finite N]
    (f : M →ₗ[ℤ] N) (hf : Function.Injective f) {ℓ : ℕ}
    [Fact ℓ.Prime] :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) ≤
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := by
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let gz := torsionByMap f ℓ
  exact LinearMap.finrank_le_finrank_of_injective
    (show Function.Injective gz from fun x y h => Subtype.ext (hf (congrArg Subtype.val h)))

private lemma finrank_torsionBy_eq_of_linearEquiv
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) {ℓ : ℕ} :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := by
  refine finrank_torsionBy_eq_of_coker_torsionFree e.toLinearMap e.injective fun x _ => ?_
  obtain ⟨y, rfl⟩ := (LinearMap.range e.toLinearMap).mkQ_surjective x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨e.symm y, by simp⟩

private lemma finrank_torsionBy_eq_of_addGroupTorsionEquiv
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {ℓ : ℕ} [Fact ℓ.Prime]
    (e : AddCommGroup.torsion M ≃ₗ[ℤ] N) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := by
  classical
  let TM := AddSubgroup.torsionBy M (ℓ : ℤ)
  let TN := AddSubgroup.torsionBy N (ℓ : ℤ)
  let : Module (ZMod ℓ) TM := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) TN := AddSubgroup.torsionBy.zmodModule
  have hfull (x : TM) : (x : M) ∈ AddCommGroup.torsion M := by
    show IsOfFinAddOrder (x : M)
    rw [isOfFinAddOrder_iff_zsmul_eq_zero]
    exact ⟨(ℓ : ℤ), Int.natCast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero, x.property⟩
  let g : TM →+ TN :=
    { toFun := fun x => ⟨e ⟨x.1, hfull x⟩, by
        have hxNat : ℓ • x.1 = 0 :=
          (AddSubgroup.torsionBy.nsmul_iff (n := ℓ) (x := x.1)).mp x.property
        have hx : ℓ • (⟨x.1, hfull x⟩ : AddCommGroup.torsion M) = 0 := Subtype.ext hxNat
        have heNat : ℓ • e ⟨x.1, hfull x⟩ = 0 := by rw [← map_nsmul, hx, map_zero]
        exact (AddSubgroup.torsionBy.nsmul_iff (n := ℓ)
          (x := e ⟨x.1, hfull x⟩)).mpr heNat⟩
      map_zero' := by ext; simp
      map_add' := by
        intro x y
        apply Subtype.ext
        show e ((⟨x.1, hfull x⟩ : AddCommGroup.torsion M) +
          ⟨y.1, hfull y⟩) = e ⟨x.1, hfull x⟩ + e ⟨y.1, hfull y⟩
        rw [map_add] }
  let gz : TM →ₗ[ZMod ℓ] TN := g.toZModLinearMap ℓ
  have hinj : Function.Injective gz := by
    intro x y h
    have hval : e ⟨x.1, hfull x⟩ = e ⟨y.1, hfull y⟩ := congrArg Subtype.val h
    exact Subtype.ext (congrArg (fun z : AddCommGroup.torsion M => (z : M)) (e.injective hval))
  have hsurj : Function.Surjective gz := by
    intro y
    let z : AddCommGroup.torsion M := e.symm y.1
    have hyNat : ℓ • y.1 = 0 :=
      (AddSubgroup.torsionBy.nsmul_iff (n := ℓ) (x := y.1)).mp y.property
    have hz : ℓ • z = 0 :=
      e.injective (by rw [map_nsmul, e.apply_symm_apply, hyNat, map_zero])
    have hzNat : ℓ • (z : M) = 0 := congrArg Subtype.val hz
    have hzmem : (z : M) ∈ TM := by
      simpa only [TM] using
        (AddSubgroup.torsionBy.nsmul_iff (n := ℓ) (x := (z : M))).mpr hzNat
    refine ⟨⟨z, hzmem⟩, ?_⟩
    apply Subtype.ext
    show e ⟨z, hfull ⟨z, hzmem⟩⟩ = y.1
    simp [z]
  exact (LinearEquiv.ofBijective gz ⟨hinj, hsurj⟩).finrank_eq

private lemma finrank_torsionBy_eq_of_surjective_of_kernel_annihilated
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {ℓ : ℕ}
    (c : ℤ) (hker : ∀ x ∈ LinearMap.ker f, c • x = 0)
    (a b : ℤ) (hab : a * (ℓ : ℤ) + b * c = 1) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := by
  classical
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy M (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy N (ℓ : ℤ)) := AddSubgroup.torsionBy.zmodModule
  let gz := torsionByMap f ℓ
  have hgz : Function.Injective gz := by
    intro x y h
    apply Subtype.ext
    have hval : f x.1 = f y.1 := congrArg Subtype.val h
    have hℓxy : (ℓ : ℤ) • (x.1 - y.1) = 0 := by
      have hx := x.property
      have hy := y.property
      change (ℓ : ℤ) • x.1 = 0 at hx
      change (ℓ : ℤ) • y.1 = 0 at hy
      rw [zsmul_sub, hx, hy, sub_self]
    have hcxy := hker (x.1 - y.1) (LinearMap.mem_ker.mpr (by rw [map_sub, hval, sub_self]))
    have hone : (1 : ℤ) • (x.1 - y.1) = 0 := by
      rw [← hab, add_zsmul, mul_zsmul, mul_zsmul, hℓxy, hcxy]
      simp only [zsmul_zero, zero_add]
    simpa [sub_eq_zero] using hone
  have hsurj : Function.Surjective gz := by
    intro y
    obtain ⟨x, hx⟩ := hf y.1
    let u : M := (ℓ : ℤ) • x
    have hu : u ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_zsmul, hx]
      exact y.property
    have hcu : c • u = 0 := hker u hu
    have hℓk : (ℓ : ℤ) • (a • u) = u := by
      calc
        (ℓ : ℤ) • (a • u) = ((ℓ : ℤ) * a) • u := by rw [mul_zsmul]
        _ = (a * (ℓ : ℤ)) • u := by rw [mul_comm]
        _ = (1 - b * c) • u := by rw [show a * (ℓ : ℤ) = 1 - b * c by omega]
        _ = (1 : ℤ) • u - (b * c) • u := by
          rw [sub_zsmul]
          abel
        _ = u := by
          rw [mul_zsmul, hcu]
          simp only [zsmul_zero, sub_zero, one_zsmul]
    let x' : M := x - a • u
    have hx' : f x' = y.1 := by
      show f (x - a • u) = y.1
      rw [map_sub, map_zsmul, LinearMap.mem_ker.mp hu, zsmul_zero, sub_zero, hx]
    have hkill : (ℓ : ℤ) • x' = 0 := by
      dsimp [x']
      rw [zsmul_sub, hℓk]
      simp [u]
    exact ⟨⟨x', hkill⟩, Subtype.ext hx'⟩
  exact (LinearEquiv.ofBijective gz ⟨hgz, hsurj⟩).finrank_eq

private lemma finrank_torsionBy_le_finrank_of_surjective
    {G H : Type*} [AddCommGroup G] [Finite G]
    [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H]
    (q : H →ₗ[ℤ] G) (hq : Function.Surjective q) {ℓ : ℕ}
    [Fact ℓ.Prime] :
    let T := AddSubgroup.torsionBy G (ℓ : ℤ)
    letI : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) T ≤ Module.finrank ℤ H := by
  classical
  let T := AddSubgroup.torsionBy G (ℓ : ℤ)
  let U := ModN G ℓ
  let : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  let : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
  let : Fintype G := Fintype.ofFinite G
  let : Fintype T := Fintype.ofFinite T
  let : Fintype U := Fintype.ofFinite U
  have hcardT : Nat.card T = Nat.card U := by
    let f : G →ₗ[ℤ] G := LinearMap.lsmul ℤ G ℓ
    let K : Submodule ℤ G := f.ker
    let R : Submodule ℤ G := f.range
    have hK : T = K.toAddSubgroup := by
      ext x
      simp [T, K, AddSubgroup.torsionBy, f, Submodule.mem_torsionBy_iff,
        LinearMap.mem_ker, Nat.cast_smul_eq_nsmul]
    have hQR : Nat.card (G ⧸ K) = Nat.card R := Nat.card_congr f.quotKerEquivRange.toEquiv
    have hG₁ : Nat.card G = Nat.card K * Nat.card (G ⧸ K) :=
      Submodule.card_eq_card_quotient_mul_card K
    have hG₂ : Nat.card G = Nat.card R * Nat.card (G ⧸ R) :=
      Submodule.card_eq_card_quotient_mul_card R
    have hKR : Nat.card K = Nat.card (G ⧸ R) :=
      Nat.mul_left_cancel Nat.card_pos (by rw [← hG₂, hG₁, hQR, Nat.mul_comm])
    calc
      Nat.card T = Nat.card K :=
        Nat.card_congr (Set.equivOfEq (congrArg (fun S : AddSubgroup G => (S : Set G)) hK))
      _ = Nat.card (G ⧸ R) := hKR
      _ = Nat.card U := rfl
  let UH := ModN H ℓ
  let NH : Submodule ℤ H := LinearMap.range (LinearMap.lsmul ℤ H ℓ)
  let NG : Submodule ℤ G := LinearMap.range (LinearMap.lsmul ℤ G ℓ)
  let qlin : H →ₗ[ℤ] U := NG.mkQ.comp q
  have hker : NH ≤ LinearMap.ker qlin := by
    rintro _ ⟨x, rfl⟩
    show qlin ((LinearMap.lsmul ℤ H ℓ) x) = 0
    show NG.mkQ (q ((ℓ : ℤ) • x)) = 0
    rw [map_smul]
    show (Submodule.Quotient.mk (p := NG) ((ℓ : ℤ) • q x) : G ⧸ NG) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨q x, by simp [LinearMap.lsmul_apply]⟩
  let qbarInt : UH →ₗ[ℤ] U := NH.liftQ qlin hker
  let qbar : UH →ₗ[ZMod ℓ] U := qbarInt.toAddMonoidHom.toZModLinearMap ℓ
  have hqbar : Function.Surjective qbar := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      obtain ⟨y, rfl⟩ := hq x
      refine ⟨ModN.mkQ ℓ y, ?_⟩
      show qbarInt (Submodule.Quotient.mk (p := NH) y) =
        Submodule.Quotient.mk (p := NG) (q y)
      rw [Submodule.liftQ_apply]
      rfl
  have hdim : Module.finrank (ZMod ℓ) T = Module.finrank (ZMod ℓ) U := by
    have hp : (Fintype.card (ZMod ℓ)) ^ Module.finrank (ZMod ℓ) T =
        (Fintype.card (ZMod ℓ)) ^ Module.finrank (ZMod ℓ) U := by
      rw [← Module.card_eq_pow_finrank, ← Module.card_eq_pow_finrank,
        ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardT]
    exact Nat.pow_right_injective (by simpa [ZMod.card] using (Fact.out : Nat.Prime ℓ).two_le) hp
  have hquot : Module.finrank (ZMod ℓ) U ≤ Module.finrank ℤ H := by
    let b := Module.Free.chooseBasis ℤ H
    calc
      Module.finrank (ZMod ℓ) U ≤ Module.finrank (ZMod ℓ) UH :=
        LinearMap.finrank_le_finrank_of_surjective hqbar
      _ = Fintype.card (Module.Free.ChooseBasisIndex ℤ H) :=
        Module.finrank_eq_card_basis (ModN.basis b)
      _ = Module.finrank ℤ H := (Module.finrank_eq_card_basis b).symm
  simpa only [T] using hdim.le.trans hquot

private lemma finite_discriminantGroup_of_positive
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (form : LinearMap.BilinForm ℤ M)
    (hpos : ∀ x : M, x ≠ 0 → 0 < form x x) :
    Finite (DiscriminantGroup form) := by
  classical
  let : Module.Finite ℤ (Module.Dual ℤ M) :=
    (Module.finite_dual_iff ℤ).mpr inferInstance
  have hinj : Function.Injective form := fun x y hxy => by
    by_contra hne
    exact (hpos (x - y) (sub_ne_zero.mpr hne)).ne' (by simp [hxy])
  let b := Module.Free.chooseBasis ℤ M
  have hrange : Module.finrank ℤ (LinearMap.range form) =
      Module.finrank ℤ (Module.Dual ℤ M) := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_eq_card_basis b.dualBasis,
      Module.finrank_eq_card_basis b]
  exact Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range form) hrange

private lemma finrank_torsionBy_discriminantGroup_le
    {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (form : LinearMap.BilinForm ℤ M)
    (hpos : ∀ x : M, x ≠ 0 → 0 < form x x)
    {ℓ : ℕ} [Fact ℓ.Prime] :
    let T := AddSubgroup.torsionBy (DiscriminantGroup form) (ℓ : ℤ)
    letI : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) T ≤ Module.finrank ℤ M := by
  classical
  let : Module.Finite ℤ (Module.Dual ℤ M) :=
    (Module.finite_dual_iff ℤ).mpr inferInstance
  let : Finite (DiscriminantGroup form) :=
    finite_discriminantGroup_of_positive form hpos
  let T := AddSubgroup.torsionBy (DiscriminantGroup form) (ℓ : ℤ)
  let : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
  let b := Module.Free.chooseBasis ℤ M
  calc
    Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy (DiscriminantGroup form) (ℓ : ℤ)) ≤
        Module.finrank ℤ (Module.Dual ℤ M) :=
      finrank_torsionBy_le_finrank_of_surjective
        (LinearMap.range form).mkQ (LinearMap.range form).mkQ_surjective (ℓ := ℓ)
    _ = Fintype.card (Module.Free.ChooseBasisIndex ℤ M) :=
      Module.finrank_eq_card_basis b.dualBasis
    _ = Module.finrank ℤ M := (Module.finrank_eq_card_basis b).symm

private def integerDiagonalLin {E : Type*} (w : E → ℤ) :
    (E → ℤ) →ₗ[ℤ] (E → ℤ) where
  toFun y e := w e * y e
  map_add' x y := by ext e; simp [mul_add]
  map_smul' a x := by
    ext e
    change w e * (a * x e) = a * (w e * x e)
    ring

private lemma diagonalCoker_no_ell_torsion
    {E : Type*} [Fintype E] (w : E → ℤ) {ℓ : ℕ}
    (hw : ∀ e, IsCoprime (ℓ : ℤ) (w e)) :
    ∀ x : (E → ℤ) ⧸ LinearMap.range (integerDiagonalLin w),
      (ℓ : ℤ) • x = 0 → x = 0 := by
  classical
  let d := integerDiagonalLin w
  intro x hx
  obtain ⟨y, rfl⟩ := (LinearMap.range d).mkQ_surjective x
  have hmem : (ℓ : ℤ) • y ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa only [map_zsmul, hx]
  obtain ⟨z, hz⟩ := hmem
  have hdiv (e : E) : w e ∣ y e :=
    (hw e).symm.dvd_of_dvd_mul_left
      ⟨z e, by simpa [d, integerDiagonalLin, mul_comm] using (congrFun hz e).symm⟩
  choose q hq using hdiv
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨q, funext fun e => (hq e).symm⟩

private lemma diagonalCoker_annihilated_product
    {E : Type*} [Fintype E] (w : E → ℤ) (hw : ∀ e, w e ≠ 0) :
    ∀ x : (E → ℤ) ⧸ LinearMap.range (integerDiagonalLin w),
      (∏ e, w e) • x = 0 := by
  classical
  let d := integerDiagonalLin w
  intro x
  obtain ⟨y, rfl⟩ := (LinearMap.range d).mkQ_surjective x
  let q : E → ℤ := fun e => (∏ j, w j) / w e * y e
  have hy : d q = (∏ e, w e) • y := by
    ext e
    show w e * ((∏ j, w j) / w e * y e) = (∏ j, w j) * y e
    rw [← mul_assoc, Int.mul_ediv_cancel' (Finset.dvd_prod_of_mem w (Finset.mem_univ e))]
  show (Submodule.Quotient.mk (p := LinearMap.range d)
      ((∏ e, w e) • y) : (E → ℤ) ⧸ LinearMap.range d) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨q, hy⟩

private noncomputable def weightedDiscriminantEquivDiagonal
    {E : Type*} [Fintype E] [DecidableEq E] (w : E → ℤ) :
    ((E → ℤ) ⧸ LinearMap.range (integerDiagonalLin w)) ≃ₗ[ℤ]
      DiscriminantGroup (weightedDotForm w) := by
  let e : (E → ℤ) ≃ₗ[ℤ] Module.Dual ℤ (E → ℤ) :=
    LinearEquiv.ofBijective dotForm dotForm_bijective
  have hform : weightedDotForm w = e.toLinearMap.comp (integerDiagonalLin w) := by
    ext x y
    simp [weightedDotForm_apply, dotForm_apply, e, integerDiagonalLin]
  have hrange : (LinearMap.range (integerDiagonalLin w)).map e.toLinearMap =
      LinearMap.range (weightedDotForm w) := by
    rw [hform, LinearMap.range_comp]
  exact Submodule.Quotient.equiv (LinearMap.range (integerDiagonalLin w))
    (LinearMap.range (weightedDotForm w)) e hrange

private lemma weightedDiscriminant_annihilated_product
    {E : Type*} [Fintype E] [DecidableEq E] (w : E → ℤ)
    (hw : ∀ e, w e ≠ 0) :
    ∀ x : DiscriminantGroup (weightedDotForm w),
      (∏ e, w e) • x = 0 := by
  intro x
  let e := weightedDiscriminantEquivDiagonal w
  rw [← e.apply_symm_apply x, ← map_zsmul, diagonalCoker_annihilated_product w hw, map_zero]

private lemma eq_zero_of_zsmul_eq_zero_of_bezout
    {M : Type*} [AddCommGroup M] [Module ℤ M] (x : M)
    {r s a b : ℤ} (hr : r • x = 0) (hs : s • x = 0)
    (hab : a * r + b * s = 1) : x = 0 := by
  rw [← one_zsmul x, ← hab, add_zsmul, mul_zsmul, mul_zsmul, hr, hs]
  simp only [zsmul_zero, zero_add]

private lemma no_ell_torsion_of_surjective_of_annihilated
    {G H : Type*} [AddCommGroup G] [Module ℤ G]
    [AddCommGroup H] [Module ℤ H]
    (q : G →ₗ[ℤ] H) (hq : Function.Surjective q) {ℓ : ℕ}
    (c : ℤ) (hkill : ∀ x : G, c • x = 0)
    (a b : ℤ) (hab : a * (ℓ : ℤ) + b * c = 1) :
    ∀ x : H, (ℓ : ℤ) • x = 0 → x = 0 := by
  intro x hx
  obtain ⟨y, rfl⟩ := hq x
  apply eq_zero_of_zsmul_eq_zero_of_bezout (q y) hx ?_ hab
  rw [← map_zsmul]
  simpa using congrArg q (hkill y)

private lemma finrank_torsionBy_scale_coker
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f g : M →ₗ[ℤ] M) (hg : Function.Injective g)
    {ℓ : ℕ} (c : ℤ) (hc : ∀ x : M, c • x ∈ LinearMap.range g)
    (a b : ℤ) (hab : a * (ℓ : ℤ) + b * c = 1) :
    let fg := f.comp g
    let gfg := g.comp fg
    let Cfg := M ⧸ LinearMap.range fg
    let Cf := M ⧸ LinearMap.range f
    let Cgfg := M ⧸ LinearMap.range gfg
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Cfg (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Cf (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy Cgfg (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy Cfg (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy Cf (ℓ : ℤ)) ∧
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy Cfg (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy Cgfg (ℓ : ℤ)) := by
  classical
  let fg := f.comp g
  let gfg := g.comp fg
  let Cfg := M ⧸ LinearMap.range fg
  let Cf := M ⧸ LinearMap.range f
  let Cgfg := M ⧸ LinearMap.range gfg
  let pfg := LinearMap.range fg
  let pf := LinearMap.range f
  let pgfg := LinearMap.range gfg
  let : Module ℤ Cfg := Submodule.Quotient.module pfg
  let : Module ℤ Cf := Submodule.Quotient.module pf
  let : Module ℤ Cgfg := Submodule.Quotient.module pgfg
  have hker₁ : pfg ≤ LinearMap.ker pf.mkQ := by
    rintro y ⟨x, rfl⟩
    show (Submodule.Quotient.mk (p := pf) (f (g x)) : M ⧸ pf) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨g x, rfl⟩
  let q₁ : Cfg →ₗ[ℤ] Cf := pfg.liftQ pf.mkQ hker₁
  have hsurj₁ : Function.Surjective q₁ := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      refine ⟨pfg.mkQ x, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.mkQ_apply]
  have hkerKilled₁ : ∀ x ∈ LinearMap.ker q₁, c • x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := pfg.mkQ_surjective x
    have hy := LinearMap.mem_ker.mp hx
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨t, ht⟩ := hc z
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨t, show f (g t) = c • f z by rw [ht, map_zsmul]⟩
  have hEq₁ := finrank_torsionBy_eq_of_surjective_of_kernel_annihilated
    q₁ hsurj₁ c hkerKilled₁ a b hab
  have hker₂ : pfg ≤ LinearMap.ker (pgfg.mkQ.comp g) := by
    rintro y ⟨x, rfl⟩
    show (Submodule.Quotient.mk (p := pgfg) (g (f (g x))) : M ⧸ pgfg) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  let q₂ : Cfg →ₗ[ℤ] Cgfg := pfg.liftQ (pgfg.mkQ.comp g) hker₂
  have hinj₂ : Function.Injective q₂ := by
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        have hxy' : pgfg.mkQ (g x) = pgfg.mkQ (g y) := by
          change ((pfg.liftQ (pgfg.mkQ.comp g) hker₂).comp pfg.mkQ) x =
            ((pfg.liftQ (pgfg.mkQ.comp g) hker₂).comp pfg.mkQ) y at hxy
          rw [Submodule.liftQ_mkQ] at hxy
          simpa only [LinearMap.comp_apply] using hxy
        have hm' : g x - g y ∈ pgfg := (Submodule.Quotient.eq pgfg).1 hxy'
        have hm : g (x - y) ∈ pgfg := by simpa only [map_sub] using hm'
        obtain ⟨u, hu⟩ := hm
        have hxu : fg u = x - y := hg (by simpa [gfg] using hu)
        apply (Submodule.Quotient.eq pfg).2
        exact ⟨u, hxu⟩
  have hQ : ∀ x : Cgfg ⧸ LinearMap.range q₂,
      (ℓ : ℤ) • x = 0 → x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := (LinearMap.range q₂).mkQ_surjective x
    have hcKill : c • (LinearMap.range q₂).mkQ y = 0 := by
      obtain ⟨v, rfl⟩ := pgfg.mkQ_surjective y
      obtain ⟨z, hz⟩ := hc v
      rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨pfg.mkQ z, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
      show pgfg.mkQ (g z) = c • pgfg.mkQ v
      rw [hz, map_zsmul]
    exact eq_zero_of_zsmul_eq_zero_of_bezout
      ((LinearMap.range q₂).mkQ y) hx hcKill hab
  have hEq₂ := finrank_torsionBy_eq_of_coker_torsionFree q₂ hinj₂ hQ
  exact ⟨by simpa only [Cfg, Cf] using hEq₁, by simpa only [Cfg, Cgfg] using hEq₂⟩

private lemma finrank_torsionBy_eq_of_diagonal_conjugation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (m : ι → ℤ)
    (hm : ∀ i, m i ≠ 0) {ℓ : ℕ}
    (hℓm : ∀ i, IsCoprime (ℓ : ℤ) (m i)) :
    let D := Matrix.diagonal m
    let C := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
    let B := D * A * D
    let CB := (ι → ℤ) ⧸ LinearMap.range B.mulVecLin
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy CB (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) =
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy CB (ℓ : ℤ)) := by
  classical
  let c : ℤ := ∏ i, m i
  obtain ⟨a, b, hab⟩ : IsCoprime (ℓ : ℤ) c := IsCoprime.prod_right fun i _ => hℓm i
  let g : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := integerDiagonalLin m
  have hg : Function.Injective g := by
    intro x y hxy
    ext i
    have h := congrFun hxy i
    dsimp [g, integerDiagonalLin] at h
    exact mul_left_cancel₀ (hm i) h
  have hc : ∀ x : (ι → ℤ), c • x ∈ LinearMap.range g := by
    intro x
    refine ⟨fun i => (c / m i) * x i, ?_⟩
    ext i
    have hmul : m i * (c / m i) = c :=
      Int.mul_ediv_cancel' (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
    show m i * ((c / m i) * x i) = c * x i
    rw [← mul_assoc, hmul]
  have hscale := finrank_torsionBy_scale_coker A.mulVecLin g hg c hc a b hab
  let D := Matrix.diagonal m
  have hD : D.mulVecLin = g := by
    ext x i
    simp [D, g, integerDiagonalLin, Matrix.mulVec_diagonal]
  let B := D * A * D
  have hB : B.mulVecLin = g.comp (A.mulVecLin.comp g) := by
    dsimp [B]
    rw [Matrix.mul_assoc, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hD]
  let Cfg := (ι → ℤ) ⧸ LinearMap.range (A.mulVecLin.comp g)
  let Cf := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Cfg (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy Cf (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have hfirst := hscale.1
  have hsecond := hscale.2
  let C := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
  let CB := (ι → ℤ) ⧸ LinearMap.range B.mulVecLin
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy C (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy CB (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let CComp := (ι → ℤ) ⧸ LinearMap.range (g.comp (A.mulVecLin.comp g))
  let : Module (ZMod ℓ) (AddSubgroup.torsionBy CComp (ℓ : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  have hrange : LinearMap.range B.mulVecLin =
      LinearMap.range (g.comp (A.mulVecLin.comp g)) := by
    rw [hB]
  let e : ((ι → ℤ) ⧸ LinearMap.range B.mulVecLin) ≃ₗ[ℤ] CComp :=
    (LinearMap.range B.mulVecLin).quotEquivOfEq
      (LinearMap.range (g.comp (A.mulVecLin.comp g))) hrange
  have htransport := finrank_torsionBy_eq_of_linearEquiv (ℓ := ℓ) e
  have hsecond' :
      Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy Cfg (ℓ : ℤ)) =
        Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy CB (ℓ : ℤ)) :=
    hsecond.trans htransport.symm
  simpa [Cfg, CB, C, B, D] using hfirst.symm.trans hsecond'

private lemma finrank_torsionBy_incidenceCokernel_le
    {V E : Type u} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (w : E → ℤ)
    (hw : ∀ e, 0 < w e) (hV : Nonempty V)
    (hconn : ∀ I : Set V, I.Nonempty → I ≠ Set.univ →
      ∃ e, (src e ∈ I ∧ tgt e ∉ I) ∨ (tgt e ∈ I ∧ src e ∉ I))
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hcop : ∀ e, IsCoprime (ℓ : ℤ) (w e)) :
    let d := incidenceMap src tgt
    let ds := weightedAdjoint src tgt w
    let C := (V → ℤ) ⧸ LinearMap.range (ds.comp d)
    let T := AddSubgroup.torsionBy C (ℓ : ℤ)
    letI : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) T + Fintype.card V ≤
      1 + Fintype.card E := by
  classical
  let d := incidenceMap src tgt
  let ds := weightedAdjoint src tgt w
  let f₀ := dotForm (κ := V)
  let f₁ := weightedDotForm w
  let A := LinearMap.range d
  let H := A.orthogonalBilin f₁
  let : Module ℤ A := A.module
  let : Module ℤ H := H.module
  let : Module.Finite ℤ H :=
    Module.Finite.of_fg (Submodule.FG.of_le
      (Module.finite_def.mp inferInstance) le_top)
  let : Module.Free ℤ H := inferInstance
  have hpair : LinearMap.IsAdjointPair f₀ f₁ d ds := by
    intro x y
    calc
      f₁ (d x) y = f₁ y (d x) := (weightedDotForm_isSymm w).eq _ _
      _ = f₀ (ds y) x := (incidence_weighted_adjoint src tgt w y x).symm
      _ = f₀ x (ds y) := (dotForm_isSymm (κ := V)).eq _ _
  have hA : Module.IsTorsionFree ℤ ((E → ℤ) ⧸ A) :=
    incidence_range_quotient_torsionFree src tgt hV hconn
  obtain ⟨eT⟩ := torsionCokernelEquiv_discriminantGroup_range
    f₀ f₁ dotForm_isSymm (weightedDotForm_isSymm w)
    dotForm_pos (weightedDotForm_pos w hw) d ds hpair dotForm_bijective
  obtain ⟨iL, hiL, qL, hqL⟩ :=
    exists_injective_to_discriminantGroup_left
      f₁ (weightedDotForm_isSymm w) (weightedDotForm_pos w hw) A hA
  obtain ⟨iR, hiR, qR, hqR⟩ :=
    exists_injective_to_discriminantGroup_orthogonal
      f₁ (weightedDotForm_isSymm w) (weightedDotForm_pos w hw) A hA
  let c : ℤ := ∏ e, w e
  obtain ⟨a, b, hab⟩ : IsCoprime (ℓ : ℤ) c := IsCoprime.prod_right fun e _ => hcop e
  have hkill : ∀ x : DiscriminantGroup f₁, c • x = 0 :=
    weightedDiscriminant_annihilated_product w (fun e => ne_of_gt (hw e))
  have hQ : ∀ x : SubmoduleDiscriminantGroup f₁ A ⧸
      LinearMap.range iL, (ℓ : ℤ) • x = 0 → x = 0 :=
    no_ell_torsion_of_surjective_of_annihilated qL hqL c hkill a b hab
  have hEqL := finrank_torsionBy_eq_of_coker_torsionFree iL hiL hQ
  have hposH : ∀ x : H, x ≠ 0 → 0 < (f₁.restrict H) x x := fun x hx =>
    weightedDotForm_pos w hw x.1 fun h => hx (Subtype.ext h)
  let : Finite (SubmoduleDiscriminantGroup f₁ H) :=
    finite_discriminantGroup_of_positive (f₁.restrict H) hposH
  have hLeR := finrank_torsionBy_le_of_injective iR hiR (ℓ := ℓ)
  have hDisc := finrank_torsionBy_discriminantGroup_le
    (f₁.restrict H) hposH (ℓ := ℓ)
  have hRank : Module.finrank ℤ H + Fintype.card V =
      1 + Fintype.card E := by
    have hHEq : H = LinearMap.ker ds :=
      range_incidenceMap_orthogonal_eq_ker_weightedAdjoint src tgt w
    let : Module ℤ (LinearMap.ker ds) := (LinearMap.ker ds).module
    let : Module.Finite ℤ (LinearMap.ker ds) :=
      Module.Finite.of_fg (Submodule.FG.of_le
        (Module.finite_def.mp inferInstance) le_top)
    have hfin : Module.finrank ℤ H =
        Module.finrank ℤ (LinearMap.ker ds) :=
      (Submodule.finrank_mono hHEq.le).antisymm (Submodule.finrank_mono hHEq.ge)
    rw [hfin]
    exact finrank_ker_weightedAdjoint src tgt w hw hV hconn
  have hT := finrank_torsionBy_eq_of_addGroupTorsionEquiv eT (ℓ := ℓ)
  let Q := OrthogonalSumQuotient f₁ A
  let TQ := AddSubgroup.torsionBy Q (ℓ : ℤ)
  let TA := AddSubgroup.torsionBy
    (SubmoduleDiscriminantGroup f₁ A) (ℓ : ℤ)
  let TH := AddSubgroup.torsionBy
    (SubmoduleDiscriminantGroup f₁ H) (ℓ : ℤ)
  let : Module (ZMod ℓ) TA := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) TQ := AddSubgroup.torsionBy.zmodModule
  let : Module (ZMod ℓ) TH := AddSubgroup.torsionBy.zmodModule
  let C := (V → ℤ) ⧸ LinearMap.range (ds.comp d)
  let T := AddSubgroup.torsionBy C (ℓ : ℤ)
  let : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
  calc
    Module.finrank (ZMod ℓ) T + Fintype.card V =
        Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy (SubmoduleDiscriminantGroup f₁ A)
            (ℓ : ℤ)) + Fintype.card V := by rw [hT]
    _ = Module.finrank (ZMod ℓ) TQ + Fintype.card V := by
      rw [hEqL]
    _ ≤ Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy (SubmoduleDiscriminantGroup f₁ H)
            (ℓ : ℤ)) + Fintype.card V := Nat.add_le_add_right hLeR _
    _ ≤ Module.finrank ℤ H + Fintype.card V :=
      Nat.add_le_add_right hDisc _
    _ = 1 + Fintype.card E := hRank

private lemma matrixSupport_connected
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hconnected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0) :
    let E := {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2}
    ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
      ∃ e : E, (e.1.1 ∈ I ∧ e.1.2 ∉ I) ∨
        (e.1.2 ∈ I ∧ e.1.1 ∉ I) := by
  classical
  intro E I hI hproper
  have hcross := hconnected I hI hproper
  push Not at hcross
  obtain ⟨i, hi, j, hj, hne⟩ := hcross
  have hij : i ≠ j := fun heq => hj (heq ▸ hi)
  have hpos : 0 < A i j := lt_of_le_of_ne (hoffDiag i j hij) (Ne.symm hne)
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact ⟨⟨(i, j), hlt, hpos⟩, Or.inl ⟨hi, hj⟩⟩
  · exact (hij heq).elim
  · have hpos' : 0 < A j i := by simpa only [hA.apply i j] using hpos
    exact ⟨⟨(j, i), hgt, hpos'⟩, Or.inr ⟨hi, hj⟩⟩

private lemma sum_matrixSupport
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (f : ι × ι → ℤ) :
    (∑ e : {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2}, f e.1) =
      ∑ p : ι × ι,
        if p.1 < p.2 ∧ 0 < A p.1 p.2 then f p else 0 := by
  classical
  let s : Finset (ι × ι) :=
    Finset.univ.filter fun p => p.1 < p.2 ∧ 0 < A p.1 p.2
  calc
    (∑ e : {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2}, f e.1) =
        ∑ p ∈ s, f p := by
      symm
      exact Finset.sum_subtype s (by intro p; simp [s]) f
    _ = _ := by simp [s, Finset.sum_filter]

private lemma sum_matrixSupport_source
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (x : ι → ℤ) (i : ι) :
    (∑ e : {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2},
      if e.1.1 = i then A e.1.1 e.1.2 * (x e.1.1 - x e.1.2) else 0) =
    ∑ j, if i < j ∧ 0 < A i j then A i j * (x i - x j) else 0 := by
  classical
  calc
    _ = ∑ p : ι × ι,
        if p.1 < p.2 ∧ 0 < A p.1 p.2 then
          (if p.1 = i then A p.1 p.2 * (x p.1 - x p.2) else 0)
        else 0 := sum_matrixSupport A _
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      calc
        (∑ a : ι, ∑ b : ι,
            if a < b ∧ 0 < A a b then
              (if a = i then A a b * (x a - x b) else 0) else 0) =
          ∑ a : ι, if a = i then
            (∑ b : ι, if a < b ∧ 0 < A a b then A a b * (x a - x b) else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hai : a = i <;> simp [hai]
        _ = _ := by simp

private lemma sum_matrixSupport_target
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (x : ι → ℤ) (i : ι) :
    (∑ e : {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2},
      if e.1.2 = i then A e.1.1 e.1.2 * (x e.1.1 - x e.1.2) else 0) =
    ∑ j, if j < i ∧ 0 < A j i then A j i * (x j - x i) else 0 := by
  classical
  calc
    _ = ∑ p : ι × ι,
        if p.1 < p.2 ∧ 0 < A p.1 p.2 then
          (if p.2 = i then A p.1 p.2 * (x p.1 - x p.2) else 0)
        else 0 := sum_matrixSupport A _
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      calc
        (∑ b : ι, ∑ a : ι,
            if a < b ∧ 0 < A a b then
              (if b = i then A a b * (x a - x b) else 0) else 0) =
          ∑ b : ι, if b = i then
            (∑ a : ι, if a < b ∧ 0 < A a b then A a b * (x a - x b) else 0)
            else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hbi : b = i <;> simp [hbi]
        _ = _ := by simp

private lemma weightedAdjoint_incidenceMap_eq_matrixRow
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j)
    (x : ι → ℤ) (i : ι) :
    let E := {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2}
    let src : E → ι := fun e => e.1.1
    let tgt : E → ι := fun e => e.1.2
    let w : E → ℤ := fun e => A e.1.1 e.1.2
    (weightedAdjoint src tgt w (incidenceMap src tgt x)) i =
      ∑ j, A i j * (x i - x j) := by
  classical
  intro E src tgt w
  calc
    (weightedAdjoint src tgt w (incidenceMap src tgt x)) i =
        (∑ e : E, if e.1.1 = i then
          A e.1.1 e.1.2 * (x e.1.1 - x e.1.2) else 0) -
        (∑ e : E, if e.1.2 = i then
          A e.1.1 e.1.2 * (x e.1.1 - x e.1.2) else 0) := by
      rw [weightedAdjoint_apply, ← Finset.sum_sub_distrib]
      rfl
    _ = (∑ j, if i < j ∧ 0 < A i j then
            A i j * (x i - x j) else 0) -
          (∑ j, if j < i ∧ 0 < A j i then
            A j i * (x j - x i) else 0) := by
      rw [sum_matrixSupport_source, sum_matrixSupport_target]
    _ = ∑ j, A i j * (x i - x j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rcases lt_trichotomy i j with hij | heq | hji
      · have hji' : ¬ j < i := not_lt.mpr (le_of_lt hij)
        by_cases hp : 0 < A i j
        · simp [hij, hji', hp]
        · have hz : A i j = 0 := by
            have hn := hoffDiag i j (ne_of_lt hij)
            omega
          simp [hij, hji', hz]
      · subst j
        simp
      · have hij' : ¬ i < j := not_lt.mpr (le_of_lt hji)
        have hsym : A j i = A i j := hA.apply i j
        by_cases hp : 0 < A i j
        · simp [hji, hij', hsym, hp]
          ring
        · have hz : A i j = 0 := by
            have hn := hoffDiag i j (ne_of_gt hji)
            omega
          simp [hji, hij', hsym, hz]

private lemma weightedAdjoint_comp_incidenceMap_eq_neg_matrix
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℤ) (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hrow : A *ᵥ (fun _ => 1) = 0) :
    let E := {p : ι × ι // p.1 < p.2 ∧ 0 < A p.1 p.2}
    let src : E → ι := fun e => e.1.1
    let tgt : E → ι := fun e => e.1.2
    let w : E → ℤ := fun e => A e.1.1 e.1.2
    (weightedAdjoint src tgt w).comp (incidenceMap src tgt) =
      -A.mulVecLin := by
  classical
  intro E src tgt w
  refine LinearMap.ext fun x => funext fun i => ?_
  have hsum : ∑ j, A i j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hrow i
  have hcalc : (∑ j, A i j * (x i - x j)) = -(A *ᵥ x) i := by
    calc
      (∑ j, A i j * (x i - x j)) =
          (∑ j, A i j) * x i - ∑ j, A i j * x j := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = -(A *ᵥ x) i := by
        simp [hsum, Matrix.mulVec, dotProduct]
  calc
    ((weightedAdjoint src tgt w).comp (incidenceMap src tgt)) x i =
        ∑ j, A i j * (x i - x j) :=
      weightedAdjoint_incidenceMap_eq_matrixRow A hA hoffDiag x i
    _ = -(A.mulVecLin x) i := by simpa only [Matrix.mulVecLin_apply] using hcalc
    _ = (-A.mulVecLin) x i := rfl

private lemma diagonal_conjugate_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (m : ι → ℤ) (i j : ι) :
    (Matrix.diagonal m * A * Matrix.diagonal m) i j =
      m i * A i j * m j := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

-- Preserve the `ZMod` semiring instance used when the accepted statement was
-- elaborated, before the additional proof imports supplied its field instance.
attribute [-instance] DivisionSemiring.toSemiring Semifield.toCommSemiring in
/-- The prime torsion in the cokernel of a connected recurring symmetric
integer matrix has dimension at most the cycle rank of its support graph. -/
@[stacks 0C6X]
lemma finrank_torsionBy_matrixCokernel_le_cycleRank
    {ι : Type*} [Fintype ι] [LinearOrder ι] {A : Matrix ι ι ℤ}
    {m : ι → ℤ} {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.IsSymm)
    (hoffDiag : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hm : ∀ i, 0 < m i)
    (hAm : A *ᵥ m = 0)
    (hconnected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
      ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0)
    (hℓA : ∀ i j, 0 < A i j → IsCoprime (ℓ : ℤ) (A i j))
    (hℓm : ∀ i, IsCoprime (ℓ : ℤ) (m i)) :
    let C := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
    let T := AddSubgroup.torsionBy C (ℓ : ℤ)
    letI : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    Module.finrank (ZMod ℓ) T + Fintype.card ι ≤
      1 + (Finset.univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < A p.1 p.2).card := by
  classical
  by_cases hV : Nonempty ι
  · let D := Matrix.diagonal m
    let B := D * A * D
    have hmne (i : ι) : m i ≠ 0 := ne_of_gt (hm i)
    have hBsymm : B.IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      simp only [B, D, diagonal_conjugate_apply]
      rw [hA.apply i j]; ring
    have hBoff : ∀ i j, i ≠ j → 0 ≤ B i j := by
      intro i j hij
      rw [show B i j = m i * A i j * m j from
        diagonal_conjugate_apply A m i j]
      exact mul_nonneg (mul_nonneg (le_of_lt (hm i)) (hoffDiag i j hij)) (le_of_lt (hm j))
    have hBpos (i j : ι) (hij : i ≠ j) :
        0 < B i j ↔ 0 < A i j := by
      rw [show B i j = m i * A i j * m j from
        diagonal_conjugate_apply A m i j]
      constructor
      · intro hp
        by_contra hnot
        have hz : A i j = 0 := by
          have hn := hoffDiag i j hij
          omega
        simp [hz] at hp
      · exact fun hp => mul_pos (mul_pos (hm i) hp) (hm j)
    have hD1 : D *ᵥ (fun _ => (1 : ℤ)) = m := by
      ext i; simp [D, Matrix.mulVec_diagonal]
    have hBrow : B *ᵥ (fun _ => (1 : ℤ)) = 0 := by
      have hh : B *ᵥ (fun _ => (1 : ℤ)) =
          D *ᵥ (A *ᵥ (D *ᵥ (fun _ => (1 : ℤ)))) := by
        simp [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hh, hD1, hAm]; simp
    have hBconn : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
        ¬ ∀ i ∈ I, ∀ j ∉ I, B i j = 0 := by
      intro I hI hproper hzero
      apply hconnected I hI hproper
      intro i hi j hj
      have hb := hzero i hi j hj
      rw [show B i j = m i * A i j * m j from
        diagonal_conjugate_apply A m i j] at hb
      by_contra ha
      exact (mul_ne_zero (mul_ne_zero (hmne i) ha) (hmne j)) hb
    let E := {p : ι × ι // p.1 < p.2 ∧ 0 < B p.1 p.2}
    let src : E → ι := fun e => e.1.1
    let tgt : E → ι := fun e => e.1.2
    let w : E → ℤ := fun e => B e.1.1 e.1.2
    have hw (e : E) : 0 < w e := e.property.2
    have hcop (e : E) : IsCoprime (ℓ : ℤ) (w e) := by
      have ha : 0 < A e.1.1 e.1.2 :=
        (hBpos _ _ (ne_of_lt e.property.1)).mp e.property.2
      simpa only [w, B, D, diagonal_conjugate_apply] using
        ((hℓm e.1.1).mul_right (hℓA _ _ ha)).mul_right (hℓm e.1.2)
    have hconn : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ →
        ∃ e : E, (src e ∈ I ∧ tgt e ∉ I) ∨
          (tgt e ∈ I ∧ src e ∉ I) :=
      matrixSupport_connected B hBsymm hBoff hBconn
    have hmatrix : (weightedAdjoint src tgt w).comp
        (incidenceMap src tgt) = -B.mulVecLin :=
      weightedAdjoint_comp_incidenceMap_eq_neg_matrix B hBsymm hBoff hBrow
    have hrange : LinearMap.range ((weightedAdjoint src tgt w).comp
        (incidenceMap src tgt)) = LinearMap.range B.mulVecLin := by
      rw [hmatrix, LinearMap.range_neg]
    have hbound := finrank_torsionBy_incidenceCokernel_le
      src tgt w hw hV hconn hcop
    have hscale := finrank_torsionBy_eq_of_diagonal_conjugation
      A m hmne hℓm
    have hfilter :
        (Finset.univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < B p.1 p.2) =
        (Finset.univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < A p.1 p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_congr_right fun hp => hBpos _ _ (ne_of_lt hp)
    have hcard : Fintype.card E =
        (Finset.univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < B p.1 p.2).card := by
      simp [E, Fintype.card_subtype]
    let C := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
    let CB := (ι → ℤ) ⧸ LinearMap.range B.mulVecLin
    let T := AddSubgroup.torsionBy C (ℓ : ℤ)
    let TB := AddSubgroup.torsionBy CB (ℓ : ℤ)
    let : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    let : Module (ZMod ℓ) TB := AddSubgroup.torsionBy.zmodModule
    calc
      Module.finrank (ZMod ℓ) T + Fintype.card ι =
          Module.finrank (ZMod ℓ) TB + Fintype.card ι := by rw [hscale]
      _ ≤ 1 + Fintype.card E := by
        let pds := LinearMap.range
          ((weightedAdjoint src tgt w).comp (incidenceMap src tgt))
        let Cds := (ι → ℤ) ⧸ pds
        let Tds := AddSubgroup.torsionBy Cds (ℓ : ℤ)
        let : Module (ZMod ℓ) Tds := AddSubgroup.torsionBy.zmodModule
        let eQ : Cds ≃ₗ[ℤ] CB :=
          pds.quotEquivOfEq (LinearMap.range B.mulVecLin) hrange
        rw [← finrank_torsionBy_eq_of_linearEquiv eQ (ℓ := ℓ)]
        exact hbound
      _ = 1 + (Finset.univ.filter
          fun p : ι × ι => p.1 < p.2 ∧ 0 < A p.1 p.2).card := by
        rw [hcard, hfilter]
  · have : IsEmpty ι := not_nonempty_iff.mp hV
    let C := (ι → ℤ) ⧸ LinearMap.range A.mulVecLin
    let T := AddSubgroup.torsionBy C (ℓ : ℤ)
    let : Module (ZMod ℓ) T := AddSubgroup.torsionBy.zmodModule
    have : Subsingleton (ι → ℤ) := inferInstance
    have : Subsingleton C := inferInstance
    have : Subsingleton T := inferInstance
    have hfin : Module.finrank (ZMod ℓ) T = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [C, T, hfin]

end Matrix
