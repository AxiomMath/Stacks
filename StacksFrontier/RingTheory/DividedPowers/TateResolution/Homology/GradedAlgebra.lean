module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-!
# Divided powers on the homology of a differential graded algebra

Let `B` be a strictly graded-commutative nonnegatively graded algebra with a differential `d`
that lowers degrees by one, and let divided powers on its positive even part be compatible with
`d`. The homology `ker d / im d` is again a graded algebra, and the files of this directory
transport the divided powers to it: the operations are defined on a class by applying `γₙ` to a
homogeneous cycle representative, which is well defined because two representatives of the same
class differ by a boundary and `γₙ` of a boundary differs from `γₙ` of the other representative
by a boundary again.

Independence of the representative is the only delicate point, and it is where the hypothesis
enters that the structure comes from a surjective morphism `f : A → B` of divided-power
differential graded algebras whose source has vanishing homology in positive degrees. Given two
homogeneous cycles `x`, `y` of the same positive even degree with `y - x` a boundary, one lifts
`x` and a preimage of `y - x` along `f` and expands `γₙ y` by the convolution formula; every term
but `γₙ x` carries a positive divided power of a boundary, which is itself a boundary.

This file defines the differential graded algebra predicate, cycles, boundaries and homology,
and constructs the ring, algebra and grading on cycles and on homology. The independence of the
representative is in `StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.Representative`
and the divided power structure on homology in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.DividedPowerStructure`.

## Main definitions

* `DividedPowers.TateResolution.IsDifferentialGradedAlgebra` records the differential axioms for
  the concrete nonnegative grading used by the divided-power results of this directory.
* `DividedPowers.TateResolution.cycles`, `DividedPowers.TateResolution.boundaries` and
  `DividedPowers.TateResolution.Homology` are the kernel of the differential, the image of the
  differential inside it, and their quotient.

## Main results

* `DividedPowers.TateResolution.dividedPowerStructureOnHomology_of_surjective` (in
  `StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.DividedPowerStructure`) equips the
  homology quotient with its graded algebra and divided power structures, and records that the
  quotient map is a morphism of all the structures involved.

## Implementation notes

Homology is formed as a quotient of the kernel of the differential by its image. The conclusion
constructs the ring, algebra, graded ring and divided power structures on that quotient. The
equations for zero, addition, and scalar multiplication require the constructed structures to
extend the quotient's canonical module structure, so they are part of the statement. The
concrete differential graded algebra predicate supplies the axioms that the compatibility
predicate of Tag 09PJ deliberately omits.

## References

* [Stacks Project, Tag 09PK](https://stacks.math.columbia.edu/tag/09PK)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w t

/-- The differential axioms on a nonnegatively graded algebra.  The differential lowers degree
by one, is square-zero, and satisfies the signed Leibniz rule on homogeneous elements. -/
public class IsDifferentialGradedAlgebra {R : Type u} {A : Type v} [CommRing R] [Ring A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) : Prop where
  /-- The differential vanishes in degree zero. -/
  d_grade_zero : ∀ {x : A}, x ∈ 𝒜 0 → d x = 0
  /-- The differential lowers every positive degree by one. -/
  d_mem : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 (n + 1) → d x ∈ 𝒜 n
  /-- Applying the differential twice gives zero. -/
  d_sq_zero : ∀ x : A, d (d x) = 0
  /-- The differential satisfies the signed Leibniz rule on homogeneous elements. -/
  leibniz : ∀ {i j : ℕ} {x y : A}, x ∈ 𝒜 i → y ∈ 𝒜 j →
    d (x * y) = d x * y + (-1 : R) ^ i • (x * d y)

/-- Cycles in a differential graded algebra. -/
public abbrev cycles {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (d : A →ₗ[R] A) : Submodule R A := LinearMap.ker d

/-- The differential, regarded as a map into cycles. -/
public def boundaryMap {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d] : A →ₗ[R] cycles d :=
  d.codRestrict (cycles d) (fun x =>
    IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := d) x)

/-- Boundaries, as a submodule of cycles. -/
public abbrev boundaries {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d] : Submodule R (cycles d) :=
  LinearMap.range (boundaryMap (𝒜 := 𝒜) d)

/-- Homology of a differential graded algebra, as a quotient module. -/
public abbrev Homology {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
    [IsDifferentialGradedAlgebra 𝒜 d] :=
  (cycles d) ⧸ (boundaries (𝒜 := 𝒜) d)

/-- The differential commutes with taking homogeneous components, up to a shift of degree. -/
private theorem decompose_d_apply {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] (z : B) (n : ℕ) :
    (DirectSum.decompose 𝒜 (d z) n : B) = d (DirectSum.decompose 𝒜 z (n + 1) : B) := by
  classical
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun z => (DirectSum.decompose 𝒜 (d z) n : B) =
      d (DirectSum.decompose 𝒜 z (n + 1) : B)) (by simp) (fun {i} m => ?_)
    (fun a b ha hb => by simp [ha, hb]) z
  obtain ⟨m, hm⟩ := m
  obtain _ | k := i
  · simp [IsDifferentialGradedAlgebra.d_grade_zero hm, DirectSum.decompose_of_mem 𝒜 hm,
      DirectSum.of_apply]
  · by_cases h : k = n
    · subst h
      simp [DirectSum.decompose_of_mem_same 𝒜 hm,
        DirectSum.decompose_of_mem_same 𝒜 (IsDifferentialGradedAlgebra.d_mem hm)]
    · simp [DirectSum.decompose_of_mem_ne 𝒜 hm (j := n + 1) (by omega),
        DirectSum.decompose_of_mem_ne 𝒜 (IsDifferentialGradedAlgebra.d_mem hm) h]

private theorem differential_of_component_of_cycle {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x : B} (hx : d x = 0) (n : ℕ) :
    d ((DirectSum.decompose 𝒜 x n : 𝒜 n) : B) = 0 := by
  obtain _ | m := n
  · exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
      (DirectSum.decompose 𝒜 x 0).property
  · rw [← decompose_d_apply, hx]
    simp

private theorem differential_mul_right_cycle {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x y : B} (hy : d y = 0) : d (x * y) = d x * y := by
  classical
  let sx := (DirectSum.decompose 𝒜 x).support
  let sy := (DirectSum.decompose 𝒜 y).support
  have hxsum : (∑ i ∈ sx, ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) = x := by
    simpa [sx] using (DirectSum.sum_support_decompose 𝒜 x)
  have hysum : (∑ j ∈ sy, ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B)) = y := by
    simpa [sy] using (DirectSum.sum_support_decompose 𝒜 y)
  have hdy : ∀ j, d ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B) = 0 :=
    differential_of_component_of_cycle 𝒜 d hy
  have hdxsum : (∑ i ∈ sx, d ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) = d x := by
    calc
      (∑ i ∈ sx, d ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) =
          d (∑ i ∈ sx, ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) := by simp only [map_sum]
      _ = d x := congrArg d hxsum
  calc
    d (x * y) = d ((∑ i ∈ sx, ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) *
        (∑ j ∈ sy, ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B))) := by rw [hxsum, hysum]
    _ = ∑ i ∈ sx, ∑ j ∈ sy,
        d (((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) *
          ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B)) := by
      rw [Finset.sum_mul_sum]
      simp only [map_sum]
    _ = ∑ i ∈ sx, ∑ j ∈ sy,
        d ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) *
          ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have h := IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d)
          (DirectSum.decompose 𝒜 x i).property (DirectSum.decompose 𝒜 y j).property
      rw [hdy j] at h
      simpa using h
    _ = d x * y := by
      rw [← Finset.sum_mul_sum sx sy
        (fun i => d ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B))
        (fun j => ((DirectSum.decompose 𝒜 y j : 𝒜 j) : B)), hdxsum, hysum]


private theorem differential_mul_of_cycles {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x y : B} (hx : d x = 0) (hy : d y = 0) : d (x * y) = 0 := by
  rw [differential_mul_right_cycle 𝒜 d hy, hx, zero_mul]

private theorem boundary_mul_cycle_exists_preimage {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x y : B} (hx : ∃ z, d z = x) (hy : d y = 0) :
    ∃ z, d z = x * y := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y, differential_mul_right_cycle 𝒜 d hy⟩

private theorem cycle_mul_boundary_exists_preimage {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x y : B} (hx : d x = 0) (hy : ∃ z, d z = y) :
    ∃ w, d w = x * y := by
  classical
  obtain ⟨z, rfl⟩ := hy
  let sx := (DirectSum.decompose 𝒜 x).support
  let sz := (DirectSum.decompose 𝒜 z).support
  have hxsum : (∑ i ∈ sx, ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) = x := by
    simpa [sx] using (DirectSum.sum_support_decompose 𝒜 x)
  have hzsum : (∑ j ∈ sz, ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) = z := by
    simpa [sz] using (DirectSum.sum_support_decompose 𝒜 z)
  have hdxi (i : ℕ) : d ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) = 0 :=
    differential_of_component_of_cycle 𝒜 d hx i
  have hdzsum : d z = ∑ j ∈ sz, d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) := by
    calc
      d z = d (∑ j ∈ sz, ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) := congrArg d hzsum.symm
      _ = _ := by simp only [map_sum]
  let w : B := ∑ i ∈ sx, ∑ j ∈ sz,
    if j = 0 then 0 else
      (-1 : R) ^ (i * (j - 1)) •
        (((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) *
          ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B))
  refine ⟨w, ?_⟩
  have hmulExpand : x * d z = ∑ i ∈ sx, ∑ j ∈ sz,
      ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) *
        d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) := by
    calc
      x * d z = (∑ i ∈ sx, ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) *
          (∑ j ∈ sz, d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) := by rw [hxsum, hdzsum]
      _ = _ := Finset.sum_mul_sum sx sz
        (fun i => ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B))
        (fun j => d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B))
  have hterm (i j : ℕ) :
      ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) *
          d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) =
        d (if j = 0 then 0 else
          (-1 : R) ^ (i * (j - 1)) •
            (((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) *
              ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) ) := by
    by_cases hj : j = 0
    · subst j
      have hdj := IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
        (DirectSum.decompose 𝒜 z 0).property
      simp [hdj]
    · let k := j - 1
      have hkj : k + 1 = j := by dsimp [k]; omega
      have hinput : ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B) ∈ 𝒜 (k + 1) := by
        rw [hkj]
        exact (DirectSum.decompose 𝒜 z j).property
      have hmj := IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d)
        (n := k) hinput
      have hcomm := IsStrictlyGradedComm.graded_comm (𝒜 := 𝒜)
        (DirectSum.decompose 𝒜 x i).property hmj
      have hdiff := differential_mul_right_cycle 𝒜 d
        (x := ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B))
        (y := ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B)) (hdxi i)
      rw [ite_eq_right hj]
      simp only [map_smul]
      rw [hdiff, ← hcomm]
  have hsum : (∑ i ∈ sx, ∑ j ∈ sz,
      ((DirectSum.decompose 𝒜 x i : 𝒜 i) : B) *
        d ((DirectSum.decompose 𝒜 z j : 𝒜 j) : B)) = d w := by
    simp only [w, map_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
  rw [hmulExpand, hsum]

private def cycleSubalgebra {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] : Subalgebra R B where
  toSubsemiring := {
    carrier := cycles d
    zero_mem' := by simp [cycles]
    one_mem' := by
      change d (1 : B) = 0
      exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d)
        SetLike.GradedOne.one_mem
    add_mem' := by
      intro x y hx hy
      change d (x + y) = 0
      rw [map_add, hx, hy, add_zero]
    mul_mem' := by
      intro x y hx hy
      change d (x * y) = 0
      exact differential_mul_of_cycles 𝒜 d hx hy
  }
  algebraMap_mem' := by
    intro r
    change d (algebraMap R B r) = 0
    have h1 : (1 : B) ∈ 𝒜 0 := SetLike.GradedOne.one_mem
    have hr : algebraMap R B r ∈ 𝒜 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (𝒜 0).smul_mem r h1
    exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) hr

private theorem comp_of_graded {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (gM : ℕ → Submodule R M) (gN : ℕ → Submodule R N)
    [DirectSum.Decomposition gM] [DirectSum.Decomposition gN]
    (f : M →ₗ[R] N)
    (hf : ∀ i x, x ∈ gM i → f x ∈ gN i) (x : M) (i : ℕ) :
    (DirectSum.decompose gN (f x) i : N) = f ((DirectSum.decompose gM x i : M)) := by
  have key : ∀ z : DirectSum ℕ (fun j => gM j),
      (DirectSum.decompose gN (f ((DirectSum.decompose gM).symm z)) i : N) = f (z i : M) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j y =>
        rw [DirectSum.decompose_symm_of]
        rw [show f (y : M) = ((⟨f y, hf j y y.2⟩ : gN j) : N) from rfl]
        rw [DirectSum.decompose_coe, DirectSum.of_apply, DirectSum.of_apply]
        by_cases h : j = i
        · subst h
          simp
        · rw [dite_eq_right h, dite_eq_right h]
          simp
    | add a b ha hb =>
        have e : (DirectSum.decompose gM).symm (a + b) =
            (DirectSum.decompose gM).symm a + (DirectSum.decompose gM).symm b := by simp
        rw [e, map_add, DirectSum.decompose_add, DirectSum.add_apply,
          Submodule.coe_add, DirectSum.add_apply, Submodule.coe_add, map_add, ha, hb]
  have h := key (DirectSum.decompose gM x)
  simpa using h

private def comapGrading {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    (p : Submodule R M) (i : ℕ) : Submodule R p := (gM i).comap p.subtype

private theorem comapGrading_iSupIndep {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    [DirectSum.Decomposition gM] (p : Submodule R M) :
    iSupIndep (comapGrading gM p) := by
  have hind : iSupIndep gM := (DirectSum.Decomposition.isInternal gM).submodule_iSupIndep
  rw [iSupIndep_def] at hind ⊢
  intro i
  have hmono : Disjoint ((gM i) ⊓ p) (⨆ j, ⨆ (_ : j ≠ i), ((gM j) ⊓ p)) := by
    apply (hind i).mono inf_le_left
    refine iSup_le ?_
    intro j
    refine iSup_le ?_
    intro hj
    exact le_trans inf_le_left (le_iSup₂ (f := fun j _ => gM j) j hj)
  have hmapi : Submodule.map p.subtype (comapGrading gM p i) = (gM i) ⊓ p := by
    rw [comapGrading, Submodule.map_comap_subtype, inf_comm]
  have hmapsup : Submodule.map p.subtype (⨆ j, ⨆ (_ : j ≠ i), comapGrading gM p j) =
      ⨆ j, ⨆ (_ : j ≠ i), ((gM j) ⊓ p) := by
    simp only [Submodule.map_iSup]
    refine iSup_congr fun j => iSup_congr fun hj => ?_
    rw [comapGrading, Submodule.map_comap_subtype, inf_comm]
  rw [Submodule.disjoint_def]
  intro x hxi hxsup
  have h1 : (x : M) ∈ Submodule.map p.subtype (comapGrading gM p i) := ⟨x, hxi, rfl⟩
  have h2 : (x : M) ∈ Submodule.map p.subtype
      (⨆ j, ⨆ (_ : j ≠ i), comapGrading gM p j) := ⟨x, hxsup, rfl⟩
  rw [hmapi] at h1
  rw [hmapsup] at h2
  exact Subtype.ext ((Submodule.disjoint_def.mp hmono) (x : M) h1 h2)

private theorem comapGrading_iSup_top {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    [DirectSum.Decomposition gM] (p : Submodule R M)
    (hp : ∀ i m, m ∈ p → (DirectSum.decompose gM m i : M) ∈ p) :
    iSup (comapGrading gM p) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  classical
  set s := DFinsupp.support (DirectSum.decompose gM (y.val : M)) with hs
  have hcomp : ∀ i, ((DirectSum.decompose gM (y.val : M)) i : M) ∈ p :=
    fun i => hp i y.val y.property
  have hsum : (∑ i ∈ s, ((DirectSum.decompose gM (y.val : M)) i : M)) = (y.val : M) :=
    DirectSum.sum_support_decompose gM (y.val : M)
  have hy : y = ∑ i ∈ s,
      (⟨((DirectSum.decompose gM (y.val : M)) i : M), hcomp i⟩ : p) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using hsum.symm
  rw [hy]
  refine Submodule.sum_mem _ ?_
  intro i _
  apply Submodule.mem_iSup_of_mem i
  show ((DirectSum.decompose gM (y.val : M)) i : M) ∈ gM i
  exact ((DirectSum.decompose gM (y.val : M)) i).property

@[instance_reducible]
private noncomputable def comapGrading_decomposition {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    [DirectSum.Decomposition gM] (p : Submodule R M)
    (hp : ∀ i m, m ∈ p → (DirectSum.decompose gM m i : M) ∈ p) :
    DirectSum.Decomposition (comapGrading gM p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (comapGrading_iSupIndep gM p) (comapGrading_iSup_top gM p hp)).chooseDecomposition _

private theorem decompose_eq_zero_of_mem_iSup_ne {R : Type u} {ι : Type t}
    [CommRing R] [DecidableEq ι] {M : Type w} [AddCommGroup M] [Module R M]
    (gM : ι → Submodule R M) [DirectSum.Decomposition gM] (i : ι)
    (z : M) (hz : z ∈ ⨆ j, ⨆ (_ : j ≠ i), gM j) :
    (DirectSum.decompose gM z i : M) = 0 := by
  induction hz using Submodule.iSup_induction' with
  | mem j z hzj =>
      by_cases hj : j = i
      · subst hj
        rw [iSup_neg (fun h => h rfl)] at hzj
        rw [Submodule.mem_bot] at hzj
        simp [hzj]
      · rw [iSup_pos hj] at hzj
        rw [DirectSum.decompose_of_mem gM hzj, DirectSum.of_apply]
        rw [dite_eq_right hj]
        rfl
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, iha, ihb, add_zero]

private def quotientGrading {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    (s : Submodule R M) (i : ℕ) : Submodule R (M ⧸ s) := (gM i).map s.mkQ

private theorem quotientGrading_iSupIndep {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    [DirectSum.Decomposition gM] (s : Submodule R M)
    (hs : ∀ i m, m ∈ s → (DirectSum.decompose gM m i : M) ∈ s) :
    iSupIndep (quotientGrading gM s) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  rintro ybar hyi hysup
  obtain ⟨y, hy, rfl⟩ := hyi
  have hmapsup : (⨆ j, ⨆ (_ : j ≠ i), quotientGrading gM s j) =
      Submodule.map s.mkQ (⨆ j, ⨆ (_ : j ≠ i), gM j) := by
    simp only [quotientGrading, Submodule.map_iSup]
  rw [hmapsup] at hysup
  obtain ⟨z, hz, hzeq⟩ := hysup
  have hdiff : y - z ∈ s := by
    rw [← Submodule.Quotient.eq]
    exact hzeq.symm
  have hcomp := hs i (y - z) hdiff
  have hyc : (DirectSum.decompose gM y i : M) = y := by
    rw [DirectSum.decompose_of_mem_same gM hy]
  have hzc : (DirectSum.decompose gM z i : M) = 0 :=
    decompose_eq_zero_of_mem_iSup_ne gM i z hz
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, hyc, hzc, sub_zero] at hcomp
  show s.mkQ y = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcomp

private theorem quotientGrading_iSup_top {R : Type u} {M : Type w} [CommRing R]
    [AddCommGroup M] [Module R M] (gM : ℕ → Submodule R M)
    [DirectSum.Decomposition gM] (s : Submodule R M) :
    iSup (quotientGrading gM s) = ⊤ := by
  have htop : iSup gM = ⊤ := (DirectSum.Decomposition.isInternal gM).submodule_iSup_eq_top
  rw [eq_top_iff]
  rintro ybar -
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective s ybar
  have hy : y ∈ iSup gM := by rw [htop]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem j z hz =>
      apply Submodule.mem_iSup_of_mem j
      exact ⟨z, hz, rfl⟩
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [map_add]
      exact Submodule.add_mem _ iha ihb

@[instance_reducible]
private noncomputable def quotientGrading_decomposition {R : Type u} {M : Type w}
    [CommRing R] [AddCommGroup M] [Module R M]
    (gM : ℕ → Submodule R M) [DirectSum.Decomposition gM] (s : Submodule R M)
    (hs : ∀ i m, m ∈ s → (DirectSum.decompose gM m i : M) ∈ s) :
    DirectSum.Decomposition (quotientGrading gM s) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientGrading_iSupIndep gM s hs) (quotientGrading_iSup_top gM s)).chooseDecomposition _

private def cyclesGrading {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] (n : ℕ) :
    Submodule R (cycles d) := comapGrading 𝒜 (cycles d) n

private theorem cycle_component_mem {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    {x : B} (hx : d x = 0) (n : ℕ) :
    (DirectSum.decompose 𝒜 x n : B) ∈ cycles d :=
  LinearMap.mem_ker.mpr (differential_of_component_of_cycle 𝒜 d hx n)

@[instance_reducible]
private noncomputable def cyclesGrading_decomposition {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    DirectSum.Decomposition (cyclesGrading 𝒜 d) := by
  apply comapGrading_decomposition 𝒜 (cycles d)
  intro n x hx
  exact cycle_component_mem 𝒜 d hx n

private theorem decompose_cycles_coe {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    [DirectSum.Decomposition (cyclesGrading 𝒜 d)] (x : cycles d) (n : ℕ) :
    (DirectSum.decompose (cyclesGrading 𝒜 d) x n : B) =
      (DirectSum.decompose 𝒜 (x : B) n : B) :=
  (comp_of_graded (cyclesGrading 𝒜 d) 𝒜 (cycles d).subtype
    (fun _ _ hz => hz) x n).symm

@[instance_reducible]
private noncomputable def cyclesRing {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] : Ring (cycles d) := by
  let S := cycleSubalgebra 𝒜 d
  exact { S.toRing with
    toAddCommGroup := Submodule.addCommGroup (cycles d) }

@[instance_reducible]
private noncomputable def cyclesAlgebra {R : Type u} {B : Type w} [CommRing R] [Ring B]
    [Algebra R B] (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    letI : Ring (cycles d) := cyclesRing 𝒜 d
    Algebra R (cycles d) := by
  let : Ring (cycles d) := cyclesRing 𝒜 d
  exact (cycleSubalgebra 𝒜 d).algebra

/-- A cycle `x` is a boundary if and only if `x = d z` for some `z`. -/
public theorem mem_boundaries_iff {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] (x : cycles d) :
    x ∈ boundaries (𝒜 := 𝒜) d ↔ ∃ z, d z = (x : B) := by
  show x ∈ LinearMap.range (boundaryMap (𝒜 := 𝒜) d) ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

private theorem differential_component_is_boundary {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (𝒜 : ℕ → Submodule R B) [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    (z : B) (n : ℕ) :
    (DirectSum.decompose 𝒜 (d z) n : B) ∈ LinearMap.range d :=
  ⟨_, (decompose_d_apply 𝒜 d z n).symm⟩

private theorem boundaries_homogeneous {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d]
    [DirectSum.Decomposition (cyclesGrading 𝒜 d)]
    {x : cycles d} (hx : x ∈ boundaries (𝒜 := 𝒜) d) (n : ℕ) :
    (DirectSum.decompose (cyclesGrading 𝒜 d) x n : cycles d) ∈ boundaries (𝒜 := 𝒜) d := by
  obtain ⟨z, hz⟩ := (mem_boundaries_iff d x).mp hx
  rw [mem_boundaries_iff]
  have hcoe := decompose_cycles_coe 𝒜 d x n
  have hcomp := differential_component_is_boundary 𝒜 d z n
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hcomp
  refine ⟨w, ?_⟩
  rw [hcoe, ← hz]
  exact hw

private def boundaryIdeal {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    letI : Ring (cycles d) := cyclesRing 𝒜 d
    Ideal (cycles d) := by
  letI : Ring (cycles d) := cyclesRing 𝒜 d
  exact {
  carrier := boundaries (𝒜 := 𝒜) d
  zero_mem' := by
    change (0 : cycles d) ∈ boundaries (𝒜 := 𝒜) d
    rw [mem_boundaries_iff]
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    change x ∈ boundaries (𝒜 := 𝒜) d at hx
    change y ∈ boundaries (𝒜 := 𝒜) d at hy
    change x + y ∈ boundaries (𝒜 := 𝒜) d
    rw [mem_boundaries_iff] at hx hy ⊢
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by simp [hz, hw]⟩
  smul_mem' := by
    intro a x hx
    change x ∈ boundaries (𝒜 := 𝒜) d at hx
    change a • x ∈ boundaries (𝒜 := 𝒜) d
    rw [mem_boundaries_iff] at hx ⊢
    obtain ⟨z, hz⟩ := hx
    change ∃ w, d w = (a : B) * (x : B)
    exact cycle_mul_boundary_exists_preimage 𝒜 d a.property ⟨z, hz⟩
  }

private theorem boundaryIdeal_isTwoSided {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    letI : Ring (cycles d) := cyclesRing 𝒜 d
    (boundaryIdeal (𝒜 := 𝒜) d).IsTwoSided := by
  let : Ring (cycles d) := cyclesRing 𝒜 d
  constructor
  intro x y hx
  change x ∈ boundaries (𝒜 := 𝒜) d at hx
  show x * y ∈ boundaries (𝒜 := 𝒜) d
  rw [mem_boundaries_iff] at hx ⊢
  obtain ⟨z, hz⟩ := hx
  exact boundary_mul_cycle_exists_preimage 𝒜 d ⟨z, hz⟩ y.property

@[instance_reducible]
private noncomputable def homologyRing {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    Ring (Homology (𝒜 := 𝒜) d) := by
  let : Ring (cycles d) := cyclesRing 𝒜 d
  let I := boundaryIdeal (𝒜 := 𝒜) d
  let : I.IsTwoSided := boundaryIdeal_isTwoSided (𝒜 := 𝒜) d
  exact Ideal.Quotient.ring I

@[instance_reducible]
private noncomputable def homologyAlgebra {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    {𝒜 : ℕ → Submodule R B} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra 𝒜 d] :
    letI : Ring (Homology (𝒜 := 𝒜) d) := homologyRing (𝒜 := 𝒜) d
    Algebra R (Homology (𝒜 := 𝒜) d) := by
  let : Ring (cycles d) := cyclesRing 𝒜 d
  let : Algebra R (cycles d) := cyclesAlgebra 𝒜 d
  let : Ring (Homology (𝒜 := 𝒜) d) := homologyRing (𝒜 := 𝒜) d
  let I := boundaryIdeal (𝒜 := 𝒜) d
  let : I.IsTwoSided := boundaryIdeal_isTwoSided (𝒜 := 𝒜) d
  let h : Algebra R (cycles d ⧸ I) := Ideal.Quotient.algebra R
  change Algebra R (cycles d ⧸ I)
  exact h

private theorem homologyGrading_eq_quotientGrading {R : Type u} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    (d : B →ₗ[R] B) [IsDifferentialGradedAlgebra ℬ d]
    [DirectSum.Decomposition (cyclesGrading ℬ d)] :
    (fun n : ℕ => Submodule.span R {z : Homology (𝒜 := ℬ) d |
      ∃ x : cycles d, (x : B) ∈ ℬ n ∧
        (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) d) = z}) =
      quotientGrading (cyclesGrading ℬ d) (boundaries (𝒜 := ℬ) d) := by
  funext n
  show Submodule.span R {z : Homology (𝒜 := ℬ) d |
      ∃ x : cycles d, (x : B) ∈ ℬ n ∧
        (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) d) = z} =
    Submodule.map (Submodule.mkQ (boundaries (𝒜 := ℬ) d))
      (cyclesGrading ℬ d n)
  have hset : {z : Homology (𝒜 := ℬ) d |
      ∃ x : cycles d, (x : B) ∈ ℬ n ∧
        (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) d) = z} =
      (Submodule.mkQ (boundaries (𝒜 := ℬ) d)) ''
        {x : cycles d | x ∈ cyclesGrading ℬ d n} := by
    ext z
    simp [cyclesGrading, comapGrading]
  rw [hset, ← Submodule.map_span]
  congr 1
  exact Submodule.span_eq (R := R) (M := cycles d) (cyclesGrading ℬ d n)

end DividedPowers.TateResolution
