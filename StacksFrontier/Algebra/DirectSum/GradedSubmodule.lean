module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Gradings induced on submodules and quotients

Let `M` be a module with an internal grading `ℳ : ι → Submodule R M`, i.e. a family of
submodules carrying a `DirectSum.Decomposition`. A submodule `p ≤ M` is *homogeneous* when it
contains every graded component of each of its elements; such a `p`, and the quotient `M ⧸ p`,
then inherit gradings, namely `(ℳ i).comap p.subtype` and `(ℳ i).map p.mkQ`. This file
constructs the resulting direct-sum decompositions, together with elementary facts about graded
components.

The same induced family `(ℳ i).comap p.subtype` is also a decomposition of `p` under a quite
different hypothesis: that `p` is the supremum of an independent family, the members of which
are then its graded pieces. Both routes are provided.

## Main definitions

* `Submodule.inducedGrading`: the grading `(ℳ i).comap p.subtype` on a submodule `p`.
* `Submodule.quotientGrading`: the grading `(ℳ i).map p.mkQ` on a quotient `M ⧸ p`.
* `Submodule.inducedGrading.decomposition`,
  `Submodule.inducedGrading.decompositionOfEqISup` and
  `Submodule.quotientGrading.decomposition`: the induced direct-sum decompositions.

## Main results

* `DirectSum.coe_decompose_apply_map`: a grading-preserving linear map commutes with taking
  graded components.
* `DirectSum.coe_decompose_apply_eq_zero_of_mem_iSup_ne`: an element of `⨆_{j ≠ i} ℳ j` has
  vanishing degree-`i` component.
* `Submodule.inducedGrading_iSupIndep` and `Submodule.quotientGrading_iSupIndep`: the induced
  families are independent.
* `Submodule.inducedGrading_iSup_eq_top`, `Submodule.inducedGrading_iSup_eq_top_of_eq_iSup` and
  `Submodule.quotientGrading_iSup_eq_top`: the induced families span.
-/

@[expose] public section

universe u v w

namespace DirectSum

variable {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]

/-- A grading-preserving linear map commutes with taking graded components: the degree-`i`
component of `f x` is `f` applied to the degree-`i` component of `x`. -/
theorem coe_decompose_apply_map {M N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (ℳ : ι → Submodule R M) (𝒩 : ι → Submodule R N)
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] (f : M →ₗ[R] N)
    (hf : ∀ (i : ι) (x : M), x ∈ ℳ i → f x ∈ 𝒩 i) (x : M) (i : ι) :
    (DirectSum.decompose 𝒩 (f x) i : N) = f ((DirectSum.decompose ℳ x i : M)) := by
  classical
  have key : ∀ z : DirectSum ι (fun j => ℳ j),
      (DirectSum.decompose 𝒩 (f ((DirectSum.decompose ℳ).symm z)) i : N) = f ((z i : M)) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j y =>
        rw [DirectSum.decompose_symm_of,
          show f (y : M) = ((⟨f y, hf j y y.2⟩ : 𝒩 j) : N) from rfl, DirectSum.decompose_coe,
          DirectSum.of_apply, DirectSum.of_apply]
        by_cases h : j = i
        · subst h; simp
        · rw [dite_eq_right h, dite_eq_right h]; simp
    | add a b ha hb =>
        have e : (DirectSum.decompose ℳ).symm (a + b)
            = (DirectSum.decompose ℳ).symm a + (DirectSum.decompose ℳ).symm b := by simp
        rw [e, map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
          DirectSum.add_apply, Submodule.coe_add, map_add, ha, hb]
  simpa using key (DirectSum.decompose ℳ x)

/-- The degree-`i` component of an element of `⨆_{j ≠ i} ℳ j` vanishes. -/
theorem coe_decompose_apply_eq_zero_of_mem_iSup_ne {M : Type w} [AddCommGroup M] [Module R M]
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (i : ι) (z : M)
    (hz : z ∈ ⨆ (j : ι) (_ : j ≠ i), ℳ j) :
    (DirectSum.decompose ℳ z i : M) = 0 := by
  classical
  induction hz using Submodule.iSup_induction' with
  | mem j z hzj =>
      by_cases hj : j = i
      · subst hj
        rw [iSup_neg (fun h => h rfl), Submodule.mem_bot] at hzj
        simp [hzj]
      · rw [iSup_pos hj] at hzj
        rw [DirectSum.decompose_of_mem ℳ hzj, DirectSum.of_apply, dite_eq_right hj]
        rfl
  | zero => simp
  | add a b _ _ iha ihb =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, iha, ihb, add_zero]

end DirectSum

namespace Submodule

variable {R : Type u} [Ring R] {ι : Type v} {M : Type w} [AddCommGroup M] [Module R M]

/-- The grading induced on a submodule `p` by a family `ℳ` of submodules of the ambient module:
the degree-`i` piece is `(ℳ i) ⊓ p`, viewed inside `p`. -/
def inducedGrading (ℳ : ι → Submodule R M) (p : Submodule R M) (i : ι) : Submodule R p :=
  (ℳ i).comap p.subtype

/-- An element `x` of `p` lies in the degree-`i` induced piece if and only if `x`, viewed in
`M`, lies in `ℳ i`. -/
theorem mem_inducedGrading {ℳ : ι → Submodule R M} {p : Submodule R M} {i : ι} {x : p} :
    x ∈ inducedGrading ℳ p i ↔ (x : M) ∈ ℳ i := Iff.rfl

/-- The image in `M` of the degree-`i` induced piece of `p` is `ℳ i ⊓ p`. -/
theorem map_subtype_inducedGrading (ℳ : ι → Submodule R M) (p : Submodule R M) (i : ι) :
    Submodule.map p.subtype (inducedGrading ℳ p i) = ℳ i ⊓ p := by
  rw [inducedGrading, Submodule.map_comap_subtype, inf_comm]

/-- The grading induced on a submodule by an independent family is independent. -/
theorem inducedGrading_iSupIndep {ℳ : ι → Submodule R M} (h : iSupIndep ℳ)
    (p : Submodule R M) : iSupIndep (inducedGrading ℳ p) := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have hmono : Disjoint (ℳ i ⊓ p) (⨆ j, ⨆ (_ : j ≠ i), (ℳ j ⊓ p)) := by
    refine (h i).mono inf_le_left (iSup_le fun j => iSup_le fun hj => ?_)
    exact le_trans inf_le_left (le_iSup₂ (f := fun j _ => ℳ j) j hj)
  have hmapsup : Submodule.map p.subtype (⨆ j, ⨆ (_ : j ≠ i), inducedGrading ℳ p j)
      = ⨆ j, ⨆ (_ : j ≠ i), (ℳ j ⊓ p) := by
    simp only [Submodule.map_iSup]
    exact iSup_congr fun j => iSup_congr fun _ => map_subtype_inducedGrading ℳ p j
  rw [Submodule.disjoint_def]
  intro x hxi hxsup
  have h1 : (x : M) ∈ ℳ i ⊓ p := ⟨hxi, x.2⟩
  have h2 : (x : M) ∈ ⨆ j, ⨆ (_ : j ≠ i), (ℳ j ⊓ p) := by
    rw [← hmapsup]; exact ⟨x, hxsup, rfl⟩
  exact Subtype.ext (Submodule.disjoint_def.mp hmono (x : M) h1 h2)

/-- A homogeneous submodule is spanned by its induced graded pieces. -/
theorem inducedGrading_iSup_eq_top [DecidableEq ι] {ℳ : ι → Submodule R M}
    [DirectSum.Decomposition ℳ]
    {p : Submodule R M} (hp : ∀ (i : ι) (m : M), m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p) :
    iSup (inducedGrading ℳ p) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro y _
  have hmem : ∀ i, ((DirectSum.decompose ℳ (y.val : M)) i : M) ∈ p := fun i => hp i y.val y.2
  have hy : y = ∑ i ∈ DFinsupp.support (DirectSum.decompose ℳ (y.val : M)),
      (⟨((DirectSum.decompose ℳ (y.val : M)) i : M), hmem i⟩ : p) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using (DirectSum.sum_support_decompose ℳ (y.val : M)).symm
  rw [hy]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
  exact ((DirectSum.decompose ℳ (y.val : M)) i).2

/-- A submodule that is the supremum of a family is spanned by the pieces that family induces. -/
theorem inducedGrading_iSup_eq_top_of_eq_iSup (ℳ : ι → Submodule R M) {p : Submodule R M}
    (hp : p = ⨆ i, ℳ i) : iSup (inducedGrading ℳ p) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  have hy' : y ∈ ⨆ i, ℳ i := hp ▸ hy
  induction hy' using Submodule.iSup_induction' with
  | mem i z hz => exact Submodule.mem_iSup_of_mem i hz
  | zero => exact Submodule.zero_mem _
  | add a b ha hb iha ihb => exact Submodule.add_mem _ (iha (hp ▸ ha)) (ihb (hp ▸ hb))

/-- A homogeneous submodule of a graded module is graded by its induced pieces. -/
@[instance_reducible]
noncomputable def inducedGrading.decomposition [DecidableEq ι] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] (p : Submodule R M)
    (hp : ∀ (i : ι) (m : M), m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p) :
    DirectSum.Decomposition (inducedGrading ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (inducedGrading_iSupIndep
      (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep p)
    (inducedGrading_iSup_eq_top hp)).chooseDecomposition _

/-- The supremum of an independent family is graded by the pieces that family induces. -/
@[instance_reducible]
noncomputable def inducedGrading.decompositionOfEqISup [DecidableEq ι] (ℳ : ι → Submodule R M)
    (h : iSupIndep ℳ) (p : Submodule R M) (hp : p = ⨆ i, ℳ i) :
    DirectSum.Decomposition (inducedGrading ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (inducedGrading_iSupIndep h p)
    (inducedGrading_iSup_eq_top_of_eq_iSup ℳ hp)).chooseDecomposition _

/-- The grading induced on a quotient `M ⧸ p` by a family `ℳ` of submodules of `M`: the
degree-`i` piece is the image of `ℳ i`. -/
def quotientGrading (ℳ : ι → Submodule R M) (p : Submodule R M) (i : ι) :
    Submodule R (M ⧸ p) :=
  (ℳ i).map p.mkQ

/-- The grading induced on the quotient by a homogeneous submodule is independent. -/
theorem quotientGrading_iSupIndep [DecidableEq ι] {ℳ : ι → Submodule R M}
    [DirectSum.Decomposition ℳ]
    {p : Submodule R M}
    (hp : ∀ (i : ι) (m : M), m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p) :
    iSupIndep (quotientGrading ℳ p) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  rintro ybar hyi hysup
  obtain ⟨y, hy, rfl⟩ := hyi
  have hmapsup : (⨆ (j : ι) (_ : j ≠ i), quotientGrading ℳ p j)
      = Submodule.map p.mkQ (⨆ (j : ι) (_ : j ≠ i), ℳ j) := by
    simp only [quotientGrading, Submodule.map_iSup]
  obtain ⟨z, hz, hzeq⟩ := hmapsup ▸ hysup
  have hcomp := hp i (y - z) ((Submodule.Quotient.eq p).mp hzeq.symm)
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    show (DirectSum.decompose ℳ y i : M) = y from DirectSum.decompose_of_mem_same ℳ hy,
    DirectSum.coe_decompose_apply_eq_zero_of_mem_iSup_ne ℳ i z hz, sub_zero] at hcomp
  exact (Submodule.Quotient.mk_eq_zero p).mpr hcomp

/-- The grading induced on a quotient of a graded module spans the quotient. -/
theorem quotientGrading_iSup_eq_top [DecidableEq ι] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ]
    (p : Submodule R M) : iSup (quotientGrading ℳ p) = ⊤ := by
  rw [eq_top_iff]
  rintro ybar -
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective p ybar
  have hy : y ∈ iSup ℳ :=
    (DirectSum.Decomposition.isInternal ℳ).submodule_iSup_eq_top ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem j z hz => exact Submodule.mem_iSup_of_mem j ⟨z, hz, rfl⟩
  | zero => simp
  | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb

/-- The quotient of a graded module by a homogeneous submodule is graded by the images of the
graded pieces. -/
@[instance_reducible]
noncomputable def quotientGrading.decomposition [DecidableEq ι] (ℳ : ι → Submodule R M)
    [DirectSum.Decomposition ℳ] (p : Submodule R M)
    (hp : ∀ (i : ι) (m : M), m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p) :
    DirectSum.Decomposition (quotientGrading ℳ p) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientGrading_iSupIndep hp) (quotientGrading_iSup_eq_top ℳ p)).chooseDecomposition _

end Submodule
