module

public import StacksFrontier.Algebra.DifferentialGraded.Basic

@[expose] public section

/-!
# The telescope of a filtration with property (P)

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `P` be a
right differential graded `A`-module carrying a filtration `F_*` as in property (P), that is
a `Stacks.DifferentialGraded.DGModule.PropertyPFiltration`.  This file constructs the *telescope*
  of `F_*`:
the differential graded `A`-module `⨁_{i ≥ 0} F_i P`, the two homomorphisms `α = id - shift`
and `β = ∑ inclusions` out of and into it, and the proof that
`0 → ⨁_{i ≥ 0} F_i P →[α] ⨁_{i ≥ 0} F_i P →[β] P → 0`
is an admissible short exact sequence of differential graded `A`-modules.

The differential graded vocabulary itself — `DGAlgebra`, `DGModule`, its homomorphisms,
submodules, direct sums, shifts, admissible monomorphisms and epimorphisms, and
`PropertyPFiltration` — lives in `StacksFrontier.Algebra.DifferentialGraded.Basic`, which this
file imports.

## Main definitions

* `Stacks.DifferentialGraded.DGModule.telescopeObj`: the telescope object `⨁_{i ≥ 0} F_i P`.
* `Stacks.DifferentialGraded.DGModule.telescopeAlphaFun`,
  `Stacks.DifferentialGraded.DGModule.telescopeBetaFun`: the
  underlying linear maps of `α` and `β`.

## Main results

* `Stacks.DifferentialGraded.DGModule.admissible_ses_of_propertyP`: Stacks Tag 09KL, the
  telescoping admissible short exact sequence attached to a filtration with property (P).

## References

* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL)
-/

-- needed file-scoped: the `rw`/`change` steps in the telescope proofs below rely on defeq
-- that ignores transparency, because `directSum`/`shiftFree`/`DGSubmodule.toDGModule` are
-- semireducible defs whose `DFinsupp`/`Subtype` unfoldings those steps pattern-match against.
set_option backward.isDefEq.respectTransparency false

universe u v w w₀ w₁ wq

open scoped DirectSum
open MulOpposite

namespace Stacks.DifferentialGraded

variable {R : Type u} [CommRing R]

namespace DGModule

variable {A : DGAlgebra R}

/- ## Main Statement (Tag 09KL, Lemma 22.20.1)

Let `(A, d)` be a differential graded algebra and `P` a differential graded `A`-module.
Given a filtration `F_*` as in property (P), the telescoping sequence
`0 → ⨁_{i≥0} F_i P → ⨁_{i≥0} F_i P → P → 0`
is an admissible short exact sequence of differential graded `A`-modules, where
`β` is the sum of the inclusions `F_i P ↪ P` and `α` is `id - shift`
(`x ∈ F_i P ↦ x - ι_i x`, into the `i`-th and `(i+1)`-st summands respectively).
-/

/-- The source/target object `⨁_{i ≥ 0} F_i P` of the telescoping sequence. -/
noncomputable def telescopeObj {P : DGModule A} (F : PropertyPFiltration P) : DGModule A :=
  directSum (fun i : ℕ => (F.F i).toDGModule)

/-- The underlying `Aᵐᵒᵖ`-linear map of `β : ⨁_i F_i P → P`, the direct sum of the
inclusions `F_i P ↪ P`. -/
noncomputable def telescopeBetaFun {P : DGModule A} (F : PropertyPFiltration P) :
    (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] P.carrier :=
  DirectSum.toModule _ _ _ (fun i => (F.F i).toSubmodule.subtype)

/-- The underlying `Aᵐᵒᵖ`-linear map of `α : ⨁_i F_i P → ⨁_i F_i P`, which on the `i`-th
summand `F_i P` is `x ↦ x - ι_i x` (where `x` lands in the `i`-th summand and `ι_i x`,
the inclusion of `x` into `F_{i+1} P`, lands in the `(i+1)`-st summand). -/
noncomputable def telescopeAlphaFun {P : DGModule A} (F : PropertyPFiltration P) :
    (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
  DirectSum.toModule _ _ _ (fun i =>
    (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i)
      - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (i + 1)).comp
          (F.inclHom i).toFun)

/- ## Proof sketch of Tag 09KL: decomposition into sub-lemmas

The conjunctive goal of `admissible_ses_of_propertyP` decomposes into eight
independently-provable obligations, formalized as the lemmas below.  Each carries the
informal argument for why the sequence is exact and admissible
as a comment, with the proof left open for the formal (closing) phase.

Notation: write `G := telescopeObj F` (carrier `⨁_{i≥0} F_i P`), `lof i` for the canonical
inclusion of the `i`-th summand `F_i P ↪ G`, and `ι_i := (F.inclHom i).toFun : F_i P → F_{i+1}P`
the filtration inclusion.  By definition (`telescopeAlphaFun`, `telescopeBetaFun`):
* `α (lof i x) = lof i x − lof (i+1) (ι_i x)`     (the "id − shift" / telescope map);
* `β (lof i x) = (F.F i).subtype x = x`            (sum of the inclusions `F_i P ↪ P`).
The universal property `DirectSum.toModule … ∘ lof i = (fun i ↦ …) i` (`DirectSum.toModule_lof`)
reduces every claim about `α`, `β` to the per-summand formulas above. -/

/-- `α` on a single summand: `x ↦ x - ι_i x`. -/
private theorem telescopeAlphaFun_of {P : DGModule A} (F : PropertyPFiltration P) (i : ℕ)
    (a : (F.F i).toDGModule.carrier) :
    telescopeAlphaFun F ((DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) a)
      = (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i) a
        - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (i + 1))
            ((F.inclHom i).toFun a) :=
  DirectSum.toModule_lof (A.carrier)ᵐᵒᵖ (M := fun i => (F.F i).toDGModule.carrier) i a
    (φ := fun i =>
      (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i)
        - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (i + 1)).comp
            (F.inclHom i).toFun)

/-- `β` on a single summand is the inclusion `F_i P ↪ P`. -/
private theorem telescopeBetaFun_of {P : DGModule A} (F : PropertyPFiltration P) (i : ℕ)
    (a : (F.F i).toDGModule.carrier) :
    telescopeBetaFun F ((DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) a)
      = (F.F i).toSubmodule.subtype a :=
  DirectSum.toModule_lof (A.carrier)ᵐᵒᵖ (M := fun i => (F.F i).toSubmodule) i a

/-- The differential of the telescope object acts summandwise. -/
private theorem telescopeObj_d_of {P : DGModule A} (F : PropertyPFiltration P) (i : ℕ)
    (a : (F.F i).toDGModule.carrier) :
    (telescopeObj F).d ((DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) a)
      = (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) ((F.F i).toDGModule.d a) :=
  DirectSum.toModule_lof (R := R) (M := fun i => (F.F i).toDGModule.carrier) i a

/-- A linear map out of the telescope object that preserves the grading on each summand
preserves the grading. -/
private theorem telescope_map_grading {P : DGModule A} (F : PropertyPFiltration P)
    {M : DGModule A} (f : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] M.carrier)
    (h : ∀ (n : ℤ) (i : ℕ) (a : (F.F i).toDGModule.carrier), a ∈ (F.F i).grading n →
      f ((DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) a) ∈ M.grading n)
    (n : ℤ) (x : (telescopeObj F).carrier) (hx : x ∈ (telescopeObj F).grading n) :
    f x ∈ M.grading n := by
  classical
  rw [← DirectSum.sum_support_of (β := fun i => (F.F i).toDGModule.carrier) x, map_sum]
  exact sum_mem fun i _ => h n i _ (hx i)

set_option maxHeartbeats 1000000 in
-- long proof checking every DG-module law componentwise over the `DirectSum`
/-- **(1) Lawfulness of the telescope object.**
`G = ⨁_{i≥0} F_i P` is a lawful DG `A`-module.  Each `F_i P = (F.F i).toDGModule` is lawful
by `F.F_lawful i`, and `directSum` is lawful whenever every summand is: the internal-direct-sum
grading of `G` is the "all components homogeneous of degree `n`" grading (`directSumGrading`),
`DirectSum.IsInternal` for `G` follows from internality of each summand and of the indexing
`⨁`, the action `op a • -` and the differential `directSumD` both act componentwise, so
`grading_smul`, `d_mem`, `d_comp_d`, and the graded Leibniz rule all hold componentwise from
the corresponding laws of each `F_i P` (which in turn come from `hP` via `DGSubmodule`). -/
theorem telescopeObj_isLawful {P : DGModule A} (hP : P.IsLawful)
    (F : PropertyPFiltration P) : (telescopeObj F).IsLawful := by
  -- SANITY CHECK PASSED
  classical
  -- Abbreviation for the summands.
  set N : ℕ → DGModule A := fun i => (F.F i).toDGModule with hN
  -- Membership in `(F.F i).grading` unfolds to membership of the underlying element in
  -- `P.grading`.
  have mem_grading : ∀ i (n : ℤ) (y : (N i).carrier),
      y ∈ (N i).grading n ↔ ((F.F i).toSubmodule.subtype y : P.carrier) ∈ P.grading n := by
    intro i n y
    rfl
  -- The differential on a summand is the restriction of `P.d`.
  have d_eq : ∀ i (y : (N i).carrier),
      ((F.F i).toSubmodule.subtype ((N i).d y) : P.carrier) = P.d ((F.F i).toSubmodule.subtype
          y) := by
    intro i y
    rfl
  -- The right `A`-action on a summand is the restriction of that on `P`.
  have smul_eq : ∀ i (a : A.carrier) (y : (N i).carrier),
      ((F.F i).toSubmodule.subtype ((op a) • y) : P.carrier)
        = (op a) • ((F.F i).toSubmodule.subtype y) := by
    intro i a y
    rfl
  -- Each summand `(F.F i).toDGModule` is itself a lawful DG module.
  have summandLawful : ∀ i, (N i).IsLawful := by
    intro i
    refine ⟨F.F_lawful i, ?_, ?_, ?_, ?_⟩
    · -- grading_smul
      intro n m y a hy ha
      rw [mem_grading] at hy ⊢
      rw [smul_eq]
      exact hP.grading_smul n m _ a hy ha
    · -- d_mem
      intro n y hy
      rw [mem_grading] at hy ⊢
      rw [d_eq]
      exact hP.d_mem n _ hy
    · -- d_comp_d
      intro y
      apply Subtype.ext
      change ((F.F i).toSubmodule.subtype ((N i).d ((N i).d y)) : P.carrier)
          = ((F.F i).toSubmodule.subtype 0 : P.carrier)
      rw [d_eq, d_eq]
      simp [hP.d_comp_d]
    · -- leibniz
      intro n m y a hy ha
      rw [mem_grading] at hy
      apply Subtype.ext
      change ((F.F i).toSubmodule.subtype ((N i).d ((op a) • y)) : P.carrier)
          = ((F.F i).toSubmodule.subtype
              ((op a) • (N i).d y + ((-1 : ℤ) ^ n.natAbs) • (op (A.d a) • y)) : P.carrier)
      rw [d_eq, smul_eq]
      show P.d ((op a) • ((F.F i).toSubmodule.subtype y)) = _
      rw [hP.leibniz n m _ a hy ha]
      rfl
  -- The differential of the direct sum, read componentwise.
  have d_ds : ∀ (x : ⨁ i, (N i).carrier) (i : ℕ),
      (directSumD N x) i = (N i).d (x i) := by
    intro x j
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        have hlof : directSumD N ((DirectSum.of (fun i => (N i).carrier) i) a)
            = (DirectSum.of (fun i => (N i).carrier) i) ((N i).d a) :=
          DirectSum.toModule_lof (R := R) (M := fun i => (N i).carrier) i a
        rw [hlof]
        by_cases hij : i = j
        · subst hij
          rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)]
          simp
    | add a b ha hb =>
        rw [map_add, DirectSum.add_apply, DirectSum.add_apply, ha, hb, map_add]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- isInternal
    change Function.Bijective (DirectSum.coeAddMonoidHom (directSumGrading N))
    -- Each summand is internally graded.
    have hbij : ∀ i, Function.Bijective (DirectSum.coeAddMonoidHom (N i).grading) :=
      fun i => F.F_lawful i
    -- Per-degree projection to the `i`-th summand grading.
    let pdeg : ∀ (i : ℕ) (n : ℤ), ↥(directSumGrading N n) →+ ↥((N i).grading n) := fun i n =>
      { toFun := fun w => ⟨(w : ⨁ j, (N j).carrier) i, w.2 i⟩
        map_zero' := by apply Subtype.ext; simp
        map_add' := by intro a b; apply Subtype.ext; simp }
    -- Projection on the whole graded direct sum.
    let proj : ∀ i, (⨁ n, ↥(directSumGrading N n)) →+ (⨁ n, ↥((N i).grading n)) := fun i =>
      DirectSum.map (fun n => pdeg i n)
    have proj_of : ∀ i n (w : ↥(directSumGrading N n)),
        proj i ((DirectSum.of (fun n => ↥(directSumGrading N n)) n) w)
          = (DirectSum.of (fun n => ↥((N i).grading n)) n) (pdeg i n w) := by
      intro i n w
      exact DirectSum.map_of (fun n => pdeg i n) n w
    -- Bridge: the `i`-th component of the total coercion is the per-summand coercion of `proj i`.
    have bridge : ∀ (i : ℕ) (z : ⨁ n, ↥(directSumGrading N n)),
        (DirectSum.coeAddMonoidHom (directSumGrading N) z : ⨁ j, (N j).carrier) i
          = DirectSum.coeAddMonoidHom (N i).grading (proj i z) := by
      intro i z
      induction z using DirectSum.induction_on with
      | zero => simp
      | of n w =>
          rw [DirectSum.coeAddMonoidHom_of, proj_of, DirectSum.coeAddMonoidHom_of]
          rfl
      | add a b ha hb =>
          simp only [map_add, DirectSum.add_apply, ha, hb]
    -- Component of `proj i z` at degree `n`.
    have proj_apply : ∀ i (z : ⨁ n, ↥(directSumGrading N n)) (n : ℤ),
        (proj i z) n = pdeg i n (z n) := by
      intro i z n
      exact DirectSum.map_apply (fun n => pdeg i n) n z
    constructor
    · -- injective
      rw [injective_iff_map_eq_zero]
      intro z hz
      -- each `proj i z = 0`
      have hpz : ∀ i, proj i z = 0 := by
        intro i
        apply (hbij i).injective
        rw [← bridge i z, hz]
        simp
      -- conclude `z = 0` degreewise and componentwise
      apply DirectSum.ext (fun n => ?_)
      apply Subtype.ext
      apply DirectSum.ext (fun i => ?_)
      have hcomp : (pdeg i n (z n) : ↥((N i).grading n)) = (0 : ↥((N i).grading n)) := by
        rw [← proj_apply i z n, hpz i]; simp
      have hval : ((z n : ↥(directSumGrading N n)) : ⨁ j, (N j).carrier) i = 0 := by
        change ((pdeg i n (z n) : ↥((N i).grading n)) : (N i).carrier) = 0
        rw [hcomp]; simp
      rw [hval]; simp
    · -- surjective
      -- per-`j` embedding of `(N j).grading n` into the product grading.
      intro m
      induction m using DirectSum.induction_on with
      | zero => exact ⟨0, by simp⟩
      | of j a =>
          -- preimage of `a` under the `j`-th internal bijection
          obtain ⟨u, hu⟩ := (hbij j).surjective a
          -- the embedding map `Z j`
          let embj : ∀ (n : ℤ), ↥((N j).grading n) →+ ↥(directSumGrading N n) := fun n =>
            { toFun := fun c => ⟨(DirectSum.of (fun k => (N k).carrier) j (c : (N j).carrier)),
                by
                  intro k
                  by_cases hjk : j = k
                  · subst hjk; rw [DirectSum.of_eq_same]; exact c.2
                  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk)]; exact AddSubgroup.zero_mem _⟩
              map_zero' := by apply Subtype.ext; simp
              map_add' := by
                intro c d; apply Subtype.ext
                change (DirectSum.of (fun k => (N k).carrier) j) ((c : (N j).carrier) + d) = _
                rw [map_add]; rfl }
          let Z : (⨁ n, ↥((N j).grading n)) →+ (⨁ n, ↥(directSumGrading N n)) :=
            DirectSum.map embj
          refine ⟨Z u, ?_⟩
          -- `coe (Z u) = of j (coe u) = of j a`
          have key : ∀ v : ⨁ n, ↥((N j).grading n),
              DirectSum.coeAddMonoidHom (directSumGrading N) (Z v)
              = (DirectSum.of (fun k => (N k).carrier) j)
                  (DirectSum.coeAddMonoidHom (N j).grading v) := by
            intro v
            induction v using DirectSum.induction_on with
            | zero => simp
            | of n c =>
                rw [show Z ((DirectSum.of (fun n => ↥((N j).grading n)) n) c)
                      = (DirectSum.of (fun n => ↥(directSumGrading N n)) n) (embj n c) from
                    DirectSum.map_of embj n c,
                  DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
                rfl
            | add a b ha hb =>
                rw [map_add, map_add, ha, hb, map_add, ← map_add]
          rw [key u, hu]
      | add a b ha hb =>
          obtain ⟨za, hza⟩ := ha
          obtain ⟨zb, hzb⟩ := hb
          exact ⟨za + zb, by rw [map_add, hza, hzb]⟩
  · -- grading_smul
    change ∀ (n m : ℤ) (x : ⨁ i, (N i).carrier) (a : A.carrier),
        x ∈ directSumGrading N n → a ∈ A.grading m →
        (op a) • x ∈ directSumGrading N (n + m)
    intro n m x a hx ha i
    rw [DirectSum.smul_apply]
    exact (summandLawful i).grading_smul n m (x i) a (hx i) ha
  · -- d_mem
    change ∀ (n : ℤ) (x : ⨁ i, (N i).carrier),
        x ∈ directSumGrading N n → directSumD N x ∈ directSumGrading N (n + 1)
    intro n x hx i
    rw [d_ds]
    exact (summandLawful i).d_mem n (x i) (hx i)
  · -- d_comp_d
    change ∀ (x : ⨁ i, (N i).carrier), directSumD N (directSumD N x) = 0
    intro x
    apply DirectSum.ext (fun i => ?_)
    rw [d_ds, d_ds, (summandLawful i).d_comp_d (x i)]
    rfl
  · -- leibniz
    change ∀ (n m : ℤ) (x : ⨁ i, (N i).carrier) (a : A.carrier),
        x ∈ directSumGrading N n → a ∈ A.grading m →
        directSumD N (op a • x)
          = op a • directSumD N x
            + ((-1 : ℤ) ^ n.natAbs) • ((op (A.d a)) • x)
    intro n m x a hx ha
    apply DirectSum.ext (fun i => ?_)
    rw [DirectSum.add_apply, DirectSum.smul_apply, DirectSum.smul_apply, DirectSum.smul_apply,
      d_ds, DirectSum.smul_apply, d_ds,
      (summandLawful i).leibniz n m (x i) a (hx i) ha]

/-- **(2) `α` is a DG homomorphism with the prescribed underlying map.**
The underlying map `telescopeAlphaFun F` is `Aᵐᵒᵖ`-linear by construction.  It is
grading-preserving: on summand `i`, `lof i` and `lof (i+1)` preserve degree, and `ι_i`
preserves degree (it is a `Hom`), so `x ↦ lof i x − lof (i+1) (ι_i x)` maps degree-`n`
elements to degree-`n` elements.  It commutes with the differential: the differential on `G`
is componentwise (`directSumD`), `lof i` commutes with `d` (intertwines `(F_i P).d` and the
`i`-th component of `directSumD`), and `ι_i` commutes with `d` (`(F.inclHom i).commute_d`),
whence `d (lof i x − lof (i+1)(ι_i x)) = lof i (d x) − lof (i+1)(ι_i (d x)) = α (lof i (d x))`,
i.e. `d ∘ α = α ∘ d` on each summand, hence everywhere by linearity and `DirectSum.toModule`. -/
theorem exists_telescopeAlpha {P : DGModule A}
    (F : PropertyPFiltration P) :
    ∃ α : Hom (telescopeObj F) (telescopeObj F), α.toFun = telescopeAlphaFun F := by
  -- SANITY CHECK PASSED
  classical
  -- helper_09kl: a `lof i y` element lands in the direct-sum grading whenever `y` is homogeneous
  have lof_mem : ∀ n i (y : (F.F i).toDGModule.carrier), y ∈ (F.F i).grading n →
      (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i) y
        ∈ (telescopeObj F).grading n := by
    intro n i y hy j
    change (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i y) j ∈ (F.F j).grading n
    rw [DirectSum.of_apply]
    by_cases hij : i = j
    · subst hij
      simpa using hy
    · rw [dite_eq_right hij]
      simp
  refine ⟨{ toFun := telescopeAlphaFun F, map_grading := ?_, commute_d := ?_ }, rfl⟩
  · refine telescope_map_grading F _ fun n i a ha => ?_
    rw [telescopeAlphaFun_of]
    exact sub_mem (lof_mem n i _ ha) (lof_mem n (i + 1) _ ((F.inclHom i).map_grading n _ ha))
  · intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeObj_d_of, telescopeAlphaFun_of, telescopeAlphaFun_of, map_sub]
        simp only [DirectSum.lof_eq_of]
        rw [telescopeObj_d_of, telescopeObj_d_of, (F.inclHom i).commute_d a]
    | add a b ha hb =>
        rw [map_add, map_add, map_add, ha, hb, map_add]

/-- **(3) `β` is a DG homomorphism with the prescribed underlying map.**
`telescopeBetaFun F = DirectSum.toModule … (fun i ↦ (F.F i).subtype)` is `Aᵐᵒᵖ`-linear by
construction.  It is grading-preserving: each inclusion `F_i P ↪ P` preserves degree (the
grading on `F_i P` is `(P.grading n).comap subtype`, so `subtype` maps `(F_i P)^n` into `P^n`),
hence by `DirectSum.toModule` so does `β`.  It commutes with the differential: each inclusion
`(F.F i).incl` commutes with `d` (`DGSubmodule.incl.commute_d`, since the submodule differential
is the restriction of `P.d`), and the `G`-differential is componentwise, so
`β (d (lof i x)) = β (lof i (d x)) = subtype (d x) = P.d (subtype x) = P.d (β (lof i x))`. -/
theorem exists_telescopeBeta {P : DGModule A}
    (F : PropertyPFiltration P) :
    ∃ β : Hom (telescopeObj F) P, β.toFun = telescopeBetaFun F := by
  -- SANITY CHECK PASSED
  refine ⟨{ toFun := telescopeBetaFun F, map_grading := ?_, commute_d := ?_ }, rfl⟩
  · refine telescope_map_grading F _ fun n i a ha => ?_
    rw [telescopeBetaFun_of]
    exact ha
  · intro x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeObj_d_of, telescopeBetaFun_of, telescopeBetaFun_of]
        rfl
    | add a b ha hb =>
        rw [map_add, map_add, map_add, ha, hb, map_add]

/-- **(4) Injectivity of `α` (telescope).**
Let `x = (x_i) ∈ ⨁_i F_i P` with `α x = 0`.  Computing components: the `j`-th component of
`α x` is `x_j − ι_{j-1}(x_{j-1})` (with the convention `x_{-1} = 0`).  As `x` has finite
support, let `j₀` be minimal with `x_{j₀} ≠ 0`; then the `j₀`-th component of `α x` is
`x_{j₀} − ι_{j₀-1}(x_{j₀-1}) = x_{j₀} − 0 = x_{j₀} ≠ 0`, contradicting `α x = 0`.  Hence
`x = 0`.  (Equivalently, induct on `j`: the `0`-component gives `x_0 = 0`, then the
`(j+1)`-component gives `x_{j+1} = ι_j(x_j) = 0`.)  Formally: read off
`(telescopeAlphaFun F x) j` via `DirectSum.toModule_lof`/`DFinsupp` component lemmas and run the
strong induction on the support. -/
theorem telescopeAlphaFun_injective {P : DGModule A}
    (F : PropertyPFiltration P) : Function.Injective (telescopeAlphaFun F) := by
  -- SANITY CHECK PASSED
  classical
  -- component of `of` in application form
  have of_comp : ∀ i (a : (F.F i).toDGModule.carrier) k,
      DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) k
        (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i a)
        = (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i a) k := fun i a k =>
    (DirectSum.apply_eq_component (A.carrier)ᵐᵒᵖ
      (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i a) k).symm
  -- `lof` and `of` agree at every component
  have lof_comp : ∀ i (a : (F.F i).toDGModule.carrier) k,
      DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) k
        (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i a)
        = (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i a) k := fun i a k =>
    (DirectSum.apply_eq_component (A.carrier)ᵐᵒᵖ
      (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i a) k).symm
  -- the `(j+1)`-th component of `α y`
  have comp_succ : ∀ (y : (telescopeObj F).carrier) (j : ℕ),
      DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (j + 1)
          (telescopeAlphaFun F y)
        = DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (j + 1) y
          - (F.inclHom j).toFun
              (DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) j y) := by
    intro y j
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeAlphaFun_of, map_sub]
        simp only [lof_comp, of_comp]
        by_cases hij : i = j
        · subst hij
          simp only [DirectSum.of_eq_same]
        · have h1 : (DirectSum.of (fun i => (F.F i).toDGModule.carrier) (i + 1)
              ((F.inclHom i).toFun a)) (j + 1) = 0 :=
            DirectSum.of_eq_of_ne _ _ _ (by omega)
          have h2 : (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i a) j = 0 :=
            DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)
          rw [h1, h2]
          simp
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb]
        simp only [map_add]
        abel
  -- the `0`-th component of `α y`
  have comp_zero : ∀ (y : (telescopeObj F).carrier),
      DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) 0
          (telescopeAlphaFun F y)
        = DirectSum.component (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) 0 y := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeAlphaFun_of, map_sub]
        simp only [lof_comp, of_comp]
        have h1 : (DirectSum.of (fun i => (F.F i).toDGModule.carrier) (i + 1)
            ((F.inclHom i).toFun a)) 0 = 0 :=
          DirectSum.of_eq_of_ne _ _ _ (by omega)
        rw [h1]
        simp
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb, map_add]
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- every component of `x` vanishes, by induction
  have hxj : ∀ j, DirectSum.component (A.carrier)ᵐᵒᵖ ℕ
      (fun i => (F.F i).toDGModule.carrier) j x = 0 := by
    intro j
    induction j with
    | zero =>
        rw [← comp_zero x, hx, map_zero]
    | succ j ih =>
        have h := comp_succ x j
        rw [hx, map_zero] at h
        rw [ih, map_zero, sub_zero] at h
        exact h.symm
  -- conclude `x = 0`
  apply DirectSum.ext
  intro j
  rw [DirectSum.apply_eq_component (A.carrier)ᵐᵒᵖ x j, hxj j]
  simp

/-- **(5) Surjectivity of `β`.**
By `F.exhaustive`, every `p ∈ P` lies in some `F_q P`; then `β (lof q ⟨p, _⟩) = p` since on the
`q`-th summand `β` is the inclusion `F_q P ↪ P`.  So `β` is surjective. -/
theorem telescopeBetaFun_surjective {P : DGModule A}
    (F : PropertyPFiltration P) : Function.Surjective (telescopeBetaFun F) := by
  -- SANITY CHECK PASSED
  intro p
  obtain ⟨q, hq⟩ := F.exhaustive p
  refine ⟨DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toSubmodule) q ⟨p, hq⟩, ?_⟩
  exact telescopeBetaFun_of F q ⟨p, hq⟩

/-- **(6) Exactness: `range α = ker β`.**
`⊆`: `β (α (lof i x)) = β (lof i x) − β (lof (i+1)(ι_i x)) = x − ι_i x = 0` in `P` (both equal
the image of `x` under `F_i P ↪ P`, since `ι_i` is the filtration inclusion, compatible via
`F.inclHom_apply`).  Hence `β ∘ α = 0`, i.e. `range α ⊆ ker β`.
`⊇`: suppose `x = (x_i)` with `β x = Σ_i (incl x_i) = 0` in `P`.  Define `z_i := Σ_{j ≤ i} x_j`
computed inside `F_i P` (legitimate: for `j ≤ i`, `x_j ∈ F_j P ⊆ F_i P` by `F.mono`, so the
partial sum lands in `F_i P`).  Then `z = (z_i)` has finite support: for `i` beyond the support
of `x` and large enough, `incl z_i = β x = 0`, and since each `incl` is injective `z_i = 0`.
A direct computation gives `α z = x` (the telescope `z_i − ι_{i-1}(z_{i-1}) = x_i`).  Hence
`x ∈ range α`.  This is the standard mapping-telescope presentation of the colimit
`P = colim_i F_i P`. -/
theorem telescope_exact {P : DGModule A}
    (F : PropertyPFiltration P) :
    LinearMap.range (telescopeAlphaFun F) = LinearMap.ker (telescopeBetaFun F) := by
  -- SANITY CHECK PASSED
  classical
  -- Abbreviations.
  set R := LinearMap.range (telescopeAlphaFun F) with hR
  -- `α (lof i a) ∈ R` and pushes `lof i a` up one level.
  have push_one : ∀ i (a : (F.F i).toDGModule.carrier),
      (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) i) a
        - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (i + 1))
            ((F.inclHom i).toFun a) ∈ R := by
    intro i a
    rw [hR, ← telescopeAlphaFun_of]
    exact ⟨_, rfl⟩
  -- Push-up lemma: send `lof a c` up to any level `b ≥ a`, modulo `R`, preserving `β`-image.
  have push : ∀ (b a : ℕ) (c : (F.F a).toDGModule.carrier), a ≤ b →
      ∃ c' : (F.F b).toDGModule.carrier,
        (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) a) c
          - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) b) c' ∈ R
        ∧ (F.F b).toSubmodule.subtype c' = (F.F a).toSubmodule.subtype c := by
    intro b
    induction b with
    | zero =>
        intro a c hab
        have ha0 : a = 0 := Nat.le_zero.1 hab
        subst ha0
        exact ⟨c, by simp, rfl⟩
    | succ b ih =>
        intro a c hab
        rcases Nat.lt_or_ge a (b + 1) with hlt | hge
        · -- `a ≤ b`, push to `b` then one more step.
          have hab' : a ≤ b := Nat.lt_succ_iff.1 hlt
          obtain ⟨c', hc'mem, hc'sub⟩ := ih a c hab'
          refine ⟨(F.inclHom b).toFun c', ?_, ?_⟩
          · have hstep := push_one b c'
            have : (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) a) c
                - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (b + 1))
                    ((F.inclHom b).toFun c')
                = ((DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) a) c
                    - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) b) c')
                  + ((DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) b) c'
                    - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) (b + 1))
                        ((F.inclHom b).toFun c')) := by abel
            rw [this]
            exact Submodule.add_mem R hc'mem hstep
          · rw [F.inclHom_apply b c', hc'sub]
        · -- `a = b + 1`.
          have ha : a = b + 1 := le_antisymm hab hge
          subst ha
          exact ⟨c, by simp, rfl⟩
  -- Main congruence: every `x` is congruent mod `R` to a single-summand element with the same
  -- `β`-image.
  have main : ∀ x : ⨁ i, (F.F i).toDGModule.carrier, ∃ N, ∃ c : (F.F N).toDGModule.carrier,
      x - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) N) c ∈ R
      ∧ (F.F N).toSubmodule.subtype c = telescopeBetaFun F x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero =>
        exact ⟨0, 0, by simp, by simp⟩
    | of i a =>
        exact ⟨i, a, by simp [DirectSum.lof_eq_of], (telescopeBetaFun_of F i a).symm⟩
    | add x y hx hy =>
        obtain ⟨N₁, c₁, hc₁mem, hc₁sub⟩ := hx
        obtain ⟨N₂, c₂, hc₂mem, hc₂sub⟩ := hy
        obtain ⟨d₁, hd₁mem, hd₁sub⟩ := push (N₁ + N₂) N₁ c₁ (Nat.le_add_right _ _)
        obtain ⟨d₂, hd₂mem, hd₂sub⟩ := push (N₁ + N₂) N₂ c₂ (Nat.le_add_left _ _)
        refine ⟨N₁ + N₂, d₁ + d₂, ?_, ?_⟩
        · have e :
              x + y - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                  (fun i => (F.F i).toDGModule.carrier) (N₁ + N₂)) (d₁ + d₂)
              = (x - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                    (fun i => (F.F i).toDGModule.carrier) N₁) c₁)
                + (y - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                    (fun i => (F.F i).toDGModule.carrier) N₂) c₂)
                + ((DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                      (fun i => (F.F i).toDGModule.carrier) N₁) c₁
                    - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                        (fun i => (F.F i).toDGModule.carrier) (N₁ + N₂)) d₁)
                + ((DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                      (fun i => (F.F i).toDGModule.carrier) N₂) c₂
                    - (DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ
                        (fun i => (F.F i).toDGModule.carrier) (N₁ + N₂)) d₂) := by
            rw [map_add]; abel
          rw [e]
          exact Submodule.add_mem R (Submodule.add_mem R (Submodule.add_mem R hc₁mem hc₂mem)
            hd₁mem) hd₂mem
        · rw [map_add, map_add, hd₁sub, hd₂sub, hc₁sub, hc₂sub]
  -- Now prove the set equality by antisymmetry.
  apply le_antisymm
  · -- range α ⊆ ker β, i.e. β ∘ α = 0.
    rintro g ⟨y, rfl⟩
    simp only [LinearMap.mem_ker]
    induction y using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeAlphaFun_of, map_sub, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
          telescopeBetaFun_of, telescopeBetaFun_of, F.inclHom_apply i a, sub_self]
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb, add_zero]
  · -- ker β ⊆ range α.
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨N, c, hcmem, hcsub⟩ := main x
    have hc0 : (F.F N).toSubmodule.subtype c = 0 := by rw [hcsub, hx]
    have hc : c = 0 := by
      have := Submodule.injective_subtype (F.F N).toSubmodule
      exact this hc0
    rw [hc] at hcmem
    simpa using hcmem

/-- Subtraction of graded homomorphisms (the target grading is closed under subtraction). -/
def GradedHom.sub {M N : DGModule A} (f g : GradedHom M N) : GradedHom M N where
  toFun := f.toFun - g.toFun
  map_grading := by
    intro n x hx
    change f.toFun x - g.toFun x ∈ N.grading n
    exact AddSubgroup.sub_mem _ (f.map_grading n x hx) (g.map_grading n x hx)

/-- The canonical inclusion `lof j : F_j P → ⨁_i F_i P` as a graded homomorphism. -/
noncomputable def lofGraded {P : DGModule A} (F : PropertyPFiltration P) (j : ℕ) :
    GradedHom (F.F j).toDGModule (telescopeObj F) where
  toFun := DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) j
  map_grading := by
    classical
    intro n y hy i
    change (DirectSum.of (fun i => (F.F i).toDGModule.carrier) j y) i ∈ (F.F i).grading n
    rw [DirectSum.of_apply]
    by_cases hij : j = i
    · subst hij
      simp only []
      exact hy
    · rw [dite_eq_right hij]
      simp

/-- The graded left inverse `s_j : F_{j+1} P → F_j P` of the inclusion `ι_j`, from
`F.admissible j`. -/
noncomputable def telescopeRetrS {P : DGModule A} (F : PropertyPFiltration P) (j : ℕ) :
    GradedHom (F.F (j + 1)).toDGModule (F.F j).toDGModule :=
  (F.admissible j).2.choose

/-- The map `telescopeRetrS F j` is a left inverse of the inclusion `F_j P → F_{j+1} P`:
`s_j (ι_j x) = x`. -/
lemma telescopeRetrS_spec {P : DGModule A} (F : PropertyPFiltration P) (j : ℕ)
    (x : (F.F j).toDGModule.carrier) :
    (telescopeRetrS F j).toFun ((F.inclHom j).toFun x) = x :=
  (F.admissible j).2.choose_spec x

/-- The per-summand retraction maps `R_j : F_j P → ⨁_i F_i P`, defined recursively by
`R_0 = lof_0` and `R_{j+1} = (R_j − lof_j) ∘ s_j`. They satisfy the telescoping identity
`R_i − R_{i+1} ∘ ι_i = lof_i`, which yields `ρ ∘ α = id`. -/
noncomputable def telescopeRetrR {P : DGModule A} (F : PropertyPFiltration P) :
    (j : ℕ) → GradedHom (F.F j).toDGModule (telescopeObj F)
  | 0 => lofGraded F 0
  | (j + 1) => ((telescopeRetrR F j).sub (lofGraded F j)).comp (telescopeRetrS F j)

/-- **(7) `α` is an admissible monomorphism.**
We must produce a graded `A`-module retraction `ρ : G → G` with `ρ ∘ α = id` (injectivity is
(4)).  By `F.admissible i`, each inclusion `ι_i : F_i P → F_{i+1}P` has a graded left inverse
`s_i : F_{i+1}P → F_i P` (`s_i ∘ ι_i = id`).  Compose: for `j > i` set
`s_{j,i} := s_i ∘ s_{i+1} ∘ … ∘ s_{j-1} : F_j P → F_i P`, with `s_{j,j} = id`.  Define the graded
map `ρ` by `ρ (lof j x) = Σ_{i ≤ j} lof i (s_{j,i} x)` (a finite sum, landing in `⨁_{i≤j} F_i P`).
Each `s_{j,i}` is a graded `Aᵐᵒᵖ`-linear map (composite of the graded `s_i`), and `lof i` is
graded, so `ρ` is a `GradedHom`.  Check `ρ ∘ α = id`: on summand `i`,
`ρ(α(lof i x)) = ρ(lof i x) − ρ(lof (i+1)(ι_i x))`
`= Σ_{k≤i} lof k (s_{i,k} x) − Σ_{k≤i+1} lof k (s_{i+1,k}(ι_i x))`.
Using `s_{i+1,k}(ι_i x) = s_{i,k}(s_i(ι_i x)) = s_{i,k} x` for `k ≤ i` and
`s_{i+1,i+1}(ι_i x) = ι_i x`-term cancels appropriately, the two sums telescope to leave exactly
`lof i x`.  (Equivalently: `ρ` is the graded splitting induced by the complements `C_i := ker s_i`,
giving `F_q P = ι(F_0 P) ⊕ C_0 ⊕ … ⊕ C_{q-1}`.)  Hence `IsAdmissibleMono α`. -/
theorem telescopeAlpha_admissibleMono {P : DGModule A}
    (F : PropertyPFiltration P) (α : Hom (telescopeObj F) (telescopeObj F))
    (hα : α.toFun = telescopeAlphaFun F) : IsAdmissibleMono α := by
  classical
  refine ⟨?_, ?_⟩
  · -- injectivity
    rw [hα]; exact telescopeAlphaFun_injective F
  · -- the graded retraction ρ
    -- the underlying linear map of ρ
    set ρFun : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
      DirectSum.toModule (A.carrier)ᵐᵒᵖ ℕ _ (fun j => (telescopeRetrR F j).toFun) with hρFun
    -- ρ on a generator
    have rho_of : ∀ j (a : (F.F j).toDGModule.carrier),
        ρFun ((DirectSum.of (fun i => (F.F i).toDGModule.carrier) j) a)
          = (telescopeRetrR F j).toFun a :=
      fun j a => DirectSum.toModule_lof (A.carrier)ᵐᵒᵖ
        (M := fun i => (F.F i).toDGModule.carrier) j a
    have rho_lof : ∀ j (a : (F.F j).toDGModule.carrier),
        ρFun ((DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toDGModule.carrier) j) a)
          = (telescopeRetrR F j).toFun a :=
      fun j a => DirectSum.toModule_lof (A.carrier)ᵐᵒᵖ
        (M := fun i => (F.F i).toDGModule.carrier) j a
    -- recursion equation for telescopeRetrR
    have retrR_succ : ∀ j (y : (F.F (j + 1)).toDGModule.carrier),
        (telescopeRetrR F (j + 1)).toFun y
          = (telescopeRetrR F j).toFun ((telescopeRetrS F j).toFun y)
            - (lofGraded F j).toFun ((telescopeRetrS F j).toFun y) :=
      fun _ _ => rfl
    -- ρ is grading-preserving
    have rho_grading := telescope_map_grading F ρFun fun n i a ha => by
      rw [rho_of]
      exact (telescopeRetrR F i).map_grading n _ ha
    -- assemble ρ as a graded hom
    refine ⟨{ toFun := ρFun, map_grading := rho_grading }, ?_⟩
    -- ρ ∘ α = id
    intro x
    rw [hα]
    change ρFun (telescopeAlphaFun F x) = x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeAlphaFun_of, map_sub, rho_lof, rho_lof, retrR_succ, telescopeRetrS_spec]
        change (telescopeRetrR F i).toFun a
            - ((telescopeRetrR F i).toFun a - (lofGraded F i).toFun a)
          = (DirectSum.of (fun i => (F.F i).toDGModule.carrier) i) a
        rw [sub_sub_cancel]
        rfl
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb]

/-- **(8) `β` is an admissible epimorphism.**
We must produce a graded `A`-module section `σ : P → G` with `β ∘ σ = id` (surjectivity is (5)).
Using the graded complements `C_i := ker s_i` from `F.admissible` (left inverses `s_i` of `ι_i`),
every `p ∈ P` (which lies in some `F_q P` by `F.exhaustive`) has a unique finite graded expansion
`p = (incl c_{-1}) + (incl c_0) + … ` with `c_{-1} ∈ F_0 P`, `c_m ∈ C_m ⊆ F_{m+1}P`, only finitely
many nonzero.  Define `σ(p) := lof 0 c_{-1} + Σ_m lof (m+1) c_m ∈ G`.  This is graded and
`Aᵐᵒᵖ`-linear (it is the inverse of the graded iso `G/range α ≅ P` precomposed with a graded
splitting), and `β(σ p) = (incl c_{-1}) + Σ_m (incl c_m) = p`, so `β ∘ σ = id`.  Hence
`IsAdmissibleEpi β`.  (Concretely `σ` may be built as `(id − α ∘ ρ')` transported through the
splitting, where `ρ'` realises the partial-sum retraction; the key input is the family of graded
complements supplied by `F.admissible`.) -/
theorem telescopeBeta_admissibleEpi {P : DGModule A}
    (F : PropertyPFiltration P) (β : Hom (telescopeObj F) P)
    (hβ : β.toFun = telescopeBetaFun F) : IsAdmissibleEpi β := by
  -- SANITY CHECK PASSED
  classical
  refine ⟨by rw [hβ]; exact telescopeBetaFun_surjective F, ?_⟩
  -- Obtain α and its graded retraction ρ (ρ ∘ α = id), from lemma (7).
  obtain ⟨α, hα⟩ := exists_telescopeAlpha F
  obtain ⟨-, ρ, hρ⟩ := telescopeAlpha_admissibleMono F α hα
  -- Abbreviations for the underlying linear maps.
  set bf : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] P.carrier := telescopeBetaFun F with hbf
  set af : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
    α.toFun with haf
  set ρf : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
    ρ.toFun with hρf
  have hρα : ∀ x, ρf (af x) = x := hρ
  -- Easy direction of exactness: `β ∘ α = 0`.
  have hβα : ∀ x, bf (af x) = 0 := by
    intro x
    rw [hbf, hα]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        rw [telescopeAlphaFun_of, map_sub, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
          telescopeBetaFun_of, telescopeBetaFun_of, F.inclHom_apply i a, sub_self]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  -- The hard kernel-intersection fact: `ker β ∩ ker ρ = 0`.
  -- This follows from exactness (`range α = ker β`) together with `ρ ∘ α = id`:
  -- if `β g = 0` then `g = α z` for some `z`, and `0 = ρ g = ρ (α z) = z`, so `g = α 0 = 0`.
  have hexact : LinearMap.range (telescopeAlphaFun F) = LinearMap.ker (telescopeBetaFun F) :=
    telescope_exact F
  have hker : ∀ g, ρf g = 0 → bf g = 0 → g = 0 := by
    intro g hρg hbg
    have hmem : g ∈ LinearMap.ker (telescopeBetaFun F) := by
      simp only [LinearMap.mem_ker]
      rw [← hbf]; exact hbg
    rw [← hexact] at hmem
    obtain ⟨z, hz⟩ := hmem
    -- hz : telescopeAlphaFun F z = g
    have hzaf : af z = g := by rw [hα]; exact hz
    have : z = 0 := by rw [← hρα z, hzaf, hρg]
    rw [← hzaf, this, map_zero]
  -- `φ := id - α ∘ ρ` lands in `ker ρ` and is a graded right inverse of β on the nose.
  set φ : (telescopeObj F).carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
    LinearMap.id - af ∘ₗ ρf with hφ
  have hρφ : ∀ g, ρf (φ g) = 0 := by
    intro g
    change ρf (g - af (ρf g)) = 0
    rw [map_sub, hρα, sub_self]
  have hβφ : ∀ g, bf (φ g) = bf g := by
    intro g
    change bf (g - af (ρf g)) = bf g
    rw [map_sub, hβα, sub_zero]
  -- The kernel submodule of ρ.
  set Kρ : Submodule (A.carrier)ᵐᵒᵖ (telescopeObj F).carrier := LinearMap.ker ρf with hKρ
  -- β restricted to ker ρ.
  set bfK : Kρ →ₗ[(A.carrier)ᵐᵒᵖ] P.carrier := bf.comp Kρ.subtype with hbfK
  have hbfK_apply : ∀ g : Kρ, bfK g = bf (g : (telescopeObj F).carrier) := fun _ => rfl
  -- Surjective.
  have hbfK_surj : Function.Surjective bfK := by
    intro y
    obtain ⟨g, hg⟩ := telescopeBetaFun_surjective F y
    refine ⟨⟨φ g, hρφ g⟩, ?_⟩
    rw [hbfK_apply]
    change bf (φ g) = y
    rw [hβφ, hbf, hg]
  -- Injective (uses the hard fact).
  have hbfK_inj : Function.Injective bfK := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have hg0 : bf (g : (telescopeObj F).carrier) = 0 := by rw [← hbfK_apply]; exact hg
    have hgρ : ρf (g : (telescopeObj F).carrier) = 0 := g.2
    exact Subtype.ext (hker _ hgρ hg0)
  -- The graded section: invert β on ker ρ.
  set e : Kρ ≃ₗ[(A.carrier)ᵐᵒᵖ] P.carrier :=
    LinearEquiv.ofBijective bfK ⟨hbfK_inj, hbfK_surj⟩ with he
  set sLin : P.carrier →ₗ[(A.carrier)ᵐᵒᵖ] (telescopeObj F).carrier :=
    Kρ.subtype.comp (e.symm.toLinearMap) with hsLin
  -- β ∘ s = id.
  have hsec : ∀ y, bf (sLin y) = y := by
    intro y
    change bf ((e.symm y : (telescopeObj F).carrier)) = y
    have : bfK (e.symm y) = y := e.apply_symm_apply y
    rw [hbfK_apply] at this
    exact this
  -- s is graded.
  have hsgr : ∀ (n : ℤ) (y : P.carrier), y ∈ P.grading n → sLin y ∈ (telescopeObj F).grading n := by
    intro n y hy
    -- Pick a homogeneous preimage g of y in G; then φ g is the section value.
    obtain ⟨g, hg, hgmem⟩ : ∃ g, bf g = y ∧ g ∈ (telescopeObj F).grading n := by
      -- y lies in some F_q P, homogeneously.
      obtain ⟨q, hq⟩ := F.exhaustive y
      refine ⟨DirectSum.lof (A.carrier)ᵐᵒᵖ ℕ (fun i => (F.F i).toSubmodule) q ⟨y, hq⟩, ?_, ?_⟩
      · show bf _ = y
        rw [hbf]
        exact telescopeBetaFun_of F q ⟨y, hq⟩
      · exact (lofGraded F q).map_grading n ⟨y, hq⟩ hy
    -- φ g is homogeneous of degree n, in ker ρ, with β (φ g) = y.
    have hφg_mem : φ g ∈ (telescopeObj F).grading n := by
      change g - af (ρf g) ∈ (telescopeObj F).grading n
      refine AddSubgroup.sub_mem _ hgmem ?_
      have : ρf g ∈ (telescopeObj F).grading n := ρ.map_grading n g hgmem
      exact α.map_grading n (ρf g) this
    -- s y = φ g by uniqueness.
    have hsy : sLin y = φ g := by
      have h1 : bfK ⟨φ g, hρφ g⟩ = y := by
        rw [hbfK_apply]; change bf (φ g) = y; rw [hβφ, hg]
      have h2 : e ⟨φ g, hρφ g⟩ = y := h1
      have h3 : e.symm y = ⟨φ g, hρφ g⟩ := by
        rw [← h2, e.symm_apply_apply]
      change (e.symm y : (telescopeObj F).carrier) = φ g
      rw [h3]
    rw [hsy]; exact hφg_mem
  exact ⟨⟨sLin, hsgr⟩, by rw [hβ]; exact hsec⟩

/-- **Stacks Tag 09KL (Lemma 22.20.1).**
Let `(A, d)` be a *lawful* differential graded algebra, `P` a lawful differential graded
`A`-module, and `F_*` a filtration as in property (P) (Definition 3, with all its
gradedness/lawfulness/quotient conditions bundled into `PropertyPFiltration`).  Then the
telescope object `⨁_{i ≥ 0} F_i P` is itself a lawful differential graded `A`-module, and
there exist DG homomorphisms `α` and `β` whose underlying linear maps are the explicit
telescoping maps `telescopeAlphaFun F` and `telescopeBetaFun F`, fitting into an admissible
short exact sequence of differential graded `A`-modules
`0 → ⨁_{i ≥ 0} F_i P →[α] ⨁_{i ≥ 0} F_i P →[β] P → 0`.

In particular this asserts items (1)–(5) of the Main Statement: the source/target object
lives in the category `Mod_(A,d)` (it is lawful), `α, β` are DG homomorphisms with the
prescribed underlying maps, `α` is injective, `β` is surjective, `range α = ker β`, and the
sequence is admissible.

Proof: assemble the eight sub-lemmas above.  Lawfulness is `telescopeObj_isLawful`; obtain
`α, β` from `exists_telescopeAlpha`/`exists_telescopeBeta` with `α.toFun = telescopeAlphaFun F`
and `β.toFun = telescopeBetaFun F`; the `AdmissibleSES` fields are then
`telescopeAlphaFun_injective`,
`telescopeBetaFun_surjective`, `telescope_exact`, `telescopeAlpha_admissibleMono`, and
`telescopeBeta_admissibleEpi`, with the underlying-map equalities `hα`, `hβ` used to rewrite
`α.toFun`/`β.toFun` to the explicit telescope maps. -/
@[stacks 09KL]
theorem admissible_ses_of_propertyP
    {P : DGModule A} (hP : P.IsLawful)
    (F : PropertyPFiltration P) :
    (telescopeObj F).IsLawful ∧
    ∃ (α : Hom (telescopeObj F) (telescopeObj F)) (β : Hom (telescopeObj F) P),
      α.toFun = telescopeAlphaFun F ∧
      β.toFun = telescopeBetaFun F ∧
      AdmissibleSES α β := by
  refine ⟨telescopeObj_isLawful hP F, ?_⟩
  obtain ⟨α, hα⟩ := exists_telescopeAlpha F
  obtain ⟨β, hβ⟩ := exists_telescopeBeta F
  refine ⟨α, β, hα, hβ, ?_⟩
  refine
    { injective := ?_
      surjective := ?_
      exact := ?_
      admissibleMono := telescopeAlpha_admissibleMono F α hα
      admissibleEpi := telescopeBeta_admissibleEpi F β hβ }
  · rw [hα]; exact telescopeAlphaFun_injective F
  · rw [hβ]; exact telescopeBetaFun_surjective F
  · rw [hα, hβ]; exact telescope_exact F
end DGModule

end Stacks.DifferentialGraded
