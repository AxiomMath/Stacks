module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradeOne
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.MixedDegreePolynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.NoetherianCycles

/-!
# The homogeneous pieces are finite modules over the coefficient algebra

A graded divided-power polynomial algebra with finitely many variables in each degree has each
homogeneous piece *finitely generated over its coefficient algebra*. This is not the freeness
over the base ring that `free_grade_of_finite_indices` supplies: that is a statement about
infinitely many basis elements over `R`, and it does not bound the number of generators over the
coefficients.

The coefficients sit in degree zero, hence are central, so they act on the algebra; each
homogeneous piece and each finite variable stage is stable under that action. Adjoining one
variable of degree `d` multiplies the degree-`m` piece of a stage by the divided powers of that
variable, of which only those with `n * d ≤ m` contribute — finitely many, since `d` is
positive. So one variable enlarges a finitely generated piece to a finitely generated piece, and
a finite set of variables keeps it finitely generated. Finally the degree-`m` piece of the whole
algebra is the degree-`m` piece of the stage on the variables of degree at most `m`, which is a
finite set when each degree contributes finitely many variables.

## Main definitions

* `DividedPowers.TateResolution.mulRightLinearMap` — right multiplication, as a map of
  coefficient modules.
* `DividedPowers.TateResolution.coefficientSubmodule` — an `R`-submodule stable under the
  coefficients, as a module over them.
* `DividedPowers.TateResolution.gradeStageModule` and
  `DividedPowers.TateResolution.gradeModule` — the degree-`m` piece of a finite variable stage,
  and of the whole algebra, as modules over the coefficient algebra.

## Main results

* `DividedPowers.TateResolution.gradeStageModule_eq_sup_of_decomposition` and
  `DividedPowers.TateResolution.exists_insert_gradeStageModule_eq` — adjoining one variable
  enlarges a homogeneous piece of a stage to a finite join of images of pieces of that stage.
* `DividedPowers.TateResolution.fg_gradeStageModule` — the degree-`m` piece of a finite variable
  stage is finitely generated over the coefficient algebra.
* `DividedPowers.TateResolution.fg_gradeModule` — the degree-`m` piece of the whole algebra is
  finitely generated over the coefficient algebra when each degree contributes finitely many
  variables.
* `DividedPowers.TateResolution.fg_of_le_gradeModule` — hence, over a Noetherian coefficient
  algebra, every module of coefficients inside a homogeneous piece is finitely generated.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

attribute [local implicit_reducible] TwistedModule

section MulRight

variable {P : Type v} {A : Type w} [CommRing P] [Ring A] [Algebra P A]

/-- Right multiplication by a fixed element, as a map of modules over a commutative ring acting
through its structure map. It is linear because the structure map lands in the centre. -/
public def mulRightLinearMap (c : A) : A →ₗ[P] A where
  toFun x := x * c
  map_add' x y := add_mul x y c
  map_smul' p x := by
    change (p • x) * c = p • (x * c)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]

/-- `mulRightLinearMap c` sends `x` to `x * c`. -/
@[simp] public theorem mulRightLinearMap_apply (c x : A) :
    mulRightLinearMap (P := P) c x = x * c := rfl

/-- A finite join of finitely generated modules is finitely generated. -/
public theorem fg_finsetSup {M : Type w} [AddCommGroup M] [Module P M] (s : Finset ℕ)
    (N : ℕ → Submodule P M) (hN : ∀ n ∈ s, (N n).FG) :
    (s.sup N).FG := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Submodule.fg_bot
  | insert n t hn ih =>
      rw [Finset.sup_insert]
      exact (hN n (Finset.mem_insert_self n t)).sup
        (ih fun k hk => hN k (Finset.mem_insert_of_mem hk))

end MulRight

section Submod

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Algebra R P] [Ring A] [Algebra R A] [Algebra P A]
  (ι : P →ₐ[R] A) (hPA : ∀ p : P, algebraMap P A p = ι p)

/-- An `R`-submodule stable under multiplication by the coefficients, as a module over the
coefficient algebra. The carrier is unchanged, so every inclusion proved for the `R`-submodule
transfers. -/
public def coefficientSubmodule (N : Submodule R A)
    (hN : ∀ (p : P) (x : A), x ∈ N → ι p * x ∈ N) : Submodule P A where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' p x hx := by
    rw [Algebra.smul_def, hPA]
    exact hN p x hx

/-- Membership in `coefficientSubmodule ι hPA N hN` is membership in `N`. -/
@[simp] public theorem mem_coefficientSubmodule (N : Submodule R A)
    (hN : ∀ (p : P) (x : A), x ∈ N → ι p * x ∈ N) (x : A) :
    x ∈ coefficientSubmodule ι hPA N hN ↔ x ∈ N := Iff.rfl

end Submod


section Stage

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [CommRing P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}
  (h : GradedDividedPowerPolynomial 𝒜 γ ι)
  [Algebra P A] (hPA : ∀ p : P, algebraMap P A p = ι p)

/-- **The degree-`m` piece of a finite variable stage, as a module over the coefficient
algebra.** A coefficient has degree zero and lies in every stage, so both halves of the
intersection are stable under multiplying by it. -/
public def gradeStageModule (m : ℕ) (S : Finset (Σ n : ℕ, h.indices n)) : Submodule P A :=
  coefficientSubmodule ι hPA (𝒜 m ⊓ finiteVariableStageSubmodule γ ι h.generator S)
    fun p x hx => ⟨by simpa using SetLike.mul_mem_graded (h.coefficient_mem p) hx.1,
      Subring.mul_mem _ (coefficient_mem_finiteVariableStage γ ι h.generator S p) hx.2⟩

/-- An element lies in `gradeStageModule h hPA m S` if and only if it is homogeneous of degree `m`
and lies in the finite variable stage on `S`. -/
@[simp] public theorem mem_gradeStageModule (m : ℕ) (S : Finset (Σ n : ℕ, h.indices n)) (x : A) :
    x ∈ gradeStageModule h hPA m S ↔
      x ∈ 𝒜 m ∧ x ∈ finiteVariableStage γ ι h.generator S := Iff.rfl

/-- **The degree-`m` piece of the whole algebra, as a module over the coefficient algebra.** -/
public def gradeModule (m : ℕ) : Submodule P A :=
  coefficientSubmodule ι hPA (𝒜 m)
    fun p x hx => by simpa using SetLike.mul_mem_graded (h.coefficient_mem p) hx

/-- An element lies in `gradeModule h hPA m` if and only if it is homogeneous of degree `m`. -/
@[simp] public theorem mem_gradeModule (m : ℕ) (x : A) :
    x ∈ gradeModule h hPA m ↔ x ∈ 𝒜 m := Iff.rfl


/-- **The one-variable step.** If every element of the degree-`m` piece of the larger stage is a
sum of multiples of the fixed elements `c n` by elements of the degree-`(m - n * d)` pieces of the
smaller stage, and each `c n` is homogeneous of degree `n * d` and lies in the larger stage, then
the degree-`m` piece of the larger stage is the join of finitely many images of pieces of the
smaller one. -/
public theorem gradeStageModule_eq_sup_of_decomposition
    (S U : Finset (Σ n : ℕ, h.indices n)) (d : ℕ) (hd : 0 < d) (hSU : S ⊆ U) (c : ℕ → A)
    (hcmem : ∀ n, c n ∈ 𝒜 (n * d))
    (hcU : ∀ n, c n ∈ finiteVariableStage γ ι h.generator U)
    (hdecomp : ∀ (m : ℕ) (x : A), x ∈ 𝒜 m →
      x ∈ finiteVariableStage γ ι h.generator U →
      ∃ (s : Finset ℕ) (b : ℕ → A), (∀ n ∈ s, n * d ≤ m) ∧
        (∀ n ∈ s, b n ∈ 𝒜 (m - n * d) ∧
          b n ∈ finiteVariableStage γ ι h.generator S) ∧
        x = ∑ n ∈ s, b n * c n)
    (m : ℕ) :
    gradeStageModule h hPA m U =
      ((Finset.range (m + 1)).filter fun n => n * d ≤ m).sup
        fun n => Submodule.map (mulRightLinearMap (c n))
          (gradeStageModule h hPA (m - n * d) S) := by
  refine le_antisymm (fun x hx => ?_) (Finset.sup_le fun n hn => ?_)
  · obtain ⟨s, b, hs, hb, hxsum⟩ := hdecomp m x hx.1 hx.2
    rw [hxsum]
    refine Submodule.sum_mem _ fun n hn => ?_
    have hnd : n * d ≤ m := hs n hn
    have hnm : n ≤ m := le_trans (Nat.le_mul_of_pos_right n hd) hnd
    have hmem : n ∈ (Finset.range (m + 1)).filter (fun k => k * d ≤ m) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnm), hnd⟩
    have hle := Finset.le_sup (f := fun k => Submodule.map (mulRightLinearMap (c k))
        (gradeStageModule h hPA (m - k * d) S)) hmem
    exact hle ⟨b n, hb n hn, rfl⟩
  · obtain ⟨hnr, hnd⟩ := Finset.mem_filter.mp hn
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    refine ⟨?_, Subring.mul_mem _
      (finiteVariableStage_le_of_subset γ ι h.generator hSU hy.2) (hcU n)⟩
    have hmul := SetLike.mul_mem_graded hy.1 (hcmem n)
    rwa [show m - n * d + n * d = m by omega] at hmul

/-- **Adjoining one variable to a finite variable stage, as a finite join.** There are fixed
elements `c n`, homogeneous of degree `n * d` for `d` the degree of the new variable, such that
every homogeneous piece of the enlarged stage is the join of the images of pieces of the old
stage under multiplication by them.

In odd degree only `c 0 = 1` and `c 1`, the variable itself, are nonzero, since the square of an
odd variable vanishes; in even degree `c n` is the `n`-th divided power of the variable. Below
the degree of the variable the enlarged stage contributes nothing new, which is
`inf_finiteVariableStageSubmodule_insert_le`, and that case is common to both parities. -/
public theorem exists_insert_gradeStageModule_eq
    (S : Finset (Σ n : ℕ, h.indices n)) (j : Σ n : ℕ, h.indices n) (hj : j ∉ S)
    (U : Finset (Σ n : ℕ, h.indices n)) (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S) :
    ∃ c : ℕ → A, ∀ m : ℕ,
      gradeStageModule h hPA m U =
        ((Finset.range (m + 1)).filter fun n => n * (j.1 + 1) ≤ m).sup
          fun n => Submodule.map (mulRightLinearMap (c n))
            (gradeStageModule h hPA (m - n * (j.1 + 1)) S) := by
  classical
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, -, hoddBr, hevenBr⟩ := h.successor S j hj
  let instJ : DecidableEq ((n : ℕ) × h.indices n) := Classical.decEq _
  have hUeq : (insert j S : Finset ((n : ℕ) × h.indices n)) = U := by
    ext k
    simp [hU k]
  rw [hUeq] at hoddBr hevenBr
  let instA : Algebra R (finiteVariableStage γ ι h.generator S) := aS
  let instG : GradedAlgebra Sᵢ := gS
  let instC : IsStrictlyGradedComm Sᵢ := cS
  have hSU : S ⊆ U := fun k hk => (hU k).mpr (Or.inr hk)
  have hjU : j ∈ U := (hU j).mpr (Or.inl rfl)
  rcases Nat.even_or_odd (j.1 + 1) with heven | hodd
  · let instFact : Fact (Even (j.1 + 1)) := ⟨heven⟩
    obtain ⟨e, hcoeff, -, hgrade, -⟩ := hevenBr heven
    have hcoe : ∀ (k : ℕ) (b : finiteVariableStage γ ι h.generator S),
        b ∈ Sᵢ k → (b : A) ∈ 𝒜 k := by
      intro k b hb
      have hmon : EvenVariableAlgebra.monomial 0 b ∈
          EvenVariableAlgebra.grade Sᵢ (j.1 + 1) k := by
        rw [EvenVariableAlgebra.monomial_mem_grade_iff, ite_eq_left (by omega : 0 * (j.1 + 1) ≤ k)]
        simpa using hb
      have := (hgrade k _).mp hmon
      rwa [show EvenVariableAlgebra.monomial 0 b =
        EvenVariableAlgebra.coeffEmbedding b from rfl, hcoeff b] at this
    refine ⟨fun n => ((e (EvenVariableAlgebra.monomial n 1) :
      finiteVariableStage γ ι h.generator U) : A), fun m => ?_⟩
    refine gradeStageModule_eq_sup_of_decomposition h hPA S U (j.1 + 1) (Nat.succ_pos j.1) hSU _
      (fun n => ?_) (fun n => (e _).2) (fun m' x hx0 hxU => ?_) m
    · have hmon : EvenVariableAlgebra.monomial n (1 : finiteVariableStage γ ι h.generator S) ∈
          EvenVariableAlgebra.grade Sᵢ (j.1 + 1) (n * (j.1 + 1)) := by
        rw [EvenVariableAlgebra.monomial_mem_grade_iff, ite_eq_left (le_refl (n * (j.1 + 1))),
          Nat.sub_self]
        exact SetLike.one_mem_graded Sᵢ
      exact (hgrade (n * (j.1 + 1)) _).mp hmon
    · obtain ⟨z, hz⟩ := exists_stageRingHom_eq γ ι h.generator U e x hxU
      have hzx : ((e z : finiteVariableStage γ ι h.generator U) : A) = x := hz
      have hzg : z ∈ EvenVariableAlgebra.grade Sᵢ (j.1 + 1) m' :=
        (hgrade m' z).mpr (by rw [hzx]; exact hx0)
      rw [EvenVariableAlgebra.mem_grade_iff] at hzg
      have hle : ∀ n ∈ z.coeff.support, n * (j.1 + 1) ≤ m' := by
        intro n hn
        by_contra hcon
        have hzn := hzg n
        rw [ite_eq_right hcon, Submodule.mem_bot] at hzn
        exact (Finsupp.mem_support_iff.mp hn) hzn
      refine ⟨z.coeff.support,
        fun n => ((z.coeff n : finiteVariableStage γ ι h.generator S) : A), hle,
        fun n hn => ⟨hcoe _ _ ?_, (z.coeff n).2⟩, ?_⟩
      · have := hzg n
        rwa [ite_eq_left (hle n hn)] at this
      · rw [← hzx]
        conv_lhs => rw [← EvenVariableAlgebra.sum_monomial z]
        rw [map_sum, AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [show EvenVariableAlgebra.monomial n (z.coeff n) =
          EvenVariableAlgebra.coeffEmbedding (z.coeff n) *
            EvenVariableAlgebra.monomial n 1 from ?_, map_mul, MulMemClass.coe_mul, hcoeff]
        rw [show EvenVariableAlgebra.coeffEmbedding (z.coeff n) =
          EvenVariableAlgebra.monomial 0 (z.coeff n) from rfl,
          EvenVariableAlgebra.monomial_mul_monomial]
        simp
  · obtain ⟨e, hcoeff, hgen, hgrade, -⟩ := hoddBr hodd
    have hcoe : ∀ (k : ℕ) (b : finiteVariableStage γ ι h.generator S),
        b ∈ Sᵢ k → (b : A) ∈ 𝒜 k := by
      intro k b hb
      have := (hgrade k _).mp (OddVariableExtension.inclusion_mem_grade Sᵢ (j.1 + 1) k hb)
      rwa [hcoeff b] at this
    refine ⟨fun n => if n = 0 then (1 : A) else if n = 1 then h.generator j else 0, fun m => ?_⟩
    refine gradeStageModule_eq_sup_of_decomposition h hPA S U (j.1 + 1) (Nat.succ_pos j.1) hSU _
      (fun n => ?_) (fun n => ?_) (fun m' x hx0 hxU => ?_) m
    · match n with
      | 0 => simpa using (SetLike.one_mem_graded 𝒜 : (1 : A) ∈ 𝒜 0)
      | 1 => simpa using h.generator_mem j
      | (k + 2) => simp
    · match n with
      | 0 => simp
      | 1 => simpa using generator_mem_finiteVariableStage γ ι h.generator hjU
      | (k + 2) => simp
    · by_cases hdm : j.1 + 1 ≤ m'
      · obtain ⟨z, hz⟩ := exists_stageRingHom_eq γ ι h.generator U e x hxU
        have hzx : ((e z : finiteVariableStage γ ι h.generator U) : A) = x := hz
        have hzg : z ∈ OddVariableExtension.grade Sᵢ (j.1 + 1) m' :=
          (hgrade m' z).mpr (by rw [hzx]; exact hx0)
        obtain ⟨hzf, hzs⟩ := (OddVariableExtension.mem_grade_iff Sᵢ (j.1 + 1) m' z).mp hzg
        rw [ite_eq_left hdm] at hzs
        refine ⟨{0, 1}, fun n => if n = 0 then ((z.fst : A))
          else ((show finiteVariableStage γ ι h.generator S from z.snd : A)), ?_, ?_, ?_⟩
        · simpa using hdm
        · simpa using ⟨hcoe m' z.fst hzf, hcoe (m' - (j.1 + 1)) _ hzs⟩
        · rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), ← hzx]
          conv_lhs => rw [← OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator
            Sᵢ (j.1 + 1) z]
          rw [map_add, AddMemClass.coe_add, map_mul, MulMemClass.coe_mul, hcoeff, hcoeff, hgen]
          simp
      · refine ⟨{0}, fun _ => x, ?_, ?_, ?_⟩
        · simp
        · simp only [Finset.mem_singleton, forall_eq, Nat.zero_mul, Nat.sub_zero]
          exact inf_finiteVariableStageSubmodule_insert_le h S j hj U hU
            (by omega : m' ≤ j.1) ⟨hx0, hxU⟩
        · simp

omit [Algebra P A] [IsStrictlyGradedComm 𝒜] in
/-- A degree-zero element that is also homogeneous of nonzero degree is zero. -/
public theorem eq_zero_of_mem_grade_zero_of_mem_grade {m : ℕ} (hm : m ≠ 0) {x : A}
    (h0 : x ∈ 𝒜 0) (hmx : x ∈ 𝒜 m) : x = 0 := by
  have h1 : ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = x :=
    DirectSum.decompose_of_mem_same 𝒜 hmx
  have h2 : ((DirectSum.decompose 𝒜 x m : 𝒜 m) : A) = 0 :=
    DirectSum.decompose_of_mem_ne 𝒜 h0 (Ne.symm hm)
  rw [← h1, h2]

/-- The degree-zero piece of the initial stage is the coefficients, generated by `1`. -/
public theorem gradeStageModule_zero_empty :
    gradeStageModule h hPA 0 (∅ : Finset (Σ n : ℕ, h.indices n)) = Submodule.span P {(1 : A)} := by
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨p, hp⟩ := (mem_finiteVariableStage_empty_iff h x).mp hx.2
    rw [← hp, show ι p = p • (1 : A) by rw [Algebra.smul_def, hPA, mul_one]]
    exact Submodule.smul_mem _ p (Submodule.mem_span_singleton_self _)
  · rintro y rfl
    exact ⟨by simpa using SetLike.one_mem_graded 𝒜,
      (finiteVariableStage γ ι h.generator ∅).one_mem⟩

/-- Above degree zero the initial stage contributes nothing: its elements are coefficients,
which are homogeneous of degree zero. -/
public theorem gradeStageModule_empty_of_ne {m : ℕ} (hm : m ≠ 0) :
    gradeStageModule h hPA m (∅ : Finset (Σ n : ℕ, h.indices n)) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨p, hp⟩ := (mem_finiteVariableStage_empty_iff h x).mp hx.2
  rw [Submodule.mem_bot]
  exact eq_zero_of_mem_grade_zero_of_mem_grade hm (hp ▸ h.coefficient_mem p) hx.1

/-- **Every homogeneous piece of a finite variable stage is finitely generated over the
coefficient algebra.** The induction is on the finite set of adjoined variables, with the degree
left general because one variable relates the degree-`m` piece of the larger stage to the
degree-`(m - n * d)` pieces of the smaller one. -/
public theorem fg_gradeStageModule (S : Finset (Σ n : ℕ, h.indices n)) (m : ℕ) :
    (gradeStageModule h hPA m S).FG := by
  classical
  induction S using Finset.induction generalizing m with
  | empty =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [gradeStageModule_zero_empty h hPA]
        exact Submodule.fg_span_singleton _
      · rw [gradeStageModule_empty_of_ne h hPA (by omega : m ≠ 0)]
        exact Submodule.fg_bot
  | insert j T hj ih =>
      obtain ⟨c, hc⟩ := exists_insert_gradeStageModule_eq h hPA T j hj _
        (fun _ => Finset.mem_insert)
      rw [hc m]
      exact fg_finsetSup _ _ fun n _ => (ih (m := m - n * (j.1 + 1))).map _

/-- **Every homogeneous piece of a graded divided-power polynomial algebra with finitely many
variables in each degree is finitely generated over its coefficient algebra.**

Only the variables of degree at most `m` contribute to degree `m`, by
`inf_finiteVariableStageSubmodule_le_filter`, and there are finitely many of those. -/
public theorem fg_gradeModule (hfin : ∀ n : ℕ, Finite (h.indices n)) (m : ℕ) :
    (gradeModule h hPA m).FG := by
  classical
  let _ : ∀ n : ℕ, Fintype (h.indices n) := fun n => @Fintype.ofFinite _ (hfin n)
  let Sk : Finset (Σ n : ℕ, h.indices n) :=
    (Finset.range m).biUnion fun n =>
      Finset.univ.map ⟨fun i => ⟨n, i⟩, fun a b hab => by simpa using hab⟩
  have hSk : ∀ j : Σ n : ℕ, h.indices n, j.1 < m → j ∈ Sk := fun j hj =>
    Finset.mem_biUnion.mpr ⟨j.1, Finset.mem_range.mpr hj,
      Finset.mem_map.mpr ⟨j.2, Finset.mem_univ _, rfl⟩⟩
  have heq : gradeModule h hPA m = gradeStageModule h hPA m Sk := by
    refine le_antisymm (fun x hx => ⟨hx, ?_⟩) (fun x hx => hx.1)
    obtain ⟨S, hS⟩ := h.finite_support x
    have hfil := inf_finiteVariableStageSubmodule_le_filter h m S ⟨hx, hS⟩
    exact finiteVariableStage_le_of_subset γ ι h.generator
      (fun k hk => hSk k (Finset.mem_filter.mp hk).2) hfil.2
  rw [heq]
  exact fg_gradeStageModule h hPA Sk m

/-- **Every module of the coefficient algebra inside a homogeneous piece is finitely generated,
when the coefficient algebra is Noetherian and each degree contributes finitely many
variables.** -/
public theorem fg_of_le_gradeModule [IsNoetherianRing P] (hfin : ∀ n : ℕ, Finite (h.indices n))
    (m : ℕ) (N : Submodule P A) (hN : N ≤ gradeModule h hPA m) :
    N.FG := by
  have _ : IsNoetherian P (gradeModule h hPA m) :=
    isNoetherian_of_fg_of_noetherian _ (fg_gradeModule h hPA hfin m)
  have hcomap := IsNoetherian.noetherian (N.comap (gradeModule h hPA m).subtype)
  have hmap := hcomap.map (gradeModule h hPA m).subtype
  rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hN] at hmap

end Stage

end DividedPowers.TateResolution

end
