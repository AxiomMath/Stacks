module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable

/-!
# Freeness of the homogeneous pieces of a one-variable extension

A Tate resolution is required to be free over the base ring in every degree. This file supplies
the base case and the two induction steps of that requirement for the tower of one-variable
extensions: the degree-zero algebra, the odd (exterior) extension, and the even (divided-power)
extension.

The two extensions have explicitly described homogeneous pieces, and the descriptions are what
the proofs use. For an odd variable of degree `d` the degree-`m` piece is `A_m ⊕ A_{m-d} T`, a
product of two homogeneous pieces of the coefficient algebra, with the second one replaced by
zero below degree `d`. For an even variable of degree `d > 0` the degree-`m` piece is
`A_m ⊕ A_{m-d} T ⊕ A_{m-2d} T⁽²⁾ ⊕ ⋯`, and positivity of `d` makes that sum finite: the
coefficient of `T⁽ⁿ⁾` is forced to vanish as soon as `n > m / d`. In both cases the piece is a
finite product of homogeneous pieces of the coefficient algebra, hence free whenever those are.

## Main definitions

* `DividedPowers.TateResolution.OddVariableExtension.gradeLinearEquiv` — the degree-`m` piece of
  an odd-variable extension as the product of `A_m` with the shifted piece carried by the
  variable.
* `DividedPowers.TateResolution.EvenVariableAlgebra.gradeLinearEquiv` — the degree-`m` piece of an
  even-variable extension of positive degree as the finite product of the pieces carried by the
  divided powers of the variable.

## Main results

* `DividedPowers.TateResolution.free_degreeZeroGrade` — every piece of the degree-zero grading is
  free as soon as the algebra is.
* `DividedPowers.TateResolution.OddVariableExtension.free_grade` and
  `DividedPowers.TateResolution.EvenVariableAlgebra.free_grade` — each homogeneous piece of a
  one-variable extension is free over the base ring when every homogeneous piece of the
  coefficient algebra is.
* `DividedPowers.TateResolution.free_grade_of_ringEquiv` — freeness of a homogeneous piece
  transfers along a grading-detecting ring equivalence that fixes the base ring, which is the
  shape in which the successor stages of the tower are presented.
* `DividedPowers.TateResolution.free_of_directed_bases` — a module exhausted by a directed family
  of submodules carrying increasing bases is free.

## Implementation notes

Freeness of the coefficient pieces is taken as an explicit hypothesis `∀ k, Module.Free R (Aᵢ k)`
rather than as an instance binder, because the index `k` at which it is used is computed from the
degree (`m - n * d`) and an instance binder over all `k` would be seated at the wrong index by
unification. Where Mathlib's product instances are needed the hypothesis is reseated as a named
local hypothesis, which instance search then picks up.

The coefficient module of the odd variable is the type synonym `TwistedModule`, whose `R`-module
structure is the one of the coefficient algebra, so a homogeneous piece of the coefficient algebra
and the submodule of `TwistedModule` spelled by the same term have the same subtype. Freeness is
transferred between them by `exact`, which checks the two module instances definitionally rather
than searching.

The even-variable index set is `Fin (m / d + 1)`, which needs `0 < d`: at `d = 0` the degree-`m`
piece is the whole extension and is a countable, not finite, product of copies of `A_m`. That is
not a restriction here, since a Tate resolution adjoins variables in positive degrees only.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 09PI](https://stacks.math.columbia.edu/tag/09PI)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section DegreeZero

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- Every homogeneous piece of the grading concentrated in degree zero is free over the base ring
as soon as the algebra itself is: the degree-zero piece is everything and the others vanish. -/
public theorem free_degreeZeroGrade [Module.Free R A] (n : ℕ) :
    Module.Free R (degreeZeroGrade R A n) := by
  match n with
  | 0 => exact Module.Free.of_equiv (Submodule.topEquiv (R := R) (M := A)).symm
  | n + 1 =>
      rw [degreeZeroGrade_succ]
      infer_instance

end DegreeZero

section Odd

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace OddVariableExtension

/-- The degree-`m` piece of an odd-variable extension splits as the coefficient piece in degree
`m` together with the piece carried by the variable. -/
public def gradeLinearEquiv (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d m : ℕ) :
    grade Aᵢ d m ≃ₗ[R] Aᵢ m × shiftedGrade Aᵢ d m where
  toFun x :=
    (⟨x.1.fst, ((mem_grade_iff Aᵢ d m x.1).mp x.2).1⟩,
      ⟨x.1.snd, ((mem_grade_iff Aᵢ d m x.1).mp x.2).2⟩)
  invFun p :=
    ⟨TrivSqZeroExt.inl (p.1 : A) +
        TrivSqZeroExt.inr (p.2 : TwistedModule Aᵢ d),
      by
        refine ⟨?_, ?_⟩
        · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
            add_zero]
          exact p.1.property
        · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
            zero_add]
          exact p.2.property⟩
  left_inv x := Subtype.ext (TrivSqZeroExt.inl_fst_add_inr_snd_eq x.1)
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add]
  map_add' x y := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact TrivSqZeroExt.fst_add x.1 y.1
    · exact TrivSqZeroExt.snd_add x.1 y.1
  map_smul' r x := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact TrivSqZeroExt.fst_smul r x.1
    · exact TrivSqZeroExt.snd_smul r x.1

/-- The piece carried by the odd variable is free over the base ring: it is a shifted coefficient
piece in degrees at least `d`, and zero below. -/
public theorem free_shiftedGrade (Aᵢ : ℕ → Submodule R A)
    (hfree : ∀ k, Module.Free R (Aᵢ k)) (d m : ℕ) :
    Module.Free R (shiftedGrade Aᵢ d m) := by
  by_cases hdm : d ≤ m
  · have h : shiftedGrade Aᵢ d m = Aᵢ (m - d) := ite_eq_left hdm
    rw [h]
    exact hfree (m - d)
  · have h : shiftedGrade Aᵢ d m = ⊥ := ite_eq_right hdm
    rw [h]
    infer_instance

/-- Each homogeneous piece of an odd-variable extension is free over the base ring when every
homogeneous piece of the coefficient algebra is. -/
public theorem free_grade (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (hfree : ∀ k, Module.Free R (Aᵢ k)) (d m : ℕ) :
    Module.Free R (grade Aᵢ d m) := by
  have hm := hfree m
  have hs := free_shiftedGrade Aᵢ hfree d m
  exact Module.Free.of_equiv (gradeLinearEquiv Aᵢ d m).symm

end OddVariableExtension

end Odd

section Even

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace EvenVariableAlgebra

/-- A coefficient of a homogeneous element lies in the shifted coefficient piece whenever the
shift is available. -/
public theorem coeff_mem_of_mem_grade {𝒜 : ℕ → Submodule R A} {d m : ℕ}
    {x : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d m) {n : ℕ} (hn : n * d ≤ m) :
    x.coeff n ∈ 𝒜 (m - n * d) := by
  simpa [hn] using (mem_grade_iff 𝒜 d m x).mp hx n

/-- A coefficient of a homogeneous element vanishes once the shift is unavailable. -/
public theorem coeff_eq_zero_of_mem_grade {𝒜 : ℕ → Submodule R A} {d m : ℕ}
    {x : EvenVariableAlgebra A} (hx : x ∈ grade 𝒜 d m) {n : ℕ} (hn : ¬ n * d ≤ m) :
    x.coeff n = 0 := by
  simpa [hn] using (mem_grade_iff 𝒜 d m x).mp hx n

/-- For a variable of positive degree the coefficient of `T⁽ⁿ⁾` in a degree-`m` element can be
nonzero only for `n ≤ m / d`. -/
public theorem mul_le_iff_lt_div_succ {d m : ℕ} (hd : 0 < d) (n : ℕ) :
    n * d ≤ m ↔ n < m / d + 1 := by
  rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]

/-- The degree-`m` piece of an even-variable extension of positive degree `d` is the product of
the coefficient pieces `A_{m - n d}` for `n ≤ m / d`, one for each divided power `T⁽ⁿ⁾` of the
variable that can appear. -/
public noncomputable def gradeLinearEquiv (𝒜 : ℕ → Submodule R A) {d : ℕ} (hd : 0 < d) (m : ℕ) :
    grade 𝒜 d m ≃ₗ[R] ((n : Fin (m / d + 1)) → 𝒜 (m - (n : ℕ) * d)) where
  toFun x n :=
    ⟨x.1.coeff n, coeff_mem_of_mem_grade x.2 ((mul_le_iff_lt_div_succ hd n).mpr n.isLt)⟩
  invFun f :=
    ⟨⟨Finsupp.onFinset (Finset.range (m / d + 1))
        (fun n => if h : n < m / d + 1 then ((f ⟨n, h⟩ : A)) else 0)
        (by
          intro n hn
          rw [Finset.mem_range]
          by_contra h
          rw [dite_eq_right h] at hn
          exact hn rfl)⟩,
      by
        rw [mem_grade_iff]
        intro n
        by_cases hn : n * d ≤ m
        · have hlt : n < m / d + 1 := (mul_le_iff_lt_div_succ hd n).mp hn
          rw [ite_eq_left hn]
          change (if h : n < m / d + 1 then ((f ⟨n, h⟩ : A)) else 0) ∈ _
          rw [dite_eq_left hlt]
          exact (f ⟨n, hlt⟩).property
        · have hlt : ¬ n < m / d + 1 := fun h => hn ((mul_le_iff_lt_div_succ hd n).mpr h)
          rw [ite_eq_right hn]
          change (if h : n < m / d + 1 then ((f ⟨n, h⟩ : A)) else 0) ∈ _
          rw [dite_eq_right hlt]
          exact Submodule.zero_mem _⟩
  left_inv x := by
    refine Subtype.ext (EvenVariableAlgebra.ext (Finsupp.ext fun n => ?_))
    change (if h : n < m / d + 1 then ((x.1.coeff n : A)) else 0) = x.1.coeff n
    by_cases hlt : n < m / d + 1
    · rw [dite_eq_left hlt]
    · rw [dite_eq_right hlt]
      exact (coeff_eq_zero_of_mem_grade x.2
        (fun h => hlt ((mul_le_iff_lt_div_succ hd n).mp h))).symm
  right_inv f := by
    funext n
    refine Subtype.ext ?_
    change (if h : (n : ℕ) < m / d + 1 then ((f ⟨(n : ℕ), h⟩ : A)) else 0) = _
    rw [dite_eq_left n.isLt]
  map_add' x y := by
    funext n
    exact Subtype.ext (by simp)
  map_smul' r x := by
    funext n
    exact Subtype.ext (by simp)

/-- Each homogeneous piece of an even-variable extension of positive degree is free over the base
ring when every homogeneous piece of the coefficient algebra is. -/
public theorem free_grade (𝒜 : ℕ → Submodule R A)
    (hfree : ∀ k, Module.Free R (𝒜 k)) {d : ℕ} (hd : 0 < d) (m : ℕ) :
    Module.Free R (grade 𝒜 d m) := by
  have hn : ∀ n : Fin (m / d + 1), Module.Free R (𝒜 (m - (n : ℕ) * d)) := fun n => hfree _
  exact Module.Free.of_equiv (gradeLinearEquiv 𝒜 hd m).symm

end EvenVariableAlgebra

end Even

section Transfer

variable {R : Type u} [CommRing R]

/-- A ring equivalence commuting with the base-ring structure map is `R`-linear. -/
public theorem map_smul_of_algebraMap {B C : Type v} [Ring B] [Ring C]
    [Algebra R B] [Algebra R C] (e : B ≃+* C)
    (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r) (r : R) (x : B) :
    e (r • x) = r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, he]

/-- A grading-detecting ring equivalence which commutes with the base-ring structure map
identifies the homogeneous pieces as `R`-modules. This is the shape in which the successor stages
of a graded divided-power polynomial algebra are presented: a ring equivalence from a
one-variable extension onto the next stage, fixing the coefficients and detecting the grading. -/
public def gradeLinearEquivOfRingEquiv {B C : Type v} [Ring B] [Ring C]
    [Algebra R B] [Algebra R C] (Bᵢ : ℕ → Submodule R B) (Cᵢ : ℕ → Submodule R C)
    (e : B ≃+* C) (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ e x ∈ Cᵢ m) (m : ℕ) :
    Bᵢ m ≃ₗ[R] Cᵢ m where
  toFun x := ⟨e x.1, (hgrade m x.1).mp x.2⟩
  invFun y := ⟨e.symm y.1, (hgrade m (e.symm y.1)).mpr (by rw [e.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul_of_algebraMap e he r x.1)

/-- Freeness of a homogeneous piece transfers along a grading-detecting ring equivalence that
commutes with the base-ring structure map. -/
public theorem free_grade_of_ringEquiv {B C : Type v} [Ring B] [Ring C]
    [Algebra R B] [Algebra R C] (Bᵢ : ℕ → Submodule R B) (Cᵢ : ℕ → Submodule R C)
    (e : B ≃+* C) (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ e x ∈ Cᵢ m) (m : ℕ)
    (hfree : Module.Free R (Bᵢ m)) :
    Module.Free R (Cᵢ m) :=
  Module.Free.of_equiv (gradeLinearEquivOfRingEquiv Bᵢ Cᵢ e he hgrade m)

end Transfer

section DirectedUnion

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module exhausted by a directed family of submodules each of which carries a basis, the
bases increasing with the family, is free: a finite subset of the union of the bases already lies
in one of them, so independence is inherited, and the union spans because the submodules do.

The compatibility of the bases is essential and not a formality. A directed union of free
submodules need not be free — `ℚ` is the union of the free `ℤ`-submodules `ℤ · (1 / n)` and is not
a free `ℤ`-module — so this is the hypothesis a construction has to supply by hand. -/
public theorem free_of_directed_bases
    {σ : Type w} [Preorder σ] [IsDirected σ (· ≤ ·)]
    (N : σ → Submodule R M) (b : σ → Set M) (hb : Monotone b)
    (hspan : ∀ s, Submodule.span R (b s) = N s)
    (hind : ∀ s, LinearIndepOn R id (b s))
    (hsup : ⨆ s, N s = ⊤) :
    Module.Free R M := by
  have hdir : Directed (· ⊆ ·) b := by
    intro s t
    obtain ⟨w, hsw, htw⟩ := directed_of (· ≤ ·) s t
    exact ⟨w, hb hsw, hb htw⟩
  have hiu : LinearIndepOn R id (⋃ s, b s) :=
    linearIndepOn_iUnion_of_directed hdir hind
  have hspan' : Submodule.span R (⋃ s, b s) = ⊤ := by
    rw [Submodule.span_iUnion]
    simp only [hspan]
    exact hsup
  have hrange : (Set.range fun y : ((⋃ s, b s : Set M)) => id (y : M)) = ⋃ s, b s :=
    Subtype.range_val
  exact Module.Free.of_basis (Module.Basis.mk hiu (by
    intro x _
    rw [hrange, hspan']
    exact Submodule.mem_top))

end DirectedUnion

end DividedPowers.TateResolution

end
