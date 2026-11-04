module

public import Mathlib.RingTheory.Congruence.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial

/-!
# Lifting maps from graded divided-power polynomial algebras

A map on zeroth homology from a graded divided-power polynomial differential
algebra lifts to a divided-power differential graded algebra map when the target
has no positive homology.

## Main definitions

* `zerothHomologyCongruence` kills positive-degree elements and degree-zero
  boundaries. Its quotient is the zeroth homology algebra.

## Main results

* `exists_dividedPowerDGAMap_lift` lifts a map on zeroth homology.
* `finiteVariableStage_erase_high`, `exists_finiteVariableStage_le_degree` and
  `gradeZero_mem_coefficientClosure` cut a finite variable stage down to the variables whose
  degree an element can see.

## Implementation notes

The zeroth homology algebra is presented as a quotient of the total algebra by
positive homogeneous elements and boundaries of degree one. The lifting equation
is stated on all representatives of the quotient; positive-degree representatives
are zero on both sides.

## References

* [Stacks Project, Tag 09PP](https://stacks.math.columbia.edu/tag/09PP)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- The ring congruence cutting out zeroth homology in a nonnegatively graded DGA. -/
public def zerothHomologyCongruence
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A) : RingCon A :=
  ringConGen (fun x y : A => y = 0 ∧
    ((∃ n : ℕ, 0 < n ∧ x ∈ 𝒜 n) ∨
      (∃ z : A, z ∈ 𝒜 1 ∧ d z = x)))

/-- Zeroth homology as an `R`-algebra quotient. -/
public abbrev zerothHomology
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A) :=
  (zerothHomologyCongruence 𝒜 d).Quotient

private theorem zerothHomology_mk'_positive_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
    {n : ℕ} (hn : 0 < n) {x : A} (hx : x ∈ 𝒜 n) :
    (zerothHomologyCongruence 𝒜 d).mk' x = 0 := by
  apply (RingCon.eq (zerothHomologyCongruence 𝒜 d)).2
  apply RingCon.le_ringConGen
  exact ⟨rfl, Or.inl ⟨n, hn, hx⟩⟩

private theorem exists_zerothRepresentative
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A) (x : A) :
    ∃ x₀ : A, x₀ ∈ 𝒜 0 ∧
      (zerothHomologyCongruence 𝒜 d).mk' x =
        (zerothHomologyCongruence 𝒜 d).mk' x₀ := by
  classical
  let c := zerothHomologyCongruence 𝒜 d
  let z := DirectSum.decompose 𝒜 x
  refine ⟨(z 0 : A), (z 0).property, ?_⟩
  have hsum : (∑ i ∈ z.support, (z i : A)) = x := by
    simpa [z] using DirectSum.sum_support_decompose 𝒜 x
  have hterm : ∀ i ∈ z.support, i ≠ 0 → c.mk' (z i : A) = 0 := fun i _ hiz =>
    zerothHomology_mk'_positive_eq_zero 𝒜 d (Nat.pos_of_ne_zero hiz) (z i).property
  have hz : 0 ∉ z.support → c.mk' (z 0 : A) = 0 := by
    intro h0
    have hzero : z 0 = 0 := by
      simpa [DFinsupp.mem_support_iff] using h0
    simp [hzero]
  rw [← hsum, map_sum]
  exact Finset.sum_eq_single 0 hterm hz

private theorem zerothHomology_mk'_d_grade_one_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
    {x : A} (hx : x ∈ 𝒜 1) :
    (zerothHomologyCongruence 𝒜 d).mk' (d x) = 0 := by
  apply (RingCon.eq (zerothHomologyCongruence 𝒜 d)).2
  apply RingCon.le_ringConGen
  exact ⟨rfl, Or.inr ⟨x, hx, rfl⟩⟩

/-- In degree zero the quotient congruence has exactly the degree-one boundaries
as its kernel. This is the bridge from equality in the presented zeroth homology
algebra to the actual differential equation needed when lifting degree-one generators. -/
private theorem zerothHomology_gradeZero_eq_boundary
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d]
    {x : A} (hx : x ∈ 𝒜 0)
    (hzero : (zerothHomologyCongruence 𝒜 d).mk' x = 0) :
    ∃ z : A, z ∈ 𝒜 1 ∧ d z = x := by
  classical
  let r : A → A → Prop := fun a b => b = 0 ∧
    ((∃ n : ℕ, 0 < n ∧ a ∈ 𝒜 n) ∨ (∃ z : A, z ∈ 𝒜 1 ∧ d z = a))
  let p₀ : A →+* 𝒜 0 := GradedRing.projZeroRingHom' 𝒜
  have hp_grade (a : A) : (p₀ a : A) ∈ 𝒜 0 := (p₀ a).property
  have hp_id {a : A} (ha : a ∈ 𝒜 0) : (p₀ a : A) = a :=
    DirectSum.decompose_of_mem_same 𝒜 ha
  have hrel : RingConGen.Rel r x 0 := by
    show (ringConGen r) x 0
    exact (RingCon.eq (ringConGen r)).1 hzero
  have hboundary : ∀ {a b : A}, RingConGen.Rel r a b →
      ∃ z : A, z ∈ 𝒜 1 ∧ d z = (p₀ a : A) - p₀ b := by
    intro a b hab
    induction hab with
    | of a b hab =>
        rcases hab with ⟨rfl, hgen⟩
        rcases hgen with ⟨n, hn, ha⟩ | ⟨z, hz, hdz⟩
        · have hp0 : (p₀ a : A) = 0 := by
            show GradedRing.projZeroRingHom 𝒜 a = 0
            rw [GradedRing.projZeroRingHom_apply]
            exact DirectSum.decompose_of_mem_ne 𝒜 ha (Nat.ne_of_gt hn)
          refine ⟨0, (𝒜 1).zero_mem, ?_⟩
          simp [hp0]
        · have hz0 : d z ∈ 𝒜 0 := by
            simpa using (IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := d) hz)
          refine ⟨z, hz, ?_⟩
          rw [← hdz, hp_id hz0]
          simp
    | refl a =>
        exact ⟨0, (𝒜 1).zero_mem, by simp⟩
    | symm hab ih =>
        obtain ⟨z, hz, hdz⟩ := ih
        refine ⟨-z, (𝒜 1).neg_mem hz, ?_⟩
        simp [hdz]
    | trans hab hbc ihab ihbc =>
        obtain ⟨z₁, hz₁, hdz₁⟩ := ihab
        obtain ⟨z₂, hz₂, hdz₂⟩ := ihbc
        refine ⟨z₁ + z₂, (𝒜 1).add_mem hz₁ hz₂, ?_⟩
        simp [map_add, hdz₁, hdz₂]
    | add hab hcd ihab ihcd =>
        obtain ⟨z₁, hz₁, hdz₁⟩ := ihab
        obtain ⟨z₂, hz₂, hdz₂⟩ := ihcd
        refine ⟨z₁ + z₂, (𝒜 1).add_mem hz₁ hz₂, ?_⟩
        simp [map_add, hdz₁, hdz₂]
        abel
    | mul hab hcd ihab ihcd =>
        rename_i w x y z
        obtain ⟨z₁, hz₁, hdz₁⟩ := ihab
        obtain ⟨z₂, hz₂, hdz₂⟩ := ihcd
        have hpc : d (p₀ y) = 0 :=
          IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) (hp_grade y)
        have hpb : d (p₀ x) = 0 :=
          IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) (hp_grade x)
        have hfirst : d (z₁ * (p₀ y : A)) =
            ((p₀ w : A) - p₀ x) * (p₀ y : A) := by
          rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) hz₁ (hp_grade y),
            hdz₁, hpc]
          simp
        have hsecond : d ((p₀ x : A) * z₂) =
            (p₀ x : A) * ((p₀ y : A) - p₀ z) := by
          rw [IsDifferentialGradedAlgebra.leibniz (𝒜 := 𝒜) (d := d) (hp_grade x) hz₂,
            hpb, hdz₂]
          simp
        refine ⟨z₁ * (p₀ y : A) + (p₀ x : A) * z₂, (𝒜 1).add_mem
          (SetLike.mul_mem_graded hz₁ (hp_grade y))
          (SetLike.mul_mem_graded (hp_grade x) hz₂), ?_⟩
        rw [map_add, hfirst, hsecond, map_mul p₀ w y, map_mul p₀ x z, sub_mul, mul_sub]
        abel
  obtain ⟨z, hz, hdz⟩ := hboundary hrel
  refine ⟨z, hz, ?_⟩
  rw [hp_id hx] at hdz
  simpa using hdz

/-- Removing a variable whose degree is above the degree of an element does not
change the finite-stage subring needed to contain that element. -/
public theorem finiteVariableStage_erase_high
    {R : Type u} {A : Type v} {σ : Type z}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γ ι)
    [DecidableEq (Σ k : ℕ, hA.indices k)]
    (n : ℕ) (x : A) (S : Finset (Σ k : ℕ, hA.indices k))
    (j : Σ k : ℕ, hA.indices k) (hj : j ∈ S)
    (hhigh : n < j.1 + 1)
    (hxS : x ∈ finiteVariableStage γ ι hA.generator S)
    (hx : x ∈ 𝒜 n) :
    x ∈ finiteVariableStage γ ι hA.generator (S.erase j) := by
  classical
  let T := finiteVariableStage γ ι hA.generator
  let S' := S.erase j
  let S'' : Finset (Σ k : ℕ, hA.indices k) := by
    let : DecidableEq (Σ k : ℕ, hA.indices k) := Classical.decEq _
    exact insert j S'
  show x ∈ T S'
  have hjnot : j ∉ S' := Finset.notMem_erase j S
  rcases hA.successor S' j hjnot with
    ⟨aS, -, Sᵢ, gS, cS, δS, hδ, hodd, heven⟩
  let : Algebra R (T S') := aS
  let : GradedAlgebra Sᵢ := gS
  let : IsStrictlyGradedComm Sᵢ := cS
  let d := j.1 + 1
  have hinsert : S'' = S := by
    apply Finset.ext
    intro k
    by_cases hk : k = j
    · subst k
      simp [S'', S', hj]
    · simp [S'', S', hk]
  by_cases hd : Even d
  · let : Fact (Even d) := ⟨hd⟩
    rcases heven hd with ⟨e, hebase, hgen, hgrade, hdpow⟩
    let u : EvenVariableAlgebra
        (T S') := e.symm ⟨x, by simpa [T, S'', hinsert] using hxS⟩
    have hu : u ∈ EvenVariableAlgebra.grade
        Sᵢ d n := by
      rw [hgrade]
      simpa [u, hinsert] using hx
    have hucoeff (k : ℕ) (hk : k ≠ 0) : u.coeff k = 0 := by
      have hmem := (EvenVariableAlgebra.mem_grade_iff
        Sᵢ d n u).1 hu k
      have hkn : n < k * d := by
        have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        calc
          n < d := by simpa [d] using hhigh
          _ ≤ k * d := by simpa [Nat.mul_comm] using Nat.mul_le_mul_right d hkpos
      have : u.coeff k ∈ (⊥ : Submodule R (T S')) := by
        simpa [not_le_of_gt hkn] using hmem
      simpa using this
    have hu_eq :
        EvenVariableAlgebra.coeffEmbedding
          (u.coeff 0) = u := by
      apply EvenVariableAlgebra.ext
      ext k
      by_cases hk : k = 0
      · subst k
        simp
      · rw [hucoeff k hk]
        simp [EvenVariableAlgebra.coeffEmbedding, hk]
    have hxu : ((e u : T S'') : A) = x := by
      simp [u]
    have hxval : x = (u.coeff 0 : A) :=
      hxu.symm.trans ((congrArg (fun y : EvenVariableAlgebra (T S') =>
        ((e y : T S'') : A)) hu_eq.symm).trans (hebase (u.coeff 0)))
    rw [hxval]
    show (u.coeff 0 : A) ∈ T S'
    exact (u.coeff 0).property
  · have hdOdd : Odd d := Nat.not_even_iff_odd.mp hd
    rcases hodd hdOdd with ⟨e, hebase, hgen, hgrade, hdpow⟩
    let u : OddVariableExtension Sᵢ d :=
      e.symm ⟨x, by simpa [T, S'', hinsert] using hxS⟩
    have hu : u ∈ OddVariableExtension.grade
        Sᵢ d n := by
      rw [hgrade]
      simpa [u, hinsert] using hx
    have husnd : (u.snd : T S') = 0 := by
      have hmem := (OddVariableExtension.mem_grade_iff
        Sᵢ d n u).1 hu
      have hdgt : ¬ d ≤ n := Nat.not_le_of_gt (by simpa [d] using hhigh)
      have hsnd : (show T S' from u.snd) ∈ (⊥ : Submodule R (T S')) := by
        simpa [hdgt] using hmem.2
      exact (Submodule.mem_bot R).mp hsnd
    have hu_eq :
        OddVariableExtension.inclusion Sᵢ d
          u.fst = u := by
      apply TrivSqZeroExt.ext
      · rfl
      · show (0 : T S') = (show T S' from u.snd)
        exact husnd.symm
    have hxu : ((e u : T S'') : A) = x := by
      simp [u]
    have hxval : x = (u.fst : A) :=
      hxu.symm.trans ((congrArg (fun y : OddVariableExtension Sᵢ d =>
        ((e y : T S'') : A)) hu_eq.symm).trans (hebase u.fst))
    rw [hxval]
    show (u.fst : A) ∈ T S'
    exact u.fst.property

/-- A homogeneous element in a finite stage can be represented in the substage
generated by variables of no greater degree. -/
public theorem exists_finiteVariableStage_le_degree
    {R : Type u} {A : Type v} {σ : Type z}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [IsStrictlyGradedComm 𝒜] (γ : DividedPowerStructure 𝒜)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γ ι)
    (n : ℕ) (x : A) (S : Finset (Σ k : ℕ, hA.indices k))
    (hxS : x ∈ finiteVariableStage γ ι hA.generator S)
    (hx : x ∈ 𝒜 n) :
    ∃ T : Finset (Σ k : ℕ, hA.indices k), T ⊆ S ∧
      (∀ j ∈ T, j.1 + 1 ≤ n) ∧
      x ∈ finiteVariableStage γ ι hA.generator T := by
  classical
  let P (S : Finset (Σ k : ℕ, hA.indices k)) :=
    ∀ x : A, x ∈ finiteVariableStage γ ι hA.generator S →
      x ∈ 𝒜 n → ∃ T : Finset (Σ k : ℕ, hA.indices k), T ⊆ S ∧
        (∀ j ∈ T, j.1 + 1 ≤ n) ∧
        x ∈ finiteVariableStage γ ι hA.generator T
  have hall : ∀ S : Finset (Σ k : ℕ, hA.indices k), P S := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih y hyS hy
    by_cases hlow : ∀ j ∈ S, j.1 + 1 ≤ n
    · exact ⟨S, Finset.Subset.rfl, hlow, hyS⟩
    · push Not at hlow
      obtain ⟨j, hjS, hjhigh⟩ := hlow
      have hy' := finiteVariableStage_erase_high 𝒜 γ ι hA n y S j hjS hjhigh hyS hy
      obtain ⟨T, hTS, hTlow, hyT⟩ :=
        ih (S.erase j) (Finset.erase_ssubset hjS) y hy' hy
      exact ⟨T, hTS.trans (Finset.erase_subset _ _), hTlow, hyT⟩
  exact hall S x hxS hx

/-- Ring homomorphisms agreeing on the coefficients, the generators and their divided powers
agree on the finite stage. -/
private theorem ringHom_eq_on_finiteVariableStage
    {R : Type u} {A : Type v} {D : Type w} {σ : Type z} {J : Type*}
    [CommRing R] [Ring A] [Ring D] [Algebra R A]
    {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (ι : MvPolynomial σ R →ₐ[R] A) (T : J → A)
    (F G : A →+* D) (S : Finset J)
    (hι : ∀ p, F (ι p) = G (ι p)) (hT : ∀ j ∈ S, F (T j) = G (T j))
    (hdp : ∀ j ∈ S, ∀ n, F (γ.dpow n (T j)) = G (γ.dpow n (T j)))
    {x : A} (hx : x ∈ finiteVariableStage γ ι T S) : F x = G x := by
  refine RingHom.eqOn_set_closure ?_ hx
  rintro y (⟨p, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩)
  exacts [hι p, hT j hj, hdp j hj n]

/-- Equality on the generators and coefficient algebra implies equality on a
finite divided-power polynomial stage. -/
private theorem algHom_eq_on_finiteVariableStage
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (f g : A →ₐ[R] B)
    (hf_coeff : ∀ p, f (ι p) = g (ι p))
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    (hg_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      g (γA.dpow n a) = γB.dpow n (g a))
    (S : Finset (Σ k : ℕ, hA.indices k))
    (hf_gen : ∀ j, j ∈ S → f (hA.generator j) = g (hA.generator j))
    {x : A} (hx : x ∈ finiteVariableStage γA ι hA.generator S) :
    f x = g x := by
  refine ringHom_eq_on_finiteVariableStage γA ι hA.generator f.toRingHom g.toRingHom S
    hf_coeff hf_gen (fun j hj n => ?_) hx
  by_cases hp : hA.generator j ∈ positiveEvenPart 𝒜
  · exact (hf_dpow _ _ hp).trans ((congrArg _ (hf_gen j hj)).trans (hg_dpow _ _ hp).symm)
  · simp [γA.dpow_null hp]

/-- Two grading-preserving maps that agree through degree `n` agree on every
homogeneous element of degree `n`. -/
private theorem gradedAlgHom_eq_on_grade
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (f g : A →ₐ[R] B)
    (hf_coeff : ∀ p, f (ι p) = g (ι p))
    (_hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    (_hg_grade : ∀ n a, a ∈ 𝒜 n → g a ∈ ℬ n)
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    (hg_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      g (γA.dpow n a) = γB.dpow n (g a))
    (n : ℕ) (hf_gen : ∀ j, j.1 + 1 ≤ n →
      f (hA.generator j) = g (hA.generator j))
    {x : A} (hx : x ∈ 𝒜 n) : f x = g x := by
  classical
  obtain ⟨S, hS⟩ := hA.finite_support x
  obtain ⟨T, hTS, hTdegree, hxT⟩ :=
    exists_finiteVariableStage_le_degree 𝒜 γA ι hA n x S hS hx
  exact algHom_eq_on_finiteVariableStage 𝒜 ℬ γA γB ι hA f g hf_coeff
    hf_dpow hg_dpow T (fun j hj => hf_gen j (hTdegree j hj)) hxT

private def gradedComponent
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x : A) (n : ℕ) : A :=
  (DirectSum.decompose 𝒜 x n : 𝒜 n)

private theorem gradedComponent_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x : A) (n : ℕ) :
    gradedComponent 𝒜 x n ∈ 𝒜 n :=
  (DirectSum.decompose 𝒜 x n).property

private theorem gradedComponent_add
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x y : A) (n : ℕ) :
    gradedComponent 𝒜 (x + y) n = gradedComponent 𝒜 x n + gradedComponent 𝒜 y n := by
  simp [gradedComponent]

private theorem gradedComponent_mul
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (x y : A) (n : ℕ) :
    gradedComponent 𝒜 (x * y) n =
      ∑ ij ∈ Finset.antidiagonal n,
        gradedComponent 𝒜 x ij.1 * gradedComponent 𝒜 y ij.2 := by
  classical
  show ((DirectSum.decompose 𝒜 (x * y) n : 𝒜 n) : A) = _
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  simp [gradedComponent]

private theorem homogeneous_mem_positiveEven_degree
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {n : ℕ} {x : A} (hx : x ∈ 𝒜 n)
    (hp : x ∈ positiveEvenPart 𝒜) : Even n ∨ x = 0 := by
  classical
  by_cases hn : Even n
  · exact Or.inl hn
  · let π : A →ₗ[R] 𝒜 n :=
      (DFinsupp.lapply n).comp (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap
    have hle : positiveEvenPart 𝒜 ≤ LinearMap.ker π := by
      rw [positiveEvenPart]
      refine iSup_le fun k => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show ((DirectSum.decompose 𝒜 y) n : A) = 0
      apply DirectSum.decompose_of_mem_ne 𝒜 hy
      intro heq
      apply hn
      refine ⟨k + 1, ?_⟩
      calc
        n = 2 * (k + 1) := heq.symm
        _ = (k + 1) + (k + 1) := by ring
    have hπ0 : π x = 0 := hle hp
    have hπx : π x = ⟨x, hx⟩ := Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 hx)
    exact Or.inr (congrArg Subtype.val (hπx.symm.trans hπ0))

private theorem dgaMap_chain_on_homogeneous_components
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (f : A →ₐ[R] B) (dB : B →ₗ[R] B)
    {m : ℕ} {a : A} (ha : a ∈ 𝒜 m)
    (hchain : dB (f a) = f (dA a)) (i : ℕ) :
    dB (f (gradedComponent 𝒜 a i)) = f (dA (gradedComponent 𝒜 a i)) := by
  by_cases hi : i = m
  · subst i
    have hdecomp : gradedComponent 𝒜 a m = a :=
      DirectSum.decompose_of_mem_same 𝒜 ha
    simpa [hdecomp] using hchain
  · have hdecomp : gradedComponent 𝒜 a i = 0 :=
      DirectSum.decompose_of_mem_ne 𝒜 ha (Ne.symm hi)
    simp [hdecomp]

private theorem dgaMap_chain_of_mem_gradeZero
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    (f : A →ₐ[R] B) (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    {a : A} (ha : a ∈ 𝒜 0) : dB (f a) = f (dA a) := by
  simp [IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := dA) ha,
    IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := ℬ) (d := dB) (hf_grade 0 a ha)]

private theorem positiveEvenPart_map
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    {a : A} (ha : a ∈ positiveEvenPart 𝒜) : f a ∈ positiveEvenPart ℬ := by
  apply (Submodule.mem_iSup _).2
  intro N hN
  have hmem := (Submodule.mem_iSup _).1 ha
  apply hmem (Submodule.comap f.toLinearMap N)
  intro k x hx
  show f x ∈ N
  exact hN k (hf_grade _ _ hx)

private theorem dgaMap_chain_dpow
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    {a : A} (ha : a ∈ positiveEvenPart 𝒜)
    (hchain : dB (f a) = f (dA a)) (n : ℕ) :
    dB (f (γA.dpow n a)) = f (dA (γA.dpow n a)) := by
  have hfa : f a ∈ positiveEvenPart ℬ := positiveEvenPart_map 𝒜 ℬ f hf_grade ha
  cases n with
  | zero =>
      simp [γA.dpow_zero ha,
        IsDifferentialGradedAlgebra.d_grade_zero
          (𝒜 := ℬ) (d := dB) (SetLike.one_mem_graded ℬ),
        IsDifferentialGradedAlgebra.d_grade_zero
          (𝒜 := 𝒜) (d := dA) (SetLike.one_mem_graded 𝒜)]
  | succ n =>
      have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
      calc
        dB (f (γA.dpow (n + 1) a)) =
            dB (γB.dpow (n + 1) (f a)) := by rw [hf_dpow (n + 1) a ha]
        _ = dB (f a) * γB.dpow ((n + 1) - 1) (f a) :=
          IsCompatibleWithDifferential.d_dpow (γ := γB) hn hfa
        _ = f (dA a) * γB.dpow n (f a) := by rw [hchain, Nat.succ_sub_one]
        _ = f (dA a) * f (γA.dpow n a) := by rw [hf_dpow n a ha]
        _ = f (dA a * γA.dpow n a) := (map_mul f _ _).symm
        _ = f (dA (γA.dpow (n + 1) a)) := by
          rw [IsCompatibleWithDifferential.d_dpow (γ := γA) hn ha]
          simp

/-- Chain compatibility on a finite-variable stage follows from compatibility on
its coefficient algebra and generators. The predicate is stated on every
homogeneous component because products of elements of a stage need not be
homogeneous. -/
private theorem dgaMap_chain_on_finiteVariableStage
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (f : A →ₐ[R] B)
    (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    (_hf_coeff : ∀ p, dB (f (ι p)) = f (dA (ι p)))
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    (S : Finset (Σ k : ℕ, hA.indices k))
    (hf_gen : ∀ j, j ∈ S →
      dB (f (hA.generator j)) = f (dA (hA.generator j)))
    {x : A} (hx : x ∈ finiteVariableStage γA ι hA.generator S) :
    ∀ i, dB (f (gradedComponent 𝒜 x i)) =
      f (dA (gradedComponent 𝒜 x i)) := by
  classical
  rw [finiteVariableStage] at hx
  let p (x : A) := ∀ i, dB (f (gradedComponent 𝒜 x i)) =
    f (dA (gradedComponent 𝒜 x i))
  have hzero : ∀ {a : A}, a ∈ 𝒜 0 → p a := fun ha =>
    dgaMap_chain_on_homogeneous_components 𝒜 dA f dB ha
      (dgaMap_chain_of_mem_gradeZero 𝒜 ℬ dA dB f hf_grade ha)
  refine Subring.closure_induction (s := Set.range ι ∪
      {y : A | ∃ j, j ∈ S ∧
        (y = hA.generator j ∨ ∃ n, y = γA.dpow n (hA.generator j))})
    (p := fun y _ => p y) ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨q, rfl⟩ | hy
    · exact hzero (hA.coefficient_mem q)
    · rcases hy with ⟨j, hj, hyj⟩
      rcases hyj with rfl | ⟨n, rfl⟩
      · intro i
        exact dgaMap_chain_on_homogeneous_components 𝒜 dA f dB
          (hA.generator_mem j) (hf_gen j hj) i
      · intro i
        by_cases hp : hA.generator j ∈ positiveEvenPart 𝒜
        · cases n with
          | zero =>
              rw [γA.dpow_zero hp]
              exact hzero (SetLike.one_mem_graded 𝒜) i
          | succ m =>
              rcases homogeneous_mem_positiveEven_degree 𝒜 (hA.generator_mem j) hp with
                ⟨k, hk⟩ | hzero
              · have hgrade : γA.dpow (m + 1) (hA.generator j) ∈
                    𝒜 (2 * (m + 1) * k) := by
                  apply γA.dpow_mem_grade (Nat.succ_ne_zero m) hp
                  simpa [hk, two_mul] using hA.generator_mem j
                have hchain := dgaMap_chain_dpow 𝒜 ℬ γA γB dA dB f hf_grade
                  hf_dpow hp (hf_gen j hj) (m + 1)
                exact dgaMap_chain_on_homogeneous_components 𝒜 dA f dB hgrade hchain i
              · cases m with
                | zero =>
                    rw [γA.dpow_one hp, hzero]
                    simp [gradedComponent]
                | succ m =>
                    have hdpow : γA.dpow (m + 2) (hA.generator j) = 0 := by
                      rw [hzero]
                      simpa using γA.dpow_mul_odd (n := m + 2) (d := 0) (e := 0)
                        (by omega) ((𝒜 1).zero_mem) ((𝒜 1).zero_mem)
                    simp [gradedComponent, hdpow]
        · have hnull : γA.dpow n (hA.generator j) = 0 := γA.dpow_null hp
          simp [gradedComponent, hnull]
  · intro i
    simp [gradedComponent]
  · exact hzero (SetLike.one_mem_graded 𝒜)
  · intro x y _ _ hx hy i
    rw [gradedComponent_add]
    simp only [map_add]
    rw [hx i, hy i]
  · intro x _ hx i
    have hcomp : gradedComponent 𝒜 (-x) i = -gradedComponent 𝒜 x i := by
      simp only [gradedComponent]
      rw [DirectSum.decompose_neg]
      exact Submodule.coe_neg (𝒜 i) ((DirectSum.decompose 𝒜 x) i)
    rw [hcomp]
    simp [hx i]
  · intro x y _ _ hx hy i
    classical
    rw [gradedComponent_mul]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    have hxi := hx ij.1
    have hyj := hy ij.2
    have hleibA := IsDifferentialGradedAlgebra.leibniz
      (𝒜 := 𝒜) (d := dA) (gradedComponent_mem 𝒜 x ij.1)
      (gradedComponent_mem 𝒜 y ij.2)
    have hleibB := IsDifferentialGradedAlgebra.leibniz
      (𝒜 := ℬ) (d := dB)
      (hf_grade ij.1 _ (gradedComponent_mem 𝒜 x ij.1))
      (hf_grade ij.2 _ (gradedComponent_mem 𝒜 y ij.2))
    rw [map_mul, hleibB, hxi, hyj, hleibA]
    simp only [map_add, map_smul, map_mul]

private theorem dgaMap_chain_on_grade_from_generators
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (f : A →ₐ[R] B)
    (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    (hf_coeff : ∀ p, dB (f (ι p)) = f (dA (ι p)))
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    (n : ℕ)
    (hf_gen : ∀ j, j.1 + 1 ≤ n →
      dB (f (hA.generator j)) = f (dA (hA.generator j)))
    {x : A} (hx : x ∈ 𝒜 n) :
    dB (f x) = f (dA x) := by
  classical
  obtain ⟨S, hS⟩ := hA.finite_support x
  obtain ⟨T, hTS, hTdegree, hxT⟩ :=
    exists_finiteVariableStage_le_degree 𝒜 γA ι hA n x S hS hx
  have hstage := dgaMap_chain_on_finiteVariableStage 𝒜 ℬ γA γB dA dB ι hA f
    hf_grade hf_coeff hf_dpow T (fun j hj => hf_gen j (hTdegree j hj)) hxT
  have hcomp : gradedComponent 𝒜 x n = x := DirectSum.decompose_of_mem_same 𝒜 hx
  simpa [hcomp] using hstage n

private theorem dgaMap_chain_on_finiteVariableStage_element
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (f : A →ₐ[R] B)
    (hf_grade : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ n)
    (hf_coeff : ∀ p, dB (f (ι p)) = f (dA (ι p)))
    (hf_dpow : ∀ n a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n a) = γB.dpow n (f a))
    (S : Finset (Σ k : ℕ, hA.indices k))
    (hf_gen : ∀ j, j ∈ S →
      dB (f (hA.generator j)) = f (dA (hA.generator j)))
    {x : A} (hx : x ∈ finiteVariableStage γA ι hA.generator S) :
    dB (f x) = f (dA x) := by
  classical
  let z := DirectSum.decompose 𝒜 x
  have hsum : (∑ i ∈ z.support, (z i : A)) = x := by
    simpa [z] using DirectSum.sum_support_decompose 𝒜 x
  have hcomp := dgaMap_chain_on_finiteVariableStage 𝒜 ℬ γA γB dA dB ι hA f
    hf_grade hf_coeff hf_dpow S hf_gen hx
  calc
    dB (f x) = dB (f (∑ i ∈ z.support, (z i : A))) := by rw [hsum]
    _ = ∑ i ∈ z.support, dB (f (z i : A)) := by simp only [map_sum]
    _ = ∑ i ∈ z.support, f (dA (z i : A)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [gradedComponent, z] using hcomp i
    _ = f (dA x) := by rw [← hsum]; simp only [map_sum]

/-- An element of degree zero lies in the subring generated by the coefficients. -/
public theorem gradeZero_mem_coefficientClosure
    {R : Type u} {A : Type v} {σ : Type z}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γ ι)
    {x : A} (hx : x ∈ 𝒜 0) : x ∈ Subring.closure (Set.range ι) := by
  classical
  obtain ⟨S, hS⟩ := hA.finite_support x
  obtain ⟨T, hTS, hTdegree, hxT⟩ :=
    exists_finiteVariableStage_le_degree 𝒜 γ ι hA 0 x S hS hx
  obtain rfl : T = ∅ := Finset.eq_empty_of_forall_notMem fun j hj => by
    have := hTdegree j hj
    omega
  simpa [finiteVariableStage] using hxT

private theorem degreeZero_quotient_compat
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    (γA : DividedPowerStructure 𝒜)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (φ₀ : zerothHomology 𝒜 dA →ₐ[R] zerothHomology ℬ dB)
    (f : A →ₐ[R] B) (fP : MvPolynomial σ R →ₐ[R] B)
    (hfP : ∀ p, (zerothHomologyCongruence ℬ dB).mk' (fP p) =
      φ₀ ((zerothHomologyCongruence 𝒜 dA).mk' (ι p)))
    (hcoeff : ∀ p, f (ι p) = fP p)
    {x : A} (hx : x ∈ 𝒜 0) :
    φ₀ ((zerothHomologyCongruence 𝒜 dA).mk' x) =
      (zerothHomologyCongruence ℬ dB).mk' (f x) := by
  classical
  let qA : A →ₐ[R] zerothHomology 𝒜 dA :=
    RingCon.mkₐ (α := R) (zerothHomologyCongruence 𝒜 dA)
  let qB : B →ₐ[R] zerothHomology ℬ dB :=
    RingCon.mkₐ (α := R) (zerothHomologyCongruence ℬ dB)
  let F : A →ₐ[R] zerothHomology ℬ dB := φ₀.comp qA
  let G : A →ₐ[R] zerothHomology ℬ dB := qB.comp f
  have hxcl : x ∈ Subring.closure (Set.range ι) :=
    gradeZero_mem_coefficientClosure 𝒜 γA ι hA hx
  have hEq : F x = G x := by
    refine RingHom.eqOn_set_closure (f := F.toRingHom) (g := G.toRingHom) ?_ hxcl
    rintro y ⟨p, rfl⟩
    show φ₀ ((zerothHomologyCongruence 𝒜 dA).mk' (ι p)) =
      (zerothHomologyCongruence ℬ dB).mk' (f (ι p))
    rw [hcoeff p, hfP p]
  simpa [F, G, qA, qB] using hEq

private def degreeZeroSubalgebra
    {R : Type u} {B : Type w} [CommRing R] [Ring B] [Algebra R B]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] : Subalgebra R B where
  carrier := ℬ 0
  zero_mem' := (ℬ 0).zero_mem
  one_mem' := SetLike.one_mem_graded ℬ
  add_mem' := (ℬ 0).add_mem
  mul_mem' := by
    intro x y hx hy
    simpa using (SetLike.mul_mem_graded hx hy)
  algebraMap_mem' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    exact (ℬ 0).smul_mem r (SetLike.one_mem_graded ℬ)

private theorem exists_degreeZeroCoefficientLift
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [IsStrictlyGradedComm ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    (ι : MvPolynomial σ R →ₐ[R] A)
    (φ₀ : zerothHomology 𝒜 dA →ₐ[R] zerothHomology ℬ dB) :
    ∃ f : MvPolynomial σ R →ₐ[R] B,
      (∀ p : MvPolynomial σ R, f p ∈ ℬ 0) ∧
      ∀ p : MvPolynomial σ R,
        (zerothHomologyCongruence ℬ dB).mk' (f p) =
          φ₀ ((zerothHomologyCongruence 𝒜 dA).mk' (ι p)) := by
  classical
  let cA := zerothHomologyCongruence 𝒜 dA
  let cB := zerothHomologyCongruence ℬ dB
  let S := degreeZeroSubalgebra ℬ
  let : CommRing S := {
    (inferInstance : Ring S) with
    mul_comm := by
      intro x y
      have h := IsStrictlyGradedComm.graded_comm (𝒜 := ℬ)
        (i := 0) (j := 0) x.property y.property
      apply Subtype.ext
      simpa using h
  }
  let y : σ → B := fun s => Classical.choose (cB.mk'_surjective
    (φ₀ (cA.mk' (ι (MvPolynomial.X s)))))
  have hy : ∀ s, cB.mk' (y s) = φ₀ (cA.mk' (ι (MvPolynomial.X s))) := fun s =>
    Classical.choose_spec (cB.mk'_surjective (φ₀ (cA.mk' (ι (MvPolynomial.X s)))))
  let z : σ → S := fun s => ⟨Classical.choose
      (exists_zerothRepresentative ℬ dB (y s)),
    (Classical.choose_spec (exists_zerothRepresentative ℬ dB (y s))).1⟩
  have hz : ∀ s, cB.mk' (z s : B) =
      φ₀ (cA.mk' (ι (MvPolynomial.X s))) := by
    intro s
    have h := Classical.choose_spec (exists_zerothRepresentative ℬ dB (y s))
    have hrep : cB.mk' (z s : B) = cB.mk' (y s) := by
      dsimp [z]
      exact h.2.symm
    exact hrep.trans (hy s)
  let fS : MvPolynomial σ R →ₐ[R] S := MvPolynomial.aeval z
  let f : MvPolynomial σ R →ₐ[R] B := S.val.comp fS
  let qA : A →ₐ[R] cA.Quotient := RingCon.mkₐ (α := R) cA
  let qB : B →ₐ[R] cB.Quotient := RingCon.mkₐ (α := R) cB
  refine ⟨f, ?_, ?_⟩
  · intro p
    dsimp [f]
    show ((fS p : S) : B) ∈ S
    exact (fS p).property
  · intro p
    show qB (f p) = φ₀ (qA (ι p))
    have hmap : qB.comp f = φ₀.comp (qA.comp ι) := by
      apply MvPolynomial.algHom_ext
      intro s
      simpa [qA, qB, f, fS, cA, cB] using hz s
    exact DFunLike.congr_fun hmap p

/-- The differential of a generator of degree `j.1 + 1` has degree `j.1`. -/
private theorem differential_generator_mem
    {R : Type u} {A : Type v} {σ : Type z}
    [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γA : DividedPowerStructure 𝒜) (dA : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 dA]
    (ι : MvPolynomial σ R →ₐ[R] A) (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (j : Σ k : ℕ, hA.indices k) : dA (hA.generator j) ∈ 𝒜 j.1 := by
  simpa using IsDifferentialGradedAlgebra.d_mem (𝒜 := 𝒜) (d := dA) (hA.generator_mem j)

/-- A map from a graded divided-power polynomial DGA to a positively acyclic
divided-power DGA lifting a prescribed map on zeroth homology. -/
@[stacks 09PP]
public theorem exists_dividedPowerDGAMap_lift
    {R : Type u} {A : Type v} {B : Type w} {σ : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA]
    [IsDifferentialGradedAlgebra ℬ dB]
    [IsCompatibleWithDifferential γA dA]
    [IsCompatibleWithDifferential γB dB]
    (ι : MvPolynomial σ R →ₐ[R] A)
    (hA : GradedDividedPowerPolynomial 𝒜 γA ι)
    (hB : ∀ (n : ℕ) (b : B), 0 < n → b ∈ ℬ n → dB b = 0 →
      ∃ c : B, c ∈ ℬ (n + 1) ∧ dB c = b)
    (φ₀ : zerothHomology 𝒜 dA →ₐ[R] zerothHomology ℬ dB) :
    ∃ φ : A →ₐ[R] B,
      (∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a ∈ ℬ n) ∧
      (∀ a : A, φ (dA a) = dB (φ a)) ∧
      (∀ (n : ℕ) (a : A), a ∈ positiveEvenPart 𝒜 →
        φ (γA.dpow n a) = γB.dpow n (φ a)) ∧
      (∀ a : A,
        φ₀ ((zerothHomologyCongruence 𝒜 dA).mk' a) =
          (zerothHomologyCongruence ℬ dB).mk' (φ a)) := by
  classical
  let cA := zerothHomologyCongruence 𝒜 dA
  let cB := zerothHomologyCongruence ℬ dB
  let qA : A →ₐ[R] cA.Quotient := RingCon.mkₐ (α := R) cA
  let qB : B →ₐ[R] cB.Quotient := RingCon.mkₐ (α := R) cB
  obtain ⟨fP, hfPgrade, hfPquot⟩ :=
    exists_degreeZeroCoefficientLift 𝒜 ℬ dA dB ι φ₀
  let Props (n : ℕ) (t : (Σ k : ℕ, hA.indices k) → B)
      (f : A →ₐ[R] B) : Prop :=
    (∀ j, j.1 + 1 ≤ n → t j ∈ ℬ (j.1 + 1)) ∧
    (∀ p, f (ι p) = fP p) ∧
    (∀ j, j.1 + 1 ≤ n → f (hA.generator j) = t j) ∧
    (∀ k a, a ∈ 𝒜 k → f a ∈ ℬ k) ∧
    (∀ m a, a ∈ positiveEvenPart 𝒜 →
      f (γA.dpow m a) = γB.dpow m (f a)) ∧
    (∀ k, k ≤ n → ∀ a, a ∈ 𝒜 k → dB (f a) = f (dA a))
  let StageData (n : ℕ) :=
    Σ t : (Σ k : ℕ, hA.indices k) → B,
      Σ f : A →ₐ[R] B, { p : Props n t f // True }
  let tZero : (Σ k : ℕ, hA.indices k) → B := fun _ => 0
  have hzeroGrade : ∀ j, tZero j ∈ ℬ (j.1 + 1) := fun j => (ℬ (j.1 + 1)).zero_mem
  obtain ⟨fZero, ⟨hfZeroCoeff, hfZeroGen, hfZeroGrade, hfZeroDpow⟩, _⟩ :=
    existsUnique_gradedDividedPowerPolynomial_map
      𝒜 γA ι hA ℬ γB fP hfPgrade tZero hzeroGrade
  have hfZeroChain : ∀ k, k ≤ 0 → ∀ a, a ∈ 𝒜 k →
      dB (fZero a) = fZero (dA a) := by
    intro k hk a ha
    obtain rfl := Nat.eq_zero_of_le_zero hk
    exact dgaMap_chain_of_mem_gradeZero 𝒜 ℬ dA dB fZero hfZeroGrade ha
  let base : StageData 0 :=
    ⟨tZero, ⟨fZero, ⟨fun j _ => hzeroGrade j, hfZeroCoeff,
      fun j hj => by omega, hfZeroGrade, hfZeroDpow, hfZeroChain⟩, trivial⟩⟩
  let step : (n : ℕ) → StageData n → StageData (n + 1) := by
    intro n s
    let t := s.1
    let f := s.2.1
    have hs : Props n t f := s.2.2.1
    have ht := hs.1
    have hcoeff := hs.2.1
    have hgen := hs.2.2.1
    have hgrade := hs.2.2.2.1
    have hdpow := hs.2.2.2.2.1
    have hchain := hs.2.2.2.2.2
    have hLift (j : Σ k : ℕ, hA.indices k) (hdeg : j.1 + 1 = n + 1) :
        ∃ c : B, c ∈ ℬ (n + 1) ∧ dB c = f (dA (hA.generator j)) := by
      have hgenGrade : hA.generator j ∈ 𝒜 (n + 1) := by
        simpa [hdeg] using hA.generator_mem j
      have hdiffGrade : dA (hA.generator j) ∈ 𝒜 n := by
        simpa [show j.1 = n by omega] using differential_generator_mem 𝒜 γA dA ι hA j
      have hbGrade : f (dA (hA.generator j)) ∈ ℬ n := hgrade n _ hdiffGrade
      cases n with
      | zero =>
          have hgenOne : hA.generator j ∈ 𝒜 1 := by
            simpa using hgenGrade
          have hqA := zerothHomology_mk'_d_grade_one_eq_zero 𝒜 dA hgenOne
          have hqcompat := degreeZero_quotient_compat 𝒜 ℬ dA dB γA ι hA φ₀
            f fP hfPquot hcoeff hdiffGrade
          have hqB : cB.mk' (f (dA (hA.generator j))) = 0 := by
            rw [hqA] at hqcompat
            simpa using hqcompat.symm
          obtain ⟨c, hc, hdc⟩ := zerothHomology_gradeZero_eq_boundary
            ℬ dB hbGrade hqB
          refine ⟨c, ?_, hdc⟩
          simpa using hc
      | succ m =>
          have hcycle : dB (f (dA (hA.generator j))) = 0 := by
            have hh := hchain (m + 1) (by omega) (dA (hA.generator j)) hdiffGrade
            rw [IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := 𝒜) (d := dA)] at hh
            simpa using hh
          obtain ⟨c, hc, hdc⟩ := hB (m + 1) (f (dA (hA.generator j))
            ) (by omega) hbGrade hcycle
          refine ⟨c, ?_, hdc⟩
          simpa using hc
    let t' : (Σ k : ℕ, hA.indices k) → B := fun j =>
      if h : j.1 + 1 ≤ n then t j
      else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h')
      else 0
    have ht' : ∀ j, t' j ∈ ℬ (j.1 + 1) := by
      intro j
      by_cases hjn : j.1 + 1 ≤ n
      · show (if h : j.1 + 1 ≤ n then t j
          else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h') else 0)
            ∈ ℬ (j.1 + 1)
        rw [dite_eq_left hjn]
        exact ht j hjn
      · by_cases hjeq : j.1 + 1 = n + 1
        · show (if h : j.1 + 1 ≤ n then t j
            else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h') else 0)
              ∈ ℬ (j.1 + 1)
          rw [dite_eq_right hjn, dite_eq_left hjeq]
          simpa [hjeq] using (Classical.choose_spec (hLift j hjeq)).1
        · show (if h : j.1 + 1 ≤ n then t j
            else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h') else 0)
              ∈ ℬ (j.1 + 1)
          rw [dite_eq_right hjn, dite_eq_right hjeq]
          exact (ℬ (j.1 + 1)).zero_mem
    have hmapExists := existsUnique_gradedDividedPowerPolynomial_map
      𝒜 γA ι hA ℬ γB fP hfPgrade t' ht'
    let f' : A →ₐ[R] B := Classical.choose hmapExists.exists
    have hf'prop := Classical.choose_spec hmapExists.exists
    have hf'coeff := hf'prop.1
    have hf'gen := hf'prop.2.1
    have hf'grade := hf'prop.2.2.1
    have hf'dpow := hf'prop.2.2.2
    have hEqGrade (k : ℕ) (hk : k ≤ n) {a : A} (ha : a ∈ 𝒜 k) :
        f' a = f a := by
      refine gradedAlgHom_eq_on_grade 𝒜 ℬ γA γB ι hA f' f
        (fun p => by rw [hf'coeff p, hcoeff p]) hf'grade hgrade hf'dpow hdpow k
        (fun j hj => ?_) ha
      have hjn : j.1 + 1 ≤ n := le_trans hj hk
      calc
        f' (hA.generator j) = t' j := hf'gen j
        _ = t j := by
          show (if h : j.1 + 1 ≤ n then t j
            else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h') else 0) = _
          rw [dite_eq_left hjn]
        _ = f (hA.generator j) := (hgen j hjn).symm
    have hnew (j : Σ k : ℕ, hA.indices k)
        (hdeg : j.1 + 1 = n + 1) :
        dB (t' j) = f (dA (hA.generator j)) := by
      have hnot : ¬ j.1 + 1 ≤ n := by omega
      have htval : t' j = Classical.choose (hLift j hdeg) := by
        show (if h : j.1 + 1 ≤ n then t j
          else if h' : j.1 + 1 = n + 1 then Classical.choose (hLift j h') else 0) = _
        rw [dite_eq_right hnot, dite_eq_left hdeg]
      rw [htval]
      exact (Classical.choose_spec (hLift j hdeg)).2
    have hgenChain : ∀ j, j.1 + 1 ≤ n + 1 →
        dB (f' (hA.generator j)) = f' (dA (hA.generator j)) := by
      intro j hj
      by_cases hjn : j.1 + 1 ≤ n
      · have hgenGrade : hA.generator j ∈ 𝒜 (j.1 + 1) := hA.generator_mem j
        have hdiffGrade := differential_generator_mem 𝒜 γA dA ι hA j
        rw [hEqGrade (j.1 + 1) hjn hgenGrade, hEqGrade j.1 (by omega) hdiffGrade]
        exact hchain (j.1 + 1) hjn (hA.generator j) hgenGrade
      · have hdeg : j.1 + 1 = n + 1 := by omega
        have hdiffGrade : dA (hA.generator j) ∈ 𝒜 n := by
          simpa [show j.1 = n by omega] using differential_generator_mem 𝒜 γA dA ι hA j
        have hright := hEqGrade n (Nat.le_refl n) hdiffGrade
        calc
          dB (f' (hA.generator j)) = dB (t' j) := by rw [hf'gen j]
          _ = f (dA (hA.generator j)) := hnew j hdeg
          _ = f' (dA (hA.generator j)) := hright.symm
    have hf'coeffChain : ∀ p, dB (f' (ι p)) = f' (dA (ι p)) := fun p =>
      dgaMap_chain_of_mem_gradeZero 𝒜 ℬ dA dB f' hf'grade (hA.coefficient_mem p)
    have hchain' : ∀ k, k ≤ n + 1 → ∀ a, a ∈ 𝒜 k →
        dB (f' a) = f' (dA a) := fun k hk a ha =>
      dgaMap_chain_on_grade_from_generators 𝒜 ℬ γA γB dA dB ι hA f'
        hf'grade hf'coeffChain hf'dpow k
        (fun j hj => hgenChain j (le_trans hj hk)) ha
    exact ⟨t', ⟨f', ⟨fun j _ => ht' j, hf'coeff,
      fun j _ => hf'gen j, hf'grade, hf'dpow, hchain'⟩, trivial⟩⟩
  let stages : (n : ℕ) → StageData n := Nat.rec base step
  have hstep_keep (n : ℕ) (s : StageData n) (j : Σ k : ℕ, hA.indices k)
      (hj : j.1 + 1 ≤ n) : (step n s).1 j = s.1 j := by
    rcases s with ⟨t, f, hp⟩
    show (step n ⟨t, ⟨f, hp⟩⟩).1 j = t j
    simp [step, hj]
  have hstable : ∀ n (j : Σ k : ℕ, hA.indices k), j.1 + 1 ≤ n →
      (stages n).1 j = (stages (j.1 + 1)).1 j := by
    intro n
    induction n with
    | zero =>
        intro j hj
        omega
    | succ n ih =>
        intro j hj
        by_cases hjn : j.1 + 1 ≤ n
        · have hcopy : (stages (n + 1)).1 j = (stages n).1 j := by
            show (step n (stages n)).1 j = (stages n).1 j
            exact hstep_keep n (stages n) j hjn
          rw [show n + 1 = Nat.succ n by omega, hcopy]
          exact ih j hjn
        · have hjeq : j.1 + 1 = n + 1 := by omega
          rw [show n + 1 = Nat.succ n by omega, hjeq]
  let tFinal : (Σ k : ℕ, hA.indices k) → B :=
    fun j => (stages (j.1 + 1)).1 j
  have htFinal : ∀ j, tFinal j ∈ ℬ (j.1 + 1) := by
    intro j
    have hs := (stages (j.1 + 1)).2.2.1.1 j
    simpa [tFinal] using hs
  obtain ⟨φ, ⟨hφcoeff, hφgen, hφgrade, hφdpow⟩, _⟩ :=
    existsUnique_gradedDividedPowerPolynomial_map
      𝒜 γA ι hA ℬ γB fP hfPgrade tFinal htFinal
  have hφeqStage (n : ℕ) (k : ℕ) (hk : k ≤ n) {a : A}
      (ha : a ∈ 𝒜 k) : φ a = (stages n).2.1 a := by
    let fₙ := (stages n).2.1
    let tₙ := (stages n).1
    have hn := (stages n).2.2.1
    rcases hn with ⟨htₙ, hcoeffₙ, hgenₙ, hgradeₙ, hdpowₙ, hchainₙ⟩
    refine gradedAlgHom_eq_on_grade 𝒜 ℬ γA γB ι hA φ fₙ
      (fun p => by rw [hφcoeff p, hcoeffₙ p]) hφgrade hgradeₙ hφdpow hdpowₙ k
      (fun j hj => ?_) ha
    calc
      φ (hA.generator j) = tFinal j := hφgen j
      _ = tₙ j := by simpa [tFinal, tₙ] using (hstable n j (le_trans hj hk)).symm
      _ = fₙ (hA.generator j) := (hgenₙ j (le_trans hj hk)).symm
  have hφgenChain : ∀ j,
      dB (φ (hA.generator j)) = φ (dA (hA.generator j)) := by
    intro j
    let n := j.1 + 1
    have hs := (stages n).2.2.1
    rcases hs with ⟨htₙ, hcoeffₙ, hgenₙ, hgradeₙ, hdpowₙ, hchainₙ⟩
    have hgenGrade : hA.generator j ∈ 𝒜 n := by
      simpa [n] using hA.generator_mem j
    have hdiffGrade := differential_generator_mem 𝒜 γA dA ι hA j
    have hleft := hφeqStage n n (Nat.le_refl n) hgenGrade
    have hright := hφeqStage n j.1 (by dsimp [n]; omega) hdiffGrade
    have hchain := hchainₙ n (Nat.le_refl n) (hA.generator j) hgenGrade
    calc
      dB (φ (hA.generator j)) = dB ((stages n).2.1 (hA.generator j)) :=
        congrArg dB hleft
      _ = (stages n).2.1 (dA (hA.generator j)) := hchain
      _ = φ (dA (hA.generator j)) := hright.symm
  have hcoeffChain : ∀ p, dB (φ (ι p)) = φ (dA (ι p)) := fun p =>
    dgaMap_chain_of_mem_gradeZero 𝒜 ℬ dA dB φ hφgrade (hA.coefficient_mem p)
  have hchainAll (a : A) : dB (φ a) = φ (dA a) := by
    obtain ⟨S, hS⟩ := hA.finite_support a
    exact dgaMap_chain_on_finiteVariableStage_element 𝒜 ℬ γA γB dA dB ι hA φ
      hφgrade hcoeffChain hφdpow S (fun j hj => hφgenChain j) hS
  have hquotient : ∀ a : A,
      φ₀ (cA.mk' a) = cB.mk' (φ a) := by
    intro a
    let F : A →ₐ[R] cB.Quotient := φ₀.comp qA
    let G : A →ₐ[R] cB.Quotient := qB.comp φ
    have hpos : ∀ {m : ℕ} {y : A}, 0 < m → y ∈ 𝒜 m → φ₀ (cA.mk' y) = cB.mk' (φ y) := by
      intro m y hm hy
      have hsrc := zerothHomology_mk'_positive_eq_zero 𝒜 dA hm hy
      have htar := zerothHomology_mk'_positive_eq_zero ℬ dB hm (hφgrade m _ hy)
      rw [show cA.mk' y = 0 from hsrc, show cB.mk' (φ y) = 0 from htar]
      simp
    obtain ⟨S, hS⟩ := hA.finite_support a
    refine ringHom_eq_on_finiteVariableStage γA ι hA.generator F.toRingHom G.toRingHom S
      (fun p => ?_) (fun j _ => ?_) (fun j _ m => ?_) hS
    · show φ₀ (cA.mk' (ι p)) = cB.mk' (φ (ι p))
      rw [hφcoeff p, hfPquot p]
    · exact hpos (m := j.1 + 1) (Nat.zero_lt_succ _) (hA.generator_mem j)
    · show φ₀ (cA.mk' (γA.dpow m (hA.generator j))) =
        cB.mk' (φ (γA.dpow m (hA.generator j)))
      by_cases hp : hA.generator j ∈ positiveEvenPart 𝒜
      · by_cases hm : m = 0
        · subst m
          rw [γA.dpow_zero hp]
          simp [cA, cB]
        · rcases homogeneous_mem_positiveEven_degree 𝒜
            (hA.generator_mem j) hp with ⟨k, hk⟩ | hzero
          · have hkpos : 0 < k := by
              have hjpos : 0 < j.1 + 1 := Nat.zero_lt_succ _
              omega
            refine hpos (m := 2 * m * k)
              (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hm)) hkpos) ?_
            apply γA.dpow_mem_grade hm hp
            simpa [hk, two_mul] using hA.generator_mem j
          · have hdpow : γA.dpow m (hA.generator j) = 0 := by
              rw [hzero]
              by_cases hmone : m = 1
              · subst m
                simp
              · simpa using γA.dpow_mul_odd (n := m) (d := 0) (e := 0)
                  (by omega) ((𝒜 1).zero_mem) ((𝒜 1).zero_mem)
            rw [hdpow]
            simp [cA, cB]
      · rw [γA.dpow_null hp]
        simp [cA, cB]
  exact ⟨φ, hφgrade, fun a => (hchainAll a).symm, hφdpow, hquotient⟩

end DividedPowers.TateResolution

end
