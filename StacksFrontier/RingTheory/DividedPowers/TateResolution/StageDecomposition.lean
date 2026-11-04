module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial

/-!
# Coordinates on a successor stage of a graded divided-power polynomial algebra

A graded divided-power polynomial algebra is the directed union of its finite-variable stages,
and adjoining one variable to a stage is an odd-variable or divided-power one-variable
extension. Accordingly, an element of the stage at `S ∪ {j}` is a polynomial in the new variable
with coefficients in the stage at `S`, and its coefficients are unique.

In odd degree the polynomial is `b₀ + b₁ T j` with two coefficients. In even degree it is a
finite sum `∑ aₙ γₙ (T j)` of divided powers of the new variable.

## Main results

* `DividedPowers.TateResolution.exists_coefficient_of_mem_stage_empty`: an element of the stage
  at the empty index set lies in the image of the coefficient algebra.
* `DividedPowers.TateResolution.stage_insert_odd_decomposition`: an element of an odd successor
  stage is `b₀ + b₁ T j` for unique `b₀`, `b₁` in the previous stage.
* `DividedPowers.TateResolution.stage_insert_even_decomposition`: an element of an even successor
  stage is `∑ aₙ γₙ (T j)` for unique `aₙ` in the previous stage.

## References

* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : P →ₐ[R] A}

/-- An element of the finite stage at an index set with no members lies in the image of `ι`. -/
public theorem exists_coefficient_of_mem_stage_empty
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι)
    {S : Finset (Σ n : ℕ, hp.indices n)} (hS : ∀ k, k ∉ S)
    {b : A} (hb : b ∈ finiteVariableStage γ ι hp.generator S) :
    ∃ p : P, b = ι p := by
  obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem hS
  rw [finiteVariableStage_empty 𝒜 γ ι hp.generator] at hb
  have hrange : Subring.closure (Set.range ι) = (ι : P →+* A).range := by
    rw [show Set.range ι = ((ι : P →+* A).range : Set A) from rfl, Subring.closure_eq]
  rw [hrange] at hb
  exact ⟨hb.choose, hb.choose_spec.symm⟩

/-- **Coordinates on an odd successor stage.** Adjoining a variable of odd degree `j.1 + 1` to
the stage at `S` produces exactly the elements `b₀ + b₁ T j` with `b₀` and `b₁` in the stage at
`S`, and the pair `(b₀, b₁)` is uniquely determined. -/
public theorem stage_insert_odd_decomposition
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι)
    (S U : Finset (Σ n : ℕ, hp.indices n)) (j : Σ n : ℕ, hp.indices n) (hj : j ∉ S)
    (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S) (hodd : Odd (j.1 + 1)) :
    (∀ b ∈ finiteVariableStage γ ι hp.generator U,
        ∃ b₀ b₁ : A, b₀ ∈ finiteVariableStage γ ι hp.generator S ∧
          b₁ ∈ finiteVariableStage γ ι hp.generator S ∧
          b = b₀ + b₁ * hp.generator j) ∧
      (∀ b₀ b₁ : A, b₀ ∈ finiteVariableStage γ ι hp.generator S →
        b₁ ∈ finiteVariableStage γ ι hp.generator S →
        b₀ + b₁ * hp.generator j = 0 → b₀ = 0 ∧ b₁ = 0) := by
  classical
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, -, hoddpart, -⟩ := hp.successor S j hj
  let _ : Algebra R (finiteVariableStage γ ι hp.generator S) := aS
  let _ : GradedAlgebra Sᵢ := gS
  let _ : IsStrictlyGradedComm Sᵢ := cS
  obtain ⟨e, hincl, hgen, -, -⟩ := hoddpart hodd
  have hUeq : U = @insert _ _ (@Finset.instInsert _ (Classical.decEq _)) j S := by
    ext k; simp [hU]
  let g : OddVariableExtension Sᵢ (j.1 + 1) →+* A :=
    (Subring.subtype _).comp e.toRingHom
  have hginc : ∀ u : finiteVariableStage γ ι hp.generator S,
      g (OddVariableExtension.inclusion Sᵢ (j.1 + 1) u) = (u : A) := hincl
  have hggen : g (OddVariableExtension.generator Sᵢ (j.1 + 1)) = hp.generator j := hgen
  refine ⟨fun b hb => ?_, fun b₀ b₁ h0 h1 h => ?_⟩
  · rw [hUeq] at hb
    set x := e.symm ⟨b, hb⟩ with hxdef
    refine ⟨((OddVariableExtension.coefficients Sᵢ (j.1 + 1) x).1 : A),
      ((OddVariableExtension.coefficients Sᵢ (j.1 + 1) x).2 : A),
      (OddVariableExtension.coefficients Sᵢ (j.1 + 1) x).1.2,
      (OddVariableExtension.coefficients Sᵢ (j.1 + 1) x).2.2, ?_⟩
    have hgx : g x = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    conv_lhs => rw [← hgx,
      ← OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator Sᵢ (j.1 + 1) x]
    rw [map_add, map_mul]
    exact congrArg₂ _ (hginc _) (congrArg₂ _ (hginc _) hggen)
  · set u₀ : finiteVariableStage γ ι hp.generator S := ⟨b₀, h0⟩ with hu₀
    set u₁ : finiteVariableStage γ ι hp.generator S := ⟨b₁, h1⟩ with hu₁
    set x : OddVariableExtension Sᵢ (j.1 + 1) :=
      OddVariableExtension.inclusion Sᵢ (j.1 + 1) u₀ +
        OddVariableExtension.inclusion Sᵢ (j.1 + 1) u₁ *
          OddVariableExtension.generator Sᵢ (j.1 + 1) with hxdef
    have hgx : g x = 0 := by rwa [hxdef, map_add, map_mul, hginc u₀, hginc u₁, hggen]
    have hx0 : x = 0 := (map_eq_zero_iff e e.injective).1 (Subtype.ext hgx)
    have hcoeff : OddVariableExtension.coefficients Sᵢ (j.1 + 1) x = (u₀, u₁) := by
      rw [hxdef]; simp
    rw [hx0] at hcoeff
    simp only [map_zero, Prod.ext_iff] at hcoeff
    exact ⟨congrArg Subtype.val hcoeff.1.symm, congrArg Subtype.val hcoeff.2.symm⟩

/-- **Coordinates on an even successor stage.** Adjoining a variable of even degree `j.1 + 1` to
the stage at `S` produces exactly the finite sums `∑ aₙ γₙ (T j)` with every `aₙ` in the stage at
`S`, and the coefficients `aₙ` are uniquely determined. -/
public theorem stage_insert_even_decomposition
    (hp : GradedDividedPowerPolynomial 𝒜 γ ι)
    (S U : Finset (Σ n : ℕ, hp.indices n)) (j : Σ n : ℕ, hp.indices n) (hj : j ∉ S)
    (hU : ∀ k, k ∈ U ↔ k = j ∨ k ∈ S) (heven : Even (j.1 + 1)) :
    (∀ b ∈ finiteVariableStage γ ι hp.generator U,
        ∃ (s : Finset ℕ) (a : ℕ → A),
          (∀ n, a n ∈ finiteVariableStage γ ι hp.generator S) ∧
          b = ∑ n ∈ s, a n * γ.dpow n (hp.generator j)) ∧
      (∀ (s : Finset ℕ) (a : ℕ → A),
        (∀ n, a n ∈ finiteVariableStage γ ι hp.generator S) →
        ∑ n ∈ s, a n * γ.dpow n (hp.generator j) = 0 → ∀ n ∈ s, a n = 0) := by
  classical
  obtain ⟨aS, -, Sᵢ, gS, cS, δS, -, -, hevenpart⟩ := hp.successor S j hj
  let _ : Algebra R (finiteVariableStage γ ι hp.generator S) := aS
  let _ : GradedAlgebra Sᵢ := gS
  let _ : IsStrictlyGradedComm Sᵢ := cS
  let _ : Fact (Even (j.1 + 1)) := ⟨heven⟩
  obtain ⟨e, hincl, hgen, -, hdpow⟩ := hevenpart heven
  have hUeq : U = @insert _ _ (@Finset.instInsert _ (Classical.decEq _)) j S := by
    ext k; simp [hU]
  let g : EvenVariableAlgebra (finiteVariableStage γ ι hp.generator S) →+* A :=
    (Subring.subtype _).comp e.toRingHom
  have hone : (1 : finiteVariableStage γ ι hp.generator S) ∈ evenPart Sᵢ :=
    Submodule.mem_iSup_of_mem 0 (by simpa using SetLike.one_mem_graded Sᵢ)
  have hpos : EvenVariableAlgebra.monomial 1 (1 : finiteVariableStage γ ι hp.generator S) ∈
      positiveEvenPart (EvenVariableAlgebra.grade Sᵢ (j.1 + 1)) :=
    EvenVariableAlgebra.monomial_mem_positiveEvenPart heven (Nat.zero_lt_succ j.1)
      Nat.one_pos hone
  have hmono1 : ∀ n : ℕ, g (EvenVariableAlgebra.monomial n
      (1 : finiteVariableStage γ ι hp.generator S)) = γ.dpow n (hp.generator j) := by
    intro n
    rw [← hgen, hdpow n _ hpos,
      dpow_monomial_one (j.1 + 1) (Nat.zero_lt_succ j.1) δS n 1 Nat.one_pos]
    simp only [mul_one, dividedPowerMonomialCoefficient_one_right, one_smul]
    rfl
  have hmono : ∀ (n : ℕ) (u : finiteVariableStage γ ι hp.generator S),
      g (EvenVariableAlgebra.monomial n u) = (u : A) * γ.dpow n (hp.generator j) := by
    intro n u
    have hsplit : EvenVariableAlgebra.monomial n u =
        EvenVariableAlgebra.coeffEmbedding u *
          EvenVariableAlgebra.monomial n (1 : finiteVariableStage γ ι hp.generator S) := by
      rw [EvenVariableAlgebra.coeffEmbedding_apply, EvenVariableAlgebra.monomial_mul_monomial]
      simp
    rw [hsplit, map_mul, hmono1]
    exact congrArg₂ _ (hincl u) rfl
  refine ⟨fun b hb => ?_, fun s a ha h n hn => ?_⟩
  · rw [hUeq] at hb
    set x := e.symm ⟨b, hb⟩ with hxdef
    refine ⟨x.coeff.support,
      fun n => ((x.coeff n : finiteVariableStage γ ι hp.generator S) : A),
      fun n => (x.coeff n).2, ?_⟩
    have hgx : g x = b := congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    calc b = g x := hgx.symm
      _ = g (∑ n ∈ x.coeff.support, EvenVariableAlgebra.monomial n (x.coeff n)) := by
          rw [EvenVariableAlgebra.sum_monomial]
      _ = ∑ n ∈ x.coeff.support, g (EvenVariableAlgebra.monomial n (x.coeff n)) := map_sum _ _ _
      _ = _ := Finset.sum_congr rfl fun n _ => hmono n (x.coeff n)
  · set x : EvenVariableAlgebra (finiteVariableStage γ ι hp.generator S) :=
      ∑ m ∈ s, EvenVariableAlgebra.monomial m ⟨a m, ha m⟩ with hxdef
    have hgx : g x = 0 := by
      rwa [hxdef, map_sum, Finset.sum_congr rfl fun m _ => hmono m ⟨a m, ha m⟩]
    have hx0 : x = 0 := (map_eq_zero_iff e e.injective).1 (Subtype.ext hgx)
    let C : EvenVariableAlgebra (finiteVariableStage γ ι hp.generator S) →+
        (ℕ →₀ finiteVariableStage γ ι hp.generator S) :=
      { toFun := EvenVariableAlgebra.coeff
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hCx : C x = ∑ m ∈ s, Finsupp.single m (⟨a m, ha m⟩ :
        finiteVariableStage γ ι hp.generator S) := by
      rw [hxdef, map_sum]
      rfl
    rw [hx0, map_zero] at hCx
    have hval := DFunLike.congr_fun hCx n
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply,
      Finsupp.single_apply] at hval
    rw [Finset.sum_ite_eq' s n (fun m => (⟨a m, ha m⟩ :
      finiteVariableStage γ ι hp.generator S))] at hval
    have hzero : (⟨a n, ha n⟩ : finiteVariableStage γ ι hp.generator S) = 0 := by
      simpa [hn] using hval.symm
    exact congrArg Subtype.val hzero

end DividedPowers.TateResolution

end
