module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage.DirectedColimit

/-!
# Divided powers on the finite-variable stages

Every finite-variable stage is closed under the divided powers of the ambient algebra, divided
powers on the ambient algebra are determined by their restriction to the coefficients and by
their values on the variables, and compatible divided powers on the members of a directed system
of graded algebras extend uniquely to a graded colimit of that system.

## Main results

* `DividedPowers.TateResolution.finiteVariableStage_dpow_mem` — every stage is closed under the
  divided powers of `C`.
* `DividedPowers.TateResolution.existsUnique_dividedPowerStructure_of_finiteStages` — compatible
  divided powers on the stages of a directed system extend uniquely to a graded colimit of it.
* `DividedPowers.TateResolution.dividedPowerStructure_unique_of_generators` — divided powers on
  `C` are determined by their restriction to the coefficients and their values on the variables.
* `DividedPowers.TateResolution.positiveEven_homogeneous_eq_zero_or_grade` — a homogeneous
  element of the positive even part either vanishes or has positive even degree.
* `DividedPowers.TateResolution.algHom_mem_positiveEvenPart` and
  `DividedPowers.TateResolution.exists_lift_positiveEvenPart` — the positive even part is
  preserved by grading-preserving algebra maps, and an element of the positive even part of a
  directed union is the image of such an element from some stage.

## Implementation notes

Closure under divided powers and the directed colimit property are recorded as two separate
results rather than packaged into one statement about a filtered divided-power subalgebra,
because the uniqueness argument uses them separately: the colimit property reduces an identity
on `C` to identities on the individual stages, while closure under divided powers is what makes
those identities statements about elements of a single stage. Both are proved by exhibiting the
set of elements satisfying the relevant property as a subring containing the generators, and the
homogeneous-component lemmas are needed because divided powers are only defined on the positive
even part, so an element of a stage must first be decomposed into its homogeneous pieces.

The colimit hypotheses of
`DividedPowers.TateResolution.existsUnique_dividedPowerStructure_of_finiteStages` are stated
elementwise — homogeneous elements lift to some stage, and two stage elements with the same
image already agree at a later stage — rather than through a colimit construction, so that the
result applies both to a concrete directed union of subrings and to an abstract direct limit.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

/-- An algebra map which sends each homogeneous piece into the homogeneous piece of the same
degree sends a sum of homogeneous pieces of the degrees `e d` into the corresponding sum. -/
private theorem algHom_mem_iSup_grade
    {R : Type u} {A : Type v} {B : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (Aᵢ : ℕ → Submodule R A) (Bᵢ : ℕ → Submodule R B) (e : ℕ → ℕ)
    (φ : A →ₐ[R] B)
    (hgrade : ∀ (m : ℕ) (x : A), x ∈ Aᵢ m → φ x ∈ Bᵢ m)
    {x : A} (hx : x ∈ ⨆ d, Aᵢ (e d)) :
    φ x ∈ ⨆ d, Bᵢ (e d) := by
  refine Submodule.iSup_induction (p := fun d : ℕ => Aᵢ (e d))
    (motive := fun x => φ x ∈ ⨆ d, Bᵢ (e d)) hx ?_ ?_ ?_
  · intro d x hx
    exact Submodule.mem_iSup_of_mem d (hgrade (e d) x hx)
  · simp
  · intro x y hx hy
    simpa only [map_add] using (⨆ d, Bᵢ (e d)).add_mem hx hy

/-- An algebra map which sends each homogeneous piece into the homogeneous piece of the same
degree sends the positive even part into the positive even part. -/
public theorem algHom_mem_positiveEvenPart
    {R : Type u} {A : Type v} {B : Type z}
    [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (Aᵢ : ℕ → Submodule R A) (Bᵢ : ℕ → Submodule R B)
    (φ : A →ₐ[R] B)
    (hgrade : ∀ (m : ℕ) (x : A), x ∈ Aᵢ m → φ x ∈ Bᵢ m)
    {x : A} (hx : x ∈ positiveEvenPart Aᵢ) :
    φ x ∈ positiveEvenPart Bᵢ :=
  algHom_mem_iSup_grade Aᵢ Bᵢ (fun d => 2 * (d + 1)) φ hgrade hx

/-- In a directed system of graded algebras mapping compatibly to a graded algebra whose
homogeneous elements all lift to some stage, every element of a sum of homogeneous pieces of the
degrees `e d` of the target is the image of an element of the corresponding sum of a single
stage. -/
private theorem exists_lift_iSup_grade
    {R : Type u} [CommRing R] {I : Type w} [LE I] [IsDirectedOrder I] [Nonempty I]
    (B : I → Type v) [stageRing : ∀ S, Ring (B S)]
    [stageAlgebra : ∀ S, Algebra R (B S)]
    (Bᵢ : (S : I) → ℕ → Submodule R (B S))
    {C : Type z} [Ring C] [Algebra R C]
    (Cᵢ : ℕ → Submodule R C) (e : ℕ → ℕ)
    (transition : ∀ {S T : I}, S ≤ T → B S →ₐ[R] B T)
    (ι : (S : I) → B S →ₐ[R] C)
    (hι : ∀ {S T : I} (h : S ≤ T) (x : B S),
      ι T (transition h x) = ι S x)
    (htransition_grade : ∀ {S T : I} (h : S ≤ T)
      (m : ℕ) (x : B S), x ∈ Bᵢ S m → transition h x ∈ Bᵢ T m)
    (hgrade_lift : ∀ (m : ℕ) (x : C), x ∈ Cᵢ m →
      ∃ (S : I) (y : B S), y ∈ Bᵢ S m ∧ ι S y = x)
    {x : C} (hx : x ∈ ⨆ d, Cᵢ (e d)) :
    ∃ (S : I) (y : B S), y ∈ (⨆ d, Bᵢ S (e d)) ∧ ι S y = x := by
  refine Submodule.iSup_induction (p := fun d : ℕ => Cᵢ (e d))
    (motive := fun x => ∃ (S : I) (y : B S),
      y ∈ (⨆ d, Bᵢ S (e d)) ∧ ι S y = x) hx ?_ ?_ ?_
  · intro d x hx
    obtain ⟨S, y, hy, hxy⟩ := hgrade_lift (e d) x hx
    exact ⟨S, y, Submodule.mem_iSup_of_mem d hy, hxy⟩
  · obtain ⟨S₀⟩ := (inferInstance : Nonempty I)
    exact ⟨S₀, 0, Submodule.zero_mem _, map_zero _⟩
  · intro x y ihx ihy
    obtain ⟨S, xS, hxS, hix⟩ := ihx
    obtain ⟨T, yT, hyT, hiy⟩ := ihy
    obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
    refine ⟨U, transition hSU xS + transition hTU yT, Submodule.add_mem _
      (algHom_mem_iSup_grade (Bᵢ S) (Bᵢ U) e _ (htransition_grade hSU) hxS)
      (algHom_mem_iSup_grade (Bᵢ T) (Bᵢ U) e _ (htransition_grade hTU) hyT), ?_⟩
    rw [map_add, hι hSU, hι hTU, hix, hiy]

/-- In a directed system of graded algebras mapping compatibly to a graded algebra whose
homogeneous elements all lift to some stage, every element of the positive even part of the
target is the image of an element of the positive even part of a single stage. -/
public theorem exists_lift_positiveEvenPart
    {R : Type u} [CommRing R] {I : Type w} [LE I] [IsDirectedOrder I] [Nonempty I]
    (B : I → Type v) [stageRing : ∀ S, Ring (B S)]
    [stageAlgebra : ∀ S, Algebra R (B S)]
    (Bᵢ : (S : I) → ℕ → Submodule R (B S))
    {C : Type z} [Ring C] [Algebra R C]
    (Cᵢ : ℕ → Submodule R C)
    (transition : ∀ {S T : I}, S ≤ T → B S →ₐ[R] B T)
    (ι : (S : I) → B S →ₐ[R] C)
    (hι : ∀ {S T : I} (h : S ≤ T) (x : B S),
      ι T (transition h x) = ι S x)
    (htransition_grade : ∀ {S T : I} (h : S ≤ T)
      (m : ℕ) (x : B S), x ∈ Bᵢ S m → transition h x ∈ Bᵢ T m)
    (hgrade_lift : ∀ (m : ℕ) (x : C), x ∈ Cᵢ m →
      ∃ (S : I) (y : B S), y ∈ Bᵢ S m ∧ ι S y = x)
    {x : C} (hx : x ∈ positiveEvenPart Cᵢ) :
    ∃ (S : I) (y : B S),
      y ∈ positiveEvenPart (Bᵢ S) ∧ ι S y = x :=
  exists_lift_iSup_grade B Bᵢ Cᵢ (fun d => 2 * (d + 1)) transition ι hι htransition_grade
    hgrade_lift hx

private theorem positiveEvenPart_mem_grade_zero_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x : A} (hx : x ∈ positiveEvenPart Aᵢ) (h0 : x ∈ Aᵢ 0) : x = 0 := by
  have hproj : GradedAlgebra.proj Aᵢ 0 x = 0 := by
    refine Submodule.iSup_induction (p := fun d : ℕ => Aᵢ (2 * (d + 1)))
      (motive := fun x => GradedAlgebra.proj Aᵢ 0 x = 0) hx ?_ ?_ ?_
    · intro d x hx
      rw [GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_ne Aᵢ hx (by omega)]
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy, zero_add]
  have hproj0 : GradedAlgebra.proj Aᵢ 0 x = x := by
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same Aᵢ h0]
  exact hproj0.symm.trans hproj

private def gradedComponent
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (x : A) (m : ℕ) : A :=
  (DirectSum.decompose Aᵢ x m : Aᵢ m)

private theorem algHom_gradedComponent
    {R : Type u} {A : Type v} {C : Type z}
    [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    (ι : A →ₐ[R] C)
    (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (a : A) (m : ℕ) :
    gradedComponent Cᵢ (ι a) m = ι (gradedComponent Aᵢ a m) := by
  let φ : Aᵢ →+*ᵍ Cᵢ :=
    { toRingHom := ι.toRingHom
      map_mem := by
        intro i x hx
        exact hgrade i x hx }
  change (DirectSum.decompose Cᵢ (ι a) m : C) =
    ι (DirectSum.decompose Aᵢ a m : A)
  exact (GradedRingHom.map_directSumDecompose
    (𝒜 := Aᵢ) (ℬ := Cᵢ) φ (x := a) (i := m)).symm

private theorem gradedComponent_mem
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (x : A) (m : ℕ) :
    gradedComponent Aᵢ x m ∈ Aᵢ m :=
  (DirectSum.decompose Aᵢ x m).property

private theorem gradedComponent_add
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (x y : A) (m : ℕ) :
    gradedComponent Aᵢ (x + y) m = gradedComponent Aᵢ x m + gradedComponent Aᵢ y m := by
  simp [gradedComponent]

/-- A homogeneous element of degree `d` lying in the positive even part is either zero or has
`d` of the form `2 * (k + 1)`. -/
public theorem positiveEven_homogeneous_eq_zero_or_grade
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x : A} {d : ℕ} (hx : x ∈ Aᵢ d) (hpos : x ∈ positiveEvenPart Aᵢ) :
    x = 0 ∨ ∃ k : ℕ, d = 2 * (k + 1) := by
  by_cases hd : ∃ k : ℕ, d = 2 * (k + 1)
  · exact Or.inr hd
  · have hproj : gradedComponent Aᵢ x d = 0 := by
      refine Submodule.iSup_induction (p := fun k : ℕ => Aᵢ (2 * (k + 1)))
        (motive := fun y => gradedComponent Aᵢ y d = 0) hpos ?_ ?_ ?_
      · intro k y hy
        rw [gradedComponent]
        exact DirectSum.decompose_of_mem_ne Aᵢ hy (by
          intro h
          exact hd ⟨k, h.symm⟩)
      · simp [gradedComponent]
      · intro y z ihy ihz
        rw [gradedComponent_add, ihy, ihz, zero_add]
    have hprojx : gradedComponent Aᵢ x d = x := by
      rw [gradedComponent, DirectSum.decompose_of_mem_same Aᵢ hx]
    exact Or.inl (hprojx.symm.trans hproj)

private theorem gradedComponent_neg
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (x : A) (m : ℕ) :
    gradedComponent Aᵢ (-x) m = -gradedComponent Aᵢ x m := by
  change ((DirectSum.decompose Aᵢ (-x) m : Aᵢ m) : A) = _
  rw [DirectSum.decompose_neg]
  exact Submodule.coe_neg (Aᵢ m) ((DirectSum.decompose Aᵢ x) m)

private theorem gradedComponent_mul
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (x y : A) (m : ℕ) :
    gradedComponent Aᵢ (x * y) m =
      ∑ ij ∈ Finset.antidiagonal m,
        gradedComponent Aᵢ x ij.1 * gradedComponent Aᵢ y ij.2 := by
  classical
  change ((DirectSum.decompose Aᵢ (x * y) m : Aᵢ m) : A) = _
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  simp [gradedComponent]

/-- Positive divided powers of zero vanish. -/
private theorem dpow_zero_arg_of_ne_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (δ : DividedPowerStructure Aᵢ) {n : ℕ} (hn : n ≠ 0) : δ.dpow n (0 : A) = 0 := by
  simpa [zero_pow hn] using
    δ.dpow_mul_even hn (evenPart Aᵢ).zero_mem (positiveEvenPart Aᵢ).zero_mem

private theorem dpow_zero_mem_subring
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (δ : DividedPowerStructure Aᵢ) (S : Subring A) (n : ℕ) :
    δ.dpow n 0 ∈ S := by
  by_cases hn : n = 0
  · subst n
    rw [δ.dpow_zero (positiveEvenPart Aᵢ).zero_mem]
    exact S.one_mem
  · rw [dpow_zero_arg_of_ne_zero Aᵢ δ hn]
    exact S.zero_mem

private theorem gradedComponent_eq_self_or_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    {x : A} {d m : ℕ} (hx : x ∈ Aᵢ d) :
    gradedComponent Aᵢ x m = if m = d then x else 0 := by
  unfold gradedComponent
  split_ifs with hmd
  · subst m
    exact DirectSum.decompose_of_mem_same Aᵢ hx
  · exact DirectSum.decompose_of_mem_ne Aᵢ hx (Ne.symm hmd)

/-- Every divided power of a homogeneous element is homogeneous. -/
private theorem exists_grade_dpow
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (δ : DividedPowerStructure Aᵢ) {x : A} {d : ℕ} (hx : x ∈ Aᵢ d) (k : ℕ) :
    ∃ e : ℕ, δ.dpow k x ∈ Aᵢ e := by
  by_cases hp : x ∈ positiveEvenPart Aᵢ
  · by_cases hk : k = 0
    · exact ⟨0, by rw [hk, δ.dpow_zero hp]; exact SetLike.GradedOne.one_mem⟩
    · rcases positiveEven_homogeneous_eq_zero_or_grade Aᵢ hx hp with hz | ⟨r, hr⟩
      · exact ⟨0, by rw [hz, dpow_zero_arg_of_ne_zero Aᵢ δ hk]; exact (Aᵢ 0).zero_mem⟩
      · exact ⟨2 * k * (r + 1), δ.dpow_mem_grade hk hp (by rw [← hr]; exact hx)⟩
  · exact ⟨0, by rw [δ.dpow_null hp]; exact (Aᵢ 0).zero_mem⟩

/-- The homogeneous components of an element of the positive even part lie in it. -/
private theorem gradedComponent_mem_positiveEvenPart
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] {x : A} (hx : x ∈ positiveEvenPart Aᵢ)
    (m : ℕ) : gradedComponent Aᵢ x m ∈ positiveEvenPart Aᵢ := by
  revert m
  refine Submodule.iSup_induction (p := fun k : ℕ => Aᵢ (2 * (k + 1)))
    (motive := fun y => ∀ m : ℕ, gradedComponent Aᵢ y m ∈ positiveEvenPart Aᵢ) hx ?_ ?_ ?_
  · intro k y hy m
    rw [gradedComponent_eq_self_or_zero Aᵢ hy]
    split_ifs with h
    · exact Submodule.mem_iSup_of_mem k hy
    · exact (positiveEvenPart Aᵢ).zero_mem
  · intro m
    simp [gradedComponent]
  · intro y z ihy ihz m
    rw [gradedComponent_add]
    exact (positiveEvenPart Aᵢ).add_mem (ihy m) (ihz m)

private theorem finiteVariableStage_gradedComponent_mem
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ] (δ : DividedPowerStructure Cᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (S : Finset J) (deg : J → ℕ)
    (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j : J, T j ∈ Cᵢ (deg j))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S) (m : ℕ) :
    gradedComponent Cᵢ x m ∈ finiteVariableStage δ ι T S := by
  classical
  let G : Set C := Set.range ι ∪ {y : C | ∃ j : J, j ∈ S ∧
    (y = T j ∨ ∃ n : ℕ, y = δ.dpow n (T j))}
  let Q := finiteVariableStage δ ι T S
  have hgenerator : ∀ y : C, y ∈ G → ∀ m : ℕ,
      gradedComponent Cᵢ y m ∈ Q := by
    intro y hy m
    rcases hy with hy | hy
    · obtain ⟨a, rfl⟩ := hy
      rw [algHom_gradedComponent Aᵢ Cᵢ ι hgrade a m]
      exact Subring.subset_closure (Or.inl (Set.mem_range_self _))
    · rcases hy with ⟨j, hj, hjx⟩
      rcases hjx with rfl | ⟨n, rfl⟩
      · have hmem : T j ∈ Q :=
          Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)
        rw [gradedComponent_eq_self_or_zero Cᵢ (hT j)]
        split_ifs with h
        · simpa using hmem
        · exact Q.zero_mem
      · have hmem : δ.dpow n (T j) ∈ Q :=
          Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨n, rfl⟩⟩)
        obtain ⟨e, he⟩ := exists_grade_dpow Cᵢ δ (hT j) n
        rw [gradedComponent_eq_self_or_zero Cᵢ he]
        split_ifs with h
        · exact hmem
        · exact Q.zero_mem
  let K : Subring C := {
    carrier := {y | ∀ m : ℕ, gradedComponent Cᵢ y m ∈ Q}
    zero_mem' := by
      intro m
      simp [gradedComponent]
    one_mem' := by
      intro m
      have hone : (1 : C) ∈ Cᵢ 0 := SetLike.GradedOne.one_mem
      rw [gradedComponent_eq_self_or_zero Cᵢ hone]
      split_ifs with h
      · simp
      · exact Q.zero_mem
    add_mem' := by
      intro y z hy hz m
      rw [gradedComponent_add]
      exact Q.add_mem (hy m) (hz m)
    neg_mem' := by
      intro y hy m
      rw [gradedComponent_neg]
      exact Q.neg_mem (hy m)
    mul_mem' := by
      intro y z hy hz m
      rw [gradedComponent_mul]
      exact Q.sum_mem fun ij hij => Q.mul_mem (hy ij.1) (hz ij.2)
  }
  have hGK : G ⊆ K := fun y hy => hgenerator y hy
  change gradedComponent Cᵢ x m ∈ Q
  have hxK : x ∈ K := Subring.closure_le.mpr hGK hx
  exact hxK m

/-- A product of homogeneous elements of total degree `2 * (k + 1)` lies in the positive even
part, and is either a product of two odd homogeneous elements, or of an even element and a
positive even one in some order. -/
private theorem homogeneous_mul_cases
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    {i j : ℕ} {x y : A} (hx : x ∈ Aᵢ i) (hy : y ∈ Aᵢ j) {k : ℕ} (hij : i + j = 2 * (k + 1)) :
    x * y ∈ positiveEvenPart Aᵢ ∧
      ((∃ d e : ℕ, x ∈ Aᵢ (2 * d + 1) ∧ y ∈ Aᵢ (2 * e + 1)) ∨
        (x ∈ evenPart Aᵢ ∧ y ∈ positiveEvenPart Aᵢ) ∨
        (y ∈ evenPart Aᵢ ∧ x ∈ positiveEvenPart Aᵢ ∧ x * y = y * x)) := by
  refine ⟨Submodule.mem_iSup_of_mem k (by rw [← hij]; exact SetLike.GradedMul.mul_mem hx hy), ?_⟩
  rcases Nat.even_or_odd i with ⟨a, ha⟩ | ⟨a, ha⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine Or.inr (Or.inr ⟨Submodule.mem_iSup_of_mem 0 hy,
        mem_positiveEvenPart_of_mem_grade Aᵢ (d := a) (by omega) (by rw [two_mul, ← ha]; exact hx),
        ?_⟩)
      rw [IsStrictlyGradedComm.graded_comm hx hy]
      simp
    · refine Or.inr (Or.inl ⟨Submodule.mem_iSup_of_mem a (by rw [two_mul, ← ha]; exact hx),
        mem_positiveEvenPart_of_mem_grade Aᵢ (d := k + 1 - a) (by omega) ?_⟩)
      convert hy using 2
      omega
  · exact Or.inl ⟨a, k - a, by rw [← ha]; exact hx, by convert hy using 2; omega⟩

private theorem dpow_mem_homogeneous_mul_subring
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (δ : DividedPowerStructure Aᵢ) (S : Subring A)
    {i j : ℕ} {x y : A} (hx : x ∈ Aᵢ i) (hy : y ∈ Aᵢ j)
    {k : ℕ} (hij : i + j = 2 * (k + 1))
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hxd : ∀ n, x ∈ positiveEvenPart Aᵢ → δ.dpow n x ∈ S)
    (hyd : ∀ n, y ∈ positiveEvenPart Aᵢ → δ.dpow n y ∈ S)
    (n : ℕ) : δ.dpow n (x * y) ∈ S := by
  obtain ⟨hpos, hcases⟩ := homogeneous_mul_cases Aᵢ hx hy hij
  by_cases hn0 : n = 0
  · rw [hn0, δ.dpow_zero hpos]
    exact S.one_mem
  by_cases hn1 : n = 1
  · rw [hn1, δ.dpow_one hpos]
    exact S.mul_mem hxS hyS
  rcases hcases with ⟨d, e, hxd', hye'⟩ | ⟨hxe, hyp⟩ | ⟨hye, hxp, hcomm⟩
  · rw [δ.dpow_mul_odd (by omega) hxd' hye']
    exact S.zero_mem
  · rw [δ.dpow_mul_even hn0 hxe hyp]
    exact S.mul_mem (S.pow_mem hxS n) (hyd n hyp)
  · rw [hcomm, δ.dpow_mul_even hn0 hye hxp]
    exact S.mul_mem (S.pow_mem hyS n) (hxd n hxp)

/-- A subring containing all divided powers of the summands contains all divided powers of a
finite sum of elements of the positive even part. -/
private theorem dpow_mem_finite_positive_sum
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
    (δ : DividedPowerStructure Aᵢ) (S : Subring A)
    {ι : Type*} (s : Finset ι) (f : ι → A)
    (hpos : ∀ i ∈ s, f i ∈ positiveEvenPart Aᵢ)
    (hdpow : ∀ i ∈ s, ∀ n, δ.dpow n (f i) ∈ S) (n : ℕ) :
    δ.dpow n (∑ i ∈ s, f i) ∈ S := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      simpa using dpow_zero_mem_subring Aᵢ δ S n
  | @insert a s has ih =>
      have htail : (∑ i ∈ s, f i) ∈ positiveEvenPart Aᵢ :=
        (positiveEvenPart Aᵢ).sum_mem (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
      rw [Finset.sum_insert has, δ.dpow_add (hpos a (Finset.mem_insert_self ..)) htail]
      exact S.sum_mem fun ij _ => S.mul_mem (hdpow a (Finset.mem_insert_self ..) ij.1)
        (ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
          (fun i hi => hdpow i (Finset.mem_insert_of_mem hi)) ij.2)

/-- Let a directed system of strictly graded-commutative graded algebras with divided powers,
indexed by a nonempty directed preorder, map compatibly to a strictly graded-commutative graded
algebra `C` in such a way that homogeneous elements of `C` lift to some stage and two stage
elements with the same image in `C` already agree at a later stage. Then `C` carries exactly one
divided power structure for which every stage map preserves divided powers.

The index order is an arbitrary nonempty directed one; the finite subsets of a set ordered by
inclusion, which is the indexing of the set-variable construction of Tag 0F4I, are the special
case `I = Finset J`, and an `ℕ`-indexed tower is the case `I = ℕ`. -/
@[stacks 0F4I "finite-stage extension"]
public theorem existsUnique_dividedPowerStructure_of_finiteStages
    {R : Type u} [CommRing R] {I : Type w} [LE I] [IsDirectedOrder I] [Nonempty I]
    (B : I → Type v)
    [stageRing : ∀ S, Ring (B S)]
    [stageAlgebra : ∀ S, Algebra R (B S)]
    (Bᵢ : (S : I) → ℕ → Submodule R (B S))
    [stageGraded : ∀ S, GradedAlgebra (Bᵢ S)]
    [stageComm : ∀ S, IsStrictlyGradedComm (Bᵢ S)]
    (γ : (S : I) → DividedPowerStructure (Bᵢ S))
    {C : Type z} [Ring C] [Algebra R C]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (transition : ∀ {S T : I}, S ≤ T → B S →ₐ[R] B T)
    (ι : (S : I) → B S →ₐ[R] C)
    (hι : ∀ {S T : I} (h : S ≤ T) (x : B S),
      ι T (transition h x) = ι S x)
    (hgrade : ∀ (S : I) (m : ℕ) (x : B S),
      x ∈ Bᵢ S m → ι S x ∈ Cᵢ m)
    (hgrade_lift : ∀ (m : ℕ) (x : C), x ∈ Cᵢ m →
      ∃ (S : I) (y : B S), y ∈ Bᵢ S m ∧ ι S y = x)
    (heq : ∀ (S T : I) (x : B S) (y : B T),
      ι S x = ι T y →
      ∃ U : I, ∃ (hS : S ≤ U) (hT : T ≤ U),
        transition hS x = transition hT y)
    (htransition_grade : ∀ {S T : I} (h : S ≤ T)
      (m : ℕ) (x : B S), x ∈ Bᵢ S m → transition h x ∈ Bᵢ T m)
    (htransition_dpow : ∀ {S T : I} (h : S ≤ T)
      (n : ℕ) (x : B S), x ∈ positiveEvenPart (Bᵢ S) →
        transition h ((γ S).dpow n x) = (γ T).dpow n (transition h x)) :
    ∃! δ : DividedPowerStructure Cᵢ,
      ∀ (S : I) (n : ℕ) (x : B S),
        x ∈ positiveEvenPart (Bᵢ S) →
          δ.dpow n (ι S x) = ι S ((γ S).dpow n x) := by
  classical
  have hpos_ι (S : I) {x : B S} (hx : x ∈ positiveEvenPart (Bᵢ S)) :
      ι S x ∈ positiveEvenPart Cᵢ :=
    algHom_mem_positiveEvenPart (Bᵢ S) Cᵢ (ι S) (hgrade S) hx
  have hpos_tr {S T : I} (h : S ≤ T) {x : B S} (hx : x ∈ positiveEvenPart (Bᵢ S)) :
      transition h x ∈ positiveEvenPart (Bᵢ T) :=
    algHom_mem_positiveEvenPart (Bᵢ S) (Bᵢ T) (transition h) (htransition_grade h) hx
  let repS (x : C) (hx : x ∈ positiveEvenPart Cᵢ) : I :=
    Classical.choose (exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
      htransition_grade hgrade_lift hx)
  let repY (x : C) (hx : x ∈ positiveEvenPart Cᵢ) : B (repS x hx) :=
    Classical.choose (Classical.choose_spec (exists_lift_positiveEvenPart B Bᵢ Cᵢ
      transition ι hι htransition_grade hgrade_lift hx))
  have rep_pos (x : C) (hx : x ∈ positiveEvenPart Cᵢ) :
      repY x hx ∈
        positiveEvenPart (Bᵢ (repS x hx)) :=
    (Classical.choose_spec (Classical.choose_spec (exists_lift_positiveEvenPart B Bᵢ Cᵢ
      transition ι hι htransition_grade hgrade_lift hx))).1
  have rep_image (x : C) (hx : x ∈ positiveEvenPart Cᵢ) :
      ι (repS x hx)
        (repY x hx) = x :=
    (Classical.choose_spec (Classical.choose_spec (exists_lift_positiveEvenPart B Bᵢ Cᵢ
      transition ι hι htransition_grade hgrade_lift hx))).2
  let dp : ℕ → C → C := fun n x =>
    if hx : x ∈ positiveEvenPart Cᵢ then
      ι (repS x hx)
        ((γ (repS x hx)).dpow n
          (repY x hx))
    else 0
  have dp_lift (n : ℕ) {x : C} (hx : x ∈ positiveEvenPart Cᵢ)
      {S : I} (y : B S) (hy : y ∈ positiveEvenPart (Bᵢ S)) (hiy : ι S y = x) :
      dp n x = ι S ((γ S).dpow n y) := by
    dsimp [dp]
    rw [dite_eq_left hx]
    let T := repS x hx
    let z := repY x hx
    have hz : z ∈ positiveEvenPart (Bᵢ T) := rep_pos x hx
    have hzx : ι T z = x := rep_image x hx
    change ι T ((γ T).dpow n z) = ι S ((γ S).dpow n y)
    obtain ⟨U, hTU, hSU, he⟩ := heq T S z y (hzx.trans hiy.symm)
    calc
      ι T ((γ T).dpow n z) = ι U (transition hTU ((γ T).dpow n z)) :=
        (hι hTU _).symm
      _ = ι U ((γ U).dpow n (transition hTU z)) :=
        congrArg (ι U) (htransition_dpow hTU n z hz)
      _ = ι U ((γ U).dpow n (transition hSU y)) :=
        congrArg (fun w => ι U ((γ U).dpow n w)) he
      _ = ι U (transition hSU ((γ S).dpow n y)) :=
        congrArg (ι U) (htransition_dpow hSU n y hy).symm
      _ = ι S ((γ S).dpow n y) := hι hSU _
  let δ : DividedPowerStructure Cᵢ := {
    dpow := dp
    dpow_null := by
      intro n x hx
      by_cases hx' : x ∈ positiveEvenPart Cᵢ
      · exact (hx hx').elim
      · simp [dp, hx']
    dpow_zero := by
      intro x hx
      rw [dp_lift (S := repS x hx) 0 hx (repY x hx) (rep_pos x hx)
        (rep_image x hx)]
      rw [(γ (repS x hx)).dpow_zero (rep_pos x hx)]
      exact map_one (ι (repS x hx))
    dpow_one := by
      intro x hx
      rw [dp_lift (S := repS x hx) 1 hx (repY x hx) (rep_pos x hx)
        (rep_image x hx)]
      rw [(γ (repS x hx)).dpow_one (rep_pos x hx)]
      exact rep_image x hx
    dpow_mem := by
      intro n x hn hx
      rw [dp_lift n hx (repY x hx) (rep_pos x hx)
        (rep_image x hx)]
      exact hpos_ι _ ((γ (repS x hx)).dpow_mem hn (rep_pos x hx))
    dpow_mem_grade := by
      intro n d x hn hx hxd
      by_cases hd : d = 0
      · subst d
        have hxzero : x = 0 := positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hx hxd
        subst x
        have hzero : dp n 0 = 0 := by
          obtain ⟨S₀⟩ := (inferInstance : Nonempty I)
          rw [dp_lift n (positiveEvenPart Cᵢ).zero_mem (0 : B S₀)
            (positiveEvenPart (Bᵢ S₀)).zero_mem (map_zero (ι S₀)),
            dpow_zero_arg_of_ne_zero (Bᵢ S₀) (γ S₀) hn, map_zero]
        rw [hzero]
        exact (Cᵢ 0).zero_mem
      · obtain ⟨S, y, hy, hiy⟩ := hgrade_lift (2 * d) x hxd
        have hypos : y ∈ positiveEvenPart (Bᵢ S) := by
          refine Submodule.mem_iSup_of_mem (d - 1) ?_
          simpa [show 2 * d = 2 * ((d - 1) + 1) by omega] using hy
        rw [dp_lift n hx y hypos hiy]
        exact hgrade S (2 * n * d) ((γ S).dpow n y)
          ((γ S).dpow_mem_grade hn hypos hy)
    dpow_mul := by
      intro n m x hx
      obtain ⟨S, y, hy, hiy⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hx
      rw [dp_lift m hx y hy hiy, dp_lift n hx y hy hiy,
        dp_lift (m + n) hx y hy hiy]
      simpa only [map_mul, map_natCast] using
        congrArg (ι S) ((γ S).dpow_mul (m := n) (n := m) hy)
    dpow_mul_even := by
      intro n x y hn hx hy
      obtain ⟨S, xS, hxS, hix⟩ := exists_lift_iSup_grade B Bᵢ Cᵢ (fun d => 2 * d) transition ι
        hι htransition_grade hgrade_lift hx
      obtain ⟨T, yT, hyT, hiy⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hy
      obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
      let xU := transition hSU xS
      let yU := transition hTU yT
      have hxU : xU ∈ evenPart (Bᵢ U) :=
        algHom_mem_iSup_grade (Bᵢ S) (Bᵢ U) (fun d => 2 * d) _ (htransition_grade hSU) hxS
      have hyU : yU ∈ positiveEvenPart (Bᵢ U) := hpos_tr hTU hyT
      have hprodU : xU * yU ∈ positiveEvenPart (Bᵢ U) :=
        evenPart_mul_positiveEvenPart (Bᵢ U) hxU hyU
      have hprod : ι U (xU * yU) = x * y := by
        rw [map_mul, hι hSU, hι hTU, hix, hiy]
      have hiyU : ι U yU = y := by
        rw [hι hTU, hiy]
      have hixU : ι U xU = x := by
        rw [hι hSU, hix]
      rw [dp_lift n (evenPart_mul_positiveEvenPart Cᵢ hx hy) (xU * yU) hprodU hprod,
        dp_lift n hy yU hyU hiyU]
      rw [(γ U).dpow_mul_even hn hxU hyU, map_mul, map_pow]
      rw [hixU]
    dpow_mul_odd := by
      intro n d e x y hn hx hy
      obtain ⟨S, xS, hxS, hix⟩ := hgrade_lift (2 * d + 1) x hx
      obtain ⟨T, yT, hyT, hiy⟩ := hgrade_lift (2 * e + 1) y hy
      obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
      let xU := transition hSU xS
      let yU := transition hTU yT
      have hxU := htransition_grade hSU (2 * d + 1) xS hxS
      have hyU := htransition_grade hTU (2 * e + 1) yT hyT
      have hprodU : xU * yU ∈ positiveEvenPart (Bᵢ U) := by
        refine Submodule.mem_iSup_of_mem (d + e) ?_
        have hprodGrade : xU * yU ∈ Bᵢ U ((2 * d + 1) + (2 * e + 1)) :=
          SetLike.GradedMul.mul_mem hxU hyU
        have hdeg : (2 * d + 1) + (2 * e + 1) = 2 * ((d + e) + 1) := by omega
        simpa [hdeg] using hprodGrade
      have hprod : ι U (xU * yU) = x * y := by
        rw [map_mul, hι hSU, hι hTU, hix, hiy]
      have hprodGrade : xU * yU ∈ Bᵢ U (2 * (d + e + 1)) := by
        have hprodGrade' : xU * yU ∈ Bᵢ U ((2 * d + 1) + (2 * e + 1)) :=
          SetLike.GradedMul.mul_mem hxU hyU
        have hdeg : (2 * d + 1) + (2 * e + 1) = 2 * (d + e + 1) := by omega
        simpa only [hdeg] using hprodGrade'
      have hprodC : x * y ∈ positiveEvenPart Cᵢ := by
        rw [← hprod]
        exact hpos_ι U hprodU
      rw [dp_lift n hprodC
        (xU * yU) hprodU hprod]
      rw [(γ U).dpow_mul_odd hn hxU hyU]
      simp
    dpow_add := by
      intro n x y hx hy
      obtain ⟨S, xS, hxS, hix⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hx
      obtain ⟨T, yT, hyT, hiy⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hy
      obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
      let xU := transition hSU xS
      let yU := transition hTU yT
      have hxU : xU ∈ positiveEvenPart (Bᵢ U) := hpos_tr hSU hxS
      have hyU : yU ∈ positiveEvenPart (Bᵢ U) := hpos_tr hTU hyT
      have hsumU : xU + yU ∈ positiveEvenPart (Bᵢ U) :=
        (positiveEvenPart (Bᵢ U)).add_mem hxU hyU
      have hsum : ι U (xU + yU) = x + y := by
        rw [map_add, hι hSU, hι hTU, hix, hiy]
      have hsumC : x + y ∈ positiveEvenPart Cᵢ := by
        rw [← hsum]
        exact hpos_ι U hsumU
      have hixU : ι U xU = x := by
        rw [hι hSU, hix]
      have hiyU : ι U yU = y := by
        rw [hι hTU, hiy]
      rw [dp_lift n hsumC (xU + yU) hsumU hsum, (γ U).dpow_add hxU hyU]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [map_mul,
        ← hixU, ← hiyU,
        ← dp_lift ij.1 (hpos_ι U hxU) xU hxU rfl, ← dp_lift ij.2 (hpos_ι U hyU) yU hyU rfl]
    dpow_dpow := by
      intro n m x hn hm hx
      obtain ⟨S, y, hy, hiy⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hx
      rw [dp_lift n hx y hy hiy]
      rw [dp_lift m (hpos_ι S ((γ S).dpow_mem hn hy)) ((γ S).dpow n y) ((γ S).dpow_mem hn hy) rfl]
      rw [(γ S).dpow_dpow (m := n) (n := m) hn hm hy]
      rw [dp_lift (m * n) hx y hy hiy]
      simp only [map_mul, map_natCast]
  }
  refine ⟨δ, ?_, ?_⟩
  · intro S n x hx
    exact dp_lift n (hpos_ι S hx) x hx rfl
  · intro ε hε
    apply DividedPowerStructure.ext
    funext n x
    by_cases hx : x ∈ positiveEvenPart Cᵢ
    · obtain ⟨S, y, hy, hiy⟩ := exists_lift_positiveEvenPart B Bᵢ Cᵢ transition ι hι
        htransition_grade hgrade_lift hx
      calc
        ε.dpow n x = ε.dpow n (ι S y) := congrArg (ε.dpow n) hiy.symm
        _ = ι S ((γ S).dpow n y) := hε S n y hy
        _ = dp n x := (dp_lift n hx y hy hiy).symm
        _ = δ.dpow n x := rfl
    · rw [ε.dpow_null hx, δ.dpow_null hx]

/-- Divided powers of elements supported on a finite set of homogeneous variables over a
graded coefficient algebra are still supported on that set. The variables need not all have the
same degree: each `T j` is homogeneous of its own degree `deg j`. The coefficient map preserves
grading, as do the inclusions in the extensions of Tags 09PH and 09PI. Thus every
finite-variable stage is a divided-power subalgebra. -/
@[stacks 0F4I "finite stages preserve divided powers"]
public theorem finiteVariableStage_dpow_mem
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ] (δ : DividedPowerStructure Cᵢ)
    (ι : A →ₐ[R] C) (T : J → C) (S : Finset J) (deg : J → ℕ)
    (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j : J, T j ∈ Cᵢ (deg j))
    (hcoeff : ∀ (n : ℕ) (a : A), ι a ∈ positiveEvenPart Cᵢ →
      δ.dpow n (ι a) ∈ Set.range ι)
    (n : ℕ) (x : C)
    (hx : x ∈ finiteVariableStage δ ι T S)
    (hpositive : x ∈ positiveEvenPart Cᵢ) :
    δ.dpow n x ∈ finiteVariableStage δ ι T S := by
  classical
  let Q := finiteVariableStage δ ι T S
  let G : Set C := Set.range ι ∪ {y : C | ∃ j : J, j ∈ S ∧
    (y = T j ∨ ∃ k : ℕ, y = δ.dpow k (T j))}
  have hcomp (y : C) (hy : y ∈ Q) (m : ℕ) :
      gradedComponent Cᵢ y m ∈ Q :=
    finiteVariableStage_gradedComponent_mem Aᵢ Cᵢ δ ι T S deg hgrade hT hy m
  have hgen : ∀ y : C, y ∈ G →
      (∀ m, gradedComponent Cᵢ y m ∈ Q) ∧
      (∀ m n, gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ →
        δ.dpow n (gradedComponent Cᵢ y m) ∈ Q) := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨a, rfl⟩ := hy
      constructor
      · intro m
        exact hcomp (ι a) (Subring.subset_closure (Or.inl (Set.mem_range_self a))) m
      · intro m n hm
        rw [algHom_gradedComponent Aᵢ Cᵢ ι hgrade a m]
        have hpre : ι (gradedComponent Aᵢ a m) ∈ positiveEvenPart Cᵢ := by
          simpa [algHom_gradedComponent Aᵢ Cᵢ ι hgrade a m] using hm
        obtain ⟨b, hb⟩ := hcoeff n (gradedComponent Aᵢ a m) hpre
        exact Subring.subset_closure (Or.inl ⟨b, hb⟩)
    · rcases hy with ⟨j, hj, rfl | ⟨k, rfl⟩⟩
      · constructor
        · intro m
          exact hcomp (T j)
            (Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)) m
        · intro m n hm
          rw [gradedComponent_eq_self_or_zero Cᵢ (hT j)] at hm ⊢
          split_ifs at hm ⊢ with h
          · exact Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨n, rfl⟩⟩)
          · exact dpow_zero_mem_subring Cᵢ δ Q n
      · have hhom := exists_grade_dpow Cᵢ δ (hT j) k
        constructor
        · intro m
          exact hcomp (δ.dpow k (T j))
            (Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨k, rfl⟩⟩)) m
        · intro m n hm
          by_cases hk : k = 0
          · subst k
            by_cases hp : T j ∈ positiveEvenPart Cᵢ
            · rw [δ.dpow_zero hp] at hm ⊢
              have hone : (1 : C) ∈ Cᵢ 0 := SetLike.GradedOne.one_mem
              rw [gradedComponent_eq_self_or_zero Cᵢ hone] at hm ⊢
              split_ifs at hm ⊢ with h
              · have hz : (1 : C) = 0 :=
                  positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hm hone
                rw [hz]
                exact dpow_zero_mem_subring Cᵢ δ Q n
              · exact dpow_zero_mem_subring Cᵢ δ Q n
            · rw [δ.dpow_null hp] at hm ⊢
              simpa [gradedComponent] using dpow_zero_mem_subring Cᵢ δ Q n
          · obtain ⟨e, he⟩ := hhom
            rw [gradedComponent_eq_self_or_zero Cᵢ he] at hm ⊢
            split_ifs at hm ⊢ with h
            · by_cases hp : T j ∈ positiveEvenPart Cᵢ
              · by_cases hn : n = 0
                · subst n
                  rw [δ.dpow_zero hm]
                  exact Q.one_mem
                · rw [δ.dpow_dpow (m := k) (n := n) hk hn hp]
                  exact Q.mul_mem (natCast_mem Q _)
                    (Subring.subset_closure
                      (Or.inr ⟨j, hj, Or.inr ⟨n * k, rfl⟩⟩))
              · rw [δ.dpow_null hp] at hm ⊢
                simpa [gradedComponent] using dpow_zero_mem_subring Cᵢ δ Q n
            · exact dpow_zero_mem_subring Cᵢ δ Q n
  let K : Subring C := {
    carrier := {y | (∀ m, gradedComponent Cᵢ y m ∈ Q) ∧
      (∀ m n, gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ →
        δ.dpow n (gradedComponent Cᵢ y m) ∈ Q)}
    zero_mem' := by
      constructor
      · intro m
        simp [gradedComponent, Q]
      · intro m n hm
        simpa [gradedComponent] using dpow_zero_mem_subring Cᵢ δ Q n
    one_mem' := by
      constructor
      · intro m
        have hone : (1 : C) ∈ Cᵢ 0 := SetLike.GradedOne.one_mem
        rw [gradedComponent_eq_self_or_zero Cᵢ hone]
        split_ifs with h
        · exact Q.one_mem
        · exact Q.zero_mem
      · intro m n hm
        have hone : (1 : C) ∈ Cᵢ 0 := SetLike.GradedOne.one_mem
        rw [gradedComponent_eq_self_or_zero Cᵢ hone] at hm ⊢
        split_ifs at hm ⊢ with h
        · have hzero : (1 : C) = 0 :=
            positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hm hone
          rw [hzero]
          exact dpow_zero_mem_subring Cᵢ δ Q n
        · exact dpow_zero_mem_subring Cᵢ δ Q n
    add_mem' := by
      intro x y hx hy
      constructor
      · intro m
        rw [gradedComponent_add]
        exact Q.add_mem (hx.1 m) (hy.1 m)
      · intro m n hm
        rw [gradedComponent_add] at hm ⊢
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ
          (by
            simpa only [gradedComponent_add] using
              (Cᵢ m).add_mem (gradedComponent_mem Cᵢ x m)
                (gradedComponent_mem Cᵢ y m)) hm with
          hz | ⟨k, hk⟩
        · rw [hz]
          exact dpow_zero_mem_subring Cᵢ δ Q n
        · have hxpos : gradedComponent Cᵢ x m ∈ positiveEvenPart Cᵢ :=
            Submodule.mem_iSup_of_mem k (by rw [← hk]; exact gradedComponent_mem Cᵢ x m)
          have hypos : gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ :=
            Submodule.mem_iSup_of_mem k (by rw [← hk]; exact gradedComponent_mem Cᵢ y m)
          rw [δ.dpow_add hxpos hypos]
          exact Q.sum_mem fun ij _ => Q.mul_mem (hx.2 m ij.1 hxpos) (hy.2 m ij.2 hypos)
    neg_mem' := by
      intro x hx
      constructor
      · intro m
        rw [gradedComponent_neg]
        exact Q.neg_mem (hx.1 m)
      · intro m n hm
        rw [gradedComponent_neg] at hm ⊢
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ
          ((Cᵢ m).neg_mem (gradedComponent_mem Cᵢ x m)) hm with hz | ⟨k, hk⟩
        · rw [hz]
          exact dpow_zero_mem_subring Cᵢ δ Q n
        · have hcpos : gradedComponent Cᵢ x m ∈ positiveEvenPart Cᵢ := by
            refine Submodule.mem_iSup_of_mem k ?_
            rw [← hk]
            exact gradedComponent_mem Cᵢ x m
          have hminusOne : (-1 : C) ∈ Cᵢ 0 :=
            (Cᵢ 0).neg_mem SetLike.GradedOne.one_mem
          have hminusD : ∀ l, (-1 : C) ∈ positiveEvenPart Cᵢ →
              δ.dpow l (-1 : C) ∈ Q := by
            intro l hp
            have hz := positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hp hminusOne
            rw [hz]
            exact dpow_zero_mem_subring Cᵢ δ Q l
          have hprod := dpow_mem_homogeneous_mul_subring Cᵢ δ Q
            (i := 0) (j := m) (k := k) (x := (-1 : C))
            (y := gradedComponent Cᵢ x m) hminusOne
            (gradedComponent_mem Cᵢ x m) (by omega)
            (Q.neg_mem Q.one_mem) (hx.1 m) hminusD
            (fun l hp => hx.2 m l hcpos) n
          simpa using hprod
    mul_mem' := by
      intro x y hx hy
      constructor
      · intro m
        rw [gradedComponent_mul]
        apply Q.sum_mem
        intro ij hij
        exact Q.mul_mem (hx.1 ij.1) (hy.1 ij.2)
      · intro m n hm
        have hmulcomp := gradedComponent_mul Cᵢ x y m
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ
          (gradedComponent_mem Cᵢ (x * y) m) (by simpa [hmulcomp] using hm) with
          hz | ⟨k, hk⟩
        · rw [hz]
          exact dpow_zero_mem_subring Cᵢ δ Q n
        · have hsumGrade : ∀ ij ∈ Finset.antidiagonal m,
              (gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2) ∈
                Cᵢ (2 * (k + 1)) := by
            intro ij hij
            have hsum := Finset.mem_antidiagonal.mp hij
            have hdeg : ij.1 + ij.2 = 2 * (k + 1) := by omega
            simpa [hdeg] using SetLike.GradedMul.mul_mem
              (gradedComponent_mem Cᵢ x ij.1) (gradedComponent_mem Cᵢ y ij.2)
          have hsumDpow : ∀ ij ∈ Finset.antidiagonal m, ∀ l,
              δ.dpow l (gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2) ∈ Q := by
            intro ij hij l
            have hsum := Finset.mem_antidiagonal.mp hij
            have hdeg : ij.1 + ij.2 = 2 * (k + 1) := by omega
            exact dpow_mem_homogeneous_mul_subring Cᵢ δ Q
              (gradedComponent_mem Cᵢ x ij.1) (gradedComponent_mem Cᵢ y ij.2)
              hdeg (hx.1 ij.1) (hy.1 ij.2)
              (fun r hr => hx.2 ij.1 r hr)
              (fun r hr => hy.2 ij.2 r hr) l
          have hsumDpow' := dpow_mem_finite_positive_sum Cᵢ δ Q
            (Finset.antidiagonal m)
            (fun ij => gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2)
            (fun ij hij => Submodule.mem_iSup_of_mem k (hsumGrade ij hij)) hsumDpow n
          simpa only [hmulcomp] using hsumDpow'
  }
  have hxK : x ∈ K := Subring.closure_le.mpr (fun y hy => hgen y hy) hx
  let F := (DirectSum.decompose Cᵢ x).support
  have hdecomp : (∑ i ∈ F, gradedComponent Cᵢ x i) = x := by
    simpa [F, gradedComponent] using DirectSum.sum_support_decompose Cᵢ x
  have htermsPos : ∀ i ∈ F, gradedComponent Cᵢ x i ∈ positiveEvenPart Cᵢ :=
    fun i _ => gradedComponent_mem_positiveEvenPart Cᵢ hpositive i
  have htermsDpow : ∀ i ∈ F, ∀ l,
      δ.dpow l (gradedComponent Cᵢ x i) ∈ Q := by
    intro i hi l
    exact hxK.2 i l (htermsPos i hi)
  rw [← hdecomp]
  exact dpow_mem_finite_positive_sum Cᵢ δ Q F (fun i => gradedComponent Cᵢ x i) htermsPos
    htermsDpow n

private theorem dividedPower_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    {Cᵢ : ℕ → Submodule R A} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
    (δ ε : DividedPowerStructure Cᵢ) (n : ℕ) :
    ε.dpow n (0 : A) = δ.dpow n 0 := by
  by_cases hn : n = 0
  · subst n
    rw [ε.dpow_zero (positiveEvenPart Cᵢ).zero_mem,
      δ.dpow_zero (positiveEvenPart Cᵢ).zero_mem]
  · rw [dpow_zero_arg_of_ne_zero Cᵢ ε hn, dpow_zero_arg_of_ne_zero Cᵢ δ hn]

private theorem dividedPower_eq_homogeneous_mul
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Cᵢ : ℕ → Submodule R A) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ] (δ ε : DividedPowerStructure Cᵢ)
    {i j : ℕ} {x y : A} (hx : x ∈ Cᵢ i) (hy : y ∈ Cᵢ j)
    {k : ℕ} (hij : i + j = 2 * (k + 1))
    (hxeq : ∀ n, x ∈ positiveEvenPart Cᵢ → ε.dpow n x = δ.dpow n x)
    (hyeq : ∀ n, y ∈ positiveEvenPart Cᵢ → ε.dpow n y = δ.dpow n y)
    (n : ℕ) : ε.dpow n (x * y) = δ.dpow n (x * y) := by
  obtain ⟨hpos, hcases⟩ := homogeneous_mul_cases Cᵢ hx hy hij
  by_cases hn0 : n = 0
  · rw [hn0, δ.dpow_zero hpos, ε.dpow_zero hpos]
  by_cases hn1 : n = 1
  · rw [hn1, δ.dpow_one hpos, ε.dpow_one hpos]
  rcases hcases with ⟨d, e, hxd, hye⟩ | ⟨hxe, hyp⟩ | ⟨hye, hxp, hcomm⟩
  · rw [δ.dpow_mul_odd (by omega) hxd hye, ε.dpow_mul_odd (by omega) hxd hye]
  · rw [δ.dpow_mul_even hn0 hxe hyp, ε.dpow_mul_even hn0 hxe hyp, hyeq n hyp]
  · rw [hcomm, δ.dpow_mul_even hn0 hye hxp, ε.dpow_mul_even hn0 hye hxp, hxeq n hxp]

private theorem dividedPower_eq_finite_positive_sum
    {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    (Cᵢ : ℕ → Submodule R A) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ] (δ ε : DividedPowerStructure Cᵢ)
    {ι : Type*} (s : Finset ι) (f : ι → A)
    (hpos : ∀ i ∈ s, f i ∈ positiveEvenPart Cᵢ)
    (heq : ∀ i ∈ s, ∀ n, ε.dpow n (f i) = δ.dpow n (f i))
    (n : ℕ) : ε.dpow n (∑ i ∈ s, f i) = δ.dpow n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
      simp only [Finset.sum_empty]
      exact dividedPower_eq_zero δ ε n
  | @insert a s has ih =>
      have htail : (∑ i ∈ s, f i) ∈ positiveEvenPart Cᵢ :=
        (positiveEvenPart Cᵢ).sum_mem (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
      have heqTail : ∀ m, ε.dpow m (∑ i ∈ s, f i) = δ.dpow m (∑ i ∈ s, f i) :=
        fun m => ih (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
          (fun i hi l => heq i (Finset.mem_insert_of_mem hi) l) m
      rw [Finset.sum_insert has,
        ε.dpow_add (hpos a (Finset.mem_insert_self ..)) htail,
        δ.dpow_add (hpos a (Finset.mem_insert_self ..)) htail]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [heq a (Finset.mem_insert_self ..) ij.1, heqTail ij.2]

private theorem dividedPower_eq_on_finiteVariableStage
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ]
    (δ ε : DividedPowerStructure Cᵢ) (ι : A →ₐ[R] C) (T : J → C)
    (S : Finset J) (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j : J, T j ∈ Cᵢ d)
    (hcoeff : ∀ n a, ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (ι a) = δ.dpow n (ι a))
    (hgenerator : ∀ n j, T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (T j) = δ.dpow n (T j))
    {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hpositive : x ∈ positiveEvenPart Cᵢ) (n : ℕ) :
    ε.dpow n x = δ.dpow n x := by
  classical
  let Q := finiteVariableStage δ ι T S
  let G : Set C := Set.range ι ∪ {y : C | ∃ j : J, j ∈ S ∧
    (y = T j ∨ ∃ k : ℕ, y = δ.dpow k (T j))}
  have hcomp (y : C) (hy : y ∈ Q) (m : ℕ) :
      gradedComponent Cᵢ y m ∈ Q :=
    finiteVariableStage_gradedComponent_mem Aᵢ Cᵢ δ ι T S (fun _ => d) hgrade hT hy m
  have hgen : ∀ y : C, y ∈ G →
      (∀ m, gradedComponent Cᵢ y m ∈ Q) ∧
      (∀ m l, gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ →
        ε.dpow l (gradedComponent Cᵢ y m) =
          δ.dpow l (gradedComponent Cᵢ y m)) := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨a, rfl⟩ := hy
      constructor
      · intro m
        exact hcomp (ι a) (Subring.subset_closure (Or.inl (Set.mem_range_self a))) m
      · intro m l hm
        rw [algHom_gradedComponent Aᵢ Cᵢ ι hgrade a m] at hm ⊢
        exact hcoeff l (gradedComponent Aᵢ a m) hm
    · rcases hy with ⟨j, hj, rfl | ⟨k, rfl⟩⟩
      · constructor
        · intro m
          exact hcomp (T j)
            (Subring.subset_closure (Or.inr ⟨j, hj, Or.inl rfl⟩)) m
        · intro m l hm
          rw [gradedComponent_eq_self_or_zero Cᵢ (hT j)] at hm ⊢
          split_ifs at hm ⊢ with h
          · exact hgenerator l j hm
          · exact dividedPower_eq_zero δ ε l
      · constructor
        · intro m
          exact hcomp (δ.dpow k (T j))
            (Subring.subset_closure (Or.inr ⟨j, hj, Or.inr ⟨k, rfl⟩⟩)) m
        · intro m l hm
          by_cases hk : k = 0
          · subst k
            by_cases hp : T j ∈ positiveEvenPart Cᵢ
            · rw [δ.dpow_zero hp] at hm ⊢
              have hone : (1 : C) ∈ Cᵢ 0 := SetLike.GradedOne.one_mem
              rw [gradedComponent_eq_self_or_zero Cᵢ hone] at hm ⊢
              split_ifs at hm ⊢ with h
              · have hz : (1 : C) = 0 :=
                  positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hm hone
                rw [hz]
                exact dividedPower_eq_zero δ ε l
              · exact dividedPower_eq_zero δ ε l
            · rw [δ.dpow_null hp] at hm ⊢
              simpa [gradedComponent] using dividedPower_eq_zero δ ε l
          · obtain ⟨e, he⟩ := exists_grade_dpow Cᵢ δ (hT j) k
            rw [gradedComponent_eq_self_or_zero Cᵢ he] at hm ⊢
            split_ifs at hm ⊢ with h
            · by_cases hp : T j ∈ positiveEvenPart Cᵢ
              · by_cases hn : l = 0
                · subst l
                  rw [δ.dpow_zero hm, ε.dpow_zero hm]
                · have hinner := hgenerator k j hp
                  conv_lhs => rw [← hinner]
                  rw [ε.dpow_dpow (m := k) (n := l) hk hn hp,
                    δ.dpow_dpow (m := k) (n := l) hk hn hp,
                    hgenerator (l * k) j hp]
              · rw [δ.dpow_null hp] at hm ⊢
                simpa [gradedComponent] using dividedPower_eq_zero δ ε l
            · exact dividedPower_eq_zero δ ε l
  let K : Subring C := {
    carrier := {y | (∀ m, gradedComponent Cᵢ y m ∈ Q) ∧
      (∀ m l, gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ →
        ε.dpow l (gradedComponent Cᵢ y m) = δ.dpow l (gradedComponent Cᵢ y m))}
    zero_mem' := by
      constructor
      · intro m
        simp [gradedComponent]
      · intro m l hm
        simpa [gradedComponent] using dividedPower_eq_zero δ ε l
    one_mem' := by
      constructor
      · intro m
        rw [gradedComponent_eq_self_or_zero Cᵢ SetLike.GradedOne.one_mem]
        split_ifs with h
        · exact Q.one_mem
        · exact Q.zero_mem
      · intro m l hm
        rw [gradedComponent_eq_self_or_zero Cᵢ SetLike.GradedOne.one_mem] at hm ⊢
        split_ifs at hm ⊢ with h
        · have hz : (1 : C) = 0 :=
            positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hm SetLike.GradedOne.one_mem
          rw [hz]
          exact dividedPower_eq_zero δ ε l
        · exact dividedPower_eq_zero δ ε l
    add_mem' := by
      intro x y hx hy
      constructor
      · intro m
        rw [gradedComponent_add]
        exact Q.add_mem (hx.1 m) (hy.1 m)
      · intro m l hm
        rw [gradedComponent_add] at hm ⊢
        have hgradeSum : gradedComponent Cᵢ x m + gradedComponent Cᵢ y m ∈ Cᵢ m :=
          (Cᵢ m).add_mem (gradedComponent_mem Cᵢ x m)
            (gradedComponent_mem Cᵢ y m)
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ hgradeSum hm with
          hz | ⟨k, hk⟩
        · rw [hz]
          exact dividedPower_eq_zero δ ε l
        · have hxpos : gradedComponent Cᵢ x m ∈ positiveEvenPart Cᵢ :=
            Submodule.mem_iSup_of_mem k (by rw [← hk]; exact gradedComponent_mem Cᵢ x m)
          have hypos : gradedComponent Cᵢ y m ∈ positiveEvenPart Cᵢ :=
            Submodule.mem_iSup_of_mem k (by rw [← hk]; exact gradedComponent_mem Cᵢ y m)
          rw [ε.dpow_add hxpos hypos, δ.dpow_add hxpos hypos]
          apply Finset.sum_congr rfl
          intro ij hij
          rw [hx.2 m ij.1 hxpos, hy.2 m ij.2 hypos]
    neg_mem' := by
      intro x hx
      constructor
      · intro m
        rw [gradedComponent_neg]
        exact Q.neg_mem (hx.1 m)
      · intro m l hm
        rw [gradedComponent_neg] at hm ⊢
        have hgradeNeg : -gradedComponent Cᵢ x m ∈ Cᵢ m :=
          (Cᵢ m).neg_mem (gradedComponent_mem Cᵢ x m)
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ hgradeNeg hm with
          hz | ⟨k, hk⟩
        · rw [hz]
          exact dividedPower_eq_zero δ ε l
        · have hxpos : gradedComponent Cᵢ x m ∈ positiveEvenPart Cᵢ := by
            refine Submodule.mem_iSup_of_mem k ?_
            rw [← hk]
            exact gradedComponent_mem Cᵢ x m
          have hminusOne : (-1 : C) ∈ Cᵢ 0 :=
            (Cᵢ 0).neg_mem SetLike.GradedOne.one_mem
          have hminusEq : ∀ q, (-1 : C) ∈ positiveEvenPart Cᵢ →
              ε.dpow q (-1 : C) = δ.dpow q (-1 : C) := by
            intro q hq
            have hz := positiveEvenPart_mem_grade_zero_eq_zero Cᵢ hq hminusOne
            rw [hz]
            exact dividedPower_eq_zero δ ε q
          have hmul := dividedPower_eq_homogeneous_mul Cᵢ δ ε
            (i := 0) (j := m) (k := k) (x := (-1 : C))
            (y := gradedComponent Cᵢ x m) hminusOne
            (gradedComponent_mem Cᵢ x m) (by omega)
            hminusEq (fun q hq => hx.2 m q hxpos) l
          simpa using hmul
    mul_mem' := by
      intro x y hx hy
      constructor
      · intro m
        rw [gradedComponent_mul]
        apply Q.sum_mem
        intro ij hij
        exact Q.mul_mem (hx.1 ij.1) (hy.1 ij.2)
      · intro m l hm
        have hmulcomp := gradedComponent_mul Cᵢ x y m
        have hgradeProd := gradedComponent_mem Cᵢ (x * y) m
        rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ hgradeProd
          (by simpa [hmulcomp] using hm) with hz | ⟨k, hk⟩
        · rw [hz]
          exact dividedPower_eq_zero δ ε l
        · have htermsPos : ∀ ij ∈ Finset.antidiagonal m,
              gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2 ∈
                positiveEvenPart Cᵢ := by
            intro ij hij
            have hsum := Finset.mem_antidiagonal.mp hij
            have hdeg : ij.1 + ij.2 = 2 * (k + 1) := hsum.trans hk
            apply Submodule.mem_iSup_of_mem k
            rw [← hdeg]
            exact SetLike.GradedMul.mul_mem
              (gradedComponent_mem Cᵢ x ij.1) (gradedComponent_mem Cᵢ y ij.2)
          have htermsEq : ∀ ij ∈ Finset.antidiagonal m, ∀ q,
              ε.dpow q (gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2) =
                δ.dpow q (gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2) := by
            intro ij hij q
            have hsum := Finset.mem_antidiagonal.mp hij
            have hdeg : ij.1 + ij.2 = 2 * (k + 1) := hsum.trans hk
            exact dividedPower_eq_homogeneous_mul Cᵢ δ ε
              (gradedComponent_mem Cᵢ x ij.1) (gradedComponent_mem Cᵢ y ij.2)
              hdeg (fun q hq => hx.2 ij.1 q hq)
              (fun q hq => hy.2 ij.2 q hq) q
          have hsumEq := dividedPower_eq_finite_positive_sum Cᵢ δ ε
            (Finset.antidiagonal m)
            (fun ij => gradedComponent Cᵢ x ij.1 * gradedComponent Cᵢ y ij.2)
            htermsPos htermsEq l
          simpa only [hmulcomp] using hsumEq
  }
  have hxK : x ∈ K := Subring.closure_le.mpr (fun y hy => hgen y hy) hx
  let F := (DirectSum.decompose Cᵢ x).support
  have hdecomp : (∑ i ∈ F, gradedComponent Cᵢ x i) = x := by
    simpa [F, gradedComponent] using DirectSum.sum_support_decompose Cᵢ x
  have htermsPos : ∀ i ∈ F, gradedComponent Cᵢ x i ∈ positiveEvenPart Cᵢ :=
    fun i _ => gradedComponent_mem_positiveEvenPart Cᵢ hpositive i
  have htermsEq : ∀ i ∈ F, ∀ l,
      ε.dpow l (gradedComponent Cᵢ x i) = δ.dpow l (gradedComponent Cᵢ x i) :=
    fun i hi l => hxK.2 i l (htermsPos i hi)
  rw [← hdecomp]
  exact dividedPower_eq_finite_positive_sum Cᵢ δ ε F
    (fun i => gradedComponent Cᵢ x i) htermsPos htermsEq n

/-- On a set-indexed extension, divided powers are forced by their restriction to the
coefficient algebra and by their values on the adjoined generators. -/
@[stacks 0F4I "uniqueness"]
public theorem dividedPowerStructure_unique_of_generators
    {R : Type u} {A : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring A] [Ring C] [Algebra R A] [Algebra R C]
    (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) (hd : 0 < d)
    (Cᵢ : ℕ → Submodule R C) [GradedAlgebra Cᵢ]
    [IsStrictlyGradedComm Cᵢ]
    (δ ε : DividedPowerStructure Cᵢ) (ι : A →ₐ[R] C) (T : J → C)
    (hgrade : ∀ (m : ℕ) (a : A), a ∈ Aᵢ m → ι a ∈ Cᵢ m)
    (hT : ∀ j : J, T j ∈ Cᵢ d)
    (hfinite : ∀ x : C, ∃ S : Finset J, x ∈ finiteVariableStage δ ι T S)
    (hcoeff : ∀ (n : ℕ) (a : A), ι a ∈ positiveEvenPart Cᵢ →
      ε.dpow n (ι a) = δ.dpow n (ι a))
    (hgenerator : ∀ (n : ℕ) (j : J), T j ∈ positiveEvenPart Cᵢ →
      ε.dpow n (T j) = δ.dpow n (T j)) :
    ε = δ := by
  -- Positivity of `d` is part of the source statement but is not needed by the argument, since
  -- the degree-zero case is handled by the homogeneous decomposition; it is kept and referenced
  -- here rather than renamed away.
  have := hd
  apply DividedPowerStructure.ext
  funext n x
  by_cases hx : x ∈ positiveEvenPart Cᵢ
  · obtain ⟨S, hS⟩ := hfinite x
    exact dividedPower_eq_on_finiteVariableStage Aᵢ d Cᵢ δ ε ι T S
      hgrade hT hcoeff hgenerator hS hx n
  · rw [ε.dpow_null hx, δ.dpow_null hx]

end DividedPowers.TateResolution
