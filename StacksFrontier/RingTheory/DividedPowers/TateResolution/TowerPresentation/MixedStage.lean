module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TowerPresentation.MappingProperty

/-! # Finite variable stages of mixed degree as graded divided power algebras

The one-variable extensions bundled as graded divided power algebras, and the finite variable
stages of an algebra whose variables are homogeneous of varying degrees, as graded divided power
subalgebras: graded subrings, closed under divided powers, bundled as `stageDPAlgebra`.
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w y z

section OneVariableBundles

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
  (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] [IsStrictlyGradedComm Aᵢ]
  (γ : DividedPowerStructure Aᵢ)

/-- The odd one-variable extension of a graded divided power algebra, bundled. -/
public noncomputable def oddVariableDPAlgebra (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    GradedDPAlgebra.{u, v} R where
  carrier := OddVariableExtension Aᵢ d
  ring := inferInstance
  algebra := inferInstance
  grade := OddVariableExtension.grade Aᵢ d
  graded := inferInstance
  strict := inferInstance
  gamma := oddVariableDividedPowerStructure Aᵢ γ d hd hodd

/-- The even one-variable extension of a graded divided power algebra, bundled. -/
public noncomputable def evenVariableDPAlgebra (d : ℕ) (hd : 0 < d) [Fact (Even d)] :
    GradedDPAlgebra.{u, v} R where
  carrier := EvenVariableAlgebra A
  ring := inferInstance
  algebra := inferInstance
  grade := EvenVariableAlgebra.grade Aᵢ d
  graded := inferInstance
  strict := inferInstance
  gamma := evenVariableDividedPowerStructure d hd γ

end OneVariableBundles

section HomogeneousVariables

/-- The hypotheses under which the finite variable stages of a graded divided power algebra are
graded subrings: the coefficient algebra sits in degree zero and every variable is homogeneous of
*some* degree. They are bundled as a class so that the graded structure of a stage, which depends
on them, can be a local instance. The degrees themselves are deliberately not recorded, so that
the class is determined by the grading, the coefficient map and the family of variables alone. -/
public class IsHomogeneousVariableFamily {R : Type u} {P : Type v} {C : Type z} {J : Type w}
    [CommRing R] [Ring P] [Algebra R P] [Ring C] [Algebra R C]
    (Cᵢ : ℕ → Submodule R C) (ι : P →ₐ[R] C) (T : J → C) : Prop where
  /-- The coefficient algebra lands in degree zero. -/
  coefficient_mem : ∀ p : P, ι p ∈ Cᵢ 0
  /-- Every variable is homogeneous. -/
  variable_homogeneous : ∀ j : J, ∃ m : ℕ, T j ∈ Cᵢ m

end HomogeneousVariables

section MixedStage

variable {R : Type u} {P : Type v} {C : Type z} {J : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring C] [Algebra R C]
  {Cᵢ : ℕ → Submodule R C} [GradedAlgebra Cᵢ] [IsStrictlyGradedComm Cᵢ]
  (δ : DividedPowerStructure Cᵢ) (ι : P →ₐ[R] C) (T : J → C)

/-- A divided power of a homogeneous element is homogeneous: in positive even degree by the
degree formula, and outside the positive even part because it vanishes. -/
public theorem exists_mem_grade_dpow_of_mem_grade {e : ℕ} {x : C} (hx : x ∈ Cᵢ e) (n : ℕ) :
    ∃ m : ℕ, δ.dpow n x ∈ Cᵢ m := by
  by_cases hpos : x ∈ positiveEvenPart Cᵢ
  · by_cases hn : n = 0
    · subst hn
      exact ⟨0, by rw [δ.dpow_zero hpos]; exact SetLike.one_mem_graded Cᵢ⟩
    · rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ hx hpos with hz | ⟨k, hk⟩
      · exact ⟨0, by rw [hz, δ.dpow_zero_eq_zero hn]; exact Submodule.zero_mem _⟩
      · exact ⟨2 * n * (k + 1), δ.dpow_mem_grade hn hpos (hk ▸ hx)⟩
  · exact ⟨0, by rw [δ.dpow_null hpos]; exact Submodule.zero_mem _⟩

/-- **A finite variable stage is a graded subring**, for variables of *varying* degrees. The
statement `DividedPowers.TateResolution.IsSetVariableExtension.gradedPart_mem_finiteVariableStage`
is the same fact for a set-variable extension, whose variables all have one degree; the proof
needs no more than that each variable is homogeneous of *some* degree, which is what makes it
available for the mixed-degree stages of a divided power polynomial algebra. -/
public theorem gradedPart_mem_finiteVariableStage_of_homogeneous
    (hι0 : ∀ p : P, ι p ∈ Cᵢ 0) (hT : ∀ j : J, ∃ m : ℕ, T j ∈ Cᵢ m)
    (S : Finset J) {x : C} (hx : x ∈ finiteVariableStage δ ι T S) (m : ℕ) :
    gradedPart Cᵢ x m ∈ finiteVariableStage δ ι T S := by
  have key : ∀ y ∈ finiteVariableStage δ ι T S, ∀ m,
      gradedPart Cᵢ y m ∈ finiteVariableStage δ ι T S := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem w hw =>
        rcases hw with ⟨p, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩
        · exact gradedPart_mem_subring_of_mem_grade Cᵢ (hι0 p) _
            (mem_finiteVariableStage_coefficient δ ι T S p)
        · obtain ⟨m₁, hm₁⟩ := hT j
          exact gradedPart_mem_subring_of_mem_grade Cᵢ hm₁ _
            (mem_finiteVariableStage_generator δ ι T hj)
        · obtain ⟨m₁, hm₁⟩ := hT j
          obtain ⟨m₀, hm₀⟩ := exists_mem_grade_dpow_of_mem_grade δ hm₁ n
          exact gradedPart_mem_subring_of_mem_grade Cᵢ hm₀ _
            (mem_finiteVariableStage_dpow_generator δ ι T hj n)
    | zero => intro m; rw [gradedPart_zero]; exact Subring.zero_mem _
    | one =>
        exact gradedPart_mem_subring_of_mem_grade Cᵢ (SetLike.one_mem_graded Cᵢ) _
          (Subring.one_mem _)
    | add a b _ _ iha ihb =>
        intro m
        rw [gradedPart_add]
        exact Subring.add_mem _ (iha m) (ihb m)
    | neg a _ iha =>
        intro m
        rw [gradedPart_neg]
        exact Subring.neg_mem _ (iha m)
    | mul a b _ _ iha ihb =>
        intro m
        obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ a
        obtain ⟨u, hu⟩ := exists_gradedPart_decomposition Cᵢ b
        have hkey := gradedPart_mul_sum Cᵢ (s := s) (t := u)
          (gradedPart Cᵢ a) (gradedPart Cᵢ b) m
        rw [← hs, ← hu] at hkey
        rw [hkey]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun k _ => ?_
        by_cases hik : i + k = m
        · rw [gradedPart_mul_homogeneous Cᵢ (gradedPart_mem Cᵢ a i)
            (gradedPart_mem Cᵢ b k) hik]
          exact mul_mem (iha i) (ihb k)
        · rw [gradedPart_mul_homogeneous_of_ne Cᵢ (gradedPart_mem Cᵢ a i)
            (gradedPart_mem Cᵢ b k) hik]
          exact Subring.zero_mem _
  exact key x hx m

attribute [instance] stageAlgebra

/-- Scalar multiplication on a finite variable stage is that of the ambient algebra. -/
public theorem coe_stageAlgebra_smul (S : Finset J) (r : R)
    (x : finiteVariableStage δ ι T S) :
    ((r • x : finiteVariableStage δ ι T S) : C) = r • (x : C) :=
  (Algebra.smul_def r (x : C)).symm

/-- **The homogeneous pieces of a finite variable stage**: the elements of the stage which are
homogeneous of the given degree in the ambient algebra. -/
public def stageGrade (S : Finset J) (m : ℕ) : Submodule R (finiteVariableStage δ ι T S) where
  carrier := {x | (x : C) ∈ Cᵢ m}
  zero_mem' := Submodule.zero_mem (Cᵢ m)
  add_mem' hx hy := Submodule.add_mem (Cᵢ m) hx hy
  smul_mem' r x hx := by
    have hmem : r • (x : C) ∈ Cᵢ m := Submodule.smul_mem (Cᵢ m) r hx
    rw [← coe_stageAlgebra_smul δ ι T S r x] at hmem
    exact hmem

/-- Membership in a homogeneous piece of a finite variable stage. -/
@[simp]
public theorem mem_stageGrade (S : Finset J) (m : ℕ) (x : finiteVariableStage δ ι T S) :
    x ∈ stageGrade δ ι T S m ↔ (x : C) ∈ Cᵢ m := Iff.rfl

/-- The unit of a finite variable stage has degree zero and its multiplication adds degrees. -/
public instance stageGradedMonoid (S : Finset J) :
    SetLike.GradedMonoid (stageGrade δ ι T S) where
  one_mem := show ((1 : finiteVariableStage δ ι T S) : C) ∈ Cᵢ 0 from by
    simpa using SetLike.one_mem_graded Cᵢ
  mul_mem {i j x y} hx hy := by
    have hx' : (x : C) ∈ Cᵢ i := hx
    have hy' : (y : C) ∈ Cᵢ j := hy
    change ((x * y : finiteVariableStage δ ι T S) : C) ∈ Cᵢ (i + j)
    simpa using SetLike.mul_mem_graded hx' hy'

/-- A homogeneous element of a stage is a homogeneous element of the ambient algebra. -/
public def stageGradeIncl (S : Finset J) (m : ℕ) : stageGrade δ ι T S m →+ Cᵢ m where
  toFun x := ⟨((x : finiteVariableStage δ ι T S) : C), x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The direct sum of the homogeneous pieces of a stage, mapped into that of the ambient
algebra. It is built with `DFinsupp.mapRange` rather than from the universal property so that
its components are available by definition. -/
public noncomputable def stageDirectSumMap (S : Finset J) :
    DirectSum ℕ (fun m => ↥(stageGrade δ ι T S m)) →+
      DirectSum ℕ (fun m => ↥(Cᵢ m)) :=
  DFinsupp.mapRange.addMonoidHom fun m => stageGradeIncl δ ι T S m

/-- The components of `DividedPowers.TateResolution.stageDirectSumMap`. -/
public theorem stageDirectSumMap_apply (S : Finset J)
    (v : DirectSum ℕ (fun m => ↥(stageGrade δ ι T S m))) (m : ℕ) :
    stageDirectSumMap δ ι T S v m = stageGradeIncl δ ι T S m (v m) := rfl

/-- Summing the homogeneous pieces of a stage and then including into the ambient algebra is
including each piece and then summing. -/
public theorem stageDirectSumMap_coe (S : Finset J) :
    (DirectSum.coeAddMonoidHom Cᵢ).comp (stageDirectSumMap δ ι T S) =
      ((finiteVariableStage δ ι T S).subtype.toAddMonoidHom).comp
        (DirectSum.coeAddMonoidHom (stageGrade δ ι T S)) := by
  refine DirectSum.addHom_ext fun m y => ?_
  show DirectSum.coeAddMonoidHom Cᵢ (stageDirectSumMap δ ι T S
      (DirectSum.of (fun m => ↥(stageGrade δ ι T S m)) m y)) =
    ((DirectSum.coeAddMonoidHom (stageGrade δ ι T S)
      (DirectSum.of (fun m => ↥(stageGrade δ ι T S m)) m y) :
        finiteVariableStage δ ι T S) : C)
  rw [DirectSum.coeAddMonoidHom_of]
  have hof : stageDirectSumMap δ ι T S (DirectSum.of (fun m => ↥(stageGrade δ ι T S m)) m y) =
      DirectSum.of (fun m => ↥(Cᵢ m)) m (stageGradeIncl δ ι T S m y) := by
    refine DFinsupp.ext fun m' => ?_
    rw [stageDirectSumMap_apply]
    by_cases hm : m' = m
    · subst hm
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hm, DirectSum.of_eq_of_ne _ _ _ hm, map_zero]
  rw [hof, DirectSum.coeAddMonoidHom_of]
  rfl

/-- **The homogeneous pieces of a finite variable stage decompose it.** They are independent
because they are independent in the ambient algebra, and they span because the homogeneous
components of an element of the stage lie in the stage. -/
@[instance_reducible]
public noncomputable instance stageDecomposition [IsHomogeneousVariableFamily Cᵢ ι T]
    (S : Finset J) : DirectSum.Decomposition (stageGrade δ ι T S) := by
  classical
  refine DirectSum.IsInternal.chooseDecomposition _ ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : DirectSum.coeAddMonoidHom Cᵢ (stageDirectSumMap δ ι T S v) = 0 := by
      have h : DirectSum.coeAddMonoidHom Cᵢ (stageDirectSumMap δ ι T S v) =
          ((DirectSum.coeAddMonoidHom (stageGrade δ ι T S) v :
            finiteVariableStage δ ι T S) : C) :=
        DFunLike.congr_fun (stageDirectSumMap_coe δ ι T S) v
      rw [h, hv]
      rfl
    have h2 : stageDirectSumMap δ ι T S v = 0 :=
      (injective_iff_map_eq_zero _).1 (DirectSum.Decomposition.isInternal Cᵢ).1 _ h1
    refine DFinsupp.ext fun m => ?_
    have h3 : stageDirectSumMap δ ι T S v m = 0 := by rw [h2]; rfl
    rw [stageDirectSumMap_apply] at h3
    refine Subtype.ext (Subtype.ext ?_)
    change ((v m : finiteVariableStage δ ι T S) : C) = 0
    exact congrArg Subtype.val h3
  · intro y
    obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ (y : C)
    refine ⟨∑ m ∈ s, DirectSum.of (fun m => ↥(stageGrade δ ι T S m)) m
        ⟨⟨gradedPart Cᵢ (y : C) m,
          gradedPart_mem_finiteVariableStage_of_homogeneous δ ι T
            (IsHomogeneousVariableFamily.coefficient_mem (Cᵢ := Cᵢ) (T := T))
            (IsHomogeneousVariableFamily.variable_homogeneous (Cᵢ := Cᵢ) (ι := ι)) S y.2 m⟩,
          gradedPart_mem Cᵢ (y : C) m⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    refine Subtype.ext ?_
    push_cast
    exact hs.symm

/-- **A finite variable stage is a graded algebra**, with the homogeneous pieces it inherits from
the ambient algebra. -/
@[instance_reducible]
public noncomputable instance stageGradedAlgebra [IsHomogeneousVariableFamily Cᵢ ι T]
    (S : Finset J) : GradedAlgebra (stageGrade δ ι T S) :=
  { stageDecomposition δ ι T S, stageGradedMonoid δ ι T S with }

/-- A finite variable stage is strictly graded-commutative, being a subring of a strictly
graded-commutative algebra. -/
public instance stageStrictlyGradedComm (S : Finset J) :
    IsStrictlyGradedComm (stageGrade δ ι T S) where
  graded_comm {i j x y} hx hy := by
    refine Subtype.ext ?_
    rw [coe_neg_one_pow_smul]
    exact IsStrictlyGradedComm.graded_comm (R := R) (𝒜 := Cᵢ) hx hy
  odd_sq_zero {e x} hx := by
    refine Subtype.ext ?_
    simpa using IsStrictlyGradedComm.odd_sq_zero (R := R) (𝒜 := Cᵢ) (d := e) hx

/-- A sum of homogeneous pieces of a stage, in degrees `f d`, is such a sum in the ambient
algebra. -/
private theorem coe_mem_iSup_of_mem_iSup_stageGrade (S : Finset J) (f : ℕ → ℕ)
    {x : finiteVariableStage δ ι T S} (hx : x ∈ ⨆ d, stageGrade δ ι T S (f d)) :
    (x : C) ∈ ⨆ d, Cᵢ (f d) := by
  induction hx using Submodule.iSup_induction' with
  | mem k b hbm => exact Submodule.mem_iSup_of_mem k hbm
  | zero => simp
  | add b b' _ _ ihb ihb' => simpa using Submodule.add_mem (⨆ d, Cᵢ (f d)) ihb ihb'

/-- The positive even part of a finite variable stage is cut out by that of the ambient algebra.
The nontrivial direction uses that the homogeneous components of an element of the stage lie in
the stage, so a positive even element of the ambient algebra lying in the stage is a sum of
positive even homogeneous elements *of the stage*. -/
public theorem mem_positiveEvenPart_stageGrade_iff [IsHomogeneousVariableFamily Cᵢ ι T]
    (S : Finset J) (x : finiteVariableStage δ ι T S) :
    x ∈ positiveEvenPart (stageGrade δ ι T S) ↔ (x : C) ∈ positiveEvenPart Cᵢ := by
  classical
  constructor
  · exact fun hx => coe_mem_iSup_of_mem_iSup_stageGrade δ ι T S _ hx
  · intro hx
    obtain ⟨s, hs⟩ := exists_gradedPart_decomposition Cᵢ (x : C)
    have hmemS : ∀ m : ℕ, gradedPart Cᵢ (x : C) m ∈ finiteVariableStage δ ι T S := fun m =>
      gradedPart_mem_finiteVariableStage_of_homogeneous δ ι T
        (IsHomogeneousVariableFamily.coefficient_mem (Cᵢ := Cᵢ) (T := T))
        (IsHomogeneousVariableFamily.variable_homogeneous (Cᵢ := Cᵢ) (ι := ι)) S x.2 m
    have hxsum : x = ∑ m ∈ s,
        (⟨gradedPart Cᵢ (x : C) m, hmemS m⟩ : finiteVariableStage δ ι T S) :=
      Subtype.ext (by push_cast; exact hs)
    rw [hxsum]
    refine Submodule.sum_mem _ fun m _ => ?_
    by_cases hm : ∃ k : ℕ, m = 2 * (k + 1)
    · obtain ⟨k, hk⟩ := hm
      refine Submodule.mem_iSup_of_mem k ?_
      show gradedPart Cᵢ (x : C) m ∈ Cᵢ (2 * (k + 1))
      rw [← hk]
      exact gradedPart_mem Cᵢ _ m
    · rw [show (⟨gradedPart Cᵢ (x : C) m, hmemS m⟩ : finiteVariableStage δ ι T S) = 0 from
        Subtype.ext (gradedPart_eq_zero_of_mem_positiveEvenPart Cᵢ hx hm)]
      exact Submodule.zero_mem _

/-- The inclusion of a finite variable stage into the ambient algebra, as an `R`-algebra
homomorphism for the stage's own algebra structure. It is in this shape that a stage serves as
the coefficient algebra of a *later* stage. -/
public def stageInclusion (S : Finset J) : finiteVariableStage δ ι T S →ₐ[R] C :=
  { (finiteVariableStage δ ι T S).subtype with commutes' := fun _ => rfl }

/-- The inclusion of a finite variable stage is the coercion. -/
@[simp]
public theorem stageInclusion_apply (S : Finset J) (x : finiteVariableStage δ ι T S) :
    stageInclusion δ ι T S x = (x : C) := rfl

/-- A finite variable stage depends on the family of variables only through its values on the
indexing set. -/
public theorem finiteVariableStage_congr (T' : J → C) (S : Finset J)
    (h : ∀ j ∈ S, T j = T' j) :
    finiteVariableStage δ ι T S = finiteVariableStage δ ι T' S := by
  unfold finiteVariableStage
  congr 1
  ext x
  constructor <;> rintro (hx | ⟨j, hj, hx⟩)
  exacts [Or.inl hx, Or.inr ⟨j, hj, by rwa [← h j hj]⟩, Or.inl hx, Or.inr ⟨j, hj, by rwa [h j hj]⟩]

/-- **Adjoining some of the variables and then the rest is adjoining all of them.** A finite
variable stage over the coefficient algebra of an *earlier* stage is the stage over the union of
the two sets of variables. This is what lets the mixed-degree stages be analysed one degree at a
time. -/
public theorem finiteVariableStage_stageInclusion (S₁ S₂ S : Finset J)
    (hS : ∀ j : J, j ∈ S ↔ (j ∈ S₁ ∨ j ∈ S₂)) :
    finiteVariableStage δ (stageInclusion δ ι T S₁) T S₂ = finiteVariableStage δ ι T S := by
  have hS₁ : S₁ ⊆ S := fun j hj => (hS j).2 (Or.inl hj)
  refine le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_le.2 ?_)
  · rintro x (⟨b, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩)
    · exact finiteVariableStage_le_of_subset δ ι T hS₁ b.2
    · exact mem_finiteVariableStage_generator δ ι T ((hS j).2 (Or.inr hj))
    · exact mem_finiteVariableStage_dpow_generator δ ι T ((hS j).2 (Or.inr hj)) n
  · rintro x (⟨p, rfl⟩ | ⟨j, hj, rfl | ⟨n, rfl⟩⟩)
    · exact Subring.subset_closure
        (Or.inl ⟨⟨ι p, mem_finiteVariableStage_coefficient δ ι T S₁ p⟩, rfl⟩)
    · rcases (hS j).1 hj with hj1 | hj2
      · exact Subring.subset_closure
          (Or.inl ⟨⟨T j, mem_finiteVariableStage_generator δ ι T hj1⟩, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨j, hj2, Or.inl rfl⟩)
    · rcases (hS j).1 hj with hj1 | hj2
      · exact Subring.subset_closure
          (Or.inl ⟨⟨δ.dpow n (T j),
            mem_finiteVariableStage_dpow_generator δ ι T hj1 n⟩, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨j, hj2, Or.inr ⟨n, rfl⟩⟩)

/-- The initial finite variable stage is the image of the coefficient algebra. -/
public theorem exists_coefficient_eq_of_mem_finiteVariableStage_empty {x : C}
    (hx : x ∈ finiteVariableStage δ ι T (∅ : Finset J)) : ∃ p : P, ι p = x := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
      rcases hy with ⟨p, rfl⟩ | ⟨c, hc, -⟩
      · exact ⟨p, rfl⟩
      · exact absurd hc (Finset.notMem_empty c)
  | zero => exact ⟨0, map_zero ι⟩
  | one => exact ⟨1, map_one ι⟩
  | add a b _ _ iha ihb =>
      obtain ⟨p, hp⟩ := iha
      obtain ⟨q, hq⟩ := ihb
      exact ⟨p + q, by rw [map_add, hp, hq]⟩
  | neg a _ iha =>
      obtain ⟨p, hp⟩ := iha
      exact ⟨-p, by rw [map_neg, hp]⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨p, hp⟩ := iha
      obtain ⟨q, hq⟩ := ihb
      exact ⟨p * q, by rw [map_mul, hp, hq]⟩

/-- **A finite variable stage is closed under the divided powers of the ambient algebra**, for
variables of *varying* degrees.

`DividedPowers.TateResolution.finiteVariableStage_dpow_mem` is the same statement for variables
of a single degree. The mixed-degree case is reduced to it by induction on a bound for the
degrees: the variables of the top degree are adjoined to the stage generated by the variables of
lower degree, which by induction is itself a divided power subalgebra and so may serve as the
coefficient algebra of the single-degree statement. -/
public theorem finiteVariableStage_dpow_mem_of_homogeneous
    [IsHomogeneousVariableFamily Cᵢ ι T] (deg : J → ℕ) (hdeg : ∀ j : J, T j ∈ Cᵢ (deg j))
    (S : Finset J) (n : ℕ) {x : C} (hx : x ∈ finiteVariableStage δ ι T S)
    (hpos : x ∈ positiveEvenPart Cᵢ) :
    δ.dpow n x ∈ finiteVariableStage δ ι T S := by
  classical
  suffices H : ∀ (N : ℕ) (U : Finset J), (∀ j ∈ U, deg j < N) → ∀ (k : ℕ) (y : C),
      y ∈ finiteVariableStage δ ι T U → y ∈ positiveEvenPart Cᵢ →
      δ.dpow k y ∈ finiteVariableStage δ ι T U by
    exact H (S.sup deg + 1) S (fun j hj => Nat.lt_succ_of_le (Finset.le_sup (f := deg) hj))
      n x hx hpos
  intro N
  induction N with
  | zero =>
      intro U hU k y hy hypos
      have hUempty : U = ∅ :=
        Finset.eq_empty_of_forall_notMem fun j hj => absurd (hU j hj) (by omega)
      subst hUempty
      obtain ⟨p, hp⟩ := exists_coefficient_eq_of_mem_finiteVariableStage_empty δ ι T hy
      have hy0 : y ∈ Cᵢ 0 := hp ▸ IsHomogeneousVariableFamily.coefficient_mem (T := T) p
      rcases positiveEven_homogeneous_eq_zero_or_grade Cᵢ hy0 hypos with hz | ⟨c, hc⟩
      · rcases k with _ | k
        · rw [hz, δ.dpow_zero (Submodule.zero_mem _)]
          exact Subring.one_mem _
        · rw [hz, δ.dpow_zero_eq_zero (Nat.succ_ne_zero k)]
          exact Subring.zero_mem _
      · omega
  | succ N ih =>
      intro U hU k y hy hypos
      have hsplit : ∀ j : J, j ∈ U ↔
          (j ∈ U.filter (fun j => deg j < N) ∨ j ∈ U.filter (fun j => deg j = N)) := by
        intro j
        simp only [Finset.mem_filter]
        refine ⟨fun hj => ?_, fun h => h.elim (fun h => h.1) fun h => h.1⟩
        rcases Nat.lt_or_ge (deg j) N with h | h
        · exact Or.inl ⟨hj, h⟩
        · exact Or.inr ⟨hj, by have := hU j hj; omega⟩
      have hIH : ∀ (k : ℕ) (b : finiteVariableStage δ ι T (U.filter (fun j => deg j < N))),
          (b : C) ∈ positiveEvenPart Cᵢ →
          δ.dpow k (b : C) ∈ finiteVariableStage δ ι T (U.filter (fun j => deg j < N)) :=
        fun k b hb => ih _ (fun j hj => (Finset.mem_filter.1 hj).2) k _ b.2 hb
      have hTT' : ∀ j ∈ U.filter (fun j => deg j = N),
          T j = (fun j => if deg j = N then T j else 0) j := by
        intro j hj
        simp [(Finset.mem_filter.1 hj).2]
      have hstage : finiteVariableStage δ (stageInclusion δ ι T (U.filter (fun j => deg j < N)))
          (fun j => if deg j = N then T j else 0) (U.filter (fun j => deg j = N)) =
          finiteVariableStage δ ι T U := by
        rw [← finiteVariableStage_congr δ (stageInclusion δ ι T (U.filter (fun j => deg j < N)))
          T _ (U.filter (fun j => deg j = N)) hTT']
        exact finiteVariableStage_stageInclusion δ ι T _ _ U hsplit
      have hmain := finiteVariableStage_dpow_mem
        (stageGrade δ ι T (U.filter (fun j => deg j < N))) Cᵢ δ
        (stageInclusion δ ι T (U.filter (fun j => deg j < N)))
        (fun j => if deg j = N then T j else 0) (U.filter (fun j => deg j = N)) N
        (fun _ _ ha => ha)
        (fun j => by
          by_cases h : deg j = N
          · rw [show (if deg j = N then T j else 0) = T j from by simp [h]]
            exact h ▸ hdeg j
          · rw [show (if deg j = N then T j else 0) = 0 from by simp [h]]
            exact Submodule.zero_mem (Cᵢ N))
        (fun k a ha => ⟨⟨δ.dpow k (a : C), hIH k a ha⟩, rfl⟩)
        k y (by rw [hstage]; exact hy) hypos
      rw [hstage] at hmain
      exact hmain

/-- The even part of a finite variable stage sits inside that of the ambient algebra. -/
public theorem mem_evenPart_of_mem_evenPart_stageGrade (S : Finset J)
    {x : finiteVariableStage δ ι T S} (hx : x ∈ evenPart (stageGrade δ ι T S)) :
    (x : C) ∈ evenPart Cᵢ :=
  coe_mem_iSup_of_mem_iSup_stageGrade δ ι T S _ hx

/-- The divided powers of the ambient algebra are defined on all of a finite variable stage,
vanishing outside the positive even part, and take values in the stage. -/
public theorem stage_dpow_mem [IsHomogeneousVariableFamily Cᵢ ι T] (deg : J → ℕ)
    (hdeg : ∀ j : J, T j ∈ Cᵢ (deg j)) (S : Finset J) (n : ℕ)
    (x : finiteVariableStage δ ι T S) :
    δ.dpow n (x : C) ∈ finiteVariableStage δ ι T S := by
  by_cases hx : (x : C) ∈ positiveEvenPart Cᵢ
  · exact finiteVariableStage_dpow_mem_of_homogeneous δ ι T deg hdeg S n x.2 hx
  · rw [δ.dpow_null hx]
    exact Subring.zero_mem _

/-- **The divided power structure of a finite variable stage**: the restriction of that of the
ambient algebra. Every axiom is inherited, because the positive even part and the even part of
the stage are cut out by those of the ambient algebra and the inclusion is a ring homomorphism. -/
public noncomputable def stageDividedPowers [IsHomogeneousVariableFamily Cᵢ ι T] (deg : J → ℕ)
    (hdeg : ∀ j : J, T j ∈ Cᵢ (deg j)) (S : Finset J) :
    DividedPowerStructure (stageGrade δ ι T S) where
  dpow n x := ⟨δ.dpow n (x : C), stage_dpow_mem δ ι T deg hdeg S n x⟩
  dpow_null {n x} hx :=
    Subtype.ext (δ.dpow_null fun h => hx ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).2 h))
  dpow_zero {x} hx :=
    Subtype.ext (δ.dpow_zero ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx))
  dpow_one {x} hx :=
    Subtype.ext (δ.dpow_one ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx))
  dpow_mem {n x} hn hx :=
    (mem_positiveEvenPart_stageGrade_iff δ ι T S _).2
      (δ.dpow_mem hn ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx))
  dpow_mem_grade {n e x} hn hx hxe :=
    δ.dpow_mem_grade hn ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx) hxe
  dpow_mul {m n x} hx := by
    refine Subtype.ext ?_
    push_cast
    exact δ.dpow_mul ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx)
  dpow_mul_even {n x y} hn hx hy := by
    refine Subtype.ext ?_
    push_cast
    exact δ.dpow_mul_even hn (mem_evenPart_of_mem_evenPart_stageGrade δ ι T S hx)
      ((mem_positiveEvenPart_stageGrade_iff δ ι T S y).1 hy)
  dpow_mul_odd {n e e' x y} hn hx hy := by
    refine Subtype.ext ?_
    push_cast
    exact δ.dpow_mul_odd hn hx hy
  dpow_add {n x y} hx hy := by
    refine Subtype.ext ?_
    push_cast
    exact δ.dpow_add ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx)
      ((mem_positiveEvenPart_stageGrade_iff δ ι T S y).1 hy)
  dpow_dpow {m n x} hm hn hx := by
    refine Subtype.ext ?_
    push_cast
    exact δ.dpow_dpow hm hn ((mem_positiveEvenPart_stageGrade_iff δ ι T S x).1 hx)

/-- The divided powers of a finite variable stage are those of the ambient algebra. -/
@[simp]
public theorem stageDividedPowers_dpow [IsHomogeneousVariableFamily Cᵢ ι T] (deg : J → ℕ)
    (hdeg : ∀ j : J, T j ∈ Cᵢ (deg j)) (S : Finset J) (n : ℕ)
    (x : finiteVariableStage δ ι T S) :
    ((stageDividedPowers δ ι T deg hdeg S).dpow n x : C) = δ.dpow n (x : C) := rfl

/-- A finite variable stage, bundled as a graded divided power algebra over `R`. -/
public noncomputable def stageDPAlgebra [IsHomogeneousVariableFamily Cᵢ ι T] (deg : J → ℕ)
    (hdeg : ∀ j : J, T j ∈ Cᵢ (deg j)) (S : Finset J) : GradedDPAlgebra.{u, z} R where
  carrier := finiteVariableStage δ ι T S
  ring := inferInstance
  algebra := stageAlgebra δ ι T S
  grade := stageGrade δ ι T S
  graded := stageGradedAlgebra δ ι T S
  strict := stageStrictlyGradedComm δ ι T S
  gamma := stageDividedPowers δ ι T deg hdeg S

end MixedStage

end DividedPowers.TateResolution

end
