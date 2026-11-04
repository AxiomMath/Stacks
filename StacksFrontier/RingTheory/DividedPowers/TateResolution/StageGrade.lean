module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradeBasis

/-!
# The grading and the bases of a successor variable stage

A graded divided-power polynomial algebra presents its finite variable stages through its
`successor` field: adjoining one variable to a stage is a ring equivalence from the
corresponding one-variable extension onto the next stage, which fixes the coefficients and
detects the ambient grading. This file turns that presentation into the two facts an induction
over the adjoined variables needs.

The first is that the grading carried by a stage is not a free choice: it is the restriction of
the ambient grading. Composing the successor clause's grade detection with the membership
criterion of the one-variable extension at a coefficient gives
`b ∈ Sᵢ m ↔ (b : A) ∈ Aᵢ m`, so any two gradings presented this way agree, and a basis of a
stage's homogeneous piece is a basis of the ambient piece cut down to the stage.

The second is that spanning sets and independent sets of a homogeneous piece transfer along the
successor equivalence. Together with the step families of `GradeBasis.lean` this is one step of
the induction that builds a monotone family of bases for the homogeneous pieces of the whole
algebra.

## Main definitions

* `DividedPowers.TateResolution.ringEquivToLinearEquiv` — a ring equivalence commuting with the
  base-ring structure map, viewed as an `R`-linear equivalence.

## Main results

* `DividedPowers.TateResolution.OddVariableExtension.inclusion_mem_grade_iff` — a coefficient is
  homogeneous in an odd variable extension exactly when it was homogeneous already.
* `DividedPowers.TateResolution.mem_iff_of_oddVariableEquiv` and
  `mem_iff_of_evenVariableEquiv` — the grading of a stage presented by a successor equivalence is
  the restriction of the ambient grading.
* `DividedPowers.TateResolution.map_grade_of_ringEquiv` — a grading-detecting ring equivalence
  carries a homogeneous piece onto the corresponding one.
* `DividedPowers.TateResolution.span_image_of_ringEquiv` and
  `linearIndepOn_image_of_ringEquiv` — spanning sets and independent sets of a homogeneous piece
  transfer along such an equivalence.

## Implementation notes

The two stage-grading results are stated against an arbitrary pair of functions into the ambient
algebra rather than against `finiteVariableStage` and its subring coercions. The successor clause
supplies the coercions of two different stages composed with the equivalence, and these are
plain functions there, not algebra maps: the algebra structure on a stage is handed out
existentially by that clause and is not stated to be the restriction of the ambient one. Only the
two displayed equations are used, so taking the functions as parameters is both weaker and
shorter than reconstructing the subring picture.

`ringEquivToLinearEquiv` is the `R`-linear equivalence underlying `gradeLinearEquivOfRingEquiv`,
needed here on the whole algebra rather than on a single homogeneous piece, in order to move
spans and independent sets across.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

section Odd

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

namespace OddVariableExtension

/-- A coefficient is homogeneous of degree `m` in an odd variable extension exactly when it is
homogeneous of degree `m` already: its component along the new variable is zero. -/
public theorem inclusion_mem_grade_iff (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d m : ℕ) (a : A) :
    inclusion Aᵢ d a ∈ grade Aᵢ d m ↔ a ∈ Aᵢ m := by
  refine ⟨fun h => ((mem_grade_iff Aᵢ d m _).mp h).1, inclusion_mem_grade Aᵢ d m⟩

end OddVariableExtension

end Odd

section StageGrading

variable {R : Type u} {A : Type v} {B : Type w} {E : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring E]

/-- The grading of a stage presented as an odd variable extension of an earlier stage is the
restriction of the ambient grading: a stage element is homogeneous of degree `m` exactly when its
image in the ambient algebra is.

Only two components of the successor presentation are used — that the equivalence fixes the
coefficients, and that it detects the ambient grading — so they are taken as hypotheses, with the
maps of the two stages into the ambient algebra as plain functions. -/
public theorem mem_iff_of_oddVariableEquiv
    (Aᵢ : ℕ → Submodule R A) (Bᵢ : ℕ → Submodule R B) [GradedAlgebra Bᵢ] (d : ℕ)
    (e : OddVariableExtension Bᵢ d ≃+* E) (f : B → A) (g : E → A)
    (hf : ∀ b : B, g (e (OddVariableExtension.inclusion Bᵢ d b)) = f b)
    (hgrade : ∀ (m : ℕ) (x : OddVariableExtension Bᵢ d),
      x ∈ OddVariableExtension.grade Bᵢ d m ↔ g (e x) ∈ Aᵢ m)
    (m : ℕ) (b : B) :
    b ∈ Bᵢ m ↔ f b ∈ Aᵢ m := by
  rw [← OddVariableExtension.inclusion_mem_grade_iff Bᵢ d m b, hgrade, hf]

/-- The grading of a stage presented as an even variable extension of an earlier stage is the
restriction of the ambient grading. This is the even counterpart of
`mem_iff_of_oddVariableEquiv`, with the same two hypotheses. -/
public theorem mem_iff_of_evenVariableEquiv
    (Aᵢ : ℕ → Submodule R A) (Bᵢ : ℕ → Submodule R B) (d : ℕ)
    (e : EvenVariableAlgebra B ≃+* E) (f : B → A) (g : E → A)
    (hf : ∀ b : B, g (e (EvenVariableAlgebra.coeffEmbedding b)) = f b)
    (hgrade : ∀ (m : ℕ) (x : EvenVariableAlgebra B),
      x ∈ EvenVariableAlgebra.grade Bᵢ d m ↔ g (e x) ∈ Aᵢ m)
    (m : ℕ) (b : B) :
    b ∈ Bᵢ m ↔ f b ∈ Aᵢ m := by
  rw [← EvenVariableAlgebra.coeffEmbedding_mem_grade_iff Bᵢ d m b, hgrade, hf]

end StageGrading

section Transfer

variable {R : Type u} [CommRing R] {B C : Type v} [Ring B] [Ring C] [Algebra R B] [Algebra R C]

/-- A ring equivalence commuting with the base-ring structure map, as an `R`-linear
equivalence. -/
public def ringEquivToLinearEquiv (e : B ≃+* C)
    (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r) :
    B ≃ₗ[R] C where
  toFun := e
  map_add' := map_add e
  map_smul' := map_smul_of_algebraMap e he
  invFun := e.symm
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply

/-- A grading-detecting ring equivalence commuting with the base-ring structure map carries a
homogeneous piece onto the corresponding homogeneous piece. -/
public theorem map_grade_of_ringEquiv (Bᵢ : ℕ → Submodule R B) (Cᵢ : ℕ → Submodule R C)
    (e : B ≃+* C) (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ e x ∈ Cᵢ m) (m : ℕ) :
    (Bᵢ m).map (ringEquivToLinearEquiv e he).toLinearMap = Cᵢ m := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (hgrade m x).mp hx
  · refine ⟨e.symm y, (hgrade m (e.symm y)).mpr ?_, e.apply_symm_apply y⟩
    rw [e.apply_symm_apply]
    exact hy

/-- A spanning set of a homogeneous piece transfers along a grading-detecting ring equivalence. -/
public theorem span_image_of_ringEquiv (Bᵢ : ℕ → Submodule R B) (Cᵢ : ℕ → Submodule R C)
    (e : B ≃+* C) (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ e x ∈ Cᵢ m) (m : ℕ) (s : Set B)
    (hs : Submodule.span R s = Bᵢ m) :
    Submodule.span R (e '' s) = Cᵢ m := by
  rw [← map_grade_of_ringEquiv Bᵢ Cᵢ e he hgrade m, ← hs, Submodule.map_span]
  rfl

/-- An independent set transfers along a ring equivalence commuting with the base-ring structure
map. -/
public theorem linearIndepOn_image_of_ringEquiv (e : B ≃+* C)
    (he : ∀ r : R, e (algebraMap R B r) = algebraMap R C r) (s : Set B)
    (hs : LinearIndepOn R id s) :
    LinearIndepOn R id (e '' s) := by
  exact LinearIndepOn.image (f := (ringEquivToLinearEquiv e he).toLinearMap) hs (by simp)

end Transfer

end DividedPowers.TateResolution

end
