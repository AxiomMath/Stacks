module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineFibreBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalGradedCategory

/-!
# The algebra `Corr⁰(P¹_k, P¹_k) = ℚ × ℚ`

Let `k` be a field and `X = P¹_k`. Example 0FG6 states that
`Corr⁰(X, X) = CH¹(X × X) ⊗ ℚ = CH₁(X × X) ⊗ ℚ`, that for a `k`-rational point `x` the cycles
`c₀ = [x × X]` and `c₂ = [X × x]` satisfy `1 = [Δ] = c₀ + c₂` and the composition rules
`c₀ ∘ c₀ = c₀`, `c₀ ∘ c₂ = 0`, `c₂ ∘ c₀ = 0`, `c₂ ∘ c₂ = c₂`, and that consequently
`Corr⁰(X, X) = ℚ × ℚ` as a `ℚ`-algebra. This file proves all of it for the actual projective line
`Stacks.WeilCohomology.projectiveLineObj k` in the actual category of correspondences
`Stacks.WeilCohomology.canonicalCorrespondenceCompositionData k`, whose composition is
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` formed with the Gysin classes of the diagonals.

## Main definitions

* `CategoryTheory.GradedCategory.degreeZeroSubalgebra`: the subalgebra of degree-zero
  endomorphisms of an object of a graded category; for correspondences, the algebra
  `Corr⁰(X, X)`.
* `Stacks.WeilCohomology.projectiveLineCorrEquiv`: `Corr⁰(P¹, P¹) = CH₁(P¹ × P¹) ⊗ ℚ`.
* `Stacks.WeilCohomology.projectiveLinePointFibreCorr` and
  `Stacks.WeilCohomology.projectiveLineFibrePointCorr`: the correspondences `c₀ = [x × P¹]` and
  `c₂ = [P¹ × x]`.
* `Stacks.WeilCohomology.projectiveLineCorrBasis`: `c₀`, `c₂` are a basis of `Corr⁰(P¹, P¹)`.
* `Stacks.WeilCohomology.projectiveLineCorrAlgEquiv`: `ℚ × ℚ ≃ Corr⁰(P¹, P¹)` as `ℚ`-algebras.

## Main results

* `Stacks.WeilCohomology.projectiveLine_diagonal_eq_add`: `[Δ] = c₀ + c₂`.
* `Stacks.WeilCohomology.projectiveLine_pointFibre_comp_pointFibre` and the three companion
  lemmas: the composition rules.

## Implementation notes

The source's `c' ∘ c` is `c ≫ c'` in the category of correspondences, and in the endomorphism
ring `c' ∘ c = c' * c`. The composition rule `c₀ ∘ c₀ = c₀` is graph functoriality (Stacks 0FG3):
`c₀` is the graph class of the constant morphism `X → x → X`, which is idempotent. The relation
`[Δ] = c₀ + c₂` is `Stacks.WeilCohomology.diagonal_cycle_eq_add_fibres` after `⊗ ℚ`, and the other
three rules follow from these two, as the source's proof observes for `c₂ ∘ c₀ = 0`.

## References

* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped TensorProduct

universe u

/-! ### Degree-zero endomorphisms -/

namespace CategoryTheory.GradedCategory

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [GradedCategory R C]

/-- The degree-zero endomorphisms of an object of a graded category, a subalgebra of its
endomorphism algebra: identities have degree zero and composition adds degrees. -/
def degreeZeroSubalgebra (X : C) : Subalgebra R (End X) where
  carrier := (grade (R := R) X X 0 : Set (X ⟶ X))
  mul_mem' {a b} ha hb := by
    have h := comp_mem (R := R) ha hb
    rw [add_zero] at h
    exact h
  add_mem' ha hb := (grade (R := R) X X 0).add_mem ha hb
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (grade (R := R) X X 0).smul_mem r (id_mem (R := R) X)

/-- An endomorphism lies in the degree-zero subalgebra if and only if it has degree zero. -/
theorem mem_degreeZeroSubalgebra {X : C} {f : End X} :
    f ∈ degreeZeroSubalgebra (R := R) X ↔ f ∈ grade (R := R) X X 0 :=
  Iff.rfl

end CategoryTheory.GradedCategory

namespace Stacks.WeilCohomology

open CategoryTheory.GradedCategory

variable (k : Type u) [Field k]

/-- The projective line `P¹_k`. -/
local notation "ℙ" => relativeProjectiveLine (Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k`. -/
local notation "σ" => (ℙ ↘ Spec (CommRingCat.of k))

/-- The structure morphism of `P¹_k ×_k P¹_k`. -/
local notation "σ₂" => pullback.fst σ σ ≫ σ

/-- `P¹_k` as an object of the category of correspondences. -/
local notation "𝐗" => Functor.obj (canonicalGraphFunctor k) (Opposite.op (projectiveLineObj k))

/-- The projective line has relative dimension one over `k`. -/
theorem relativeDimension_projectiveLine : RelativeDimension σ 1 := by
  have h := relativeDimension_of_isIntegral_over_field k σ
  rwa [relativeDimension_projectiveLine_genericPoint] at h

/-- `Corr⁰(P¹_k, P¹_k) = CH¹(P¹ × P¹) ⊗ ℚ = CH₁(P¹ × P¹) ⊗ ℚ`: a correspondence of degree zero
on the projective line is a rational cycle class of dimension one on `P¹_k ×_k P¹_k`. -/
@[stacks 0FG6 "Corr⁰(X, X) = CH¹(X × X) ⊗ ℚ = CH₁(X × X) ⊗ ℚ"]
def projectiveLineCorrEquiv :
    SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0 ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) σ σ 1 0 :=
  (SmoothProjectiveCorr.toCorr (projectiveLineObj k) (projectiveLineObj k) 0).trans
    (corrEquivCorrespondence k σ σ (relativeDimension_projectiveLine k)
      (relativeDimension_projectiveLine k) 0)

/-- A basis of `Corr⁰(P¹_k, P¹_k)` over `ℚ`, formed by `c₀ = [x × P¹]` and `c₂ = [P¹ × x]`. -/
@[stacks 0FG6 "c₀ and c₂ are a basis of Corr⁰(X, X)"]
def projectiveLineCorrBasis :
    Module.Basis (Fin 2) ℚ (SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0) :=
  (projectiveLineFibreBasis k).map (projectiveLineCorrEquiv k).symm

/-- The degree-zero endomorphisms of `P¹_k` in the category of correspondences are the
correspondences of degree zero, `Corr⁰(P¹_k, P¹_k)`. -/
def projectiveLineDegreeZeroEquiv :
    SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0 ≃ₗ[ℚ]
      degreeZeroSubalgebra (R := ℚ) 𝐗 :=
  LinearEquiv.ofBijective
    ((DirectSum.lof ℚ ℤ
        (fun i ↦ SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0).codRestrict
      (degreeZeroSubalgebra (R := ℚ) 𝐗).toSubmodule
      fun c ↦ (GradedCompositionData.mem_grade_iff _).2 ⟨c, (DirectSum.lof_eq_of ℚ ℤ _ 0 c).symm⟩)
    ⟨fun a b h ↦ DirectSum.of_injective (β := fun i ↦
        SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0
        (((DirectSum.lof_eq_of ℚ ℤ _ 0 a).symm.trans (congrArg Subtype.val h)).trans
          (DirectSum.lof_eq_of ℚ ℤ _ 0 b)),
      fun ⟨f, hf⟩ ↦ by
        obtain ⟨a, ha⟩ := (GradedCompositionData.mem_grade_iff _).1 hf
        exact ⟨a, Subtype.ext ((DirectSum.lof_eq_of ℚ ℤ _ 0 a).trans ha)⟩⟩

/-- `Stacks.WeilCohomology.projectiveLineDegreeZeroEquiv` sends a correspondence of degree zero
to its degree-zero component as an endomorphism of `P¹_k`. -/
theorem projectiveLineDegreeZeroEquiv_apply
    (c : SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0) :
    (projectiveLineDegreeZeroEquiv k c : End 𝐗) =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0
        c :=
  DirectSum.lof_eq_of ℚ ℤ _ 0 c

/-- The basis `c₀, c₂` of the degree-zero endomorphism algebra of `P¹_k`. -/
def projectiveLineDegreeZeroBasis :
    Module.Basis (Fin 2) ℚ (degreeZeroSubalgebra (R := ℚ) 𝐗) :=
  (projectiveLineCorrBasis k).map (projectiveLineDegreeZeroEquiv k)

variable {k} (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- The correspondence `c₀ = [x × P¹] ∈ Corr⁰(P¹_k, P¹_k)` of a rational point `x`. -/
@[stacks 0FG6 "c₀ = [x × X]"]
def projectiveLinePointFibreCorr :
    SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0 :=
  (projectiveLineCorrEquiv k).symm (pointFibreCorrespondence (fieldChowSituation k) σ x hx 1)

/-- The correspondence `c₂ = [P¹ × x] ∈ Corr⁰(P¹_k, P¹_k)` of a rational point `x`. -/
@[stacks 0FG6 "c₂ = [X × x]"]
def projectiveLineFibrePointCorr :
    SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) 0 :=
  (projectiveLineCorrEquiv k).symm (fibrePointCorrespondence (fieldChowSituation k) σ x hx 1)

attribute [local instance] isClosedImmersion_graphMorphism

/-- The constant morphism `P¹ → x → P¹` of smooth projective schemes over `k`. -/
def projectiveLineConstant : projectiveLineObj k ⟶ projectiveLineObj k :=
  ObjectProperty.homMk (Over.homMk (σ ≫ x) (constantMorphism_comp_base σ x hx))

/-- The constant morphism `P¹ → x → P¹` is idempotent. -/
theorem projectiveLineConstant_comp_self :
    projectiveLineConstant x hx ≫ projectiveLineConstant x hx = projectiveLineConstant x hx := by
  ext
  show (σ ≫ x) ≫ σ ≫ x = σ ≫ x
  rw [← Category.assoc, constantMorphism_comp_base σ x hx]

/-- The graph correspondence of the constant morphism `P¹ → x → P¹` is the graph correspondence
of the morphism `σ ≫ x` over `k`. -/
theorem graphCorrespondenceSP_projectiveLineConstant :
    SmoothProjectiveCorr.toCorr (projectiveLineObj k) (projectiveLineObj k) 0
        (graphCorrespondenceSP (projectiveLineConstant x hx)) =
      graphCorr k σ σ (σ ≫ x) (constantMorphism_comp_base σ x hx) :=
  rfl

/-- On cycle classes, the graph of the constant morphism `P¹ → x → P¹` is the class of the graph
`x × P¹ ⊆ P¹ × P¹`. -/
theorem projectiveLineCorrEquiv_graphCorrespondenceSP :
    projectiveLineCorrEquiv k (graphCorrespondenceSP (projectiveLineConstant x hx)) =
      graphCorrespondence σ σ (σ ≫ x) (constantMorphism_comp_base σ x hx) 1 := by
  rw [projectiveLineCorrEquiv, LinearEquiv.trans_apply,
    graphCorrespondenceSP_projectiveLineConstant]
  exact corrEquivCorrespondence_graphCorr k σ σ (relativeDimension_projectiveLine k)
    (relativeDimension_projectiveLine k) (σ ≫ x) _

/-- `c₀` is the graph class of the constant morphism `P¹ → x → P¹`. -/
theorem projectiveLinePointFibreCorr_eq_graph :
    projectiveLinePointFibreCorr x hx = graphCorrespondenceSP (projectiveLineConstant x hx) := by
  rw [projectiveLinePointFibreCorr, LinearEquiv.symm_apply_eq,
    projectiveLineCorrEquiv_graphCorrespondenceSP, pointFibreCorrespondence, graphCorrespondence,
    cycle_pointFibre_imageι x hx]

/-- The diagonal correspondence of `P¹_k` is `c₀ + c₂`, read on cycle classes. -/
theorem diagonalCorr_projectiveLine :
    projectiveLineCorrEquiv k (correspondenceDiagonal k (projectiveLineObj k)) =
      pointFibreCorrespondence (fieldChowSituation k) σ x hx 1 +
        fibrePointCorrespondence (fieldChowSituation k) σ x hx 1 := by
  show corrEquivCorrespondence k σ σ (relativeDimension_projectiveLine k)
      (relativeDimension_projectiveLine k) 0 (diagonalCorr k σ) = _
  rw [corrEquivCorrespondence_diagonalCorr, graphCorrespondence, pointFibreCorrespondence,
    fibrePointCorrespondence, cycle_pointFibre_imageι x hx, cycle_fibrePoint_imageι x hx,
    ← TensorProduct.tmul_add]
  exact congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) (diagonal_cycle_eq_add_fibres x hx)

/-- `1 = [Δ] = c₀ + c₂` in `Corr⁰(P¹_k, P¹_k)`. -/
@[stacks 0FG6 "1 = [Δ] = c₀ + c₂"]
theorem projectiveLine_diagonal_eq_add :
    (canonicalCorrespondenceCompositionData k).diagonal (projectiveLineObj k) =
      projectiveLinePointFibreCorr x hx + projectiveLineFibrePointCorr x hx := by
  rw [projectiveLinePointFibreCorr, projectiveLineFibrePointCorr, ← map_add,
    LinearEquiv.eq_symm_apply]
  exact diagonalCorr_projectiveLine x hx

/-- The correspondence `c₀` as an endomorphism of `P¹_k` in the category of correspondences. -/
abbrev projectiveLinePointFibreHom : 𝐗 ⟶ 𝐗 :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0
    (projectiveLinePointFibreCorr x hx)

/-- The correspondence `c₂` as an endomorphism of `P¹_k` in the category of correspondences. -/
abbrev projectiveLineFibrePointHom : 𝐗 ⟶ 𝐗 :=
  DirectSum.of (fun i ↦ SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0
    (projectiveLineFibrePointCorr x hx)

/-- `𝟙 = c₀ + c₂` in the category of correspondences. -/
theorem projectiveLine_id_eq_add :
    𝟙 𝐗 = projectiveLinePointFibreHom x hx + projectiveLineFibrePointHom x hx := by
  rw [GradedCompositionData.id_eq]
  exact (congrArg (DirectSum.of
    (fun i ↦ SmoothProjectiveCorr (projectiveLineObj k) (projectiveLineObj k) i) 0)
    (projectiveLine_diagonal_eq_add x hx)).trans (map_add _ _ _)

/-- `c₀ ∘ c₀ = c₀` in the category of correspondences. -/
@[stacks 0FG6 "c₀ ∘ c₀ = c₀"]
theorem projectiveLine_pointFibre_comp_pointFibre :
    projectiveLinePointFibreHom x hx ≫ projectiveLinePointFibreHom x hx =
      projectiveLinePointFibreHom x hx := by
  have h := ((canonicalGraphFunctor k).map_comp (projectiveLineConstant x hx).op
    (projectiveLineConstant x hx).op).symm
  rw [← op_comp, projectiveLineConstant_comp_self] at h
  have he : projectiveLinePointFibreHom x hx =
      (canonicalGraphFunctor k).map (projectiveLineConstant x hx).op := by
    simp only [projectiveLinePointFibreHom, projectiveLinePointFibreCorr_eq_graph]
    rfl
  rw [he]
  exact h

/-- `c₀ ∘ c₂ = 0` in the category of correspondences. -/
@[stacks 0FG6 "c₀ ∘ c₂ = 0"]
theorem projectiveLine_fibrePoint_comp_pointFibre :
    projectiveLineFibrePointHom x hx ≫ projectiveLinePointFibreHom x hx = 0 :=
  mul_eq_zero_of_add_eq_one (A := End 𝐗) (projectiveLine_id_eq_add x hx).symm
    (projectiveLine_pointFibre_comp_pointFibre x hx)

/-- `c₂ ∘ c₀ = 0` in the category of correspondences. -/
@[stacks 0FG6 "c₂ ∘ c₀ = 0"]
theorem projectiveLine_pointFibre_comp_fibrePoint :
    projectiveLinePointFibreHom x hx ≫ projectiveLineFibrePointHom x hx = 0 :=
  mul_eq_zero_of_add_eq_one' (A := End 𝐗) (projectiveLine_id_eq_add x hx).symm
    (projectiveLine_pointFibre_comp_pointFibre x hx)

/-- `c₂ ∘ c₂ = c₂` in the category of correspondences. -/
@[stacks 0FG6 "c₂ ∘ c₂ = c₂"]
theorem projectiveLine_fibrePoint_comp_fibrePoint :
    projectiveLineFibrePointHom x hx ≫ projectiveLineFibrePointHom x hx =
      projectiveLineFibrePointHom x hx :=
  mul_self_of_add_eq_one (A := End 𝐗) (projectiveLine_id_eq_add x hx).symm
    (projectiveLine_pointFibre_comp_pointFibre x hx)

/-! ### The basis `c₀, c₂` and the algebra `ℚ × ℚ` -/

/-- A vector of `Stacks.WeilCohomology.projectiveLineCorrBasis` whose fibre basis vector is `c`
is the corresponding correspondence. -/
private theorem projectiveLineCorrBasis_eq_symm {i : Fin 2}
    {c : Correspondence (fieldChowSituation k) σ σ 1 0} (h : projectiveLineFibreBasis k i = c) :
    projectiveLineCorrBasis k i = (projectiveLineCorrEquiv k).symm c := by
  rw [projectiveLineCorrBasis, Module.Basis.map_apply, h]

/-- The first vector of `Stacks.WeilCohomology.projectiveLineCorrBasis` is `c₀`. -/
theorem projectiveLineCorrBasis_zero : projectiveLineCorrBasis k 0 =
    projectiveLinePointFibreCorr x hx :=
  projectiveLineCorrBasis_eq_symm (projectiveLineFibreBasis_zero x hx)

/-- The second vector of `Stacks.WeilCohomology.projectiveLineCorrBasis` is `c₂`. -/
theorem projectiveLineCorrBasis_one : projectiveLineCorrBasis k 1 =
    projectiveLineFibrePointCorr x hx :=
  projectiveLineCorrBasis_eq_symm (projectiveLineFibreBasis_one x hx)

/-- The first vector of `Stacks.WeilCohomology.projectiveLineDegreeZeroBasis` is `c₀`. -/
theorem projectiveLineDegreeZeroBasis_zero :
    (projectiveLineDegreeZeroBasis k 0 : End 𝐗) = projectiveLinePointFibreHom x hx :=
  (projectiveLineDegreeZeroEquiv_apply k _).trans (congrArg _ (projectiveLineCorrBasis_zero x hx))

/-- The second vector of `Stacks.WeilCohomology.projectiveLineDegreeZeroBasis` is `c₂`. -/
theorem projectiveLineDegreeZeroBasis_one :
    (projectiveLineDegreeZeroBasis k 1 : End 𝐗) = projectiveLineFibrePointHom x hx :=
  (projectiveLineDegreeZeroEquiv_apply k _).trans (congrArg _ (projectiveLineCorrBasis_one x hx))

variable (k)

/-- The two vectors of `Stacks.WeilCohomology.projectiveLineDegreeZeroBasis` sum to `1`. -/
theorem projectiveLineDegreeZeroBasis_add :
    projectiveLineDegreeZeroBasis k 0 + projectiveLineDegreeZeroBasis k 1 = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_add, projectiveLineDegreeZeroBasis_zero, projectiveLineDegreeZeroBasis_one,
      Subalgebra.coe_one, End.one_def,
      projectiveLine_id_eq_add (lineInfinitySection _) (lineInfinitySection_comp _)])

/-- The first vector of `Stacks.WeilCohomology.projectiveLineDegreeZeroBasis` is idempotent. -/
theorem projectiveLineDegreeZeroBasis_mul_self :
    projectiveLineDegreeZeroBasis k 0 * projectiveLineDegreeZeroBasis k 0 =
      projectiveLineDegreeZeroBasis k 0 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, projectiveLineDegreeZeroBasis_zero, End.mul_def,
      projectiveLine_pointFibre_comp_pointFibre (lineInfinitySection _)
        (lineInfinitySection_comp _)])

/-- `Corr⁰(P¹_k, P¹_k) = ℚ × ℚ` as a `ℚ`-algebra: the degree-zero endomorphisms of `P¹_k` in the
category of correspondences, with composition as multiplication, are the product algebra, via
`(a, b) ↦ a c₀ + b c₂`. -/
@[stacks 0FG6 "Corr⁰(X, X) = ℚ × ℚ as a ℚ-algebra"]
def projectiveLineCorrAlgEquiv : (ℚ × ℚ) ≃ₐ[ℚ] degreeZeroSubalgebra (R := ℚ) 𝐗 :=
  algEquivProdOfBasisOfAddEqOne (projectiveLineDegreeZeroBasis k)
    (projectiveLineDegreeZeroBasis_add k) (projectiveLineDegreeZeroBasis_mul_self k)

variable {k}

/-- `Stacks.WeilCohomology.projectiveLineCorrAlgEquiv` sends `(a, b)` to `a c₀ + b c₂`. -/
theorem projectiveLineCorrAlgEquiv_apply (y : ℚ × ℚ) :
    (projectiveLineCorrAlgEquiv k y : End 𝐗) =
      y.1 • projectiveLinePointFibreHom x hx + y.2 • projectiveLineFibrePointHom x hx := by
  rw [projectiveLineCorrAlgEquiv, algEquivProdOfBasisOfAddEqOne_apply, Subalgebra.coe_add,
    Subalgebra.coe_smul, Subalgebra.coe_smul, projectiveLineDegreeZeroBasis_zero,
    projectiveLineDegreeZeroBasis_one]

end Stacks.WeilCohomology

end
