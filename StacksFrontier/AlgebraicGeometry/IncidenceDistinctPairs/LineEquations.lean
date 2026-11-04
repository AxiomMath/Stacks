module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap

/-!
# The collinearity equations of two distinct points cut out the line through them

The collinearity equations of Tag 0B1R are the `3 × 3` determinants `det (fᵢ (wⱼ))` formed from
the linear functionals cutting out three points of `𝐏(V)` and three vectors of `V`. Expanded
along the third row they say that one vector of `V`, built from the `2 × 2` minors of the first
two functionals, vanishes at the third point. This file proves, over an arbitrary field, what
those equations say: if all of them vanish and the first two points are distinct, then the third
point lies on the line joining them, and that line has dimension one.

This is the linear-algebra content of the fibre of the incidence variety over a pair of distinct
points. Two features of that situation dictate the shape.

The first two points are given by *functionals*, not as closed points:
the fibre over a point `w` of the base lives over the residue field `κ(w)`, which is not
algebraically closed, and there the two points of the pair are `κ(w)`-rational but not closed, so
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_eq_linearFunctionalPoint`, which produces the
functional from a closed point, does not apply.

The third point is *arbitrary*: it ranges over the fibre, which has points that are not rational
over `κ(w)` and so are cut out by no functional at all. The hypothesis on it is therefore that
the minor vector lies in its submodule of degree-one equations, which is what the vanishing of
the determinant becomes when the third row is the one that varies.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.minorCombination`: the vector
  `∑ⱼ ± (2 × 2 minor of the first two functionals) • wⱼ`, the third-row expansion of the
  collinearity determinant.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.apply_minorCombination`: a third functional applied
  to that vector is the collinearity determinant.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ker_ne_ker_of_linearFunctionalPoint_ne`: distinct
  points cut out by functionals have different kernels.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.le_of_forall_minorCombination_mem`: **the core.** If
  every minor vector lies in a submodule `N` and the two functionals have different kernels, then
  their common kernel lies in `N`.
* `mem_linearSubspace_lineSubmodule_of_pointSubmodule_eq_ker`: **an arbitrary third point
  satisfying the collinearity equations lies on the line joining the first two**, the first two
  being given by their degree-one equations. This is the form the fibre of the incidence variety
  consumes; `mem_linearSubspace_lineSubmodule_of_forall_mem` is its `linearFunctionalPoint`
  corollary.
* `finrank_quotient_lineSubmodule_of_pointSubmodule_eq_ker` and
  `topologicalKrullDim_linearSubspace_lineSubmodule_of_pointSubmodule_eq_ker`: that line has
  corank two, hence dimension one, over an arbitrary field.
* `ker_inf_ker_le_ker_of_forall_det_eq_zero` and
  `mem_linearSubspace_lineSubmodule_of_forall_det_eq_zero`: the same two statements for a third
  point cut out by a functional, where the hypothesis is the vanishing of the determinant itself.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_lineSubmodule_linearFunctionalPoint`
  and `topologicalKrullDim_linearSubspace_lineSubmodule_linearFunctionalPoint`: **the line
  through two distinct points cut out by functionals has corank two, hence dimension one**, over
  an arbitrary field.

## Implementation notes

The core is one computation in each of two symmetric cases. Different kernels means one of the
two containments fails, so there is a vector `a` killed by one functional and not the other;
completing it by a vector `b` the other does not kill, and putting the vector `v` of the common
kernel in the third slot, every minor but one vanishes and the minor vector becomes a *nonzero*
scalar multiple of `v`.

That both functionals are nonzero is a hypothesis and not a consequence of the kernels differing:
for `f = 0` the kernels differ as soon as `g ≠ 0`, and the conclusion is then false.

The corank-two statement is
`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_inf_ker_eq_two` together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_linearFunctionalPoint`; the hypothesis
it needs, that the kernels differ, comes from the points differing by
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace_ker`, which identifies the linear
subspace cut out by a kernel with the single point of that functional.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The minor vector -/

/-- **The third-row expansion of the collinearity determinant**, as a vector of `V`: the signed
`2 × 2` minors of two functionals on a triple of vectors, contracted against that triple. A third
functional applied to it is the `3 × 3` determinant. -/
public def minorCombination (f g : Module.Dual k V) (w : Fin 3 → V) : V :=
  (f (w 1) * g (w 2) - f (w 2) * g (w 1)) • w 0 -
      (f (w 0) * g (w 2) - f (w 2) * g (w 0)) • w 1 +
    (f (w 0) * g (w 1) - f (w 1) * g (w 0)) • w 2

/-- **A third functional applied to the minor vector is the collinearity determinant.** -/
public theorem apply_minorCombination (f : Fin 3 → Module.Dual k V) (w : Fin 3 → V) :
    f 2 (minorCombination k V (f 0) (f 1) w) = (Matrix.of fun i j => f i (w j)).det := by
  rw [Matrix.det_fin_three, minorCombination]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, Matrix.of_apply]
  ring

/-! ### The core -/

/-- Swapping the two functionals negates the minor vector. -/
private theorem minorCombination_swap (f g : Module.Dual k V) (w : Fin 3 → V) :
    minorCombination k V g f w = -minorCombination k V f g w := by
  simp only [minorCombination]
  module

/-- A vector killed by both functionals lies in any submodule containing all the minor vectors,
if `g ≠ 0` and some vector is killed by `g` but not by `f`. -/
private theorem mem_of_forall_minorCombination_mem {f g : Module.Dual k V} (hg : g ≠ 0)
    (hle : ¬ LinearMap.ker g ≤ LinearMap.ker f) {N : Submodule k V}
    (hN : ∀ w : Fin 3 → V, minorCombination k V f g w ∈ N) {v : V} (hv0 : f v = 0) (hv1 : g v = 0) :
    v ∈ N := by
  obtain ⟨a, ha, ha'⟩ := Set.not_subset.mp hle
  rw [SetLike.mem_coe, LinearMap.mem_ker] at ha ha'
  obtain ⟨b, hb⟩ : ∃ b, g b ≠ 0 := by
    contrapose! hg
    exact LinearMap.ext hg
  have hmem := hN ![a, b, v]
  simp only [minorCombination, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, ha, hv0, hv1] at hmem
  have hcoe : (f a * g b) • v ∈ N := by
    convert hmem using 1
    module
  have hsm := N.smul_mem (f a * g b)⁻¹ hcoe
  rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero ha' hb), one_smul] at hsm

/-- **The common kernel of two functionals with different kernels lies in any submodule
containing all their minor vectors.** -/
public theorem le_of_forall_minorCombination_mem {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : LinearMap.ker f ≠ LinearMap.ker g) {N : Submodule k V}
    (hN : ∀ w : Fin 3 → V, minorCombination k V f g w ∈ N) :
    LinearMap.ker f ⊓ LinearMap.ker g ≤ N := by
  intro v hv
  obtain ⟨hv0, hv1⟩ := Submodule.mem_inf.mp hv
  rw [LinearMap.mem_ker] at hv0 hv1
  by_cases hle : LinearMap.ker f ≤ LinearMap.ker g
  · exact mem_of_forall_minorCombination_mem k V hg (fun h => hne (le_antisymm hle h)) hN hv0 hv1
  · refine mem_of_forall_minorCombination_mem k V hf hle (fun w => ?_) hv1 hv0
    rw [minorCombination_swap]
    exact N.neg_mem (hN w)

/-! ### The line through two points given by their degree-one equations -/

/-- **Two points whose degree-one equations are the kernels of two functionals with different
kernels are distinct**, since the equations of a point determine it when they are a hyperplane. -/
public theorem ne_of_pointSubmodule_eq_ker {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    {p₀ p₁ : projectiveSpaceOfModule k V} (hp₀ : pointSubmodule k V p₀ = LinearMap.ker f)
    (hp₁ : pointSubmodule k V p₁ = LinearMap.ker g)
    (hne : LinearMap.ker f ≠ LinearMap.ker g) : p₀ ≠ p₁ := by
  rintro rfl
  exact hne (hp₀.symm.trans hp₁)

/-- **The line through two points whose degree-one equations are the kernels of two functionals
with different kernels has corank two.** -/
public theorem finrank_quotient_lineSubmodule_of_pointSubmodule_eq_ker {f g : Module.Dual k V}
    (hf : f ≠ 0) (hg : g ≠ 0) {p₀ p₁ : projectiveSpaceOfModule k V}
    (hp₀ : pointSubmodule k V p₀ = LinearMap.ker f)
    (hp₁ : pointSubmodule k V p₁ = LinearMap.ker g)
    (hne : LinearMap.ker f ≠ LinearMap.ker g) :
    Module.finrank k (V ⧸ lineSubmodule k V p₀ p₁) = 2 := by
  rw [lineSubmodule, hp₀, hp₁]
  exact finrank_quotient_inf_ker_eq_two k V hf hg hne

/-- **That line has dimension one.** -/
public theorem topologicalKrullDim_linearSubspace_lineSubmodule_of_pointSubmodule_eq_ker
    {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    {p₀ p₁ : projectiveSpaceOfModule k V} (hp₀ : pointSubmodule k V p₀ = LinearMap.ker f)
    (hp₁ : pointSubmodule k V p₁ = LinearMap.ker g)
    (hne : LinearMap.ker f ≠ LinearMap.ker g) :
    topologicalKrullDim (linearSubspace k V (lineSubmodule k V p₀ p₁)) = 1 :=
  topologicalKrullDim_linearSubspace_eq_one k V _
    (finrank_quotient_lineSubmodule_of_pointSubmodule_eq_ker k V hf hg hp₀ hp₁ hne)

/-- **An arbitrary third point satisfying the collinearity equations lies on the line joining two
points given by their degree-one equations.** This is the form the fibre of the incidence variety
consumes: the two points of the pair are rational over the residue field and so have hyperplanes
by `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_dual_pointSubmodule_eq_ker`, while the third
ranges over the fibre and need not be rational at all. -/
public theorem mem_linearSubspace_lineSubmodule_of_pointSubmodule_eq_ker {f g : Module.Dual k V}
    (hf : f ≠ 0) (hg : g ≠ 0) {p₀ p₁ q : projectiveSpaceOfModule k V}
    (hp₀ : pointSubmodule k V p₀ = LinearMap.ker f)
    (hp₁ : pointSubmodule k V p₁ = LinearMap.ker g)
    (hne : LinearMap.ker f ≠ LinearMap.ker g)
    (hq : ∀ w : Fin 3 → V, minorCombination k V f g w ∈ pointSubmodule k V q) :
    q ∈ linearSubspace k V (lineSubmodule k V p₀ p₁) := by
  rw [mem_linearSubspace_iff, lineSubmodule, hp₀, hp₁]
  exact le_of_forall_minorCombination_mem k V hf hg hne hq

/-! ### Distinct points and the line through them -/

/-- **Distinct points cut out by functionals have different kernels.** -/
public theorem ker_ne_ker_of_linearFunctionalPoint_ne {f g : Module.Dual k V} (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hne : linearFunctionalPoint k V f hf ≠ linearFunctionalPoint k V g hg) :
    LinearMap.ker f ≠ LinearMap.ker g := by
  intro hker
  refine hne (Set.singleton_injective ?_)
  rw [← linearSubspace_ker k V f hf, ← linearSubspace_ker k V g hg, hker]

/-- **The line through two distinct points cut out by functionals has corank two**, over an
arbitrary field: the degree-one forms vanishing at both of them are the common kernel of the two
functionals. -/
public theorem finrank_quotient_lineSubmodule_linearFunctionalPoint {f g : Module.Dual k V}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : linearFunctionalPoint k V f hf ≠ linearFunctionalPoint k V g hg) :
    Module.finrank k
        (V ⧸ lineSubmodule k V (linearFunctionalPoint k V f hf)
          (linearFunctionalPoint k V g hg)) = 2 :=
  finrank_quotient_lineSubmodule_of_pointSubmodule_eq_ker k V hf hg
    (pointSubmodule_linearFunctionalPoint k V f hf) (pointSubmodule_linearFunctionalPoint k V g hg)
    (ker_ne_ker_of_linearFunctionalPoint_ne k V hf hg hne)

/-- **The line through two distinct points cut out by functionals has dimension one**, over an
arbitrary field. -/
public theorem topologicalKrullDim_linearSubspace_lineSubmodule_linearFunctionalPoint
    {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : linearFunctionalPoint k V f hf ≠ linearFunctionalPoint k V g hg) :
    topologicalKrullDim
        (linearSubspace k V (lineSubmodule k V (linearFunctionalPoint k V f hf)
          (linearFunctionalPoint k V g hg))) = 1 :=
  topologicalKrullDim_linearSubspace_eq_one k V _
    (finrank_quotient_lineSubmodule_linearFunctionalPoint k V hf hg hne)

/-- **An arbitrary third point satisfying the collinearity equations lies on the line joining the
first two.** The third point is not assumed rational: the hypothesis is that every minor vector
is a degree-one equation of it, which is what the vanishing of the determinants becomes when the
third row is the one that varies. The line has dimension one by
`topologicalKrullDim_linearSubspace_lineSubmodule_linearFunctionalPoint`. -/
public theorem mem_linearSubspace_lineSubmodule_of_forall_mem {f g : Module.Dual k V}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : linearFunctionalPoint k V f hf ≠ linearFunctionalPoint k V g hg)
    (q : projectiveSpaceOfModule k V)
    (hq : ∀ w : Fin 3 → V, minorCombination k V f g w ∈ pointSubmodule k V q) :
    q ∈ linearSubspace k V (lineSubmodule k V (linearFunctionalPoint k V f hf)
      (linearFunctionalPoint k V g hg)) :=
  mem_linearSubspace_lineSubmodule_of_pointSubmodule_eq_ker k V hf hg
    (pointSubmodule_linearFunctionalPoint k V f hf) (pointSubmodule_linearFunctionalPoint k V g hg)
    (ker_ne_ker_of_linearFunctionalPoint_ne k V hf hg hne) hq

/-! ### The form for a third point cut out by a functional -/

/-- **The collinearity equations say that the third functional kills the common kernel of the
first two.** -/
public theorem ker_inf_ker_le_ker_of_forall_det_eq_zero {f : Fin 3 → Module.Dual k V}
    (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0) (hne : LinearMap.ker (f 0) ≠ LinearMap.ker (f 1))
    (hdet : ∀ w : Fin 3 → V, (Matrix.of fun i j => f i (w j)).det = 0) :
    LinearMap.ker (f 0) ⊓ LinearMap.ker (f 1) ≤ LinearMap.ker (f 2) :=
  le_of_forall_minorCombination_mem k V h0 h1 hne fun w =>
    LinearMap.mem_ker.mpr ((apply_minorCombination k V f w).trans (hdet w))

/-- **A third point cut out by a functional and satisfying the collinearity determinants lies on
the line joining the first two.** -/
public theorem mem_linearSubspace_lineSubmodule_of_forall_det_eq_zero
    {f : Fin 3 → Module.Dual k V} (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0) (h2 : f 2 ≠ 0)
    (hne : linearFunctionalPoint k V (f 0) h0 ≠ linearFunctionalPoint k V (f 1) h1)
    (hdet : ∀ w : Fin 3 → V, (Matrix.of fun i j => f i (w j)).det = 0) :
    linearFunctionalPoint k V (f 2) h2 ∈
      linearSubspace k V (lineSubmodule k V (linearFunctionalPoint k V (f 0) h0)
        (linearFunctionalPoint k V (f 1) h1)) :=
  mem_linearSubspace_lineSubmodule_of_forall_mem k V h0 h1 hne _ fun w => by
    rw [pointSubmodule_linearFunctionalPoint]
    exact LinearMap.mem_ker.mpr ((apply_minorCombination k V f w).trans (hdet w))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
