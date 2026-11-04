module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ChartLinear
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Diagonal
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.LineDeterminant

/-!
# Three collinear points give a point of the collinearity locus

`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine` reads the collinearity
equations forwards: a point of the collinearity locus has its third point on the line joining the
first two. This file is the converse, which is what the *set-theoretic* half of Tag 0B1R needs:
a triple of points whose first two have distinct hyperplanes of degree-one equations and whose
third point lies on the line joining them is a point of the collinearity locus.

The two directions are proved differently. Forwards, the determinant is evaluated at one chosen
triple of vectors and the chart coordinate enters only through the vanishing of its values.
Backwards, *every* determinant has to vanish, so the chart coordinates have to be known linear:
the three of them kill the common kernel of the first two functionals, which has corank two, so
they span a space of rank two and every `3 × 3` determinant they form is zero. That linearity is
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.ChartLinear` and the determinant count is
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.LineDeterminant`. The three projections
of the triple product are morphisms over `Spec k`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.pr₁_comp_toSpec` and its two companions), which is
what makes the three chart coordinates at a point semilinear over *one* ring homomorphism.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_of_pointSubmodule_inf_le`:
  **a triple whose third point satisfies the degree-one equations of the first two is
  collinear.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_of_isClosed`: the same for a
  triple of closed points over an algebraically closed field, where the two hyperplanes are
  produced from the points.

## Implementation notes

The chart is chosen exactly as in the forward direction: one vector outside the degree-one
equations of each of the three points, which exists by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_ι_notMem`. On that chart the determinant
section becomes the determinant of the matrix of residues of the chart coordinates
(`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_detSection_iff_mem_basicOpen`),
and a vanishing residue of a function says that the function is not a unit at the point, so the
point is outside the basic open and the determinant section vanishes there. Since the triple of
vectors is arbitrary, every determinant section vanishes and the point is collinear.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The converse of the collinearity dictionary -/

/-- **A triple of points of `𝐏(V)` whose third point satisfies every degree-one equation of the
first two is a point of the collinearity locus**, as soon as the first two have distinct
hyperplanes of degree-one equations.

This is the converse of
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointSubmodule_inf_le_pointSubmodule_of_collinear`,
and it is what exhibits a collinear triple of rational points as a point of the incidence
variety. -/
public theorem mem_collinearLocus_of_pointSubmodule_inf_le {t : prodThree k V}
    {f g : Module.Dual k V} (hf : f ≠ 0) (hg : g ≠ 0)
    (hft : pointSubmodule k V ((pr₁ k V).base t) = LinearMap.ker f)
    (hgt : pointSubmodule k V ((pr₂ k V).base t) = LinearMap.ker g)
    (hne : LinearMap.ker f ≠ LinearMap.ker g)
    (hle : pointSubmodule k V ((pr₁ k V).base t) ⊓ pointSubmodule k V ((pr₂ k V).base t) ≤
      pointSubmodule k V ((pr₃ k V).base t)) :
    t ∈ collinearLocus k V := by
  obtain ⟨u, hx⟩ := exists_mem_chartOpen k V t
  have h₁ := chartOpen_le_pr₁ k V u
  have h₂ := chartOpen_le_pr₂ k V u
  have h₃ := chartOpen_le_pr₃ k V u
  refine (mem_collinearLocus_iff_forall_not_isUnit_germ_det k V u h₁ h₂ h₃ hx).mpr fun w => ?_
  -- the three chart functionals at `t`
  set φ : Fin 3 → V → IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk t) :=
    ![fun v => chartResidue k V hx (chartRatio k V (pr₁ k V) (u 0) v h₁),
      fun v => chartResidue k V hx (chartRatio k V (pr₂ k V) (u 1) v h₂),
      fun v => chartResidue k V hx (chartRatio k V (pr₃ k V) (u 2) v h₃)]
  have hadd : ∀ (i : Fin 3) (v v' : V), φ i (v + v') = φ i v + φ i v' := by
    intro i v v'
    fin_cases i
    · exact chartResidue_chartRatio_add k V (pr₁ k V) (u 0) v v' h₁ hx
    · exact chartResidue_chartRatio_add k V (pr₂ k V) (u 1) v v' h₂ hx
    · exact chartResidue_chartRatio_add k V (pr₃ k V) (u 2) v v' h₃ hx
  have hsmul : ∀ (i : Fin 3) (c : k) (v : V),
      φ i (c • v) = residueScalarHom k V hx c * φ i v := by
    intro i c v
    fin_cases i
    · exact chartResidue_chartRatio_smul k V (pr₁ k V) (pr₁_comp_toSpec k V) c (u 0) v h₁ hx
    · exact chartResidue_chartRatio_smul k V (pr₂ k V) (pr₂_comp_toSpec k V) c (u 1) v h₂ hx
    · exact chartResidue_chartRatio_smul k V (pr₃ k V) (pr₃_comp_toSpec k V) c (u 2) v h₃ hx
  have hker : ∀ i : Fin 3, ∀ v ∈ LinearMap.ker f ⊓ LinearMap.ker g, φ i v = 0 := by
    intro i v hv
    rw [← hft, ← hgt] at hv
    fin_cases i
    · exact (chartResidue_chartRatio_eq_zero_iff k V (pr₁ k V) (u 0) v h₁ hx).mpr hv.1
    · exact (chartResidue_chartRatio_eq_zero_iff k V (pr₂ k V) (u 1) v h₂ hx).mpr hv.2
    · exact (chartResidue_chartRatio_eq_zero_iff k V (pr₃ k V) (u 2) v h₃ hx).mpr (hle hv)
  -- the matrix of residues of the chart coordinates is the matrix of the three functionals
  have hentry : ((chartMatrix k V u w h₁ h₂ h₃).map (chartResidue k V hx)) =
      Matrix.of fun i j => φ i (w j) := by
    ext i j
    fin_cases i <;> rfl
  -- a function whose residue vanishes is not a unit at the point
  have hres : chartResidue k V hx ((chartMatrix k V u w h₁ h₂ h₃).det) = 0 :=
    (RingHom.map_det _ _).trans <| (congrArg Matrix.det hentry).trans <|
      det_eq_zero_of_forall_mem_ker_inf_ker k V (residueScalarHom k V hx) φ hadd hsmul
        hf hg hne hker w
  rwa [chartResidue, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres

/-- **A triple of closed points of `𝐏(V)` whose third point satisfies every degree-one equation
of the first two is collinear**, over an algebraically closed field. The two hyperplanes are the
ones cutting out the first two points, and they are distinct because the points are. -/
public theorem mem_collinearLocus_of_isClosed [IsAlgClosed k] [Module.Finite k V]
    {t : prodThree k V}
    (h₁ : IsClosed ({(pr₁ k V).base t} : Set (projectiveSpaceOfModule k V)))
    (h₂ : IsClosed ({(pr₂ k V).base t} : Set (projectiveSpaceOfModule k V)))
    (hne : (pr₁ k V).base t ≠ (pr₂ k V).base t)
    (hle : pointSubmodule k V ((pr₁ k V).base t) ⊓ pointSubmodule k V ((pr₂ k V).base t) ≤
      pointSubmodule k V ((pr₃ k V).base t)) :
    t ∈ collinearLocus k V := by
  have key : ∀ p : projectiveSpaceOfModule k V, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
      ∃ f : Module.Dual k V, f ≠ 0 ∧ pointSubmodule k V p = LinearMap.ker f := fun p hp => by
    obtain ⟨f, hf, rfl⟩ := exists_eq_linearFunctionalPoint k V p hp
    exact ⟨f, hf, pointSubmodule_linearFunctionalPoint k V f hf⟩
  obtain ⟨f, hf, hft⟩ := key _ h₁
  obtain ⟨g, hg, hgt⟩ := key _ h₂
  exact mem_collinearLocus_of_pointSubmodule_inf_le k V hf hg hft hgt
    (fun h => hne (eq_of_pointSubmodule_eq k V h₁ h₂ (hft.trans (h.trans hgt.symm)))) hle

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
