module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective space has no global differential forms in positive degree

For a commutative ring `A` and `n ≥ 1`, `Γ(ℙⁿ_A, Ω^s_{ℙⁿ_A/A}) = 0` for every `s ≥ 1`. This is the
degree-zero case of clause (1) of [Stacks, Tag 0FUK], which the development proves on the source's
model `Proj A[T₀, …, Tₙ]` (`StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology`),
read on global sections and transported to the library's model `projectiveSpaceOverRing n A`, the
base change of the integral model of projective space. It is the vanishing
`pr_{1,*}pr_2^*Ω^s_{𝐏^{n-1}_S/S} = 0` for `s > 0` that the source's proof of clause (2) of
[Stacks, Tag 0FUR] quotes from Section 50.10 (Tag 0FMG) and the proof of Tag 0FMI.

## Main results

* `ProjectiveSpaceHodge.subsingleton_sections_forms`: on the source's model.
* `ProjectiveSpaceHodge.subsingleton_sections_forms_projectiveSpaceOverRing`: on the library's
  model.

## Implementation notes

The source's model is `ℙ^{k+1}_A`, with `k + 1 ≥ 1`, because that is how
`Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projSpace` is indexed. `ℙ⁰` is not needed: in the
application `n = 1` is handled separately, the bundle then being the centre itself.

## References

* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHodge

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {k : ℕ}

/-- **`H⁰(ℙ^{k+1}_A, Ω^s) = 0` for `s ≥ 1`**, read on global sections: the degree-zero case of
clause (1) of [Stacks, Tag 0FUK] (`isZero_hodgeCohomology`), with the zeroth right derived functor
of the sections functor identified with the sections functor, which is left exact. -/
@[sga "7 XI 1.1" "(ii), special case"]
theorem subsingleton_sections_forms (s : ℕ) (hs : s ≠ 0) :
    Subsingleton Γ(forms A k s, ⊤) := by
  have h := isZero_hodgeCohomology (A := A) (m := k) s 0 (fun h => hs h.1)
  have h1 : IsZero (cohomologySheaf A k (forms A k s) 0) :=
    (isZero_restrictScalars_iff _ _).mp h
  have h' := h1.of_iso ((globalSections A k).rightDerivedZeroIsoSelf.app (forms A k s)).symm
  exact (ModuleCat.isZero_iff_subsingleton.mp h')

/-- The identification of the two models of projective space over `Spec A` carries the
structure morphism of the library's model to
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, the structure morphism the Hodge
cohomology computation of [Stacks, Tag 0FUK] is stated for. -/
theorem projModelIso_hom_comp_structureMorphism (A : Type u) [CommRing A] (N : ℕ) :
    (Stacks.ProjectiveCohomology.projModelIso A N).hom ≫
        (projectiveSpaceOverRing N (CommRingCat.of A) ↘ Spec (CommRingCat.of A)) =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff A N := by
  refine (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism A N).trans ?_
  exact (congrArg (fun φ => AlgebraicGeometry.Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) ≫ Spec.map φ)
    (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.polyDegreeZeroHom_eq A N)).symm

/-- **`Γ(ℙ^{k+1}_A, Ω^s) = 0` for `s ≥ 1`, on the library's model of projective space**
`projectiveSpaceOverRing (k + 1) A`, the base change of the integral model. It is
`subsingleton_sections_forms` on the source's model `Proj A[T₀, …, T_{k+1}]`, transported along
the identification `Stacks.ProjectiveCohomology.projModelIso` of the two models over `Spec A`. -/
@[sga "7 XI 1.1" "special case"]
theorem subsingleton_sections_forms_projectiveSpaceOverRing (A : Type u) [CommRing A] (k : ℕ)
    (s : ℕ) (hs : s ≠ 0) :
    Subsingleton Γ(Scheme.Hom.relativeDifferentialForms
      (projectiveSpaceOverRing (k + 1) (CommRingCat.of A) ↘ Spec (CommRingCat.of A)) s, ⊤) :=
  Scheme.Hom.subsingleton_sections_relativeDifferentialForms_of_iso
    (Stacks.ProjectiveCohomology.projModelIso A (k + 1)).symm
    (by rw [Iso.symm_hom, Iso.inv_comp_eq, projModelIso_hom_comp_structureMorphism]) s
    (subsingleton_sections_forms (A := A) (k := k) s hs)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHodge
