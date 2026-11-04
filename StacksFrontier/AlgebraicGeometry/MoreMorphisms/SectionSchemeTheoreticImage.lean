module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The scheme-theoretic image of a section

A section `σ : S ⟶ X` of a morphism `f : X ⟶ S` which happens to be a closed immersion cuts out
a closed subscheme of `X` that maps isomorphically to `S`. A closed immersion factors through its
scheme-theoretic image by an isomorphism
(`AlgebraicGeometry.Scheme.Hom.toImage`, which is an isomorphism for a closed immersion), and the
scheme-theoretic image is by definition the closed subscheme cut out by the kernel ideal sheaf
(`AlgebraicGeometry.Scheme.Hom.imageι` is an `abbrev` for
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` of the kernel), so the two spellings of the
inclusion are interchangeable with no transport.

## Main results

* `AlgebraicGeometry.isIso_subschemeι_ker_comp_of_section`

## Implementation notes

This is the base-agnostic form of a statement that the tree formerly proved three times over, once
for each base morphism it was wanted at: the structure morphism of a relative projective line
(`Stacks.Chow.isIso_sectionKer_over` and `Stacks.Chow.isIso_lineConstantSection_ker_over`) and the
projection of a product over a base (`Stacks.Hilbert.isIso_subschemeι_pointIdeal_comp`). All three
are now one application of it; the geometric content is in neither the base nor the section but
only in the factorization through the image.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The closed subscheme cut out by a section is the base.** If `σ : S ⟶ X` is a closed
immersion with `σ ≫ f = 𝟙 S`, then the closed subscheme of `X` cut out by `σ.ker` maps
isomorphically to `S` along `f`. -/
theorem isIso_subschemeι_ker_comp_of_section {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)
    [IsClosedImmersion σ] (hσ : σ ≫ f = 𝟙 S) : IsIso (σ.ker.subschemeι ≫ f) := by
  have h : IsIso σ.toImage := inferInstance
  have hfac : σ.toImage ≫ (σ.imageι ≫ f) = 𝟙 S := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hσ]
  have : IsIso (σ.toImage ≫ (σ.imageι ≫ f)) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left σ.toImage _

end AlgebraicGeometry

end
