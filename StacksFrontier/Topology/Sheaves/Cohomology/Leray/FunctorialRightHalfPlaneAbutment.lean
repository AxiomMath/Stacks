module

public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo

/-!
# Functorial filtered abutments of right-half-plane spectral sequences

`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` is the functorial filtered abutment of
a first-quadrant spectral sequence, the shape the convergence clause of [Stacks, Tag 01F6] and
[Stacks, Tag 0734] takes for a single module.  For a *bounded below complex* the second page is
supported in the right half plane only: the first index is still non-negative, but the second
one is bounded below by a quantity that varies with the complex, so the filtration of the
abutment in total degree `n` is finite at each object without a uniform length.  This file
carries the corresponding notion.

The two differences from the first-quadrant structure are the index type of the abutment, `ℤ`
rather than `ℕ`, and the replacement of the uniform bottom step `F^{n+1}H^n = 0` by the
objectwise convergence statement `CategoryTheory.SpectralSequence.AbutsTo`, which asks for a
finite filtration without naming where it ends.

## Main definitions

* `Stacks.Cohomology.Leray.FunctorialRightHalfPlaneAbutsTo`: a functorial finite filtered
  abutment of a functorial right-half-plane `E₂` cohomological spectral sequence.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Leray

variable {D A : Type*} [Category* D] [Category* A] [Abelian A]

/-- A **functorial** finite filtered abutment of a right-half-plane `E₂` cohomological spectral
sequence: for a spectral sequence `E` and an abutment `H`, both functorial on a parameter
category `D`, a functorial finite decreasing filtration of each `H^n` which is the whole of
`H^n` in step `0`, together with objectwise convergence, an identification of the graded pieces
with the terms of the infinity page of `E`, and the compatibility of those identifications with
the maps a morphism of `D` induces on both. -/
structure FunctorialRightHalfPlaneAbutsTo
    (E : D ⥤ E₂CohomologicalSpectralSequence A) (H : ℤ → D ⥤ A) where
  /-- The functorial filtration of the abutment in each total degree. -/
  filtration (n : ℤ) : D ⥤ FilteredObject A ℤᵒᵖ
  /-- The underlying object of the filtration is naturally the asserted abutment. -/
  abutmentIso (n : ℤ) : filtration n ⋙ FilteredObject.forget ≅ H n
  /-- The filtration of every abutment object is finite. -/
  isFinite (K : D) (n : ℤ) : Filtration.IsFinite ((filtration n).obj K).filtration
  /-- In total degree `n`, the zeroth filtration step is the whole abutment. -/
  isTop (K : D) (n : ℤ) :
    ((filtration n).obj K).filtration.subobject (op (0 : ℤ)) = ⊤
  /-- At each object of the parameter category the spectral sequence converges in the standard
  finite-filtration sense. -/
  abutsTo (K : D) : SpectralSequence.AbutsTo (E.obj K) (fun n => (H n).obj K)
  /-- The infinity term is the corresponding associated graded object. -/
  gradedIso (K : D) (p q : ℤ) :
    (E.obj K).pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj ((filtration (p + q)).obj K)
  /-- The graded identifications are compatible with the maps a morphism of `D` induces on the
  infinity page and on the graded pieces. -/
  gradedIso_naturality {K L : D} (φ : K ⟶ L) (p q : ℤ) :
    SpectralSequence.Hom.mapPageInfinity (E.map φ) (p, q) ≫
        (gradedIso L p q).hom =
      (gradedIso K p q).hom ≫
        (FilteredObject.gr p).map ((filtration (p + q)).map φ)

end Stacks.Cohomology.Leray

end
