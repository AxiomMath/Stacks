module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromKFlatIntoKInjective
import StacksCore.Tactic.StacksAttribute

/-! # The internal Hom complex from a K-flat complex into a K-injective complex is K-injective

Let `(C, O)` be a ringed site, let `L` be a K-flat complex of `O`-modules and let `I` be a
K-injective complex of `O`-modules. **Stacks 0A96** asserts that the internal Hom complex
`SheafHom(L, I)` of Stacks 0A8Z is again K-injective.

`StacksDraft.Ch21.Sec34.InternalHomOfKFlatIntoKInjective` proves this with the currying
isomorphism of Stacks 0A90 as an explicit hypothesis, in exactly the shape the `iso` field of
that construction provides it, and
`StacksDraft.Ch21.Sec34.CurryingIsoOfHomComplexes` constructs that isomorphism. This file
supplies the one to the other.

## Main results

* `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_of_isKFlat`: Stacks 0A96.

## Implementation notes

The hypothesis discharged is a family of isomorphisms indexed by the first complex, so the
currying isomorphism is supplied pointwise as
`fun K ↦ AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso X K L I`; neither the induced maps
of internal Hom complexes nor their naturality is used.

The two files whose hypotheses meet here spell the quantified
`CategoryTheory.HomologicalComplex.HasMapBifunctor` assumption differently — one over
`CochainComplex`, the other over `HomologicalComplex _ (ComplexShape.up ℤ)`. The two are the same
assumption, `CochainComplex` being an abbreviation, so a single binder in the
`HomologicalComplex` spelling serves both and no bridging instance is needed. Sheafification is
assumed in the strong form `CategoryTheory.HasSheafify`, as in the file proving the implication;
the construction of the isomorphism needs only `CategoryTheory.HasWeakSheafify`, which the
strong form provides.

## References

* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 0A96.** The internal Hom complex `SheafHom(L, I)` from a K-flat complex `L` of
`O`-modules into a K-injective complex `I` of `O`-modules is K-injective. -/
@[stacks 0A96]
theorem isKInjective_sheafHomComplex_of_isKFlat
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (sheafHomComplex X L I).obj.IsKInjective :=
  isKInjective_sheafHomComplex_of_curryIso X L I hL fun K ↦ sheafHomTensorCurryIso X K L I

end AlgebraicGeometry.RingedSite

end
