module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-! # The tensor–internal-Hom adjunction datum of a ringed site

`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction` is the
repository's packaging of Stacks 08J8 as an adjunction: the bijection
`(A ⟶ RSheafHom(B, M)) ≃ (A ⊗^L_O B ⟶ M)` together with its naturality in the source `A`, its
dinaturality in the internal-Hom variable `B`, and its naturality in the target `M`. The
implementation notes of `…InternalHom.ProjectionFormulaInternalHom` record it as *data*.

All three clauses are proved —
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality` and
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target` — so the datum can be
supplied rather than assumed, and this file supplies it for a ringed site.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorHomAdjunctionDatum`: the tensor–internal-Hom
  adjunction of a ringed site, at the derived tensor product
  `Stacks.SheafOfModules.derivedTensorProductFunctor` and the derived internal Hom
  `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`.

## Implementation notes

The three clauses are discharged by `apply` rather than by giving the terms: matching a
naturality lemma against a field of a structure instance whose remaining fields are still
metavariables exceeds the elaborator's recursion depth on morphism groups of this size, while
`apply`, which unifies the conclusion first, does not.

*Which derived tensor product.* This is the datum at
`Stacks.SheafOfModules.derivedTensorProductFunctor`, the ringed-*site* derived tensor product,
which is the one Stacks 08J8 is stated at. The canonical map of Stacks 0B6D in
`…InternalHom.ProjectionFormulaInternalHom` needs the datum at
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` instead, because that is where the
relative cup product of Stacks 0B6C lands; the two agree up to canonical isomorphism, and that
isomorphism is still not part of the development. So this file removes the *naturality* half of
0B6D's hypothesis and leaves the bifunctor comparison, which is the whole of what remains.

Nothing here is tagged. Stacks 08J8 is an equation tag, already registered on
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`; the functoriality in the three objects is
Stacks 08J9, registered on `AlgebraicGeometry.RingedSite.derivedCurryNatIso`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

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

/-- **The tensor–internal-Hom adjunction of a ringed site, as a datum rather than a
hypothesis.** The bijection is Stacks 08J8 and the three clauses are its naturality in the
source, its dinaturality in the internal-Hom variable, and its naturality in the target. -/
@[sga "4½ Etat_0 6.2" "more general"]
def derivedTensorHomAdjunctionDatum :
    TensorHomAdjunction (Stacks.SheafOfModules.derivedTensorProductFunctor X)
      (derivedSheafHomBifunctor X) where
  homEquiv A B M := (derivedCurryHomEquiv X A B M).toEquiv
  homEquiv_naturality_source _ _ := by apply derivedCurryHomEquiv_naturality_source
  homEquiv_naturality_middle _ _ := by apply derivedCurryHomEquiv_dinaturality
  homEquiv_naturality_target _ _ := by apply derivedCurryHomEquiv_naturality_target

end AlgebraicGeometry.RingedSite

end
