module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfectTensorFactor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorTotalKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels

/-!
# The diagonal of Stacks 0BYS at a globally strictly perfect tensor factor

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. If `K` is represented by a
strictly perfect complex then the diagonal morphism of Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism, for every `L` and `M`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isStrictlyPerfect_tensorFactor`:
  the diagonal of Stacks 0BYS is an isomorphism when `K` is represented by a strictly perfect
  complex.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Remark 20.49.12 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Definition 20.47.1 (Tag 08FL)](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Lemma 20.46.5 (Tag 06YQ)](https://stacks.math.columbia.edu/tag/06YQ)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **The diagonal of Stacks 0BYS is an isomorphism at a globally strictly perfect tensor
factor.** If the object `K` of `D(O)` is represented by a strictly perfect complex `E` — finitely
many nonzero terms, each a direct summand of a finite free `O`-module — then

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism for every `L` and `M`. -/
theorem isIso_derivedTensorHomDiagonal_of_isStrictlyPerfect_tensorFactor
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eE : DerivedCategory.Q.obj E ≅ K)
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  have hterm : ∀ i, IsFiniteFreeSummand X (E.X i) := fun i =>
    IsDirectSummandOfFiniteFree.isFiniteFreeSummand X (hE.termDirectSummand i)
  have hki : (tensorTotal X E (kInjectiveModel X L)).IsKInjective :=
    isKInjective_tensorTotal_of_isFiniteFreeSummand X (kInjectiveModel X L) E hE.bounded hterm
  have hq : IsIso (DerivedCategory.Q.map (𝟙 (tensorTotal X E (kInjectiveModel X L)))) :=
    Iso.isIso_hom (DerivedCategory.Q.mapIso (Iso.refl _))
  exact (isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange X K L M
    (kFlat_of_isStrictlyPerfect X E hE) eE (kInjectiveModelIso X L)
    (kInjectiveModelIso X M) (𝟙 _) hq).2
    (tensorHomInterchange_quasiIso_of_isFiniteFreeSummand_tensorFactor X
      (kInjectiveModel X L) (kInjectiveModel X M) E hE.bounded hterm)

end AlgebraicGeometry.RingedSite

end
