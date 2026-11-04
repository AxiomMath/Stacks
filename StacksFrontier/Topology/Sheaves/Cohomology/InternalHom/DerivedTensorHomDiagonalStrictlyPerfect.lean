module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels

/-!
# The diagonal of Stacks 0BYS at a globally strictly perfect source

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The diagonal morphism of
Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism as soon as `M` is represented by a **globally strictly perfect** complex: one
with finitely many nonzero terms, each a direct summand of a finite free `O`-module. Stacks 0ATN
part (1) assumes only that `M` is *perfect*, a local condition on the site; a globally strictly
perfect representative is strictly stronger.

The proof joins two results. The reduction
`isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange_of_isFiniteFreeSummand`
turns the invertibility of the diagonal into a single statement about complexes — that the
interchange morphism of Stacks 0BYR is a quasi-isomorphism — for a strictly perfect
representative of `M` and arbitrary models of `K` and `L`. That statement is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`. Neither
needs anything of the other two objects: `K` and `L` are arbitrary.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand`: the
  diagonal is an isomorphism when `M` has a globally strictly perfect representative.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Remark 20.49.12 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Lemma 20.49.5 (Tag 08JH)](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The diagonal of Stacks 0BYS is an isomorphism at a globally strictly perfect source.** If
the object `M` of `D(O)` is represented by a complex `N` with finitely many nonzero terms, each
a direct summand of a finite free `O`-module, then

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism for every `K` and `L`.

The models of `K` and `L` are the chosen ones — a K-flat representative of `K`, a K-injective
representative of `L`, and the functorial K-injective resolution of their total tensor complex —
because the reduction holds at any choice and nothing here depends on it. -/
theorem isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eN : DerivedCategory.Q.obj N ≅ M)
    (hNbdd : {i : ℤ | ¬ IsZero (N.X i)}.Finite)
    (hNterm : ∀ i, IsFiniteFreeSummand X (N.X i)) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  have hqI : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (tensorTotal X (kFlatModel X K) (kInjectiveModel X L)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact (isIso_derivedTensorHomDiagonal_iff_quasiIso_tensorHomInterchange_of_isFiniteFreeSummand
    X K L M (isKFlat_kFlatModel X K) (kFlatModelIso X K) (kInjectiveModelIso X L) eN
    ((kInjectiveAugmentation X).app _) hqI hNbdd hNterm).2
    (tensorHomInterchange_quasiIso_of_isFiniteFreeSummand X _ _ N hNbdd hNterm)

end AlgebraicGeometry.RingedSite

end
