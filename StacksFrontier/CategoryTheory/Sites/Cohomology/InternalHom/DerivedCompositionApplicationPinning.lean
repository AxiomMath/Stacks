module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionTransposePinning
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationArbitrarySource

/-!
# The derived composition against the derived application morphism

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. Write
`G = SheafHom(K, L)` and `E' = SheafHom(K, M)` for the internal Hom complexes and `σ` for the
comparison `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`. The derived composition
morphism, conjugated by `σ` on the two tensor factors and on the target, is

`Q(doubleContraction) ▷ QG` followed by `σ_{G, E'} ▷ QG` and the application morphism
`RSheafHom(QG, QE') ⊗^L_O QG ⟶ QE'`,

with no K-flatness or K-injectivity hypothesis on `K`, `L` or `M`.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_application`: the
  derived composition, conjugated by `σ`, is the double contraction followed by the application
  morphism.

## Implementation notes

* The comparison at the pair `(G, E')` and a K-flat resolution of `G` are variables: writing
  `strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) G E'` into a statement that
  also mentions `derivedCurryHomEquiv` exhausts `maxRecDepth` at the declaration's type.
* The application morphism is written as `derivedCurryHomEquiv` at an identity, not as
  `AlgebraicGeometry.RingedSite.derivedSheafHomCounit`: the two agree by definition, but a `rfl`
  between them inside the proof reaches the maximum recursion depth.
* The proof applies the composition square by `Eq.trans` and rewrites only with the currying
  square: rewriting with both in one `rw` chain times out at `whnf`.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

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

/-- For complexes `K`, `L`, `M` of `O`-modules, with `G = SheafHom(K, L)` and
`E' = SheafHom(K, M)`, the derived composition conjugated by the comparisons `σ` is the double
contraction followed by the application morphism:

`(σ_{L,M} ⊗ σ_{K,L}) ≫ cmp_{QK,QL,QM} =
  Q(doubleContraction) ▷ QG ≫ σ_{G,E'} ▷ QG ≫ ε_{QG,QE'} ≫ σ_{K,M}`.

Here `cmp` is the derived composition, `ε` the application morphism, `v : G' ⟶ G` a K-flat
resolution, and `σ` and `σ'` comparisons at `(G, E')` and `(G', E')` characterized by `hnat` and
`hσ'`. -/
theorem strictlyPerfectHomComparison_composition_application
    (K L M G' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : G' ⟶ (sheafHomComplex X K L).obj) (hG' : Stacks.SheafOfModules.IsKFlat X.O G')
    [QuasiIso v]
    (σ : DerivedCategory.Q.obj (sheafHomComplex X (sheafHomComplex X K L).obj
          (sheafHomComplex X K M).obj).obj ⟶
      ((derivedSheafHomBifunctor X).obj
          (op (DerivedCategory.Q.obj (sheafHomComplex X K L).obj))).obj
        (DerivedCategory.Q.obj (sheafHomComplex X K M).obj))
    (σ' : DerivedCategory.Q.obj (sheafHomComplex X G' (sheafHomComplex X K M).obj).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj G'))).obj
        (DerivedCategory.Q.obj (sheafHomComplex X K M).obj))
    (hnat : σ ≫ ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
          (DerivedCategory.Q.obj (sheafHomComplex X K M).obj) =
      DerivedCategory.Q.map (homMap X v (𝟙 (sheafHomComplex X K M).obj)) ≫ σ')
    (hσ' : derivedSheafHomGlobalSectionsEquiv X
        (DerivedCategory.Q.obj (kFlatHomResolution X G' (sheafHomComplex X K M).obj))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj G'))).obj
          (DerivedCategory.Q.obj (sheafHomComplex X K M).obj))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) G'
          (sheafHomComplex X K M).obj (kFlatHomResolution X G' (sheafHomComplex X K M).obj) hG'
          (isKFlat_kFlatHomResolution X G' (sheafHomComplex X K M).obj)
          (kFlatHomResolutionMap X G' (sheafHomComplex X K M).obj)) =
      DerivedCategory.Q.map (kFlatHomResolutionMap X G' (sheafHomComplex X K M).obj) ≫ σ') :
    derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) L M)
          (strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) K L) ≫
        derivedSheafHomComposition X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (derivedInternalHomOfBifunctor X) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
              (DerivedCategory.Q.map (doubleContraction X K L M))).app
          (DerivedCategory.Q.obj (sheafHomComplex X K L).obj) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
            (DerivedCategory.Q.obj (sheafHomComplex X K L).obj) ≫
          derivedCurryHomEquiv X
              (((derivedSheafHomBifunctor X).obj
                  (op (DerivedCategory.Q.obj (sheafHomComplex X K L).obj))).obj
                (DerivedCategory.Q.obj (sheafHomComplex X K M).obj))
              (DerivedCategory.Q.obj (sheafHomComplex X K L).obj)
              (DerivedCategory.Q.obj (sheafHomComplex X K M).obj) (𝟙 _) ≫
            strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) K M := by
  have h := derivedApplication_curryingSquare_toTensor X (sheafHomComplex X L M).obj
    (sheafHomComplex X K L).obj G' (sheafHomComplex X K M).obj v hG' σ σ' hnat hσ'
    (doubleContraction X K L M)
  refine (strictlyPerfectHomComparison_composition_doubleContraction X K L M).trans ?_
  rw [← Category.assoc, ← h]
  simp only [Category.assoc]

end AlgebraicGeometry.RingedSite

end
