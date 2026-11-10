module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationSquareCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality

/-!
# The application morphism of Stacks 08J8 against a cochain-level transpose

Let `(C, O)` be a ringed site, let `B`, `C` be complexes of `O`-modules with `B` **K-flat**, and
let `f : A ⟶ SheafHom(B, C)` be a morphism of complexes out of an arbitrary complex `A`.  Write
`σ` for the comparison of Stacks 08DM, `Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)`, and

`ε = RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC`

for the application morphism of Stacks 08J8, i.e. the bijection of Stacks 08DI at the identity
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv X _ _ _ (𝟙 _)`).  The theorem below is

`Q f ▷ QB ≫ σ ▷ QB ≫ ε = (K-flat comparison of Stacks 06YU) ≫ Q(curryHomEquiv f)`,

with `curryHomEquiv` the cochain-level currying bijection of Stacks 0A90.  At `A = SheafHom(B, C)`
and `f = 𝟙` this is **the evaluation square of Tag 0GM7**: the application morphism of Stacks 08J8
is, after the K-flat comparison and the comparison `σ`, the cochain-level evaluation morphism
`AlgebraicGeometry.RingedSite.cochainEvaluation` of Stacks 0A90.

## Main results

* `AlgebraicGeometry.RingedSite.derivedApplication_curryingSquare`: the displayed identity, for an
  arbitrary source `A` and an arbitrary `f`, with `σ` carried as a variable.
* `AlgebraicGeometry.RingedSite.derivedApplication_curryingSquare_kInjective`: the same with `σ`
  written out, at a K-injective target, where it is the inverse of the K-injective model
  comparison.
* `AlgebraicGeometry.RingedSite.derivedApplication_eq_cochainEvaluation`: **the evaluation square
  of Tag 0GM7.**  For `B` K-flat and `C` K-injective the application morphism of Stacks 08J8 is
  the cochain-level evaluation morphism of Stacks 0A90, conjugated by the two comparisons.

## Implementation notes

* In `derivedApplication_curryingSquare` the comparison `σ` is a variable and the Stacks 08JA
  identification is a hypothesis. Writing
  `strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C` into a statement that
  also mentions `derivedCurryHomEquiv` exhausts `maxRecDepth` at the declaration's type. This
  happens
  on the conclusion of `derivedApplication_curryingSquare` with `σ` written out: the error lands
  on the declaration's name, so no restructuring of the proof can help. A consumer instantiates
  `σ` inside a proof, where it is left to unification and costs nothing. The hypothesis is
  discharged by
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`
  at the K-flat resolution `kFlatHomResolution` of `SheafHom(B, C)`.
* The three steps of `derivedApplication_curryingSquare` are composed by `rw [← ht, ← hn, h]`,
  not by `Eq.trans`: `hn.symm.trans h`, and a generic pasting lemma applied to `ht`,
  `hn` and `h`, both exhaust `maxRecDepth`; `rw [← h, hn, ht]`, the same three steps in the
  opposite order, fails with a deterministic `isDefEq` timeout on the last rewrite. The three
  hypotheses are compatible under the keyed matching of `rw` but not under the unifier.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
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

/-- **The application morphism of Stacks 08J8 against a cochain-level transpose.**  For complexes
`A`, `B`, `C` of `O`-modules with `B` K-flat, a morphism of complexes `f : A ⟶ SheafHom(B, C)`,
and the comparison `σ` of Stacks 08DM identified by `hσ`,

`Q f ▷ QB ≫ σ ▷ QB ≫ ε = (K-flat comparison of Stacks 06YU) ≫ Q(curryHomEquiv f)`,

where `ε` is the application morphism `RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC` of Stacks 08J8.

At `A = SheafHom(B, C)` and `f = 𝟙` this is the **evaluation square of Tag 0GM7**, since
`AlgebraicGeometry.RingedSite.cochainEvaluation` is by definition
`curryHomEquiv X (sheafHomComplex X B C).obj B C (𝟙 _)`.

The hypothesis `hσ` is discharged, with no condition on `B` or `C` beyond the K-flatness of `B`, by
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`
at `σ := strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C`; it is a hypothesis
rather than an instantiation for the elaboration reason in the implementation notes. -/
theorem derivedApplication_curryingSquare
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (hσ : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj (kFlatHomResolution X B C))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B C
          (kFlatHomResolution X B C) hB (isKFlat_kFlatHomResolution X B C)
          (kFlatHomResolutionMap X B C)) =
      DerivedCategory.Q.map (kFlatHomResolutionMap X B C) ≫ σ)
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map σ).app
          (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) := by
  have h := curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass_source X
    A B C (kFlatHomResolution X B C) hB
    (isKFlat_kFlatHomResolution X B C) (kFlatHomResolutionMap X B C) inferInstance σ hσ f
  have hn := derivedCurryHomEquiv_naturality_source X (DerivedCategory.Q.map f) σ
  have ht := derivedCurryHomEquiv_eq_tensor_evaluation X
    (DerivedCategory.Q.obj (sheafHomComplex X B C).obj) (DerivedCategory.Q.obj B)
    (DerivedCategory.Q.obj C) σ
  rw [← ht, ← hn, h]

/-- **The currying square with the comparison of Stacks 08DM written out**, available at a
K-injective target, where that comparison is the inverse of the K-injective model comparison
(`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_eq_homComparison_inv`).  This is
`derivedApplication_curryingSquare` with `σ` instantiated; the instantiation is made inside a
proof because the type of the general statement cannot carry it (see the implementation notes). -/
theorem derivedApplication_curryingSquare_kInjective
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [C.IsKInjective]
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (derivedSheafHomComparison X B C).inv).app (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) :=
  derivedApplication_curryingSquare X A B C hB (derivedSheafHomComparison X B C).inv
    ((derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass X
        (derivedInternalHomOfBifunctor X) B C (kFlatHomResolution X B C) hB
        (isKFlat_kFlatHomResolution X B C) (kFlatHomResolutionMap X B C)).trans
      (congrArg (fun t ↦ DerivedCategory.Q.map (kFlatHomResolutionMap X B C) ≫ t)
        (strictlyPerfectHomComparison_eq_homComparison_inv X
          (derivedInternalHomOfBifunctor X) B C)))
    f

/-- **The evaluation square of Tag 0GM7.**  For `B` K-flat and `C` K-injective the application
morphism of Stacks 08J8,

`ε : RSheafHom(QB, QC) ⊗^L_O QB ⟶ QC`,

is the cochain-level evaluation morphism `AlgebraicGeometry.RingedSite.cochainEvaluation` of
Stacks 0A90, conjugated by the K-injective model comparison of Stacks 08DM on the internal Hom
factor and by the one-sided K-flat comparison of Stacks 06YU.

This is `derivedApplication_curryingSquare_kInjective` at `A = SheafHom(B, C)` and `f = 𝟙`, since
`cochainEvaluation X B C` is by definition `curryHomEquiv X (sheafHomComplex X B C).obj B C (𝟙 _)`.
-/
theorem derivedApplication_eq_cochainEvaluation
    (B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [C.IsKInjective] :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (derivedSheafHomComparison X B C).inv).app (DerivedCategory.Q.obj B) ≫
        derivedCurryHomEquiv X
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))
          (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) (𝟙 _) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
          (sheafHomComplex X B C).obj B hB).hom ≫
        DerivedCategory.Q.map (cochainEvaluation X B C) := by
  have h := derivedApplication_curryingSquare_kInjective X (sheafHomComplex X B C).obj B C hB
    (𝟙 (sheafHomComplex X B C).obj)
  have hce : curryHomEquiv X (sheafHomComplex X B C).obj B C (𝟙 (sheafHomComplex X B C).obj) =
      cochainEvaluation X B C := by
    rw [← curryHomEquiv_symm_cochainEvaluation X B C]
    exact (curryHomEquiv X (sheafHomComplex X B C).obj B C).apply_symm_apply _
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, hce] using h

end AlgebraicGeometry.RingedSite

end
