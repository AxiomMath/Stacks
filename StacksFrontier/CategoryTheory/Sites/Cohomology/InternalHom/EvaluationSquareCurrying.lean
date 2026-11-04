module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationSquareComparisonClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsAgreement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalHomsFromCocycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryHomEquivTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct

/-! # Degree-zero global hypercohomology of the currying isomorphism of Stacks 08DJ

Let `(C, O)` be a ringed site, let `B`, `C` be complexes of `O`-modules with `B` K-flat, let `P`
be a K-flat complex and let `p : P ⟶ SheafHom(B, C)` be a morphism of complexes.  The evaluation
square of Tag 0GM7 is reduced in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StrictlyPerfectHomComparisonEvaluation`
to the single assertion that the bijection of Stacks 08DI carries `Q p ≫ σ` to the one-sided
K-flat comparison of Stacks 06YU followed by the class of the cochain-level transpose of `p`,
where `σ` is the comparison of Stacks 08DM; and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationSquareComparisonClass`
rewrites the left-hand side of that assertion, with the bijection of Stacks 08DI eliminated, as
Stacks 08JA of the value of degree-zero global hypercohomology of the currying isomorphism of
Stacks 08DJ on one explicit class.

**This file computes that value.**  The remaining content of the square was exactly that
computation, and nothing else.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryIso_naturality_target`: the derived currying
  isomorphism of Stacks 08DJ is natural in its target, at the ringed-site spelling.  This is
  `AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the source and of the
  middle object.
* `derivedCurryGlobalEquiv_derivedGlobalSectionsClassOfHomComp_kInjectiveResolution` and
  `AlgebraicGeometry.RingedSite.derivedCurryGlobalEquiv_precomposedHomComparisonClass`:
  **the value of degree-zero global hypercohomology of the currying isomorphism of Stacks 08DJ on
  `AlgebraicGeometry.RingedSite.precomposedHomComparisonClass`.**  It is the Stacks 08JA preimage
  of the K-flat comparison of Stacks 06YU followed by the class of the transpose of `p`.  The
  second statement is the first with the class written in the form
  `EvaluationSquareComparisonClass` supplies it.
* `curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass`:
  **the currying square of Tag 0GM7 at the K-flat source `P`** — that is, the hypothesis
  `hcurry` of
  `AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare` — granted only that Stacks
  08JA carries `precomposedHomComparisonClass` to `Q p ≫ σ`, which is
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`.
* `curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass_source`:
  **the currying square at an arbitrary source.**  Its proof forms the evaluation square of
  Tag 0GM7 itself, as the input to
  `AlgebraicGeometry.RingedSite.curryingSquare_of_evaluationSquare`; so the square is proved
  inside this statement rather than merely implied by it.

## Nothing here is tagged

Stacks 08DJ is carried by `Stacks.SheafOfModules.derivedCurryingData`, Stacks 08J9 by
`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`, Stacks 08JA by
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, Stacks 08J8 by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and Stacks 0A90 by
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`.  Everything below is a step of the *proof*
of Tag 0GM7 — one leg of its evaluation square, and the computation that closes it — and no
declaration here carries a tag.

## The proof

The class is a push of the class of a morphism of complexes `P ⟶ SheafHom(B, R C)` along two
isomorphisms of `D(O)`, where `R C` is the chosen K-injective resolution of `C`.  Composing the
goal with the image of the augmentation `𝜀 : C ⟶ R C`, which is invertible in `D(O)`, moves the
whole statement to a K-injective target; the naturality of the currying isomorphism in its target
carries the currying isomorphism across that move, and the second of the two isomorphisms cancels
against it, leaving the K-injective model comparison of Stacks 08DM alone.

At a K-injective target the currying isomorphism *is* the currying isomorphism of complexes of
Stacks 0A90 conjugated by the model comparisons
(`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`), so the composite becomes the push of
the class of `P ⟶ SheafHom(B, R C)` along `Q` of a morphism of internal Hom complexes, conjugated
by two model comparisons.  That push is computed on the *cochain* side: the identification of the
degree-zero global hypercohomology of `RSheafHom(QA, QI)` with the degree-zero cohomology of the
global sections of `SheafHom(A, I)` is natural for morphisms of complexes — which is
`globalSectionsKInjectiveIso_naturality_complexMap` and the naturality of
`DerivedCategory.homologyFunctorFactors` — and on cocycles the currying isomorphism of Stacks 0A90
is the currying bijection of morphism groups, which is
`AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv`.  Finally the target is
released from `R C` back to `C` by the target naturality of the cochain-level currying bijection,
`AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_target`.

## Implementation notes

*`σ` is a variable and the identification of Stacks 08JA is a hypothesis.*  Writing
`strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C` into a statement that also
mentions `derivedCurryHomEquiv` **exhausts `maxRecDepth` at the declaration's type** (here
as well as in `EvaluationSquareComparisonClass`: the error is reported at the declaration's name
column, so no restructuring of a proof can help).  The statements below therefore carry `σ` as a
variable with the Stacks 08JA identification as a hypothesis, and a consumer instantiates it; at
the *term* level the instantiation costs nothing, provided `σ` is left to unification rather than
written out.

*The conclusion of the evaluation square is not a statable declaration in this cone.*  The
conclusion of `AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare` together with the
hypothesis mentioning `precomposedHomComparisonClass` exhausts `maxRecDepth` at the declaration's
type, in every arrangement tried — while the conclusion together with an *abstract* class and its
Stacks 08JA identification elaborates, which locates the cost precisely at that pairing.  The
square is therefore recorded by proving the currying square at an arbitrary source, whose proof
forms the evaluation square as a subterm.

*Rewriting is avoided wherever the two sides spell one object through a representative functor
and once directly.*  `rw [Category.assoc]` is rejected — "did not find an occurrence" of a
pattern the goal prints verbatim — on goals whose last factor is
`HomologicalComplex.homologyMap f 0` while the factor before it lands in
`(HomologicalComplex.homologyFunctor _ _ 0).obj`, the two being definitionally but not
syntactically equal; the statements below are written in the functor spelling throughout and the
single crossing to `homologyMap` is made by `exact`.  Likewise
`AlgebraicGeometry.RingedSite.iteratedHomRepresentativeIso` and
`AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` are objects of the representative
trifunctors, so the cancellations around them are done with `Iso.inv_comp_eq` and
`Iso.eq_comp_inv` *as terms* rather than by `rw`.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The naturality of global sections on K-injective complexes, after homology -/

/-- **Global sections computing derived global sections on a K-injective complex is natural,
after degree-zero homology.**  For K-injective complexes `W`, `W'` and a morphism of complexes
`φ : W ⟶ W'`, the identification of the degree-zero homology of `RΓ(C, Q W)` with the degree-zero
cohomology of the complex of global sections of `W` carries the map induced by `Q φ` to the map
induced by the global sections of `φ`.

Both factors of that identification are natural: the comparison of Stacks 07A5 by
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality_complexMap`, and the
factorization of the homology functor through the localization by its being an isomorphism of
functors. -/
private lemma factors_gsKI_naturality
    {W W' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [W.IsKInjective] [W'.IsKInjective] (φ : W ⟶ W') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            (globalSectionsKInjectiveIso X W').inv ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
            (globalSectionsComplex X W') =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            (globalSectionsKInjectiveIso X W).inv ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
            (globalSectionsComplex X W) ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
          (globalSectionsComplexMap X φ) := by
  have h1 : (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) ≫
        (globalSectionsKInjectiveIso X W').inv =
      (globalSectionsKInjectiveIso X W).inv ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X φ) := by
    rw [Iso.comp_inv_eq, Category.assoc, globalSectionsKInjectiveIso_naturality_complexMap,
      Iso.inv_hom_id_assoc]
  have h2 := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
    (globalSectionsComplexMap X φ)
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
  exact congrArg _ h2

/-- Degree-zero homology of derived global sections of a composite is the composite of the
induced maps, applied to an element. -/
private lemma homology_globalSections_map_comp_apply
    {M N M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : M ⟶ N) (b : N ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj M) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (a ≫ b)) z =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map b)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map a) z) := by
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-! ### The transport of the class of a morphism of complexes along the model comparisons -/

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsModelEquiv` written out as a
composite of three maps, with the two functor images separated.  This is its definition up to the
associativity of composition, and it is the form in which the naturality above applies to it. -/
private lemma modelEquiv_apply
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsModelEquiv X A I z =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              (globalSectionsKInjectiveIso X (sheafHomComplex X A I).obj).inv ≫
            (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
              (globalSectionsComplex X (sheafHomComplex X A I).obj)) z := by
  have h : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X (sheafHomComplex X A I).obj).inv) ≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
          (globalSectionsComplex X (sheafHomComplex X A I).obj) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              (globalSectionsKInjectiveIso X (sheafHomComplex X A I).obj).inv ≫
            (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
              (globalSectionsComplex X (sheafHomComplex X A I).obj) := by
    rw [Functor.map_comp_assoc]
  exact ConcreteCategory.congr_hom h z

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The three comparisons out of which Stacks 08JA is built at a K-injective internal Hom
complex are natural for a morphism of internal Hom complexes.**  Let `φ : SheafHom(A, I) ⟶
SheafHom(A', I')` be a morphism of complexes between two K-injective internal Hom complexes.  The
identification of
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsModelEquiv` carries the map that `φ`
induces on degree-zero global hypercohomology, conjugated by the two K-injective model
comparisons of the derived internal Hom, to the map that the global sections of `φ` induce on
degree-zero cohomology.

The conjugating isomorphism is the only thing the statement assumes about `φ`: it is an arbitrary
morphism of complexes, not one of the maps `AlgebraicGeometry.RingedSite.homMap` induces. -/
private lemma modelEquiv_map_comp
    {A I A' I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective]
    (φ : (sheafHomComplex X A I).obj ⟶ (sheafHomComplex X A' I').obj)
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomGlobalSectionsModelEquiv X A' I'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ ≫
              (derivedSheafHomComparison X A' I').inv)) z) =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
          (globalSectionsComplexMap X φ)
        (derivedSheafHomGlobalSectionsModelEquiv X A I z) := by
  have hθ : ((derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ ≫
        (derivedSheafHomComparison X A' I').inv) ≫
      (derivedSheafHomComparison X A' I').hom =
    (derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : (derivedModuleGlobalSections X).map
        ((derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ ≫
          (derivedSheafHomComparison X A' I').inv) ≫
      (derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom =
    (derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
      (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ hθ
  have hmor : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          ((derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ ≫
            (derivedSheafHomComparison X A' I').inv)) ≫
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              (globalSectionsKInjectiveIso X (sheafHomComplex X A' I').obj).inv ≫
            (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
              (globalSectionsComplex X (sheafHomComplex X A' I').obj)) =
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              (globalSectionsKInjectiveIso X (sheafHomComplex X A I).obj).inv ≫
            (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
              (globalSectionsComplex X (sheafHomComplex X A I).obj)) ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
        (globalSectionsComplexMap X φ) := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
    exact congrArg _ (factors_gsKI_naturality X φ)
  rw [modelEquiv_apply, modelEquiv_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom hmor z

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The class of a morphism of complexes is transported along a morphism of internal Hom
complexes.**  Let `φ : SheafHom(A, I) ⟶ SheafHom(A', I')` be a morphism of complexes between two
K-injective internal Hom complexes, and let `f : A ⟶ I` and `f₂ : A' ⟶ I'` be morphisms of
complexes whose degree-zero global cohomology classes `φ` matches.  Then the K-injective model
comparisons of the derived internal Hom carry the degree-zero global hypercohomology class of `f`
to that of `f₂`.

This is the step that brings the *cochain-level* currying of Stacks 0A90 to bear on the derived
currying isomorphism: at `φ` the currying isomorphism of complexes and `f₂` the transpose of `f`,
the hypothesis is
`AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv`. -/
private lemma classOfHom_transport
    {A I A' I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective]
    (φ : (sheafHomComplex X A I).obj ⟶ (sheafHomComplex X A' I').obj)
    (f : A ⟶ I) (f₂ : A' ⟶ I')
    (hf : HomologicalComplex.homologyMap (globalSectionsComplexMap X φ) 0
        (globalCohomologyClassOfHom X A I f) = globalCohomologyClassOfHom X A' I' f₂) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          ((derivedSheafHomComparison X A I).hom ≫ DerivedCategory.Q.map φ ≫
            (derivedSheafHomComparison X A' I').inv))
        (derivedGlobalSectionsClassOfHom X A I f) =
      derivedGlobalSectionsClassOfHom X A' I' f₂ := by
  refine (derivedSheafHomGlobalSectionsModelEquiv X A' I').injective ?_
  rw [modelEquiv_map_comp, derivedGlobalSectionsClassOfHom, derivedGlobalSectionsClassOfHom,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact hf

/-! ### The derived currying isomorphism, natural in its target -/

/-- **The derived currying isomorphism of Stacks 08DJ is natural in its target**, at the
ringed-site spelling: for objects `K`, `L` of `D(O)` and a morphism `m : M ⟶ M'`, the map induced
on the iterated derived internal Hom commutes with the currying isomorphism.

This is `AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of `K` and of `L`.
-/
theorem derivedCurryIso_naturality_target
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    ((derivedSheafHomBifunctor X).obj (op K)).map
          (((derivedSheafHomBifunctor X).obj (op L)).map m) ≫
        (derivedCurryIso X K L M').hom =
      (derivedCurryIso X K L M).hom ≫
        ((derivedSheafHomBifunctor X).obj
          (op (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))).map m := by
  simpa using derivedCurryIso_natural X (𝟙 K) (𝟙 L) m

/-- **The currying isomorphism of Stacks 08DJ at a K-flat middle complex and a K-injective
target, read against the two representative identifications.**  This is
`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison` with the two identifications moved to
the other side; the cancellations are `Iso.inv_comp_eq` and `Iso.eq_comp_inv` applied as terms,
because the two sides spell the derived objects once through the representative trifunctors of
`…InternalHom.DerivedCurryingNaturality` and once directly, and a rewrite is rejected at that
crossing. -/
private lemma curryIso_comparison_representative
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] :
    (iteratedHomRepresentativeIso X A B I hB).inv ≫
        (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj I)).hom =
      DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
        (tensorHomRepresentativeIso X A B I hB).inv :=
  (Iso.inv_comp_eq _).2 (Eq.trans ((Iso.eq_comp_inv _).2
    (derivedCurryIso_comparison X A B I hB)) (Category.assoc _ _ _))

/-- **The currying isomorphism of Stacks 08DJ, conjugated by the K-injective model comparisons.**
For complexes `A`, `B`, `I` with `B` K-flat and `I` K-injective, the map that the model comparison
`RSheafHom(QB, QI) ⟶ Q SheafHom(B, I)` inverted induces on the derived internal Hom out of `QA`,
followed by the currying isomorphism, is the model comparison at `A` and `SheafHom(B, I)`, then
the class of the currying isomorphism of complexes of Stacks 0A90, then the model comparison at
`Tot(A ⊗_O B)` and `I` inverted.

This is `curryIso_comparison_representative` with the first representative identification moved
across, and it is the form in which the comparison applies to the class of a morphism of
complexes: the class carries the *inverse* of the model comparison, so that is what the statement
is written against. -/
private lemma curryIso_comparison_conj
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective]
    [((sheafHomComplex X B I).obj).IsKInjective] :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (derivedSheafHomComparison X B I).inv ≫
        (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj I)).hom =
      (derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
          (tensorHomRepresentativeIso X A B I hB).inv :=
  (Iso.inv_comp_eq (derivedSheafHomComparison X A (sheafHomComplex X B I).obj)).1
    (Eq.trans (Category.assoc _ _ _).symm (curryIso_comparison_representative X A B I hB))

/-- The inverse of `AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` written out, so
that its second factor can be recognised as the map Stacks 08JA is natural against in its source
variable.  This is its definition. -/
private lemma tensorHomRepresentativeIso_inv_eq
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] :
    (tensorHomRepresentativeIso X A B I hB).inv =
      (derivedSheafHomComparison X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
          I).inv ≫
        ((derivedSheafHomBifunctor X).map
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B
            hB).hom.op).app (DerivedCategory.Q.obj I) :=
  rfl

/-! ### Stacks 08JA against the class of a morphism of complexes, in the source variable -/

/-- **Stacks 08JA, in its source variable, at the class of a morphism of complexes.**  For `A`
K-flat, `I` K-injective, a morphism of complexes `f : A ⟶ I` and an arbitrary morphism
`u : N ⟶ QA` of `D(O)`, Stacks 08JA carries the class of `f` pushed along the contravariant
functoriality of the derived internal Hom in `u` to `u ≫ Q f`. -/
private lemma globalSectionsEquiv_classOfHom_map_source
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective] (f : A ⟶ I)
    {N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (u : N ⟶ DerivedCategory.Q.obj A) :
    derivedSheafHomGlobalSectionsEquiv X N (DerivedCategory.Q.obj I)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map u.op).app (DerivedCategory.Q.obj I)))
          (derivedGlobalSectionsClassOfHomOfKFlat X A I hA f)) =
      u ≫ DerivedCategory.Q.map f := by
  rw [derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap,
    derivedSheafHomGlobalSectionsEquiv_apply_eq_ofKFlat X hA,
    derivedSheafHomGlobalSectionsEquivOfKFlat_derivedGlobalSectionsClassOfHomOfKFlat]

/-! ### Pushing the class of Stacks 08DM along a further morphism of `D(O)` -/

/-- **The class of a morphism of complexes followed by a morphism of `D(O)`, pushed along a
further morphism.**  Pushing
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsClassOfHomComp` along the covariant
functoriality of the derived internal Hom in `χ` is the same class at `ψ ≫ χ`.  This is the
functoriality of degree-zero global hypercohomology, and it is what lets the K-injective
augmentation of the target be cancelled from the class. -/
private lemma derivedGlobalSectionsClassOfHomComp_comp
    (A J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (f : A ⟶ J)
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : DerivedCategory.Q.obj J ⟶ M) (χ : M ⟶ M') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map χ))
        (derivedGlobalSectionsClassOfHomComp X A J hA f ψ) =
      derivedGlobalSectionsClassOfHomComp X A J hA f (ψ ≫ χ) := by
  exact (homology_globalSections_map_comp_apply X _ _ _).symm.trans
    (by rw [← Functor.map_comp]; rfl)

/-! ### The currying isomorphism on global hypercohomology, natural in its target -/

/-- **Degree-zero global hypercohomology of the currying isomorphism of Stacks 08DJ is natural
in the target, read through Stacks 08JA.**  For a morphism `m : M ⟶ M'` of `D(O)` and a class `z`
of `RSheafHom(K, RSheafHom(L, M))`, pushing `z` along the map `m` induces on the iterated derived
internal Hom and then applying the currying isomorphism and Stacks 08JA gives the value at `z`
followed by `m`.

This is `derivedCurryIso_naturality_target` together with the target naturality of Stacks 08JA,
and it is the step that moves the whole computation to a K-injective target. -/
private lemma globalSectionsEquiv_curryGlobalEquiv_naturality_target
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M))) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) M'
        (derivedCurryGlobalEquiv X K L M'
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map
              (((derivedSheafHomBifunctor X).obj (op K)).map
                (((derivedSheafHomBifunctor X).obj (op L)).map m))) z)) =
      derivedSheafHomGlobalSectionsEquiv X
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) M
          (derivedCurryGlobalEquiv X K L M z) ≫ m := by
  rw [derivedCurryGlobalEquiv_apply, derivedCurryGlobalEquiv_apply,
    ← homology_globalSections_map_comp_apply, derivedCurryIso_naturality_target,
    homology_globalSections_map_comp_apply]
  exact derivedSheafHomGlobalSectionsEquiv_naturality_target X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) m _

/-! ### The currying square at a K-injective target -/

/-- **The value of degree-zero global hypercohomology of the currying isomorphism of Stacks
08DJ on the class of a morphism of complexes, at a K-injective target.**  For `A`, `B` K-flat and
`I` K-injective and a morphism of complexes `f : A ⟶ SheafHom(B, I)`, the currying isomorphism
carries the class of `f` pushed along the inverse of the K-injective model comparison to the class
of the transpose of `f` pushed along the K-flat comparison of Stacks 06YU.

This is `curryIso_comparison_conj` and `classOfHom_transport`, the latter at the currying
isomorphism of complexes of Stacks 0A90 and at
`AlgebraicGeometry.RingedSite.globalCohomologyClassOfHom_curryHomEquiv`. -/
private lemma curryGlobalEquiv_classOfHomComp_comparison
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    [I.IsKInjective] [((sheafHomComplex X B I).obj).IsKInjective]
    (f : A ⟶ (sheafHomComplex X B I).obj) :
    derivedCurryGlobalEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj I)
        (derivedGlobalSectionsClassOfHomComp X A (sheafHomComplex X B I).obj hA f
          (derivedSheafHomComparison X B I).inv) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map
              ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B
                hB).hom.op).app (DerivedCategory.Q.obj I)))
        (derivedGlobalSectionsClassOfHomOfKFlat X
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I
          (Stacks.SheafOfModules.kFlat_tensorComplex X.O hA hB) (curryHomEquiv X A B I f)) := by
  have : ((sheafHomComplex X A (sheafHomComplex X B I).obj).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A (sheafHomComplex X B I).obj hA
  have : ((sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ I
      (Stacks.SheafOfModules.kFlat_tensorComplex X.O hA hB)
  have hD : ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
        (derivedSheafHomComparison X B I).inv ≫
      (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj I)).hom =
    ((derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
          (derivedSheafHomComparison X
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv) ≫
      ((derivedSheafHomBifunctor X).map
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B
          hB).hom.op).app (DerivedCategory.Q.obj I) := by
    rw [curryIso_comparison_conj X A B I hB, tensorHomRepresentativeIso_inv_eq X A B I hB]
    simp only [Category.assoc]
    rfl
  rw [derivedCurryGlobalEquiv_apply, derivedGlobalSectionsClassOfHomComp,
    ← homology_globalSections_map_comp_apply, hD, homology_globalSections_map_comp_apply]
  exact congrArg _ (classOfHom_transport X (sheafHomTensorCurryIso X A B I).hom f
    (curryHomEquiv X A B I f) (globalCohomologyClassOfHom_curryHomEquiv X A B I f).symm)

/-- **The currying square of Tag 0GM7 at a K-injective target.**  Stacks 08JA of the value of
the currying isomorphism of Stacks 08DJ on the class of a morphism of complexes
`f : A ⟶ SheafHom(B, I)` is the K-flat comparison of Stacks 06YU followed by the class of the
transpose of `f`. -/
private lemma globalSectionsEquiv_curryGlobalEquiv_classOfHomComp_comparison
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    [I.IsKInjective] [((sheafHomComplex X B I).obj).IsKInjective]
    (f : A ⟶ (sheafHomComplex X B I).obj) :
    derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) (DerivedCategory.Q.obj I)
        (derivedCurryGlobalEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj I)
          (derivedGlobalSectionsClassOfHomComp X A (sheafHomComplex X B I).obj hA f
            (derivedSheafHomComparison X B I).inv)) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B I f) := by
  rw [curryGlobalEquiv_classOfHomComp_comparison X A B I hA hB f]
  exact globalSectionsEquiv_classOfHom_map_source X
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I
    (Stacks.SheafOfModules.kFlat_tensorComplex X.O hA hB) (curryHomEquiv X A B I f)
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom

/-! ### The currying square at an arbitrary target, on the explicit class -/

/-- **The value of degree-zero global hypercohomology of the currying isomorphism of Stacks
08DJ on the class the evaluation square of Tag 0GM7 asks about.**  For `B`, `P` K-flat and `C`
arbitrary, and a morphism of complexes `p : P ⟶ SheafHom(B, C)`, the currying isomorphism carries
the class of `p` composed with the K-injective augmentation of the target, pushed along the two
isomorphisms of `D(O)` that the comparison of Stacks 08DM factors through, to the Stacks 08JA
preimage of the K-flat comparison of Stacks 06YU followed by the class of the transpose of `p`.

**This is the computation the evaluation square of Tag 0GM7 was reduced to**, and nothing else was
owed.  The target is released from the K-injective resolution by cancelling the image of the
augmentation, which is invertible in `D(O)` — on the left by
`globalSectionsEquiv_curryGlobalEquiv_naturality_target` and
`derivedGlobalSectionsClassOfHomComp_comp`, and on the right by
`AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_target`. -/
theorem derivedCurryGlobalEquiv_derivedGlobalSectionsClassOfHomComp_kInjectiveResolution
    (B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj)
    [((sheafHomComplex X B ((kInjectiveResolution X).obj C)).obj).IsKInjective] :
    derivedCurryGlobalEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C)
        (derivedGlobalSectionsClassOfHomComp X P
          (sheafHomComplex X B ((kInjectiveResolution X).obj C)).obj hP
          (p ≫ homMap X (𝟙 B) ((kInjectiveAugmentation X).app C))
          ((derivedSheafHomComparison X B ((kInjectiveResolution X).obj C)).inv ≫
            inv (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).map
              (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C))))) =
      (derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj B))
        (DerivedCategory.Q.obj C)).symm
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
          DerivedCategory.Q.map (curryHomEquiv X P B C p)) := by
  have : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hψχ : ((derivedSheafHomComparison X B ((kInjectiveResolution X).obj C)).inv ≫
        inv (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).map
          (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C)))) ≫
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).map
        (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C)) =
    (derivedSheafHomComparison X B ((kInjectiveResolution X).obj C)).inv := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine (derivedSheafHomGlobalSectionsEquiv X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj B))
    (DerivedCategory.Q.obj C)).injective ?_
  rw [AddEquiv.apply_symm_apply]
  refine (cancel_mono
    (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C))).1 ?_
  refine Eq.trans (globalSectionsEquiv_curryGlobalEquiv_naturality_target X
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
    (DerivedCategory.Q.map ((kInjectiveAugmentation X).app C)) _).symm ?_
  rw [derivedGlobalSectionsClassOfHomComp_comp, hψχ,
    globalSectionsEquiv_curryGlobalEquiv_classOfHomComp_comparison X P B
      ((kInjectiveResolution X).obj C) hP hB
      (p ≫ homMap X (𝟙 B) ((kInjectiveAugmentation X).app C)),
    curryHomEquiv_naturality_target X P B ((kInjectiveAugmentation X).app C) p,
    CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- **Degree-zero global hypercohomology of the currying isomorphism of Stacks 08DJ on
`AlgebraicGeometry.RingedSite.precomposedHomComparisonClass`.**  This is the statement the module
note of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationSquareComparisonClass` records
as what the evaluation square of Tag 0GM7 still owes, with the class written as that file supplies
it: the comparison of Stacks 08DM is the class of a morphism of internal Hom complexes followed by
two isomorphisms of `D(O)`, and `derivedInternalHomOfBifunctor` is the derived internal Hom whose
bifunctor is `RSheafHom(-, -)` on the nose. -/
theorem derivedCurryGlobalEquiv_precomposedHomComparisonClass
    (B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj) :
    derivedCurryGlobalEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C)
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B C P hB hP p) =
      (derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj B))
        (DerivedCategory.Q.obj C)).symm
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
          DerivedCategory.Q.map (curryHomEquiv X P B C p)) :=
  have := isKInjective_sheafHomComplex_of_isKFlat X B ((kInjectiveResolution X).obj C) hB
  derivedCurryGlobalEquiv_derivedGlobalSectionsClassOfHomComp_kInjectiveResolution X B C P hB hP p

/-! ### The currying square of Tag 0GM7 -/

/-- **The currying square of Tag 0GM7 at a K-flat source** — the hypothesis `hcurry` of
`AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare`, discharged.  Granted only that
Stacks 08JA carries `AlgebraicGeometry.RingedSite.precomposedHomComparisonClass` to `Q p ≫ σ` —
which is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass`,
holding for `σ` the comparison of Stacks 08DM — the bijection of Stacks 08DI carries `Q p ≫ σ` to
the K-flat comparison of Stacks 06YU followed by the class of the transpose of `p`.

`σ` is a variable and the identification is a hypothesis for the reason recorded in the
implementation notes: the statement with the comparison of Stacks 08DM written out exhausts
`maxRecDepth` at its own type. -/
theorem curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass
    (B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj)
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (hσ : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj P)
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B C P hB hP p) =
      DerivedCategory.Q.map p ≫ σ) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) (DerivedCategory.Q.map p ≫ σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X P B C p) := by
  rw [derivedCurryHomEquiv_Q_map_comp_of_globalSectionsEquiv X B C P σ p _ hσ,
    derivedCurryGlobalEquiv_precomposedHomComparisonClass X B C P hB hP p,
    AddEquiv.apply_symm_apply]

/-- `curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass` with the class
abstracted: both of its identifications — the Stacks 08JA preimage and the value of the currying
isomorphism — are hypotheses, so a consumer with any class satisfying them obtains the currying
square.  The instance of it used here takes
`AlgebraicGeometry.RingedSite.precomposedHomComparisonClass` for the class. -/
theorem curryingSquare_of_curryGlobalEquiv
    (B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (p : P ⟶ (sheafHomComplex X B C).obj)
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj P))).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C)))) : Type u))
    (hx : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj P)
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C)) x =
      DerivedCategory.Q.map p ≫ σ)
    (hcl : derivedCurryGlobalEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) x =
      (derivedSheafHomGlobalSectionsEquiv X
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj B))
        (DerivedCategory.Q.obj C)).symm
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
          DerivedCategory.Q.map (curryHomEquiv X P B C p))) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) (DerivedCategory.Q.map p ≫ σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight P B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X P B C p) := by
  rw [derivedCurryHomEquiv_Q_map_comp_of_globalSectionsEquiv X B C P σ p x hx, hcl,
    AddEquiv.apply_symm_apply]

/-- **The currying square of Tag 0GM7 at an arbitrary source.**  For a morphism of complexes
`f : A ⟶ SheafHom(B, C)` with `A` arbitrary, the bijection of Stacks 08DI carries `Q f ≫ σ` to the
K-flat comparison of Stacks 06YU followed by the class of the transpose of `f`.

**The evaluation square of Tag 0GM7 is formed in the proof**: the square at `σ` is
`AlgebraicGeometry.RingedSite.evaluationSquare_of_curryingSquare` applied to the currying square
at the K-flat source `P`, and the conclusion here is
`AlgebraicGeometry.RingedSite.curryingSquare_of_evaluationSquare` applied to that square.  So the
square is proved inside this statement; it is recorded this way because the square's own
conclusion, together with the hypothesis `hσ`, exhausts `maxRecDepth` at a declaration's type. -/
theorem curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass_source
    (A B C P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hP : Stacks.SheafOfModules.IsKFlat X.O P)
    (p : P ⟶ (sheafHomComplex X B C).obj) (hp : IsIso (DerivedCategory.Q.map p))
    (σ : DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C))
    (hσ : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj P)
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
          (DerivedCategory.Q.obj C))
        (precomposedHomComparisonClass X (derivedInternalHomOfBifunctor X) B C P hB hP p) =
      DerivedCategory.Q.map p ≫ σ)
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) (DerivedCategory.Q.map f ≫ σ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) :=
  curryingSquare_of_evaluationSquare X A B C σ hB
    (evaluationSquare_of_curryingSquare X P B C σ hB p hp
      (curryingSquare_of_globalSectionsEquiv_precomposedHomComparisonClass X B C P hB hP p σ hσ)) f

end AlgebraicGeometry.RingedSite

end
