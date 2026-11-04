module

public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechDerivedSections
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyComparisonSupplement

/-!
# The Koszul Čech complex computes `RΓ(U, -)` on the associated sheaves

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  For a complex `M^•` of `A`-modules the
total alternating Čech complex of the associated sheaves, which Tag 08D1 identifies with
`colimₑ Hom^•(I^•(f^e), M^•)`, computes `RΓ(U, M̃^•)`: this file assembles the identification

`Q(Tot(Č_alt(𝒰, M̃^•))) ≅ RΓ(U, M̃^•)` in `D(Ab)`,

and reads it in degree zero as a natural isomorphism onto `H⁰(U, M̃^•)` in the spelling the
Koszul comparison map of Tag 08DC is stated against.

## Main definitions

* `Koszul.DerivedSystem.alternatingCechTotalDerivedSectionsIso` is the resulting natural
  isomorphism `H⁰(Tot(Č_alt(𝒰, M̃^•))) ≅ H⁰(U, M̃^•)`, natural in the complex `M^•`.

## Main results

* `Koszul.DerivedSystem.isQuasicoherent_restrictTilde_X`: the terms of `M̃^•|_U` are
  quasi-coherent, which is what feeds the abelian form of Tag 08D2.
* `Koszul.DerivedSystem.isIso_alternatingCechToDerivedComparison_tilde`: the comparison map of
  Tag 08C1 for the covering of `U` by the `D(fᵢ)` is an isomorphism at `M̃^•|_U`.
* `Koszul.DerivedSystem.restrictComplexFunctor_eq`: restriction of complexes to `U` is the
  functor of the extension-by-zero adjunction, applied degreewise.

## Implementation notes

The chain has five links, all of them already available: the abelian form of Tag 08D2 inverts
the Čech comparison of Tag 08C1 at a complex with quasi-coherent terms; the two models of
derived global sections on an open subspace agree; restriction of complexes commutes with the
passage to the derived category; derived sections over an open are derived sections of the
restriction, which is Tag 0D5V; and sheafification of complexes commutes with the passage to
the derived category.

The sheaf of rings of the open subscheme `U` is spelled `resRing U 𝒪_X` here and
`(unionScheme f).ringCatSheaf` in the Čech identification of
`StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechOnUnion`; the two are the same object, and the
restatement is what lets the Čech comparison of Tag 08C1, which is phrased for a sheaf of rings
on a space, be applied.

## References

* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A)

/-! ### Quasi-coherence of the restricted associated sheaves -/

/-- The associated sheaf of a module is quasi-coherent. -/
public instance isQuasicoherent_sheafifyModule_obj (M : ModuleCat.{u} A) :
    ((sheafifyModule A).obj M).IsQuasicoherent :=
  inferInstanceAs (((tilde.functor A).obj M).IsQuasicoherent)

/-- The restriction to `U` of a quasi-coherent module is quasi-coherent. -/
public instance isQuasicoherent_restrictFunctorOfUnion_obj
    (N : SheafOfModules.{u} (Spec A).ringCatSheaf) [N.IsQuasicoherent] :
    ((restrictFunctorOfUnion f).obj N).IsQuasicoherent :=
  @Scheme.Modules.isQuasicoherent_restrictFunctor _ (Spec A) (unionOfBasicOpens f).ι
    inferInstance N inferInstance

/-- **The terms of `M̃^•|_U` are quasi-coherent.** -/
public theorem isQuasicoherent_restrictTilde_X (M : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (((restrictComplexFunctor f).obj ((tildeFunctorMapComplex A).obj M)).X n).IsQuasicoherent :=
  isQuasicoherent_restrictFunctorOfUnion_obj f ((sheafifyModule A).obj (M.X n))

/-! ### The Čech comparison is an isomorphism on the associated sheaves -/

/-- **The comparison map of Tag 08C1 is an isomorphism at `M̃^•|_U`.**  This is the abelian form
of Tag 08D2, fed with the quasi-coherence of the terms. -/
public theorem isIso_alternatingCechToDerivedComparison_tilde
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso ((Stacks.Cech.alternatingCechToDerivedComparison (unionSpace f) (unionRingSheaf f)
      (unionSpaceCover f) (iSup_unionSpaceCover f)).app
        ((restrictComplexFunctor f).obj ((tildeFunctorMapComplex A).obj M))) :=
  isIso_alternatingCechToDerivedComparison f _ (isQuasicoherent_restrictTilde_X f M)

/-! ### Restriction of complexes is the extension-by-zero restriction -/

/-- **Restriction of complexes to `U` is the restriction functor of the extension-by-zero
adjunction, applied degreewise.** -/
public theorem restrictComplexFunctor_eq :
    restrictComplexFunctor f =
      (jStar (unionOfBasicOpens f) (Spec A).ringCatSheaf).mapHomologicalComplex (up ℤ) := by
  unfold restrictComplexFunctor
  congr 1
  exact restrictFunctorOfUnion_eq_jStar f

/-! ### The identification of degree-zero cohomology -/

/-- **The total alternating Čech complex computes `H⁰(U, -)` on the associated sheaves.**  For a
complex `M^•` of `A`-modules the degree-zero cohomology of the total alternating Čech complex of
the covering of `U` by the `D(fᵢ)`, with coefficients in `M̃^•`, is the degree-zero
hypercohomology of `M̃^•` over `U`, naturally in `M^•`. -/
public def alternatingCechTotalDerivedSectionsIso :
    Koszul.alternatingCechTotalFunctor f ⋙ DerivedCategory.Q ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 ≅
      DerivedCategory.Q ⋙ derivedSheafify A ⋙ sectionsOnUnion f := by
  have happ : ∀ M, IsIso ((Functor.whiskerLeft
      (tildeFunctorMapComplex A ⋙ restrictComplexFunctor f)
      (Stacks.Cech.alternatingCechToDerivedComparison (unionSpace f) (unionRingSheaf f)
        (unionSpaceCover f) (iSup_unionSpaceCover f))).app M) :=
    fun M ↦ isIso_alternatingCechToDerivedComparison_tilde f M
  have hcomp : IsIso (Functor.whiskerLeft (tildeFunctorMapComplex A ⋙ restrictComplexFunctor f)
      (Stacks.Cech.alternatingCechToDerivedComparison (unionSpace f) (unionRingSheaf f)
        (unionSpaceCover f) (iSup_unionSpaceCover f))) := NatIso.isIso_of_isIso_app _
  exact
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight (alternatingCechTotalIsoOfUnion f)
        DerivedCategory.Q) (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)) ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerLeft
        (tildeFunctorMapComplex A ⋙ restrictComplexFunctor f)
        (Stacks.Cech.alternatingCechToDerivedComparison (unionSpace f) (unionRingSheaf f)
          (unionSpaceCover f) (iSup_unionSpaceCover f))))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft
        (tildeFunctorMapComplex A ⋙ restrictComplexFunctor f)
        (unboundedDerivedSectionsIso (Spec A).ringCatSheaf (unionOfBasicOpens f)))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (tildeFunctorMapComplex A)
        (Functor.isoWhiskerRight
          (eqToIso (congrArg (· ⋙ DerivedCategory.Q) (restrictComplexFunctor_eq f)) ≪≫
            restrictComplexDerivedIso (Spec A).ringCatSheaf (unionOfBasicOpens f))
          (derivedSectionsOnOpenSubspace (Spec A).ringCatSheaf (unionOfBasicOpens f))))
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0) ≪≫
    Functor.isoWhiskerLeft (tildeFunctorMapComplex A ⋙ DerivedCategory.Q)
      (cohomologyOnOpenIsoRestriction (Spec A).ringCatSheaf (unionOfBasicOpens f) 0).symm ≪≫
    Functor.isoWhiskerRight (sheafifyModule A).mapDerivedCategoryFactors.symm
      (derivedSectionsOnOpen (Spec A).ringCatSheaf (unionOfBasicOpens f) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0)

end Koszul.DerivedSystem

end
