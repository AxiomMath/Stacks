module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedPlusDoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentPushforwardAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationTotalComparison

/-!
# The spectral sequence of an augmentation of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and let `a` be an augmentation of `S` towards
a site `(D, K)` (Stacks 0D6Z). For `M` in `D⁺(C_total)` there is a spectral sequence

```
E_1^{p,q} = R^q a_{p,*} M_p  ⇒  R^{p+q} a_* M,
```

functorial in `M` (Stacks 0D7A). This file constructs it.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.HigherDirectImageSpectralSequence`: the
  statement of Stacks 0D7A as a structure: a functor from `D⁺(C_total)` to cohomological spectral
  sequences of abelian sheaves on `D`, an identification of its first page with
  `R^q a_{p,*} M_p` natural in `M`, the vanishing of the first page in negative columns, and the
  abutment to `R^{p+q} a_* M`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.higherDirectImageSpectralSequence`:
  **Stacks 0D7A**.

## Implementation notes

The construction is the source's. Represent `M` by a bounded below complex of injectives `I^•` and
take the double complex `A^{q,p} = a_{p,*} I^q_p` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationSpectralSequence.lean`, whose horizontal
maps come from Stacks 0D79. Restriction to `C_p` is exact and preserves injectives (Stacks 09WH),
so `I^•_p` is a bounded below complex of injectives representing `M_p` and the columns compute
`R^q a_{p,*} M_p`; the rows are exact in positive degrees with `a_* I^q` as kernel in degree `0`
(Stacks 0D79), so the total complex computes `R a_* M` (Stacks 0133). The spectral sequence is the
one of the filtration by the simplicial degree; it is functorial in `M` from its first page on,
homotopic maps of complexes inducing the same maps there. The general machinery is
`StacksFrontier/Algebra/Homology/SpectralSequence/DerivedPlusDoubleComplex.lean`.

The spectral sequence is presented from its first page: its zeroth page is the double complex of a
chosen resolution, which is not functorial in `M`. The first page is indexed by `ℤ × ℤ`, an object
of `D⁺(C_total)` being bounded below in an arbitrary degree; it vanishes in the negative columns.

The derived categories are the standard ones, `CategoryTheory.HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

section Construction

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

attribute [local instance] abelianSheafTarget abelianSheafTotal hasInjectiveResolutionsSheafTotal
  hasZeroObjectSheafTotal hasColimitsOfSizeSheafTarget hasColimitsOfShapeDiscreteSheafTarget

/-- Every double complex of abelian sheaves on the augmentation site has a total complex. -/
local instance hasTotalSheafTarget
    (L : HomologicalComplex₂ (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    L.HasTotal (ComplexShape.up ℤ) :=
  inferInstance

/-- Evaluating the complex of degreewise direct images, extended by zero, in a non-negative
simplicial degree `p` gives `a_{p,*}(-)_p`, read as the restriction to `C_p` followed by the
direct image along `a_p`. -/
def degreewisePushforwardComplexCompEvalIso (p : ℕ) :
    degreewisePushforwardComplex S D K a ⋙
        HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) (p : ℤ) ≅
      restrictAb S ⦋p⦌ ⋙ componentAugmentationPushforwardAb S D K a ⦋p⦌ :=
  Functor.isoWhiskerLeft (degreewisePushforwardComplexNat S D K a)
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso (Sheaf K AddCommGrpCat.{u})
        (i := p) (i' := (p : ℤ)) rfl) ≪≫
    abelianComponentPushforwardIso S D K a ⦋p⦌

/-- The spectral sequence of Stacks 0D7A, as a functor of `M` in `D⁺(C_total)`: represent `M` by
a bounded below complex of injectives `I^•` and take the second spectral sequence of the double
complex `A^{q,p} = a_{p,*} I^q_p`. -/
def derivedSpectralSequence :
    DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u}) ⥤
      CohomologicalSpectralSequence (Sheaf K AddCommGrpCat.{u}) 1 :=
  Stacks.DegreewiseSpectralSequence.derivedFunctor (degreewisePushforwardComplex S D K a)

/-- **`E_1^{p,q} = R^q a_{p,*} M_p`**, naturally in `M`. -/
def derivedSpectralSequencePageOneIso (p : ℕ) (q : ℤ) :
    derivedSpectralSequence S D K a ⋙
        CategoryTheory.SpectralSequence.pageFunctor (Sheaf K AddCommGrpCat.{u}) _ 1 1 le_rfl ⋙
          HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u}) _ ((p : ℤ), q) ≅
      (restrictAb S ⦋p⦌).mapDerivedCategoryPlus ⋙
        (componentAugmentationPushforwardAb S D K a ⦋p⦌).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (Sheaf K AddCommGrpCat.{u}) q :=
  Stacks.DegreewiseSpectralSequence.derivedPageOneIso (degreewisePushforwardComplex S D K a)
    (p : ℤ) q (restrictAb S ⦋p⦌) (componentAugmentationPushforwardAb S D K a ⦋p⦌)
    (degreewisePushforwardComplexCompEvalIso S D K a p)

/-- The first page vanishes in the negative columns. -/
theorem isZero_derivedSpectralSequence_page_one
    (M : DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u})) (p q : ℤ)
    (hp : p < 0) :
    IsZero ((((derivedSpectralSequence S D K a).obj M).page 1 le_rfl).X (p, q)) :=
  Stacks.DegreewiseSpectralSequence.isZero_derivedFunctor_page_one
    (degreewisePushforwardComplex S D K a) p q
    (fun _ => HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
      fun i => by change ((i : ℕ) : ℤ) ≠ p; omega) M

/-- **The spectral sequence abuts to `R^{p+q} a_* M`.** -/
theorem abutsTo_derivedSpectralSequence
    (M : DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u})) :
    CategoryTheory.SpectralSequence.AbutsTo ((derivedSpectralSequence S D K a).obj M)
      (fun n => (DerivedCategory.Plus.homologyFunctor (Sheaf K AddCommGrpCat.{u}) n).obj
        ((abelianTotalPushforward S D K a).rightDerivedFunctorPlus.obj M)) :=
  Stacks.DegreewiseSpectralSequence.abutsTo_derivedFunctor
    (degreewisePushforwardComplex S D K a) (abelianTotalPushforward S D K a)
    (totalAugmentationNat S D K a)
    (fun Z n hZ hinj => have := hZ; totalHypotheses S D K a Z n hinj) M

end Construction

section Statement

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

attribute [local instance] abelianSheafTarget abelianSheafTotal

/-- **The statement of Stacks 0D7A.** For an augmentation `a` of a simplicial-site situation
towards a site `(D, K)`: a cohomological spectral sequence of abelian sheaves on `D`, presented
from its first page and functorial in `M` in `D⁺(C_total)`, with
`E_1^{p,q} = R^q a_{p,*} M_p` naturally in `M` (and `E_1^{p,q} = 0` for `p < 0`), converging to
`R^{p+q} a_* M`. -/
structure HigherDirectImageSpectralSequence where
  /-- The spectral sequence, as a functor of `M` in `D⁺(C_total)`. -/
  sequence : DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u}) ⥤
    CohomologicalSpectralSequence (Sheaf K AddCommGrpCat.{u}) 1
  /-- `E_1^{p,q} = R^q a_{p,*} M_p`, naturally in `M`: the first page in column `p ≥ 0` is the
  `q`-th cohomology of the right derived direct image along `a_p` of the restriction of `M` to
  the component `C_p`. -/
  pageOneIso (p : ℕ) (q : ℤ) :
    sequence ⋙ CategoryTheory.SpectralSequence.pageFunctor (Sheaf K AddCommGrpCat.{u}) _ 1 1
        le_rfl ⋙ HomologicalComplex.eval (Sheaf K AddCommGrpCat.{u}) _ ((p : ℤ), q) ≅
      (restrictAb S ⦋p⦌).mapDerivedCategoryPlus ⋙
        (componentAugmentationPushforwardAb S D K a ⦋p⦌).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (Sheaf K AddCommGrpCat.{u}) q
  /-- The first page vanishes in the negative columns. -/
  isZero_pageOne (M : DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u}))
    (p q : ℤ) : p < 0 → IsZero (((sequence.obj M).page 1 le_rfl).X (p, q))
  /-- The spectral sequence converges to `R^{p+q} a_* M`. -/
  abutsTo (M : DerivedCategory.Plus (Sheaf S.totalTopology AddCommGrpCat.{u})) :
    CategoryTheory.SpectralSequence.AbutsTo (sequence.obj M)
      (fun n => (DerivedCategory.Plus.homologyFunctor (Sheaf K AddCommGrpCat.{u}) n).obj
        ((abelianTotalPushforward S D K a).rightDerivedFunctorPlus.obj M))

/-- **Stacks 0D7A.** For an augmentation `a` of a simplicial-site situation towards a site
`(D, K)` and `M` in `D⁺(C_total)` there is a spectral sequence

`E_1^{p,q} = R^q a_{p,*} M_p  ⇒  R^{p+q} a_* M`,

functorial in `M`. It is the spectral sequence of the double complex `A^{q,p} = a_{p,*} I^q_p` of
a bounded below complex of injectives `I^•` representing `M`, filtered by the simplicial
degree. -/
@[stacks 0D7A]
def higherDirectImageSpectralSequence : HigherDirectImageSpectralSequence S D K a where
  sequence := derivedSpectralSequence S D K a
  pageOneIso := derivedSpectralSequencePageOneIso S D K a
  isZero_pageOne M p q := isZero_derivedSpectralSequence_page_one S D K a M p q
  abutsTo := abutsTo_derivedSpectralSequence S D K a

end Statement

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
