module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigModuleAbelianComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# `H^n(CRIS(X/S), ℱ) = H^n(Cris(X/S), i_X^{-1}ℱ)` at abelian coefficients

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `i : Cris(X/S) ⥤ CRIS(X/S)` be the
inclusion of the small crystalline site into the big one.  Restriction along `i` does not change
cohomology, at abelian coefficients and in every degree:

`R^n Γ(CRIS(X/S), -) ≅ i^{-1} ⋙ R^n Γ(Cris(X/S), -)`.

This is Leray for the retraction `π : (X/S)_CRIS ⟶ (X/S)_cris` of [Stacks, Tag 07IJ], whose
pushforward is `π_* = i^{-1}`, collapsed because `π_*` is exact: `i^{-1}` is a right adjoint of
the abelian lower shriek `i_!`, which is exact by clause (6) of [Stacks, Tag 07IJ], so it
preserves injective objects by [Stacks, Tag 015Z]; it is also a left adjoint, of `i_*`; and the
global sections satisfy `Γ(Cris(X/S), i^{-1}ℱ) ≅ Γ(CRIS(X/S), ℱ)`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `preservesFiniteColimits_smallRestriction` — `i^{-1}` on abelian sheaves preserves finite
  colimits, being a left adjoint of the abelian direct image along the inclusion.
* `bigRightDerivedGlobalSectionsIso` — **`R^n Γ(CRIS(X/S), -) ≅ i^{-1} ⋙ R^n Γ(Cris(X/S), -)`**
  for every `n`, naturally in the abelian sheaf on the big crystalline site.
* `isZero_rightDerivedGlobalSections_smallRestriction_iff` — the vanishing form: the abelian
  cohomology of `i^{-1}ℱ` over `Cris(X/S)` vanishes in a degree exactly when that of `ℱ` over
  `CRIS(X/S)` does.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **Restriction to the small crystalline site preserves finite colimits**, being the left
adjoint of the abelian direct image `i_{X, *}` along the inclusion. -/
instance preservesFiniteColimits_smallRestriction :
    PreservesFiniteColimits (smallRestriction S) :=
  haveI : PreservesColimitsOfSize.{u + 1, u + 1} (smallRestriction S) :=
    (bigDirectImageAdjunction S).leftAdjoint_preservesColimits
  inferInstance

/-- **`R^n Γ(CRIS(X/S), -) ≅ i^{-1} ⋙ R^n Γ(Cris(X/S), -)`**: the abelian-valued cohomology of
the big crystalline site is the cohomology of the small crystalline site of the restricted sheaf,
in every degree and naturally in the sheaf.

This is [Stacks, Tag 015M] for the pair `(i^{-1}, Γ(Cris(X/S), -))`, which is Leray for the
retraction `π` of [Stacks, Tag 07IJ] with `R^{>0}π_* = 0`. -/
def bigRightDerivedGlobalSectionsIso (n : ℕ) :
    (bigGlobalSections S).rightDerived n ≅
      smallRestriction S ⋙ (globalSections S).rightDerived n :=
  (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (smallRestrictionGlobalSectionsIso (S := S)) n).symm ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (smallRestriction S) (globalSections S) n

/-- **Restriction to the small crystalline site neither creates nor destroys abelian cohomology.**
The degreewise form of `bigRightDerivedGlobalSectionsIso` at a fixed abelian sheaf on
`CRIS(X/S)`. -/
theorem isZero_rightDerivedGlobalSections_smallRestriction_iff
    (F : Sheaf (topology S) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsZero (((globalSections S).rightDerived n).obj ((smallRestriction S).obj F)) ↔
      IsZero (((bigGlobalSections S).rightDerived n).obj F) :=
  ((bigRightDerivedGlobalSectionsIso S n).app F).isZero_iff.symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end
