module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
public import StacksFrontier.Cotangent.AtiyahClassBigSiteResolution
public import StacksFrontier.Cotangent.DerivedLowerShriekRestrictedCoefficients
public import StacksFrontier.Cotangent.Triangle.KeyFact

/-!
# `Lπ_!(𝒪) = Lπ_!(B̲)` at the site `C_{B/A}` itself

Let `A → B` be a ring map and let `𝒪 ⟶ B̲` be the augmentation of the structure sheaf of the site
`C_{B/A}` of [Stacks, Tag 08PR], read on the `AsSmall` model `CommAlgCat.atiyahSite` over which
the Atiyah triangle of [Stacks, Tag 09DD] is formed. This file proves that derived lower shriek
inverts that augmentation in every degree, which is the hypothesis
`Stacks.ChaoticSite.CoefficientInverted` of [Stacks, Tag 08RX] at that site.

## Main results

* `CommAlgCat.coefficientInverted_atiyahCoefficientHom`: `L_nπ_!` inverts the augmentation
  `𝒪 ⟶ B̲` of `CommAlgCat.atiyahSite` in every degree.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- Evaluating the augmentation `𝒪 ⟶ B̲` of `CommAlgCat.atiyahSite` on the cosimplicial object of
the standard resolution returns the universe lift of the augmentation `P_• ⟶ B`, as a map of
simplicial abelian groups. -/
private theorem whiskerLeft_atiyahStandardCosimplicialObject_atiyahCoefficientHom :
    Functor.whiskerLeft (atiyahStandardCosimplicialObject A B).op
        (Functor.whiskerRight (atiyahCoefficientHom A B)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) =
      Functor.whiskerRight
        (Functor.whiskerRight (standardResolution.{u, u} A B).hom (forgetAlgToAddCommGrp A))
        AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  rfl

/-- `L_nπ_!(𝒪) = L_nπ_!(B̲)` at the site `C_{B/A}` itself: derived lower shriek inverts the
augmentation `𝒪 ⟶ B̲` of `CommAlgCat.atiyahSite`, read on the underlying abelian presheaves, in
every degree. This is the hypothesis of [Stacks, Tag 08RX] on the coefficient map of the Atiyah
triangle of [Stacks, Tag 09DD]. -/
theorem coefficientInverted_atiyahCoefficientHom :
    Stacks.ChaoticSite.CoefficientInverted (atiyahCoefficientHom A B) := by
  intro n
  have hq := quasiIso_standardResolution_hom A B
  have hlift : QuasiIso ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight (standardResolution.{u, u} A B).hom
          (forgetAlgToAddCommGrp A)))) := inferInstance
  refine (Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff
    (atiyahStandardCosimplicialObject A B)
    (isPointResolution_atiyahStandardCosimplicialObject A B) _ n).2 ?_
  rw [whiskerLeft_atiyahStandardCosimplicialObject_atiyahCoefficientHom A B]
  exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight
        (alternatingFaceMapComplexCompMapHomologicalComplexIso
          AddCommGrpCat.uliftFunctor.{u + 1, u})
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.down ℕ) n))
      (Functor.whiskerRight (standardResolution.{u, u} A B).hom
        (forgetAlgToAddCommGrp A))).mp
    ((quasiIsoAt_iff_isIso_homologyMap _ n).mp (hlift.quasiIsoAt n))

end CommAlgCat

end
