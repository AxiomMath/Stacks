module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceDeRhamPushforward
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.AbelianAcyclic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic

/-!
# `π_* = Rπ_*` on the de Rham complex of the total space of a line bundle

Let `f : X ⟶ S` be a morphism of schemes, let `L` be an invertible `𝒪_X`-module and let
`π : 𝕃 ⟶ X` be the total space of `L`, packaged as `Stacks.LineBundle.Situation`. This file shows
that the sheaves `Ω^p_{𝕃/S}` of relative differential forms on the total space are right acyclic
for the direct image of abelian sheaves along `π`, and deduces that
`π_*Ω^•_{𝕃/S} ⟶ Rπ_*Ω^•_{𝕃/S}` is an isomorphism in `D⁺`.

## Main results

* `Stacks.LineBundle.Situation.rightAcyclic_abelianPushforward_totalSpaceForms`: the abelian
  sheaf underlying `Ω^p_{𝕃/S}` is right acyclic for the direct image of abelian sheaves along
  `π`, in every degree `p : ℕ`.
* `Stacks.LineBundle.Situation.rightAcyclic_abelianPushforward_deRhamTermInt`: the same in every
  degree `n : ℤ` of the de Rham complex extended to a `ℤ`-indexed complex.
* `Stacks.LineBundle.Situation.isIso_deRhamPushforwardToDerived`: **`π_*Ω^•_{𝕃/S} = Rπ_*Ω^•_{𝕃/S}`
  for the total space of a line bundle** —
  `AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` is an isomorphism.
* `Stacks.LineBundle.Situation.isIso_deRhamCohomologyPullback_of_isIso_derivedComparison`:
  **de Rham cohomology is unchanged by passing to the total space as soon as the de Rham
  comparison is inverted in `D⁺`** — the second conclusion of [Stacks, Tag 0FUI] granted its
  first, in derived-category form.

## References

* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.LerayLowDegree

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The abelian sheaf underlying `Ω^p_{𝕃/S}` is right acyclic for the direct image of abelian
sheaves along the projection from the total space of a line bundle**, in every degree. -/
theorem Situation.rightAcyclic_abelianPushforward_totalSpaceForms (p : ℕ) :
    (Stacks.AlgebraicGeometry.HigherDirectImage.abelianPushforward
        D.totalSpaceToBase).rightAcyclic
      ((_root_.SheafOfModules.toSheaf.{u} D.totalSpace.ringCatSheaf).obj
        (Scheme.Hom.relativeDifferentialForms (D.totalSpaceToBase ≫ D.f) (p : ℤ))) :=
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (D.totalSpaceToBase ≫ D.f) p
  Stacks.AlgebraicGeometry.HigherDirectImage.rightAcyclic_abelianPushforward_toSheaf_of_isAffineHom
    _ _

/-- **Every degree of the `ℤ`-indexed abelian de Rham complex of the total space is right acyclic
for the direct image of abelian sheaves along `π`.** -/
theorem Situation.rightAcyclic_abelianPushforward_deRhamTermInt (n : ℤ) :
    (abelianPushforward.{u, u} D.totalSpaceToBase.base).rightAcyclic
      ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt
        (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f)))).X n) := by
  rcases Int.lt_or_le n 0 with hn | hn
  · exact Stacks.RightAcyclicProduct.rightAcyclic_of_isZero _
      (HomologicalComplex.isZero_extend_X _ _ n (fun i hi => by
        have hi' : (i : ℤ) = n := hi
        omega))
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := p) rfl).symm
      (D.rightAcyclic_abelianPushforward_totalSpaceForms p)

/-- **The unit `π_*Ω^•_{𝕃/S} ⟶ Rπ_*Ω^•_{𝕃/S}` is invertible**: the unit of the right derived
functor of the direct image of abelian sheaves along `π` is an isomorphism at the de Rham complex
of the total space. -/
theorem Situation.isIso_rightDerivedFunctorPlusUnit_deRhamAbelianComplexPlus :
    IsIso ((abelianPushforward.{u, u} D.totalSpaceToBase.base).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient
          (Stacks.Cohomology.Leray.AbelianSheaf D.totalSpace.toRingedSpace.carrier)).obj
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
          (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (D.totalSpaceToBase ≫ D.f)))))) :=
  CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _
    D.rightAcyclic_abelianPushforward_deRhamTermInt

/-- **`π_*Ω^•_{𝕃/S} = Rπ_*Ω^•_{𝕃/S}` for the total space of a line bundle**: the comparison
`AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` is an isomorphism. -/
theorem Situation.isIso_deRhamPushforwardToDerived :
    IsIso (Scheme.Hom.deRhamPushforwardToDerived D.totalSpaceToBase
      (D.totalSpaceToBase ≫ D.f)) := by
  have := D.isIso_rightDerivedFunctorPlusUnit_deRhamAbelianComplexPlus
  delta Scheme.Hom.deRhamPushforwardToDerived
  infer_instance

/-- **De Rham cohomology is unchanged by passing to the total space of a line bundle, granted
that the de Rham comparison is inverted in `D⁺`**: if the comparison
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus` becomes invertible under
`DerivedCategory.Plus.Q`, then the pullback `Scheme.Hom.deRhamCohomologyPullback` along `π` is an
isomorphism in every degree `i`. -/
theorem Situation.isIso_deRhamCohomologyPullback_of_isIso_derivedComparison
    (hcomparison : IsIso (DerivedCategory.Plus.Q.map
      (Scheme.Hom.deRhamAbelianPushforwardMapPlus D.totalSpaceToBase D.f
        (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp)))
    (i : ℤ) :
    IsIso (Scheme.Hom.deRhamCohomologyPullback D.totalSpaceToBase D.f
      (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp i) := by
  have := D.isIso_deRhamPushforwardToDerived
  have : IsIso (Scheme.Hom.deRhamDerivedSectionsPullback D.totalSpaceToBase D.f
      (D.totalSpaceToBase ≫ D.f) (𝟙 D.S) D.totalSpaceToBase_comp) := by
    delta Scheme.Hom.deRhamDerivedSectionsPullback
    infer_instance
  delta Scheme.Hom.deRhamCohomologyPullback
  infer_instance

end Stacks.LineBundle

end
