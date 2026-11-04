module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamEnvelopeComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothPresentationBaseChange

/-!
# The structure module of the example of [Stacks, Tag 07LK], base changed to its presentation

In the situation `X/S` of the example of [Stacks, Tag 07LK], with `D` the completed envelope of
the canonical presentation of [Stacks, Section 60.17, Tag 07J7] and `D'` the completed envelope of
the example's presentation `P = 𝐙_p[x_1, …, x_r] → Γ(X, 𝒪_X)`, the structure module `(D, d)`
base changed along any morphism `D → D'` of rings with forms has for de Rham complex the example's
complex `D → Ω¹_D → ⋯ → Ω^r_D` (`Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat`).

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.unitBaseChangeComplexIso` — the identification of
  complexes.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DividedPowers

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

/-- The ring with forms `D` of the canonical presentation of the situation of the example. -/
abbrev canonicalData : FormsData.{0} T.affineSit.p := canonicalFormsData T.affineSit 0

/-- The ring with forms `D'` of the example's presentation `P → Γ(X, 𝒪_X)`. -/
abbrev presentationData : FormsData.{0} T.affineSit.p :=
  presentationFormsData T.affineSit T.presentation

/-- **The structure module of `D`, base changed along a morphism `D → D'` of rings with forms, has
the example's complex `D → Ω¹_D → ⋯` for de Rham complex.** -/
def unitBaseChangeComplexIso (g : FormsData.Hom T.canonicalData T.presentationData) :
    ((T.canonicalData.unitConnModule
      (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _)).baseChange g).complex ≅
      T.deRhamComplexNat :=
  haveI := FormsData.ConnModule.isIso_complexMap _
    (FormsData.baseChangeUnitHom_bijective g
      (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _)
      (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _))
  (asIso (FormsData.ConnModule.complexMap (FormsData.baseChangeUnitHom g
      (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _)
      (FormsData.isPAdicallyComplete_ofDividedPowers _ _ _)))).symm ≪≫
    FormsData.unitComplexIso T.affineSit.p (T.affineSit.A : Type)
      (presentationEnvelope T.affineSit T.presentation).object.dividedPowers ≪≫
    T.deRhamComplexNatIsoEnvelope.symm

end AffineSpaceCrystallineSetup

end Crystalline

end
