module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup

/-!
# A dominating admissible blowup in Situation 0AX8, from the strict-transform input alone

In Situation [Stacks, Tag 0AX8] there is a `U`-admissible blowup `b : S' ⟶ S` of the punctured
spectrum `U = S ∖ {s}` which dominates `X`, granted the strict-transform input
`AlgebraicGeometry.StrictTransformOpenImmersion` of the cited flattening result
[Stacks, Tag 081S]. The other input of
`AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating`, the Cartier
boundary reduction of [Stacks, Tag 080Y], is discharged here.

## Main results

* `AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating_of_strictTransform`

## References

* [Stacks Project, Tag 0B4M](https://stacks.math.columbia.edu/tag/0B4M)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

/-- In Situation [Stacks, Tag 0AX8] there is a `U`-admissible blowup `b : S' ⟶ S` of the
punctured spectrum `U = S ∖ {s}` which dominates `X`: it factors as `S' ⟶ X ⟶ S`, granted the
strict-transform input `hstrict` of [Stacks, Tag 081S].

This is [Stacks, Tag 081T] at the modification `f`, which is an isomorphism over `U`
(`isIso_morphismRestrict_puncturedSpectrumOpen`). The input [Stacks, Tag 080Y] of 081T holds
because `Spec(A)` is Noetherian, so its punctured spectrum is quasi-compact. Without the
hypothesis `hstrict` this is [Stacks, Tag 0B4M]. -/
theorem exists_isAdmissibleBlowup_dominating_of_strictTransform (V : VanishingSituation.{u})
    (hstrict : StrictTransformOpenImmersion V.f V.puncturedSpectrumOpen) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ V.base),
      Stacks.Blowup.IsAdmissibleBlowup V.puncturedSpectrumOpen b ∧
        ∃ g : S' ⟶ V.X, g ≫ V.f = b :=
  have : IsIso (V.f ∣_ V.puncturedSpectrumOpen) :=
    V.isIso_morphismRestrict_puncturedSpectrumOpen
  AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_isCompact V.f
    V.puncturedSpectrumOpen (NoetherianSpace.isCompact _) hstrict

end VanishingSituation

end AlgebraicGeometry

end
