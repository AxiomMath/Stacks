module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionInfinityZeroScheme

/-!
# The vector bundle as the complement of the zero scheme in its projective completion

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r`, with
vector bundle `p : E ⟶ X` and projective completion `π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X`, and let
`D = Z(s) ⊂ P` be the zero scheme of the section `s` of `𝒪_P(1)` given by `(0, 1)`. As soon as
`ψ : U ⟶ E` is an isomorphism, the open immersion `j : E ⟶ P` over `X` has image the
complement of `|D|` (Stacks 0ERW, proof).

## Main results

* `range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso_eq_compl_zeroScheme`:
  the image of `j` on points is the complement of `|D|`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- **The points of the zero scheme `Z(s)` are the image of the hyperplane at infinity.** -/
theorem range_pointsMap_zeroScheme_projectiveCompletionSection :
    Set.range (pointsMap B S hS _ (zeroScheme B S hS (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι) =
      Set.range (pointsMap B S hS _ (projectiveCompletionInfinityImmersion E hr).hom) := by
  have : Mono (projectiveCompletionInfinityImmersion E hr).hom :=
    mono_of_isClosedImmersion B S hS _
      (isClosedImmersion_projectiveCompletionInfinityImmersion E hr)
  rw [← range_pointsMap_ι_range B S hS (projectiveCompletionInfinityImmersion E hr).hom,
    range_projectiveCompletionInfinityImmersion_eq_zeroScheme E hr]

variable (hs : IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)))
    [IsIso (projectiveCompletionAffinePartToVectorBundle E hr hs)]

/-- **The image of `j : E ⟶ P` is the complement of the zero scheme `D = Z(s)`.** -/
theorem range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso_eq_compl_zeroScheme :
    Set.range (pointsMap B S hS _ (projectiveCompletionVectorBundleImmersionOfIsIso E hr hs).hom) =
      (Set.range (pointsMap B S hS _ (zeroScheme B S hS (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι))ᶜ := by
  rw [range_pointsMap_zeroScheme_projectiveCompletionSection,
    range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso]

end AlgebraicGeometry.Space

end
