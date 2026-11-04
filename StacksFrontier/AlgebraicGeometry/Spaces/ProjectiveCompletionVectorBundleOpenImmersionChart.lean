module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleChartIsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionVectorBundleOpenImmersion

/-!
# The vector bundle `𝐕(ℰ)` is an open subspace of its projective completion

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r`, with
projective completion `π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X`, the section `s ∈ Γ(P, 𝒪_P(1))` given by `(0, 1)`,
and its zero scheme `D = Z(s)`. The morphism `ψ : U ⟶ E` from the affine part `U = P ∖ D` to the
vector bundle `p : E ⟶ X` is an isomorphism, since it is one on every affine trivializing chart
of `X` (`isIso_toScheme_map_projectiveCompletionAffinePartChartToVectorBundleChart`).
Hence `j = ι ∘ ψ⁻¹ : E ⟶ P` is an open immersion over `X` whose image is the complement of `D`
(Stacks 0ERW, proof).

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `isIso_projectiveCompletionAffinePartToVectorBundle`: `ψ` is an isomorphism.
* `projectiveCompletionVectorBundleImmersion`: `j : E ⟶ P`.
* `isOpenImmersion_projectiveCompletionVectorBundleImmersion`,
  `projectiveCompletionVectorBundleImmersion_comp_projectiveCompletionProj`,
  `range_pointsMap_projectiveCompletionVectorBundleImmersion_eq_compl_zeroScheme`.

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

/-- **The affine part `U = P ∖ D` of the projective completion is the vector bundle**: the
morphism `ψ : U ⟶ E` is an isomorphism (Stacks 0ERW, proof). -/
instance isIso_projectiveCompletionAffinePartToVectorBundle :
    IsIso (projectiveCompletionAffinePartToVectorBundle' E hr) :=
  isIso_projectiveCompletionAffinePartToVectorBundle_of_forall_chart E hr
    (fun _ m _ _ _ e => by
      classical
      exact isIso_toScheme_map_projectiveCompletionAffinePartChartToVectorBundleChart E hr m e)

/-- **The open immersion `j : E ⟶ P = 𝐏(ℰ ⊕ 𝒪_X)` of the vector bundle into its projective
completion**: the inverse of `ψ : U ⟶ E` followed by the inclusion of the affine part. -/
def projectiveCompletionVectorBundleImmersion :
    (vectorBundle B S hS X E).obj.left ⟶ projectiveCompletion E hr :=
  projectiveCompletionVectorBundleImmersionOfIsIso E hr
    (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E hr)

/-- **`j` lies over `X`**: `π ∘ j = p`. -/
@[reassoc]
theorem projectiveCompletionVectorBundleImmersion_comp_projectiveCompletionProj :
    projectiveCompletionVectorBundleImmersion E hr ≫ projectiveCompletionProj E hr =
      vectorBundleProjection B S hS X E :=
  projectiveCompletionVectorBundleImmersionOfIsIso_comp_projectiveCompletionProj E hr _

/-- **`j` is an open immersion.** -/
theorem isOpenImmersion_projectiveCompletionVectorBundleImmersion :
    IsOpenImmersion B S hS (projectiveCompletionVectorBundleImmersion E hr).hom :=
  isOpenImmersion_projectiveCompletionVectorBundleImmersionOfIsIso E hr _

/-- **The image of `j : E ⟶ P` is the complement of the zero scheme `D = Z(s)`.** -/
theorem range_pointsMap_projectiveCompletionVectorBundleImmersion_eq_compl_zeroScheme :
    Set.range (pointsMap B S hS _ (projectiveCompletionVectorBundleImmersion E hr).hom) =
      (Set.range (pointsMap B S hS _ (zeroScheme B S hS (projectiveCompletion E hr)
        (projectiveCompletionTwist E hr).obj (projectiveCompletionSection E hr)).1.ι))ᶜ :=
  range_pointsMap_projectiveCompletionVectorBundleImmersionOfIsIso_eq_compl_zeroScheme E hr _

end AlgebraicGeometry.Space

end
