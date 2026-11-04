module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.LimitObjectPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.RestrictionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Existence

/-!
# Grothendieck's existence theorem, derived form

**[Stacks, Tag 0DIG].** In Situation [Stacks, Tag 0DIB] there exists a pseudo-coherent `K` in
`D(𝒪_X)` such that `Kₙ = K ⊗ᴸ_{𝒪_X} 𝒪_{Xₙ}` for all `n`, compatibly with the maps `φₙ`.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.`
  `exists_isPseudoCoherent_derivedPullback_iso`: **[Stacks, Tag 0DIG].**

## Implementation notes

The proof is the source's. `K` is the object `DQ_X(R lim R(iₙ)_* Kₙ)` of [Stacks, Tag 0DIC]
(`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`), with its
projections `πₙ : K ⟶ R(iₙ)_* Kₙ` compatible with the tower of derived direct images
(`limitProjection_comp_towerTransition`). It is pseudo-coherent by [Stacks, Tag 0DIE]
(`isPseudoCoherent_limitObject`), and the adjoint `L(iₙ)^* K ⟶ Kₙ` of `πₙ` is an isomorphism by
[Stacks, Tag 0DIF] on affine opens (`isIso_restrictionMap`). The compatibility of these
isomorphisms with the `φₙ` is formal: it is
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.`
`exists_derivedPullback_iso_of_isIso`.

The derived tensor product `K ⊗ᴸ_{𝒪_X} 𝒪_{Xₙ}`, an object on the closed subscheme `Xₙ`, is the
derived pullback `L(iₙ)^* K` along the closed immersion `iₙ : Xₙ ⟶ X`, the reading Situation 0DIB
gives the derived restriction in `φₙ`. Compatibility with `φₙ` is the commutativity of
`L(jₙ)^* L(iₙ₊₁)^* K ≅ L(iₙ)^* K ⟶ Kₙ` with `L(jₙ)^* L(iₙ₊₁)^* K ⟶ L(jₙ)^* Kₙ₊₁ ⟶ Kₙ`, the first
isomorphism being the composition isomorphism of derived pullbacks along `iₙ₊₁ ∘ jₙ = iₙ`.

As in Situation 0DIB the derived categories are taken at the standard model.

## References

* [Stacks Project, Tag 0DIG](https://stacks.math.columbia.edu/tag/0DIG)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
* [Stacks Project, Tag 0DIE](https://stacks.math.columbia.edu/tag/0DIE)
* [Stacks Project, Tag 0DIF](https://stacks.math.columbia.edu/tag/0DIF)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})

/-- **[Stacks, Tag 0DIG], Grothendieck's existence theorem in its derived form.** In Situation
[Stacks, Tag 0DIB] there is a pseudo-coherent `K ∈ D(𝒪_X)` together with isomorphisms
`βₙ : K ⊗ᴸ_{𝒪_X} 𝒪_{Xₙ} = L(iₙ)^* K ≅ Kₙ` compatible with the maps `φₙ`: the composite
`L(jₙ)^* L(iₙ₊₁)^* K ≅ L(iₙ)^* K ⟶ Kₙ` of the composition isomorphism with `βₙ` is
`L(jₙ)^* βₙ₊₁` followed by `φₙ`. -/
@[stacks 0DIG]
theorem exists_isPseudoCoherent_derivedPullback_iso :
    ∃ K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} S.X.left.toRingedSpace),
      RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) K ∧
        ∃ β : ∀ n : ℕ, (derivedPullback (S.levelInclusion n)).obj K ≅ S.K n,
          ∀ n : ℕ,
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
                (S.levelTransition n) (S.levelInclusion (n + 1))).hom.app K ≫
              eqToHom (congrArg (fun t : (schemeAt S.system S.X n).toRingedSpace ⟶
                  S.X.left.toRingedSpace => (derivedPullback t).obj K)
                (S.levelTransition_comp_levelInclusion n)) ≫ (β n).hom =
            (derivedPullback (S.levelTransition n)).map (β (n + 1)).hom ≫ S.φ n :=
  S.exists_derivedPullback_iso_of_isIso S.limitObject S.isPseudoCoherent_limitObject
    S.limitProjection
    S.limitProjection_comp_towerTransition S.isIso_restrictionMap

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation
