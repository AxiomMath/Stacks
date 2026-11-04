module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ph sheaf condition for `π_S⁻¹F`, from descent along proper surjections

Let `F` be a sheaf of sets on the small étale site of `S`. By
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf`, `π_S⁻¹F` is a
ph sheaf as soon as it satisfies descent along every proper surjective morphism of the big ph
category over `S`. That remaining half of Stacks 0DDW, the equalizer diagram of its proof, is
deduced here from effective descent of small étale sheaves along proper surjections, Stacks 0GF0,
taken as the single named hypothesis.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isProperSurjectiveSheaf_of_descent` — the
  proper-surjective half of the ph sheaf condition, from effective descent along proper
  surjections.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_descent` — Stacks 0DDW, with the
  conclusion of Stacks 0GF0 as the single hypothesis.

## Implementation notes

Full faithfulness of the descent functor along `V ⟶ U` at the pair (terminal sheaf, `F|_U`) is
the sheaf condition, along that one arrow, of the presheaf of morphisms between their
restrictions, and that presheaf is `π_S⁻¹F`:
`AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence`.

## References

* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Descent along proper surjections gives the proper-surjective half of the ph sheaf
condition.** If descent of small étale sheaves along every proper surjective morphism of the
underlying category is effective (Stacks 0GF0), then `π_S⁻¹F` satisfies descent along every
proper surjective morphism of the big ph category over `S`: this is the equalizer diagram of the
proof of Stacks 0DDW, by
`AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence`. -/
@[sga "1 XIII 1.11" "special case"]
public theorem smallEtaleInverseImage_isProperSurjectiveSheaf_of_descent
    (h0GF0 : ∀ {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
      [Surjective ((phAssociatedBigEtaleSite B).inclusion.map f)]
      [IsProper ((phAssociatedBigEtaleSite B).inclusion.map f)],
      (smallEtaleSheafDescentFunctor (phAssociatedBigEtaleSite B) f).IsEquivalence) :
    IsProperSurjectiveSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X Y f hp hs
  rw [Presieve.ofArrows_pUnit]
  exact isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence (phAssociatedBigEtaleSite B)
    ((phAssociatedBigEtaleSite B).obj S hS) F f (@h0GF0 _ _ f.left hs hp)

/-- **Stacks 0DDW, granted effective descent along proper surjections (Stacks 0GF0).** For a sheaf
of sets `F` on the small étale site of `S`, the rule `X ↦ Γ(X_ét, f_X⁻¹F)` — the presheaf
underlying `π_S⁻¹F`, by `AlgebraicGeometry.etaleInverseImageSectionsIso` — is a sheaf for the
ph topology of the big ph category over `S`, and the unit of `ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an
isomorphism, so the ph sheaf is `ε_S⁻¹π_S⁻¹F`. That `π_S⁻¹F` is a sheaf for the étale topology,
and is the rule on the big étale site, holds by construction and by Stacks 09XN.

The single input `h0GF0` is the conclusion of Stacks 0GF0 on the underlying category of the
site. -/
public theorem smallEtaleInverseImage_isSheaf_ph_of_descent
    (h0GF0 : ∀ {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
      [Surjective ((phAssociatedBigEtaleSite B).inclusion.map f)]
      [IsProper ((phAssociatedBigEtaleSite B).inclusion.map f)],
      (smallEtaleSheafDescentFunctor (phAssociatedBigEtaleSite B) f).IsEquivalence) :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((phToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  have h := smallEtaleInverseImage_isProperSurjectiveSheaf_of_descent B S hS F h0GF0
  ⟨smallEtaleInverseImage_isSheaf_ph_of_isProperSurjectiveSheaf B S hS F h,
    smallEtaleInverseImage_isIso_phToBigEtale_unit_app_of_properSurjective B S hS F h⟩

end AlgebraicGeometry

end
