module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentSectionsInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The h sheaf condition for `π_S⁻¹F`: Stacks 0EW8

Let `B` be a chosen big h site, `S` one of its schemes and `F` a sheaf of sets on the small étale
site of `S`. By
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf` (Stacks
0EU5 together with the Zariski half of Stacks 0EW8), `π_S⁻¹F` is an h sheaf as soon as it satisfies
descent along every proper surjective morphism of finite presentation of the big h category over
`S`. That descent holds: small étale sheaves descend effectively along a proper surjection by the
proper base change theorem in degree zero, Stacks 0A3U,
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`, through the theorem in the
namespace `AlgebraicGeometry`
`smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isProperFinitePresentationSheaf` — the proper half of
  the h sheaf condition for `π_S⁻¹F`.
* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_h_and_isIso_unit` — **Stacks 0EW8**: `π_S⁻¹F`
  is an h sheaf, and it is `ε_S⁻¹π_S⁻¹F`.

## Implementation notes

The source deduces Stacks 0EW8 from the ph statement Stacks 0DDW, an h covering being a ph
covering. The big h and big ph sites of this development are separate structures, so the
argument of Stacks 0DDW is repeated on the h site; finite presentation is not used.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **The proper half of the h sheaf condition for `π_S⁻¹F`.** For a sheaf of sets `F` on the
small étale site of `S`, `π_S⁻¹F` satisfies descent along every proper surjective morphism of
the big h category over `S`: small étale sheaves descend effectively along a proper surjection,
by the proper base change theorem in degree zero (Stacks 0A3U). Finite presentation is not
used. -/
public theorem smallEtaleInverseImage_isProperFinitePresentationSheaf :
    BigHOver.IsProperFinitePresentationSheaf B S hS
      ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
        F).obj := by
  intro X Y f hp hs _
  have : IsProper ((hAssociatedBigEtaleSite B).inclusion.map f.left) := hp
  have : Surjective ((hAssociatedBigEtaleSite B).inclusion.map f.left) := hs
  have hdesc : (smallEtaleSheafInverseImageDescentFunctor (hAssociatedBigEtaleSite B)
      f.left).IsEquivalence :=
    smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
      (hAssociatedBigEtaleSite B) f.left (fun f g g' f' sq hf =>
        have := hf
        Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
  exact isSheafFor_smallEtaleInverseImage_singleton_of_inverseImageDescent
    (hAssociatedBigEtaleSite B) ((hAssociatedBigEtaleSite B).obj S hS) F f hdesc

/-- **Stacks 0EW8.** For a sheaf of sets `F` on the small étale site of `S`, the rule
`(f : X ⟶ S) ↦ Γ(X_ét, f⁻¹F)` — the presheaf underlying `π_S⁻¹F` on the big étale category over
`S`, by the sections formula `AlgebraicGeometry.etaleInverseImageSectionsIso` and Stacks 09XN —
is a sheaf for the h topology of the big h category over `S`, and the unit of `ε_S⁻¹ ⊣ ε_{S,*}`
at `π_S⁻¹F` is an isomorphism, so that this h sheaf is `ε_S⁻¹π_S⁻¹F`.

The h sheaf condition is Stacks 0EU5: the Zariski half is
`AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_h` and the proper half is
`AlgebraicGeometry.smallEtaleInverseImage_isProperFinitePresentationSheaf`. -/
@[stacks 0EW8]
public theorem smallEtaleInverseImage_isSheaf_h_and_isIso_unit :
    Presieve.IsSheaf (BigHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((hToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  ⟨(isSheaf_iff_isSheaf_of_type _ _).mp
      (smallEtaleInverseImage_isSheaf_h_of_isProperFinitePresentationSheaf B S hS F
        (smallEtaleInverseImage_isProperFinitePresentationSheaf B S hS F)),
    smallEtaleInverseImage_isIso_hToBigEtale_unit_app_of_properFinitePresentation B S hS F
      (smallEtaleInverseImage_isProperFinitePresentationSheaf B S hS F)⟩

end AlgebraicGeometry

end
