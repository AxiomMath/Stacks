module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheafProperBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The ph sheaf condition for `π_S⁻¹F`: Stacks 0DDW

Let `B` be a chosen big ph site, `S` one of its schemes and `F` a sheaf of sets on the small étale
site of `S`. `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_of_properBaseChange` deduces
Stacks 0DDW from the proper base change theorem in degree zero for sheaves of sets, Stacks 0A3U,
through effective descent of small étale sheaves along proper surjections (Stacks 0GF0). Stacks
0A3U is proved, `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`, and this file
records the resulting statement of Stacks 0DDW.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph_and_isIso_unit` — **Stacks 0DDW**: `π_S⁻¹F`
  is a ph sheaf, and it is `ε_S⁻¹π_S⁻¹F`.

## Implementation notes

The rule `X ↦ Γ(X_ét, f_X⁻¹F)` of the source is the presheaf underlying `π_S⁻¹F` by the sections
formula `AlgebraicGeometry.etaleInverseImageSectionsIso`, and that it is a sheaf on the big étale
site is Stacks 09XN; the statement below is about `π_S⁻¹F` itself. The source's argument takes
stalks at geometric points and uses the proper base change computation of the stalk of a
pushforward, Stacks 0A3T; the route here uses the same input, proper base change in degree zero,
through descent of small étale sheaves along the proper surjection.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0DBQ](https://stacks.math.columbia.edu/tag/0DBQ)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) S hS) (Type (u + 1)))

/-- **Stacks 0DDW.** For a sheaf of sets `F` on the small étale site of `S`, the rule
`(f : X ⟶ S) ↦ Γ(X_ét, f⁻¹F)` — the presheaf underlying `π_S⁻¹F` on the big étale category over
`S`, by the sections formula `AlgebraicGeometry.etaleInverseImageSectionsIso` and Stacks 09XN —
is a sheaf for the ph topology of the big ph category over `S`, and the unit of
`ε_S⁻¹ ⊣ ε_{S,*}` at `π_S⁻¹F` is an isomorphism, so that this ph sheaf is `ε_S⁻¹π_S⁻¹F`.

By Stacks 0DBQ the ph sheaf condition splits into its Zariski half and descent along proper
surjections; the latter follows from the proper base change theorem in degree zero, Stacks 0A3U,
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`. -/
@[stacks 0DDW]
public theorem smallEtaleInverseImage_isSheaf_ph_and_isIso_unit :
    Presieve.IsSheaf (BigPHOver.topology B S hS)
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj
          F).obj ∧
      IsIso ((phToBigEtaleMorphism B (B.obj S hS)).adj.unit.app
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) S hS).inverseImage.obj F)) :=
  smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B S hS F fun f g g' f' sq hf =>
    have := hf
    Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq

end AlgebraicGeometry

end
