module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentEtaleLocal
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonUnitFork

/-!
# A sheaf is the equalizer of its restrictions along a proper surjection (Stacks 0DFX)

Let `f : Y ⟶ X` be a surjective proper morphism of algebraic spaces over a scheme `S` and let
`F` be a sheaf on `X_étale`, here the spaces-étale site of `X`, whose topos is that of `X_étale`
(Stacks 03G1). Write `g : Y ×_X Y ⟶ X` for the structure morphism of the fibre product. Then
`F ⟶ f_* f⁻¹ F` is injective with image the equalizer of the two maps
`f_* f⁻¹ F ⇉ g_* g⁻¹ F` given by the two projections: the unit fork is a limit. This is Stacks
0DFX.

## Main results

* `AlgebraicGeometry.Space.nonempty_isLimit_unitFork_of_isProper_isSurjective` — **Stacks 0DFX**.

## Implementation notes

The restriction maps `f_* f⁻¹ F ⟶ g_* g⁻¹ F` are
`CategoryTheory.Pseudofunctor.unitForkRestriction` for the pseudofunctor of spaces-étale inverse
images, the chosen fibre product `AlgebraicGeometry.Space.spacesChosenPullback f f` and the
adjunctions `f⁻¹ ⊣ f_*` of `AlgebraicGeometry.Space.spacesEtalePseudofunctorAdjunction`. The limit
property is `CategoryTheory.Pseudofunctor.isLimitUnitFork`, from full faithfulness of descent
along `f`, which is `AlgebraicGeometry.Space.isPrestackFor_of_isProper_isSurjective`; its scheme
case `AlgebraicGeometry.Space.properSurjectivePrestackOverSchemes` comes from proper base change
in degree zero (Stacks 0A3U). The source proves the statement through the ph sheaf property of
`π_X⁻¹F` (Stacks 0DDW); full faithfulness of descent along `f` is the same input.

## References

* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Descent of spaces-étale sheaves along a surjective proper morphism of algebraic spaces is
fully faithful. -/
noncomputable def fullyFaithful_toDescentData_of_isProper_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hp : IsProper B S hS f.hom) (hs : IsSurjective B S hS f.hom) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit ↦ f)).FullyFaithful := by
  have hpre := isPrestackFor_of_isProper_isSurjective
    (properSurjectivePrestackOverSchemes B S hS) f hp hs
  rw [Sieve.ofArrows, Pseudofunctor.IsPrestackFor_generate_iff,
    Pseudofunctor.isPrestackFor_ofArrows_iff] at hpre
  exact hpre.some

/-- **Stacks 0DFX.** Let `f : Y ⟶ X` be a surjective proper morphism of algebraic spaces over
`S`, let `F` be a sheaf on `X_étale` (the spaces-étale site of `X`, Stacks 03G1), and let
`g : Y ×_X Y ⟶ X` be the structure morphism. Then `F ⟶ f_* f⁻¹ F` is injective with image the
equalizer of the two maps `f_* f⁻¹ F ⇉ g_* g⁻¹ F` induced by the two projections
`Y ×_X Y ⟶ Y`: the fork formed by the unit of `f⁻¹ ⊣ f_*` and these two maps is a limit. -/
@[stacks 0DFX]
theorem nonempty_isLimit_unitFork_of_isProper_isSurjective {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hs : IsSurjective B S hS f.hom) (hp : IsProper B S hS f.hom)
    (F : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) :
    Nonempty (IsLimit (Fork.ofι ((spacesEtalePseudofunctorAdjunction B S hS f).unit.app F)
      ((Pseudofunctor.unit_comp_unitForkRestriction _ f (spacesChosenPullback B S hS f f)
          (spacesEtalePseudofunctorAdjunction B S hS f)
          (spacesEtalePseudofunctorAdjunction B S hS (spacesChosenPullback B S hS f f).p)
          (spacesChosenPullback B S hS f f).p₁ (spacesChosenPullback B S hS f f).hp₁ F).trans
        (Pseudofunctor.unit_comp_unitForkRestriction _ f (spacesChosenPullback B S hS f f)
          (spacesEtalePseudofunctorAdjunction B S hS f)
          (spacesEtalePseudofunctorAdjunction B S hS (spacesChosenPullback B S hS f f).p)
          (spacesChosenPullback B S hS f f).p₂ (spacesChosenPullback B S hS f f).hp₂ F).symm) :
      Fork (Pseudofunctor.unitForkRestriction _ f (spacesChosenPullback B S hS f f)
          (spacesEtalePseudofunctorAdjunction B S hS f)
          (spacesEtalePseudofunctorAdjunction B S hS (spacesChosenPullback B S hS f f).p)
          (spacesChosenPullback B S hS f f).p₁ (spacesChosenPullback B S hS f f).hp₁ F)
        (Pseudofunctor.unitForkRestriction _ f (spacesChosenPullback B S hS f f)
          (spacesEtalePseudofunctorAdjunction B S hS f)
          (spacesEtalePseudofunctorAdjunction B S hS (spacesChosenPullback B S hS f f).p)
          (spacesChosenPullback B S hS f f).p₂ (spacesChosenPullback B S hS f f).hp₂ F))) :=
  ⟨Pseudofunctor.isLimitUnitFork _ f (spacesChosenPullback B S hS f f)
    (spacesEtalePseudofunctorAdjunction B S hS f)
    (spacesEtalePseudofunctorAdjunction B S hS (spacesChosenPullback B S hS f f).p)
    (fullyFaithful_toDescentData_of_isProper_isSurjective B S hS f hp hs) F⟩

end AlgebraicGeometry.Space

end
