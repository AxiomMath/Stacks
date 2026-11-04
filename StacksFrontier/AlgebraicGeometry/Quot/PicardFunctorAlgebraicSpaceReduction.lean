module

public import StacksFrontier.AlgebraicGeometry.Quot.AlgebraicSpaceOverDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSectionTransportCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.StructureSheafMapIsoBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.StructureSheafMapIsoSurjective

/-!
# Stacks 0D2C, reduced to the representability of `Picardstack_{X/X ×_B X, Δ}`

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` of finite presentation (the standing
data `D` of Situation 08KB), flat, with `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every scheme `T` over `B`.
This file assembles the proof of Stacks 0D2C from its two halves, **except for one input**:

* base change along `f` itself: `X' = X ×_B X ⟶ X` has the diagonal as a section
  (`AlgebraicGeometry.Space.CoherentSituation.diagonalSection`), satisfies the same hypothesis
  on structure sheaves
  (`AlgebraicGeometry.Space.CoherentSituation.structureSheafMapIso_baseChange`),
  and `Pic_{X'/X}` is `Pic_{X/B}` read over `X`
  (`AlgebraicGeometry.Space.CoherentSituation.picardFunctorBaseChangeIso`);
* `f` is surjective (`AlgebraicGeometry.Space.isSurjective_of_isIso_structureSharp`), flat and
  locally of finite presentation, so an algebraic space over `X` descends to one over `B`
  (`AlgebraicGeometry.Space.isAlgebraicSpaceOver_of_map`, through Stacks 04S6);
* with a section, `Pic` is an algebraic space as soon as the rigidified Picard stack is
  representable by an algebraic space
  (`AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace`,
  through Stacks 0D2B, 0D28 and 02ZX).

The input left as the hypothesis `hrep` of
`isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace` (in the namespace
`AlgebraicGeometry.Space.CoherentSituation`) is that `Picardstack_{X'/X, Δ}` is representable
by an algebraic space.  The source obtains it
from Stacks 0D04 (`Picardstack` is algebraic, for `X' ⟶ X` flat, of finite presentation and
proper), Stacks 0D2A and 05UM (`Picardstack_{X'/X, Δ}` is algebraic) and Stacks 04SZ (an
algebraic stack fibred in setoids, Stacks 0D2B, is an algebraic space).  Stacks 0D04 is not in
this development, and 05UM and 04SZ are stated here only for categories fibred in groupoids whose
hom-sets lie in the universe of the site, while the Picard stacks have hom-sets one universe up;
see `StacksFrontier/AlgebraicGeometry/Quot/PicardFunctorAlgebraicSpace.lean`.  So this carries no
`@[stacks 0D2C]` attribute.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- The diagonal `X ⟶ X ×_Y X`, a section of the base change `X ×_Y X ⟶ X` of `f` along
itself. -/
def diagonalSection :
    (D.baseChange D.f).toPicardSituation.base ⟶ (D.baseChange D.f).toPicardSituation.X :=
  ObjectProperty.homMk (pullback.lift (𝟙 D.X.1) (𝟙 D.X.1) rfl)

/-- The diagonal is a section of the base change of `f` along itself. -/
theorem diagonalSection_comp :
    D.diagonalSection ≫ (D.baseChange D.f).toPicardSituation.f = 𝟙 _ :=
  ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)

/-- **Stacks 0D2C, reduced to one input.**  Let `f : X ⟶ B` be flat and of finite presentation
with `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every scheme `T` over `B`.  If the rigidified Picard stack
`Picardstack_{X'/X, Δ}` of the base change `X' = X ×_B X ⟶ X`, rigidified along the diagonal, is
representable by an algebraic space, then `Pic_{X/B}` is an algebraic space over `B`.

The hypothesis `hrep` is what Stacks 0D04, 0D2A, 05UM and 04SZ give in the source (properness of
`f` enters only there); it is not proved in this development. -/
theorem isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace
    (hflat : IsFlat B S hS D.f.hom) (hstr : D.toPicardSituation.StructureSheafMapIso)
    (hrep : IsRepresentableByAlgebraicSpace B S hS
      (sectionedPicardCFG (modulePushforwardCoherence B S hS)
        (sectionTransportCoherence (modulePushforwardCoherence B S hS) D.diagonalSection
          D.diagonalSection_comp))) :
    IsAlgebraicSpaceOver D.toPicardSituation.picardFunctor := by
  have hstr' := D.structureSheafMapIso_baseChange D.f hstr
  have h₁ : IsAlgebraicSpaceOver (D.baseChange D.f).toPicardSituation.picardFunctor :=
    Space.isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace _ _ hstr' hrep
  obtain ⟨H', p', ⟨c⟩⟩ := h₁.of_iso (D.picardFunctorBaseChangeIso D.f)
  exact isAlgebraicSpaceOver_of_map D.f p' c hflat D.finitePresentation.1
    (isSurjective_of_isIso_structureSharp D.f hstr) D.toPicardSituation.isSheaf_picardFunctor

end AlgebraicGeometry.Space.CoherentSituation

end
