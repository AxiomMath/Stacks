module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRestrictBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NonemptyChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus

/-!
# The two sides of the triangle of Stacks 06CL, in the site of the base

The first three steps of the proof of **Stacks 06CL** apply Stacks 05X8 and Stacks 06CE to the
relative map `x_α : Z ⟶ X_y` of Stacks 06CK attached to an object `Ξ = (U, Z, y, x, α)` of
`ℋ_d(𝒳/𝒴)`, read in the big fppf site of `U` over its terminal object. That needs five
properties: the structure morphism `Z ⟶ U` of the cover must be flat, locally of finite
presentation and closed, and the structure morphism `X_y ⟶ U` must be flat and locally of finite
presentation.

The first three come from the cover of a quintuple being finite locally free of degree `d` as a
morphism of *schemes*: a finite locally free morphism of schemes is flat, locally of finite
presentation and proper (Stacks 02KB), each of the first two conditions is étale local on the
source and target, and a proper morphism is closed on points. The last two are the standing
hypotheses of the source's section, which are imposed on the 1-morphism `F` through the structural
morphism of Stacks 04SG; this file reads them in the big fppf site of `U`.

## Main results

* `CategoryTheory.Over.left_eqToHom_conj`: the underlying morphism of a morphism of a slice
  conjugated by identifications of its source and of its target.
* `AlgebraicGeometry.Stack.eq_toYonedaId`: a morphism to the representable presheaf of the
  terminal object of a slice is the structural morphism.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.isFlat_coverToBase`,
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.isLocallyOfFinitePresentation_coverToBase` and
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.isClosedMorphism_coverToBase`: **the cover of a
  quintuple is flat, locally of finite presentation and closed over the base.**
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.yonedaMap_coverToBase_eq`: the structure morphism
  of the cover is the structural morphism of its representable presheaf to the terminal object of
  the site of the base.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.isFlat_toYonedaId_coverOver`,
  `...isLocallyOfFinitePresentation_toYonedaId_coverOver` and
  `...isClosedMorphism_toYonedaId_coverOver`: the same three conditions, read on that structural
  morphism, which is the form the locus argument consumes.

## Implementation notes

The structure morphism of the cover is read twice: as a morphism `Z ⟶ U` of the big fppf site of
`S`, which is where the quintuple records its finite local freeness, and as a morphism
`Object.coverOver ⟶ Object.baseOver` of the big fppf site of `U`, which is where the locus
argument runs. The two have the same underlying morphism of schemes, by definition of
`AlgebraicGeometry.Stack.FiniteHilbert.Object.coverToBase`, so the transfer costs nothing, and the
finite local freeness of the quintuple's cover is the hypothesis of Stacks 02KB on the nose.

The last two of the five properties are read off the structural morphism of Stacks 04SG by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff`, which says that condition
does not depend on which of the two bases it is taken over.

Any two morphisms to the representable presheaf of the terminal object of a slice agree, so the
structural morphism of a presheaf there is unique; that is what identifies the three morphisms the
locus argument consumes with the ones whose properties are established here, and what makes the
compatibility condition of a base change over that presheaf automatic.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace CategoryTheory.Over

/-- **The underlying morphism of a morphism of a slice category conjugated by identifications of
its source and of its target.** It is the underlying morphism itself, preceded by the
identification of the sources; the identifications of the targets cancel, both targets being
identified with the same object. -/
theorem left_eqToHom_conj {C : Type*} [Category C] {X : C} {a b c d e : Over X}
    (hab : a = b) (f : b ⟶ c) (hcd : c = d) (hde : d = e) :
    ((eqToHom hab ≫ f ≫ eqToHom hcd) ≫ eqToHom hde).left =
      eqToHom (congrArg Over.left hab) ≫ f.left ≫
        eqToHom (congrArg Over.left (hcd.trans hde)) := by
  cases hab
  cases hcd
  cases hde
  simp

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

/-! ### Morphisms to the representable presheaf of the terminal object -/

/-- **A morphism to the representable presheaf of the terminal object of a slice is unique.** It
is therefore the structural morphism `AlgebraicGeometry.Space.toYonedaId`. -/
theorem eq_toYonedaId (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)
    {X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hW)))) :
    f = Space.toYonedaId B W hW X := by
  ext Z x
  exact (OverShriek.subsingleton_yoneda_obj_mkId Z).elim _ _

namespace FiniteHilbert

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-! ### The cover of a quintuple over its base -/

variable (P : Object B S hS 𝒳 𝒴 F d)

/-- **The cover of a quintuple is finite locally free of degree `d` over its base**, read in the
big fppf site of the base. -/
theorem Object.isFiniteLocallyFreeOfRank_coverToBase :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B P.U.left.1 P.U.left.2).map P.coverToBase) d :=
  P.finiteLocallyFree

/-- **The cover of a quintuple is flat over its base**: it is finite locally free as a morphism of
schemes, hence flat by Stacks 02KB, and flatness is étale local on the source and target. -/
theorem Object.isFlat_coverToBase :
    Space.IsFlat B P.U.left.1 P.U.left.2 (yoneda.map P.coverToBase) :=
  have := P.isFiniteLocallyFreeOfRank_coverToBase
  Space.isFlat_yoneda_map B P.U.left.1 P.U.left.2 P.coverToBase
    (Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank _ d)

/-- **The cover of a quintuple is locally of finite presentation over its base**: it is finite
locally free as a morphism of schemes, hence locally of finite presentation by Stacks 02KB, and
that condition is étale local on the source and target. -/
theorem Object.isLocallyOfFinitePresentation_coverToBase :
    Space.IsLocallyOfFinitePresentation B P.U.left.1 P.U.left.2 (yoneda.map P.coverToBase) :=
  have := P.isFiniteLocallyFreeOfRank_coverToBase
  have := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((BigFppfOver.toScheme B P.U.left.1 P.U.left.2).map P.coverToBase) d
  Space.isLocallyOfFinitePresentation_yoneda_map B P.U.left.1 P.U.left.2 P.coverToBase
    (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation _)

/-- **The cover of a quintuple is closed over its base**: it is finite locally free as a morphism
of schemes, hence proper, hence a closed map on underlying topological spaces, and on a
representable morphism the points of Stacks 03BU are the points of the representing scheme. -/
theorem Object.isClosedMorphism_coverToBase :
    Space.IsClosedMorphism B P.U.left.1 P.U.left.2 (yoneda.map P.coverToBase) := by
  have := P.isFiniteLocallyFreeOfRank_coverToBase
  have hproper : IsProper
      ((BigFppfOver.toScheme B P.U.left.1 P.U.left.2).map P.coverToBase) :=
    Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank _ d
  have _ : UniversallyClosed
      ((BigFppfOver.toScheme B P.U.left.1 P.U.left.2).map P.coverToBase) :=
    have := hproper
    inferInstance
  exact (Space.isClosedMap_pointsMap_yoneda_iff B P.U.left.1 P.U.left.2 P.coverToBase).mpr
    (Scheme.Hom.isClosedMap _)

/-- The structure morphism of the cover of a quintuple, read in the big fppf site of the base, is
the structural morphism of its representable presheaf to the terminal object of that site. -/
theorem Object.yonedaMap_coverToBase_eq :
    yoneda.map P.coverToBase =
      Space.toYonedaId B P.U.left.1 P.U.left.2 (yoneda.obj P.coverOver) :=
  eq_toYonedaId B P.U.left.1 P.U.left.2 (yoneda.map P.coverToBase)

/-- **The cover of a quintuple is flat over the terminal object of the big fppf site of its
base.** -/
theorem Object.isFlat_toYonedaId_coverOver :
    Space.IsFlat B P.U.left.1 P.U.left.2
      (Space.toYonedaId B P.U.left.1 P.U.left.2 (yoneda.obj P.coverOver)) := by
  rw [← P.yonedaMap_coverToBase_eq]
  exact P.isFlat_coverToBase

/-- **The cover of a quintuple is locally of finite presentation over the terminal object of the
big fppf site of its base.** -/
theorem Object.isLocallyOfFinitePresentation_toYonedaId_coverOver :
    Space.IsLocallyOfFinitePresentation B P.U.left.1 P.U.left.2
      (Space.toYonedaId B P.U.left.1 P.U.left.2 (yoneda.obj P.coverOver)) := by
  rw [← P.yonedaMap_coverToBase_eq]
  exact P.isLocallyOfFinitePresentation_coverToBase

/-- **The cover of a quintuple is closed over the terminal object of the big fppf site of its
base.** -/
theorem Object.isClosedMorphism_toYonedaId_coverOver :
    Space.IsClosedMorphism B P.U.left.1 P.U.left.2
      (Space.toYonedaId B P.U.left.1 P.U.left.2 (yoneda.obj P.coverOver)) := by
  rw [← P.yonedaMap_coverToBase_eq]
  exact P.isClosedMorphism_coverToBase

end FiniteHilbert

end AlgebraicGeometry.Stack

end
