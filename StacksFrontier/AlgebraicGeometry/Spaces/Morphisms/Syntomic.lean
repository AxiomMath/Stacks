module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic

/-!
# Permanence properties of syntomic morphisms of algebraic spaces

Syntomicity of a morphism of algebraic spaces over a scheme `S`, in the sense of Tag 03Z7, is
the condition of Tag 03MJ that the underlying scheme morphism of every commuting square of
étale scheme charts be syntomic. This file proves that a syntomic morphism of algebraic spaces
is flat and locally of finite presentation, and that the class of syntomic morphisms is stable
under composition and under base change.

The first two statements are implications between chart conditions and are proved chart by
chart from the corresponding statements about morphisms of schemes, Tags 01UK and 01UL.

Composition and base change go instead through the comparison of the every-chart condition of
Tag 03MJ with its one-surjective-chart form, which needs syntomicity of morphisms of *schemes*
to be étale local on the source and target in the sense of Tag 04QZ. That is Tag 04R3 for
syntomicity, proved here from the étale source-locality of syntomic morphisms of schemes,
`AlgebraicGeometry.Syntomic.isLocalAtSource_etalePrecoverage`.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSyntomic`: **Stacks 0DEY**.
* `AlgebraicGeometry.Space.isFlat_of_isSyntomic`: **Stacks 0DEZ**.
* `AlgebraicGeometry.Space.isSyntomic_iff_isFlat_and_isLocalCompleteIntersection`:
  **Stacks 06C9**.
* `AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, the syntomic
  case.
* `AlgebraicGeometry.Space.isSyntomic_comp`: **Stacks 03Z8**.
* `AlgebraicGeometry.Space.isSyntomic_isStableUnderBaseChange`: **Stacks 03Z9**.

## Implementation notes

Tags 0DEY, 0DEZ and 06C9 need no algebraic-space hypothesis: all three are implications between
chart conditions, proved chart by chart, so they hold for arbitrary morphisms of presheaves on
the big fppf site. Tags 03Z8 and 03Z9 do need them, because they pass through the comparison of
the every-chart condition with the one-surjective-chart condition of Tag 03MJ, which takes
atlases of the spaces involved.

Of the three conditions of Tag 04QZ for syntomicity, two are immediate. Étale base change is
the special case of arbitrary base change, which is Tag 01UI. Composition with an étale
morphism on either side preserves syntomicity, because an étale morphism of schemes is smooth
and hence syntomic (Tag 01VD) and syntomic morphisms compose (Tag 01UH); these two are
`AlgebraicGeometry.Syntomic.respectsLeft_etale` and
`AlgebraicGeometry.Syntomic.respectsRight_etale`. The third condition, the local criterion, is
supplied by `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource` from étale
source-locality, which is the syntomic case of Tag 02KM and is proved in
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource`.

Inside the namespace `AlgebraicGeometry.Space` the scheme-morphism class `Syntomic` and the two
scheme-level lemmas of Tags 01UK and 01UL are written with an explicit `_root_.`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Syntomic.lean`, because the unqualified names would be
read in the `Space` namespace.

## References

* [Stacks Project, Tag 01UH](https://stacks.math.columbia.edu/tag/01UH)
* [Stacks Project, Tag 01UI](https://stacks.math.columbia.edu/tag/01UI)
* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
* [Stacks Project, Tag 01VD](https://stacks.math.columbia.edu/tag/01VD)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03Z7](https://stacks.math.columbia.edu/tag/03Z7)
* [Stacks Project, Tag 03Z8](https://stacks.math.columbia.edu/tag/03Z8)
* [Stacks Project, Tag 03Z9](https://stacks.math.columbia.edu/tag/03Z9)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
* [Stacks Project, Tag 0DEY](https://stacks.math.columbia.edu/tag/0DEY)
* [Stacks Project, Tag 0DEZ](https://stacks.math.columbia.edu/tag/0DEZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04R3, syntomic case.** Being a syntomic morphism of schemes is étale
local on the source and target.

The geometric content of Tag 04R2 is not needed: postcomposition with an étale morphism
preserves syntomicity outright, by `AlgebraicGeometry.Syntomic.respectsRight_etale`, and base
change is Tag 01UI. The local criterion comes from étale source-locality of syntomic morphisms
of schemes, `AlgebraicGeometry.Syntomic.isLocalAtSource_etalePrecoverage`. -/
@[stacks 04R3 "syntomic"]
theorem syntomic_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Syntomic.{u} : MorphismProperty Scheme.{u}) :=
  let := Syntomic.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Flatness and local finite presentation -/

/-- **Stacks 0DEY.** A syntomic morphism of algebraic spaces over `S` is locally of finite
presentation.

Both properties are the condition of Tag 03MJ on every commuting square of étale charts, so the
statement is the scheme-level implication of [Stacks Project, Tag 01UK] quantified over the
charts. -/
@[stacks 0DEY]
theorem isLocallyOfFinitePresentation_of_isSyntomic {f : X ⟶ Y}
    (hf : IsSyntomic B S hS f) : IsLocallyOfFinitePresentation B S hS f :=
  fun U V a b h ha hb hsq =>
    _root_.AlgebraicGeometry.locallyOfFinitePresentation (hf U V a b h ha hb hsq)

/-- **Stacks 0DEZ.** A syntomic morphism of algebraic spaces over `S` is flat.

Both properties are the condition of Tag 03MJ on every commuting square of étale charts, so the
statement is the scheme-level implication of [Stacks Project, Tag 01UL] quantified over the
charts. -/
@[stacks 0DEZ]
theorem isFlat_of_isSyntomic {f : X ⟶ Y} (hf : IsSyntomic B S hS f) : IsFlat B S hS f :=
  fun U V a b h ha hb hsq => _root_.AlgebraicGeometry.flat (hf U V a b h ha hb hsq)

/-- **Stacks 06C9.** A morphism of algebraic spaces over `S` is syntomic if and only if it is
flat and a local complete intersection morphism.

All three properties are the condition of Tag 03MJ on every commuting square of étale charts, so
the statement is the scheme-level equivalence of Tag 069K quantified over the charts. -/
@[stacks 06C9]
theorem isSyntomic_iff_isFlat_and_isLocalCompleteIntersection (f : X ⟶ Y) :
    IsSyntomic B S hS f ↔ IsFlat B S hS f ∧ IsLocalCompleteIntersection B S hS f := by
  simp only [IsSyntomic, IsFlat, IsLocalCompleteIntersection, HoldsOnEveryEtaleChart,
    _root_.AlgebraicGeometry.syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism, forall_and]

/-! ### Composition and base change -/

/-- **Stacks 03Z8.** The composite of two syntomic morphisms of algebraic spaces over `S` is
syntomic.

Syntomicity of scheme morphisms is stable under composition ([Stacks Project, Tag 01UH]) and is
étale local on the source and target (Tag 04R3), so this is the instance of
[Stacks Project, Tag 0AML] at that property. -/
@[stacks 03Z8]
theorem isSyntomic_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSyntomic B S hS f) (hg : IsSyntomic B S hS g) :
    IsSyntomic B S hS (f ≫ g) :=
  holdsOnEveryEtaleChart_comp B S hS
    (@_root_.AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget hX hY hZ f g hf hg

/-- **Stacks 03Z9.** Syntomic morphisms of algebraic spaces over `S` are stable under base
change.

Syntomicity of scheme morphisms is stable under base change ([Stacks Project, Tag 01UI]) and is
étale local on the source and target (Tag 04R3), so this is the instance of
[Stacks Project, Tag 0AMM] at that property. -/
@[stacks 03Z9]
theorem isSyntomic_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSyntomic B S hS f.hom) :=
  holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS
    (@_root_.AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget

/-- **Stacks 06CP.** A smooth morphism of algebraic spaces over `S` is syntomic.

On each commuting square of étale charts the underlying morphism of schemes is smooth, hence
syntomic by `AlgebraicGeometry.syntomic_of_smooth`, which is Stacks 01VD. -/
@[stacks 06CP]
theorem isSyntomic_of_isSmooth (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    IsSyntomic B S hS f := fun U V a b h ha hb hcomm ↦
  @syntomic_of_smooth _ _ _ (hf U V a b h ha hb hcomm)

end Space

end AlgebraicGeometry

end
