module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation

/-!
# The identity of an algebraic space is flat and locally of finite presentation

An identity morphism of algebraic spaces over `S` is flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isFlat_id`: an identity morphism of algebraic spaces is flat.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_id`: an identity morphism of algebraic
  spaces is locally of finite presentation.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An identity morphism of algebraic spaces over `S` is flat. -/
theorem isFlat_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : IsFlat B S hS (𝟙 X) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
    Flat.isEtaleLocalOnSourceAndTarget hX hX (𝟙 X)).mpr ?_
  refine ⟨U, U, a, a, 𝟙 U, haEtale, haEtale, haSurj, by simp, ?_⟩
  simp only [CategoryTheory.Functor.map_id]
  infer_instance

/-- An identity morphism of algebraic spaces over `S` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : IsLocallyOfFinitePresentation B S hS (𝟙 X) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hX hX (𝟙 X)).mpr ?_
  refine ⟨U, U, a, a, 𝟙 U, haEtale, haEtale, haSurj, by simp, ?_⟩
  simp only [CategoryTheory.Functor.map_id]
  infer_instance

end AlgebraicGeometry.Space

end
