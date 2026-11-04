module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Separatedness supplied by finiteness, by integrality, or by an affine étale chart

Separatedness of a morphism of algebraic spaces over a scheme `S` is a property of its relative
diagonal (Tag 03HL), about which `AlgebraicGeometry.Space.IsEtale` says nothing. This file shows
that a morphism of algebraic spaces is separated when it is finite, or integral, in the sense of
Tag 03ZP, and when it is étale from an object of the site whose underlying scheme is affine.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isIntegralHom`: an integral morphism of algebraic spaces
  over `S` is separated.
* `AlgebraicGeometry.Space.isSeparated_of_isFinite`: a finite morphism of algebraic spaces over `S`
  is separated.
* `AlgebraicGeometry.Space.isSeparated_of_isEtale_of_isAffine`: an étale morphism to an algebraic
  space over `S` from an object of the site with affine underlying scheme is separated.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 01KN](https://stacks.math.columbia.edu/tag/01KN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A relatively representable morphism whose pullback to schemes lies in a class `P` of
separated morphisms is separated. -/
private theorem isSeparated_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ @_root_.AlgebraicGeometry.IsSeparated) (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hpres : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsSeparated B S hS f :=
  (isSeparated_iff_presheaf B S hS f hX hY hrep).2
    (MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ _ hg => hP _ hg) f hpres)

/-- An integral morphism of algebraic spaces over `S` is separated. -/
theorem isSeparated_of_isIntegralHom (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsIntegralHom B S hS f) : IsSeparated B S hS f := by
  obtain ⟨hrep, hpres⟩ := (isIntegralHom_iff_representable B S hS f hX hY).1 hf
  exact isSeparated_of_presheaf B S hS (fun _ _ _ (_ : _root_.AlgebraicGeometry.IsIntegralHom _) =>
    inferInstance) f hX hY hrep hpres

/-- A finite morphism of algebraic spaces over `S` is separated. -/
theorem isSeparated_of_isFinite (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFinite B S hS f) : IsSeparated B S hS f := by
  obtain ⟨hrep, hpres⟩ := (isFinite_iff_representable B S hS f hX hY).1 hf
  exact isSeparated_of_presheaf B S hS (fun _ _ _ (_ : _root_.AlgebraicGeometry.IsFinite _) =>
    inferInstance) f hX hY hrep hpres

/-- An étale morphism to an algebraic space over `S` from an object of the site with affine
underlying scheme is separated. -/
theorem isSeparated_of_isEtale_of_isAffine
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : yoneda.obj U ⟶ X) (hf : IsEtale B S hS f) : IsSeparated B S hS f :=
  isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX U
    (by let _ := hU; infer_instance) f hf

end AlgebraicGeometry.Space

end
