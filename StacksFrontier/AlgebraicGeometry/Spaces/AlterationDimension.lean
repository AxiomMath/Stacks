module

public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDominantMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralGenericallyFinite

/-!
# An alteration does not raise the dimension

Let `f : Y ⟶ X` be an alteration of integral algebraic spaces over `S` with `X` locally
Noetherian.  Then `dim Y ≤ dim X`.  An alteration is quasi-finite at the generic point of `|Y|`
(Stacks 0ADB), so the transcendence degree of `f` at that point is zero (Stacks 0AD5, condition
(4) implies condition (1)), and the dimension inequality of Stacks 0EDC reads
`dim Y ≤ dim X + 0`.

## Main results

* `AlgebraicGeometry.Space.dimension_le_of_isAlteration`: `dim Y ≤ dim X` for an alteration
  `Y ⟶ X` with locally Noetherian target.

## References

* [Stacks Project, Tag 0EDC](https://stacks.math.columbia.edu/tag/0EDC)
* [Stacks Project, Tag 0ADB](https://stacks.math.columbia.edu/tag/0ADB)
* [Stacks Project, Tag 0AD5](https://stacks.math.columbia.edu/tag/0AD5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An alteration does not raise the dimension.**  For an alteration `f : Y ⟶ X` with `X`
locally Noetherian, `dim Y ≤ dim X`: the transcendence degree of `f` at the generic point of
`|Y|` is zero, `f` being quasi-finite there (Stacks 0ADB and 0AD5), and Stacks 0EDC bounds
`dim Y` by `dim X` plus that transcendence degree. -/
theorem dimension_le_of_isAlteration (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hXN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (f : Y ⟶ X) (hf : IsAlteration B S hS f) :
    dimension B S hS Y hY ≤ dimension B S hS X hX := by
  have hYint := hf.isIntegralSpace_source
  have hXint := hf.isIntegralSpace_target
  have hy := isGenericPoint_genericPoint B S hS hY hYint
  have hx := isGenericPoint_genericPoint B S hS hX hXint
  have hqf := (isAlteration_iff_isQuasiFiniteAt B S hS hY hX hYint hXint f hf.isProper
    hf.isDominant hy hx).1 hf
  let s : IntegralDominantMorphismSituation B S hS :=
    { source := Y
      target := X
      hom := f
      isAlgebraicSpace_source := hY
      isAlgebraicSpace_target := hX
      locallyNoetherian_target := hXN
      isIntegralSpace_source := hYint
      isIntegralSpace_target := hXint
      isDominant := hf.isDominant
      isLocallyOfFiniteType := hf.isProper.2.1.1
      sourcePoint := genericPoint B S hS hY hYint
      targetPoint := genericPoint B S hS hX hXint
      isGenericPoint_sourcePoint := hy
      isGenericPoint_targetPoint := hx }
  simpa using dimension_le_dimension_add_transcendenceDegree B S hS s 0
    (hasTranscendenceDegreeAt_zero_of_isQuasiFiniteAt B S hS hY hX f hqf)

end AlgebraicGeometry.Space

end
