module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroSeparatedScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase

/-!
# A zero-dimensional space locally of finite type over a field of the base is a scheme

**Stacks 06LZ** at condition (2) says that an algebraic space of dimension zero which is locally
of finite type over a field is a scheme. The field there is an *absolute* datum: the morphism
tested is a morphism `X ⟶ Spec(k)` of algebraic spaces over the terminal scheme `Spec ℤ`, and
that is the shape in which
`AlgebraicGeometry.Space.isRepresentable_of_isLocallyOfFiniteType_over_field` is stated.

Over a base scheme `S` the field is instead given by a morphism `X ⟶ h_K` of presheaves on the
big fppf site of `S`, with `K` an object of that site whose underlying scheme is the spectrum of
a field. This file states the tag at that datum.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isLocallyOfFiniteType_over_field_of_base`:
  **Stacks 06LZ at condition (2) with the field-valued morphism given over `S`.**
* `AlgebraicGeometry.Space.dimension_eq_zero_of_dimension_le_zero`: an algebraic space of
  dimension at most zero with a point has dimension zero.

## Implementation notes

The dimension of **Stacks 04N6** is a supremum in `WithBot ℕ∞`, so the dimension of the empty
space is `⊥` and `dim X ≤ 0` is the unconditional form of zero-dimensionality; the `= 0` form
that **Stacks 06LZ** is stated at needs a point, which is
`AlgebraicGeometry.Space.dimension_eq_zero_of_dimension_le_zero`.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An algebraic space of dimension at most zero which has a point has dimension zero. -/
theorem dimension_eq_zero_of_dimension_le_zero (hX : IsAlgebraicSpace B S hS X)
    (hdim : dimension B S hS X hX ≤ 0) (hne : Nonempty (points B S hS X)) :
    dimension B S hS X hX = 0 :=
  le_antisymm hdim (le_iSup_of_le hne.some (zero_le_dimensionAtPoint B S hS hX _))

/-- **Stacks 06LZ, case (2): `X` is a scheme, with the field read on the base site.** An
algebraic space over `S` of dimension zero which is locally of finite type over an object `K`
of the big fppf site of `S` whose underlying scheme is the spectrum of a field is
representable. -/
theorem isRepresentable_of_isLocallyOfFiniteType_over_field_of_base
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) {k : Type u} [Field k] {K : BigFppfOver B S hS}
    (eK : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (.of k))
    {m : X ⟶ yoneda.obj K} (hm : IsLocallyOfFiniteType B S hS m)
    (hdim : dimension B S hS X hX = 0) : X.IsRepresentable := by
  set g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩ with hg
  refine isRepresentable_of_isLocallyOfFiniteType_over_field B S hS hZ hX
    (K := (Over.map g).obj K) eK
    (f := (relocalizePresheafFunctor g).map m ≫
      (relocalizedYonedaIso B (B.obj hS) (B.obj hZ) g K).hom) ?_ hdim
  exact (Space.holdsOnEveryEtaleChart_comp_iso_iff B (⊤_ Scheme.{u}) hZ
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) _ _).2
    ((Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S (⊤_ Scheme.{u}) hS hZ g
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) m).2 hm)

end AlgebraicGeometry.Space

end
