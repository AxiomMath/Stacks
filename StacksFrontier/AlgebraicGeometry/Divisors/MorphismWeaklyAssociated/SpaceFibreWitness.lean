module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreRefinement

/-!
# A fibre witness above a prescribed point, for algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be a
quasi-coherent `𝒪_X`-module and let `x` be a point of the relative weak assassin
`WeakAss_{X/Y}(F)`. For any morphism `g : Y' ⟶ Y` and any point `y'` of `Y'` above the image of
`x` in `Y`, there is a field-valued representative `q` of `y'` such that `x` is witnessed on the
fibre of `f` over the image of `q` in `Y`: some point of that fibre above `x` is weakly
associated to the restriction of `F`.

This is the algebraic space form of the step the source takes through Divisors, Lemma 31.7.3
(Stacks 05DC): for schemes one passes to a generic point of
`Spec(κ(y') ⊗_{κ(y)} κ(x))`. Here the given witness, over some representative `p` of the image
of `x`, is moved to a representative of `y'` which refines `p`.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq`:
  a point of `WeakAss_{X/Y}(F)` is witnessed on the fibre over the image of some field-valued
  representative of any prescribed point of `Y'` above its image.

## Implementation notes

A point of `Y'` above the class of `p` is the class of a field-valued point `q` refining `p`
through `g`, by `AlgebraicGeometry.Space.exists_fieldValuedPoint_refining`. The fibre of `f`
over the image of `q` is then the base change of the fibre over `p` along a morphism of spectra
of fields, which is flat and surjective, and weak association ascends along it by
`AlgebraicGeometry.Space.isWeaklyAssociatedOnFibre_of_refines`; that ascent is proved by étale
localization onto a chart, where it is Stacks 05F0 at a generic point of the nonempty fibre.

The module universe is that of the structure rings, since Stacks 0CUU is available there.

## References

* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Y' : AlgebraicSpaces B S hS}

/-- **A fibre witness above a prescribed point.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `x` lie in the relative weak
assassin `WeakAss_{X/Y}(F)`. For a morphism `g : Y' ⟶ Y` and a point `y'` of `Y'` whose image
in `Y` is the image of `x`, some field-valued representative `q` of `y'` has the property that
a point of the fibre of `f` over the image of `q` in `Y`, lying above `x`, is weakly associated
to the restriction of `F` to that fibre.

This is what the source obtains from a generic point of `Spec(κ(y') ⊗_{κ(y)} κ(x))` by
Stacks 05DC, for schemes. -/
theorem exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    {x : points B S hS X.1} (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x) (g : Y' ⟶ Y)
    {y' : points B S hS Y'.1}
    (hy' : pointsMap B S hS Y'.1 g.hom y' = pointsMap B S hS X.1 f.hom x) :
    ∃ q : FieldValuedPoint B S hS Y'.1,
      q.class B S hS Y'.1 = y' ∧
        IsWeaklyAssociatedOnFibre B S hS f F (FieldValuedPoint.map B S hS Y'.1 g.hom q) x := by
  obtain ⟨p, hp, hfib⟩ := hx
  obtain ⟨q, κ, hq, hκ⟩ := exists_fieldValuedPoint_refining B S hS g p (hp.trans hy'.symm)
  exact ⟨q, hq, isWeaklyAssociatedOnFibre_of_refines B S hS f F hF
    (p := p) (q := FieldValuedPoint.map B S hS Y'.1 g.hom q) κ hκ hfib⟩

end AlgebraicGeometry.Space

end
