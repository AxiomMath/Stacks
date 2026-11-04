module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
import all StacksFrontier.AlgebraicGeometry.Etale.GeometricallyIrreducibleFibres

/-!
# A morphism with one point in its source and a section is universally injective

A morphism of schemes whose source has at most one point and which admits a section is
universally injective.  Both halves of condition (3) of **Stacks 01S4** are immediate for such a
morphism: it is injective on points because its source is a subsingleton, and its residue field
extensions are trivial because every point of the source is in the image of the section, where
`AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section` makes the residue field map an
isomorphism.

The typical source of such a morphism is the restriction of the source map of a groupoid scheme
to a one-point open piece of its arrow scheme through the identity: the identity section of the
groupoid restricts to a section of that morphism.  Base changing it then forces the scheme of
composable pairs of the piece to have at most one point too, which is what makes the piece
stable under the composition.

## Main results

* `AlgebraicGeometry.universallyInjective_of_subsingleton_of_section`: the criterion.

## Implementation notes

Universal injectivity is `AlgebraicGeometry.UniversallyInjective`, and the criterion used is
condition (3) of Mathlib's `AlgebraicGeometry.tfae_universallyInjective`, that is of
**Stacks 01S4**: injectivity on points together with purely inseparable residue field
extensions. That a bijective homomorphism of fields is purely inseparable is the private
`AlgebraicGeometry.isPurelyInseparable_of_bijective` of
`StacksFrontier.AlgebraicGeometry.Etale.GeometricallyIrreducibleFibres`, reached by `import all`.

A point `x` of the source is identified with `s (f x)` rather than the statement being proved
only at points of the form `s y`: the two are equal because the source is a subsingleton, and
`s (f x)` is of that form, so no transport of the residue field map along an equality of points
is needed.

## References

* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes whose source is a subsingleton and which admits a section is
universally injective.**  This is condition (3) of **Stacks 01S4**: injectivity on points is the
subsingleton hypothesis, and at a point `x` of the source the residue field map is an
isomorphism because `x` coincides with the image under the section of its own image. -/
@[stacks 01S4 "a morphism with a subsingleton source and a section is universally injective"]
theorem universallyInjective_of_subsingleton_of_section {X Y : Scheme.{u}} [Subsingleton X]
    (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : UniversallyInjective f := by
  have key : ∀ (x : X) (y : Y), s.base y = x →
      (f.residueFieldMap x).hom.IsPurelyInseparable := by
    intro x y hxy
    subst hxy
    have : IsIso (f.residueFieldMap (s.base y)) :=
      isIso_residueFieldMap_of_mem_range_section f s hs y
    exact isPurelyInseparable_of_bijective _ (ConcreteCategory.bijective_of_isIso _)
  have hc : Function.Injective f ∧
      ∀ x : X, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ⟨fun a b _ => Subsingleton.elim a b, fun x => key x (f.base x) (Subsingleton.elim _ _)⟩
  exact ((tfae_universallyInjective f).out 3 1).mp hc

/-- **Universal injectivity is cancellable on the right.**  If a composite is universally
injective then so is its first factor.  Read through condition (2) of **Stacks 01S4** this is
immediate: two field-valued points of the source with the same image under the first factor have
the same image under the composite. -/
@[ega "I 3.5.6"]
theorem universallyInjective_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : UniversallyInjective (f ≫ g)) : UniversallyInjective f := by
  have h2 : ∀ (K : Type u) [Field K],
      Function.Injective (fun a : Spec (.of K) ⟶ X => a ≫ (f ≫ g)) :=
    ((tfae_universallyInjective (f ≫ g)).out 1 2).mp h
  refine ((tfae_universallyInjective f).out 2 1).mp ?_
  intro K _ a b hab
  refine h2 K ?_
  simp only [← Category.assoc]
  exact congrArg (fun q : Spec (.of K) ⟶ Y => q ≫ g) hab

end AlgebraicGeometry

end
