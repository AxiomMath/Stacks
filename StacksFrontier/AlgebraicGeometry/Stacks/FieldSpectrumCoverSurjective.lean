module

public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFlatFieldCover

/-!
# Field-valued morphisms to a stack covered by the spectrum of a field

Let `𝒵` be an algebraic stack over `S`. If some 1-morphism to `𝒵` from the algebraic stack of the
spectrum of a field is surjective, then *every* 1-morphism to `𝒵` from the algebraic stack of the
spectrum of a field is surjective. This is the surjectivity half of **Stacks 06MM**.

The mechanism is that the spectrum of a field has exactly one point. A surjection out of a
one-point stack leaves `𝒵` with at most one point, and the spectrum of a field, being nonempty,
contributes a point to its own stack; a map between point sets whose target has at most one point
and whose source has at least one is surjective. In particular the flatness hypothesis that
Stacks 06MM also carries is not used for this conclusion, and neither is any topology on the point
sets: `AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**) is surjectivity of the underlying
map of sets.

## Main definitions

* `AlgebraicGeometry.Stack.fieldSpectrumPoint`: the tautological field-valued point of the
  algebraic stack of the spectrum of a field, given by the identity of that spectrum.

## Main results

* `AlgebraicGeometry.Stack.nonempty_points_fieldSpectrumStack`: the algebraic stack of the
  spectrum of a field has at least one point.
* `AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum_cover`: **Stacks 06MM**, surjectivity.

## Implementation notes

The field spectra are taken as `AlgebraicGeometry.Stack.FieldSpectrum`, i.e. as objects of the big
fppf site of `S` presented with an isomorphism of the underlying scheme onto the spectrum of a
field. That is more general than naming a field `k` and a structure morphism `Spec k ⟶ S`: such
data determine a `FieldSpectrum` whose isomorphism is the identity, so the statement for a named
field and structure morphism is an instance of the one proved here.

That at most one point remains is `AlgebraicGeometry.Stack.subsingleton_points_fieldSpectrumStack`
together with `Function.Surjective.subsingleton`. The companion nonemptiness is proved here by
exhibiting a field-valued point: the objects of the stack of an object `U` of the site are the
objects of the site over `U`, so the identity of `U` is such an object, lying over `U` itself.

## References

* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06MM](https://stacks.math.columbia.edu/tag/06MM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tautological field-valued point of the spectrum of a field.** The objects of the
algebraic stack represented by an object `U` of the big fppf site of `S` are the objects of the
site over `U`, so the identity of `U` is one of them, and it lies over `U`. Taking `U` to be the
spectrum of a field makes it a field-valued point in the sense of **Stacks 04XF**. -/
def fieldSpectrumPoint (F : FieldSpectrum B S hS) :
    FieldValuedPoint B S hS (schemeStack.{u, w} B S hS F.base).val.val where
  carrier := F.carrier
  base := F.base
  isSpec := F.isSpec
  obj := Over.mk (𝟙 F.base)
  «over» := rfl

/-- **The algebraic stack of the spectrum of a field has a point.** It is represented by the
tautological field-valued point `AlgebraicGeometry.Stack.fieldSpectrumPoint`.

This is the companion of `AlgebraicGeometry.Stack.subsingleton_points_fieldSpectrumStack`: the two
together say that the point space of **Stacks 04XG** of such a stack is a singleton. -/
theorem nonempty_points_fieldSpectrumStack (F : FieldSpectrum B S hS) :
    Nonempty (points B S hS (schemeStack.{u, w} B S hS F.base).val.val
      (Classical.choose (schemeStack.{u, w} B S hS F.base).property)) :=
  ⟨pointClass B S hS _ _ (fieldSpectrumPoint.{u, w} B S hS F)⟩

/-- **Stacks 06MM, surjectivity.** Let `𝒵` be an algebraic stack over `S` admitting a surjective
1-morphism from the algebraic stack of the spectrum of a field. Then every 1-morphism to `𝒵` from
the algebraic stack of the spectrum of a field is surjective.

The spectrum of a field has one point, so a surjection out of its stack leaves `𝒵` with at most
one point; the source of the second 1-morphism has a point, which therefore hits every point of
`𝒵`. Flatness of the given surjection, which Stacks 06MM also assumes, is not needed. -/
@[stacks 06MM "surjectivity"]
theorem isSurjective_of_fieldSpectrum_cover (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (F F' : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ 𝒵)
    (g : schemeStack.{u, w} B S hS F'.base ⟶ 𝒵)
    (hf : IsSurjective B S hS f) :
    IsSurjective B S hS g := by
  have := subsingleton_points_fieldSpectrumStack.{u, w} B S hS F
  have : Subsingleton (points B S hS 𝒵.val.val (Classical.choose 𝒵.property)) :=
    hf.subsingleton
  obtain ⟨p⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F'
  exact fun _ => ⟨p, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Stack

end
