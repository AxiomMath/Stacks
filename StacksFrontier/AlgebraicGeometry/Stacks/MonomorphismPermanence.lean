module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe

/-!
# Permanence properties of monomorphisms of algebraic stacks (Stacks 04ZX, Stacks 04ZY)

Monomorphisms of algebraic stacks over `S`, in the sense of **Stacks 04ZW**, are stable under
base change (**Stacks 04ZX**) and under composition (**Stacks 04ZY**).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_comp`: **Stacks 04ZY**.
* `Stack.AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks`:
  **Stacks 04ZX**, registered here with `add_to_stacks`.

## Implementation notes

The source proves this from the general discussion of Section 04XB together with the stability of
monomorphisms of algebraic spaces under composition (**Stacks 042O**), which is here
`CategoryTheory.mono_comp`. The general discussion is this library's
`AlgebraicGeometry.Stack.hasRelativeProperty_comp` (**Stacks 045B**), and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` is representability by algebraic spaces
together with `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) at
`CategoryTheory.MorphismProperty.monomorphisms`, written out; so the proof is that lemma at that
property, with representability of the composite supplied by **Stacks 0301**.

`HasRelativeProperty` takes locality of the property at the target for the fppf precoverage as an
instance argument. For monomorphisms of algebraic spaces over `S` that is **Stacks 042D**, which
is `AlgebraicGeometry.Space.mono_isLocalAtTarget_fppf`; earlier modules in this directory record
it as unavailable and carry it as a hypothesis instead, but it is available now, so this lemma is
unconditional. Stability under base change and under composition are Mathlib instances on
`CategoryTheory.MorphismProperty.monomorphisms`.

## References

* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 042O](https://stacks.math.columbia.edu/tag/042O)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZY](https://stacks.math.columbia.edu/tag/04ZY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04ZY.** A composite of monomorphisms of algebraic stacks over `S` (**Stacks 04ZW**)
is a monomorphism. -/
@[stacks 04ZY]
theorem isMonomorphism_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsMonomorphism B S hS f) (hg : IsMonomorphism B S hS g) :
    IsMonomorphism B S hS (f ≫ g) :=
  have hrep := isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hf.1 hg.1
  ⟨hrep, Stack.hasRelativeProperty_comp.{u, u, u + 1, u} B S hS
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
    f.hom g.hom hf.1 hg.1 hf.2 hg.2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end

-- **Stacks 04ZX**, monomorphisms are stable under base change: the tag is exactly the existing
-- `isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks`, registered here, in the semantic
-- module for permanence of monomorphisms, rather than restated.
namespace AlgebraicGeometry.Stack

add_to_stacks 04ZX AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks

end AlgebraicGeometry.Stack
