module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimitIff

/-!
# A colimit along thickenings has a fundamental system of weak ideals of definition

The last sentence of **Stacks 0AIV** reads: the formal algebraic space `h_𝔛` attached to a formal
scheme `𝔛` in the sense of McQuillan is a colimit of schemes as in Stacks 0AIU if and only if there
exists a fundamental system of weak ideals of definition for `𝔛`. Its two directions behave
differently.

The "if" direction is false as the source states it: the twisted double has a fundamental system
of weak ideals of definition, in the sectionwise sense the source defines, and its functor of
points is not such a colimit
(`AlgebraicGeometry.McQuillanFormalScheme.not_forall_isFppfColimitOfThickenings_of_exists`). It
becomes true once the members of the system are required to be cut out by their sections over the
affine formal opens, and
`AlgebraicGeometry.McQuillanFormalScheme.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`
is that equivalence.

The "only if" direction, proved here, needs no such repair: a colimit presentation produces the
fundamental system the source asks for, with the source's own sectionwise notion of a fundamental
system of weak ideals of definition and no condition on its members.

## Main results

* `AlgebraicGeometry.McQuillanFormalScheme`
  `.exists_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFppfColimitOfThickenings`:
  the "only if" direction of the last sentence of Stacks 0AIV, as printed.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.McQuillanFormalScheme

open LocallyTopologicallyRingedSpace

/-- If the functor of points `h_𝔛` of a formal scheme `𝔛` in the sense of McQuillan is a colimit
of schemes along thickenings, then there exists a fundamental system of weak ideals of definition
for `𝔛`: a family of ideal sheaves each of which is a weak ideal of definition over every affine
formal open, whose ideals of sections form a neighbourhood basis of zero over every affine formal
open. -/
@[stacks 0AIV "the only if direction of the last sentence, as printed and unconditional: if h_𝔛 \
is a colimit of schemes along thickenings as in Lemma 0AIU (colimit in fppf sheaves), then there \
exists a fundamental system of weak ideals of definition for 𝔛, in the sectionwise sense the \
source defines, with no condition on its members. The converse fails as printed \
(not_forall_isFppfColimitOfThickenings_of_exists) and needs the members to be cut out by their \
sections (isFppfColimitOfThickenings_iff_exists_isFundamentalSystem)"]
theorem exists_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFppfColimitOfThickenings
    (𝔛 : McQuillanFormalScheme.{u}) (h : 𝔛.IsFppfColimitOfThickenings) :
    ∃ 𝒮 : Set (IdealSheaf 𝔛.obj),
      IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj) := by
  obtain ⟨𝒮, -, hfund⟩ := 𝔛.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem.mp h
  exact ⟨𝒮, hfund⟩

end AlgebraicGeometry.McQuillanFormalScheme

end
