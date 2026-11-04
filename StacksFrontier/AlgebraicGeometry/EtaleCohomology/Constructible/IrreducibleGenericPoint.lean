module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic point is hit by every nonempty étale neighbourhood

Stacks 09BG says that a sheaf squeezed between two constant sheaves on an irreducible scheme, whose
stalk at a geometric point of the generic point is the smaller group, *is* the smaller constant
sheaf. The entire proof the source gives for it is one sentence: *for every étale morphism
`U → X` with `U ≠ ∅` the point `η` is in the image.* This file proves that sentence.

The content is topological once openness is in hand: an étale morphism is universally open, so the
image of a nonempty open of the source is a nonempty open of `X`, and the generic point of an
irreducible sober space lies in every nonempty open subset. The form with a nonempty *open subset*
of the source, and not only with a nonempty source, is the one the argument of 09BG uses: a section
of a subsheaf of a constant sheaf is locally constant, and one works on the open subset of the
étale neighbourhood where it takes a given value.

## Main results

* `AlgebraicGeometry.genericPoint_mem_range_of_universallyOpen`: the generic point of an
  irreducible scheme lies in the image of any universally open morphism with nonempty source.
* `AlgebraicGeometry.genericPoint_mem_image_of_universallyOpen`: the same for the image of a
  nonempty open subscheme of the source.
* `AlgebraicGeometry.SmallEtale.genericPoint_mem_range_structureMorphism` and
  `AlgebraicGeometry.SmallEtale.genericPoint_mem_image_structureMorphism`: the two statements for
  an object of the small étale site of Stacks 021B, whose structure morphism is étale and
  therefore universally open.

## Implementation notes

The hypothesis is `UniversallyOpen` rather than `Etale`: openness of the underlying map is all the
argument uses, and `AlgebraicGeometry.Etale` supplies it by instance search, so the étale
statements are the same theorem with nothing added. Sobriety is not a hypothesis either — the
underlying space of a scheme is sober, which is what gives `TopologicalSpace.genericPoint` its
defining property on an irreducible scheme.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The generic point of an irreducible scheme lies in the image of every universally open
morphism with nonempty source.** The image is open because the morphism is, it is nonempty because
the source is, and a nonempty open subset of an irreducible sober space contains its generic
point. -/
@[ega "I 7.1.10" "partial"]
public theorem genericPoint_mem_range_of_universallyOpen {X Y : Scheme.{u}} (f : Y ⟶ X)
    [UniversallyOpen f] [IrreducibleSpace X] [Nonempty Y] :
    genericPoint X ∈ Set.range f.base := by
  refine ((genericPoint_spec X).mem_open_set_iff f.isOpenMap.isOpen_range).2 ?_
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact ⟨f.base y, Set.mem_univ _, Set.mem_range_self _⟩

/-- **The generic point of an irreducible scheme lies in the image of every nonempty open subscheme
of the source of a universally open morphism to it.**

This is the form Stacks 09BG uses: a section of a subsheaf of a constant sheaf over an étale
neighbourhood is locally constant, and the argument is run on the open subset of that neighbourhood
where the section takes a prescribed value. -/
public theorem genericPoint_mem_image_of_universallyOpen {X Y : Scheme.{u}} (f : Y ⟶ X)
    [UniversallyOpen f] [IrreducibleSpace X] (W : Y.Opens) (hW : (W : Set Y).Nonempty) :
    genericPoint X ∈ f.base '' (W : Set Y) := by
  refine ((genericPoint_spec X).mem_open_set_iff (f.isOpenMap _ W.2)).2 ?_
  obtain ⟨y, hy⟩ := hW
  exact ⟨f.base y, Set.mem_univ _, y, hy, rfl⟩

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IrreducibleSpace S]

/-- **Every nonempty object of the small étale site of an irreducible scheme covers the generic
point.** The structure morphism of an object of the small étale site is étale, hence universally
open, so this is
`AlgebraicGeometry.genericPoint_mem_range_of_universallyOpen`. -/
public theorem genericPoint_mem_range_structureMorphism (U : SmallEtale B S hS)
    [Nonempty ((toScheme B S hS).obj U)] :
    genericPoint S ∈ Set.range (B.inclusion.map U.obj.hom).base := by
  have : IrreducibleSpace ↥(B.inclusion.obj (B.obj S hS)) := inferInstanceAs (IrreducibleSpace ↥S)
  have : Nonempty ↥(B.inclusion.obj (Over.left U.obj)) :=
    inferInstanceAs (Nonempty ↥((toScheme B S hS).obj U))
  exact genericPoint_mem_range_of_universallyOpen _

/-- **Every nonempty open subset of an object of the small étale site of an irreducible scheme
covers the generic point.** -/
public theorem genericPoint_mem_image_structureMorphism (U : SmallEtale B S hS)
    (W : ((toScheme B S hS).obj U).Opens)
    (hW : (W : Set ((toScheme B S hS).obj U)).Nonempty) :
    genericPoint S ∈ (B.inclusion.map U.obj.hom).base '' (W : Set ((toScheme B S hS).obj U)) := by
  have : IrreducibleSpace ↥(B.inclusion.obj (B.obj S hS)) := inferInstanceAs (IrreducibleSpace ↥S)
  exact genericPoint_mem_image_of_universallyOpen _ W hW

end SmallEtale

end AlgebraicGeometry

end
