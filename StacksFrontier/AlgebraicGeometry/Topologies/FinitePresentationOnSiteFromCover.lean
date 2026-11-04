module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Finite presentation on a site from a family covering the final object

Stacks 03DL(7), `SheafOfModules.IsFinitePresentationOnSite`, asks for a covering of *every*
object of the site on whose members the restricted module has a finite global presentation.
Stacks 03DN says that it is enough to exhibit one family covering the final object.  This file
proves that implication in the rendering by universal properties: the sieve of objects of such a
family covers every object, and a finite global presentation travels along each of that sieve's
arrows.

The quasi-coherent counterpart is the backward implication of
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`.  It is not
reused here, because it passes through quasi-coherence of the restrictions and so forgets the
two integers whose finiteness is the point.

## Main results

* `SheafOfModules.isFinitePresentationOnSite_of_coversTop_hasFiniteGlobalPresentation`: a sheaf
  of modules with a finite global presentation on each member of a family covering the final
  object is of finite presentation on the site.

## Implementation notes

The argument is the assembly already performed inside
`SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite` and
`SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`, extracted so that it can be
run from any covering family rather than from the one coherence or Mathlib's finite presentation
happens to supply.  The index type demanded by `SheafOfModules.IsFinitePresentationOnSite` is
`Type (max u v)`, and the arrows of the sieve of objects over a fixed object form a subtype of
`CategoryTheory.Over`, which lives in `Type (max u v)`; so the index universe of the given family
is free.

No tag attribute is placed: Stacks 03DN is already carried by the two comparisons of the
renderings of Stacks 03DL(7), and this is one direction of one of them.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A finite global presentation on each member of a family covering the final object gives
finite presentation on the site.**  The sieve of objects of the family covers every object, and
a finite global presentation restricts along each of that sieve's arrows by
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap`. -/
theorem isFinitePresentationOnSite_of_coversTop_hasFiniteGlobalPresentation
    (M : SheafOfModules.{w} R) {K : Type t} (Z : K → C) (hZ : J.CoversTop Z)
    (hpres : ∀ k, (M.over (Z k)).HasFiniteGlobalPresentation) :
    M.IsFinitePresentationOnSite := by
  classical
  refine ⟨fun W => ?_⟩
  refine ⟨{g : Over W // (Sieve.ofObjects Z W) g.hom}, fun a => a.1.left, fun a => a.1.hom,
    ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {g : Over W // (Sieve.ofObjects Z W) g.hom} => a.1.left)
        (fun a => a.1.hom) = Sieve.ofObjects Z W := by
      refine le_antisymm (fun X g hg => ?_) (fun X g hg => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact (Sieve.ofObjects Z W).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 X, by simp⟩
    rw [hEq]
    exact hZ W
  · intro a
    obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff Z a.1.hom).mp a.2
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M b (hpres k)

end SheafOfModules

end
