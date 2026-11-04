module

public import StacksFrontier.Deformation.Formal.MinimalVersal.DescentVersality
public import StacksFrontier.Deformation.Formal.MinimalVersal.Existence
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.Deformation.Schlessinger.VersalImpliesS1
public import StacksCore.Tactic.StacksAttribute

/-!
# Existence of minimal versal formal objects

A predeformation category that has a versal formal object also has a minimal versal formal
object.

## Main results

* `Deformation.exists_minimalVersalFormalObject` produces a minimal versal formal object from
  the existence of a versal one.

## Implementation notes

A versal formal object makes the predeformation category satisfy Schlessinger's condition
(S1), so Stacks 06T2 applies and provides a smallest descent of it. Minimal versality of that
descent is exactly the conjunction of Stacks 06T3 — the descended object is again versal — with
the no-proper-further-descent field of `Deformation.SmallestDescent`, so no new argument is
needed and no particular versal object is fixed in the conclusion of the existence statement.

The Noetherian and finite-module hypotheses are the chapter conventions of Stacks 06G9, used
here exactly as `Deformation.exists_smallestDescent` uses them.

## References

* [Stacks Project, Tag 06T5](https://stacks.math.columbia.edu/tag/06T5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

/-- **Stacks 06T5.** A predeformation category with a versal formal object has a minimal
versal formal object: a smallest descent of the given versal object is one. -/
@[stacks 06T5 "existence"]
public theorem exists_minimalVersalFormalObject (hp : IsPredeformationCategory p)
    (hξ : ∃ ξ : FormalObject p, IsVersal hp.cofibered ξ) :
    ∃ ξ : FormalObject p, IsMinimalVersal hp.cofibered ξ := by
  obtain ⟨ξ, hξ⟩ := hξ
  let d : SmallestDescent ξ :=
    smallestDescent hp.cofibered (schlessingerConditionS1_of_versal p hp ξ hξ) ξ hξ
  exact ⟨d.object, isVersal_smallestDescent hp.cofibered hξ d, d.further_descent_surjective⟩

end Deformation

end
