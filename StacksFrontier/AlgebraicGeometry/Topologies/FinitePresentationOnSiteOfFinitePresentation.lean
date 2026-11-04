module

public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Finite presentation in Mathlib's sense is finite presentation on the site

Mathlib's `SheafOfModules.IsFinitePresentation` asks for finite presentations on the members of
one family covering the final object; the tree's `SheafOfModules.IsFinitePresentationOnSite`
asks for finite global presentations on a covering of every object.  This file proves that the
first implies the second, which is the converse of
`SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite'`: the covering of an object
is the sieve of objects of the family, and a finite global presentation restricts along each of
its arrows.

## Main results

* `SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Finite presentation in Mathlib's sense implies finite presentation on the site.** -/
theorem isFinitePresentationOnSite_of_isFinitePresentation (M : SheafOfModules.{w} R)
    [h : M.IsFinitePresentation] : M.IsFinitePresentationOnSite := by
  classical
  obtain ⟨σ, hσ⟩ := h.exists_quasicoherentData
  refine ⟨fun W => ?_⟩
  refine ⟨{g : Over W // (Sieve.ofObjects σ.X W) g.hom}, fun a => a.1.left, fun a => a.1.hom,
    ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {g : Over W // (Sieve.ofObjects σ.X W) g.hom} => a.1.left)
        (fun a => a.1.hom) = Sieve.ofObjects σ.X W := by
      refine le_antisymm (fun X g hg => ?_) (fun X g hg => ?_)
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact (Sieve.ofObjects σ.X W).downward_closed a.2 b
      · rw [Sieve.mem_ofArrows_iff]
        exact ⟨⟨Over.mk g, hg⟩, 𝟙 X, by simp⟩
    rw [hEq]
    exact σ.coversTop W
  · intro a
    obtain ⟨k, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff σ.X a.1.hom).mp a.2
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      M b (HasFiniteGlobalPresentation.of_presentation' (σ.presentation k) inferInstance)

end SheafOfModules

end
