module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality

/-!
# Complete dévissages at a point and the support of the module

A complete dévissage of `F/X/S` at `x` in the sense of the source
(`AlgebraicGeometry.NonemptyCompleteDevissageAt`, [Stacks, Tag 05HI]) places `x` in the support
of the fibre module, so the zero module has none. The notion
`AlgebraicGeometry.CompleteDevissageAt` adds the empty dévissage of the zero module; this file
shows that for a nonzero module the two notions agree.

## Main results

* `AlgebraicGeometry.NonemptyCompleteDevissageAt.not_isZero`: the zero module has no complete
  dévissage at any point.
* `AlgebraicGeometry.nonempty_nonemptyCompleteDevissageAt_iff`: a complete dévissage at `x` in
  the sense of the source exists exactly when one exists under the zero-module convention and
  the module is nonzero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- The zero module has no complete dévissage at any point. -/
theorem NonemptyCompleteDevissageAt.not_isZero (D : NonemptyCompleteDevissageAt f F x) :
    ¬ IsZero F := fun hF => by
  have h := D.mem_fiber_support
  rw [SheafOfModules.supp_eq_empty_of_isZero
    ((Scheme.Modules.pullback (f.fiberι (f x))).map_isZero hF)] at h
  exact h

/-- A complete dévissage of `F/X/S` at `x` in the sense of the source exists exactly when one
exists under the zero-module convention and `F` is nonzero. -/
theorem nonempty_nonemptyCompleteDevissageAt_iff :
    Nonempty (NonemptyCompleteDevissageAt f F x) ↔
      Nonempty (CompleteDevissageAt f F x) ∧ ¬ IsZero F :=
  ⟨fun ⟨D⟩ => ⟨⟨.nonempty D⟩, D.not_isZero⟩,
    fun ⟨⟨D⟩, hF⟩ => ⟨D.toNonemptyCompleteDevissageAt hF⟩⟩

end AlgebraicGeometry
