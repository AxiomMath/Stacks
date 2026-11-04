module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed

/-!
# Sequential and countably indexed affine presentations agree (Stacks 0AII)

An fppf sheaf on the big fppf site of `S` admits a presentation by a sequence of affine
schemes and thickenings exactly when it admits one indexed by a countable nonempty directed
preorder.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_exists_countable_presentation`:
  **Stacks 0AII**.

## Implementation notes

The sequential side is `AlgebraicGeometry.FormalSpace.IsCountablyIndexed` (**Stacks 0AIJ**),
whose clause is the colimit clause of `IsAffineFormalAlgebraicSpace` (**Stacks 0AI7**) at the
index category `ℕ`; the countable side is the same clause at a countable index, so neither
condition is restated here.

The mathematics is the source's: a countable nonempty directed preorder has a cofinal
monotone sequence, which is
`StacksDraft.Algebra.MittagLeffler.InverseSystem.exists_monotone_cofinal_nat`, and a cofinal
monotone map induces a final functor by `Monotone.final_functor_iff`, along which colimits are
preserved. Both directions are the same two lines, the forward one taking the cofinal map to be
`ULift.down` on a universe lift of `ℕ` — the index type of the countable side must live in
`Type (u + 1)`, as in the definition of an affine formal algebraic space.

The statement is about an arbitrary fppf sheaf: no part of the argument uses the set-theoretic
condition or the existence of a presentation, so assuming
`IsAffineFormalAlgebraicSpace` would be a hypothesis the source does not need.

## References

* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 0AII.** An fppf sheaf has a sequential presentation by affine
schemes and thickenings if and only if it has one indexed by a countable nonempty directed
preorder. -/
@[stacks 0AII]
theorem isCountablyIndexed_iff_exists_countable_presentation (X : FppfSheaf B S hS) :
    IsCountablyIndexed B S hS X ↔
      ∃ (I : Type (u + 1)) (pre : Preorder I),
        letI : Preorder I := pre
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧ Countable I ∧
          ∃ D : I ⥤ BigAffineFppf B S hS,
            (∀ ⦃i j : I⦄ (f : i ⟶ j),
              Stacks.Thickenings.IsThickening
                ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
              Nonempty (X ≅ colimit
                (D ⋙ BigAffineFppf.inclusion B S hS ⋙
                  Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  constructor
  · rintro ⟨D, hthick, hcolim⟩
    have hc : Monotone (ULift.down : ULift.{u + 1, 0} ℕ → ℕ) := fun _ _ h => h
    let e := hc.functor
    have : Functor.Final e := hc.final_functor_iff.mpr fun n => ⟨ULift.up n, le_rfl⟩
    refine ⟨ULift.{u + 1, 0} ℕ, inferInstance, ⟨ULift.up 0⟩, inferInstance, inferInstance,
      e ⋙ D, fun ⦃_ _⦄ f => hthick (e.map f), ?_⟩
    exact hcolim.map fun hcolim => hcolim ≪≫ (Functor.Final.colimitIso e _).symm
  · rintro ⟨I, pre, hI, hdir, hcnt, D, hthick, hcolim⟩
    obtain ⟨c, hc, hcof⟩ := exists_monotone_cofinal_nat (I := I)
    let e := hc.functor
    have : Functor.Final e := hc.final_functor_iff.mpr hcof
    refine ⟨e ⋙ D, fun ⦃_ _⦄ f => hthick (e.map f), ?_⟩
    exact hcolim.map fun hcolim => hcolim ≪≫ (Functor.Final.colimitIso e _).symm

end AlgebraicGeometry.FormalSpace

end
