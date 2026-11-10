module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequenceRestrictions

/-!
# An instance of the hypotheses of the Mayer--Vietoris Ext sequence

`Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence_restrictions` (Stacks
08BW) is stated for a sheaf of rings `O` on a topological space and two opens `U`, `V` with
`U ⊔ V = ⊤`. This file exhibits that data with `U` and `V` proper and overlapping, so that
none of the three terms of the sequence is forced to be the restriction to the whole space or
to the empty space.

## Main definitions

* `Stacks.ExtensionByZero.Example08BW.sp`: three points, discrete.
* `Stacks.ExtensionByZero.Example08BW.U` and `Stacks.ExtensionByZero.Example08BW.V`: the opens
  `{0, 1}` and `{1, 2}`.
* `Stacks.ExtensionByZero.Example08BW.ringSheaf`: the constant sheaf of rings at `ℤ`.

## Main results

* `Stacks.ExtensionByZero.Example08BW.nondegenerate`: the two opens cover the space, each is
  proper, and their intersection is non-empty.

## References

* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ExtensionByZero.Example08BW

/-- Three points, discrete. -/
def sp : TopCat.{u} := @TopCat.of (ULift.{u} (Fin 3)) ⊥

def U : Opens (sp.{u}) := ⟨{x | x.down ≠ 2}, trivial⟩

def V : Opens (sp.{u}) := ⟨{x | x.down ≠ 0}, trivial⟩

theorem cover : U.{u} ⊔ V.{u} = ⊤ := by
  ext x
  simp only [Opens.coe_sup, Set.mem_union, Opens.coe_top, Set.mem_univ, iff_true]
  change x.down ≠ 2 ∨ x.down ≠ 0
  omega

theorem overlap_ne_bot : U.{u} ⊓ V.{u} ≠ ⊥ := by
  intro h
  have : (⟨1⟩ : ULift.{u} (Fin 3)) ∈ (U.{u} ⊓ V.{u} : Opens _) :=
    ⟨show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide⟩
  rw [h] at this
  exact this

/-- An open set missing a point is not the whole space. -/
private theorem ne_top_of_notMem {X : TopCat.{u}} {W : Opens X} {x : X} (hx : x ∉ W) :
    W ≠ ⊤ :=
  fun h => hx (h ▸ trivial)

theorem U_ne_top : U.{u} ≠ ⊤ :=
  ne_top_of_notMem (x := ⟨2⟩) fun h => (show (2 : Fin 3) ≠ 2 from h) rfl

theorem V_ne_top : V.{u} ≠ ⊤ :=
  ne_top_of_notMem (x := ⟨0⟩) fun h => (show (0 : Fin 3) ≠ 0 from h) rfl

/-- A non-trivial sheaf of rings on the three-point space: the constant sheaf at `ℤ`. -/
def ringSheaf : Sheaf (Opens.grothendieckTopology (sp.{u})) RingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology (sp.{u})) RingCat.{u}).obj
    (RingCat.of (ULift.{u} ℤ))

/-- **The hypotheses of Stacks 08BW are satisfiable non-degenerately**: a space, a non-trivial
sheaf of rings on it, and two proper opens that cover it and have non-empty intersection. -/
theorem nondegenerate :
    ∃ (Y : TopCat.{u}), Nonempty (Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) ∧
      ∃ (A B : Opens Y), A ⊔ B = ⊤ ∧ A ⊓ B ≠ ⊥ ∧ A ≠ ⊤ ∧ B ≠ ⊤ :=
  ⟨sp.{u}, ⟨ringSheaf.{u}⟩, U.{u}, V.{u}, cover, overlap_ne_bot, U_ne_top, V_ne_top⟩

attribute [local instance] HasDerivedCategory.standard

/-- The theorem really applies at that witness. -/
example : True := by
  have := Stacks.ExtensionByZero.exists_mayerVietoris_ext_longExactSequence_restrictions
    ringSheaf.{u} U.{u} V.{u} cover
  trivial

end Stacks.ExtensionByZero.Example08BW

end
