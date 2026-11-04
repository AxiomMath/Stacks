module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import StacksFrontier.AlgebraicTopology.SimplicialSet.KanFibration

/-!
# Simplicial groups are Kan complexes

A simplicial group is a simplicial object `X : SimplicialObject GrpCat` in the category of groups:
each `X_n` is a group and every face map `δ i : X_{n+1} → X_n` and every degeneracy map
`σ i : X_n → X_{n+1}` is a group homomorphism; multiplicative notation is used and no
commutativity is assumed. Every horn of the underlying simplicial set `X ⋙ forget GrpCat` can be
filled (Moore's theorem).

## Main results

* `CategoryTheory.SimplicialObject.kanComplex_forget_addGrpCat`: the underlying simplicial set of
  a simplicial group written additively is a Kan complex.
* `CategoryTheory.SimplicialObject.kanComplex_forget`: the underlying simplicial set of a
  simplicial group is a Kan complex.

## Implementation notes

For a simplicial group written additively the statement is the case `Y = 0` of [Stacks, Tag 08P0]
(`CategoryTheory.SimplicialObject.fibration_whiskerRight_forget_of_surjective`), whose proof
contains Moore's horn filling: the morphism to the constant simplicial group `0` is termwise
surjective, hence a Kan fibration, and its target is the terminal simplicial set. A simplicial
group `X` is carried to a simplicial group written additively by `GrpCat.toAddGrp`, which does not
change the underlying simplicial set: `X_n` and `Additive X_n` are identified by `Additive.ofMul`.

## References

* [Stacks, Tag 08NZ](https://stacks.math.columbia.edu/tag/08NZ)
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra Limits SSet SSet.modelCategoryQuillen

universe u

namespace CategoryTheory.SimplicialObject

/-- The underlying simplicial set of a simplicial group, written additively, is a Kan complex:
the morphism to the constant simplicial group `0` is termwise surjective, hence a Kan fibration
by [Stacks, Tag 08P0], and its target is terminal. -/
theorem kanComplex_forget_addGrpCat (X : SimplicialObject AddGrpCat.{u}) :
    KanComplex (X ⋙ forget AddGrpCat) := by
  let Z : SimplicialObject AddGrpCat.{u} := (Functor.const _).obj (AddGrpCat.of PUnit)
  let f : X ⟶ Z := { app _ := AddGrpCat.ofHom 0 }
  have hZ : IsTerminal (Z ⋙ forget AddGrpCat.{u}) := Functor.isTerminal fun _ ↦ by
    dsimp [Z]
    exact Types.isTerminalPUnit
  refine (isFibrant_iff_of_isTerminal _ hZ).2
    (fibration_whiskerRight_forget_of_surjective f fun _ y ↦ ⟨0, ?_⟩)
  dsimp [Z] at y ⊢
  subsingleton

/-- **Stacks 08NZ**.
Let `X` be a simplicial group. Then the underlying simplicial set of `X` is a Kan complex. -/
@[stacks 08NZ "a simplicial group is Mathlib's `SimplicialObject GrpCat`, and its underlying \
  simplicial set is `X ⋙ forget GrpCat`"]
theorem kanComplex_forget (X : SimplicialObject GrpCat.{u}) :
    KanComplex (X ⋙ forget GrpCat) := by
  have := kanComplex_forget_addGrpCat (X ⋙ GrpCat.toAddGrp)
  let e : X ⋙ forget GrpCat ≅ (X ⋙ GrpCat.toAddGrp) ⋙ forget AddGrpCat :=
    NatIso.ofComponents (fun _ ↦ Additive.ofMul.toIso) fun _ ↦ rfl
  exact isFibrant_of_fibration e.hom

end CategoryTheory.SimplicialObject
