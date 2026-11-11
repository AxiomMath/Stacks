module

/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Sets

/-!
# Stacks 00AF — the essential image of `i_*` on sheaves of sets

Let `X` be a topological space and `i : Z → X` the inclusion of a closed subset. Stacks 00AF
states that `i_* : Sh(Z) → Sh(X)` is fully faithful and that its essential image consists
exactly of the sheaves `G` with `G_x = {*}` for every `x ∈ X \ Z`.

Sheaves of sets form a type of algebraic structure (Stacks 007M) with final object `PUnit`:
the category `Type u` with the identity functor. The converse inclusion of the essential
image is the general statement `Stacks.ClosedImmersion.closedSupport_essImage_of_terminal_stalks`
for that structure; the forward inclusion is `pushforward_stalkIsSingleton_of_notMem`.

## Main results

* `essImage_pushforward00AF_iff`: for `Z` closed, `G` is in the essential image of `i_*` iff
  `G_x` is a singleton for every `x ∉ Z`.
* `pushforward00AF_fullyFaithful_and_essImage_iff`: the whole of Stacks 00AF.
-/

@[expose] public section

open CategoryTheory TopCat Limits TopologicalSpace

universe u

namespace Stacks

/-- Sets as a type of algebraic structure: the category `Type u` with the identity functor. -/
def typesAlgStructure : AlgebraicStructureType.{u, u + 1} where
  C := Type u
  F := 𝟭 (Type u)

/-- `typesAlgStructure` has all colimits, those of `Type u`. -/
instance : HasColimits typesAlgStructure.{u}.C := inferInstanceAs (HasColimits (Type u))

/-- The one-point set `PUnit`, the final object of `typesAlgStructure`. -/
def typesAlgStructureWithFinal : typesAlgStructure.{u}.WithFinal where
  zero := PUnit.{u + 1}
  isTerminal := (Types.isTerminalEquivUnique PUnit.{u + 1}).symm inferInstance
  fZeroUnique := (inferInstance : Unique PUnit.{u + 1})

end Stacks

/-- For `Z ⊆ X` closed, a sheaf of sets `G` on `X` lies in the essential image of
`i_* : Sh(Z) → Sh(X)` iff its stalk `G_x` is a singleton at every point `x ∉ Z`. -/
theorem essImage_pushforward00AF_iff (X : TopCat.{u}) {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf (Type u) X) :
    (pushforward00AF X Z).essImage G ↔ ∀ x : X, x ∉ Z → StalkIsSingleton X G x := by
  refine ⟨fun ⟨F, ⟨e⟩⟩ x hx =>
    StalkIsSingleton.of_iso X _ G e x (pushforward_stalkIsSingleton_of_notMem X hZ F x hx),
    fun h => ?_⟩
  refine Stacks.ClosedImmersion.closedSupport_essImage_of_terminal_stalks X Z hZ
    Stacks.typesAlgStructure.{u} Stacks.typesAlgStructureWithFinal G fun x hx => ?_
  obtain ⟨hu⟩ := h x hx
  exact ⟨(Types.isTerminalEquivUnique _).symm hu |>.uniqueUpToIso
    Stacks.typesAlgStructureWithFinal.isTerminal⟩

/-- **Stacks 00AF.** For the inclusion `i : Z → X` of a closed subset, the functor
`i_* : Sh(Z) → Sh(X)` on sheaves of sets is fully faithful, and its essential image consists
exactly of the sheaves `G` with `G_x = {*}` for all `x ∈ X \ Z`. -/
@[stacks 00AF "Full faithfulness holds for any subset `Z`; closedness is used for the
  essential image."]
theorem pushforward00AF_fullyFaithful_and_essImage_iff (X : TopCat.{u}) {Z : Set X}
    (hZ : IsClosed Z) :
    (pushforward00AF X Z).Full ∧ (pushforward00AF X Z).Faithful ∧
      ∀ G : TopCat.Sheaf (Type u) X,
        (pushforward00AF X Z).essImage G ↔ ∀ x : X, x ∉ Z → StalkIsSingleton X G x :=
  ⟨pushforward_full X Z, pushforward_faithful X Z, essImage_pushforward00AF_iff X hZ⟩
