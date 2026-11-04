module

/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushforward along the inclusion of a closed subset (sheaves of sets)

Let `X` be a topological space, `Z ⊆ X` a subset and `i : Z → X` the inclusion. The pushforward
`i_* : Sh(Z) → Sh(X)` on sheaves of sets is fully faithful, and for `Z` closed the stalk of
`i_* F` at every point outside `Z` is a singleton.

## Main definitions

* `pushforward00AF`, `pullback00AF`: the functors `i_*` and `i⁻¹` on sheaves of sets.
* `pullbackPushforwardAdj`: the adjunction `i⁻¹ ⊣ i_*`.
* `StalkIsSingleton`: the stalk of a sheaf of sets at a point has exactly one element.

## Main results

* `pushforward_faithful`, `pushforward_full`: `i_*` is fully faithful.
* `pushforward_stalkIsSingleton_of_notMem`: for `Z` closed and `x ∉ Z`, the stalk `(i_* F)_x` is
  a singleton.
-/

@[expose] public section

open CategoryTheory TopCat Limits TopologicalSpace Opposite

universe u

/-- The pushforward functor `i_* : Sh(Z) → Sh(X)` on sheaves of sets, along the inclusion of a
subset `Z ⊆ X`. -/
noncomputable def pushforward00AF (X : TopCat.{u}) (Z : Set X) :
    TopCat.Sheaf (Type u) (TopCat.of Z) ⥤ TopCat.Sheaf (Type u) X :=
  TopCat.Sheaf.pushforward (Type u) (Stacks.subsetInclusion X Z)

/-- The inverse image functor `i⁻¹ : Sh(X) → Sh(Z)` on sheaves of sets, along the inclusion of
a subset `Z ⊆ X`. -/
@[ega "0 3.5.3" "partial, special case",
  ega "0 3.7.1" "special case",
  sga "4 IV 9.8.1" "special case"]
noncomputable def pullback00AF (X : TopCat.{u}) (Z : Set X) :
    TopCat.Sheaf (Type u) X ⥤ TopCat.Sheaf (Type u) (TopCat.of Z) :=
  TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion X Z)

/-- The adjunction `i⁻¹ ⊣ i_*` for the inclusion of a subset. -/
@[ega "0 3.7.1" "special case"]
noncomputable def pullbackPushforwardAdj (X : TopCat.{u}) (Z : Set X) :
    pullback00AF X Z ⊣ pushforward00AF X Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (Stacks.subsetInclusion X Z)

/-- A stalk is a singleton iff it carries a `Unique` structure. -/
def StalkIsSingleton (X : TopCat.{u}) (G : TopCat.Sheaf (Type u) X) (x : X) : Prop :=
  Nonempty (Unique (TopCat.Presheaf.stalk G.obj x))

/-- Having a singleton stalk at a point is invariant under isomorphism of sheaves. -/
lemma StalkIsSingleton.of_iso (X : TopCat.{u}) (G H : TopCat.Sheaf (Type u) X)
    (e : G ≅ H) (x : X) (h : StalkIsSingleton X G x) : StalkIsSingleton X H x := by
  obtain ⟨uG⟩ := h
  let stalkIso : TopCat.Presheaf.stalk G.obj x ≅ TopCat.Presheaf.stalk H.obj x :=
    (TopCat.Presheaf.stalkFunctor (Type u) x).mapIso
      ((TopCat.Sheaf.forget (Type u) X).mapIso e)
  exact ⟨Equiv.unique (α := TopCat.Presheaf.stalk H.obj x) stalkIso.symm.toEquiv⟩

/-! ### Full faithfulness -/

/-- The pushforward `i_* : Sh(Z) → Sh(X)` along the inclusion of any subset `Z ⊆ X` is fully
faithful. -/
noncomputable def pushforwardFullyFaithful (X : TopCat.{u}) (Z : Set X) :
    (pushforward00AF X Z).FullyFaithful :=
  ClosedImmersionSheaves.sheafPushforwardFullyFaithful (C := Type u)
    (Stacks.subsetInclusion_isInducing X Z)

/-- The pushforward of sheaves of sets along the inclusion of a subset is faithful. -/
@[stacks 00AF]
lemma pushforward_faithful (X : TopCat.{u}) (Z : Set X) : (pushforward00AF X Z).Faithful :=
  (pushforwardFullyFaithful X Z).faithful

/-- The pushforward of sheaves of sets along the inclusion of a subset is full: every morphism
`i_* F ⟶ i_* G` is `i_*` of a morphism `F ⟶ G`. -/
@[stacks 00AF]
lemma pushforward_full (X : TopCat.{u}) (Z : Set X) : (pushforward00AF X Z).Full :=
  (pushforwardFullyFaithful X Z).full

/-! ### Stalks of the pushforward outside `Z` -/

/-- For `Z` closed and `x ∉ Z`, the stalk `(i_* F)_x` is a singleton. -/
@[stacks 00AF, ega "IV 21.9.1" "special case"]
theorem pushforward_stalkIsSingleton_of_notMem
    (X : TopCat.{u}) {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf (Type u) (TopCat.of Z))
    (x : X) (hx : x ∉ Z) :
    StalkIsSingleton X ((pushforward00AF X Z).obj F) x :=
  ⟨Types.isTerminalEquivUnique _
    (ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange (Stacks.subsetInclusion X Z)
      F.property (Stacks.subsetInclusion_isClosedEmbedding X Z hZ) x
      (by rintro ⟨y, rfl⟩; exact hx y.2))⟩
