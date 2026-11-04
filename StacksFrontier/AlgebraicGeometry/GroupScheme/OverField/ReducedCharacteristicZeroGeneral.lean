/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReducedCrux
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Group schemes over a field of characteristic zero are reduced

This is [Stacks, Tag 047O] in full generality (Cartier's theorem in the form proved by Perrin): a
group scheme over a field of characteristic `0` is reduced, with no finiteness hypothesis.

The proof assembles two steps.  First,
`AlgebraicGeometry.isReduced_of_forall_isReduced_stalk_unit_of_irreducible` translates a point
to the unit after a field extension, base changes to a large algebraically closed field and
passes to the identity component.  Second,
`AlgebraicGeometry.isReduced_stalk_identity_of_irreducible_of_jacobson` treats an irreducible
Jacobson group with rational closed points: Perrin's approximation of the reduction by
quotients, the lifting lemma and the local Cartier theorem.

## Main results

* `AlgebraicGeometry.isReduced_of_grpObj_of_charZero`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 047O.**  Any group scheme over a field of characteristic `0` is
reduced (Perrin, thèse I 1.1, I 3.9, II 2.4; Bull. SMF 104, Prop. 4.2.8): a scheme `G` with a
group object structure on `f : G ⟶ Spec k` over `Spec k`, for `k` a field of characteristic
`0`, is reduced.  No finiteness assumption on `f` is made; the locally finite type case is
`AlgebraicGeometry.isReduced_of_groupScheme_of_charZero` ([Stacks, Tag 047N]). -/
@[stacks 047O,
  sga "3 VIA 6.9" "partial",
  sga "3 VIIA 8.5.1" "more general",
  sga "3 VIII 7.1" "more general"]
theorem isReduced_of_grpObj_of_charZero (k : Type u) [Field k] [CharZero k] (G : Scheme.{u})
    (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] : IsReduced G :=
  isReduced_of_forall_isReduced_stalk_unit_of_irreducible (Grp.mk (Over.mk f))
    fun Ω _ _ _ H h₁ h₂ hrat => by
      have := h₁
      have := h₂
      exact isReduced_stalk_identity_of_irreducible_of_jacobson Ω H hrat

end AlgebraicGeometry

end
