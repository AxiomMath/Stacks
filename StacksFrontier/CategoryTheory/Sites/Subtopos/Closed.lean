module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed subtopoi

## Main definitions

* `closedComplement`: for a sheaf `F` on `C`, the property of a sheaf `G` that the projection
  `F ⨯ G ⟶ F` is an isomorphism. For `F` a subsheaf of the final object this cuts out the
  strictly full subcategory of Stacks 08LY.
* `IsClosedSubtopos`: a strictly full subcategory of `Sh(C)` is a *closed subtopos* when it is
  `closedComplement F` for some subsheaf `F` of the final object (Stacks 08LZ).

Tags covered: 08LZ.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- For a sheaf `F` on `C`, `closedComplement F` is the property of a sheaf `G` that the
projection `F ⨯ G ⟶ F` is an isomorphism.

When `F` is a subsheaf of the final object `*` of `Sh(C)`, this is the strictly full
subcategory of `Sh(C)` singled out in Stacks 08LY, which that lemma shows to be a subtopos:
the closed subtopos complementary to the open subtopos `Sh(C)/F`. -/
@[sga "4 IV 9.3.4", sga "4 IV 9.3.5", sga "4 VI 4.1" "partial", sga "4½ Cycle 1.1.4"]
def closedComplement (F : Sheaf J (Type w)) : ObjectProperty (Sheaf J (Type w)) :=
  fun G => IsIso (prod.fst : F ⨯ G ⟶ F)

/-- **Stacks Project, Definition 7.43.6 (tag 08LZ).**

A strictly full subcategory `E ⊆ Sh(C, J)`, given by the property `P` of its objects, is a
*closed subtopos* if there is a subsheaf `F` of the final object of `Sh(C, J)` — that is, a
sheaf `F` whose map to the terminal object is a monomorphism — such that `E` is the subtopos
`closedComplement F` described in Stacks 08LY. -/
@[stacks 08LZ, sga "4 IV 9.3.1" "closed subtopos defn", sga "4 IV 9.3.5" "closed subtopos"]
def IsClosedSubtopos (J : GrothendieckTopology C) (P : ObjectProperty (Sheaf J (Type w))) :
    Prop :=
  ∃ F : Sheaf J (Type w), Mono (terminal.from F) ∧ closedComplement F = P
