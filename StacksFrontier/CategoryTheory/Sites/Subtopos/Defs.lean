module

public import StacksFrontier.CategoryTheory.Sites.Subtopos.Embedding
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Subtopoi

A strictly full subcategory of `Sh(C)` is modelled, as elsewhere in Mathlib, by an
`ObjectProperty (Sheaf J (Type w))`: the subcategory it spans has as objects the sheaves with
the property and all morphisms of `Sh(C)` between them.

## Main definitions

* `IsSubtopos`: such a subcategory is a *subtopos* when it is the essential image of the
  pushforward of an embedding of topoi `Sh(D) → Sh(C)` (Stacks 08LV). The site `D` is taken
  in the same universes as `C`.

## Main results

* `isSubtopos_essImage_pushforward`: the essential image of the pushforward of an embedding of
  topoi is a subtopos.

Tags covered: 08LV.
-/

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- **Stacks Project, Definition 7.43.2 (tag 08LV).**

A strictly full subcategory `E ⊆ Sh(C, J)`, given by the property `P` of its objects, is a
*subtopos* if there is an embedding of topoi `f : Sh(D, K) → Sh(C, J)`, for some site
`(D, K)`, whose pushforward has `E` as its essential image.

Since a subcategory of `Sh(C, J)` cut out by a property of objects is automatically strictly
full and closed under isomorphisms, no further condition on `P` is imposed; the equality
`f_*.essImage = P` already forces it.

The site `(D, K)` is quantified over the same universes as `(C, J)`. This is the case that
occurs in practice — in Stacks 08LY, for instance, `D` is `C` itself carrying a finer
topology — and it keeps the universe parameters of `IsSubtopos` determined by its
arguments. -/
@[stacks 08LV, sga "4 IV 9.1" "subtopos def", sga "4 IV 9.1.1" "b)"]
def IsSubtopos (J : GrothendieckTopology C) (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  ∃ (D : Type u) (_ : Category.{v} D) (K : GrothendieckTopology D)
    (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))),
    f.IsEmbedding ∧ f.pushforward.essImage = P

/-- The essential image of the pushforward of an embedding of topoi `Sh(D, K) → Sh(C, J)` is a
subtopos of `Sh(C, J)`. -/
theorem isSubtopos_essImage_pushforward {J : GrothendieckTopology C} {D : Type u}
    [Category.{v} D] {K : GrothendieckTopology D}
    {f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))} (hf : f.IsEmbedding) :
    IsSubtopos J f.pushforward.essImage :=
  ⟨D, inferInstance, K, f, hf, rfl⟩
