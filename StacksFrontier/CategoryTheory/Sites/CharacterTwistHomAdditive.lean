module

public import StacksFrontier.CategoryTheory.Sites.CharacterTwist

/-!
# Maps out of the character twist form a group, additively

Let `C` be a site, let a group `G` act by automorphisms on an object `W` of `C` and let
`χ : G → ℤˣ` be a character. `CategoryTheory.characterTwistHomEquiv` identifies the maps `ℤ(χ) ⟶ F`
of abelian sheaves with the sections of `F` over `W` transforming according to `χ`. That
identification is evaluation at the class of the identity of `W`, so it is additive, and this file
records it as an isomorphism of abelian groups.

## Main definitions

* `CategoryTheory.characterTwistHomAddEquiv`: **`Hom(ℤ(χ), F) ≅ H⁰(W, F)^χ` as abelian groups.**

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (W : C) {G : Type w} [Group G] (act : G →* Aut W)
    (χ : G →* ℤˣ) (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- **A map `ℤ(χ) ⟶ F` of abelian sheaves is the same thing as a section of `F` over `W`
transforming according to the character `χ`, as abelian groups.** Its underlying equivalence is
`CategoryTheory.characterTwistHomEquiv`. -/
def characterTwistHomAddEquiv (F : Sheaf J AddCommGrpCat.{v}) :
    (characterTwist W act χ J ⟶ F) ≃+ characterSections W act χ F.obj :=
  AddEquiv.mk' (characterTwistHomEquiv W act χ J F) (by
    intro u u'
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_add, characterTwistHomEquiv_apply]
    rfl)

/-- The additive equivalence `characterTwistHomAddEquiv` applied to a map `ℤ(χ) ⟶ F` is
`characterTwistHomEquiv` applied to it. -/
@[simp]
lemma characterTwistHomAddEquiv_apply (F : Sheaf J AddCommGrpCat.{v})
    (u : characterTwist W act χ J ⟶ F) :
    characterTwistHomAddEquiv W act χ J F u = characterTwistHomEquiv W act χ J F u :=
  rfl

end CategoryTheory

end
