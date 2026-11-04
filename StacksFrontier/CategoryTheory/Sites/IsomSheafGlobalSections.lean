module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of the sheaf of isomorphisms

Let `(C, J)` be a site with a terminal object `T` and let `F`, `G` be two sheaves on it. The
sections of `Isom(F, G)` over `T` are the isomorphisms `F ≅ G`: a section over an object `X` is
an isomorphism of the restrictions of `F` and `G` to the slice site `C/X`, and over a terminal
object restriction to the slice is an equivalence of sheaf categories, so nothing is lost.

This is what turns a statement about the *sheaf* `Isom(F, G)` into a statement about the *set* of
isomorphisms of `F` and `G` — for instance Stacks Tag 093T (2), which computes `Isom_{Λ̲}(M̲, N̲)`
as the constant sheaf on the set of linear isomorphisms `M ≃ₗ[Λ] N`.

## Main results

* `Stacks.ConstantSheaf.overPullbackFullyFaithfulOfIsTerminal`: restriction to the slice over a
  terminal object is fully faithful.
* `Stacks.ConstantSheaf.isoEquivSheafIsomObjIsTerminal`: `(F ≅ G) ≃ Γ(T, Isom(F, G))`, carrying an
  isomorphism to the restriction of its underlying morphism.

## Implementation notes

Full faithfulness is read off
`CategoryTheory.GrothendieckTopology.sheafOverTerminalEquivalence`, whose functor *is*
`CategoryTheory.GrothendieckTopology.overPullback`. Both halves are used: fullness produces a
morphism of sheaves from a morphism of the restrictions, and faithfulness is what makes the two
composites of the produced morphism with the inverse the identity, so that a section of
`Isom(F, G)` — an invertible morphism of the restrictions — comes from an isomorphism and not
merely from a morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] {T : C}

/-- **Restriction to the slice site over a terminal object is fully faithful**, being the functor
of an equivalence of sheaf categories. -/
noncomputable def overPullbackFullyFaithfulOfIsTerminal (hT : IsTerminal T) :
    (J.overPullback A T).FullyFaithful :=
  (J.sheafOverTerminalEquivalence A hT).fullyFaithfulFunctor

/-- An isomorphism in a category is the same thing as a morphism which is invertible. -/
noncomputable def isoEquivSubtypeIsIso {D : Type*} [Category D] (P Q : D) :
    (P ≅ Q) ≃ { f : P ⟶ Q // IsIso f } where
  toFun e := ⟨e.hom, inferInstance⟩
  invFun f := @asIso _ _ _ _ f.1 f.2
  left_inv _ := Iso.ext rfl
  right_inv _ := Subtype.ext rfl

/-- **The isomorphisms of two sheaves are the sections of `Isom(F, G)` over a terminal object.**
A section over `T` is an invertible morphism of the restrictions to the slice site `C/T`, and
restriction to that slice is an equivalence of sheaf categories. -/
@[sga "3 I 1.7.2" "special case"]
noncomputable def isoEquivSheafIsomObjIsTerminal (hT : IsTerminal T) (F G : Sheaf J A) :
    (F ≅ G) ≃ (sheafIsom J A F G).obj.obj (op T) :=
  ((overPullbackFullyFaithfulOfIsTerminal J A hT).isoEquiv).trans
    (isoEquivSubtypeIsIso _ _)

/-- The identification of isomorphisms with sections of `Isom(F, G)` over a terminal object is
restriction of the underlying morphism to the slice site. -/
theorem isoEquivSheafIsomObjIsTerminal_coe (hT : IsTerminal T) (F G : Sheaf J A) (e : F ≅ G) :
    (isoEquivSheafIsomObjIsTerminal J A hT F G e).1 = (J.overPullback A T).map e.hom :=
  rfl

/-- The sections of `Isom_{Λ̲}(F, G)` over a terminal object are the isomorphisms of the two
sheaves of modules. -/
noncomputable def isoEquivModuleSheafIsomObjIsTerminal (Λ : Type w) [CommRing Λ]
    (hT : IsTerminal T) (F G : Sheaf J (ModuleCat.{max u v x} Λ)) :
    (F ≅ G) ≃ (moduleSheafIsom J Λ F G).obj.obj (op T) :=
  isoEquivSheafIsomObjIsTerminal J (ModuleCat.{max u v x} Λ) hT F G

end Stacks.ConstantSheaf

end
