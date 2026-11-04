module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# The intersection of two weak Serre classes

The intersection of two weak Serre subcategories of an abelian category is again a weak Serre
subcategory (**Stacks 0754**). This is immediate from the characterization of 02MO (2): a class
is weak Serre exactly when it is nonempty and contains the middle term of every five term exact
sequence whose other four terms belong to it, and both conditions pass to intersections.

The case used in **Stacks 07BC** is `Parasitic ∩ LQCoh^fbc`, the intersection of the Serre
subcategory of parasitic modules (**Stacks 0774**) with the weak Serre subcategory of locally
quasi-coherent modules with the flat base change property (**Stacks 0771**).

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_inf`: `P ⊓ Q` is a weak Serre class when `P`
  and `Q` are.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P Q : ObjectProperty C)

/-- **The intersection of two weak Serre classes is a weak Serre class.** It contains a zero
object, and the middle term of a five term exact sequence whose other four terms lie in both
classes lies in both, by **Stacks 02MO** (2) applied to each. -/
instance isWeakSerreClass_inf [P.IsWeakSerreClass] [Q.IsWeakSerreClass] :
    (P ⊓ Q).IsWeakSerreClass :=
  (isWeakSerreClass_iff_prop_obj₂_of_exact _).2
    ⟨⟨0, P.prop_of_isZero (isZero_zero C), Q.prop_of_isZero (isZero_zero C)⟩,
      fun S hS h₀ h₁ h₃ h₄ => ⟨P.prop_obj₂_of_exact S hS h₀.1 h₁.1 h₃.1 h₄.1,
        Q.prop_obj₂_of_exact S hS h₀.2 h₁.2 h₃.2 h₄.2⟩⟩

end CategoryTheory.ObjectProperty
