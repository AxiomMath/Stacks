module

public import Mathlib.CategoryTheory.Sites.Canonical
public import StacksCore.Tactic.StacksAttribute

/-! # Representable sheaves

## Main definitions

* `IsRepresentableSheaf`: a sheaf on a site with subcanonical topology is *representable* if
  it is isomorphic to `h_U` for some object `U`.

The Yoneda embedding `J.yoneda : C ⥤ Sheaf J (Type v)` of a subcanonical topology is full and
faithful by `CategoryTheory.GrothendieckTopology.yonedaFullyFaithful`.
-/

@[expose] public section

open CategoryTheory

universe u v

/-- A sheaf `F` on a site whose topology `J` is subcanonical is *representable* if it is
isomorphic to the sheaf `h_U = J.yoneda.obj U` for some object `U`. This is
`(GrothendieckTopology.yoneda J).essImage` with the witnessing isomorphism written the other way
round. -/
@[stacks 00WR, sga "4 I 1.4.1" "special case"]
def IsRepresentableSheaf {C : Type u} [Category.{v, u} C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    (F : Sheaf J (Type v)) : Prop :=
  ∃ U : C, Nonempty (F ≅ J.yoneda.obj U)

add_to_stacks 00WR "full subcategory of sheaves"
  CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "3 I 1.1" "special case" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "3 IV 4.5.1" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "4 II 4.4.0" "full faithfulness" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "4 V 2.4.1" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "4 VI 2.17" "more general" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "4 VI 3.11" "b)" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_sga "4 VII 2.1" "more general" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
add_to_ega "0 8.1.7" "more general" CategoryTheory.GrothendieckTopology.yonedaFullyFaithful
