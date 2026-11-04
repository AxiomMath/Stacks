module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Restricting a representable presheaf along a fully faithful functor

Let `K : C ⥤ E` be fully faithful, with `C` and `E` having their morphisms in the same
universe. Restricting the presheaf represented by `K.obj c` along `K` gives the presheaf
represented by `c`, and the identification is natural in `c`.

This is Yoneda's lemma for a full subcategory. The use it is written for is recognising a
diagram of presheaves on `C` obtained by restricting representables on `E` as a diagram of
representables on `C`, so that its colimit may be computed on `C`; the statement is therefore
an isomorphism of functors `C ⥤ Cᵒᵖ ⥤ Type v`, not a family of isomorphisms of presheaves.

## Main definitions

* `CategoryTheory.Functor.FullyFaithful.yonedaRestrictionIso`: the identification.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] {E : Type u} [Category.{v} E] {K : C ⥤ E}

/-- **Yoneda's lemma for a full subcategory.** For a fully faithful `K`, the presheaf
represented by `K.obj c` restricts along `K` to the presheaf represented by `c`, naturally
in `c`. -/
@[simps! hom_app_app]
def Functor.FullyFaithful.yonedaRestrictionIso (hK : K.FullyFaithful) :
    K ⋙ yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ Eᵒᵖ (Type v)).obj K.op ≅ yoneda :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦ hK.homEquiv.symm.toIso) (by
      intro _ _ _
      ext _
      apply hK.map_injective
      simp))
    (by
      intro _ _ _
      ext _ _
      apply hK.map_injective
      simp)

end CategoryTheory

end
