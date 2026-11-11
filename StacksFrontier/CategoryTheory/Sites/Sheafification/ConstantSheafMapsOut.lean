module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a constant sheaf

Stacks tag 0H7J: the constant sheaf `⟨E⟩` with value `E` on a site `(C, J)` is the
sheafification of the constant presheaf with value `E`, and it is characterized by the rule
that morphisms `⟨E⟩ ⟶ F` into a sheaf `F` are the same as maps of sets `E → Γ(C, F)`, where
`Γ(C, F) = Mor_{PSh(C)}(*, F)` are the global sections of Stacks 06UN.

The construction is Mathlib's `CategoryTheory.constantSheaf`. The characterization is
`CategoryTheory.constantSheafHomEquiv`, with `Γ(C, F)` taken to be
`CategoryTheory.Presheaf.globalSections`, the morphisms of presheaves out of the final presheaf.
It is assembled from the sheafification adjunction and the identification of morphisms out of a
constant presheaf with maps into sections, `CategoryTheory.Presheaf.constHomEquiv`.

## Main definitions

* `CategoryTheory.Presheaf.constHomEquiv`: morphisms from the constant presheaf with value `E`
  to `G` are the maps from `E` to the sections of `G`.
* `CategoryTheory.constantSheafHomEquiv`: morphisms `⟨E⟩ ⟶ F` are the maps `E → Γ(C, F)`.

## References

* [Stacks Project, Tag 0H7J](https://stacks.math.columbia.edu/tag/0H7J)
-/

@[expose] public section

add_to_stacks 0H7J "the constant sheaf" CategoryTheory.constantSheaf

namespace CategoryTheory

open Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C]

namespace Presheaf

/-- Morphisms from the constant presheaf with value `E` to a presheaf of sets `G` are the maps
from `E` to the sections of `G`. -/
@[simps]
def constHomEquiv (E : Type w) (G : Cᵒᵖ ⥤ Type w) :
    ((Functor.const Cᵒᵖ).obj E ⟶ G) ≃ (E → G.sections) where
  toFun τ e := ⟨fun U ↦ τ.app U e, fun {U V} f ↦
    (ConcreteCategory.congr_hom (τ.naturality f) e).symm⟩
  invFun s :=
    { app U := ↾fun e ↦ (s e).1 U
      naturality U V f := by
        ext e
        exact ((s e).2 f).symm }
  left_inv _ := rfl
  right_inv _ := rfl

end Presheaf

variable (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]

/-- Morphisms from the constant sheaf `⟨E⟩` with value `E` to a sheaf of sets `F` are the maps
from `E` to the global sections `Γ(C, F) = Mor_{PSh(C)}(*, F)` of `F`. -/
@[stacks 0H7J "Characterization of the constant sheaf by maps out of it."]
noncomputable def constantSheafHomEquiv (E : Type w) (F : Sheaf J (Type w)) :
    ((constantSheaf J (Type w)).obj E ⟶ F) ≃ (E → Presheaf.globalSections F.obj) :=
  ((sheafificationAdjunction J (Type w)).homEquiv _ F).trans
    ((Presheaf.constHomEquiv E F.obj).trans
      (Equiv.arrowCongr (Equiv.refl E) (Presheaf.globalSectionsEquivSections F.obj).symm))

end CategoryTheory
