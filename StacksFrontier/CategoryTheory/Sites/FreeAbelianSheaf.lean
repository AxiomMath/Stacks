module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The free abelian sheaf on a presheaf of sets

Let `C` be a site with Grothendieck topology `J` and let `G` be a presheaf of sets on `C`. The free
abelian presheaf `ℤ_G` on `G` is `U ↦ ℤ[G(U)]`, that is `G ⋙ AddCommGrpCat.free`; the *free
abelian sheaf* `ℤ_G^♯` on `G` is its sheafification. For an object `X` of `C`, the free abelian
sheaf on the representable presheaf `h_X` is written `ℤ_X^♯`.

## Main definitions

* `CategoryTheory.Presheaf.freeAbelianSheafObj`: the free abelian sheaf `ℤ_G^♯` on a presheaf of
  sets `G`.
* `CategoryTheory.Presheaf.freeAbelianSheafYoneda`: the free abelian sheaf `ℤ_X^♯` on the
  representable presheaf `h_X` of an object `X`.

## Main results

* `CategoryTheory.Presheaf.freeAbelianSheafObj_obj`: the underlying presheaf of `ℤ_G^♯` is the
  sheafification of the free abelian presheaf `U ↦ ℤ[G(U)]`.

## References

* [Stacks Project, Tag 03AA](https://stacks.math.columbia.edu/tag/03AA)
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section

variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The free abelian sheaf `ℤ_G^♯` on a presheaf of sets `G`: the sheafification of the free
abelian presheaf `U ↦ ℤ[G(U)]`. -/
@[stacks 03AA "Z_G^#, the sheafification of the free abelian presheaf U ↦ ℤ[G(U)]"]
noncomputable def freeAbelianSheafObj (G : Cᵒᵖ ⥤ Type w) : Sheaf J AddCommGrpCat.{w} :=
  (presheafToSheaf J AddCommGrpCat.{w}).obj (G ⋙ AddCommGrpCat.free)

/-- The underlying presheaf of the free abelian sheaf `ℤ_G^♯` is the sheafification of the free
abelian presheaf `U ↦ ℤ[G(U)]`. -/
lemma freeAbelianSheafObj_obj (G : Cᵒᵖ ⥤ Type w) :
    (freeAbelianSheafObj J G).obj = sheafify J (G ⋙ AddCommGrpCat.free) :=
  rfl

end

/-- The free abelian sheaf `ℤ_X^♯` on an object `X` of the site: the free abelian sheaf on the
representable presheaf `h_X`. -/
@[stacks 03AA "Z_X^#: the case G = h_X"]
noncomputable abbrev freeAbelianSheafYoneda [HasWeakSheafify J AddCommGrpCat.{v}] (X : C) :
    Sheaf J AddCommGrpCat.{v} :=
  freeAbelianSheafObj J (yoneda.obj X)

end CategoryTheory.Presheaf
