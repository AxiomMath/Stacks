module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Pointwise left Kan extensions along an equivalence

If `L : C ⥤ D` is an equivalence of categories, then for every object `Y` of `D` the category
`CostructuredArrow L Y` has a terminal object, namely any isomorphism `L(X₀) ≅ Y`. Hence every
functor `F : C ⥤ H` has a pointwise left Kan extension along `L`, whatever the size of the
categories involved.

## Main results

* `CategoryTheory.Functor.isTerminal_costructuredArrow_mk_iso`: for a fully faithful `L`, an
  isomorphism `L(X₀) ≅ Y` is a terminal object of `CostructuredArrow L Y`.
* `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_isEquivalence`: pointwise left Kan
  extensions along an equivalence exist.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {H : Type*} [Category* H]
  (L : C ⥤ D)

/-- **For a fully faithful `L` and an isomorphism `e : L(X₀) ≅ Y`, the object `e` of
`CostructuredArrow L Y` is terminal.** -/
noncomputable def isTerminal_costructuredArrow_mk_iso [L.Full] [L.Faithful] {X₀ : C} {Y : D}
    (e : L.obj X₀ ≅ Y) : IsTerminal (CostructuredArrow.mk e.hom) :=
  IsTerminal.ofUniqueHom
    (fun f ↦ CostructuredArrow.homMk (L.preimage (f.hom ≫ e.inv)) (by simp))
    (fun f g ↦ by
      ext
      apply L.map_injective
      have hg := CostructuredArrow.w g
      dsimp at hg ⊢
      simp [← hg])

/-- **Pointwise left Kan extensions along an equivalence exist**, the indexing categories
`CostructuredArrow L Y` having terminal objects. -/
theorem hasPointwiseLeftKanExtension_of_isEquivalence [L.IsEquivalence] (F : C ⥤ H) :
    L.HasPointwiseLeftKanExtension F := fun Y ↦
  ⟨⟨⟨_, colimitOfDiagramTerminal
    (isTerminal_costructuredArrow_mk_iso L (L.objObjPreimageIso Y)) _⟩⟩⟩

end CategoryTheory.Functor

end
