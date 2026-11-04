module

public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Reading a shift through a shift-compatible functor and a shift sequence

Let `G : C ⥤ D` commute with the shifts by `ℤ` and let `H : D ⥤ A` carry a shift sequence (for
instance the cohomology functors of a derived category). For `a + n' = n` there is a canonical
isomorphism `H_n(G X) ≅ H_{n'}(G(X⟦a⟧))`. This file records that these isomorphisms are
compatible with the composition of shifts: reading `X⟦a⟧` as `(X⟦c⟧)⟦b⟧` for `c + b = a`, the
isomorphism at `a` is the one at `c` followed by the one at `b`.

## Main definitions

* `CategoryTheory.Functor.shiftSequenceCommShiftIso`: `H_n(G X) ≅ H_{n'}(G(X⟦a⟧))`.

## Main results

* `CategoryTheory.Functor.shiftSequenceCommShiftIso_add`: the compatibility with `c + b = a`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

variable {C D A : Type*} [Category C] [Category D] [Category A] [HasShift C ℤ] [HasShift D ℤ]
  (G : C ⥤ D) [G.CommShift ℤ] (H : D ⥤ A) [H.ShiftSequence ℤ]

/-- **`H_n(G X) ≅ H_{n'}(G(X⟦a⟧))`** for `a + n' = n`: the shift sequence of `H` followed by the
commutation of `G` with the shift. -/
def shiftSequenceCommShiftIso (X : C) (a n n' : ℤ) (h : a + n' = n) :
    (H.shift n).obj (G.obj X) ≅ (H.shift n').obj (G.obj (X⟦a⟧)) :=
  ((H.shiftIso a n' n h).app (G.obj X)).symm ≪≫
    (H.shift n').mapIso ((G.commShiftIso a).app X).symm

/-- `shiftSequenceCommShiftIso` is natural in the object. -/
@[reassoc]
theorem shiftSequenceCommShiftIso_hom_naturality {X Y : C} (φ : X ⟶ Y) (a n n' : ℤ)
    (h : a + n' = n) :
    (H.shift n).map (G.map φ) ≫ (shiftSequenceCommShiftIso G H Y a n n' h).hom =
      (shiftSequenceCommShiftIso G H X a n n' h).hom ≫ (H.shift n').map (G.map (φ⟦a⟧')) := by
  simp only [shiftSequenceCommShiftIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc]
  rw [H.shiftIso_inv_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (G.commShiftIso a).inv.naturality φ

/-- **Compatibility with the composition of shifts**: for `c + b = a`, the isomorphism at `a`,
followed by the identification `X⟦a⟧ ≅ (X⟦c⟧)⟦b⟧` and the isomorphism at `b` read backwards, is
the isomorphism at `c`. -/
theorem shiftSequenceCommShiftIso_add (X : C) (a b c n n' n'' : ℤ) (hab : c + b = a)
    (h : a + n'' = n) (h' : c + n' = n) (h'' : b + n'' = n') :
    (shiftSequenceCommShiftIso G H X a n n'' h).hom ≫
        (H.shift n'').map (G.map ((shiftFunctorAdd' C c b a hab).hom.app X)) ≫
        (shiftSequenceCommShiftIso G H (X⟦c⟧) b n' n'' h'').inv =
      (shiftSequenceCommShiftIso G H X c n n' h').hom := by
  simp only [shiftSequenceCommShiftIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Category.assoc, G.commShiftIso_add' hab, CommShift.isoAdd'_inv_app, Functor.map_comp,
    H.shiftIso_add'_inv_app b c a hab n'' n' n h'' h' (G.obj X)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Functor.comp_obj, G.map_id, Category.id_comp, Category.comp_id]
  rw [H.shiftIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- `shiftSequenceCommShiftIso` read backwards: the commutation of `G` with the shift followed by
the shift sequence of `H`. -/
theorem shiftSequenceCommShiftIso_inv (Z : C) (a n n' : ℤ) (h : a + n' = n) :
    (shiftSequenceCommShiftIso G H Z a n n' h).inv =
      (H.shift n').map ((G.commShiftIso a).hom.app Z) ≫
        (H.shiftIso a n' n h).hom.app (G.obj Z) := by
  simp [shiftSequenceCommShiftIso]

/-- **Compatibility with the composition of shifts, through a composite functor**: for
`G = F ⋙ G'` and `c + b = a`, the isomorphism at `a` for `G`, followed by the identification
`F(X⟦a⟧) ≅ F(X⟦c⟧)⟦b⟧` and the isomorphism at `b` for `G'` read backwards, is the isomorphism at
`c` for `G`. -/
theorem shiftSequenceCommShiftIso_add_comp {C₂ : Type*} [Category C₂] [HasShift C₂ ℤ]
    (F : C ⥤ C₂) [F.CommShift ℤ] (G' : C₂ ⥤ D) [G'.CommShift ℤ] (X : C) (a b c n n' n'' : ℤ)
    (hab : c + b = a) (h : a + n'' = n) (h' : c + n' = n) (h'' : b + n'' = n') :
    (shiftSequenceCommShiftIso (F ⋙ G') H X a n n'' h).hom ≫
        (H.shift n'').map (G'.map (F.map ((shiftFunctorAdd' C c b a hab).hom.app X) ≫
          (F.commShiftIso b).hom.app (X⟦c⟧))) ≫
        (shiftSequenceCommShiftIso G' H (F.obj (X⟦c⟧)) b n' n'' h'').inv =
      (shiftSequenceCommShiftIso (F ⋙ G') H X c n n' h').hom := by
  rw [← shiftSequenceCommShiftIso_add (F ⋙ G') H X a b c n n' n'' hab h h' h'']
  congr 1
  rw [shiftSequenceCommShiftIso_inv, shiftSequenceCommShiftIso_inv,
    Functor.commShiftIso_comp_hom_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

/-- **A morphism into a shift, followed by an isomorphism of the target, on cohomology**: for
`t : T₀ ⟶ T₁`, `e : T₁ ⟶ T₂⟦b⟧` and an isomorphism `s : K ≅ T₂`, the shift map of
`G(t ≫ e ≫ s⁻¹⟦b⟧)` followed by `H(G s)` is `H(G t) ≫ H(G e)` followed by the isomorphism
`shiftSequenceCommShiftIso` at `b` read backwards. -/
theorem shiftMap_comp_shiftSequenceCommShiftIso {T₀ T₁ T₂ K : C} (t : T₀ ⟶ T₁) (b : ℤ)
    (e : T₁ ⟶ T₂⟦b⟧) (s : K ≅ T₂) (n n' : ℤ) (h : b + n = n') :
    H.shiftMap (G.map (t ≫ e ≫ (shiftFunctor C b).map s.inv) ≫ (G.commShiftIso b).hom.app K)
        n n' h ≫ (H.shift n').map (G.map s.hom) =
      (H.shift n).map (G.map t) ≫ (H.shift n).map (G.map e) ≫
        (shiftSequenceCommShiftIso G H T₂ b n' n h).inv := by
  rw [shiftSequenceCommShiftIso_inv]
  have hc := (G.commShiftIso b).hom.naturality s.inv
  simp only [Functor.comp_map] at hc
  simp only [Functor.shiftMap, Functor.map_comp, Category.assoc]
  congr 2
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc,
    H.shiftIso_hom_naturality_assoc, ← Functor.map_comp, ← G.map_comp, Iso.inv_hom_id, G.map_id,
    Functor.map_id, Category.comp_id]

/-- The commutation of a composite functor with the shift, written out at a morphism into a
shift. -/
theorem map_comp_commShiftIso_comp {C₂ : Type*} [Category C₂] [HasShift C₂ ℤ] (F : C ⥤ C₂)
    [F.CommShift ℤ] (G' : C₂ ⥤ D) [G'.CommShift ℤ] {K₀ K : C} (b : ℤ) (x : K₀ ⟶ K⟦b⟧) :
    G'.map (F.map x ≫ (F.commShiftIso b).hom.app K) ≫ (G'.commShiftIso b).hom.app (F.obj K) =
      (F ⋙ G').map x ≫ ((F ⋙ G').commShiftIso b).hom.app K := by
  rw [Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
  rfl

end CategoryTheory.Functor
