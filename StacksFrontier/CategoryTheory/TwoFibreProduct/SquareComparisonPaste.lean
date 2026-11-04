module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# Cancelling the outer square of a pasted rectangle of categories

Paste two 2-commutative squares of categories side by side:
```
      a           a'
  C' ---> C  ----------> C''
  |       |               |
u |       | p             | p'
  v       v               v
  D' ---> D  ----------> D''
      b           b'
```
with fillers `α : a ⋙ p ≅ u ⋙ b` and `β : a' ⋙ p' ≅ p ⋙ b'`. The outer rectangle is a
2-commutative square over the cospan `(p', b ⋙ b')` whose filler is the pasted composite
`CategoryTheory.Limits.CategoricalPullback.pasteFiller`.

This file proves that, as soon as the *right-hand* square is 2-cartesian, the left-hand square
and the outer rectangle are 2-cartesian together: the comparison functor of the rectangle is the
comparison functor of the left square followed by an equivalence. That equivalence is the
composite of Stacks 02XB (3), which replaces `C` by `C'' ×_{D''} D` in the cospan, with the
cancellation `(A ×_B C) ×_C D ≌ A ×_B D` of Stacks 02XD.

Only the comparison functors of Stacks 003R are used; terminality in the category of
2-commutative squares is not, so no size or existence hypothesis appears.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.pasteFiller`: the filler of the outer rectangle.
* `CategoryTheory.Limits.CategoricalPullback.pasteCancel`: the functor `p ⊡ b ⥤ p' ⊡ (b ⋙ b')`
  through which the two comparison functors differ.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.squareComparisonPasteIso`: the comparison of the
  rectangle is the comparison of the left square followed by
  `CategoryTheory.Limits.CategoricalPullback.pasteCancel`.
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_pasteCancel`: that functor is an
  equivalence when the right-hand square is 2-cartesian.
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_paste_iff`: the
  left square and the outer rectangle are 2-cartesian together.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C' : Type u₁} {C : Type u₂} {C'' : Type u₃}
  {D' : Type u₄} {D : Type u₅} {D'' : Type u₆}
  [Category.{v₁} C'] [Category.{v₂} C] [Category.{v₃} C'']
  [Category.{v₄} D'] [Category.{v₅} D] [Category.{v₆} D'']
  (a : C' ⥤ C) (u : C' ⥤ D') (p : C ⥤ D) (b : D' ⥤ D) (α : a ⋙ p ≅ u ⋙ b)
  (a' : C ⥤ C'') (p' : C'' ⥤ D'') (b' : D ⥤ D'') (β : a' ⋙ p' ≅ p ⋙ b')

/-- **The filler of the pasted rectangle.** On an object `x` of `C'` it is the filler of the
right-hand square at `a x` followed by the image under `b'` of the filler of the left-hand
square at `x`. -/
def pasteFiller : (a ⋙ a') ⋙ p' ≅ u ⋙ b ⋙ b' :=
  NatIso.ofComponents (fun x => β.app (a.obj x) ≪≫ b'.mapIso (α.app x)) (by
    intro x y f
    have h₁ := β.hom.naturality (a.map f)
    have h₂ := α.hom.naturality f
    simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ ⊢
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [reassoc_of% h₁, ← b'.map_comp, ← b'.map_comp, h₂])

/-- The component of `CategoryTheory.Limits.CategoricalPullback.pasteFiller` at `x` is
`β.hom.app (a.obj x) ≫ b'.map (α.hom.app x)`. -/
@[simp] lemma pasteFiller_hom_app (x : C') :
    (pasteFiller a u p b α a' p' b' β).hom.app x =
      β.hom.app (a.obj x) ≫ b'.map (α.hom.app x) := rfl

/-- **The functor through which the two comparison functors differ.** It replaces `C` by the
explicit 2-fibre product `C'' ×_{D''} D` of the right-hand square (Stacks 02XB (3)) and then
cancels the middle factor (Stacks 02XD): on an object `(x, y, φ : p x ≅ b y)` of `p ⊡ b` it is
`(a' x, y, β_x ≫ b' φ)`. -/
def pasteCancel : p ⊡ b ⥤ p' ⊡ (b ⋙ b') :=
  CategoricalPullback.map p b (squareComparison a' p p' b' β) (𝟭 D') (𝟭 D)
      (π₂ p' b') b (Iso.refl b) (Iso.refl p) ⋙
    assocCompFunctor p' b' b

/-- The first component of `pasteCancel` on an object `X` is `a'.obj X.fst`. -/
@[simp] lemma pasteCancel_obj_fst (X : p ⊡ b) :
    ((pasteCancel p b a' p' b' β).obj X).fst = a'.obj X.fst := rfl

/-- The second component of `pasteCancel` on an object `X` is `X.snd`. -/
@[simp] lemma pasteCancel_obj_snd (X : p ⊡ b) :
    ((pasteCancel p b a' p' b' β).obj X).snd = X.snd := rfl

/-- The first component of `pasteCancel` on a morphism `f` is `a'.map f.fst`. -/
@[simp] lemma pasteCancel_map_fst {X Y : p ⊡ b} (f : X ⟶ Y) :
    ((pasteCancel p b a' p' b' β).map f).fst = a'.map f.fst := rfl

/-- The second component of `pasteCancel` on a morphism `f` is `f.snd`. -/
@[simp] lemma pasteCancel_map_snd {X Y : p ⊡ b} (f : X ⟶ Y) :
    ((pasteCancel p b a' p' b' β).map f).snd = f.snd := rfl

/-- The structural isomorphism of an object in the image of
`CategoryTheory.Limits.CategoricalPullback.pasteCancel`: the filler of the right-hand square
followed by the image under `b'` of the object's own. The two identities that
`CategoryTheory.Limits.CategoricalPullback.map` inserts at the unit comparisons are cancelled
here, so that the statement is in simp normal form. -/
@[simp] lemma pasteCancel_obj_iso_hom (X : p ⊡ b) :
    ((pasteCancel p b a' p' b' β).obj X).iso.hom =
      β.hom.app X.fst ≫ b'.map X.iso.hom := by
  show β.hom.app X.fst ≫ b'.map (𝟙 (p.obj X.fst) ≫ X.iso.hom ≫ 𝟙 (b.obj X.snd)) = _
  simp

/-- **Stacks 02XB (3) and Stacks 02XD.** The functor
`CategoryTheory.Limits.CategoricalPullback.pasteCancel` is an equivalence as soon as the
right-hand square is 2-cartesian, that is, as soon as its comparison functor is an
equivalence. -/
instance isEquivalence_pasteCancel [(squareComparison a' p p' b' β).IsEquivalence] :
    (pasteCancel p b a' p' b' β).IsEquivalence :=
  let : (CategoricalPullback.map p b (squareComparison a' p p' b' β) (𝟭 D') (𝟭 D)
      (π₂ p' b') b (Iso.refl b) (Iso.refl p)).IsEquivalence :=
    induced_isEquivalence_of_isEquivalence _ _ _ _ _
  let : (assocCompFunctor p' b' b).IsEquivalence :=
    inferInstanceAs (assocComp p' b' b).functor.IsEquivalence
  inferInstanceAs ((CategoricalPullback.map p b (squareComparison a' p p' b' β) (𝟭 D') (𝟭 D)
    (π₂ p' b') b (Iso.refl b) (Iso.refl p)) ⋙ assocCompFunctor p' b' b).IsEquivalence

/-- **The comparison functor of the outer rectangle factors through the left square's.** The
comparison of the rectangle is the comparison of the left-hand square followed by
`CategoryTheory.Limits.CategoricalPullback.pasteCancel`; the isomorphism is the identity in both
components, the two structural isomorphisms differing only by the identities that
`CategoryTheory.Limits.CategoricalPullback.map` inserts at the two unit comparisons. -/
def squareComparisonPasteIso :
    squareComparison a u p b α ⋙ pasteCancel p b a' p' b' β ≅
      squareComparison (a ⋙ a') u p' (b ⋙ b') (pasteFiller a u p b α a' p' b' β) :=
  NatIso.ofComponents
    (fun x => mkIso (Iso.refl _) (Iso.refl _) (by simp))
    (fun f => by refine CategoricalPullback.hom_ext ?_ ?_ <;> simp [mkIso])

/-- **The left-hand square and the outer rectangle are 2-cartesian together,** as soon as the
right-hand square is: the comparison functors of Stacks 003R differ by the equivalence
`CategoryTheory.Limits.CategoricalPullback.pasteCancel`. -/
theorem isEquivalence_squareComparison_paste_iff
    [(squareComparison a' p p' b' β).IsEquivalence] :
    (squareComparison (a ⋙ a') u p' (b ⋙ b')
        (pasteFiller a u p b α a' p' b' β)).IsEquivalence ↔
      (squareComparison a u p b α).IsEquivalence :=
  ⟨fun _ =>
    have := Functor.isEquivalence_of_iso (squareComparisonPasteIso a u p b α a' p' b' β).symm
    Functor.isEquivalence_of_comp_right _ (pasteCancel p b a' p' b' β),
    fun _ => Functor.isEquivalence_of_iso (squareComparisonPasteIso a u p b α a' p' b' β)⟩

/-! ### Changing the top functor of a square by an isomorphism

`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
transfers 2-cartesianness between two squares with the *same* top functor `a`. Two rectangles
obtained by pasting on the right are over cospans that only agree up to isomorphism, and so are
their top functors; the following is the missing half.
-/

section CongrTop

variable (a₂ : C' ⥤ C) (ia : a ≅ a₂)

/-- **The filler transported along an isomorphism of the top functor.** -/
def topIsoFiller : a₂ ⋙ p ≅ u ⋙ b :=
  Functor.isoWhiskerRight ia.symm p ≪≫ α

/-- The component of `topIsoFiller` at `x` is `p.map (ia.inv.app x) ≫ α.hom.app x`. -/
@[simp] lemma topIsoFiller_hom_app (x : C') :
    (topIsoFiller a u p b α a₂ ia).hom.app x = p.map (ia.inv.app x) ≫ α.hom.app x := rfl

/-- **Replacing the top functor of a square by an isomorphic one** and transporting the filler
leaves the comparison functor unchanged up to isomorphism: the isomorphism is `ia` in the
`C`-component and the identity in the `D'`-component. -/
def squareComparisonTopIso :
    squareComparison a u p b α ≅ squareComparison a₂ u p b (topIsoFiller a u p b α a₂ ia) :=
  NatIso.ofComponents
    (fun x => mkIso (ia.app x) (Iso.refl _) (by
      have h : p.map (ia.hom.app x) ≫ p.map (ia.inv.app x) = 𝟙 (p.obj (a.obj x)) := by
        rw [← p.map_comp, Iso.hom_inv_id_app, p.map_id]
      simp only [squareComparison_obj_iso, squareComparison_obj_snd, topIsoFiller_hom_app,
        Iso.app_hom, Iso.refl_hom, Functor.map_id, Category.comp_id, ← Category.assoc, h]
      exact Category.id_comp _))
    (fun f => by
      refine CategoricalPullback.hom_ext ?_ ?_ <;>
        simp [mkIso, ia.hom.naturality f])

/-- **2-cartesianness of a square only depends on its top functor up to isomorphism.** -/
theorem isEquivalence_squareComparison_congr_top :
    (squareComparison a u p b α).IsEquivalence ↔
      (squareComparison a₂ u p b (topIsoFiller a u p b α a₂ ia)).IsEquivalence :=
  Functor.isEquivalence_iff_of_iso (squareComparisonTopIso a u p b α a₂ ia)

end CongrTop

end CategoryTheory.Limits.CategoricalPullback

end
