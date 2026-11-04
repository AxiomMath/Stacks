module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The pointwise limit formula for a right Kan extension, naturally in the functor extended

Mathlib's `CategoryTheory.Functor.ranObjObjIsoLimit` computes a right Kan extension at an object:
for `L : C ⥤ D`, a functor `F : C ⥤ H` with a pointwise right Kan extension along `L` and an
object `X` of `D`,

`(Ran_L F)(X) ≅ lim_{StructuredArrow X L} (proj ⋙ F)`.

That isomorphism is stated for one `F` at a time.  This file records that it is **natural in
`F`**, as an isomorphism of functors `(C ⥤ H) ⥤ H`.  Naturality is forced by
`CategoryTheory.Functor.ranObjObjIsoLimit_hom_π`, which reads the isomorphism against the
projections of the limit, together with the naturality of `Ran_L` and of its counit.

The naturality is what lets the formula be composed with isomorphisms of *functors* — for instance
to identify a direct image's sections over an object with a global sections functor, rather than
only its value on one sheaf.

## Main definitions

* `CategoryTheory.Functor.ranObjNatIsoLimit` — **`Ran_L(-)(X) ≅ lim_{StructuredArrow X L}` of the
  restriction**, as an isomorphism of functors of the functor extended.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (H : Type u₃)
  [Category.{v₃} H] (L : C ⥤ D) [∀ F : C ⥤ H, L.HasPointwiseRightKanExtension F] (X : D)
  [HasLimitsOfShape (StructuredArrow X L) H]

/-- **The pointwise limit formula for a right Kan extension, naturally in the functor extended**:
evaluating `Ran_L` at an object `X` of `D` is taking the limit over `StructuredArrow X L` of the
restriction along its projection.

On each `F : C ⥤ H` this is `CategoryTheory.Functor.ranObjObjIsoLimit`.  Naturality is checked
against the projections of the limit, where
`CategoryTheory.Functor.ranObjObjIsoLimit_hom_π` turns both sides into the restriction map of
`Ran_L F` followed by the counit of the Kan extension; the two then differ by the naturality of
`Ran_L` applied to the structure morphism `X ⟶ L(c)` and the naturality of the counit. -/
noncomputable def ranObjNatIsoLimit :
    L.ran ⋙ (evaluation D H).obj X ≅
      (whiskeringLeft _ _ H).obj (StructuredArrow.proj X L) ⋙ lim :=
  NatIso.ofComponents (fun F ↦ L.ranObjObjIsoLimit F X) (fun {F G} α ↦ by
    refine limit.hom_ext fun f ↦ ?_
    dsimp
    rw [Category.assoc, Category.assoc, limMap_π, ranObjObjIsoLimit_hom_π,
      ranObjObjIsoLimit_hom_π_assoc]
    dsimp
    rw [← Category.assoc, ← (L.ran.map α).naturality f.hom, Category.assoc]
    congr 1
    simpa using congr_app (L.ranCounit.naturality α) f.right)

end CategoryTheory.Functor

end
