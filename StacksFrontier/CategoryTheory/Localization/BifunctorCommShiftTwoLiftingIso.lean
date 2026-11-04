module

public import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwo
import StacksCore.Tactic.StacksAttribute

/-!
# The lifting isomorphism of a bifunctor descended through two localizations

Let `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` be localization functors compatible with the shifts, and
let `G : C₁ ⥤ C₂ ⥤ E` be a bifunctor which commutes with the shifts in both variables and which
`G' : D₁ ⥤ D₂ ⥤ E` lifts in the sense of `CategoryTheory.Localization.Lifting₂`.
`CategoryTheory.Functor.CommShift₂.ofLocalization` equips `G'` with the descended two-variable
commutation.  This file proves that **the lifting isomorphism is itself compatible with those
shifts**, which is the two-variable analogue of Mathlib's
`CategoryTheory.NatTrans.commShift_iso_hom_of_localization`.

## Main results

* `CategoryTheory.Localization.lifting₂_iso_hom_app_commShift`: the component of the lifting
  isomorphism at an object of `C₁` commutes with the shift in the second variable.
* `CategoryTheory.Localization.lifting₂_iso_hom_commShift₂`: **the lifting isomorphism commutes
  with the shifts in both variables**, and `lifting₂_iso_hom_commShift₂Int` at the standard `ℤ`
  setup.

## Implementation notes

**Why this is the piece that was missing.**  A bifunctor obtained by descent reaches its
consumers only through its lifting isomorphism: every computation of it on the image of the two
localization functors — the K-flat comparison of [Stacks, Tag 06YU] is the example this file was
written for — is a composite in which that isomorphism is one factor.  A shift statement about
the descended bifunctor is therefore unusable until the isomorphism is known to be
shift-compatible, and that is *not* formally automatic: `CategoryTheory.Functor.CommShift₂` is
data, and the descended data is built from `CategoryTheory.Localization.bifunctorCommShiftIso`
rather than by transport along the lifting isomorphism.

What makes it true is `CategoryTheory.Localization.objCommShift_commShiftIso_hom_app_app`, which
computes the descended commutation isomorphism over the images of the two localization functors
as a four-factor composite whose two outer factors are the lifting isomorphism and its inverse.
The compatibility is then exactly the cancellation of those two factors against the ones the
equation of `CategoryTheory.NatTrans.CommShift` supplies — the same cancellation as in Mathlib's
one-variable `CategoryTheory.NatTrans.commShift_iso_hom_of_localization`, which is the proof
below in the second variable and, after `CategoryTheory.Localization.Lifting₂.flip`, in the
first.

**The two seats in the type.**  The source bifunctor of the lifting isomorphism is written
`(((whiskeringLeft₂ E).obj L₁).obj L₂).obj G'`, and `CategoryTheory.Functor.whiskeringLeft₂` is a
plain `def`: the term is definitionally `L₁ ⋙ (G' ⋙ (whiskeringLeft C₂ D₂ E).obj L₂)`, which is
the shape `CategoryTheory.Functor.CommShift₂.precomp₁` and `precomp₂` match, but instance search
does not unfold it and reports no instance.  Both statements below therefore seat the instance
with `inferInstanceAs` at the unfolded spelling, and the seat has to sit **in the type**: the
source and target `CategoryTheory.Functor.CommShift` data are instance arguments of
`CategoryTheory.NatTrans.CommShift`, so they are synthesized while the statement is elaborated
and a `haveI` in the proof is too late.  A consumer has to repeat the seat for the same reason.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor

namespace Localization

section App

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] {M : Type*} [AddMonoid M] [HasShift C₂ M] [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₂.CommShift M]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G']
  [∀ X₁ : C₁, (G.obj X₁).CommShift M]
  [∀ (X₁ Y₁ : C₁) (f : X₁ ⟶ Y₁), NatTrans.CommShift (G.map f) M]

/-- **The component of the lifting isomorphism at an object of `C₁` commutes with the shift in
the second variable**, for the descended structure of
`CategoryTheory.Localization.objCommShift`.

This is Mathlib's `CategoryTheory.NatTrans.commShift_iso_hom_of_localization` read through
`CategoryTheory.Localization.objCommShift_commShiftIso_hom_app_app`: the descended commutation
isomorphism over the images of the two localization functors is a composite whose outer two
factors are the lifting isomorphism and its inverse, and they cancel against the two factors the
equation supplies. -/
theorem lifting₂_iso_hom_app_commShift (X₁ : C₁) :
    letI := objCommShift (M := M) L₁ L₂ W₁ W₂ G G' (L₁.obj X₁)
    NatTrans.CommShift (F₁ := L₂ ⋙ G'.obj (L₁.obj X₁)) (F₂ := G.obj X₁)
      ((Lifting₂.iso L₁ L₂ W₁ W₂ G G').hom.app X₁) M := by
  let := objCommShift (M := M) L₁ L₂ W₁ W₂ G G' (L₁.obj X₁)
  constructor
  intro a
  ext X₂
  have hco := Functor.commShiftIso_comp_hom_app L₂ (G'.obj (L₁.obj X₁)) a X₂
  have hap := objCommShift_commShiftIso_hom_app_app L₁ L₂ W₁ W₂ G G' X₁ X₂ a
  -- the two components of the lifting isomorphism cancel, at the nesting the goal presents
  have key : ∀ Y : C₂, ((Lifting₂.iso L₁ L₂ W₁ W₂ G G').inv.app X₁).app Y ≫
      ((Lifting₂.iso L₁ L₂ W₁ W₂ G G').hom.app X₁).app Y = 𝟙 _ := fun Y => by
    simp
  dsimp at hco hap ⊢
  rw [hco, hap]
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.comp_id, Category.id_comp,
    Functor.comp_obj, key]

end App

section CommShiftTwo

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M]
  [HasShift D₂ M] [HasShift E M]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift M] [L₂.CommShift M]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G']
  (h : CommShift₂Setup E M) [G.CommShift₂ h]

/-- **The lifting isomorphism of a bifunctor descended through two localizations commutes with
the shifts in both variables**, for the descended structure
`CategoryTheory.Functor.CommShift₂.ofLocalization`.

Each half is `CategoryTheory.Localization.lifting₂_iso_hom_app_commShift`, in the second variable
at the components of the isomorphism and in the first at the components of its flip, which is
the lifting datum `CategoryTheory.Localization.Lifting₂.flip`. -/
theorem lifting₂_iso_hom_commShift₂ :
    letI := Functor.CommShift₂.ofLocalization L₁ L₂ W₁ W₂ G G' h
    letI : ((((whiskeringLeft₂ E).obj L₁).obj L₂).obj G').CommShift₂ h :=
      inferInstanceAs ((L₁ ⋙ (G' ⋙ (whiskeringLeft C₂ D₂ E).obj L₂)).CommShift₂ h)
    NatTrans.CommShift₂ (Lifting₂.iso L₁ L₂ W₁ W₂ G G').hom h :=
  let := Functor.CommShift₂.ofLocalization L₁ L₂ W₁ W₂ G G' h
  let : ((((whiskeringLeft₂ E).obj L₁).obj L₂).obj G').CommShift₂ h :=
    inferInstanceAs ((L₁ ⋙ (G' ⋙ (whiskeringLeft C₂ D₂ E).obj L₂)).CommShift₂ h)
  { commShift_app X₁ := lifting₂_iso_hom_app_commShift L₁ L₂ W₁ W₂ G G' X₁
    commShift_flipApp X₂ :=
      lifting₂_iso_hom_app_commShift L₂ L₁ W₂ W₁ G.flip G'.flip X₂ }

end CommShiftTwo

section Int

variable {C₁ C₂ D₁ D₂ E : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E] [Preadditive E] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [L₁.CommShift ℤ] [L₂.CommShift ℤ]
  (G : C₁ ⥤ C₂ ⥤ E) (G' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ G G'] [G.CommShift₂Int]

/-- `CategoryTheory.Localization.lifting₂_iso_hom_commShift₂` at the standard `ℤ` setup
`CategoryTheory.CommShift₂Setup.int`, with Mathlib's sign `(-1) ^ (p * q)`.  This is the form
every consumer asks for. -/
theorem lifting₂_iso_hom_commShift₂Int :
    letI := Functor.CommShift₂.ofLocalizationInt L₁ L₂ W₁ W₂ G G'
    letI : ((((whiskeringLeft₂ E).obj L₁).obj L₂).obj G').CommShift₂Int :=
      inferInstanceAs ((L₁ ⋙ (G' ⋙ (whiskeringLeft C₂ D₂ E).obj L₂)).CommShift₂Int)
    NatTrans.CommShift₂Int (Lifting₂.iso L₁ L₂ W₁ W₂ G G').hom :=
  lifting₂_iso_hom_commShift₂ L₁ L₂ W₁ W₂ G G' CommShift₂Setup.int

end Int

end Localization

end CategoryTheory

end
