module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.MorphismsOfTopoi

/-!
# Full faithfulness of the inverse image on algebraic spaces

A big fppf site contained in a larger one induces, after localizing at a scheme `S` of the
smaller site, an inverse image on sheaves of sets. The localized inclusion is cocontinuous,
continuous and fully faithful, so that inverse image is fully faithful, and hence so is the
functor it induces on the algebraic spaces over `S` defined using the smaller site.

## Main definitions

* `AlgebraicGeometry.changeBigSiteSheafPullback` — the inverse image along the localized
  inclusion, read on algebraic spaces over `S` and valued in sheaves on the larger site.

## Main results

* `AlgebraicGeometry.inclusionOver_full_and_faithful_sheafPullback` — the inverse image along
  the localized inclusion of big fppf sites is fully faithful.
* `AlgebraicGeometry.changeBigSiteSheafPullback_fullyFaithful` — the induced functor on
  algebraic spaces is fully faithful.

## Implementation notes

Full faithfulness is Stacks 00XU, whose hypotheses on the localized inclusion are all available
unconditionally: cocontinuity and continuity are Stacks 022K, fullness and faithfulness hold
because the inclusion is that of a full subcategory of schemes localized over `S`, and the
right-adjoint hypothesis is the existence of the inverse image.

Corestricting the inverse image to the algebraic spaces over `S` on the larger site is Stacks
03FP, part (2), which this library has only relative to effective descent along the covering
sieves at the monomorphisms locally of finite type. Nothing here needs that hypothesis, because
the functor is left valued in sheaves; the price is that the statements below are about that
sheaf-valued functor rather than about one landing in the algebraic spaces over `S` for the
larger site.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

private instance inclusionOver_isContinuous_overTopology :
    (inclusionOver h S hS).IsContinuous (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS)) :=
  (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous

private instance inclusionOver_sheafPushforwardContinuous_isRightAdjoint_overTopology :
    ((inclusionOver h S hS).sheafPushforwardContinuous (Type u) (overTopology .fppf B S hS)
      (overTopology .fppf B' S (largerContains h hS))).IsRightAdjoint :=
  inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS

/-- **Stacks 00XU for the localized inclusion of big fppf sites.** The inverse image along the
inclusion of the localization at `S` of a big fppf site into the localization of a larger one is
fully faithful on set-valued sheaves. -/
theorem inclusionOver_full_and_faithful_sheafPullback :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    (i.sheafPullback (Type u) J K).Full ∧ (i.sheafPullback (Type u) J K).Faithful := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  have : i.IsCocontinuous J K := inclusionOver_isCocontinuous (τ := .fppf) B B' h S hS
  have : i.Full := inclusionOver_full h S hS
  have : i.Faithful := inclusionOver_faithful h S hS
  have : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
    essentiallySmall_bigFppfOver B S hS
  have : ∀ F : (Over (base (τ := .fppf) B S hS))ᵒᵖ ⥤ Type u,
      i.op.HasPointwiseRightKanExtension F := by
    intro F Y
    have : HasLimitsOfShape (StructuredArrow Y i.op) (Type u) :=
      hasLimitsOfShape_of_essentiallySmall.{u} _ _
    show HasLimit (StructuredArrow.proj Y i.op ⋙ F)
    infer_instance
  exact Functor.full_and_faithful_sheafPullback i (Type u) J K

/-- Inverse image along the inclusion of localized big fppf sites, as a functor from the
algebraic spaces over `S` defined using the smaller site to the set-valued sheaves on the
larger one. -/
def changeBigSiteSheafPullback :
    AlgebraicSpaces B S hS ⥤
      Sheaf (overTopology .fppf B' S (largerContains h hS)) (Type u) := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  letI : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let toSheaf : AlgebraicSpaces B S hS ⥤ Sheaf J (Type u) :=
    ObjectProperty.ιOfLE fun _ hX => hX.isSheaf
  exact toSheaf ⋙ i.sheafPullback (Type u) J K

/-- **Stacks 04W1, full faithfulness**, with no descent hypothesis. Inverse image along the
inclusion of localized big fppf sites is fully faithful on the algebraic spaces over `S` defined
using the smaller site, as a functor into the sheaves on the larger site. -/
@[stacks 04W1 "full faithfulness, for the sheaf-valued inverse image"]
theorem changeBigSiteSheafPullback_fullyFaithful :
    Nonempty (changeBigSiteSheafPullback B B' h S hS).FullyFaithful := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  obtain ⟨hfull, hfaith⟩ := inclusionOver_full_and_faithful_sheafPullback B B' h S hS
  have : (i.sheafPullback (Type u) J K).Full := hfull
  have : (i.sheafPullback (Type u) J K).Faithful := hfaith
  unfold changeBigSiteSheafPullback
  exact ⟨(ObjectProperty.fullyFaithfulιOfLE _).comp
    (Functor.FullyFaithful.ofFullyFaithful (i.sheafPullback (Type u) J K))⟩

end AlgebraicGeometry

end
