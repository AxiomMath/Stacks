module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The morphism of topoi of a cocontinuous functor, at the universe of a small model

A cocontinuous functor `v : C ⥤ D` between sites induces a morphism of topoi
`Sh(C) ⟶ Sh(D)`, by Stacks 00XL.  This file supplies that morphism for sheaves of sets in
`Type u` when the two sites are essentially small at `u` — the universe one needs when the
topoi are those underlying *ringed* topoi, since `AlgebraicGeometry.RingedTopos` declares its
topos at the universe of the sections of its structure sheaf, which for the sites of schemes is
one universe below their objects.

This is the cocontinuous counterpart of `isMorphismOfSites_of_essentiallySmall`, which does the
same for a continuous functor.  Unlike that one it needs no conjugation through the small model:
the constructions of `CategoryTheory.Functor.sheafPushforwardCocontinuous` and
`CategoryTheory.Functor.sheafAdjunctionCocontinuous` are already polymorphic in the universe of
the sections, and the only things they ask for at a chosen universe are sheafification and the
existence of the Kan extensions along `v.op`.  Essential smallness supplies both.

## Main results

* `CategoryTheory.Functor.hasPointwiseRightKanExtension_op_of_essentiallySmall` and
  `.hasPointwiseLeftKanExtension_op_of_essentiallySmall`: along the opposite of a functor
  between sites essentially small at `u`, every `Type u`-valued presheaf has pointwise right and
  left Kan extensions.
* `CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous_of_essentiallySmall`:
  restriction of sheaves of sets in `Type u` along such a functor is left exact.
* `CategoryTheory.Functor.morphismOfTopoi_of_isCocontinuous`: the morphism of topoi of a functor
  that is both cocontinuous and continuous, on sheaves of sets in `Type u`, with restriction as
  its inverse image.

## Implementation notes

For a functor that is both cocontinuous and continuous, Stacks 00XR (1) identifies the inverse
image of the morphism of topoi with *restriction* along the functor, and
`CategoryTheory.Functor.sheafAdjunctionCocontinuous` exhibits restriction as the left adjoint of
the cocontinuous direct image directly.  The morphism of topoi is therefore assembled from
restriction rather than from `CategoryTheory.Functor.sheafPullbackCocontinuous`: the two are
isomorphic, but restriction is the one given by a formula, so no sheafification intervenes in
the inverse image and the comparison of sections is the identity.

Left exactness of restriction is Stacks 00XR (3): restriction is the right adjoint of the lower
shriek functor.  Its hypotheses at the universe `u` are sheafification on the target site and
pointwise left Kan extensions along `v.op`, both supplied here from essential smallness.

## References

* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
  {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u} D]

/-- The comma categories indexing the right Kan extension along the opposite of a functor
between sites essentially small at `u` have `Type u`-valued limits: they are essentially small
at `u`, the source being essentially small and the target locally small there. -/
public instance hasLimitsOfShape_structuredArrow_op_of_essentiallySmall (v : C ⥤ D)
    (W : Dᵒᵖ) : HasLimitsOfShape (StructuredArrow W v.op) (Type u) :=
  have : EssentiallySmall.{u} (StructuredArrow W v.op) := inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The comma categories indexing the left Kan extension along the opposite of such a functor
have `Type u`-valued colimits, for the same reason. -/
public instance hasColimitsOfShape_costructuredArrow_op_of_essentiallySmall (v : C ⥤ D)
    (W : Dᵒᵖ) : HasColimitsOfShape (CostructuredArrow v.op W) (Type u) :=
  have : EssentiallySmall.{u} (CostructuredArrow v.op W) := inferInstance
  hasColimitsOfShape_of_essentiallySmall _ _

/-- Along the opposite of a functor between sites that are essentially small at `u`, every
`Type u`-valued presheaf has a pointwise right Kan extension. -/
public instance hasPointwiseRightKanExtension_op_of_essentiallySmall (v : C ⥤ D)
    (F : Cᵒᵖ ⥤ Type u) : v.op.HasPointwiseRightKanExtension F :=
  fun _ => inferInstance

/-- Along the opposite of a functor between sites that are essentially small at `u`, every
`Type u`-valued presheaf has a pointwise left Kan extension. -/
public instance hasPointwiseLeftKanExtension_op_of_essentiallySmall (v : C ⥤ D)
    (F : Cᵒᵖ ⥤ Type u) : v.op.HasPointwiseLeftKanExtension F :=
  fun _ => inferInstance

/-- **Stacks 00XR (3) at the universe of a small model.**  Restriction of sheaves of sets in
`Type u` along a continuous functor between sites essentially small at `u` is left exact: it is
the right adjoint of the lower shriek functor. -/
@[stacks 00XR "(3) at the universe of a small model",
  sga "4 III 1.8" "special case",
  sga "4½ Arcata 2.3.3" "left exactness of f_*"]
public instance preservesFiniteLimits_sheafPushforwardContinuous_of_essentiallySmall (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsContinuous J K] :
    PreservesFiniteLimits (v.sheafPushforwardContinuous (Type u) J K) :=
  let : HasSheafify K (Type u) := hasSheafifyEssentiallySmallSite _ _
  inferInstance

/-- **Stacks 00XL at the universe of a small model.**  A functor between two sites essentially
small at `u` which is both cocontinuous and continuous induces a morphism of topoi on sheaves of
sets in `Type u`, in the same direction as the functor.

Its direct image is the right Kan extension along `v.op`, and its inverse image is *restriction*
along `v`, which Stacks 00XR (1) identifies with the sheafified pullback and which Stacks
00XR (3) shows to be left exact. -/
@[stacks 00XL "the morphism of topoi of a cocontinuous functor, at the universe of a small model"]
public noncomputable def morphismOfTopoi_of_isCocontinuous (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsCocontinuous J K]
    [v.IsContinuous J K] :
    MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)) where
  pushforward := v.sheafPushforwardCocontinuous (Type u) J K
  inverseImage := v.sheafPushforwardContinuous (Type u) J K
  adj := v.sheafAdjunctionCocontinuous (Type u) J K
  preservesFiniteLimits := inferInstance

/-- The direct image of `morphismOfTopoi_of_isCocontinuous v J K` is
`v.sheafPushforwardCocontinuous (Type u) J K`, the right Kan extension along `v.op`. -/
@[simp]
public theorem morphismOfTopoi_of_isCocontinuous_pushforward (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsCocontinuous J K]
    [v.IsContinuous J K] :
    (morphismOfTopoi_of_isCocontinuous v J K).pushforward =
      v.sheafPushforwardCocontinuous (Type u) J K := rfl

/-- The inverse image of `morphismOfTopoi_of_isCocontinuous v J K` is, definitionally,
restriction `v.sheafPushforwardContinuous (Type u) J K` along `v`. -/
@[simp]
public theorem morphismOfTopoi_of_isCocontinuous_inverseImage (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsCocontinuous J K]
    [v.IsContinuous J K] :
    (morphismOfTopoi_of_isCocontinuous v J K).inverseImage =
      v.sheafPushforwardContinuous (Type u) J K := rfl

end CategoryTheory.Functor

end
