module

public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.IteratedSlice

/-!
# Relocalizing the topos `Sh(C)` at a representable sheaf is relocalizing the site

Let `(C, J)` be a site and let `f : V ⟶ U` be a morphism of `C`.  There are two relocalization
triangles available:

* the one of diagram (04IK), coming from Stacks 03EH — the continuous, cocontinuous functor
  `j = Over.map f : C/V ⥤ C/U` and the triangle `j_V = j_U ∘ j` of localization morphisms of the
  site `C`;
* the one of Stacks 04IR — for a morphism of sheaves `s : G ⟶ F` on `C`, the localization `j` of
  the topos `Sh(C)/F` at the object `G/F`, whose inverse image is
  `Over.star (G/F) ⋙ iteratedSliceForward = Over.pullback s`
  (`CategoryTheory.starIteratedSliceForwardIsoPullback`) and whose lower shriek is
  `iteratedSliceBackward ⋙ Over.forget (G/F) = Over.map s` (`Over.iteratedSliceBackward_forget`).

Stacks 04IS says that when `G = h_V^#`, `F = h_U^#` and `s = h_f^#` comes from `f`, these two
triangles are identified via the identifications `Sh(C/V) = Sh(C)/h_V^#` and
`Sh(C/U) = Sh(C)/h_U^#` of Stacks 00Y1, and its proof is "this is true because the descriptions of
`j^{-1}` agree.  See 04IL and 04IR."  That is exactly what is done here: Stacks 04IL, in
`StacksFrontier.CategoryTheory.Sites.Localization.Relocalize`, describes the relocalization `j^{-1}`
and `j_!` of diagram (04IK) after the identification as base change along `h_f^#` and
postcomposition with `h_f^#`, and Stacks 04IR describes the topos-theoretic `j^{-1}` and `j_!` as
the very same two functors; composing the two descriptions gives the identification of the
triangles.

**Which direction of the identification is used.**  As in Stacks 04IL, the identification of
Stacks 00Y1 is used in its forward direction, as the functor
`Φ_U := CategoryTheory.OverShriek.sheafFunctorToOver J : Sh(C/U) ⥤ Sh(C)/h_U^#`.  Both statements
below are isomorphisms of composites in which `Φ_U` and `Φ_V` occur on one side only, so neither
depends on a choice of inverse for the equivalence.

The third face of the two triangles — that the outer morphisms agree, `j_V = j_U ∘ j` on the one
side and `j_{h_V^#} = j_{h_U^#} ∘ j` on the other — is Stacks 03EH together with Stacks 04IQ
(`StacksFrontier.CategoryTheory.Sites.Localization.ToposComparison`), which identifies `j_{h_U^#}`
with `j_U`; it is not restated here.

## Main results

* `CategoryTheory.OverShriek.relocalizeToposInverseImageIso` (Stacks 04IS): the inverse images of
  the two relocalizations agree.
* `CategoryTheory.OverShriek.relocalizeToposShriekIso` (Stacks 04IS): the lower shrieks agree.

Tags covered: 04IS.
-/

@[expose] public section

namespace CategoryTheory.OverShriek

open Limits Opposite

universe v u

-- As in Stacks 04IR: the slice `Sh(C)/h_U^#` has binary products because `Sh(C)` has pullbacks,
-- and that is what makes `Over.star` available on it.
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)] [HasWeakSheafify (J.over V) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]
  [((Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U)).IsRightAdjoint]

noncomputable section

/-- **Stacks 04IS**, on inverse images.  Under the identification of Stacks 00Y1, used in the
forward direction `Φ_U = sheafFunctorToOver J`, the inverse image `j^{-1}` of the relocalization
functor `j = Over.map f` of diagram (04IK) is the inverse image
`Over.star (h_V^#/h_U^#) ⋙ iteratedSliceForward` of the localization of the topos `Sh(C)/h_U^#` at
the object `h_V^#/h_U^#` of Stacks 04IR.

This is Stacks' proof: by Stacks 04IL the left-hand side is base change along `h_f^#`, and by
Stacks 04IR so is the right-hand side. -/
@[stacks 04IS "the inverse images of the two relocalizations agree, via 00Y1"]
def relocalizeToposInverseImageIso :
    (Over.map f).sheafPushforwardContinuous (Type v) (J.over V) (J.over U) ⋙
        sheafFunctorToOver (U := V) J ≅
      sheafFunctorToOver (U := U) J ⋙
        Over.star (Over.mk ((presheafToSheaf J (Type v)).map (yoneda.map f))) ⋙
          (Over.mk ((presheafToSheaf J (Type v)).map (yoneda.map f))).iteratedSliceForward :=
  inverseImageCompSheafFunctorToOverIso f J ≪≫
    Functor.isoWhiskerLeft (sheafFunctorToOver (U := U) J)
      (starIteratedSliceForwardIsoPullback
        ((presheafToSheaf J (Type v)).map (yoneda.map f))).symm

/-- **Stacks 04IS**, on lower shrieks.  Under the identification of Stacks 00Y1, used in the
forward direction `Φ_U = sheafFunctorToOver J`, the lower shriek `j_!` of the relocalization
functor `j = Over.map f` of diagram (04IK) is the lower shriek
`iteratedSliceBackward ⋙ Over.forget (h_V^#/h_U^#)` of the localization of the topos `Sh(C)/h_U^#`
at the object `h_V^#/h_U^#` of Stacks 04IR.

By Stacks 04IL the left-hand side is postcomposition with `h_f^#`, and by
`Over.iteratedSliceBackward_forget` — the identity underlying Stacks 04IR's description of `j_!` —
so is the right-hand side. -/
@[stacks 04IS "the lower shrieks of the two relocalizations agree, via 00Y1"]
def relocalizeToposShriekIso :
    (Over.map f).sheafPullback (Type v) (J.over V) (J.over U) ⋙ sheafFunctorToOver (U := U) J ≅
      sheafFunctorToOver (U := V) J ⋙
        (Over.mk ((presheafToSheaf J (Type v)).map (yoneda.map f))).iteratedSliceBackward ⋙
          Over.forget (Over.mk ((presheafToSheaf J (Type v)).map (yoneda.map f))) :=
  shriekCompSheafFunctorToOverIso f J ≪≫
    Functor.isoWhiskerLeft (sheafFunctorToOver (U := V) J)
      (eqToIso (Over.iteratedSliceBackward_forget
        (Over.mk ((presheafToSheaf J (Type v)).map (yoneda.map f)))).symm)

end

end CategoryTheory.OverShriek
