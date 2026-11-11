module

public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.TwoMorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExistence

/-!
# The morphism of topoi of a cocontinuous functor with a continuous right adjoint

Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be cocontinuous with right adjoint
`v : D ⥤ C`, and let `g : Sh(C) → Sh(D)` be the morphism of topoi attached to `u` (Stacks 00XO).
Stacks 00XY: if `v` is continuous then `v` defines a morphism of sites `f : C → D`, and the
morphism of topoi associated with `f` is `g`.

## Main definitions

* `CategoryTheory.Functor.sheafMorphismOfTopoiCocontinuous`: the morphism of topoi
  `g : Sh(C) → Sh(D)` of a cocontinuous functor `u` (Stacks 00XO), bundled, with `g_* = {}_su`,
  `g^{-1} = (u^p-)^#` and the adjunction of Stacks 00XL.
* `CategoryTheory.Adjunction.morphismOfTopoiPushforwardIsoOfIsCocontinuous`: for `u ⊣ v` with
  `u` cocontinuous and `v` continuous, the isomorphism `f_* ≅ g_*` between the pushforward of the
  morphism of topoi `f` of the morphism of sites defined by `v` and the pushforward of `g`.
* `CategoryTheory.Adjunction.morphismOfTopoiInverseImageIsoOfIsCocontinuous`: the isomorphism
  `g^{-1} ≅ f^{-1}` of inverse images conjugate to it.

## Main results

* `CategoryTheory.Adjunction.isMorphismOfSites_of_isLeftAdjoint` (in
  `StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExistence`): a continuous `v` with a
  left adjoint defines a morphism of sites `f : C → D`; cocontinuity of `u` is not needed.
* `CategoryTheory.Adjunction.morphismOfTopoi_adj_compatible_of_isCocontinuous`: the two
  isomorphisms above are compatible with the adjunctions `f^{-1} ⊣ f_*` and `g^{-1} ⊣ g_*`, so
  that `f = g` as morphisms of topoi: the pushforwards, the inverse images and the adjunction
  bijections `Mor(f^{-1}𝒢, ℱ) = Mor(𝒢, f_*ℱ)`, `Mor(g^{-1}𝒢, ℱ) = Mor(𝒢, g_*ℱ)` are all
  identified.

## Implementation notes

The two pushforwards are not literally equal functors: `f_* = v^s` is restriction along `v`
(`CategoryTheory.Functor.sheafPushforwardContinuous`) while `g_* = {}_su` is the right Kan
extension along `u` (Mathlib's `CategoryTheory.Functor.sheafPushforwardCocontinuous`), and
Stacks 00XX identifies them by the canonical bijection `(g_*F)(V) = F(v(V))`. The equality
`f = g` of the source is therefore the identification of the two morphisms of topoi by this
canonical isomorphism of pushforwards together with the conjugate isomorphism of inverse
images (`f^{-1} = v_s = g^{-1}` in the source's proof), which by construction transports the
adjunction of `f` to that of `g`: an invertible 2-morphism of topoi (Stacks 04IA) whose
inverse-image component is the one induced by the adjunctions.

Continuity of `v` is `CategoryTheory.Functor.IsContinuous`, the condition that restriction along
`v` take sheaves to sheaves, which is implied by the source's Definition 00WV (Stacks 00WW); the
hypothesis here is therefore the weaker one. Continuity of `u` is never used. As in Stacks 00X1
the topoi are sheaves of sets on small sites in one universe.

## References

* [Stacks 00XY](https://stacks.math.columbia.edu/tag/00XY); the computation of `g_*` is
  Stacks 00XX, the morphism of topoi of a morphism of sites is Stacks 00XC and that of a
  cocontinuous functor is Stacks 00XO.
-/

@[expose] public section

universe u

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The morphism of topoi `g : Sh(C) → Sh(D)` attached to a cocontinuous functor `u : C ⥤ D`
(Stacks 00XO), bundled: its pushforward is `g_* = {}_su`, Mathlib's
`Functor.sheafPushforwardCocontinuous`, its inverse image is `g^{-1} = (u^p-)^#`,
`Functor.sheafPullbackCocontinuous`, the adjunction is that of Stacks 00XL,
`Functor.sheafAdjunctionPullbackCocontinuous`, and `g^{-1}` is left exact by
`Functor.preservesFiniteLimits_sheafPullbackCocontinuous`. -/
noncomputable def Functor.sheafMorphismOfTopoiCocontinuous (u : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsCocontinuous J K] :
    MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)) where
  pushforward := u.sheafPushforwardCocontinuous (Type u) J K
  inverseImage := u.sheafPullbackCocontinuous (Type u) J K
  adj := u.sheafAdjunctionPullbackCocontinuous (Type u) J K
  preservesFiniteLimits := inferInstance

namespace Adjunction

variable {u : C ⥤ D} {v : D ⥤ C} (adj : u ⊣ v) [u.IsCocontinuous J K] [v.IsContinuous K J]

/-- **Stacks 00XY**, `f_* = g_*`. Let `u : C ⥤ D` be cocontinuous with continuous right adjoint
`v : D ⥤ C`. Then `v` defines a morphism of sites `f : C → D`
(`Adjunction.isMorphismOfSites_of_isLeftAdjoint`), and the pushforward `f_* = v^s` of its
morphism of topoi (Stacks 00XC) is identified with the pushforward `g_* = {}_su` of the morphism
of topoi `g` of the cocontinuous functor `u` (Stacks 00XO), by the canonical isomorphism
`(g_*F)(V) = F(v(V))` of Stacks 00XX (1). -/
@[stacks 00XY "f_* = g_*, where f is the morphism of topoi of the morphism of sites defined by
  v (constructed by Adjunction.isMorphismOfSites_of_isLeftAdjoint) and g that of the
  cocontinuous u; together with morphismOfTopoiInverseImageIsoOfIsCocontinuous and
  morphismOfTopoi_adj_compatible_of_isCocontinuous this is the equality f = g"]
noncomputable def morphismOfTopoiPushforwardIsoOfIsCocontinuous :
    (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi.pushforward ≅
      (u.sheafMorphismOfTopoiCocontinuous J K).pushforward :=
  (adj.sheafPushforwardCocontinuousIso (Type u)).symm

/-- **Stacks 00XY**, `f^{-1} = g^{-1}`. In the situation of
`morphismOfTopoiPushforwardIsoOfIsCocontinuous`, the inverse image `g^{-1} = (u^p-)^#` of the
morphism of topoi of `u` is identified with the inverse image `f^{-1} = v_s = (v_p-)^#` of the
morphism of topoi of the morphism of sites defined by `v`, by the isomorphism conjugate to the
identification `f_* ≅ g_*` of pushforwards under the adjunctions `f^{-1} ⊣ f_*` and
`g^{-1} ⊣ g_*`. -/
@[stacks 00XY "f^{-1} = v_s = g^{-1}, the conjugate of the identification f_* = g_*"]
noncomputable def morphismOfTopoiInverseImageIsoOfIsCocontinuous :
    (u.sheafMorphismOfTopoiCocontinuous J K).inverseImage ≅
      (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi.inverseImage :=
  (conjugateIsoEquiv
      (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi.adj
      (u.sheafMorphismOfTopoiCocontinuous J K).adj).symm
    (adj.morphismOfTopoiPushforwardIsoOfIsCocontinuous (J := J))

/-- The isomorphism `g^{-1} ≅ f^{-1}` of `morphismOfTopoiInverseImageIsoOfIsCocontinuous` is
the transformation of inverse images induced by the 2-morphism of topoi `f ⇒ g` given by the
isomorphism `f_* ≅ g_*` (`TwoMorphismOfTopoi.inverseImage`). -/
theorem morphismOfTopoiInverseImageIsoOfIsCocontinuous_hom :
    (adj.morphismOfTopoiInverseImageIsoOfIsCocontinuous (J := J)).hom =
      TwoMorphismOfTopoi.inverseImage
        (f := (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi)
        (g := u.sheafMorphismOfTopoiCocontinuous J K)
        (adj.morphismOfTopoiPushforwardIsoOfIsCocontinuous (J := J)).hom :=
  rfl

/-- **Stacks 00XY**, `f = g` as morphisms of topoi. Let `u : C ⥤ D` be cocontinuous with
continuous right adjoint `v : D ⥤ C`, let `f` be the morphism of topoi of the morphism of sites
defined by `v` and `g` that of the cocontinuous functor `u`. The identifications `f_* ≅ g_*`
(`morphismOfTopoiPushforwardIsoOfIsCocontinuous`) and `g^{-1} ≅ f^{-1}`
(`morphismOfTopoiInverseImageIsoOfIsCocontinuous`) identify the adjunctions as well: for sheaves
`𝒢` on `D` and `ℱ` on `C`, the bijection `Mor(𝒢, f_*ℱ) = Mor(f^{-1}𝒢, ℱ)` of `f` corresponds to
the bijection `Mor(𝒢, g_*ℱ) = Mor(g^{-1}𝒢, ℱ)` of `g`. -/
@[stacks 00XY "f = g: the identifications of pushforwards and inverse images are compatible
  with the adjunctions of f and g"]
theorem morphismOfTopoi_adj_compatible_of_isCocontinuous (𝒢 : Sheaf K (Type u))
    (ℱ : Sheaf J (Type u))
    (α : 𝒢 ⟶
      (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi.pushforward.obj
        ℱ) :
    ((u.sheafMorphismOfTopoiCocontinuous J K).adj.homEquiv 𝒢 ℱ).symm
        (α ≫ (adj.morphismOfTopoiPushforwardIsoOfIsCocontinuous (J := J)).hom.app ℱ) =
      (adj.morphismOfTopoiInverseImageIsoOfIsCocontinuous (J := J)).hom.app 𝒢 ≫
        ((adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi.adj.homEquiv
          𝒢 ℱ).symm α :=
  TwoMorphismOfTopoi.homEquiv_symm_comp
    (f := (adj.isMorphismOfSites_of_isLeftAdjoint (J := J) (K := K)).morphismOfTopoi)
    (g := u.sheafMorphismOfTopoiCocontinuous J K)
    (adj.morphismOfTopoiPushforwardIsoOfIsCocontinuous (J := J)).hom 𝒢 ℱ α

end Adjunction

end CategoryTheory
