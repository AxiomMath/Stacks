module

public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Local

/-!
# Coherence and reflexivity of a restriction along an arbitrary open immersion

The reduction to the affine case in the proof of
[Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) produces an open immersion that is
not the inclusion of an open subscheme on the nose — it is the restriction `j ∣_ V` of the
inclusion `j : U ⟶ X` over an affine open `V` of `X`.  So the statements the reduction needs are
wanted for an arbitrary open immersion.

Reflexivity of a restriction is available in the tree as
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_pullback_of_opens`, clause (2) of
Tag 0EBF, which assumes the scheme **integral**.  That is more than the statement needs and more
than is available here: an open subscheme of an integral scheme is integral only when it is
nonempty, and nothing in the reduction supplies that.  Reflexivity of a *restriction along an
open immersion* is a pointwise statement about stalks, with no integrality anywhere, and that is
what is proved here: the stalk of `F|_W` at `w` and the stalk of `F` at `j w` are modules over
isomorphic local rings, compatibly, so one is reflexive exactly when the other is.

## Main results

* `module_isReflexive_modStalk_restrict`: the converse of
  `module_isReflexive_modStalk_of_restrict` — reflexivity of a stalk descends along an open
  immersion as well as ascending.
* `isCoherent_restrict_of_isOpenImmersion` and `isReflexive_restrict_of_isOpenImmersion`:
  coherence and reflexivity pass to the restriction along an arbitrary open immersion, with no
  integrality hypothesis.
* `pushforwardIsoRestrictInverse`: the direct image along an isomorphism of schemes is the
  restriction along its inverse.

## Implementation notes

`module_isReflexive_modStalk_restrict` is `Module.IsReflexive.of_ringEquiv` applied to the
*inverses* of the two equivalences `module_isReflexive_modStalk_of_restrict` uses; the scalar
compatibility for the inverses follows from the compatibility for the originals by applying the
additive equivalence to both sides.  The docstring of `Module.IsReflexive.of_ringEquiv` already
records that this makes the transfer an equivalence.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X W : Scheme.{u}}

/-- **Reflexivity of a stalk descends along an open immersion.**  If the stalk of `F` at `j w` is
a reflexive `𝒪_{X, j w}`-module then the stalk of `F|_W` at `w` is a reflexive
`𝒪_{W, w}`-module.

This is the converse of `module_isReflexive_modStalk_of_restrict`, obtained from the same two
equivalences by inverting both. -/
public theorem module_isReflexive_modStalk_restrict (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W)
    (h : Module.IsReflexive (ringStalk X.sheaf (j w)) (modStalk F (j w))) :
    Module.IsReflexive (ringStalk W.sheaf w) (modStalk (F.restrict j) w) :=
  let := h
  Module.IsReflexive.of_ringEquiv (restrictStalkRingEquiv j w).symm
    (restrictStalkAddEquiv j F w).symm (by
      intro r m
      refine (restrictStalkAddEquiv j F w).injective ?_
      have hs := restrictStalkHom_smul j F w ((restrictStalkRingEquiv j w).symm r)
        ((restrictStalkAddEquiv j F w).symm m)
      rw [AddEquiv.apply_symm_apply]
      rw [show (restrictStalkAddEquiv j F w)
            ((restrictStalkRingEquiv j w).symm r • (restrictStalkAddEquiv j F w).symm m) =
          restrictStalkRingEquiv j w ((restrictStalkRingEquiv j w).symm r) •
            (restrictStalkAddEquiv j F w) ((restrictStalkAddEquiv j F w).symm m) from hs]
      rw [RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])

/-- **Coherence passes to the restriction along an open immersion.**  Restriction is the pullback
along the immersion, and coherence of a pullback needs only local Noetherianity of the source. -/
public theorem isCoherent_restrict_of_isOpenImmersion (j : W ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] (F : X.Modules) (hFcoh : F.IsCoherent) :
    (F.restrict j).IsCoherent :=
  let : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion j
  let := hFcoh
  let := AlgebraicGeometry.isCoherent_pullback j F
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := W.ringCatSheaf)
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F)

/-- **Reflexivity passes to the restriction along an open immersion**, with no integrality
hypothesis.  Reflexivity of a coherent module is a condition on stalks ([Stacks, Tag 0AY3]), and
the stalks of `F|_W` are the stalks of `F` at the points of the image. -/
public theorem isReflexive_restrict_of_isOpenImmersion (j : W ⟶ X) [IsOpenImmersion j]
    [IsLocallyNoetherian X] (F : X.Modules) (hFcoh : F.IsCoherent) (hF : IsReflexive F) :
    IsReflexive (F.restrict j) := by
  have := hFcoh
  have hWN : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion j
  have hWcoh : (F.restrict j).IsCoherent := isCoherent_restrict_of_isOpenImmersion j F hFcoh
  have hstalk := ((isReflexive_tfae X F).out 1 2).mp hF
  exact ((isReflexive_tfae W (F.restrict j)).out 1 2).mpr fun w =>
    module_isReflexive_modStalk_restrict j F w (hstalk (j w))

/-- **The direct image along an isomorphism of schemes is the restriction along its inverse.** -/
public noncomputable def pushforwardIsoRestrictInverse (e : W ≅ X) (F : W.Modules) :
    (Scheme.Modules.pushforward e.hom).obj F ≅ F.restrict e.inv :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app
      ((Scheme.Modules.pushforward e.hom).obj F)).symm ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso
      ((Scheme.Modules.pushforwardComp e.hom e.inv).app F ≪≫
        (Scheme.Modules.pushforwardCongr e.hom_inv_id).app F ≪≫
        (Scheme.Modules.pushforwardId W).app F)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
