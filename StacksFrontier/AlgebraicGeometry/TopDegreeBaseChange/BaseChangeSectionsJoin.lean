module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RestrictBaseUnitSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTransposeSections

/-!
# The two halves of the pure-tensor agreement of [Stacks, Tag 0EX3] (c), and their join

Conclusion (c) of [Stacks, Tag 0EX3] is reduced by
`…TopDegreeBaseChange.bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul` to a single
identity: the `Γ(Y'', W)`-linear map

> `ψ : Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V) ⟶ Γ(R^d f''_* (h')^* F', W)`

of `…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on the pure tensors
`1 ⊗ a`, the latter read at the pullback
`AlgebraicGeometry.Scheme.Modules.pullbackSection h (R^d f'_* F') V W` of the section `a`.

Both sides of that identity are now computed, each in its own file and each with no hypothesis
beyond the situation and the affineness of the two opens:

* the `ψ` side by `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul`
  (`RestrictBaseUnitSections.lean`), which sends `1 ⊗ a` to the value at `a` of [Stacks, Tag 01XK]
  over `V`, then `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`, then the identification
  of the right-hand end with the sections over `W`;
* the `γ⁺` side by `…TopDegreeBaseChange.topDirectImageBaseChangeMapPlus_app_pullbackSection`
  (`BaseChangeTransposeSections.lean`), which gives the restriction to `W` of the value over `V`
  of the transpose of `γ⁺`, written through the unit of `h^* ⊣ h_*`.

This file holds what is needed to put the two together.

## Main results

* `…TopDegreeBaseChange.upstairs_inv_comp_targetSections_hom`: **the Eilenberg-Watts object
  cancels out of the right-hand end of the `ψ` side.** Composing the inverse of
  `…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` with
  `…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` — of which it is the first factor —
  leaves the transport of the two readings of the scalars followed by [Stacks, Tag 01XK] over
  `W`, and no value of the endofunctor `Φ` of conclusion (b).
* `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_join`: **the
  pure-tensor agreement, granted the join** — the identity of the two computed right-hand sides.
  This is the form conclusion (c) consumes, with the one remaining geometric input isolated as a
  hypothesis.

## Implementation notes

*Why the join is isolated as a hypothesis.* What separates the two computed sides is a single
geometric identity: the unit occurring in the `ψ` side is that of the **restricted** adjunction
`(h' ∣)^* ⊣ (h' ∣)_*` over `f'⁻¹(V)`, inside
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`, whereas the one occurring in the `γ⁺` side
is that of `h^* ⊣ h_*` over `Y'` itself, together with the derived base change map of the square.
Relating them is the content of [Stacks, Tag 0EX3] (c) proper and is not bookkeeping; stating it as
a hypothesis here records exactly what is owed, and lets the reduction of the pure-tensor
agreement to it be checked on its own.

*No `@[stacks 0EX3]` attribute is placed.* What is here is the reduction of the pure-tensor
agreement to one geometric identity, not a conclusion of the tag.

## What the join still requires

Both **heads** of the join are proved, and they match:

* the `ψ` side's head is `Γ(V, R^d (f' ∣_ V)_* η)` for `η` the unit of the **restricted**
  adjunction, by `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_eq_sections`
  `_rightDerivedPlus_unit` (`OrdinaryPullbackUnitSections.lean`), conjugated by 01XK at the two
  coefficients, by `Stacks.DerivedIndexing.rightDerivedIso` and by the [Stacks, Tag 089W] Leray
  comparison `…TopDegreeBaseChange.cohomologyPullbackIsoPushforward`;
* the `γ⁺` side's head is `R^d f'_*` of the **ordinary** unit of `(h')^* ⊣ (h')_*`, by
  `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit`
  (`OrdinaryTopDegreeMate.lean`), with no hypothesis and with nothing in front of it;
* the two heads are identified by `…TopDegreeBaseChange.rightDerivedPlus_map_unit_resLE`
  (`TopDegreeHeadMatching.lean`) together with
  `…RestrictionSections.pullbackUnit_resLE_restrictUnit` (`Duality/ResLEUnitSections.lean`).

`BaseChangeSectionsTail.lean` performs the head matching: it cancels the two comparisons the `ψ`
side leads with against the computation of the pullback map on cohomology, and reads the `ψ` side
as the sections over `V` of the **ordinary** unit followed by a tail in which no unit occurs
(`…TopDegreeBaseChange.psi_side_eq_sections_unit_comp_tail`). With that and the `γ⁺` side's own
factorisation,
`…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_tail` discharges
**both** head-and-tail factorisations and reduces the pure-tensor agreement — the hypothesis
`join` below — to a single identity: the two tails agree. That identity is that theorem's
hypothesis `htail`, at the `Θ` and `T` which the two factorisation lemmas fix by unification when
they are handed to it, and `BaseChangeSectionsTail.lean`'s own implementation notes describe both
tails, the results its chase is assembled from, and what the chase still requires. Nothing in
this paragraph is a claim that the chase has been performed.

*The hypothesis `join` below is kept.* It is what
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isPullback_of_one_tmul` consumes, and
the sharper reduction lives in a module that imports this one.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The Eilenberg-Watts object cancels out of the right-hand end of the `ψ` side.**
`…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` is
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` followed by the transport of the
two readings of the scalars and by [Stacks, Tag 01XK] over `W`, so composing it with the inverse
of its own first factor leaves exactly those last two factors: not one value of the endofunctor
`Φ` of conclusion (b) survives on the right. -/
theorem upstairs_inv_comp_targetSections_hom :
    (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
      eqToHom (congrArg (fun ψ : (S.restrictBase V).affineBaseRing →+*
            Γ((f'' ⁻¹ᵁ W : Scheme), ⊤) =>
          (ModuleCat.restrictScalars ψ).obj
            (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
                ((Scheme.Modules.pullback h').obj F'))))
          (appTop_comp_eq_appTop_comp_algebraMap S h' f'' h hsq hWV).symm) ≫
        (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom)).map
          (targetSectionsIsoCohomology S F' h' f''
            (quasiCompact_of_isPullback S h' f'' h hsq)
            (quasiSeparated_of_isPullback S h' f'' h hsq) W).hom :=
  Iso.inv_hom_id_assoc _ _

/-- **The pure-tensor agreement of [Stacks, Tag 0EX3] (c), granted the join.** For a cartesian
square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, the map `ψ` of `…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on the
pure tensor `1 ⊗ a`, as soon as the two computed right-hand sides agree — the hypothesis `join`.

The `ψ` side is `…TopDegreeBaseChange.baseChangeSectionsMap_one_tmul`; the hypothesis is the one
geometric identity that remains, and the conclusion is what
`…TopDegreeBaseChange.bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul` consumes.

Neither `Y'` nor `Y''` carries a hypothesis; only the two opens are affine. -/
theorem baseChangeSectionsMap_one_tmul_eq_app_pullbackSection_of_join
    (join : ∀ a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V),
      (((affineOpenCohomologyIsoSectionsOf S.f' S.quasiCompact_f' S.quasiSeparated_f'
              (‹IsAffine (V : Scheme)› : IsAffineOpen V) F' inferInstance S.d).inv ≫
            (affineOpenCohomologyIsoRestrictBaseTopDegreeCohomology S V F').hom) ≫
          (ModuleCat.restrictScalars ((Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv :
              Γ(S.Y', V) →+* Γ((V : Scheme), ⊤))).map
            ((ModuleCat.restrictScalars (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤))).map
                (affineOpenCohomologyPullbackMap hsq hWV
                    (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d ≫
                  (ModuleCat.restrictScalars (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                      (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom).map
                    (restrictPullbackRightDerivedPlusIso h'
                      (preimage_le_preimage_of_isPullback hsq hWV) F' S.d).inv) ≫
              (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).inv ≫
                (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom) ≫
          (ModuleCat.restrictScalarsCongr (appLE_eq_comp_topIso S h hWV).symm).hom.app
            (ModuleCat.of Γ(Y'', W)
              Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
                ((Scheme.Modules.pullback h').obj F'), W))) a =
        (topDirectImageBaseChangeMapPlus S F' h' f'' h
            (toShHom_comm_of_isPullback h' f'' h hsq)).val.app (op W)
          (Scheme.Modules.pullbackSection h
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
            V W hWV a))
    (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)) :
    baseChangeSectionsMap S F' h' f'' h hsq hWV
        ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
      (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)).val.app (op W)
        (Scheme.Modules.pullbackSection h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
          V W hWV a) :=
  (baseChangeSectionsMap_one_tmul S F' h' f'' h hsq hWV a).trans (join a)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
