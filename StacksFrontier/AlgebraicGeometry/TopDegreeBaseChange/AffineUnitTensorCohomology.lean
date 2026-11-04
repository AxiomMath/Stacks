module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineUnitTensorIdentity

/-!
# The pure-tensor identity of [Stacks, Tag 0EX3] (c), read in cohomology

`…TopDegreeBaseChange.tensorSheafUnitRightIso_inv_comp_tensorSheaf_map` is the sheaf-level form of
the identity conclusion (c) of [Stacks, Tag 0EX3] needs over a compatible pair of affine opens:
tensoring into the restriction of `F'` a map out of the structure sheaf of `f'⁻¹(V)` which is the
pullback of the canonical map of structure sheaves gives the unit of `(h' ∣)^* ⊣ (h' ∣)_*`, read
through the projection formula.

**This file applies `H^n(f'⁻¹(V), -)` to that identity.** The right-hand side then assembles into
the two declarations the computation of conclusion (c) is phrased with: the pullback map on
cohomology `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` and the right-hand end
`…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens`. So the Eilenberg-Watts side of
(c), which produces the left-hand side, meets the geometric side, which produces the right.

## Main results

* `…TopDegreeBaseChange.rightDerived_tensorSheafUnitRightIso_inv_comp_tensorSheaf_map`: **the
  identity in cohomology.** Neither base carries a hypothesis; only the two opens are affine, and
  the degree is arbitrary.
* `…TopDegreeBaseChange.comp_assoc_rewrite_head`: the reassociation it needs, at variables of an
  abstract category.

## Implementation notes

*Why the reassociation is hoisted.* The right-hand side is a four-fold composite whose first two
factors are known to compose to `H^n` of the unit
(`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom`)
and whose last two are what the sheaf identity produces. Rewriting with that at the concrete
spelling does not fire — the goal mixes `(F ⋙ L).obj G` with `L.obj (F.obj G)`, which are
definitionally but not syntactically equal — so the reassociation is stated at variables of an
abstract category, as the directory does for the same shape in
`…TopDegreeBaseChange.comp_assoc_cancel_middle`.

*The two readings of the Leray comparison agree on the nose.* The comparison inside
`cohomologyPullbackIsoTensorCohomologyAffineOpens` takes its affineness instance from
`hsq.flip`, the one inside `affineOpenCohomologyPullbackMap` from
`…TopDegreeBaseChange.isAffineHom_resLE_of_isPullback`; `AlgebraicGeometry.IsAffineHom` is a
`Prop`, so the two terms are the same by proof irrelevance and the unfolding below is `rfl`.

*No `@[stacks 0EX3]` attribute is placed.* What is proved is one step of the computation of
conclusion (c), not a conclusion of the tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A functor applied to a three-fold composite, with the head factor rewritten.** Stated at
variables of abstract categories, where both the splitting of the composite and the reassociation
are free. -/
theorem functor_map_three_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A₁ A₂ A₃ A₄ : C} (u : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (t : A₃ ⟶ A₄)
    {B : D} (a : G.obj A₁ ⟶ B) (i : B ⟶ G.obj A₂) (hu : a ≫ i = G.map u) :
    G.map (u ≫ p ≫ t) = a ≫ (i ≫ G.map p) ≫ G.map t := by
  rw [G.map_comp, G.map_comp, ← hu]
  simp only [Category.assoc]

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The pure-tensor identity of [Stacks, Tag 0EX3] (c) over a pair of affine opens, in
cohomology.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, a quasi-coherent `F'`
and any map `m` out of the structure sheaf of `f'⁻¹(V)` which is the pullback of the canonical
`𝒪_V ⟶ (h ∣_ V^W)_* 𝒪_W` of [Stacks, Tag 01I7], the degree-`n` cohomology of the map obtained by
tensoring `m` into the restriction of `F'` against the right unitor is the pullback map on
cohomology followed by the right-hand end of the computation.

This is `tensorSheafUnitRightIso_inv_comp_tensorSheaf_map` with `H^n(f'⁻¹(V), -)` applied to it:
the unit becomes `affineOpenCohomologyPullbackMap` by
`affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom`, and the projection
formula and the tilde crossing are the two remaining factors of
`cohomologyPullbackIsoTensorTildeAffineOpens`. -/
theorem rightDerived_tensorSheafUnitRightIso_inv_comp_tensorSheaf_map (n : ℕ)
    (m : Scheme.unitModule (S.f' ⁻¹ᵁ V : Scheme) ⟶
      (Scheme.Modules.pullback (S.f' ∣_ V)).obj
        ((Stacks.Coherent.affineTilde (V : Scheme)).obj
          ((_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).obj
            ((Scheme.Modules.pushforward (h.resLE V W hWV)).obj
              (Scheme.unitModule (W : Scheme))))))
    (hm : m = ((Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) ≫
      (Scheme.Modules.pullback (S.f' ∣_ V)).map
        (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) :
    ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
        ((tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
            (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ m)) =
      affineOpenCohomologyPullbackMap hsq hWV (preimage_le_preimage_of_isPullback hsq hWV) F'
          inferInstance n ≫
        (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV
          (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance n).hom := by
  have hunit := affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom
    hsq hWV (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance n
  have hsheaf := tensorSheafUnitRightIso_inv_comp_tensorSheaf_map S F' h' f'' h hsq hWV m hm
  have hmap : ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
      ((tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
              (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
          (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ m)) =
      ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived n).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))).unit.app
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ≫
          ((pushforwardPullbackTensorIsoRight (S.f' ∣_ V)
              (h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                (preimage_le_preimage_of_isPullback hsq hWV))
              (f'' ∣_ W) (h.resLE V W hWV) (isPullback_resLE_of_isPullback hsq hWV)
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
              (Scheme.Modules.isQuasicoherent_restrictFunctor (S.f' ⁻¹ᵁ V).ι F')).inv ≫
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                  (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
              (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                (Scheme.Modules.pullback (S.f' ∣_ V)).map
                  (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv))) :=
    congrArg ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived n).map hsheaf
  exact hmap.trans (functor_map_three_eq _ _ _ _ _ _ hunit)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
