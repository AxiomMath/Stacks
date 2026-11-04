module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineUnitTensorFactor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorUnitorSpellings

/-!
# The Eilenberg-Watts unit of (b) in cohomology is the pullback map on cohomology

Over a compatible pair of affine opens — `V` of `Y'` and `W` of `Y''` with `W ≤ h⁻¹(V)` — this
file composes the two halves of the pure-tensor identity of conclusion (c) of
[Stacks, Tag 0EX3]:

* the sheaf-level half, `…TopDegreeBaseChange.tensorSheaf_map_pullbackTildeUnit_comp`, which says
  the Eilenberg-Watts unit of conclusion (b) tensored into the restriction of `F'` is the pullback
  of the canonical map of structure sheaves of [Stacks, Tag 01I7];
* the cohomological half,
  `…TopDegreeBaseChange.rightDerived_tensorSheafUnitRightIso_inv_comp_tensorSheaf_map`, which says
  `H^n` of that pullback is the pullback map on cohomology followed by the right-hand end of the
  computation.

The result is the single morphism identity the Eilenberg-Watts side of (c) needs: **`H^d` of the
Eilenberg-Watts unit is `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` followed by
`…TopDegreeBaseChange.cohomologyPullbackIsoTensorTildeAffineOpens`.** It is stated at the
`Stacks.RingedSpace.tensorSheafUnitRightIso` spelling of the right unitor;
`…TopDegreeBaseChange.tensorFactorObjUnitIso_hom_eq` carries it to the spelling the geometric
factor of conclusion (b) produces.

## Main results

* `…TopDegreeBaseChange.rightDerived_tensorSheafUnitRightIso_inv_comp_pullbackTildeUnit`: the
  identity, at the `Stacks.RingedSpace.tensorSheafUnitRightIso` spelling of the right unitor.
  Neither base carries a hypothesis; only the two opens are affine, and the map out of the
  functions on `V` is a variable with the one property of it that is used.

## Implementation notes

*The map is a variable.* As in
`…TopDegreeBaseChange.pullbackTildeUnitIso_inv_comp_pullbackTildeSectionsIso`, the ring unit
`r ↦ r • 1` is taken as a variable `ψ` with the hypothesis that it is the canonical map of
structure sheaves on global sections. Writing it out here makes the elaborator rebuild the
restriction of scalars at a second spelling of the functions on `V`, where the module instance is
not found.

*Why the unitor is not written at the spelling of conclusion (b)'s geometric factor.*
`…TopDegreeBaseChange.tensorFactorObjUnitIso` applied at a concrete scheme over a concrete affine
base does not elaborate within the heartbeat limit — it is a braiding followed by a left unitor,
and the monoidal instance it is indexed by has to be reconstructed at each use. So the identity is
stated at the other spelling, and `tensorFactorObjUnitIso_hom_eq` is applied by the consumer, in
the elaboration where the geometric factor is being unfolded anyway.

*Why `(S.restrictBase V)` does not appear.* The value of the geometric factor of conclusion (b) at
a module is definitionally a tensor product of module sheaves on `f'⁻¹(V)`, but reconciling the
two spellings inside one elaboration exhausts the budget — the restricted situation is a `def`, so
its structure morphism does not unfold at the transparency the unifier uses on a composite this
size. So the identity is stated in the explicit spelling only, and the identification with the
functor of conclusion (b) is left to its consumer, which performs it as an equality of objects in
the manner of `…TopDegreeBaseChange.topDegreeFunctor_obj_eq`.

*No `@[stacks 0EX3]` attribute is placed.* This is one step of the computation of conclusion (c).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped CategoryTheory.Prod
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **`H^d` of the Eilenberg-Watts unit of [Stacks, Tag 0EX3] (b) is the pullback map on
cohomology**, at the `Stacks.RingedSpace.tensorSheafUnitRightIso` spelling of the right unitor.
For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)`, a quasi-coherent `F'`
and any map `ψ` out of the functions on `V` which is the canonical map of structure sheaves on
global sections, the degree-`d` cohomology of the Eilenberg-Watts unit tensored into the
restriction of `F'` is `affineOpenCohomologyPullbackMap` followed by the right-hand end
`cohomologyPullbackIsoTensorTildeAffineOpens` of the computation. -/
theorem rightDerived_tensorSheafUnitRightIso_inv_comp_pullbackTildeUnit
    (ψ : ModuleCat.of Γ((V : Scheme), ⊤) Γ((V : Scheme), ⊤) ⟶
      (ModuleCat.restrictScalars
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)).obj
          (ModuleCat.of Γ(Y'', W) Γ(Y'', W)))
    (hψ : ψ ≫ (sectionsIsoPushforwardUnitSections S h hWV).hom =
      (_root_.SheafOfModules.evaluation (V : Scheme).ringCatSheaf (op ⊤)).map
        (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) :
    ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
        ((tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
            ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
              (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                (Scheme.Modules.pullbackUnitIso
                  ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).inv) ≫
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                  (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
              (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
                  (AlgebraicGeometry.tildeSelf
                    (R := CommRingCat.of Γ((V : Scheme), ⊤))).inv) ≫
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                  (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
              (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                (Scheme.Modules.pullback ((S.f' ∣_ V) ≫ (V : Scheme).isoSpec.hom)).map
                  ((AlgebraicGeometry.tilde.functor
                    (CommRingCat.of Γ((V : Scheme), ⊤))).map ψ)) ≫
            (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.presheaf,
                  (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace.IsSheaf⟩)).map
              (𝟙 ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') ×ₘ
                (pullbackTildeSectionsIso S h hWV).hom)) =
      affineOpenCohomologyPullbackMap hsq hWV (preimage_le_preimage_of_isPullback hsq hWV) F'
          inferInstance S.d ≫
        (cohomologyPullbackIsoTensorTildeAffineOpens hsq hWV
          (preimage_le_preimage_of_isPullback hsq hWV) F' inferInstance S.d).hom := by
  have hm : (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV) ≫
            (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv) =
      ((Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫
          (Scheme.Modules.pullback (S.f' ∣_ V)).map
            (Scheme.Modules.unitToPushforwardUnit (h.resLE V W hWV))) ≫
        (Scheme.Modules.pullback (S.f' ∣_ V)).map
          (pushforwardUnitIsoAffineTilde (h.resLE V W hWV)).inv :=
    (congrArg (fun z => (Scheme.Modules.pullbackUnitIso (S.f' ∣_ V)).inv ≫ z)
      ((Scheme.Modules.pullback (S.f' ∣_ V)).map_comp _ _)).trans (Category.assoc _ _ _).symm
  refine Eq.trans (congrArg ((moduleGlobalSections (S.f' ⁻¹ᵁ V : Scheme)).rightDerived S.d).map
    (congrArg (fun z => (tensorSheafUnitRightIso (S.f' ⁻¹ᵁ V : Scheme).toRingedSpace
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')).inv ≫ z)
      (tensorSheaf_map_pullbackTildeUnit_comp S F' h hWV ψ hψ))) ?_
  exact rightDerived_tensorSheafUnitRightIso_inv_comp_tensorSheaf_map S F' h' f'' h hsq hWV S.d _ hm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
