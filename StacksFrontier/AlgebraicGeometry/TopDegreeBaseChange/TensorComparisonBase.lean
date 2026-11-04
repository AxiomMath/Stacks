module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonAffineRigidity
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonRestrictSquares
public import StacksFrontier.CategoryTheory.Adjunction.DescendNatTrans

/-!
# Conclusion (b) of Tag 0EX3, over an arbitrary base

`TensorComparisonAffineRigidity.lean` proves conclusion (b) of [Stacks, Tag 0EX3] for a
top-degree base-change situation whose base is affine, and more: any natural transformation of
the two functors

> `G ↦ R^d f'_* F' ⊗_{𝒪_{Y'}} G`  and  `G ↦ R^d f'_*(F' ⊗_{𝒪_{X'}} (f')^* G)`

over an affine base, invertible at the structure sheaf, is invertible at every quasi-coherent
module.  This file removes the affineness of the base, which is the last hypothesis conclusion
(b) does not carry.

Invertibility of a morphism of quasi-coherent modules is local on the base
(`isIso_higherDirectImageTensorMap_of_isIso_restrict`) and the affine opens cover it, so it is
enough to invert the restriction of the canonical map to an affine open `V`.  Over `V` the
situation is `TopDegreeBaseChangeSituation.restrictBase`, whose base is `V` and whose
base-changed morphism is `f' ∣_ V`, and the two functors above commute with restriction
(`sourceRestrictIso`, `targetRestrictIso`).  Conjugating the restricted canonical map by those
two gives a natural transformation of the two functors of the *restricted* situation
precomposed with restriction; `CategoryTheory.Adjunction.descend` turns it into one of those two
functors themselves, because restriction is a left adjoint with invertible counit, and the
descent agrees with the conjugated map on every restricted module.

The descended transformation is invertible at the structure sheaf of `V`, because the
restriction of the structure sheaf of `Y'` is the structure sheaf of `V`
(`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`) and the canonical map at the structure
sheaf of `Y'` is invertible with no hypothesis at all.  The affine case therefore inverts it at
every quasi-coherent module of `V`, in particular at `G|_V`, which is where the descent is the
restriction of the canonical map at `G`.

So the restriction of the canonical map is invertible over every affine open, and the canonical
map is invertible.  Nothing is assumed of the base.

## Main definitions

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `restrictNatTrans`: the canonical map of conclusion (b) restricted to an open of the base, read
  through the two restriction squares as a transformation of the two functors of the restricted
  situation precomposed with restriction.
* `restrictBaseNatTrans`: its descent along the restriction adjunction, a transformation of the
  two functors of the restricted situation.

## Main results

* `restrictBaseNatTrans_app_restrict`: the descent at `G|_V` is `restrictNatTrans` at `G`.
* `isIso_restrictNatTrans_app` and `isIso_whiskerRight_app`: the restricted canonical map and
  the restriction of the canonical map invert together.
* `isIso_restrictBaseNatTrans_app_unitModule`: **the descent is invertible at the structure sheaf
  of `V`.**
* `isIso_restrictFunctor_map_higherDirectImageTensorMap`: **the canonical map of conclusion (b)
  restricts to an isomorphism over every affine open of the base.**
* `isIso_higherDirectImageTensorMap`: **conclusion (b) of [Stacks, Tag 0EX3]**, for a top-degree
  base-change situation with no hypothesis on its base.
* `topDirectImageTensorComparison`: the same, packaged as the isomorphism the tag asserts
  together with the canonicity condition that pins it down.

## Implementation notes

*Why the descent, rather than identifying the restriction of the canonical map with the
canonical map of the restricted morphism.*  The affine case is available for an arbitrary
transformation of the two functors, so the transformation produced over `V` does not have to be
recognised as a canonical map: it only has to be a natural transformation of the two functors of
the restricted situation, invertible at the structure sheaf.  Conjugating by the two restriction
squares gives a transformation of those functors *precomposed with restriction*, and the descent
of `CategoryTheory.Adjunction.descend` closes the gap exactly, its component at `G|_V` being the
conjugated map at `G` on the nose.  Identifying the restricted canonical map with the canonical
map of `f' ∣_ V` would be a statement about local pure tensors and higher direct images of
sections; none of it is needed.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable (S : TopDegreeBaseChangeSituation.{u}) (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (V : S.Y'.Opens)

/-! ### The canonical map over an open of the base -/

/-- **The canonical map of conclusion (b), restricted to an open `V` of the base and read
through the two restriction squares**: a natural transformation of the two functors of the
situation restricted to `V`, precomposed with restriction to `V`. -/
def restrictNatTrans :
    Scheme.Modules.restrictFunctor V.ι ⋙
        topDirectImageTensorLeftFunctor (S.f' ∣_ V)
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d ⟶
      Scheme.Modules.restrictFunctor V.ι ⋙
        topDirectImageTensorFunctor (S.f' ∣_ V)
          ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d :=
  (sourceRestrictIso S.f' V F' S.d).inv ≫
    Functor.whiskerRight (higherDirectImageTensorNatTrans S.f' F' S.d)
      (Scheme.Modules.restrictFunctor V.ι) ≫
    (targetRestrictIso S.f' V F' S.d).hom

omit [SheafOfModules.IsQuasicoherent F'] in
/-- The component of the restricted canonical map: the restriction of the canonical map at `G`,
conjugated by the two restriction squares. -/
theorem restrictNatTrans_app (G : S.Y'.Modules) :
    (restrictNatTrans S F' V).app G =
      (sourceRestrictIso S.f' V F' S.d).inv.app G ≫
        (Scheme.Modules.restrictFunctor V.ι).map (higherDirectImageTensorMap S.f' F' G S.d) ≫
          (targetRestrictIso S.f' V F' S.d).hom.app G := rfl

/-- **The restricted canonical map, descended along the restriction adjunction**: a natural
transformation of the two functors of the situation restricted to `V`.  Restriction is left
adjoint to the direct image along `V.ι` with invertible counit, so a transformation of the
precomposites descends. -/
def restrictBaseNatTrans :
    topDirectImageTensorLeftFunctor (S.f' ∣_ V)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d ⟶
      topDirectImageTensorFunctor (S.f' ∣_ V)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d :=
  CategoryTheory.Adjunction.descend (Scheme.Modules.restrictAdjunction V.ι)
    (restrictNatTrans S F' V)

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The descent at a restricted module is the restricted canonical map at the module**, on the
nose. -/
theorem restrictBaseNatTrans_app_restrict (G : S.Y'.Modules) :
    (restrictBaseNatTrans S F' V).app ((Scheme.Modules.restrictFunctor V.ι).obj G) =
      (restrictNatTrans S F' V).app G :=
  CategoryTheory.Adjunction.descend_app_obj (Scheme.Modules.restrictAdjunction V.ι)
    (restrictNatTrans S F' V) G

/-! ### The restricted canonical map and the canonical map invert together -/

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The restricted canonical map is invertible wherever the canonical map is**: its component
at `G` is the restriction of the canonical map at `G`, conjugated by the two restriction
squares. -/
theorem isIso_restrictNatTrans_app (G : S.Y'.Modules)
    (h : IsIso (higherDirectImageTensorMap S.f' F' G S.d)) :
    IsIso ((restrictNatTrans S F' V).app G) := by
  rw [restrictNatTrans_app]
  have := @Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.restrictFunctor V.ι) _ h
  infer_instance

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The canonical map whiskered into restriction is the restricted canonical map, conjugated
back by the two squares.**  Read in the category of functors from the modules of the base to
those of `V`, where `restrictNatTrans` is defined. -/
theorem whiskerRight_higherDirectImageTensorNatTrans_eq :
    Functor.whiskerRight (higherDirectImageTensorNatTrans S.f' F' S.d)
        (Scheme.Modules.restrictFunctor V.ι) =
      (sourceRestrictIso S.f' V F' S.d).hom ≫ restrictNatTrans S F' V ≫
        (targetRestrictIso S.f' V F' S.d).inv := by
  simp [restrictNatTrans]

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The restriction of the canonical map is invertible wherever the restricted canonical map
is**: the conjugation of `isIso_restrictNatTrans_app`, read the other way. -/
theorem isIso_whiskerRight_app (G : S.Y'.Modules)
    (h : IsIso ((restrictNatTrans S F' V).app G)) :
    IsIso ((Functor.whiskerRight (higherDirectImageTensorNatTrans S.f' F' S.d)
      (Scheme.Modules.restrictFunctor V.ι)).app G) := by
  rw [whiskerRight_higherDirectImageTensorNatTrans_eq]
  simp only [NatTrans.comp_app]
  infer_instance

/-! ### The base case over an open of the base -/

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The descended transformation is invertible at the structure sheaf of `V`.**  The
restriction of the structure sheaf of the base is the structure sheaf of `V`
(`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`), there the descent is the restricted
canonical map at the structure sheaf of the base, and the canonical map at the structure sheaf
is invertible with no hypothesis at all. -/
theorem isIso_restrictBaseNatTrans_app_restrict_unitModule :
    IsIso ((restrictBaseNatTrans S F' V).app
      ((Scheme.Modules.restrictFunctor V.ι).obj (Scheme.unitModule S.Y'))) := by
  rw [restrictBaseNatTrans_app_restrict]
  exact isIso_restrictNatTrans_app S F' V (Scheme.unitModule S.Y')
    (isIso_higherDirectImageTensorMap_unitModule S.f' F' S.d)

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The descended transformation is invertible at the structure sheaf of `V`.** -/
theorem isIso_restrictBaseNatTrans_app_unitModule :
    IsIso ((restrictBaseNatTrans S F' V).app (Scheme.unitModule (V : Scheme))) :=
  have e : (Scheme.Modules.restrictFunctor V.ι).obj (Scheme.unitModule S.Y') ≅
      Scheme.unitModule (V : Scheme) := Scheme.Modules.restrictUnitIso V.ι
  CategoryTheory.NatTrans.isIso_app_of_iso (restrictBaseNatTrans S F' V) e
    (isIso_restrictBaseNatTrans_app_restrict_unitModule S F' V)

/-! ### Conclusion (b) over an arbitrary base -/

/-- **Over an affine open of the base, a transformation of the two functors of the restricted
situation invertible at the structure sheaf of that open is invertible at every quasi-coherent
module.**  This is `isIso_app_of_isAffine_base` at the situation
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.restrictBase`, whose base is `V` and
whose base-changed morphism is `f' ∣_ V`.

The transformation is a *parameter*: that is what keeps the identification of the two spellings
of the restricted situation — `(S.restrictBase V).f'` against `S.f' ∣_ V`, which is
`TopDegreeBaseChangeSituation.restrictBase_f'` and holds by `rfl` — inside this one
declaration.  Given a transformation whose own definition the kernel can unfold, the same
application instead reduces that definition while deciding the two spellings agree, and the
budget is gone. -/
theorem isIso_app_of_isAffine_base_restrictBase [IsAffine (V : Scheme)]
    (τ : topDirectImageTensorLeftFunctor (S.f' ∣_ V)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d ⟶
      topDirectImageTensorFunctor (S.f' ∣_ V)
        ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F') S.d)
    (hτ : IsIso (τ.app (Scheme.unitModule (V : Scheme)))) (N : (V : Scheme).Modules)
    [hN : N.IsQuasicoherent] : IsIso (τ.app N) :=
  @isIso_app_of_isAffine_base (S.restrictBase V)
    (TopDegreeBaseChangeSituation.isAffine_restrictBase_Y' S V)
    ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F')
    (Scheme.Modules.isQuasicoherent_restrictFunctor (S.f' ⁻¹ᵁ V).ι F')
    τ hτ N hN

/-- **The descended transformation is invertible at the restriction of every quasi-coherent
module on the base.** -/
theorem isIso_restrictBaseNatTrans_app_restrict [IsAffine (V : Scheme)] (G : S.Y'.Modules)
    [G.IsQuasicoherent] :
    IsIso ((restrictBaseNatTrans S F' V).app ((Scheme.Modules.restrictFunctor V.ι).obj G)) :=
  have := Scheme.Modules.isQuasicoherent_restrictFunctor V.ι G
  isIso_app_of_isAffine_base_restrictBase S F' V (restrictBaseNatTrans S F' V)
    (isIso_restrictBaseNatTrans_app_unitModule S F' V)
    ((Scheme.Modules.restrictFunctor V.ι).obj G)

/-- **The canonical map of conclusion (b) of [Stacks, Tag 0EX3] restricts to an isomorphism over
every affine open of the base.**  Over an affine open the situation restricts to one with affine
base, the descended transformation is invertible at the structure sheaf, and the affine case
inverts it at every quasi-coherent module — in particular at `G|_V`, where it is the restricted
canonical map at `G`. -/
theorem isIso_restrictFunctor_map_higherDirectImageTensorMap [IsAffine (V : Scheme)]
    (G : S.Y'.Modules) [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (higherDirectImageTensorMap S.f' F' G S.d)) := by
  have hb := isIso_restrictBaseNatTrans_app_restrict S F' V G
  rw [restrictBaseNatTrans_app_restrict] at hb
  exact isIso_whiskerRight_app S F' V G hb

/-- **Conclusion (b) of [Stacks, Tag 0EX3].**  For a top-degree base-change situation, a
quasi-coherent module `F'` on `X'` and a quasi-coherent module `G` on the base `Y'`, the
canonical map

`R^d f'_* F' ⊗_{𝒪_{Y'}} G ⟶ R^d f'_*(F' ⊗_{𝒪_{X'}} (f')^* G)`

is an isomorphism.  The base carries no hypothesis: invertibility is local on it, the affine
opens cover it, and over an affine open the Eilenberg-Watts argument of
`TensorComparisonAffineRigidity.lean` applies to the restricted canonical map. -/
@[stacks 0EX3 "(b)"]
theorem isIso_higherDirectImageTensorMap (G : S.Y'.Modules) [G.IsQuasicoherent] :
    IsIso (higherDirectImageTensorMap S.f' F' G S.d) :=
  isIso_higherDirectImageTensorMap_of_isIso_restrict S.f' F' G S.d
    (fun W : S.Y'.affineOpens => (W : S.Y'.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top S.Y'))
    fun W =>
      have : IsAffine ((W : S.Y'.Opens) : Scheme) := W.2
      isIso_restrictFunctor_map_higherDirectImageTensorMap S F' (W : S.Y'.Opens) G

/-- **Conclusion (b) of [Stacks, Tag 0EX3], as the isomorphism the tag asserts.**  For a
top-degree base-change situation and quasi-coherent modules `F'` on `X'` and `G` on the base,

`R^d f'_*(F' ⊗_{𝒪_{X'}} (f')^* G) ≅ R^d f'_* F' ⊗_{𝒪_{Y'}} G`,

whose inverse satisfies the canonicity condition
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap` of the tag, so by
`eq_of_isHigherDirectImageTensorMap` it is the only candidate. -/
@[stacks 0EX3 "(b)"]
def topDirectImageTensorComparison (G : S.Y'.Modules) [G.IsQuasicoherent] :
    { e : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨S.X'.toRingedSpace.presheaf, S.X'.toRingedSpace.IsSheaf⟩).obj F').obj
              ((Scheme.Modules.pullback S.f').obj G))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.Y'.toRingedSpace.presheaf, S.Y'.toRingedSpace.IsSheaf⟩).obj
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')).obj G) //
      IsHigherDirectImageTensorMap S.f' F' G S.d e.inv } :=
  haveI := isIso_higherDirectImageTensorMap S F' G
  topDirectImageTensorComparisonOfIsIso' S.f' F' G S.d

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
