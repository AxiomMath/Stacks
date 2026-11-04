module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTopDegreeConclusion
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionStalkVanishing

/-!
# Tag 0E7D with every conclusion of Tag 0EX3

[Stacks, Tag 0E7D] fixes a proper morphism `f : X ⟶ Y` and a point `y ∈ Y` with `dim(X_y) = d`,
and asserts

1. `(Rⁱ f_* F)_y = 0` for `i > d` and every quasi-coherent `F`, and
2. `y` has an affine open neighbourhood `V` such that `f ⁻¹ V ⟶ V` and `d` satisfy the
   assumptions and the conclusions of [Stacks, Tag 0EX3].

The conclusions of Tag 0EX3 are (a) the vanishing of `Rⁱ f'_* F'` above `d` after any base
change, (b) the projection formula `Rᵈ f'_*(F' ⊗ (f')^* G') ≅ Rᵈ f'_* F' ⊗ G'`, and (c) that
formation of `Rᵈ f'_* F'` commutes with arbitrary further base change.
`exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le`
(`FibreDimensionStalkVanishing.lean`) states part (2) with (a) and (b). This file adds (c), which
is `isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`) applied to the
top-degree base-change situation formed by `f ∣_ V` and a cartesian square over `V`, and then
conjoins the two parts.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isAffineOpen_topDegreeBaseChangeConclusions_of_topologicalKrullDim_fiber_le`:
  **part (2) of [Stacks, Tag 0E7D]**, with the hypotheses of [Stacks, Tag 0EX3] for `f ∣_ V` and
  all three of its conclusions.
* `stalkVanishing_and_topDegreeBaseChange_of_topologicalKrullDim_fiber_le`:
  **[Stacks, Tag 0E7D]**, both parts.

## Implementation notes

The fibre-dimension hypothesis is `dim(X_y) ≤ d` rather than `dim(X_y) = d`, as in
`FibreDimensionStalkVanishing.lean`: this is more general, and it is the form the proof uses.

In conclusion (b), `Rᵈ f'_*` is read as the degree-`d` cohomology of the derived direct image of a
module placed in degree `0`, as in the existing statement of part (2) and in
`TopDegreeBaseChangeSituation.topDegreeTensorSheafIso`. Those statements, the higher direct images
`rightDerivedPlus`, and the canonical map of conclusion (c) are all taken in the standard model
`HasDerivedCategory.standard` of the derived category, which is the only model in which their
proofs exist. Each statement below therefore fixes that model with a `letI` at its head, so that
it is the same proposition as the statements it restates; no file-level instance is declared.

The hypotheses of Tag 0EX3 for `f ∣_ V` are bound by the existential rather than listed as
conjuncts, because conclusion (c) is about the canonical map of the situation they form.

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

noncomputable section

/-- **[Stacks, Tag 0E7D] part (2), with every conclusion of Tag 0EX3.** For `f : X ⟶ Y` proper
and `y ∈ Y` whose fibre has topological Krull dimension at most `d`, the point `y` has an affine
open neighbourhood `V` such that `f ∣_ V : f ⁻¹ V ⟶ V` and `d` satisfy the hypotheses of
[Stacks, Tag 0EX3] (`f ⁻¹ V` and `V` quasi-compact and quasi-separated, `Rⁱ (f ∣_ V)_* F = 0` for
`i > d` and quasi-coherent `F`) and, for every cartesian square `X' ⟶ f ⁻¹ V`, `f' : X' ⟶ Y'`,
`Y' ⟶ V`, its conclusions:

* (a) `Rⁱ f'_* F' = 0` for `i > d` and every quasi-coherent `F'` on `X'`;
* (b) `Rᵈ f'_*(F' ⊗ (f')^* G') ≅ Rᵈ f'_* F' ⊗ G'` for quasi-coherent `F'` on `X'` and `G'` on
  `Y'`;
* (c) for every further cartesian square `X'' ⟶ X'`, `f'' : X'' ⟶ Y''`, `h : Y'' ⟶ Y'` and every
  quasi-coherent `F'` on `X'`, the canonical map `h^* Rᵈ f'_* F' ⟶ Rᵈ f''_* (h')^* F'` is an
  isomorphism. -/
@[stacks 0E7D "part (2), with all conclusions of Tag 0EX3"]
theorem exists_isAffineOpen_topDegreeBaseChangeConclusions_of_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    letI : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
      fun C _ _ => HasDerivedCategory.standard C
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
      (hcX : CompactSpace (f ⁻¹ᵁ V).toScheme) (hqX : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme)
      (hcY : CompactSpace V.toScheme) (hqY : QuasiSeparatedSpace V.toScheme)
      (hvan : ∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)),
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (i : ℤ), (d : ℤ) < i → ∀ (F' : X'.Modules), F'.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F')) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (F' : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)), F'.IsQuasicoherent →
        ∀ (G' : SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)), G'.IsQuasicoherent →
          Nonempty ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
              ((derivedPushforward f'.toLRSHom.toShHom).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj
                  (((Stacks.SheafOfModules.Tensor.sheafTensor X'.toRingedSpace.sheaf).obj F').obj
                    ((RingedSpaceModuleAdjunction.modulePullback f'.toLRSHom.toShHom).obj
                      G')))) ≅
            ((Stacks.SheafOfModules.Tensor.sheafTensor Y'.toRingedSpace.sheaf).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
                ((derivedPushforward f'.toLRSHom.toShHom).obj
                  ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj F')))).obj
              G')) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme) (sq : IsPullback g' f' (f ∣_ V) g),
        let S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u} :=
          { X := (f ⁻¹ᵁ V).toScheme, Y := V.toScheme, f := f ∣_ V, d := d
            isCompact_X := hcX, isQuasiSeparated_X := hqX
            isCompact_Y := hcY, isQuasiSeparated_Y := hqY
            vanishes_above := hvan
            X' := X', Y' := Y', g' := g', f' := f', g := g, isPullback := sq }
        ∀ (F' : X'.Modules) [F'.IsQuasicoherent]
          {X'' Y'' : Scheme.{u}} (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
          (sq' : IsPullback h' f'' f' h),
        IsIso (topDirectImageBaseChangeMap S F' h' f'' h
          (toShHom_comm_of_isPullback (S := S) h' f'' h sq'))) := by
  obtain ⟨V, hyV, hV, hcX, hqX, hcY, hqY, hvan, ha, hb⟩ :=
    exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le f y d hdim
  refine ⟨V, hyV, hV, hcX, hqX, hcY, hqY, hvan, ha, hb, ?_⟩
  intro X' Y' g' f' g sq S F' _ X'' Y'' h' f'' h sq'
  exact isIso_topDirectImageBaseChangeMap S F' h' f'' h sq'

/-- **[Stacks, Tag 0E7D].** For `f : X ⟶ Y` proper and `y ∈ Y` whose fibre has topological
Krull dimension at most `d`: (1) the stalk at `y` of `Rⁱ f_* F` vanishes for every `i > d` and
every quasi-coherent `F`; (2) `y` has an affine open neighbourhood `V` such that `f ∣_ V` and `d`
satisfy the hypotheses and all three conclusions of [Stacks, Tag 0EX3], as in
`exists_isAffineOpen_topDegreeBaseChangeConclusions_of_topologicalKrullDim_fiber_le`. -/
@[stacks 0E7D]
theorem stalkVanishing_and_topDegreeBaseChange_of_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    letI : ∀ (C : Type (u + 1)) [Category.{u} C] [Abelian C], HasDerivedCategory.{u + 1} C :=
      fun C _ _ => HasDerivedCategory.standard C
    (∀ (F : X.Modules), F.IsQuasicoherent → ∀ (i : ℤ), (d : ℤ) < i →
      IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y)) ∧
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : IsAffineOpen V)
      (hcX : CompactSpace (f ⁻¹ᵁ V).toScheme) (hqX : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme)
      (hcY : CompactSpace V.toScheme) (hqY : QuasiSeparatedSpace V.toScheme)
      (hvan : ∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)),
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (i : ℤ), (d : ℤ) < i → ∀ (F' : X'.Modules), F'.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F')) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (F' : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)), F'.IsQuasicoherent →
        ∀ (G' : SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)), G'.IsQuasicoherent →
          Nonempty ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
              ((derivedPushforward f'.toLRSHom.toShHom).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj
                  (((Stacks.SheafOfModules.Tensor.sheafTensor X'.toRingedSpace.sheaf).obj F').obj
                    ((RingedSpaceModuleAdjunction.modulePullback f'.toLRSHom.toShHom).obj
                      G')))) ≅
            ((Stacks.SheafOfModules.Tensor.sheafTensor Y'.toRingedSpace.sheaf).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
                ((derivedPushforward f'.toLRSHom.toShHom).obj
                  ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj F')))).obj
              G')) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme) (sq : IsPullback g' f' (f ∣_ V) g),
        let S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u} :=
          { X := (f ⁻¹ᵁ V).toScheme, Y := V.toScheme, f := f ∣_ V, d := d
            isCompact_X := hcX, isQuasiSeparated_X := hqX
            isCompact_Y := hcY, isQuasiSeparated_Y := hqY
            vanishes_above := hvan
            X' := X', Y' := Y', g' := g', f' := f', g := g, isPullback := sq }
        ∀ (F' : X'.Modules) [F'.IsQuasicoherent]
          {X'' Y'' : Scheme.{u}} (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
          (sq' : IsPullback h' f'' f' h),
        IsIso (topDirectImageBaseChangeMap S F' h' f'' h
          (toShHom_comm_of_isPullback (S := S) h' f'' h sq'))) :=
  ⟨fun F _ i hi => isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le f y d hdim F i hi,
    exists_isAffineOpen_topDegreeBaseChangeConclusions_of_topologicalKrullDim_fiber_le f y d hdim⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
