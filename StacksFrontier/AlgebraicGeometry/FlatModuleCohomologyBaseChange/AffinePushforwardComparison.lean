module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence

/-!
# The comparison at the direct image of a quasi-coherent module along an affine morphism

Let

```
Z' --k'--> Z
|i'        |i
X' --g'--> X
|f'        |f
S' --g---> S
```

be two cartesian squares of schemes stacked one above the other, with `i` affine and the
composite `i ≫ f` affine, and let `M` be a quasi-coherent `𝒪_Z`-module. This file proves that
the base-change morphism of [Stacks, Tag 02KG] for the lower square — the first factor of the
underived comparison of [Stacks, Tag 0GN5] — is invertible at the direct image `i_* M`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_baseChangeNatTrans_app_pushforward`: the
  base-change morphism of [Stacks, Tag 02KG] for the lower square is invertible at `i_* M`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' Z Z' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  {i : Z ⟶ X} {k' : Z' ⟶ Z} {i' : Z' ⟶ X'}

/-- A morphism occurring as the second of four composable factors, three of which are
invertible, is invertible when the composite is. -/
private theorem isIso_of_isIso_comp_four {C : Type*} [Category* C] {V W Y₀ Y T : C}
    {a : V ⟶ W} {b : W ⟶ Y₀} {c : Y₀ ⟶ Y} {d : Y ⟶ T}
    (h : IsIso (a ≫ (b ≫ c) ≫ d)) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) :
    IsIso b := by
  have := ha
  have := hc
  have := hd
  have := h
  have hb : b = inv a ≫ (a ≫ (b ≫ c) ≫ d) ≫ inv d ≫ inv c := by simp
  rw [hb]
  infer_instance

/-- **The base-change morphism of [Stacks, Tag 02KG] at the direct image along an affine
morphism.** For two cartesian squares stacked one above the other with `i` and `i ≫ f` affine
and `M` quasi-coherent, the base-change morphism of the lower square is invertible at
`i_* M`. -/
theorem isIso_baseChangeNatTrans_app_pushforward (H : IsPullback g' f' f g)
    (Hi : IsPullback k' i' i g') [AlgebraicGeometry.IsAffineHom i]
    [AlgebraicGeometry.IsAffineHom (i ≫ f)] (M : Z.Modules) [M.IsQuasicoherent] :
    IsIso ((baseChangeNatTrans H.w).app ((Scheme.Modules.pushforward i).obj M)) := by
  have hi' : AlgebraicGeometry.IsAffineHom i' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback Hi ‹AlgebraicGeometry.IsAffineHom i›
  have hbci : IsIso ((AffinePushforward.baseChangeNatTrans Hi.w).app M) :=
    AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom Hi M
  have hbc : IsIso ((AffinePushforward.baseChangeNatTrans (Hi.paste_vert H).w).app M) :=
    AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      (Hi.paste_vert H) M
  have hci : IsIso ((Scheme.Modules.pushforwardComp i f).inv.app M) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardComp i f).app M).inv)
  have hA : IsIso ((Scheme.Modules.pullback g).map
      ((Scheme.Modules.pushforwardComp i f).inv.app M)) := Functor.map_isIso _ _
  have hC : IsIso ((Scheme.Modules.pushforward f').map
      ((AffinePushforward.baseChangeNatTrans Hi.w).app M)) := Functor.map_isIso _ _
  have hD₁ : IsIso ((Scheme.Modules.pushforwardComp i' f').hom.app
      ((Scheme.Modules.pullback k').obj M)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardComp i' f').app _).hom)
  have hD₂ : IsIso ((Scheme.Modules.pushforwardCongr (rfl : i' ≫ f' = i' ≫ f')).hom.app
      ((Scheme.Modules.pullback k').obj M)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforwardCongr
      (rfl : i' ≫ f' = i' ≫ f')).app _).hom)
  have hD := @IsIso.comp_isIso _ _ _ _ _ _ _ hD₁ hD₂
  have key := congr_app
    (AlgebraicGeometry.baseChangeNatTrans_vpaste' H.w Hi.w (Hi.paste_vert H).w rfl) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at key
  rw [key] at hbc
  exact isIso_of_isIso_comp_four hbc hA hC hD

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
