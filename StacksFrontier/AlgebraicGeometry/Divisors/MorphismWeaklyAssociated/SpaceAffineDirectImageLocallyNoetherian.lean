module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceAffineDirectImage

/-!
# Weakly associated points of an affine direct image with locally Noetherian source

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` with `X` locally Noetherian
and let `F` be a quasi-coherent `𝒪_X`-module. Then `WeakAss_Y(f_*F) = f(WeakAss_X(F))`.

## Main results

* `weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom_locallyNoetherian`: for an
  affine morphism `f : X ⟶ Y` with `X` locally Noetherian, the weakly associated points of `f_*F`
  are the images of the weakly associated points of `F`.

## Implementation notes

The module universe is the universe `u` of the structure rings, which is the only one at which
`AlgebraicGeometry.Space.modulePushforward` exists.

## References

* [Stacks Project, Tag 0CU8](https://stacks.math.columbia.edu/tag/0CU8)
* [Stacks Project, Tag 0CU2](https://stacks.math.columbia.edu/tag/0CU2)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site over `S` is deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_SpaceAffineDirectImageLocallyNoetherian :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SpaceAffineDirectImageLocallyNoetherian
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and let `F` be a
quasi-coherent `𝒪_X`-module. If `X` is locally Noetherian, then the weakly associated points of
`f_*F` are exactly the images of the weakly associated points of `F`. -/
@[stacks 0CU8 "WeakAss(f_*F) = f(WeakAss F) for f affine, X locally Noetherian, F quasi-coherent"]
theorem weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom_locallyNoetherian
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) =
      pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F := by
  refine Set.Subset.antisymm
    (weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom B S hS f hf F hF) ?_
  rintro y ⟨x, hx, hxy⟩
  obtain ⟨V, b, hV, hb, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  let g : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have hg : IsEtale B S hS g.hom := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  let X' := AlgebraicSpaces.fiberProduct B S hS g f
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.fst g.hom f.hom)
  let i : X' ⟶ X := ObjectProperty.homMk (pullback.snd g.hom f.hom)
  have sq : IsPullback i f' f g := (AlgebraicSpaces.isPullback_fiberProduct B S hS g f).flip
  have hiEt : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have hf' : IsAffineHom B S hS f'.hom :=
    isAffineHom_of_isPullback ((IsPullback.of_hasPullback g.hom f.hom).flip) hf
  have hX' : HasEtaleLocalProperty B S hS X'.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_isEtale B S hS X'.2 X.2 hiEt hX
  have hFi : ((etaleModulePullback B S hS i hiEt).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF
  have hchart := weaklyAssociatedPoints_modulePushforward_schemeTargetAffine_eq_image B S hS V f'
    hV hf' hX' _ hFi
  have hgv : pointsMap B S hS (schemeSpace V).1 g.hom v = y := hv
  have hvx : pointsMap B S hS (schemeSpace V).1 g.hom v = pointsMap B S hS X.1 f.hom x := by
    rw [hgv, hxy]
  obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS sq.flip v x hvx
  have hwF : w ∈ weaklyAssociatedPoints B S hS X'
      ((etaleModulePullback B S hS i hiEt).obj F) :=
    (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS i hiEt F w).2 (hw₂ ▸ hx)
  have h2 : v ∈ weaklyAssociatedPoints B S hS (schemeSpace V)
      ((modulePushforward B S hS f').obj ((etaleModulePullback B S hS i hiEt).obj F)) := by
    rw [hchart]
    exact ⟨w, hwF, hw₁⟩
  have h1 : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS f).obj F)) v :=
    (isWeaklyAssociatedPoint_congr B S hS
      ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).app F) v).1 h2
  have h0 := (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS g hg _ v).1 h1
  rwa [hgv] at h0

end AlgebraicGeometry.Space

end
