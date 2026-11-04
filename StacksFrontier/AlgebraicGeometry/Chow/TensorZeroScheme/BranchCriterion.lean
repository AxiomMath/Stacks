module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Branches
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ZeroSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme

/-!
# When a morphism factors through a branch of the zero scheme of a tensor product

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂`, let `i : D → Y` be the zero scheme of `s` and let
`q : T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1}) ⟶ Y` be the ambient fibre product of [Stacks,
Tag 0F97], carrying the two fibre coordinates `z₁`, `z₂` and the equation `z₁ ⊗ z₂ - q^*s` whose
zero scheme is the scheme `ι : L → T` of the tag. We describe the conditions cutting out the
branch `D₁ = Z(s₁) ⊆ L`, viewed as a closed subscheme of `T`: a morphism `f : W ⟶ T` kills `z₁`
exactly when `f` composed with the first projection factors through the zero section of the first
line bundle; and, once it kills `z₁`, it kills the equation `z₁ ⊗ z₂ - q^*s` exactly when `f ≫ q`
factors through `D`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.pullbackCongrIso`: the transport of a pullback along an equality
  of morphisms, as an isomorphism.

## Main results

* `Stacks.Chow.TensorZeroScheme.zeroScheme_coord₁` and `zeroScheme_coord₂`: **the zero scheme of
  the fibre coordinate `zᵢ` on `T` is the inverse image of the image of the zero section** of the
  corresponding line bundle along the corresponding projection.
* `Stacks.Chow.TensorZeroScheme.pullbackGlobalSections_coord₁_eq_zero_iff` and
  `pullbackGlobalSections_coord₂_eq_zero_iff`: a morphism to `T` kills `zᵢ` exactly when its
  composite with the `i`-th projection factors through the zero section.
* `Stacks.Chow.TensorZeroScheme.pullbackGlobalSections_equation_eq_zero_iff`: **for a morphism
  killing `z₁ ⊗ z₂`, killing the equation means that the ideal of `D` lies in the kernel of its
  composite with `q`.**
* `Stacks.Chow.TensorZeroScheme.pullbackGlobalSections_section₁_eq_zero_iff` and
  `pullbackGlobalSections_section₂_eq_zero_iff`: the branch section `sᵢ` on `L` is killed by a
  morphism exactly when `zᵢ` is killed by its composite with `ι`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

/-! ### The transport along an equality of morphisms -/

/-- **The transport `m^*N ≅ m'^*N` of a pullback along an equality `m = m'` of morphisms**, whose
forward direction is `Stacks.Chow.TensorZeroScheme.pullbackCongrHom`. -/
def pullbackCongrIso {A B : Scheme.{u}} {m m' : A ⟶ B} (hm : m = m') (N : B.Modules) :
    (Scheme.Modules.pullback m).obj N ≅ (Scheme.Modules.pullback m').obj N :=
  eqToIso (congrArg (fun k : A ⟶ B => (Scheme.Modules.pullback k).obj N) hm)

/-- **The transport of a section along an equality of morphisms does not move its zero
scheme.** -/
theorem zeroScheme_pullbackCongrHom {A B : Scheme.{u}} {m m' : A ⟶ B} (hm : m = m')
    (N : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property N]
    (σ : Γ((Scheme.Modules.pullback m).obj N, ⊤)) :
    Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback m').obj N)
        (PresheafOfModules.Hom.app (pullbackCongrHom hm N).val (op ⊤) σ) =
      Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback m).obj N) σ :=
  (AlgebraicGeometry.zeroScheme_eq_of_iso (pullbackCongrIso hm N) (s := σ)
    (t := PresheafOfModules.Hom.app (pullbackCongrHom hm N).val (op ⊤) σ) rfl).symm

/-! ### The zero schemes of the two fibre coordinates -/

variable (Y : Scheme.{u}) (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- **The zero scheme of the fibre coordinate of the line bundle `L(M)` is the image of the zero
section.** This is clause (1) of [Stacks, Tag 0F96]. -/
theorem zeroScheme_fibreCoordinate_eq_ker_zeroSection :
    Stacks.Divisors.zeroScheme (Stacks.LineBundle.lineBundleSpace Y M)
        (Stacks.LineBundle.lineBundlePullback Y M) (Stacks.LineBundle.fibreCoordinate Y M) =
      (Stacks.LineBundle.inverseSituation Y M).zeroSection.ker :=
  (Stacks.LineBundle.zeroScheme_fibreCoordinate Y M).trans
    ((Stacks.LineBundle.zeroScheme_tautologicalSectionBase
        (Stacks.LineBundle.inverseSituation Y M)).trans
      (Stacks.LineBundle.inverseSituation Y
        M).zeroScheme_tautologicalSectionBase_eq_ker_zeroSection)

variable (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

include h₁ h₂ in
/-- **The zero scheme of the first fibre coordinate `z₁` on `T`** is the inverse image, along the
first projection, of the image of the zero section of the first line bundle. -/
theorem zeroScheme_coord₁ :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) =
      (Stacks.LineBundle.inverseSituation Y L₁).zeroSection.ker.comap (firstProj Y L₁ L₂) :=
  (AlgebraicGeometry.zeroScheme_eq_of_iso (Stacks.Divisors.pullbackCompIso (firstProj Y L₁ L₂)
      (Stacks.LineBundle.lineBundleProj Y L₁) L₁)
      (s := pullbackGlobalSections (firstProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundlePullback Y L₁) (Stacks.LineBundle.fibreCoordinate Y L₁))
      (t := coord₁ Y L₁ L₂) rfl).symm.trans
    ((Stacks.Divisors.zeroScheme_pullback (firstProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundlePullback Y L₁)
        (Stacks.LineBundle.fibreCoordinate Y L₁)).trans
      (congrArg (fun J : (Stacks.LineBundle.lineBundleSpace Y L₁).IdealSheafData =>
          J.comap (firstProj Y L₁ L₂))
        (zeroScheme_fibreCoordinate_eq_ker_zeroSection Y L₁)))

include h₁ h₂ in
/-- **The zero scheme of the second fibre coordinate before the transport** is the inverse
image, along the second projection, of the image of the zero section of the second line
bundle. -/
theorem zeroScheme_coord₂Pre :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback
          (secondProj Y L₁ L₂ ≫ Stacks.LineBundle.lineBundleProj Y L₂)).obj L₂)
        (coord₂Pre Y L₁ L₂) =
      (Stacks.LineBundle.inverseSituation Y L₂).zeroSection.ker.comap (secondProj Y L₁ L₂) :=
  (AlgebraicGeometry.zeroScheme_eq_of_iso (Stacks.Divisors.pullbackCompIso
      (secondProj Y L₁ L₂) (Stacks.LineBundle.lineBundleProj Y L₂) L₂)
      (s := pullbackGlobalSections (secondProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundlePullback Y L₂) (Stacks.LineBundle.fibreCoordinate Y L₂))
      (t := coord₂Pre Y L₁ L₂) rfl).symm.trans
    ((Stacks.Divisors.zeroScheme_pullback (secondProj Y L₁ L₂)
        (Stacks.LineBundle.lineBundlePullback Y L₂)
        (Stacks.LineBundle.fibreCoordinate Y L₂)).trans
      (congrArg (fun J : (Stacks.LineBundle.lineBundleSpace Y L₂).IdealSheafData =>
          J.comap (secondProj Y L₁ L₂))
        (zeroScheme_fibreCoordinate_eq_ker_zeroSection Y L₂)))

include h₁ h₂ in
/-- **The zero scheme of the second fibre coordinate transported along an equality of
morphisms** is the inverse image, along the second projection, of the image of the zero section
of the second line bundle. -/
theorem zeroScheme_coord₂Of {m : totalSpace Y L₁ L₂ ⟶ Y}
    (hm : secondProj Y L₁ L₂ ≫ Stacks.LineBundle.lineBundleProj Y L₂ = m) :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback m).obj L₂) (coord₂Of Y L₁ L₂ hm) =
      (Stacks.LineBundle.inverseSituation Y L₂).zeroSection.ker.comap (secondProj Y L₁ L₂) :=
  (zeroScheme_pullbackCongrHom hm L₂ (coord₂Pre Y L₁ L₂)).trans (zeroScheme_coord₂Pre Y L₁ L₂)

include h₁ h₂ in
/-- **The zero scheme of the second fibre coordinate `z₂` on `T`** is the inverse image, along
the second projection, of the image of the zero section of the second line bundle. -/
theorem zeroScheme_coord₂ :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) =
      (Stacks.LineBundle.inverseSituation Y L₂).zeroSection.ker.comap (secondProj Y L₁ L₂) :=
  zeroScheme_coord₂Of Y L₁ L₂ (secondProj_comp Y L₁ L₂)

/-! ### Killing a fibre coordinate -/

include h₁ h₂ in
/-- **A morphism to `T` kills the first fibre coordinate exactly when its composite with the
first projection factors through the zero section** of the first line bundle. -/
theorem pullbackGlobalSections_coord₁_eq_zero_iff {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂) :
    pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        (coord₁ Y L₁ L₂) = 0 ↔
      ∃ g : W ⟶ Y,
        g ≫ (Stacks.LineBundle.inverseSituation Y L₁).zeroSection = f ≫ firstProj Y L₁ L₂ :=
  (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) f).trans
    ((iff_of_eq (congrArg (fun J : (totalSpace Y L₁ L₂).IdealSheafData => J ≤ f.ker)
          (zeroScheme_coord₁ Y L₁ L₂))).trans
      ((Stacks.Divisors.comap_le_ker_iff
            (Stacks.LineBundle.inverseSituation Y L₁).zeroSection.ker
            (firstProj Y L₁ L₂) f).trans
        (Stacks.Divisors.factorsThrough_closedImmersion_iff
          (Stacks.LineBundle.inverseSituation Y L₁).zeroSection
          (f ≫ firstProj Y L₁ L₂)).symm))

include h₁ h₂ in
/-- **A morphism to `T` kills the second fibre coordinate exactly when its composite with the
second projection factors through the zero section** of the second line bundle. -/
theorem pullbackGlobalSections_coord₂_eq_zero_iff {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂) :
    pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
        (coord₂ Y L₁ L₂) = 0 ↔
      ∃ g : W ⟶ Y,
        g ≫ (Stacks.LineBundle.inverseSituation Y L₂).zeroSection = f ≫ secondProj Y L₁ L₂ :=
  (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) f).trans
    ((iff_of_eq (congrArg (fun J : (totalSpace Y L₁ L₂).IdealSheafData => J ≤ f.ker)
          (zeroScheme_coord₂ Y L₁ L₂))).trans
      ((Stacks.Divisors.comap_le_ker_iff
            (Stacks.LineBundle.inverseSituation Y L₂).zeroSection.ker
            (secondProj Y L₁ L₂) f).trans
        (Stacks.Divisors.factorsThrough_closedImmersion_iff
          (Stacks.LineBundle.inverseSituation Y L₂).zeroSection
          (f ≫ secondProj Y L₁ L₂)).symm))

/-! ### Killing the equation -/

variable (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include h₁ h₂ in
/-- A morphism to `T` killing the first fibre coordinate kills the product of the two fibre
coordinates. -/
theorem pullbackGlobalSections_coordProduct_eq_zero_of_coord₁ {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂)
    (hc : pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      (coord₁ Y L₁ L₂) = 0) :
    pullbackGlobalSections f
      (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (coordProduct Y L₁ L₂) = 0 :=
  (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (coordProduct Y L₁ L₂) f).mpr
    (le_trans (Stacks.Divisors.zeroScheme_tensorSection_le_left _ _ (coord₁ Y L₁ L₂)
      (coord₂ Y L₁ L₂))
      ((Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (coord₁ Y L₁ L₂) f).mp hc))

include h₁ h₂ in
/-- A morphism to `T` killing the second fibre coordinate kills the product of the two fibre
coordinates. -/
theorem pullbackGlobalSections_coordProduct_eq_zero_of_coord₂ {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂)
    (hc : pullbackGlobalSections f ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
      (coord₂ Y L₁ L₂) = 0) :
    pullbackGlobalSections f
      (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (coordProduct Y L₁ L₂) = 0 :=
  (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (coordProduct Y L₁ L₂) f).mpr
    (le_trans (Stacks.Divisors.zeroScheme_tensorSection_le_right _ _ (coord₁ Y L₁ L₂)
      (coord₂ Y L₁ L₂))
      ((Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ (coord₂ Y L₁ L₂) f).mp hc))

include h₁ h₂ in
/-- **A morphism to `T` killing the product of the two fibre coordinates kills the equation
`z₁ ⊗ z₂ - q^*s` exactly when the ideal of `D` lies in the kernel of its composite with `q`.** -/
theorem pullbackGlobalSections_equation_eq_zero_iff {W : Scheme.{u}}
    (f : W ⟶ totalSpace Y L₁ L₂)
    (hp : pullbackGlobalSections f
      (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (coordProduct Y L₁ L₂) = 0) :
    pullbackGlobalSections f
          (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
            ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (equation Y L₁ L₂ s) = 0 ↔
      zeroIdeal Y L₁ L₂ s ≤ (f ≫ totalProj Y L₁ L₂).ker := by
  rw [equation, map_sub, hp, zero_sub, neg_eq_zero,
    Stacks.PullbackTensorIso.pullbackTensorSection]
  exact (Stacks.Divisors.pullbackGlobalSections_iso_eq_zero_iff f
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (totalProj Y L₁ L₂) L₁ L₂)
    (pullbackGlobalSections (totalProj Y L₁ L₂) (Stacks.Divisors.tensorModules L₁ L₂) s)).trans
    ((Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff f (totalProj Y L₁ L₂)
      (Stacks.Divisors.tensorModules L₁ L₂) s).symm.trans
      (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker
        (Stacks.Divisors.tensorModules L₁ L₂) s (f ≫ totalProj Y L₁ L₂)))

/-! ### The two branch sections -/

include h₁ h₂ in
/-- The first branch section `s₁` is killed by `f'` exactly when the first fibre coordinate is
killed by `f' ≫ ι`. -/
theorem pullbackGlobalSections_section₁_eq_zero_iff {W : Scheme.{u}}
    (f' : W ⟶ (spaceIdeal Y L₁ L₂ s).subscheme) :
    pullbackGlobalSections f' ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
        (section₁ Y L₁ L₂ s) = 0 ↔
      pullbackGlobalSections (f' ≫ spaceι Y L₁ L₂ s)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) = 0 :=
  (Stacks.Divisors.pullbackGlobalSections_iso_eq_zero_iff f'
      (Stacks.Divisors.pullbackCompIso (spaceι Y L₁ L₂ s) (totalProj Y L₁ L₂) L₁)
      (pullbackGlobalSections (spaceι Y L₁ L₂ s)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂))).trans
    (Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff f' (spaceι Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂)).symm

include h₁ h₂ in
/-- The second branch section `s₂` is killed by `f'` exactly when the second fibre coordinate is
killed by `f' ≫ ι`. -/
theorem pullbackGlobalSections_section₂_eq_zero_iff {W : Scheme.{u}}
    (f' : W ⟶ (spaceIdeal Y L₁ L₂ s).subscheme) :
    pullbackGlobalSections f' ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂)
        (section₂ Y L₁ L₂ s) = 0 ↔
      pullbackGlobalSections (f' ≫ spaceι Y L₁ L₂ s)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) = 0 :=
  (Stacks.Divisors.pullbackGlobalSections_iso_eq_zero_iff f'
      (Stacks.Divisors.pullbackCompIso (spaceι Y L₁ L₂ s) (totalProj Y L₁ L₂) L₂)
      (pullbackGlobalSections (spaceι Y L₁ L₂ s)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂))).trans
    (Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff f' (spaceι Y L₁ L₂ s)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂)).symm

end Stacks.Chow.TensorZeroScheme

end
