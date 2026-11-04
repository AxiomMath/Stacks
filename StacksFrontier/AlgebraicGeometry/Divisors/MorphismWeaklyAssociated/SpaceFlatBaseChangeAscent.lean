module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRepresentedFlatPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Weakly associated points under the base change of a morphism of representable spaces

Let `κ : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is flat and surjective, let `Z` be an algebraic space over `h_T` and let `Z'` be its base
change along `κ`, presented by a cartesian square. For a quasi-coherent `𝒪_Z`-module `G`, every
weakly associated point of `G` is the image of a weakly associated point of its inverse image
on `Z'`.

The statement is étale local on `Z`: choose an étale chart `a : h_W ⟶ Z` by a scheme of the site
through the given point, so that the point is the image of a weakly associated point of the
restriction of `G` to that chart (Stacks 0CUU). Base changing the chart in the site along `κ`
gives a chart of `Z'` — the fibre product `W ×_T T'`, whose Yoneda image is the fibre product of
the Yoneda images, hence the base change of `h_W` along `Z' ⟶ Z` — and the statement for the
represented chart is
`AlgebraicGeometry.Space.exists_isWeaklyAssociatedPoint_modulePullback_representedSpaceMap`.
Stacks 0CUU carries the point produced there back to `Z'`.

## Main results

* `AlgebraicGeometry.Space.exists_isWeaklyAssociatedPoint_modulePullback_of_isPullback_yoneda`:
  the existence of that preimage.

## Implementation notes

The base change is taken as a cartesian square of presheaves rather than constructed, since the
fibre product of algebraic spaces is formed here as a presheaf pullback and any such square is
canonically isomorphic to it. The chart base change is the fibre product in the big fppf
category, which has fibre products, and both `yoneda` and the underlying-scheme functor preserve
them; that is where the flatness and surjectivity of the underlying morphism of schemes of `κ`
are transported to the chart.

The module universe is that of the structure rings, since Stacks 0CUU is available there.

## References

* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Weak association ascends along the base change of a flat surjective morphism of the
site.** In a cartesian square exhibiting `Z'` as the base change of `Z` along `κ : T' ⟶ T`,
with the underlying morphism of schemes of `κ` flat and surjective, every point weakly
associated to a quasi-coherent `𝒪_Z`-module `G` is the image of a point weakly associated to the
inverse image of `G` on `Z'`. -/
theorem exists_isWeaklyAssociatedPoint_modulePullback_of_isPullback_yoneda
    {Z Z' : AlgebraicSpaces B S hS} {T T' : BigFppfOver B S hS}
    (c : Z.1 ⟶ yoneda.obj T) (c' : Z'.1 ⟶ yoneda.obj T') (π : Z' ⟶ Z) (κ : T' ⟶ T)
    (sq : IsPullback π.hom c' c (yoneda.map κ))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map κ))
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map κ))
    (G : Modules.{u, u} B S hS Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    {θ : points B S hS Z.1} (hθ : IsWeaklyAssociatedPoint B S hS Z G θ) :
    ∃ θ' : points B S hS Z'.1,
      pointsMap B S hS Z'.1 π.hom θ' = θ ∧
        IsWeaklyAssociatedPoint B S hS Z' ((modulePullback B S hS π).obj G) θ' := by
  -- An étale chart of `Z` by a scheme of the site through `θ`.
  obtain ⟨W, a, w, ha, haw, -, -⟩ := exists_etale_scheme_chart_through_point B S hS Z.2
    (𝟙 Z.1) (isEtale_id B S hS Z.1) θ
  have hφ : IsEtale B S hS
      (ObjectProperty.homMk (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ :
        AlgebraicSpaces B S hS)) (Y := Z) a).hom := ha
  have hNqc : ((modulePullback B S hS
      (ObjectProperty.homMk (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ :
        AlgebraicSpaces B S hS)) (Y := Z) a)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS _ hφ G hG
  have hw : IsWeaklyAssociatedPoint B S hS
      ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
      ((modulePullback B S hS (ObjectProperty.homMk
        (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
        (Y := Z) a)).obj G) w := by
    refine (isWeaklyAssociatedPoint_modulePullback_iff B S hS _ hφ G w).2 ?_
    show IsWeaklyAssociatedPoint B S hS Z G (pointsMap B S hS (yoneda.obj W) a w)
    rw [haw]
    exact hθ
  -- The chart read as a morphism of the site into `T`, and its base change along `κ`.
  obtain ⟨cW, hcW⟩ : ∃ cW : W ⟶ T, yoneda.map cW = a ≫ c :=
    ⟨yoneda.preimage (a ≫ c), yoneda.map_preimage _⟩
  obtain ⟨W', ρ, σ, sqSite⟩ : ∃ (W' : BigFppfOver B S hS) (ρ : W' ⟶ W) (σ : W' ⟶ T'),
      IsPullback ρ σ cW κ :=
    ⟨_, _, _, IsPullback.of_hasPullback cW κ⟩
  -- The represented statement on the chart base change.
  obtain ⟨w', hw'ρ, hw'⟩ := exists_isWeaklyAssociatedPoint_modulePullback_representedSpaceMap
    B S hS ρ
    (MorphismProperty.of_isPullback (sqSite.map (BigFppfOver.toScheme B S hS)).flip hflat)
    (MorphismProperty.of_isPullback (sqSite.map (BigFppfOver.toScheme B S hS)).flip hsurj)
    _ hNqc hw
  -- The chart base change is an étale chart of `Z'`.
  have hlift : (yoneda.map ρ ≫ a) ≫ c = yoneda.map σ ≫ yoneda.map κ := by
    rw [Category.assoc, ← hcW, ← yoneda.map_comp, ← yoneda.map_comp]
    exact congrArg yoneda.map sqSite.w
  obtain ⟨ψ, hψπ, hψc'⟩ : ∃ ψ : yoneda.obj W' ⟶ Z'.1,
      ψ ≫ π.hom = yoneda.map ρ ≫ a ∧ ψ ≫ c' = yoneda.map σ :=
    ⟨sq.lift (yoneda.map ρ ≫ a) (yoneda.map σ) hlift, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  have sqChart : IsPullback (yoneda.map ρ) ψ a π.hom := by
    refine IsPullback.of_bot ?_ hψπ.symm sq
    rw [hψc', ← hcW]
    exact sqSite.map yoneda
  have sqChartSpace : IsPullback
      (representedSpaceMap B S hS ρ)
      (ObjectProperty.homMk (X := (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :
        AlgebraicSpaces B S hS)) (Y := Z') ψ)
      (ObjectProperty.homMk (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ :
        AlgebraicSpaces B S hS)) (Y := Z) a) π :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F) sqChart
  have hψetale : IsEtale B S hS
      (ObjectProperty.homMk (X := (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :
        AlgebraicSpaces B S hS)) (Y := Z') ψ).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sqChartSpace hφ
  -- The two inverse images of `G` to the chart base change agree.
  have hiso : (modulePullback B S hS
        (ObjectProperty.homMk (X := (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :
          AlgebraicSpaces B S hS)) (Y := Z') ψ)).obj ((modulePullback B S hS π).obj G) ≅
      (modulePullback B S hS (representedSpaceMap B S hS ρ)).obj
        ((modulePullback B S hS (ObjectProperty.homMk
          (X := (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
          (Y := Z) a)).obj G) :=
    (modulePullbackCompIso B S hS _ π).app G ≪≫
      eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj G) sqChartSpace.w.symm) ≪≫
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ) _).app G).symm
  refine ⟨pointsMap B S hS (yoneda.obj W') ψ w', ?_, ?_⟩
  · have h := congrArg (fun k ↦ pointsMap B S hS (yoneda.obj W') k w') hψπ
    simp only [pointsMap_comp, Function.comp_apply] at h
    rw [h, hw'ρ, haw]
  · exact (isWeaklyAssociatedPoint_modulePullback_iff B S hS _ hψetale
      ((modulePullback B S hS π).obj G) w').1
      ((isWeaklyAssociatedPoint_congr B S hS hiso w').2 hw')

end AlgebraicGeometry.Space

end
