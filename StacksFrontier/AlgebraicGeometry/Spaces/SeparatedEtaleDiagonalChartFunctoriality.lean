module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalChartDecomposition
import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance

/-!
# The clopen decomposition of a chart by the diagonal is functorial

Let `f : X ⟶ Y` be a separated étale morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, with relative diagonal `Δ : X ⟶ X ×_Y X`.  For an étale chart `V` of
`X ×_Y X` the morphism `Δ` cuts `V` into two clopen pieces: the base-changed piece
`V ×_{X ×_Y X} X` and its complement. This file shows that the decomposition is compatible with a
morphism of charts `k : W ⟶ V`:

* the base-changed piece `V ×_{X ×_Y X} X` is functorial in `V`, and
* the image of `W ×_{X ×_Y X} X` in `W` is the preimage of the image of `V ×_{X ×_Y X} X`, so
  the complementary piece of `W` maps to the complementary piece of `V` over `k`.

## Main definitions

* `AlgebraicGeometry.Space.diagonalChartMap`: the functorial action of `V ↦ V ×_{X ×_Y X} X` on
  a morphism of charts.
* `AlgebraicGeometry.Space.diagonalChartComplementMap`: the induced morphism of complementary
  pieces.

## Main results

* `AlgebraicGeometry.Space.range_toScheme_map_snd_of_factor` and
  `AlgebraicGeometry.Space.range_chartSchemeMap_diagonalChartHom_comap`: the image of the
  cartesian projection at `W` is the preimage along `k` of the image at `V`.
* `AlgebraicGeometry.Space.diagonalChartMap_comp_diagonalChartHom` and
  `AlgebraicGeometry.Space.diagonalChartComplementMap_comp_diagonalChartComplementHom`: both
  induced morphisms commute with the inclusions into the ambient charts.

## References

* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inclusions of opens and the inclusion into the ambient chart -/

/-- The morphism of open subcharts induced by an inclusion of opens is a morphism over the
ambient chart. -/
theorem openChartHomOfLE_comp_openChartInclusion (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (U : SmallEtale B S hS F) {O O' : (chartScheme U).Opens} (h : O ≤ O') :
    openChartHomOfLE B S hS F U h ≫ openChartInclusion B S hS F U O' =
      openChartInclusion B S hS F U O :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (openSubHomOfLE_comp_openSubHom ((SmallEtale.toOver B S hS F).obj U) h))

variable {X Y : AlgebraicSpaces B S hS}

/-! ### Functoriality of the base-changed piece -/

/-- The functorial action on a morphism of charts of the base-changed chart
`V ↦ V ×_{X ×_Y X} X`. -/
noncomputable abbrev diagonalChartMap (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChart B S hS f het hsep W ⟶ diagonalChart B S hS f het hsep V :=
  (smallEtalePostcomp B S hS (selfFibreDiagonal B S hS f)
      (isEtale_selfFibreDiagonal B S hS f het)).map
    ((smallBaseChange B S hS (selfFibreDiagonal B S hS f)
      (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).map k)

/-- The base-changed piece is functorial over the ambient chart. -/
theorem diagonalChartMap_comp_diagonalChartHom (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChartMap B S hS f het hsep k ≫ diagonalChartHom B S hS f het hsep V =
      diagonalChartHom B S hS f het hsep W ≫ k :=
  (smallEtalePostcompBaseChangeAdjunction B S hS (selfFibreDiagonal B S hS f)
    (isEtale_selfFibreDiagonal B S hS f het)
    (relativelyRepresentable_selfFibreDiagonal B S hS f hsep)).counit.naturality k

/-! ### The image comparison -/

/-- If an étale chart `g` of `X ×_Y X` is the composite of a morphism `v` of the big fppf site
with a chart `V`, then the image of the cartesian projection of the base change of `Δ` along `g`
is the preimage along `v` of the image of the cartesian projection at `V`. -/
theorem range_toScheme_map_snd_of_factor (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    (V : SmallEtale B S hS (selfFibreSquare B S hS f).1)
    {V' : BigFppfOver B S hS} (v : V' ⟶ V.1.left)
    (g : yoneda.obj V' ⟶ (selfFibreSquare B S hS f).1)
    (hg : yoneda.map v ≫ V.1.hom = g) :
    Set.range ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_selfFibreDiagonal B S hS f hsep).snd g)) =
      (BigFppfOver.toScheme B S hS).map v ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep V)) := by
  subst hg
  have hoi := isOpenImmersion_diagonalChartProj B S hS f het hsep V
  set T := BigFppfOver.toScheme B S hS
  set hrep := relativelyRepresentable_selfFibreDiagonal B S hS f hsep
  have he := chartBaseChangeCompIso_hom_snd B S hS (selfFibreDiagonal B S hS f) hrep V v
  have h1 : Set.range (T.map (hrep.snd (yoneda.map v ≫ V.obj.hom))) =
      Set.range (T.map (pullback.fst v (hrep.snd V.obj.hom))) := by
    rw [← he, T.map_comp]
    exact (AlgebraicGeometry.SmallEtale.scheme_range_comp_iso _ _).symm
  have h2 : Set.range (T.map (pullback.fst v (hrep.snd V.obj.hom))) =
      Set.range (pullback.fst (T.map v) (T.map (hrep.snd V.obj.hom))) := by
    rw [← PreservesPullback.iso_hom_fst T v (hrep.snd V.obj.hom)]
    exact AlgebraicGeometry.SmallEtale.scheme_range_comp_iso _ _
  rw [h1, h2, AlgebraicGeometry.IsOpenImmersion.range_pullbackFst]
  rfl

/-- The image of the diagonal at `W` is the preimage along `k` of the image at `V`. -/
private theorem diagonalChartRange_eq_comap (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChartRange B S hS f hsep W = chartSchemeMap k ⁻¹' diagonalChartRange B S hS f hsep V :=
  range_toScheme_map_snd_of_factor B S hS f het hsep V
    ((SmallEtale.toOver B S hS (selfFibreSquare B S hS f).1).map k) W.obj.hom
    (yoneda_map_toOver_map_comp_hom k)

/-- The image of the diagonal in a chart is compatible with pullback along a morphism of
charts: the image at `W` is the preimage along `k` of the image at `V`. -/
theorem range_chartSchemeMap_diagonalChartHom_comap (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    Set.range (chartSchemeMap (diagonalChartHom B S hS f het hsep W)) =
      chartSchemeMap k ⁻¹' Set.range (chartSchemeMap (diagonalChartHom B S hS f het hsep V)) := by
  rw [show chartSchemeMap (diagonalChartHom B S hS f het hsep W) =
      (BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep W) from
      congrArg _ (toOver_map_diagonalChartHom B S hS f het hsep W),
    show chartSchemeMap (diagonalChartHom B S hS f het hsep V) =
      (BigFppfOver.toScheme B S hS).map (diagonalChartProj B S hS f hsep V) from
      congrArg _ (toOver_map_diagonalChartHom B S hS f het hsep V)]
  exact diagonalChartRange_eq_comap B S hS f het hsep k

/-! ### Functoriality of the complementary piece -/

/-- The complement of the image of the diagonal at `W` is contained in the preimage of the
complement at `V`. -/
theorem diagonalChartComplementOpens_le_comap (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChartComplementOpens B S hS f het hsep W ≤
      chartSchemeMap k ⁻¹ᵁ diagonalChartComplementOpens B S hS f het hsep V := by
  exact fun x hx hmem ↦ hx ((diagonalChartRange_eq_comap B S hS f het hsep k).ge hmem)

/-- The morphism of complementary pieces induced by a morphism of charts: restrict the morphism
to the complement at `V` and its preimage, then include the complement at `W` into that
preimage. -/
noncomputable def diagonalChartComplementMap (f : X ⟶ Y) (het : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChartComplement B S hS f het hsep W ⟶
      diagonalChartComplement B S hS f het hsep V :=
  openChartHomOfLE B S hS (selfFibreSquare B S hS f).1 W
      (diagonalChartComplementOpens_le_comap B S hS f het hsep k) ≫
    openChartRestrict B S hS (selfFibreSquare B S hS f).1 k
      (diagonalChartComplementOpens B S hS f het hsep V)

/-- The complementary piece is functorial over the ambient chart. -/
theorem diagonalChartComplementMap_comp_diagonalChartComplementHom (f : X ⟶ Y)
    (het : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    {W V : SmallEtale B S hS (selfFibreSquare B S hS f).1} (k : W ⟶ V) :
    diagonalChartComplementMap B S hS f het hsep k ≫
        diagonalChartComplementHom B S hS f het hsep V =
      diagonalChartComplementHom B S hS f het hsep W ≫ k :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ openChartHomOfLE B S hS (selfFibreSquare B S hS f).1 W
        (diagonalChartComplementOpens_le_comap B S hS f het hsep k) ≫ m)
      (openChartRestrict_comp_openChartInclusion B S hS (selfFibreSquare B S hS f).1 k
        (diagonalChartComplementOpens B S hS f het hsep V))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m ↦ m ≫ k)
          (openChartHomOfLE_comp_openChartInclusion B S hS (selfFibreSquare B S hS f).1 W
            (diagonalChartComplementOpens_le_comap B S hS f het hsep k)))))

end AlgebraicGeometry.Space

end
