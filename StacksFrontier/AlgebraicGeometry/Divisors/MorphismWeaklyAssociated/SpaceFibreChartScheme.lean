module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ChartSchemeNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedTFAE

/-!
# Relative weak association read on a chart scheme of the fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be a
quasi-coherent `𝒪_X`-module and let `x` be a point of `X`. The fibre of `f` over a field-valued
point of `Y` is again an algebraic space, and the condition defining the relative weak assassin
is stated there with the étale notion of weak association. An étale scheme chart of that fibre
is a *scheme*, so on it weak association is the Zariski notion of Stacks 056L; the two are
matched by the étale-chart description of Stacks 0CTW. Read over the residue field of a point
of an étale scheme chart of `Y`, the result is a form of the conditions of Stacks 0CUZ on the
chart schemes of the fibre.

## Main definitions

* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnFibreChartScheme` and
  `AlgebraicGeometry.Space.IsWeaklyAssociatedOnFibreChartSchemeEvery`: some, respectively
  every, point of an étale scheme chart of the fibre of `f` over a field-valued point of `Y`
  lying above `x` is weakly associated to the restriction of `F` to that chart scheme.
* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnSomeChartSchemeFibre` and
  `AlgebraicGeometry.Space.IsWeaklyAssociatedOnEveryChartSchemeFibre`: those conditions read
  over the residue field of a point of an étale scheme chart of `Y` above the image of `x`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint`:
  **Stacks 0CTW, conditions (1) and (2) at a point of a chart scheme.** A point of an étale
  scheme chart of an algebraic space is weakly associated to the restriction of a
  quasi-coherent module there, in the Zariski sense, exactly when its image is weakly
  associated to the module in the étale sense.
* `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibreChartScheme_iff` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibreChartSchemeEvery_iff`: at a fixed
  field-valued point of `Y`, each strength of the chart-scheme condition agrees with the
  corresponding condition on the fibre algebraic space.
* `AlgebraicGeometry.Space.isWeaklyAssociatedOnSomeChartSchemeFibre_iff` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedOnEveryChartSchemeFibre_iff`: the some-chart
  condition is condition (1) of Stacks 0CUZ and the every-chart condition is condition (2).
* `AlgebraicGeometry.Space.isWeaklyAssociatedOnSomeChartSchemeFibre_iff_of_isQuasicoherentOnSite`,
  `AlgebraicGeometry.Space.isWeaklyAssociatedOnEveryChartSchemeFibre_iff_of_isQuasicoherentOnSite`
  and `isRelativeWeaklyAssociatedPoint_of_someChartSchemeFibre_of_isQuasicoherentOnSite` in the
  same namespace: the same statements for a quasi-coherent `F`, and the resulting membership of
  `x` in the relative weak assassin.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a chart scheme -/

/-- Every point of an algebraic space is the image of a point of the scheme of some étale
chart. -/
theorem exists_chartSchemeToPoints_eq (Z : AlgebraicSpaces B S hS) (z : points B S hS Z.1) :
    ∃ (W : SmallEtale B S hS Z.1) (w : chartScheme W),
      chartSchemeToPoints B S hS Z.1 W w = z := by
  obtain ⟨W, hW⟩ := exists_surjective_smallEtale_chart B S hS Z.1 Z.2
  exact ⟨W, surjective_chartSchemeToPoints B S hS Z.1 W hW z⟩

/-! ### Zariski weak association at a point of a chart scheme -/

/-- **Zariski and étale weak association agree at a point of a chart scheme.** Let `F` be a
quasi-coherent `𝒪_Z`-module and let `w` be a point of the scheme of an étale chart `W` of `Z`.
Then `w` is weakly associated to the restriction `F|_W`, in the Zariski sense of Stacks 056L,
exactly when the point of `Z` it lies over is weakly associated to `F` in the sense of
Stacks 0CTX. -/
@[stacks 0CTW "conditions (1) and (2) at a point of a chart scheme, with no geometric point in
the statement"]
theorem isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint
    (Z : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS Z.1 Z.2)
    [F.IsQuasicoherentOnSite] (W : SmallEtale B S hS Z.1) (w : chartScheme W) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS Z.2 F W) w ↔
      IsWeaklyAssociatedPoint B S hS Z F (chartSchemeToPoints B S hS Z.1 W w) := by
  set W₀ := (SmallEtale.toOver B S hS Z.1).obj W with hW₀
  have hchart : chartSchemeToPoints B S hS Z.1 W w =
      pointsMap B S hS (yoneda.obj W₀) W.obj.hom
        ((pointsEquivScheme B S hS W₀).symm w) :=
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Z.1 W w
  have hcp : ∀ ybar : GeometricPoint B S hS (yoneda.obj W₀),
      ybar.image = (pointsEquivScheme B S hS W₀).symm w →
      chartPoint B S hS Z.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) = w :=
    fun ybar hy => by
      rw [chartPoint_ofChartGeometricPoint, hy]
      exact (pointsEquivScheme B S hS W₀).apply_symm_apply w
  constructor
  · intro h
    obtain ⟨ybar, hybar⟩ :=
      exists_geometricRepresentative B S hS (yoneda.obj W₀) ((pointsEquivScheme B S hS W₀).symm w)
    obtain rfl := hcp ybar hybar
    refine isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart B S hS Z F _ ?_
      (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) h
    rw [hchart]
    exact (geometricPointMap_image W.obj.hom ybar).trans (congrArg _ hybar)
  · rintro ⟨xbar, hlies, h3⟩
    obtain ⟨ybar, hyb, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS W₀) Z.2 W.obj.hom (isEtale_chartToSpace B S hS Z W)
      xbar ((pointsEquivScheme B S hS W₀).symm w) (by rw [← hchart]; exact hlies.symm)
    obtain rfl := hcp ybar hyb
    exact isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime B S hS Z
      (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) F
      ((Subtype.ext hval : geometricPointMap W.obj.hom ybar = xbar) ▸ h3)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The chart-scheme condition on one fibre -/

/-- Some point of the scheme of some étale chart of the fibre of `f : X ⟶ Y` over a field-valued
point `p` of `Y`, lying above `x`, is weakly associated to the restriction of `F` to that chart
scheme. -/
noncomputable def IsWeaklyAssociatedOnFibreChartScheme (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X.1) : Prop :=
  ∃ (W : SmallEtale B S hS (fibreAtFieldValuedPoint B S hS f p).1) (w : chartScheme W),
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom
        (chartSchemeToPoints B S hS (fibreAtFieldValuedPoint B S hS f p).1 W w) = x ∧
      Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS (fibreAtFieldValuedPoint B S hS f p).2
          ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) W) w

/-- Every point of the scheme of every étale chart of the fibre of `f : X ⟶ Y` over a
field-valued point `p` of `Y` which lies above `x` is weakly associated to the restriction of
`F` to that chart scheme. -/
noncomputable def IsWeaklyAssociatedOnFibreChartSchemeEvery (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X.1) : Prop :=
  ∀ (W : SmallEtale B S hS (fibreAtFieldValuedPoint B S hS f p).1) (w : chartScheme W),
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom
        (chartSchemeToPoints B S hS (fibreAtFieldValuedPoint B S hS f p).1 W w) = x →
      Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS (fibreAtFieldValuedPoint B S hS f p).2
          ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) W) w

/-- Weak association at a point of a chart scheme of a fibre, for the restriction of a
quasi-coherent module, is weak association of its image in the fibre algebraic space. -/
private theorem isWeaklyAssociatedPoint_fibreRestrictToChart_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (hF : F.IsQuasicoherentOnSite) (W : SmallEtale B S hS (fibreAtFieldValuedPoint B S hS f p).1)
    (w : chartScheme W) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS (fibreAtFieldValuedPoint B S hS f p).2
          ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) W) w ↔
      IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F)
        (chartSchemeToPoints B S hS (fibreAtFieldValuedPoint B S hS f p).1 W w) :=
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (fibreAtFieldValuedPointProjection B S hS f p) F hF
  isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS _ _ W w

/-- The some-point chart-scheme condition on the fibre over a field-valued point of `Y` is the
some-point condition on the fibre algebraic space. -/
theorem isWeaklyAssociatedOnFibreChartScheme_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X.1) (hF : F.IsQuasicoherentOnSite) :
    IsWeaklyAssociatedOnFibreChartScheme B S hS f F p x ↔
      IsWeaklyAssociatedOnFibre B S hS f F p x := by
  constructor
  · rintro ⟨W, w, hw, h⟩
    exact ⟨chartSchemeToPoints B S hS (fibreAtFieldValuedPoint B S hS f p).1 W w, hw,
      (isWeaklyAssociatedPoint_fibreRestrictToChart_iff B S hS f F p hF W w).mp h⟩
  · rintro ⟨θ, hθ, hwa⟩
    obtain ⟨W, w, hwθ⟩ :=
      exists_chartSchemeToPoints_eq B S hS (fibreAtFieldValuedPoint B S hS f p) θ
    exact ⟨W, w, by rwa [hwθ],
      (isWeaklyAssociatedPoint_fibreRestrictToChart_iff B S hS f F p hF W w).mpr (hwθ ▸ hwa)⟩

/-- The every-point chart-scheme condition on the fibre over a field-valued point of `Y` is the
every-point condition on the fibre algebraic space. -/
theorem isWeaklyAssociatedOnFibreChartSchemeEvery_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X.1) (hF : F.IsQuasicoherentOnSite) :
    IsWeaklyAssociatedOnFibreChartSchemeEvery B S hS f F p x ↔
      IsWeaklyAssociatedOnFibreEvery B S hS f F p x := by
  constructor
  · intro h θ hθ
    obtain ⟨W, w, hwθ⟩ :=
      exists_chartSchemeToPoints_eq B S hS (fibreAtFieldValuedPoint B S hS f p) θ
    refine hwθ ▸ (isWeaklyAssociatedPoint_fibreRestrictToChart_iff B S hS f F p hF W w).mp
      (h W w ?_)
    rwa [hwθ]
  · intro h W w hw
    exact (isWeaklyAssociatedPoint_fibreRestrictToChart_iff B S hS f F p hF W w).mpr (h _ hw)

/-! ### The conditions over an étale scheme chart of the target -/

/-- **Condition (3) of Stacks 0CUZ on chart schemes of the fibre.** For some étale chart
`V ⟶ Y` by a scheme and some point `v` of `V` above the image of `x`, some point of the scheme
of some étale chart of the fibre of `f` over the residue field of `v`, lying above `x`, is
weakly associated to the restriction of `F` to that chart scheme. -/
noncomputable def IsWeaklyAssociatedOnSomeChartSchemeFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g ∧
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x ∧
    IsWeaklyAssociatedOnFibreChartScheme B S hS f F
      (FieldValuedPoint.map B S hS (yoneda.obj V) g
        (schemePointRepresentative B S hS V v)) x

/-- **Condition (4) of Stacks 0CUZ on chart schemes of the fibre.** For every étale chart
`V ⟶ Y` by a scheme and every point `v` of `V` above the image of `x`, every point of the
scheme of every étale chart of the fibre of `f` over the residue field of `v` which lies above
`x` is weakly associated to the restriction of `F` to that chart scheme. -/
noncomputable def IsWeaklyAssociatedOnEveryChartSchemeFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g →
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x →
    IsWeaklyAssociatedOnFibreChartSchemeEvery B S hS f F
      (FieldValuedPoint.map B S hS (yoneda.obj V) g
        (schemePointRepresentative B S hS V v)) x

/-- The chart-scheme condition on the fibre over the residue field of a point of an étale
scheme chart of `Y` is the fibre condition on the fibre algebraic space, that is condition (1)
of Stacks 0CUZ. -/
theorem isWeaklyAssociatedOnSomeChartSchemeFibre_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1)
    (hF : F.IsQuasicoherentOnSite) :
    IsWeaklyAssociatedOnSomeChartSchemeFibre B S hS f F x ↔
      IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x :=
  exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => isWeaklyAssociatedOnFibreChartScheme_iff B S hS f F _ x hF

/-- The every-point chart-scheme condition on the fibre over the residue field of a point of an
étale scheme chart of `Y` is the every-point fibre condition on the fibre algebraic space, that
is condition (2) of Stacks 0CUZ. -/
theorem isWeaklyAssociatedOnEveryChartSchemeFibre_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1)
    (hF : F.IsQuasicoherentOnSite) :
    IsWeaklyAssociatedOnEveryChartSchemeFibre B S hS f F x ↔
      IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => isWeaklyAssociatedOnFibreChartSchemeEvery_iff B S hS f F _ x hF

/-- The chart-scheme condition on a fibre of `f` places `x` in the relative weak assassin
`WeakAss_{X/Y}(F)`. -/
theorem isRelativeWeaklyAssociatedPoint_of_someChartSchemeFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) {x : points B S hS X.1}
    (hF : F.IsQuasicoherentOnSite)
    (h : IsWeaklyAssociatedOnSomeChartSchemeFibre B S hS f F x) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  isRelativeWeaklyAssociatedPoint_of_someSchemeChart B S hS f F
    ((isWeaklyAssociatedOnSomeChartSchemeFibre_iff B S hS f F x hF).mp h)

/-! ### The conditions for a quasi-coherent module -/

section IsQuasicoherentOnSite

variable (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]

/-- The restriction of a quasi-coherent `𝒪_X`-module to a fibre of `f` over a field-valued point
of `Y` is quasi-coherent. -/
theorem isQuasicoherentOnSite_fibreRestriction (p : FieldValuedPoint B S hS Y.1) :
    ((modulePullback B S hS
      (fibreAtFieldValuedPointProjection B S hS f p)).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (fibreAtFieldValuedPointProjection B S hS f p) F inferInstance

/-- The some-chart condition on chart schemes of the fibre is condition (1) of Stacks 0CUZ,
for a quasi-coherent module. -/
theorem isWeaklyAssociatedOnSomeChartSchemeFibre_iff_of_isQuasicoherentOnSite
    (x : points B S hS X.1) :
    IsWeaklyAssociatedOnSomeChartSchemeFibre B S hS f F x ↔
      IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x :=
  isWeaklyAssociatedOnSomeChartSchemeFibre_iff B S hS f F x inferInstance

/-- The every-chart condition on chart schemes of the fibre is condition (2) of Stacks 0CUZ,
for a quasi-coherent module. -/
theorem isWeaklyAssociatedOnEveryChartSchemeFibre_iff_of_isQuasicoherentOnSite
    (x : points B S hS X.1) :
    IsWeaklyAssociatedOnEveryChartSchemeFibre B S hS f F x ↔
      IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x :=
  isWeaklyAssociatedOnEveryChartSchemeFibre_iff B S hS f F x inferInstance

/-- The some-chart condition on chart schemes of the fibre places `x` in the relative weak
assassin, for a quasi-coherent module. -/
theorem isRelativeWeaklyAssociatedPoint_of_someChartSchemeFibre_of_isQuasicoherentOnSite
    {x : points B S hS X.1}
    (h : IsWeaklyAssociatedOnSomeChartSchemeFibre B S hS f F x) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  isRelativeWeaklyAssociatedPoint_of_someChartSchemeFibre B S hS f F inferInstance h

end IsQuasicoherentOnSite

end AlgebraicGeometry.Space

end
