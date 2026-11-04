module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSlicingGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# An affine étale chart through a prescribed point, smooth over a represented base

The chart construction of **Stacks 06N3** slices the fibre `F = U ×_𝒳 Spec k` at the closed
point of an étale chart of `F` that **Stacks 056U** produces. That density statement is about a
*scheme* smooth over `Spec k`, so what the construction has to produce first is an **affine
étale chart of `F` through a prescribed point of `|F|` whose underlying scheme is smooth over
`Spec k` as a morphism of schemes**. This file produces it.

## Main results

* `AlgebraicGeometry.Space.smooth_chartMap_of_isSmooth`: **Stacks 03ZC**, part (1), read at one
  square — the morphism of schemes in a commuting square of étale charts over a smooth morphism
  of algebraic spaces is smooth.
* `AlgebraicGeometry.Space.smooth_toScheme_map_of_isSmooth_yoneda`: the same with the target
  *represented*, where the square is taken at the identity chart of the representing object, so
  that the scheme morphism is the chart's own structure morphism to the representing scheme.
* `AlgebraicGeometry.Space.exists_affine_smallEtale_smooth_chartScheme_at_point`: the affine
  étale chart through a prescribed point of `|F|`, together with the smoothness of its scheme
  over the representing scheme of the base.
* `Space.exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable`:
  that chart with the slicing point of **Stacks 056U** on it and a geometric point of `F` above
  that point — the whole slicing datum of the chart construction of **Stacks 06N3** at a
  prescribed point of `|F|`.

## Implementation notes

`AlgebraicGeometry.Space.IsSmooth` (**Stacks 03ZC**, part (1)) is
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` at smoothness of scheme morphisms, so reading
it at one square is an application, exactly as
`AlgebraicGeometry.Space.unramified_chartMap_of_isUnramified` reads **Stacks 03ZH**, part (1).

The point of taking the target *represented* is that its identity is an étale chart of it
(`AlgebraicGeometry.Space.isEtaleChart_id_yoneda`), so the square may be taken with
`AlgebraicGeometry.Space.selfChart` on the right and no chart of the base has to be chosen: the
morphism of schemes the square delivers is then the chart's structure morphism to the scheme
underlying the representing object, which is the morphism `V ⟶ Spec k` that **Stacks 056U** is
applied to. The morphism of the site underlying it exists because `yoneda` is full.

The affine chart itself is `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`; its
`(W, b)` together with the étale-chart condition *is* an object of the small étale site, and the
point of `|F|` is reached by `AlgebraicGeometry.Space.chartSchemeToPoints` at the point of the
chart scheme corresponding to the point of the represented presheaf that lemma produces.

The slicing point is `AlgebraicGeometry.Space`
`.exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable`, which takes the chart
as given; nonemptiness of its scheme is supplied by the very point through which the chart was
cut.

## References

* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03ZC, part (1), read at one square.** The morphism of schemes in a commuting square
of étale charts over a smooth morphism of algebraic spaces is smooth. This is what
`AlgebraicGeometry.Space.IsSmooth` says, read at the square the chart construction of
**Stacks 06N3** has. -/
theorem smooth_chartMap_of_isSmooth {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ξ : F ⟶ G}
    (hξ : IsSmooth B S hS ξ) (Vch : SmallEtale B S hS F) (Uch : SmallEtale B S hS G)
    (gVU : Vch.obj.left ⟶ Uch.obj.left)
    (hsq : Vch.obj.hom ≫ ξ = yoneda.map gVU ≫ Uch.obj.hom) :
    Smooth ((BigFppfOver.toScheme B S hS).map gVU) :=
  hξ Vch.obj.left Uch.obj.left Vch.obj.hom Uch.obj.hom gVU Vch.property Uch.property hsq.symm

/-- **The structure morphism of an étale chart over a represented base is smooth.** If
`ξ : F ⟶ yoneda.obj T` is a smooth morphism of algebraic spaces with represented target, then
for every étale chart `Vch` of `F` the morphism of the site under `Vch.obj.hom ≫ ξ` has smooth
underlying morphism of schemes.

The square of `AlgebraicGeometry.Space.smooth_chartMap_of_isSmooth` is taken with the identity
chart `AlgebraicGeometry.Space.selfChart` of `yoneda.obj T` on the right, which is an étale chart
by `AlgebraicGeometry.Space.isEtaleChart_id_yoneda`. -/
theorem smooth_toScheme_map_of_isSmooth_yoneda {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} {ξ : F ⟶ yoneda.obj T} (hξ : IsSmooth B S hS ξ)
    (Vch : SmallEtale B S hS F) {h : Vch.obj.left ⟶ T}
    (hcomm : Vch.obj.hom ≫ ξ = yoneda.map h) :
    Smooth ((BigFppfOver.toScheme B S hS).map h) :=
  smooth_chartMap_of_isSmooth B S hS hξ Vch (selfChart B S hS T) h
    (hcomm.trans (Category.comp_id _).symm)

/-- **Every étale chart of an algebraic space over a represented base has a structure morphism
to the representing object.** `yoneda` is full, so the composite `Vch.obj.hom ≫ ξ` of a chart
with a morphism to a represented presheaf comes from a morphism of the site. -/
theorem exists_hom_comp_eq_yoneda_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (ξ : F ⟶ yoneda.obj T) (Vch : SmallEtale B S hS F) :
    ∃ h : Vch.obj.left ⟶ T, Vch.obj.hom ≫ ξ = yoneda.map h := by
  obtain ⟨h, hh⟩ := yoneda.map_surjective (Vch.obj.hom ≫ ξ)
  exact ⟨h, hh.symm⟩

/-- **The affine étale chart of an algebraic space through a prescribed point, smooth over a
represented base.** Let `ξ : F ⟶ yoneda.obj T` be a smooth morphism of algebraic spaces with
represented target and let `x` be a point of `|F|`. Then there are an étale chart `Vch` of `F`
whose underlying scheme is **affine** and carries a point over `x`, and a morphism of schemes
`π : chartScheme Vch ⟶ T` which is **smooth** and under which the chart lies over `ξ`.

This is the first step of the chart construction of **Stacks 06N3** at a finite type point: the
nonempty affine `V` étale over `F = U ×_𝒳 Spec k` with `V ⟶ Spec k` smooth as a morphism of
schemes, which is the form **Stacks 056U**
(`AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`) is applied
in. The affine chart is `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point` and the
smoothness is `AlgebraicGeometry.Space.smooth_toScheme_map_of_isSmooth_yoneda`. -/
theorem exists_affine_smallEtale_smooth_chartScheme_at_point
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : BigFppfOver B S hS} (ξ : F ⟶ yoneda.obj T) (hξ : IsSmooth B S hS ξ)
    (x : points B S hS F) :
    ∃ (Vch : SmallEtale B S hS F) (h : Vch.obj.left ⟶ T),
      IsAffine (chartScheme Vch) ∧
      Vch.obj.hom ≫ ξ = yoneda.map h ∧
      Smooth ((BigFppfOver.toScheme B S hS).map h) ∧
      ∃ v : chartScheme Vch, chartSchemeToPoints B S hS F Vch v = x := by
  obtain ⟨W, b, hWaff, hbetale, w, hw⟩ := exists_affine_etale_chart_at_point B S hS F hF x
  refine ⟨⟨CostructuredArrow.mk b, hbetale⟩, ?_⟩
  obtain ⟨h, hh⟩ := exists_hom_comp_eq_yoneda_map B S hS ξ ⟨CostructuredArrow.mk b, hbetale⟩
  refine ⟨h, hWaff, hh, smooth_toScheme_map_of_isSmooth_yoneda B S hS hξ _ hh,
    pointsEquivScheme B S hS W w, ?_⟩
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS F
    ⟨CostructuredArrow.mk b, hbetale⟩ (pointsEquivScheme B S hS W w)]
  change pointsMap B S hS (yoneda.obj W) b
    ((pointsEquivScheme B S hS W).symm ((pointsEquivScheme B S hS W) w)) = x
  rw [Equiv.symm_apply_apply]
  exact hw

/-- **The slicing datum of the chart construction of Stacks 06N3 at a prescribed point of the
fibre.** Let `ξ : F ⟶ yoneda.obj T` be a smooth morphism of algebraic spaces whose target is
represented by an object of the site with underlying scheme `Spec k`, and let `x` be a point of
`|F|`. Then there is an **affine** étale chart `Vch` of `F` with a point over `x`, a point `v`
of its scheme which is **closed**, has **regular** local ring and has residue field finite
separable over the residue field of `Spec k`, and a geometric point of `F` — presented as a
geometric point of the presheaf represented by `Vch` — a small étale neighbourhood of which has
chart `Vch` and chart point `v`.

This is the whole of the slicing point of the chart construction of **Stacks 06N3**, produced
through a prescribed point of `|F|`: the chart is
`AlgebraicGeometry.Space.exists_affine_smallEtale_smooth_chartScheme_at_point` — whose point
over `x` is also what makes the chart scheme nonempty, as **Stacks 056U** requires — and the
point on it is
`AlgebraicGeometry.Space.exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable`,
which takes the chart as given. -/
theorem exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable
    (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS} {k : Type u} [Field k]
    (hT : (BigFppfOver.toScheme B S hS).obj T = Spec (.of k))
    (ξ : X.1 ⟶ yoneda.obj T) (hξ : IsSmooth B S hS ξ) (x : points B S hS X.1) :
    ∃ (Vch : SmallEtale B S hS X.1) (π : chartScheme Vch ⟶ Spec (.of k)) (v : chartScheme Vch)
      (y : GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj Vch))),
      IsAffine (chartScheme Vch) ∧
      Smooth π ∧
      (∃ v₀ : chartScheme Vch, chartSchemeToPoints B S hS X.1 Vch v₀ = x) ∧
      chartPoint B S hS X.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X Vch y) = v ∧
        IsClosed ({v} : Set (chartScheme Vch)) ∧
          IsRegularLocalRing ((chartScheme Vch).presheaf.stalk v) ∧
            (letI := (π.residueFieldMap v).hom.toAlgebra;
              Module.Finite ((Spec (.of k)).residueField (π v))
                  ((chartScheme Vch).residueField v) ∧
                Algebra.IsSeparable ((Spec (.of k)).residueField (π v))
                  ((chartScheme Vch).residueField v)) := by
  obtain ⟨Vch, h, hVaff, -, hsm, v₀, hv₀⟩ :=
    exists_affine_smallEtale_smooth_chartScheme_at_point B S hS X.2 ξ hξ x
  have : Smooth ((BigFppfOver.toScheme B S hS).map h) := hsm
  have : Nonempty (chartScheme Vch) := ⟨v₀⟩
  -- the structure morphism of the chart, read into `Spec k` through the given identification
  obtain ⟨v, y, hy, hvclosed, hvreg, hvsep⟩ :=
    exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable B S hS X Vch
      ((BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT)
  exact ⟨Vch, (BigFppfOver.toScheme B S hS).map h ≫ eqToHom hT, v, y, hVaff, inferInstance,
    ⟨v₀, hv₀⟩, hy, hvclosed, hvreg, hvsep⟩

end AlgebraicGeometry.Space

end
