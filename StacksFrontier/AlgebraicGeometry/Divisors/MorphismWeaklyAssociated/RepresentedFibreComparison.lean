module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartSchemeBourbakiTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedChartHenselization

/-!
# The fibre of a represented morphism, and Stacks 0CVV

Let `α : W ⟶ V` be a morphism of the big fppf category over `S` and let `G'` be a
quasi-coherent `𝒪`-module on the algebraic space `W` represents. The fibre of the represented
morphism over a field-valued point `p` of the algebraic space `V` represents is again
represented, by the fibre product `W ×_V p` formed inside the site, because the site has fibre
products and `yoneda` preserves them. On that fibre product the weak association of Stacks 0CTX
on the fibre is the Zariski weak association of Stacks 056L on the representing scheme. Hence
the relative weak assassin `WeakAss_{W/V}(G')` of Stacks 0CV0 is the scheme-level
`WeakAss_{W/V}(G)` of Stacks 05AV of the Zariski chart restriction `G` of `G'`, and the
constructibility statement Stacks 0CVV follows.

## Main definitions

* `AlgebraicGeometry.Space.representedFibreObject` is the fibre product `W ×_V p` in the site,
  and `AlgebraicGeometry.Space.representedFibreProjection` its projection to `W`.
* `AlgebraicGeometry.Space.representedFibreIso` and
  `AlgebraicGeometry.Space.representedFibreSpaceMap`: the fibre of the represented morphism
  over `p` is the algebraic space that fibre product represents.
* `AlgebraicGeometry.Space.representedChartModule` is the Zariski restriction of `G'` to the
  scheme underlying `W`, along the identity chart.
* `AlgebraicGeometry.Space.residueFibreSchemeIso`: at the canonical representative above a
  point `v` of the scheme underlying `V`, the scheme underlying `W ×_V p` is the
  scheme-theoretic fibre over `v`.

## Main results

* `mem_relativeWeaklyAssociatedPoints_of_isWeaklyAssociatedPoint_pullback_fieldValued`:
  **Stacks 0CUC for the base change along a field-valued point**, at the level of schemes: a
  weakly associated point of the pullback of a quasi-coherent module to `X ×_Y Spec k` has its
  image in the relative weak assassin of Stacks 05AV.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_representedFibre_iff`: weak association on
  the fibre is weak association of the inverse image of `G'` on the represented fibre product.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_fibre_iff_pullback_representedChartModule`:
  **the fibre comparison** — that weak association is the Zariski weak association of the
  pullback of the chart restriction of `G'`.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints`:
  **the comparison of Stacks 0CV0 for a represented algebraic space with Stacks 05AV for the
  representing morphism of schemes.**
* `AlgebraicGeometry.Space.exists_etale_surjective_schemeSpace_chart`: an algebraic space over
  the algebraic space of a scheme `V` of the site admits a surjective étale scheme chart
  together with a morphism `α : W ⟶ V` of the site below it.
* `AlgebraicGeometry.Space.locallyOfFinitePresentation_map_of_isLocallyOfFinitePresentation`:
  local finite presentation of a morphism of algebraic spaces passes to such a chart.
* `AlgebraicGeometry.Space.chartOpenOfOpenPoints` and
  `AlgebraicGeometry.Space.mem_chartOpenOfOpenPoints_iff`: an open subset of `|X|` cuts out an
  open subscheme of the chart, whose points are exactly those lying over it.
* `AlgebraicGeometry.Space.isLocallyConstructible_relativeAssassinContainmentLocus` is
  **Stacks 0CVV**.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

namespace AlgebraicGeometry

/-- Weak association to the pullback along a composite `e ≫ g` with `e` étale is weak association
of the image of the point to the pullback along `g`. -/
private theorem isWeaklyAssociatedPoint_pullback_comp_iff_of_etale {A B C : Scheme.{u}}
    (e : A ⟶ B) [Etale e] (g : B ⟶ C) (G : C.Modules) [G.IsQuasicoherent] (t : A) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback (e ≫ g)).obj G) t ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback g).obj G) (e.base t) :=
  have := Stacks.Modules.isQuasicoherent_pullback g G inferInstance
  (Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso
    ((Scheme.Modules.pullbackComp e g).app G).symm t).trans
    (isWeaklyAssociatedPoint_pullback_iff_of_etale e _ t)

/-- **Stacks 0CUC for the base change along a field-valued point.** Let `f : X ⟶ Y` be a
morphism of schemes, let `G` be a quasi-coherent `𝒪_X`-module and let
`h : Spec k ⟶ Y` be a morphism from the spectrum of a field whose image is the point `v`. A
point of `X ×_Y Spec k` which is weakly associated to the pullback of `G` has its image in `X`
in the relative weak assassin `WeakAss_{X/Y}(G)` of Stacks 05AV. -/
theorem mem_relativeWeaklyAssociatedPoints_of_isWeaklyAssociatedPoint_pullback_fieldValued
    {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules) [G.IsQuasicoherent]
    {k : Type u} [Field k] (h : Spec (CommRingCat.of k) ⟶ Y) (v : Y)
    (hv : ∀ y, h y = v) (t : (Limits.pullback f h : Scheme.{u}))
    (ht : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj G) t) :
    Limits.pullback.fst f h t ∈ relativeWeaklyAssociatedPoints f G := by
  obtain ⟨φ, hφ⟩ := exists_residueFieldHom_comp_fromSpecResidueField h v hv
  let : Algebra ↥(Y.residueField v) k := φ.hom.toAlgebra
  have hφalg : CommRingCat.ofHom (algebraMap ↥(Y.residueField v) k) = φ := rfl
  have hsq : IsPullback
      (Limits.pullback.fst (f.fiberToSpecResidueField v) (Spec.map φ) ≫ f.fiberι v)
      (Limits.pullback.snd (f.fiberToSpecResidueField v) (Spec.map φ)) f h := by
    rw [← hφ]
    exact (IsPullback.of_hasPullback (f.fiberToSpecResidueField v) (Spec.map φ)).paste_horiz
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField v))
  set e := (IsPullback.of_hasPullback f h).isoIsPullback _ _ hsq
  have hcomp : e.hom ≫ (Limits.pullback.fst (f.fiberToSpecResidueField v) (Spec.map φ) ≫
      f.fiberι v) = Limits.pullback.fst f h :=
    (IsPullback.of_hasPullback f h).isoIsPullback_hom_fst _ _ hsq
  have hqcfib : ((Scheme.Modules.pullback (f.fiberι v)).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ _ inferInstance
  have h1 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (Limits.pullback.fst (f.fiberToSpecResidueField v)
        (Spec.map φ))).obj ((Scheme.Modules.pullback (f.fiberι v)).obj G)) (e.hom.base t) := by
    refine (Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso
      ((Scheme.Modules.pullbackComp
        (Limits.pullback.fst (f.fiberToSpecResidueField v) (Spec.map φ))
        (f.fiberι v)).app G) (e.hom.base t)).2 ?_
    refine (isWeaklyAssociatedPoint_pullback_comp_iff_of_etale e.hom _ G t).1 ?_
    rwa [hcomp]
  have h2 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (f.fiberι v)).obj G)
      (Limits.pullback.fst (f.fiberToSpecResidueField v) (Spec.map φ) (e.hom.base t)) := by
    have h0 := isWeaklyAssociatedPoint_of_baseChange (k := ↥(Y.residueField v)) (K := k)
      (f.fiberToSpecResidueField v) ((Scheme.Modules.pullback (f.fiberι v)).obj G)
    rw [hφalg] at h0
    exact h0 (e.hom.base t) _ rfl h1
  refine Set.mem_iUnion.2 ⟨v, _, h2, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W V : BigFppfOver B S hS} (α : W ⟶ V)
  (p : FieldValuedPoint B S hS (yoneda.obj V))

/-! ### The fibre of a represented morphism is represented -/

/-- The object of the site presenting the fibre of a represented morphism over a field-valued
point of the target: the fibre product `W ×_V p` formed in the site. -/
noncomputable def representedFibreObject : BigFppfOver B S hS :=
  Limits.pullback α (FieldValuedPoint.siteHom B S hS p)

/-- The projection of the site fibre product `W ×_V p` to `W`. -/
noncomputable def representedFibreProjection :
    representedFibreObject B S hS α p ⟶ W :=
  pullback.fst α (FieldValuedPoint.siteHom B S hS p)

/-- The Yoneda image of the square cutting out `W ×_V p` is cartesian, and its lower edge is the
morphism of presheaves that `p` presents. -/
theorem isPullback_yoneda_representedFibreProjection :
    IsPullback (yoneda.map (representedFibreProjection B S hS α p))
      (yoneda.map (pullback.snd α (FieldValuedPoint.siteHom B S hS p)))
      (yoneda.map α) (fieldMorphism B S hS (yoneda.obj V) p) := by
  rw [fieldMorphism_yoneda B S hS p]
  exact (IsPullback.of_hasPullback α (FieldValuedPoint.siteHom B S hS p)).map yoneda

/-- **The fibre of a represented morphism over a field-valued point of the target is
represented** by the fibre product formed in the site. -/
noncomputable def representedFibreIso :
    (yoneda.obj (representedFibreObject B S hS α p) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ≅
      (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p).1 :=
  -- instance search for this pullback times out: supply it from `HasLimitsOfShape`
  letI : HasPullback (yoneda.map α) (fieldMorphism B S hS (yoneda.obj V) p) :=
    HasLimitsOfShape.has_limit _
  (isPullback_yoneda_representedFibreProjection B S hS α p).isoIsPullback _ _
    (IsPullback.of_hasPullback (yoneda.map α) (fieldMorphism B S hS (yoneda.obj V) p))

/-- The identification of the fibre carries the projection of the fibre to the projection of the
site fibre product. -/
theorem representedFibreIso_hom_comp :
    (representedFibreIso B S hS α p).hom ≫
        (fibreAtFieldValuedPointProjection B S hS (representedSpaceMap B S hS α) p).hom =
      yoneda.map (representedFibreProjection B S hS α p) :=
  (isPullback_yoneda_representedFibreProjection B S hS α p).isoIsPullback_hom_fst _ _ _

/-- The identification of the fibre, as a morphism of algebraic spaces. -/
noncomputable def representedFibreSpaceMap :
    (⟨yoneda.obj (representedFibreObject B S hS α p),
        isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p)⟩ :
      AlgebraicSpaces B S hS) ⟶
    fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p :=
  ObjectProperty.homMk (representedFibreIso B S hS α p).hom

/-- The identification of the fibre, followed by the projection of the fibre, is the morphism of
algebraic spaces represented by the projection of the site fibre product. -/
theorem representedFibreSpaceMap_comp_projection :
    representedFibreSpaceMap B S hS α p ≫
        fibreAtFieldValuedPointProjection B S hS (representedSpaceMap B S hS α) p =
      representedSpaceMap B S hS (representedFibreProjection B S hS α p) :=
  ObjectProperty.hom_ext _ (representedFibreIso_hom_comp B S hS α p)

/-- The identification of the fibre is étale. -/
theorem isEtale_representedFibreSpaceMap :
    IsEtale B S hS (representedFibreSpaceMap B S hS α p).hom :=
  isEtale_of_isIso B S hS (representedFibreIso B S hS α p).hom

/-! ### Weak association on the fibre -/

variable (G' : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))

/-- The inverse image of `G'` along the projection of the site fibre product: the restriction of
`G'` to the fibre, read on the representing object of the fibre. -/
noncomputable abbrev representedFibreModule :
    Modules.{u, u} B S hS (yoneda.obj (representedFibreObject B S hS α p))
      (isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p)) :=
  (modulePullback B S hS
    (representedSpaceMap B S hS (representedFibreProjection B S hS α p))).obj G'

/-- **Weak association on the fibre of a represented morphism, read on the represented fibre
product.** A point of the site fibre product is weakly associated to the inverse image of `G'`
there exactly when the point of the fibre algebraic space it names is weakly associated to the
restriction of `G'` to the fibre. -/
theorem isWeaklyAssociatedPoint_representedFibre_iff
    (θ : points B S hS (yoneda.obj (representedFibreObject B S hS α p))) :
    IsWeaklyAssociatedPoint B S hS
        (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS
          (representedSpaceMap B S hS α) p)).obj G')
        (pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
          (representedFibreSpaceMap B S hS α p).hom θ) ↔
      IsWeaklyAssociatedPoint B S hS
        ⟨yoneda.obj (representedFibreObject B S hS α p),
          isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p)⟩
        (representedFibreModule B S hS α p G') θ := by
  rw [representedFibreModule, ← representedFibreSpaceMap_comp_projection B S hS α p,
    ← isWeaklyAssociatedPoint_modulePullback_iff B S hS (representedFibreSpaceMap B S hS α p)
      (isEtale_representedFibreSpaceMap B S hS α p) _ θ]
  exact isWeaklyAssociatedPoint_congr B S hS
    ((modulePullbackCompIso B S hS (representedFibreSpaceMap B S hS α p)
      (fibreAtFieldValuedPointProjection B S hS (representedSpaceMap B S hS α) p)).app G') θ

/-- The Zariski restriction of `G'` to the scheme underlying `W`, along the identity chart. -/
noncomputable abbrev representedChartModule : ((BigFppfOver.toScheme B S hS).obj W).Modules :=
  restrictToChartScheme B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) G'
    (idEtaleChart B S hS W)

/-- **Stacks 0CTW at the fibre of a represented morphism.** Weak association on the fibre is the
Zariski weak association of the chart restriction of the inverse image of `G'` on the scheme
underlying the site fibre product. -/
theorem isWeaklyAssociatedPoint_fibre_iff_restrictToChart
    (hG' : G'.IsQuasicoherentOnSite)
    (t : (BigFppfOver.toScheme B S hS).obj (representedFibreObject B S hS α p)) :
    IsWeaklyAssociatedPoint B S hS
        (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS
          (representedSpaceMap B S hS α) p)).obj G')
        (pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
          (representedFibreSpaceMap B S hS α p).hom
          ((pointsEquivScheme B S hS (representedFibreObject B S hS α p)).symm t)) ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS
          (isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p))
          (representedFibreModule B S hS α p G')
          (idEtaleChart B S hS (representedFibreObject B S hS α p))) t := by
  have hqc : (representedFibreModule B S hS α p G').IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS (representedFibreProjection B S hS α p)) G' hG'
  rw [isWeaklyAssociatedPoint_representedFibre_iff B S hS α p G']
  exact (isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff B S hS
    (representedFibreObject B S hS α p) (representedFibreModule B S hS α p G') t).symm

/-- The Zariski chart restriction of a quasi-coherent module on the site is quasi-coherent. -/
private theorem isQuasicoherent_representedChartModule (hG' : G'.IsQuasicoherentOnSite) :
    (representedChartModule B S hS G').IsQuasicoherent :=
  isQuasicoherent_restrictToChartScheme B S hS (schemeSpace W) G' hG' (idEtaleChart B S hS W)

/-- **The chart restriction commutes with the fibre.** The Zariski chart restriction of the
inverse image of `G'` along the projection of the site fibre product is the Zariski pullback,
along the underlying morphism of schemes, of the chart restriction of `G'`. -/
theorem isWeaklyAssociatedPoint_restrictToChart_fibre_iff_pullback
    (hG' : G'.IsQuasicoherentOnSite)
    (t : (BigFppfOver.toScheme B S hS).obj (representedFibreObject B S hS α p)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS
          (isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p))
          (representedFibreModule B S hS α p G')
          (idEtaleChart B S hS (representedFibreObject B S hS α p))) t ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (representedFibreProjection B S hS α p))).obj
            (representedChartModule B S hS G')) t :=
  Stacks.Divisors.isWeaklyAssociatedPoint_iff_of_iso
    ((restrictToChartIsoRestrictToChartScheme B S hS
        (isAlgebraicSpace_yoneda B S hS (representedFibreObject B S hS α p))
        (representedFibreModule B S hS α p G')
        (idEtaleChart B S hS (representedFibreObject B S hS α p))) ≪≫
      (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent
        (representedFibreProjection B S hS α p) G' hG').some) t

/-- **The fibre comparison.** For `α : W ⟶ V` a morphism of the site, `G'` a quasi-coherent
`𝒪`-module on the algebraic space `W` represents and `p` a field-valued point of the algebraic
space `V` represents: a point of the scheme underlying the site fibre product `W ×_V p` is
weakly associated, in the Zariski sense of Stacks 056L, to the pullback of the chart restriction
of `G'`, exactly when the point of the fibre algebraic space it names is weakly associated, in
the sense of Stacks 0CTX, to the restriction of `G'` to that fibre. -/
theorem isWeaklyAssociatedPoint_fibre_iff_pullback_representedChartModule
    (hG' : G'.IsQuasicoherentOnSite)
    (t : (BigFppfOver.toScheme B S hS).obj (representedFibreObject B S hS α p)) :
    IsWeaklyAssociatedPoint B S hS
        (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS
          (representedSpaceMap B S hS α) p)).obj G')
        (pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
          (representedFibreSpaceMap B S hS α p).hom
          ((pointsEquivScheme B S hS (representedFibreObject B S hS α p)).symm t)) ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (representedFibreProjection B S hS α p))).obj
            (representedChartModule B S hS G')) t :=
  (isWeaklyAssociatedPoint_fibre_iff_restrictToChart B S hS α p G' hG' t).trans
    (isWeaklyAssociatedPoint_restrictToChart_fibre_iff_pullback B S hS α p G' hG' t)


/-! ### The fibre on the representing schemes -/

/-- The square cutting out `W ×_V p` in the site is carried to a cartesian square of schemes:
the forgetful functor to schemes preserves fibre products. -/
theorem isPullback_toScheme_representedFibre :
    IsPullback ((BigFppfOver.toScheme B S hS).map (representedFibreProjection B S hS α p))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd α (FieldValuedPoint.siteHom B S hS p)))
      ((BigFppfOver.toScheme B S hS).map α)
      ((BigFppfOver.toScheme B S hS).map (FieldValuedPoint.siteHom B S hS p)) :=
  (IsPullback.of_hasPullback α (FieldValuedPoint.siteHom B S hS p)).map
    (BigFppfOver.toScheme B S hS)

/-- At the canonical representative of a point `v` of the representing scheme of `V`, the lower
edge of that square is the morphism from the spectrum of the residue field at `v`. -/
theorem isPullback_toScheme_residueFibre (v : (BigFppfOver.toScheme B S hS).obj V) :
    IsPullback ((BigFppfOver.toScheme B S hS).map
        (representedFibreProjection B S hS α (schemePointRepresentative B S hS V v)))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd α
          (FieldValuedPoint.siteHom B S hS (schemePointRepresentative B S hS V v))))
      ((BigFppfOver.toScheme B S hS).map α)
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v) := by
  rw [← toScheme_map_siteHom_schemePointRepresentative B S hS V v]
  exact isPullback_toScheme_representedFibre B S hS α (schemePointRepresentative B S hS V v)

/-- **The scheme-theoretic fibre is represented.** The scheme underlying the site fibre product
of `α` with the canonical representative above `v` is the scheme-theoretic fibre of the
underlying morphism of schemes over `v`. -/
noncomputable def residueFibreSchemeIso (v : (BigFppfOver.toScheme B S hS).obj V) :
    (BigFppfOver.toScheme B S hS).obj
        (representedFibreObject B S hS α (schemePointRepresentative B S hS V v)) ≅
      ((BigFppfOver.toScheme B S hS).map α).fiber v :=
  (isPullback_toScheme_residueFibre B S hS α v).isoIsPullback _ _
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map α)
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v))

/-- The identification of the scheme-theoretic fibre carries the inclusion of the fibre to the
projection of the site fibre product. -/
theorem residueFibreSchemeIso_hom_comp (v : (BigFppfOver.toScheme B S hS).obj V) :
    (residueFibreSchemeIso B S hS α v).hom ≫
        ((BigFppfOver.toScheme B S hS).map α).fiberι v =
      (BigFppfOver.toScheme B S hS).map
        (representedFibreProjection B S hS α (schemePointRepresentative B S hS V v)) :=
  (isPullback_toScheme_residueFibre B S hS α v).isoIsPullback_hom_fst _ _ _

/-- Zariski weak association on the scheme underlying the site fibre product over the canonical
representative of `v` is Zariski weak association on the scheme-theoretic fibre over `v`. -/
theorem isWeaklyAssociatedPoint_pullback_residueFibre_iff
    (hG' : G'.IsQuasicoherentOnSite) (v : (BigFppfOver.toScheme B S hS).obj V)
    (t : (BigFppfOver.toScheme B S hS).obj
      (representedFibreObject B S hS α (schemePointRepresentative B S hS V v))) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
          (representedFibreProjection B S hS α
            (schemePointRepresentative B S hS V v)))).obj
              (representedChartModule B S hS G')) t ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).map α).fiberι v)).obj
          (representedChartModule B S hS G'))
        ((residueFibreSchemeIso B S hS α v).hom.base t) := by
  have := isQuasicoherent_representedChartModule B S hS G' hG'
  rw [← residueFibreSchemeIso_hom_comp B S hS α v]
  exact isWeaklyAssociatedPoint_pullback_comp_iff_of_etale _ _ _ t

/-! ### The comparison, from the scheme side -/

/-- A point of the site fibre product has the same image in `W` as its image in the fibre
algebraic space followed by the projection of the fibre. -/
private theorem pointsMap_projection_pointsMap_representedFibreSpaceMap
    (θ : points B S hS (yoneda.obj (representedFibreObject B S hS α p))) :
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p).1
        (fibreAtFieldValuedPointProjection B S hS (representedSpaceMap B S hS α) p).hom
        (pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
          (representedFibreSpaceMap B S hS α p).hom θ) =
      pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
        (yoneda.map (representedFibreProjection B S hS α p)) θ := by
  rw [← representedFibreIso_hom_comp B S hS α p, pointsMap_comp]
  rfl

/-- A point of the scheme-theoretic relative weak assassin of the chart restriction lies in the
relative weak assassin of Stacks 0CV0 of `G'`. -/
theorem isRelativeWeaklyAssociatedPoint_of_mem_relativeWeaklyAssociatedPoints
    (hG' : G'.IsQuasicoherentOnSite) (w : points B S hS (yoneda.obj W))
    (hw : pointsToScheme B S hS W w ∈
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α) (representedChartModule B S hS G')) :
    IsRelativeWeaklyAssociatedPoint B S hS (representedSpaceMap B S hS α) G' w := by
  obtain ⟨v, θ, hθ, hθw⟩ := Set.mem_iUnion.1 hw
  set q := schemePointRepresentative B S hS V v
  obtain ⟨t, hti⟩ : ∃ t, (residueFibreSchemeIso B S hS α v).hom.base t = θ :=
    ⟨_, Scheme.inv_hom_apply (residueFibreSchemeIso B S hS α v) θ⟩
  have hzar : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
        (representedFibreProjection B S hS α q))).obj
          (representedChartModule B S hS G')) t :=
    (isWeaklyAssociatedPoint_pullback_residueFibre_iff B S hS α G' hG' v t).2 (hti ▸ hθ)
  have hfib := (isWeaklyAssociatedPoint_fibre_iff_pullback_representedChartModule B S hS α q G'
    hG' t).2 hzar
  have hproj : pointsMap B S hS
      (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) q).1
      (fibreAtFieldValuedPointProjection B S hS (representedSpaceMap B S hS α) q).hom
      (pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α q))
        (representedFibreSpaceMap B S hS α q).hom
        ((pointsEquivScheme B S hS (representedFibreObject B S hS α q)).symm t)) = w := by
    rw [pointsMap_projection_pointsMap_representedFibreSpaceMap B S hS α q,
      pointsMap_yoneda_map_symm B S hS (representedFibreProjection B S hS α q) t]
    apply (pointsEquivScheme B S hS W).symm_apply_eq.2
    show ((BigFppfOver.toScheme B S hS).map (representedFibreProjection B S hS α q)) t =
      pointsToScheme B S hS W w
    rw [← hθw, ← hti, ← Scheme.Hom.comp_apply,
      residueFibreSchemeIso_hom_comp B S hS α v]
  have hclass : q.class B S hS (yoneda.obj V) =
      pointsMap B S hS (yoneda.obj W) (representedSpaceMap B S hS α).hom w := by
    apply (injective_pointsToScheme B S hS V)
    rw [pointsToScheme_class]
    show schemePoint B S hS V q = pointsToScheme B S hS V
      (pointsMap B S hS (yoneda.obj W) (yoneda.map α) w)
    rw [pointsToScheme_pointsMap_yoneda B S hS α w,
      schemePointRepresentative_point B S hS V v, ← hθw]
    exact (((BigFppfOver.toScheme B S hS).map α).apply_fiberι v θ).symm
  exact ⟨q, hclass, _, hproj, hfib⟩

/-! ### The comparison, from the space side -/

/-- A Zariski weakly associated point on the scheme underlying the site fibre product over a
field-valued point has its image in the scheme-theoretic relative weak assassin. -/
theorem mem_relativeWeaklyAssociatedPoints_of_isWeaklyAssociatedPoint_representedFibre
    (hG' : G'.IsQuasicoherentOnSite)
    (t : (BigFppfOver.toScheme B S hS).obj (representedFibreObject B S hS α p))
    (ht : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map
        (representedFibreProjection B S hS α p))).obj (representedChartModule B S hS G')) t) :
    (BigFppfOver.toScheme B S hS).map (representedFibreProjection B S hS α p) t ∈
      _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α) (representedChartModule B S hS G') := by
  have := isQuasicoherent_representedChartModule B S hS G' hG'
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (FieldValuedPoint.siteObject B S hS (yoneda.obj V) p)) :=
    subsingleton_toScheme_siteObject B S hS (yoneda.obj V) p
  set h := (BigFppfOver.toScheme B S hS).map (FieldValuedPoint.siteHom B S hS p)
  have hv : ∀ y, h y = schemePoint B S hS V p := fun y =>
    congrArg (fun z => (BigFppfOver.toScheme B S hS).map
      (FieldValuedPoint.siteHom B S hS p) z)
      (Subsingleton.elim y (IsLocalRing.closedPoint p.carrier))
  set d := (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map α) h).isoIsPullback _ _
    (isPullback_toScheme_representedFibre B S hS α p)
  have hdcomp : d.hom ≫ (BigFppfOver.toScheme B S hS).map
      (representedFibreProjection B S hS α p) =
      Limits.pullback.fst ((BigFppfOver.toScheme B S hS).map α) h :=
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map α) h).isoIsPullback_hom_fst
      _ _ (isPullback_toScheme_representedFibre B S hS α p)
  have hdt : d.hom.base (d.inv.base t) = t := Scheme.inv_hom_apply d t
  have h1 : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback
        (Limits.pullback.fst ((BigFppfOver.toScheme B S hS).map α) h)).obj
          (representedChartModule B S hS G')) (d.inv.base t) := by
    rw [← hdcomp]
    exact (isWeaklyAssociatedPoint_pullback_comp_iff_of_etale d.hom _ _ _).2 (by rwa [hdt])
  have h2 := mem_relativeWeaklyAssociatedPoints_of_isWeaklyAssociatedPoint_pullback_fieldValued
    (k := p.carrier) ((BigFppfOver.toScheme B S hS).map α)
    (representedChartModule B S hS G') h (schemePoint B S hS V p) hv (d.inv.base t) h1
  rwa [← hdcomp, Scheme.Hom.comp_apply, hdt] at h2

/-! ### The comparison of Stacks 0CV0 with Stacks 05AV for a represented morphism -/

/-- **The comparison of Stacks 0CV0 for a represented algebraic space with Stacks 05AV for the
representing morphism of schemes.** For `α : W ⟶ V` a morphism of the site and `G'` a
quasi-coherent `𝒪`-module on the algebraic space `W` represents, a point of that algebraic space
lies in the relative weak assassin `WeakAss_{W/V}(G')` of Stacks 0CV0 exactly when the
corresponding point of the scheme `W` lies in the scheme-level relative weak assassin
`WeakAss_{W/V}(G)` of Stacks 05AV of the Zariski chart restriction `G` of `G'`. -/
theorem isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints
    (hG' : G'.IsQuasicoherentOnSite) (w : points B S hS (yoneda.obj W)) :
    IsRelativeWeaklyAssociatedPoint B S hS (representedSpaceMap B S hS α) G' w ↔
      pointsToScheme B S hS W w ∈
        _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
          ((BigFppfOver.toScheme B S hS).map α) (representedChartModule B S hS G') := by
  refine ⟨?_, isRelativeWeaklyAssociatedPoint_of_mem_relativeWeaklyAssociatedPoints
    B S hS α G' hG' w⟩
  rintro ⟨p, -, θs, hθs, hwa⟩
  set θ' := pointsMap B S hS
    (fibreAtFieldValuedPoint B S hS (representedSpaceMap B S hS α) p).1
    (representedFibreIso B S hS α p).inv θs
  have hEθ : pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
      (representedFibreSpaceMap B S hS α p).hom θ' = θs := by
    show pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
      (representedFibreIso B S hS α p).hom (pointsMap B S hS _
        (representedFibreIso B S hS α p).inv θs) = θs
    rw [← Function.comp_apply (f := pointsMap B S hS _
      (representedFibreIso B S hS α p).hom), ← pointsMap_comp,
      (representedFibreIso B S hS α p).inv_hom_id, pointsMap_id]
    rfl
  set t := pointsEquivScheme B S hS (representedFibreObject B S hS α p) θ' with ht
  have hsymm : (pointsEquivScheme B S hS (representedFibreObject B S hS α p)).symm t = θ' := by
    rw [ht, Equiv.symm_apply_apply]
  have hzar := (isWeaklyAssociatedPoint_fibre_iff_pullback_representedChartModule B S hS α p G'
    hG' t).1 (by rwa [hsymm, hEθ])
  have himg : (BigFppfOver.toScheme B S hS).map
      (representedFibreProjection B S hS α p) t = pointsToScheme B S hS W w := by
    have hproj : pointsMap B S hS (yoneda.obj (representedFibreObject B S hS α p))
        (yoneda.map (representedFibreProjection B S hS α p)) θ' = w := by
      rw [← pointsMap_projection_pointsMap_representedFibreSpaceMap B S hS α p, hEθ]
      exact hθs
    rw [← hproj, pointsToScheme_pointsMap_yoneda B S hS
      (representedFibreProjection B S hS α p) θ']
    exact congrArg ((BigFppfOver.toScheme B S hS).map
      (representedFibreProjection B S hS α p)) ht.symm
  rw [← himg]
  exact mem_relativeWeaklyAssociatedPoints_of_isWeaklyAssociatedPoint_representedFibre
    B S hS α p G' hG' t hzar

/-! ### Étale scheme charts over a represented base -/

/-- **A surjective étale scheme chart of an algebraic space over a scheme, together with the
morphism of the site underneath it.** For an algebraic space `X` with a morphism
`f : X ⟶ schemeSpace V` to the algebraic space of a scheme `V` of the site, there are a scheme
`W` of the site, an étale morphism `φ : schemeSpace W ⟶ X` which is surjective on points, and a
morphism `α : W ⟶ V` of the site with `φ ≫ f = schemeSpaceMap α`. -/
theorem exists_etale_surjective_schemeSpace_chart {X : AlgebraicSpaces B S hS}
    (V₀ : BigFppfOver B S hS) (f : X ⟶ schemeSpace V₀) :
    ∃ (W₀ : BigFppfOver B S hS) (φ : schemeSpace W₀ ⟶ X) (α₀ : W₀ ⟶ V₀),
      IsEtale B S hS φ.hom ∧
        Function.Surjective (pointsMap B S hS (schemeSpace W₀).1 φ.hom) ∧
          φ ≫ f = schemeSpaceMap α₀ := by
  obtain ⟨W₀, a, hasurj, haetale⟩ := X.2.exists_atlas
  obtain ⟨α₀, hα₀⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (a ≫ f.hom)
  refine ⟨W₀, ObjectProperty.homMk a, α₀,
    (isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 W₀ a).1 hasurj,
    ObjectProperty.hom_ext _ hα₀.symm⟩

/-- **Local finite presentation of a morphism of algebraic spaces passes to an étale scheme
chart over the base.** If `f : X ⟶ schemeSpace V` is locally of finite presentation, `φ` is an
étale chart of `X` and `α : W ⟶ V` is a morphism of the site with
`φ ≫ f = schemeSpaceMap α`, then the morphism of schemes underlying `α` is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_map_of_isLocallyOfFinitePresentation
    {X : AlgebraicSpaces B S hS} {V₀ W₀ : BigFppfOver B S hS} {f : X ⟶ schemeSpace V₀}
    (hf : IsLocallyOfFinitePresentation B S hS f.hom) {φ : schemeSpace W₀ ⟶ X}
    (hφ : IsEtale B S hS φ.hom) {α₀ : W₀ ⟶ V₀} (hα : φ ≫ f = schemeSpaceMap α₀) :
    _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map α₀) := by
  refine hf W₀ V₀ φ.hom (𝟙 (yoneda.obj V₀)) α₀
    ((isEtale_iff_presheaf_of_yoneda B S hS φ.hom).1 hφ)
    (presheaf_id_of_iso B S hS _ (fun _ _ g hg => ?_) V₀) ?_
  · have hiso : IsIso g := hg
    show _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  · show yoneda.map α₀ ≫ 𝟙 (yoneda.obj V₀) = φ.hom ≫ f.hom
    rw [Category.comp_id]
    exact (congrArg InducedCategory.Hom.hom hα).symm

/-- **The open subscheme of an étale scheme chart cut out by an open subset of the points of an
algebraic space.** For a chart `φ : schemeSpace W ⟶ X` and an open subset `U` of `|X|`, the
open subscheme `φ⁻¹(U)` of `W`: the image in the scheme `W` of the inverse image of `U` under
the map on points induced by `φ`. -/
noncomputable def chartOpenOfOpenPoints {X : AlgebraicSpaces B S hS}
    (W₀ : BigFppfOver B S hS) (φ : schemeSpace W₀ ⟶ X) (U : Set (points B S hS X.1))
    (hU : @IsOpen _ (pointTopology B S hS X.1) U) :
    ((BigFppfOver.toScheme B S hS).obj W₀).Opens where
  carrier := pointsToScheme B S hS W₀ '' (pointsMap B S hS (schemeSpace W₀).1 φ.hom ⁻¹' U)
  is_open' := (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS W₀ _).1 <|
    @Continuous.isOpen_preimage _ _ (pointTopology B S hS (schemeSpace W₀).1)
      (pointTopology B S hS X.1) _ (continuous_pointsMap B S hS φ.hom) U hU

/-- A point of the chart lies in the open subscheme `φ⁻¹(U)` exactly when its image in `|X|`
lies in `U`. -/
theorem mem_chartOpenOfOpenPoints_iff {X : AlgebraicSpaces B S hS}
    (W₀ : BigFppfOver B S hS) (φ : schemeSpace W₀ ⟶ X) (U : Set (points B S hS X.1))
    (hU : @IsOpen _ (pointTopology B S hS X.1) U)
    (w : points B S hS (schemeSpace W₀).1) :
    schemeSpacePointToScheme B S hS W₀ w ∈ chartOpenOfOpenPoints B S hS W₀ φ U hU ↔
      pointsMap B S hS (schemeSpace W₀).1 φ.hom w ∈ U :=
  (injective_pointsToScheme B S hS W₀).mem_set_image

/-! ### Stacks 0CVV -/

/-- Let `V` be a scheme of the site, let `f : X ⟶ schemeSpace V` be a morphism of algebraic
spaces which is locally of finite presentation, let `F` be a quasi-coherent `𝒪_X`-module and let
`U` be an open subset of `|X|`. Let `φ : schemeSpace W ⟶ X` be a surjective étale scheme chart
and `α : W ⟶ V` a quasi-compact and quasi-separated morphism of the site with
`φ ≫ f = schemeSpaceMap α`, such that the chart restriction of `F` is of finite presentation
and `φ⁻¹(U)` is quasi-compact over `V`. Then the set of points `y` of `V` over which every point
of the relative assassin of `F` above `y` lies in `U` is locally constructible in `V`. -/
@[stacks 0CVV "the surjective etale scheme chart of X is a hypothesis rather than a \
construction, and so are the transfers along it of quasi-compactness and quasi-separatedness \
of alpha, of finite presentation of the chart restriction of F, and of quasi-compactness of \
U over V"]
theorem isLocallyConstructible_relativeAssassinContainmentLocus
    {X : AlgebraicSpaces B S hS} (V W : BigFppfOver B S hS)
    (f : X ⟶ schemeSpace V) (F : Modules.{u, u} B S hS X.1 X.2)
    (U : Set (points B S hS X.1)) (hUopen : @IsOpen _ (pointTopology B S hS X.1) U)
    (φ : schemeSpace W ⟶ X)
    (hφ : IsEtale B S hS φ.hom)
    (hsurj : Function.Surjective (pointsMap B S hS (schemeSpace W).1 φ.hom))
    (α : W ⟶ V) (hα : φ ≫ f = schemeSpaceMap α)
    (hfX : IsLocallyOfFinitePresentation B S hS f.hom)
    (hαqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map α))
    (hαqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map α))
    (hF : F.IsQuasicoherentOnSite)
    (hGfp : (baseChangeModule B S hS F W φ.hom).IsFinitePresentation)
    (hUqc : QuasiCompact ((chartOpenOfOpenPoints B S hS W φ U hUopen).ι ≫
      (BigFppfOver.toScheme B S hS).map α)) :
    IsLocallyConstructible (relativeAssassinContainmentLocus B S hS V f F U) := by
  obtain ⟨Uw, hUw, hUwqc⟩ : ∃ Uw : ((BigFppfOver.toScheme B S hS).obj W).Opens,
      (∀ w : points B S hS (schemeSpace W).1,
          schemeSpacePointToScheme B S hS W w ∈ Uw ↔
            pointsMap B S hS (schemeSpace W).1 φ.hom w ∈ U) ∧
        QuasiCompact (Uw.ι ≫ (BigFppfOver.toScheme B S hS).map α) :=
    ⟨chartOpenOfOpenPoints B S hS W φ U hUopen,
      fun w => mem_chartOpenOfOpenPoints_iff B S hS W φ U hUopen w, hUqc⟩
  have := hUwqc
  have hfp : AlgebraicGeometry.FinitePresentation
      ((BigFppfOver.toScheme B S hS).map α) :=
    ⟨locallyOfFinitePresentation_map_of_isLocallyOfFinitePresentation B S hS hfX hφ hα,
      hαqc, hαqs⟩
  set G' : Modules.{u, u} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) :=
    (modulePullback B S hS φ).obj F with hG'def
  have hG' : G'.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ F hF
  set G : ((BigFppfOver.toScheme B S hS).obj W).Modules :=
    representedChartModule B S hS G' with hGdef
  have hqc : G.IsQuasicoherent := isQuasicoherent_representedChartModule B S hS G' hG'
  have : G.IsFinitePresentation := hGfp
  have hAss : ∀ w : points B S hS (schemeSpace W).1,
      IsRelativeWeaklyAssociatedPoint B S hS (schemeSpaceMap α) G' w ↔
        schemeSpacePointToScheme B S hS W w ∈
          _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
            ((BigFppfOver.toScheme B S hS).map α) G :=
    fun w => isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints
      B S hS α G' hG' w
  have hchart := relativeAssassinContainmentLocus_modulePullback B S hS V f F U φ hφ hsurj
  rw [← hchart, hα]
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α) := hfp.1
  have hra : _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α) G =
      Stacks.Divisors.relativeAssassin ((BigFppfOver.toScheme B S hS).map α) G :=
    _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin _ G
  have key : relativeAssassinContainmentLocus B S hS V (schemeSpaceMap α)
        ((modulePullback B S hS φ).obj F)
        (pointsMap B S hS (schemeSpace W).1 φ.hom ⁻¹' U) =
      Stacks.RelativeAssassin.fibrewiseContainment
        ((BigFppfOver.toScheme B S hS).map α) G Uw := by
    ext y
    rw [mem_relativeAssassinContainmentLocus_iff,
      Stacks.RelativeAssassin.mem_fibrewiseContainment]
    constructor
    · intro h θ hθ
      obtain ⟨w, hw⟩ := surjective_schemeSpacePointToScheme B S hS W
        (((BigFppfOver.toScheme B S hS).map α).fiberι y θ)
      have hrel : w ∈ relativeWeaklyAssociatedPoints B S hS (schemeSpaceMap α)
          ((modulePullback B S hS φ).obj F) := by
        refine (hAss w).2 ?_
        rw [hw, hra]
        exact (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
          ((BigFppfOver.toScheme B S hS).map α) G y θ).1 hθ
      have hy : schemeSpacePointToScheme B S hS V
          (pointsMap B S hS (schemeSpace W).1
            (schemeSpaceMap α).hom w) = y := by
        rw [schemeSpacePointToScheme_pointsMap B S hS α w, hw]
        exact ((BigFppfOver.toScheme B S hS).map α).apply_fiberι y θ
      have h2 := h w hrel hy
      rwa [Set.mem_preimage, ← hUw w, hw] at h2
    · intro h w hw hwy
      obtain ⟨θ, hθ⟩ : schemeSpacePointToScheme B S hS W w ∈
          Set.range (((BigFppfOver.toScheme B S hS).map α).fiberι y) := by
        rw [((BigFppfOver.toScheme B S hS).map α).range_fiberι y]
        exact (schemeSpacePointToScheme_pointsMap B S hS α w).symm.trans hwy
      have hmemra : schemeSpacePointToScheme B S hS W w ∈
          Stacks.Divisors.relativeAssassin ((BigFppfOver.toScheme B S hS).map α) G :=
        hra ▸ (hAss w).1 hw
      have hθass : θ ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback
            (((BigFppfOver.toScheme B S hS).map α).fiberι y)).obj G) :=
        (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
          ((BigFppfOver.toScheme B S hS).map α) G y θ).2 (hθ ▸ hmemra)
      rw [Set.mem_preimage, ← hUw w, ← hθ]
      exact h hθass
  rw [key]
  exact Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment
    ((BigFppfOver.toScheme B S hS).map α) hfp G Uw

end AlgebraicGeometry.Space

end
