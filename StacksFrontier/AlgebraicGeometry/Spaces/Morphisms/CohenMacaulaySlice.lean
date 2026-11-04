module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedChartTopStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFactorisationLargeField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartNeighborhoodCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreRegularSequenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceChartFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringAffineCharts
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge

/-!
# Slicing a flat morphism of algebraic spaces by a regular sequence

Let `X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally of
finite presentation, let `Spec(k) ⟶ Y` be a point of the target with `k` a field over `S`, let
`F = X ×_Y Spec(k)` be the fibre and let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`.  Stacks 06LW asserts that if
the `f_i` have regular images in the étale local ring of `F` at a geometric point `z`, then,
after replacing `X` by an open subspace containing the image of `z`, the closed subspace
`V(f₁, …, f_r)` of `AlgebraicGeometry.Space.vanishingSubfunctor` is flat and locally of finite
presentation over `Y`.

## Main definitions

* `AlgebraicGeometry.Space.FibreIsRegularSequenceAt`: the hypothesis of Stacks 06LW that the
  `f_i` map to a regular sequence in the étale local ring of the fibre at a geometric point.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq_vanishingIdealAt`: the defining
  ideal of `V(f₁, …, f_r)` on an affine étale chart is the ideal generated there by the
  restricted functions.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_vanishingSubfunctor`: the closed
  immersion `V(f₁, …, f_r) ⟶ X` is locally of finite presentation.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_vanishingSubfunctor_comp_unconditional`
  and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_preimage_vanishingSubfunctor_comp`:
  if `X ⟶ Y` is locally of finite presentation, then so is `V(f₁, …, f_r) ⟶ Y`, on the whole of
  `X` and on an arbitrary open subspace of it.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_vanishingSubfunctor_comp`: the same on
  the whole of `X`, given that `V(f₁, …, f_r) ⟶ X` is locally of finite presentation.
* `exists_openSubspace_isFlat_isLocallyOfFinitePresentation_vanishingSubfunctor`: Stacks 06LW,
  after replacing `X` by an open subspace containing the image of `z`, `V(f₁, …, f_r) ⟶ Y` is
  flat and locally of finite presentation.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_top` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_ι_vanishingSubfunctor_of_isEmpty`: the
  inclusion of the whole space, and of the subspace cut out by the empty family of functions, are
  locally of finite presentation.

## References

* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 03FY](https://stacks.math.columbia.edu/tag/03FY)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03XQ](https://stacks.math.columbia.edu/tag/03XQ)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The defining ideal of `V(f₁, …, f_r)` on an affine étale chart -/

/-- The defining ideal of `V(f₁, …, f_r)` on an affine étale chart is the ideal generated there by
the restrictions of the functions. -/
theorem definingIdealAt_vanishingSubspace_eq_vanishingIdealAt (X : AlgebraicSpaces B S hS)
    {r : ℕ} (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1) :
    definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op U) =
      vanishingIdealAt B S hS X f U := by
  obtain ⟨Z, -, hZid⟩ := exists_vanishingSubfunctor_eq B S hS X f
  refine definingIdealAt_vanishingSubspace_eq B S hS X f Z (fun V hV ↦ ?_) U hU
  rw [← definingIdealSheaf_obj B S hS X Z (op V), hZid,
    vanishingIdealSheaf_obj_of_isAffine B S hS X f V hV]

/-- The ideal generated on an étale chart by finitely many global regular functions is finitely
generated. -/
theorem fg_vanishingIdealAt (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1) : (vanishingIdealAt B S hS X f U).FG :=
  Submodule.fg_span (Set.finite_range _)

/-- The defining ideal of `V(f₁, …, f_r)` on an affine étale chart is finitely generated. -/
theorem fg_definingIdealAt_vanishingSubspace (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj U).1) :
    (definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op U)).FG := by
  rw [definingIdealAt_vanishingSubspace_eq_vanishingIdealAt B S hS X f U hU]
  exact fg_vanishingIdealAt B S hS X f U

/-! ### Local finite presentation of the closed immersion `V(f₁, …, f_r) ⟶ X` -/

/-- The inclusion of the whole of an algebraic space is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_ι_top (X : AlgebraicSpaces B S hS) :
    IsLocallyOfFinitePresentation B S hS (⊤ : Subfunctor X.1).ι := by
  intro U V a b k ha hb hsq
  have := etale_of_comp_etale_chart B S hS
    (MorphismProperty.RespectsIso.postcomp _ (⊤ : Subfunctor X.1).ι a ha) hb hsq
  infer_instance

/-- The empty family of functions cuts out a subspace whose inclusion is locally of finite
presentation. -/
theorem isLocallyOfFinitePresentation_ι_vanishingSubfunctor_of_isEmpty
    (X : AlgebraicSpaces B S hS) {r : ℕ} [IsEmpty (Fin r)]
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    IsLocallyOfFinitePresentation B S hS (vanishingSubfunctor B S hS X f).ι := by
  rw [vanishingSubfunctor_isEmpty B S hS X f]
  exact isLocallyOfFinitePresentation_ι_top B S hS X

/-- `V(f₁, …, f_r) ⟶ X` is locally of finite presentation over an algebraic space carrying a
surjective étale chart whose underlying scheme is affine. -/
theorem isLocallyOfFinitePresentation_ι_vanishingSubfunctor_of_affineEtaleChart
    (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {V : BigFppfOver B S hS} {b : yoneda.obj V ⟶ X.1}
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hbEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbSurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    IsLocallyOfFinitePresentation B S hS (vanishingSubfunctor B S hS X f).ι := by
  refine ((isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (ObjectProperty.homMk (vanishingSubfunctor B S hS X f).ι :
      (⟨(vanishingSubfunctor B S hS X f).toFunctor,
        (vanishingSubfunctor_isClosedSubspace B S hS X f).1⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (vanishingSubfunctor_isClosedSubspace B S hS X f).2 hbEtale hbSurj).2 fun A ↦ ?_).1
  set U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hbEtale⟩
  rw [ker_chartBaseChangeHom B S hS X (vanishingSubspace B S hS X f) U hVaff]
  exact (fg_definingIdealAt_vanishingSubspace B S hS X f U hVaff).map _

/-- The closed immersion `V(f₁, …, f_r) ⟶ X` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_ι_vanishingSubfunctor (X : AlgebraicSpaces B S hS)
    {r : ℕ} (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) :
    IsLocallyOfFinitePresentation B S hS (vanishingSubfunctor B S hS X f).ι := by
  obtain ⟨I, W, hcov, hchart⟩ := exists_zariski_cover_affine_etale_atlas B S hS X.1 X.2
  refine isLocallyOfFinitePresentation_of_zariskiCover B S hS
    (vanishingSubfunctor_isClosedSubspace B S hS X f).1 X.2 _ hcov fun idx ↦ ?_
  obtain ⟨_Wobj, bchart, _Vopen, hWaff, hbSurj, hbEtale, _, _⟩ := hchart idx
  have hres := isLocallyOfFinitePresentation_ι_vanishingSubfunctor_of_affineEtaleChart B S hS
    (⟨(W idx).toFunctor, (hcov.1 idx).1⟩ : AlgebraicSpaces B S hS)
    (fun j ↦ unitSectionsRestrict B S hS
      (ObjectProperty.homMk (W idx).ι :
        (⟨(W idx).toFunctor, (hcov.1 idx).1⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (isEtale_of_isOpenImmersion B S hS (hcov.1 idx).2) (f j))
    (b := bchart) hWaff hbEtale hbSurj
  rw [vanishingSubfunctor_restrict_eq_preimage B S hS _
    (isEtale_of_isOpenImmersion B S hS (hcov.1 idx).2) f
    (definingIdealAt_vanishingSubspace_eq_vanishingIdealAt B S hS X f),
    ObjectProperty.homMk_hom] at hres
  have hsq := Subfunctor.isPullback_preimage (W idx).ι (vanishingSubfunctor B S hS X f)
  have hpre := (isClosedSubspace_preimage B S hS (W idx).ι (vanishingSubfunctor B S hS X f) X.2
    (hcov.1 idx).1 (vanishingSubfunctor_isClosedSubspace B S hS X f)).1
  rw [show pullback.snd (vanishingSubfunctor B S hS X f).ι (W idx).ι =
      hsq.isoPullback.inv ≫ ((vanishingSubfunctor B S hS X f).preimage (W idx).ι).ι from
    hsq.isoPullback_inv_snd.symm]
  exact isLocallyOfFinitePresentation_comp B S hS
    (isAlgebraicSpace_pullback B S hS (vanishingSubfunctor B S hS X f).ι (W idx).ι
      (vanishingSubfunctor_isClosedSubspace B S hS X f).1 (hcov.1 idx).1 X.2)
    hpre (hcov.1 idx).1 _ _
    (isLocallyOfFinitePresentation_of_isEtale B S hS
      (isEtale_of_isIso B S hS hsq.isoPullback.inv)) hres

/-- If `X ⟶ Y` is locally of finite presentation then so is `V(f₁, …, f_r) ⟶ Y` for the closed
subspace `V(f₁, …, f_r) ⊆ X` cut out by finitely many global regular functions. -/
theorem isLocallyOfFinitePresentation_vanishingSubfunctor_comp_unconditional
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS ((vanishingSubfunctor B S hS X f).ι ≫ g) :=
  isLocallyOfFinitePresentation_comp B S hS
    (vanishingSubfunctor_isClosedSubspace B S hS X f).1 X.2 Y.2 _ g
    (isLocallyOfFinitePresentation_ι_vanishingSubfunctor B S hS X f) hg

/-- If `X ⟶ Y` is locally of finite presentation and the closed immersion of the subspace
`V(f₁, …, f_r) ⊆ X` cut out by global regular functions `f₁, …, f_r` is locally of finite
presentation, then so is `V(f₁, …, f_r) ⟶ Y`. -/
@[stacks 06LW "locally of finite presentation, given it for V(f₁,…,f_r) ⟶ X"]
theorem isLocallyOfFinitePresentation_vanishingSubfunctor_comp (X Y : AlgebraicSpaces B S hS)
    (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (hslice : IsLocallyOfFinitePresentation B S hS (vanishingSubfunctor B S hS X f).ι)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS ((vanishingSubfunctor B S hS X f).ι ≫ g) :=
  isLocallyOfFinitePresentation_comp B S hS
    (vanishingSubfunctor_isClosedSubspace B S hS X f).1 X.2 Y.2 _ g hslice hg

/-- If `X ⟶ Y` is locally of finite presentation, then for every open subspace `V ⊆ X` the
restriction `V(f₁, …, f_r) ∩ V ⟶ V ⟶ Y` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_ι_preimage_vanishingSubfunctor_comp
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (V : Subfunctor X.1) (hV : IsOpenSubspace B S hS V)
    (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsLocallyOfFinitePresentation B S hS
      (((vanishingSubfunctor B S hS X f).preimage V.ι).ι ≫ V.ι ≫ g) := by
  have hsq := Subfunctor.isPullback_preimage V.ι (vanishingSubfunctor B S hS X f)
  have hpre := (isClosedSubspace_preimage B S hS V.ι (vanishingSubfunctor B S hS X f) X.2
    hV.1 (vanishingSubfunctor_isClosedSubspace B S hS X f)).1
  refine isLocallyOfFinitePresentation_comp B S hS hpre hV.1 Y.2 _ _ ?_ ?_
  · exact holdsOnEveryEtaleChart_of_isPullback B S hS hsq.flip
      (presheaf_etale_of_isOpenImmersion B S hS hV.2)
      (isLocallyOfFinitePresentation_ι_vanishingSubfunctor B S hS X f)
  · exact isLocallyOfFinitePresentation_comp B S hS hV.1 X.2 Y.2 _ g
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hV.2) hg

/-! ### Stacks 06LW in the shape the source states it -/

/-- The fibre hypothesis of Stacks 06LW: the global regular functions `f₁, …, f_r` on `X` map to
a regular sequence in the étale local ring `𝒪_{F, z̄}` of Stacks 04KG at a geometric point `z` of
the fibre `F = X ×_Y Spec(k)`, the image of `f_i` being its germ along any small étale
neighbourhood of `p(z)`, pushed into `𝒪_{F, z̄}` by the canonical homomorphism of étale local
rings of Stacks 04NG. -/
abbrev FibreIsRegularSequenceAt (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (p : F ⟶ X.1)
    (z : GeometricPoint B S hS F) : Prop :=
  ∀ N : SmallEtaleNeighborhood (geometricPointMap p z),
    RingTheory.Sequence.IsRegular (etaleLocalRing B S hS F z)
      (List.ofFn fun i : Fin r =>
        etaleLocalRingMap hF p z
          (etaleLocalRingGerm B S hS X.1 (geometricPointMap p z) (op N)
            ((f i).eval (op N.chart))))

/-- Let `X ⟶ Y` be flat and locally of finite presentation, let a cartesian square exhibit `F`
as the fibre `X ×_Y Spec(k)` over a field-valued point of `Y`, and let `z` be a geometric point of
`F` at which the `f_i` map to a regular sequence in `𝒪_{F, z̄}`.  Then there is an open subspace
`V ⊆ X` containing `p(z)` over which `V(f₁, …, f_r) ⟶ Y` is flat and locally of finite
presentation. -/
@[stacks 06LW]
theorem exists_openSubspace_isFlat_isLocallyOfFinitePresentation_vanishingSubfunctor
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) (pt : FieldValuedPoint B S hS Y.1)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (p : F ⟶ X.1)
    (q : F ⟶ yoneda.obj (FieldValuedPoint.siteObject B S hS Y.1 pt))
    (hcart : IsPullback p q g (yonedaEquiv.symm pt.value)) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (hflat : IsFlat B S hS g) (hg : IsLocallyOfFinitePresentation B S hS g)
    (z : GeometricPoint B S hS F)
    (hreg : FibreIsRegularSequenceAt B S hS X f hF p z) :
    ∃ (V : Subfunctor X.1) (_ : IsOpenSubspace B S hS V),
      pointsMap B S hS F p z.image ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
        IsFlat B S hS (((vanishingSubfunctor B S hS X f).preimage V.ι).ι ≫ V.ι ≫ g) ∧
          IsLocallyOfFinitePresentation B S hS
            (((vanishingSubfunctor B S hS X f).preimage V.ι).ι ≫ V.ι ≫ g) := by
  classical
  obtain ⟨Vobj, cY, hcYSurj, hcYEt⟩ := Y.2.exists_atlas
  obtain ⟨z', c, ρ, d, hc, hρ, hd⟩ :=
    exists_geometricPoint_factorThroughChart_dominates B S hS Vobj cY hcYSurj
      pt.contained pt.toBase (yonedaEquiv.symm pt.value) q z.val
  have hreg' := isRegular_ofFn_etaleLocalRingMap_eval_of_dominates B S hS X f hF p d hd hreg
  obtain ⟨w, hw⟩ := exists_geometricPoint_pullback_fst_eq B S hS q z' c hc
  have hF' : IsAlgebraicSpace B S hS (pullback q (yoneda.map c)) :=
    isAlgebraicSpace_pullback B S hS q (yoneda.map c) hF
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
  have hregw := isRegular_ofFn_etaleLocalRingMap_eval_pullback_fst B S hS X f hF p
    pt.contained pt.toBase q c hF' w (by rw [hw]; exact hreg')
  have sq1 : IsPullback (pullback.fst q (yoneda.map c)) (pullback.snd q (yoneda.map c)) q
      (yoneda.map c) := IsPullback.of_hasPullback _ _
  have sq : IsPullback (pullback.fst q (yoneda.map c) ≫ p) (pullback.snd q (yoneda.map c)) g
      (yoneda.map ρ ≫ cY) := by
    rw [hρ]
    exact (sq1.flip.paste_vert hcart.flip).flip
  obtain ⟨Uobj, gUV, aX, N, cU, v, φ, haXSurj, haXEt, hUVcomm, hv, hNcomm, e, hm⟩ :=
    exists_smallEtaleNeighborhood_fiberBaseChange_compatible B S hS X.2 Y.2 hF' g Vobj cY hcYSurj
      hcYEt z'.val.contained z'.val.toBase ρ sq w
  set U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk aX, haXEt⟩
  have hNcomm' : N.chart.obj.hom ≫
      (ObjectProperty.homMk (pullback.fst q (yoneda.map c) ≫ p) :
        (⟨pullback q (yoneda.map c), hF'⟩ : AlgebraicSpaces B S hS) ⟶ X).hom =
      yoneda.map cU ≫ U.obj.hom := hNcomm
  have hiff := isRegular_ofFn_etaleLocalRingMap_etaleLocalRingGerm_iff_fiber B S hS
    (ObjectProperty.homMk (pullback.fst q (yoneda.map c) ≫ p) :
      (⟨pullback q (yoneda.map c), hF'⟩ : AlgebraicSpaces B S hS) ⟶ X) w N U cU hNcomm'
    ((BigFppfOver.toScheme B S hS).map gUV) v φ e.hom hm
    (fun i => (f i).eval (op U))
  have hregchart := hiff.mp (hregw (targetNeighborhood B S hS N U cU hNcomm'))
  have happ := congrArg (fun m : chartScheme N.chart ⟶
      (BigFppfOver.toScheme B S hS).obj Uobj =>
    m (chartPoint B S hS (pullback q (yoneda.map c)) N)) hm
  simp only [Scheme.Hom.comp_apply] at happ
  have hgvgen : ∀ t : (((BigFppfOver.toScheme B S hS).map gUV).fiber v),
      (BigFppfOver.toScheme B S hS).map gUV
        (((BigFppfOver.toScheme B S hS).map gUV).fiberι v t) = v := by
    intro t
    have hmem : ((BigFppfOver.toScheme B S hS).map gUV).fiberι v t ∈
        Set.range (((BigFppfOver.toScheme B S hS).map gUV).fiberι v) := Set.mem_range_self _
    rwa [Scheme.Hom.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff] at hmem
  have hgv : (BigFppfOver.toScheme B S hS).map gUV
      ((BigFppfOver.toScheme B S hS).map cU (chartPoint B S hS (pullback q (yoneda.map c)) N))
      = v := by rw [happ]; exact hgvgen _
  subst hgv
  have hgsflat : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map gUV) :=
    hflat Uobj Vobj aX cY gUV haXEt hcYEt hUVcomm
  have hgslfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map gUV) :=
    hg Uobj Vobj aX cY gUV haXEt hcYEt hUVcomm
  obtain ⟨O, hxO, hfl⟩ := exists_affineOpen_isFlat_preimage_vanishingSubfunctor B S hS X Y g f
    Vobj cY hcYEt U gUV hUVcomm
    ((BigFppfOver.toScheme B S hS).map cU (chartPoint B S hS (pullback q (yoneda.map c)) N))
    _ happ.symm ((_root_.AlgebraicGeometry.Flat.iff_flat_stalkMap _).1 hgsflat _) hregchart
  have hzz' : z'.image = z.image :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
      ⟨z'.val, FieldValuedPoint.dominates_refl B S hS F z'.val, ⟨d, hd⟩⟩
  have hw' : pointsMap B S hS (pullback q (yoneda.map c)) (pullback.fst q (yoneda.map c))
      w.image = z.image := by
    rw [← geometricPointMap_image, hw]; exact hzz'
  have hchain : pointsMap B S hS (yoneda.obj N.chart.obj.left)
      (N.chart.obj.hom ≫ pullback.fst q (yoneda.map c) ≫ p)
      ((chartFieldValuedPoint N).class B S hS (yoneda.obj N.chart.obj.left))
      = pointsMap B S hS F p z.image := by
    rw [pointsMap_comp, Function.comp_apply, chartFieldValuedPoint_pointsMap,
      pointsMap_comp, Function.comp_apply, hw']
  have hcls : (chartFieldValuedPoint N).class B S hS (yoneda.obj N.chart.obj.left)
      = (canonicalSiteFieldPoint B S hS N.chart.obj.left
          (chartPoint B S hS (pullback q (yoneda.map c)) N)).class B S hS
            (yoneda.obj N.chart.obj.left) :=
    (canonicalSiteFieldPoint_class_eq B S hS N.chart.obj.left (chartFieldValuedPoint N) _
      rfl).symm
  have hchain3 : chartSchemeToPoints B S hS X.1 U
      ((BigFppfOver.toScheme B S hS).map cU
        (chartPoint B S hS (pullback q (yoneda.map c)) N))
      = pointsMap B S hS F p z.image := by
    rw [← hchain, hNcomm, hcls, pointsMap_comp, Function.comp_apply,
      pointsMap_yoneda_map_class_canonicalSiteFieldPoint]
    rfl
  have hopen := (isOpenSubspace_etale_surjective_lift_openSubspaceOfPoints_range_yoneda B S hS
    X.2 _ _ (openChart B S hS X.1 U O.1).property).1
  refine ⟨_, hopen, ?_, hfl, ?_⟩
  · rw [range_pointsMap_ι_openSubspaceOfPoints]
    refine ⟨(canonicalSiteFieldPoint B S hS _ (⟨_, hxO⟩ : ↥O.1)).class B S hS _, ?_⟩
    refine Eq.trans ?_ hchain3
    refine Eq.trans (chartSchemeToPoints_map B S hS X.1
      (openChartInclusion B S hS X.1 U O.1) (⟨_, hxO⟩ : ↥O.1)).symm ?_
    congr 1
    rw [toScheme_map_toOver_map_openChartInclusion]
    rfl
  · exact isLocallyOfFinitePresentation_ι_preimage_vanishingSubfunctor_comp B S hS X Y g f _
      hopen hg

end AlgebraicGeometry.Space

end
