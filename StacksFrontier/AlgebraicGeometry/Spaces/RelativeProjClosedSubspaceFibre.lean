module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.FiniteTypePresentationOffSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# A closed subspace of the constructed relative Proj, read on the fibres of Stacks 084B

Let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Situation 0849 constructed in
Stacks 084A–084B (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`), and let
`i : Z ⟶ P` be a closed immersion.  Over a scheme point `f : T ⟶ X` the second assertion of
Stacks 084B identifies `T ×_X P` with the scheme `Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`); the base change of `i` to it
is a closed subscheme `Z_T` of `Proj_T(f^*𝒜)`.  This file constructs that closed subscheme,
transfers to it the hypotheses of Stacks 085N, and applies the case of schemes, Stacks 0803, over
an affine étale chart of `X`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.fibreClosedSubspace`: the object `Z ×_P (T ×_X P)`
  of the site.
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreClosedImmersion`: its closed immersion into
  `Proj_T(f^*𝒜)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.quasiCompact_fibre_toBase`: if `π` is
  quasi-compact, so is `Proj_T(f^*𝒜) ⟶ T` for `T` affine.
* `AlgebraicGeometry.Space.RelativeProjSituation.finitePresentation_fibreClosedImmersion`: if `i`
  is of finite presentation, so is `Z_T ⟶ Proj_T(f^*𝒜)` for an étale point `f`.
* `AlgebraicGeometry.Space.RelativeProjSituation.isFiniteType_pointAlgebra_piece`: if every
  `𝒜_n` is of finite type, so is every piece of `f^*𝒜`.
* `AlgebraicGeometry.Space.RelativeProjSituation.inter_range_fibreClosedImmersion_eq_empty` and
  `AlgebraicGeometry.Space.RelativeProjSituation.exists_isCompact_opens_image_cover`: hypotheses
  (3) and (4) of Stacks 085N read on a surjective étale chart.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_fibre_finiteType_presentation_supp`:
  **the case of schemes, Stacks 0803, on the fibre of the constructed relative Proj over an affine
  étale chart of `X`**, and
  `AlgebraicGeometry.Space.RelativeProjSituation.exists_chart_finiteType_presentation_supp`, the
  same with the hypotheses of Stacks 085N on `X`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

namespace AlgebraicGeometry.Space

/-- **The Zariski reading of a quasi-coherent module of finite type on a represented space is of
finite type**: it is the chart restriction of the module along the identity chart. -/
theorem isFiniteType_zariskiReading_piece {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
    (hqc : N.IsQuasicoherentOnSite) (hft : N.IsFiniteTypeOnSite) :
    SheafOfModules.IsFiniteType.{u, u, u}
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj
        N : (chartScheme (idEtaleChart B S hS T)).Modules) := by
  have h5 := isFiniteType_restrictToChart B S hS (X := yonedaSpace B S hS T) N hqc hft
    (idEtaleChart B S hS T)
  let e := restrictToChartIsoRestrictToChartScheme B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) N (idEtaleChart B S hS T) ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS T N ≪≫ selfOpensPushforwardIso B S hS T N
  exact Stacks.SheafOfModules.isFiniteType_of_epi e.hom h5

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})
    {Z : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {i : Z ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **The base change of a closed subspace of `P` to the fibre `T ×_X P = Proj_T(f^*𝒜)`**, as an
object of the site: the closed immersion `i` is representable, and this is the object
representing `Z ×_P (T ×_X P)`. -/
def fibreClosedSubspace : BigFppfOver s.site s.base s.containsBase :=
  hi.rep.pullback (s.relativeProjPoints.fibreToSpace T f)

/-- The projection of `Z ×_P (T ×_X P)` to the fibre `T ×_X P`, as a morphism of the site. -/
def fibreClosedSubspaceHom : s.fibreClosedSubspace hi T f ⟶ s.relativeProjPoints.fibre T f :=
  hi.rep.snd (s.relativeProjPoints.fibreToSpace T f)

/-- The projection of `Z ×_P (T ×_X P)` to `Z`. -/
def fibreClosedSubspaceToSpace : yoneda.obj (s.fibreClosedSubspace hi T f) ⟶ Z :=
  hi.rep.fst (s.relativeProjPoints.fibreToSpace T f)

/-- The square exhibiting `Z ×_P (T ×_X P)` as a fibre product. -/
theorem isPullback_fibreClosedSubspace :
    IsPullback (s.fibreClosedSubspaceToSpace hi T f)
      (yoneda.map (s.fibreClosedSubspaceHom hi T f)) i
      (s.relativeProjPoints.fibreToSpace T f) :=
  hi.rep.isPullback _

/-- **The closed subscheme `Z_T ⊆ Proj_T(f^*𝒜)`**: the base change of `i` to the fibre, read
through the identification of the fibre with the relative Proj of the restricted algebra. -/
def fibreClosedImmersion :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.fibreClosedSubspace hi T f) ⟶
      (relativeProj (s.shrink.pointAlgebra T f)).scheme :=
  (BigFppfOver.toScheme s.site s.base s.containsBase).map (s.fibreClosedSubspaceHom hi T f) ≫
    (s.relativeProjPoints.fibreIso T f).hom

/-- `Z_T ⟶ Proj_T(f^*𝒜)` is a closed immersion. -/
instance isClosedImmersion_fibreClosedImmersion :
    _root_.AlgebraicGeometry.IsClosedImmersion (s.fibreClosedImmersion hi T f) := by
  have h : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.fibreClosedSubspaceHom hi T f)) :=
    hi.property_snd _
  have hiso : IsIso (s.relativeProjPoints.fibreIso T f).hom := Iso.isIso_hom _
  have h' : _root_.AlgebraicGeometry.IsClosedImmersion (s.relativeProjPoints.fibreIso T f).hom :=
    inferInstance
  exact @_root_.AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _ h h'

/-- **Quasi-compactness of `π` passes to the fibres over affine test objects.**  The fibre
`T ×_X P` is the base change of `π` along `f`, so it is quasi-compact when `T` is, and over the
affine `T` this is quasi-compactness of `Proj_T(f^*𝒜) ⟶ T`. -/
theorem quasiCompact_fibre_toBase
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) :
    _root_.AlgebraicGeometry.QuasiCompact (relativeProj (s.shrink.pointAlgebra T f)).toBase := by
  have hTq := isQuasiCompactSpace_yoneda_of_isAffine s.site s.base s.containsBase T hT
  have hpb := hπ (yoneda.obj T)
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda s.site s.base s.containsBase T) hTq f
  have hfib : IsQuasiCompactSpace s.site s.base s.containsBase
      (yoneda.obj (s.relativeProjPoints.fibre T f)) :=
    IsQuasiCompactSpace.of_iso s.site s.base s.containsBase hpb
      ((s.relativeProjPoints.isPullback T f).flip.isoPullback).symm
  have hc : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre T f)) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj s.site s.base s.containsBase hfib
  have : CompactSpace (relativeProj (s.shrink.pointAlgebra T f)).scheme :=
    (s.relativeProjPoints.fibreIso T f).hom.homeomorph.compactSpace
  exact _root_.AlgebraicGeometry.quasiCompact_of_compactSpace _

variable {T f} in
/-- Over an étale scheme point of `X`, the morphism from the fibre `T ×_X P` to `P` is étale: it is
the base change of the point along `π`. -/
theorem presheaf_etale_fibreToSpace
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
      (s.relativeProjPoints.fibreToSpace T f) := by
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (s.relativeProjPoints.isPullback T f).flip hf

variable {T f} in
/-- Over an étale scheme point of `X`, the morphism from `Z ×_P (T ×_X P)` to `Z` is étale. -/
theorem presheaf_etale_fibreClosedSubspaceToSpace
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
      (s.fibreClosedSubspaceToSpace hi T f) := by
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (s.isPullback_fibreClosedSubspace hi T f).flip (s.presheaf_etale_fibreToSpace hf)

variable {T f} in
/-- **Finite presentation of `i` passes to the closed subscheme `Z_T ⊆ Proj_T(f^*𝒜)` over an
étale scheme point.**  Local finite presentation is read on the commuting square of étale charts
formed by the fibre `T ×_X P ⟶ P` and its base change `Z ×_P (T ×_X P) ⟶ Z`; quasi-compactness
and quasi-separatedness hold for every closed immersion of schemes. -/
theorem finitePresentation_fibreClosedImmersion
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i) :
    _root_.AlgebraicGeometry.FinitePresentation (s.fibreClosedImmersion hi T f) := by
  have hl : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.fibreClosedSubspaceHom hi T f)) :=
    hfp.1 _ _ (s.fibreClosedSubspaceToSpace hi T f) (s.relativeProjPoints.fibreToSpace T f)
      (s.fibreClosedSubspaceHom hi T f) (s.presheaf_etale_fibreClosedSubspaceToSpace hi hf)
      (s.presheaf_etale_fibreToSpace hf) (s.isPullback_fibreClosedSubspace hi T f).w.symm
  have hiso : IsIso (s.relativeProjPoints.fibreIso T f).hom := Iso.isIso_hom _
  have h' : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      (s.relativeProjPoints.fibreIso T f).hom := inferInstance
  exact _root_.AlgebraicGeometry.FinitePresentation.mk
    (MorphismProperty.comp_mem _ _ _ hl h') inferInstance inferInstance

/-- **Hypothesis (5) of Stacks 085N passes to the restriction `f^*𝒜` at a scheme point**, for an
arbitrary situation `t`: the pullback to the represented space `T` preserves finite type, and the
Zariski reading of a quasi-coherent module of finite type on a represented space is of finite
type. -/
theorem isFiniteType_pointAlgebra_piece_of (t : RelativeProjSituation.{u, u})
    (T : BigFppfOver t.site t.base t.containsBase) (f : yoneda.obj T ⟶ t.space.1)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteTypeOnSite (t.algebra.piece n)) (n : ℤ) :
    SheafOfModules.IsFiniteType.{u, u, u} ((t.pointAlgebra T f).piece n) :=
  isFiniteType_zariskiReading_piece T _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite t.site t.base t.containsBase
      (pointHom f) _ (t.isQuasicoherent n))
    (isFiniteTypeOnSite_modulePullback t.site t.base t.containsBase (pointHom f) _ (hA n))

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Hypothesis (5) of Stacks 085N passes to the restriction `f^*𝒜` at a scheme point.**  If
every homogeneous piece of `𝒜` is of finite type, so is every homogeneous piece of the graded
algebra `f^*𝒜` on the scheme of `T`. -/
theorem isFiniteType_pointAlgebra_piece
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n)) (n : ℤ) :
    SheafOfModules.IsFiniteType.{u, u, u} ((s.shrink.pointAlgebra T f).piece n) := by
  refine isFiniteType_pointAlgebra_piece_of s.shrink T f (fun m => ?_) n
  refine Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ ?_
  obtain ⟨σ, hσ⟩ := (hA m).exists_localGeneratorsData
  exact ⟨Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso (s.smallAlgebraPieceIso m).inv σ,
    inferInstance⟩

variable {T f} in
/-- **The case of schemes, Stacks 0803, on the fibre of the constructed relative Proj over an
affine étale chart.**  Let `f : T ⟶ X` be an étale scheme point of `X` with `T` affine, let
`i : Z ⟶ P` be a closed immersion of finite presentation, `π` quasi-compact and every `𝒜_n` of
finite type, and let `U_T` be a quasi-compact open of `T` missing the image of the closed
subscheme `Z_T ⊆ Proj_T(f^*𝒜)`.  Then there are `d > 0` and a quasi-coherent finite type
submodule `ℱ' ⊆ (f^*𝒜)_d` with `Z_T = Proj_T(f^*𝒜/ℱ'(f^*𝒜))` and the support of `(f^*𝒜)_d/ℱ'`
disjoint from `U_T`. -/
theorem exists_fibre_finiteType_presentation_supp
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n))
    (UT : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (hU : (UT : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
      Set.range (s.fibreClosedImmersion hi T f ≫
        (relativeProj (s.shrink.pointAlgebra T f)).toBase).base = ∅)
    (hUc : IsCompact (UT : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : ((s.shrink.pointAlgebra T f).piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (UT : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
              (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
                RingedSpace.ModuleSheaf.{u}
                  ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).toRingedSpace).supp =
            ∅ ∧
            Nonempty (DegreeQuotientPresentation (s.shrink.pointAlgebra T f)
              (s.fibreClosedImmersion hi T f) ℱ) := by
  have _ := s.quasiCompact_fibre_toBase T f hπ hT
  exact Stacks.AlgebraicGeometry.RelativeProjTwists.exists_finiteType_presentation_supp
    (s.shrink.pointAlgebra T f) (s.fibreClosedImmersion hi T f) UT
    (s.finitePresentation_fibreClosedImmersion hi hf hfp) hU hUc
    (fun n => s.isFiniteType_pointAlgebra_piece T f hA n)

/-- The structure morphism `Z_T ⟶ T` of the closed subscheme of the fibre is the scheme morphism of
the composite `Z ×_P (T ×_X P) ⟶ T ×_X P ⟶ T` of the site. -/
theorem fibreClosedImmersion_comp_toBase :
    s.fibreClosedImmersion hi T f ≫ (relativeProj (s.shrink.pointAlgebra T f)).toBase =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.fibreClosedSubspaceHom hi T f ≫ s.relativeProjPoints.fibreHom T f) := by
  rw [Functor.map_comp, s.relativeProjPoints.fibreHom_comp T f, fibreClosedImmersion]
  exact Category.assoc _ _ _

attribute [local instance] pointTopology in
/-- **Hypothesis (3) of Stacks 085N passes to the fibre.**  A set of points of `T` lying over a
set `U` of points of `X` which misses the image of `Z` misses the image of the closed subscheme
`Z_T ⊆ Proj_T(f^*𝒜)` in `T`. -/
theorem inter_range_fibreClosedImmersion_eq_empty
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z i z)))
    {V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)}
    (hV : ∀ t ∈ V, pointsMap s.site s.base s.containsBase (yoneda.obj T) f
      ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t) ∈ U) :
    V ∩ Set.range (s.fibreClosedImmersion hi T f ≫
      (relativeProj (s.shrink.pointAlgebra T f)).toBase).base = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro t ⟨htV, z, rfl⟩
  set g := s.fibreClosedSubspaceHom hi T f ≫ s.relativeProjPoints.fibreHom T f
  set p := (schemePointsHomeomorph s.site s.base s.containsBase
    (s.fibreClosedSubspace hi T f)).symm z
  have hz : pointsToScheme s.site s.base s.containsBase _ p = z :=
    (schemePointsHomeomorph s.site s.base s.containsBase _).apply_symm_apply z
  have ht : (schemePointsHomeomorph s.site s.base s.containsBase T).symm
      ((s.fibreClosedImmersion hi T f ≫ (relativeProj (s.shrink.pointAlgebra T f)).toBase).base
        z) = pointsMap s.site s.base s.containsBase _ (yoneda.map g) p := by
    apply (schemePointsHomeomorph s.site s.base s.containsBase T).injective
    rw [Homeomorph.apply_symm_apply]
    show _ = pointsToScheme s.site s.base s.containsBase T _
    rw [pointsToScheme_pointsMap, hz, s.fibreClosedImmersion_comp_toBase]
  have hsq : yoneda.map g ≫ f = s.fibreClosedSubspaceToSpace hi T f ≫ i ≫ s.relativeProjπ := by
    rw [Functor.map_comp, Category.assoc, ← (s.relativeProjPoints.isPullback T f).w,
      ← Category.assoc, ← (s.isPullback_fibreClosedSubspace hi T f).w, Category.assoc]
  have hmem := hV _ htV
  rw [ht, ← pointsMap_comp_apply, hsq, pointsMap_comp_apply, pointsMap_comp_apply] at hmem
  exact Set.disjoint_left.1 hZU hmem ⟨_, rfl⟩

attribute [local instance] pointTopology in
/-- **Hypothesis (4) of Stacks 085N, read on a surjective étale chart.**  Let `f : T ⟶ X` be an
étale scheme point surjective on points and `U` a quasi-compact open set of points of `X`.  Then
there is a quasi-compact open `V` of the scheme of `T` lying over `U` whose image covers `U`. -/
theorem exists_isCompact_opens_image_cover
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hsurj : Function.Surjective (pointsMap s.site s.base s.containsBase (yoneda.obj T) f))
    {U : Set (points s.site s.base s.containsBase s.space.1)} (hU : IsOpen U)
    (hUc : IsCompact U) :
    ∃ V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∧
        (∀ t ∈ V, pointsMap s.site s.base s.containsBase (yoneda.obj T) f
          ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t) ∈ U) ∧
          U ⊆ (fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
            ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t)) '' V := by
  set φ := fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
    ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t) with hφ
  have hφc : Continuous φ := (continuous_pointsMap s.site s.base s.containsBase f).comp
    (schemePointsHomeomorph s.site s.base s.containsBase T).symm.continuous
  have hφo : IsOpenMap φ := (isOpenMap_pointsMap_of_presheafEtale s.site s.base s.containsBase f
    hf).comp (schemePointsHomeomorph s.site s.base s.containsBase T).symm.isOpenMap
  let W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens :=
    ⟨φ ⁻¹' U, hU.preimage hφc⟩
  let ι := {O : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).affineOpens //
    O.1 ≤ W}
  have hcover : U ⊆ ⋃ O : ι, φ '' (SetLike.coe O.1.1) := by
    intro x hx
    obtain ⟨p, rfl⟩ := hsurj x
    set t := schemePointsHomeomorph s.site s.base s.containsBase T p
    have hφt : φ t = pointsMap s.site s.base s.containsBase (yoneda.obj T) f p := by
      rw [hφ]
      exact congrArg _ ((schemePointsHomeomorph s.site s.base s.containsBase T).symm_apply_apply p)
    have htW : t ∈ W := by
      show φ t ∈ U
      rwa [hφt]
    obtain ⟨_, ⟨O, hO, rfl⟩, htO, hOW⟩ :=
      (((BigFppfOver.toScheme s.site s.base s.containsBase).obj
        T).isBasis_affineOpens).exists_subset_of_mem_open htW W.2
    exact Set.mem_iUnion.2 ⟨⟨⟨O, hO⟩, hOW⟩, t, htO, hφt⟩
  obtain ⟨F, hF⟩ := hUc.elim_finite_subcover (fun O : ι ↦ φ '' (SetLike.coe O.1.1))
    (fun O ↦ hφo _ O.1.1.2) hcover
  have hcoe : ((F.sup fun O : ι ↦ O.1.1 :
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) : Set _) =
      ⋃ O ∈ F, (SetLike.coe O.1.1) := by
    rw [TopologicalSpace.Opens.coe_finset_sup, Finset.sup_eq_iSup]
    rfl
  refine ⟨F.sup fun O : ι ↦ O.1.1, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact F.isCompact_biUnion fun O _ ↦ O.1.2.isCompact
  · intro t ht
    have ht' : t ∈ ⋃ O ∈ F, (SetLike.coe O.1.1) := by rwa [← hcoe]
    obtain ⟨O, -, htO⟩ := Set.mem_iUnion₂.1 ht'
    exact O.2 htO
  · intro x hx
    obtain ⟨O, hOF, y, hy, rfl⟩ := Set.mem_iUnion₂.1 (hF hx)
    refine ⟨y, ?_, rfl⟩
    have : y ∈ ⋃ O ∈ F, (SetLike.coe O.1.1) := Set.mem_iUnion₂.2 ⟨O, hOF, hy⟩
    rwa [← hcoe] at this

attribute [local instance] pointTopology in
variable {T f} in
/-- **The chart case of Stacks 085N, from the hypotheses of Stacks 085N.**  Let `f : T ⟶ X` be an
étale scheme point surjective on points with `T` affine, and assume hypotheses (1)–(5) of
Stacks 085N for the closed immersion `i : Z ⟶ P` and the open `U` of `X`.  Then there are a
quasi-compact open `V` of `T` lying over `U` and covering it, a degree `d > 0` and a
quasi-coherent finite type submodule `ℱ' ⊆ (f^*𝒜)_d` with `Z_T = Proj_T(f^*𝒜/ℱ'(f^*𝒜))` and the
support of `(f^*𝒜)_d/ℱ'` disjoint from `V`. -/
theorem exists_chart_finiteType_presentation_supp
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hsurj : Function.Surjective (pointsMap s.site s.base s.containsBase (yoneda.obj T) f))
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z i z)))
    (hU : IsOpen U) (hUc : IsCompact U)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n)) :
    ∃ V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens,
      (∀ t ∈ V, pointsMap s.site s.base s.containsBase (yoneda.obj T) f
          ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t) ∈ U) ∧
        U ⊆ (fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
          ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t)) '' V ∧
        ∃ d : ℕ, 0 < d ∧ ∃ ℱ : ((s.shrink.pointAlgebra T f).piece (d : ℤ)).Submodule,
          ℱ.toSheafOfModules.IsQuasicoherent ∧
            SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
              (V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
                  (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
                    RingedSpace.ModuleSheaf.{u}
                      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
                        T).toRingedSpace).supp = ∅ ∧
                Nonempty (DegreeQuotientPresentation (s.shrink.pointAlgebra T f)
                  (s.fibreClosedImmersion hi T f) ℱ) := by
  obtain ⟨V, hVc, hVU, hUV⟩ := s.exists_isCompact_opens_image_cover T f hf hsurj hU hUc
  exact ⟨V, hVU, hUV, s.exists_fibre_finiteType_presentation_supp hi hT hf hπ hfp hA V
    (s.inter_range_fibreClosedImmersion_eq_empty hi T f hZU hVU) hVc⟩

end AlgebraicGeometry.Space.RelativeProjSituation

end
