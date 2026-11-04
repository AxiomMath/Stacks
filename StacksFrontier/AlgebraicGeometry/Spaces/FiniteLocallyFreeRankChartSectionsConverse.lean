module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The chartwise reading of the rank is the rank

Let `F` be an algebraic space and let `G` be an `𝒪_F`-module on its small étale site which is
cartesian on affine charts.  If the affine étale charts over which the sections of `G` form a
finite locally free module of rank `r` generate a covering sieve of every chart, then `G` is
finite locally free of rank `r` in the sense of the rank clause of Stacks 0409.  Together with
`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank` this is the
rank form of Descent, Proposition 03DX (2).

Two steps.  Over an affine chart whose sections are *free* of rank `r` a basis gives a morphism
from a coproduct of `r` copies of the structure sheaf, bijective on the sections over every
affine chart below because the base change comparison is, hence an isomorphism.  And an affine
chart whose sections are only finite locally free of rank `r` is covered by the basic opens on
which they become free, the sections over such a basic open being the corresponding localization.

## Main results

* `AlgebraicGeometry.Space.exists_isColimitCofan_of_basis`: over an affine chart whose sections
  are free of rank `r`, the module is a coproduct of `r` copies of the structure sheaf.
* `AlgebraicGeometry.Space.basisPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`: an affine
  chart whose sections are finite locally free of rank `r` is covered by affine charts whose
  sections are free of rank `r`.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`: **the chartwise
  reading of the rank implies the rank clause of Stacks 0409.**
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_freeRankPresieve`: **the rank form of
  Descent, Proposition 03DX (2).**

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Transport of a basis along a localization -/

/-- A basis of the localization of `M` away from `r` is a basis of any module realizing that
localization, over any ring realizing the localization of the coefficients. -/
private noncomputable def basisOfLocalizationAway {R : Type u} [CommRing R] {A : Type u}
    [CommRing A] [Algebra R A] {M : Type u} [AddCommGroup M] [Module R M]
    {N : Type u} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (r : R) [IsLocalization.Away r A] (f : M →ₗ[R] N) [IsLocalizedModule.Away r f]
    {I : Type*} (b : Module.Basis I (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M)) :
    Module.Basis I A N :=
  let e := IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) A
  letI : Module (Localization.Away r) N := Module.compHom N e.toRingHom
  haveI : IsScalarTower R (Localization.Away r) N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      change e (algebraMap R (Localization.Away r) a) • n = a • n
      rw [e.commutes, IsScalarTower.algebraMap_smul]
  let eM := (IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M) f).extendScalarsOfIsLocalization
      (Submonoid.powers r) (Localization.Away r)
  (b.map eM).mapCoeffs e.toRingEquiv fun _ _ => rfl

/-! ### A basis gives a coproduct decomposition -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The global section of the restriction of `G` to the slice at a chart `U` determined by a
section of `G` over `U`: its component over a chart above `U` is the restriction along the
structure morphism. -/
private noncomputable def chartSection (G : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) (x : G.val.obj (op U)) :
    (SmallEtale.sliceModule B S hS F hF U G).sections :=
  PresheafOfModules.sectionsMk (fun V => G.val.map V.unop.hom.op x)
    fun V W g => (PresheafOfModules.map_comp_apply (M := G.val) (unop V).hom.op
        (Over.Hom.left g.unop).op x).symm.trans
      (congrArg (fun k : (unop W).left ⟶ U => G.val.map k.op x) (Over.w g.unop))

/-- The morphism from a coproduct of copies of the structure sheaf on the slice at `U`
determined by a family of sections of `G` over `U`. -/
private noncomputable def freeChartComparison (G : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) {I : Type u} (t : I → G.val.obj (op U)) :
    SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF U) I ⟶
      SmallEtale.sliceModule B S hS F hF U G :=
  (SheafOfModules.freeHomEquiv _).symm fun i => chartSection B S hS F hF G U (t i)

private theorem freeChartComparison_app_single (G : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) {I : Type u} (t : I → G.val.obj (op U)) (V : Over U) (i : I)
    (a : chartRing B S hS F hF V.left) :
    ((freeChartComparison B S hS F hF G U t).val.app (op V)).hom
        ((Stacks.Sites.freeSectionsMap
          (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom
            (Finsupp.single i a)) =
      a • chartRestrictLinear G V.hom (t i) :=
  Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
    (SmallEtale.sliceModule B S hS F hF U G)
    (fun i => chartSection B S hS F hF G U (t i)) (op V) i a

/-- **The restrictions of a basis of the sections over an affine chart are a basis of the
sections over every affine chart below it.**  The base change comparison is bijective, and it
carries the base change of a basis to the restricted basis. -/
private noncomputable def basisChartRestrict (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (f : V ⟶ U) {I : Type*}
    (b : Module.Basis I (chartRing B S hS F hF U) (G.val.obj (op U))) :
    Module.Basis I (chartRing B S hS F hF V) (G.val.obj (op V)) :=
  letI := chartAlgebra (hF := hF) f
  letI := chartSectionsModule G f
  haveI := chartSections_isScalarTower G f
  (Algebra.TensorProduct.basis (chartRing B S hS F hF V) b).map
    (LinearEquiv.ofBijective (sectionsBaseChange G f) (hG U V hU hV f))

private theorem basisChartRestrict_apply (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (f : V ⟶ U) {I : Type*}
    (b : Module.Basis I (chartRing B S hS F hF U) (G.val.obj (op U))) (i : I) :
    basisChartRestrict B S hS F hF G hG hU hV f b i = chartRestrictLinear G f (b i) := by
  let := chartAlgebra (hF := hF) f
  let := chartSectionsModule G f
  have := chartSections_isScalarTower G f
  show sectionsBaseChange G f
    (Algebra.TensorProduct.basis (chartRing B S hS F hF V) b i) = _
  rw [Algebra.TensorProduct.basis_apply]
  exact chartBaseChange_one_tmul G f (b i)

/-- **The comparison morphism attached to a basis is bijective on the sections over an affine
chart below.**  Both sides are the finitely supported families of regular functions there: the
coproduct by `Stacks.Sites.bijective_freeSectionsMap`, since an affine chart is a quasi-compact
object, and the module by the restricted basis. -/
private theorem bijective_freeChartComparison_app (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) {I : Type u}
    (b : Module.Basis I (chartRing B S hS F hF U) (G.val.obj (op U)))
    (V : Over U) (hV : IsAffine (chartScheme V.left)) :
    Function.Bijective
      ((freeChartComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom := by
  classical
  have hfs : Function.Bijective (Stacks.Sites.freeSectionsMap
      (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom :=
    Stacks.Sites.bijective_freeSectionsMap I V
      (GrothendieckTopology.isQuasiCompactObject_over _ V
        (isQuasiCompactObject_of_isAffine B S hS F V.left hV))
  let b' : Module.Basis I ((SmallEtale.sliceRingSheaf B S hS F hF U).obj.obj (op V))
      ((SmallEtale.sliceModule B S hS F hF U G).val.obj (op V)) :=
    basisChartRestrict B S hS F hF G hG hU hV V.hom b
  have hsingle : ∀ (i : I) (a : (SmallEtale.sliceRingSheaf B S hS F hF U).obj.obj (op V)),
      ((freeChartComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom
          ((Stacks.Sites.freeSectionsMap
            (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom
              (Finsupp.single i a)) = b'.repr.symm (Finsupp.single i a) := by
    intro i a
    have hbi : b' i = chartRestrictLinear G V.hom (b i) :=
      basisChartRestrict_apply B S hS F hF G hG hU hV V.hom b i
    refine (freeChartComparison_app_single B S hS F hF G U (fun i => b i) V i a).trans ?_
    rw [Module.Basis.repr_symm_single, hbi]
    rfl
  have hcomp : ((freeChartComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom ∘ₗ
      (Stacks.Sites.freeSectionsMap
        (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom =
      b'.repr.symm.toLinearMap :=
    Finsupp.lhom_ext hsingle
  refine (Function.Bijective.of_comp_iff _ hfs).1 ?_
  rw [← LinearMap.coe_comp, hcomp]
  exact b'.repr.symm.bijective

include hF in
/-- **Over an affine chart whose sections are free of rank `r`, the module is a coproduct of `r`
copies of the structure sheaf.**  The comparison morphism attached to the basis is bijective on
the sections over the affine charts below, which cover, so it is an isomorphism. -/
theorem exists_isColimitCofan_of_basis (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) {r : ℕ}
    (b : Module.Basis (Fin r) (chartRing B S hS F hF U) (G.val.obj (op U))) :
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (SmallEtale.sliceRingSheaf B S hS F hF U) ⟶
        SmallEtale.sliceModule B S hS F hF U G,
      Nonempty (IsColimit (Cofan.mk (SmallEtale.sliceModule B S hS F hF U G) ι)) := by
  classical
  let b' : Module.Basis (ULift.{u} (Fin r)) (chartRing B S hS F hF U) (G.val.obj (op U)) :=
    b.reindex Equiv.ulift.symm
  have hiso : IsIso (freeChartComparison B S hS F hF G U (fun i => b' i)) :=
    SmallEtale.isIso_of_bijective_app_of_isAffine B S hS F hF U _ fun V hV =>
      bijective_freeChartComparison_app B S hS F hF G hG U hU b' V hV
  let e : SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF U)
      (ULift.{u} (Fin r)) ≅ SmallEtale.sliceModule B S hS F hF U G :=
    asIso (freeChartComparison B S hS F hF G U (fun i => b' i))
  have h1 : IsColimit (Cofan.mk (SmallEtale.sliceModule B S hS F hF U G)
      (fun k : ULift.{u} (Fin r) => Sigma.ι _ k ≫ e.hom)) :=
    IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cocone.ext e (by rintro ⟨k⟩; rfl))
  exact ⟨_, ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _ h1⟩⟩

/-! ### Refining to charts with free sections -/

/-- The affine étale charts over which the sections of `G` form a free module of rank `r`, as a
presieve on an étale chart. -/
def basisPresieve (G : Modules.{u, u} B S hS F hF) (r : ℕ) (U : SmallEtale B S hS F) :
    Presieve U :=
  fun V _ => IsAffine (chartScheme V) ∧
    Nonempty (Module.Basis (Fin r) (chartRing B S hS F hF V) (G.val.obj (op V)))

include hF in
/-- **An affine chart whose sections are finite locally free of rank `r` is covered by the
charts over which they are free of rank `r`.**  The covering is by the basic opens of a family
of functions generating the unit ideal over which the sections become free; the sections over
such a basic-open chart are the corresponding localization, by
`AlgebraicGeometry.Space.isLocalizedModule_chartRestrictLinear_openChart_basicOpen`. -/
theorem basisPresieve_mem_topology_of_isFiniteLocallyFreeOfRank
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G) (r : ℕ)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hflf : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF U)
      (G.val.obj (op U)) r) :
    Sieve.generate (basisPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U := by
  classical
  obtain ⟨ι, g, hspan, hb⟩ := hflf
  have key : ∀ i : ι, Nonempty (Module.Basis (Fin r)
      (chartRing B S hS F hF (openChart B S hS F U ((chartScheme U).basicOpen (g i))))
      (G.val.obj (op (openChart B S hS F U ((chartScheme U).basicOpen (g i)))))) := by
    intro i
    let := chartAlgebra (hF := hF)
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen (g i)))
    let := chartSectionsModule G
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen (g i)))
    have := chartSections_isScalarTower G
      (openChartInclusion B S hS F U ((chartScheme U).basicOpen (g i)))
    have := isLocalization_away_chartRing_openChart_basicOpen B S hS hF U hU (g i)
    have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS hF G hG U hU (g i)
    exact ⟨basisOfLocalizationAway (g i)
      (chartRestrictLinear G
        (openChartInclusion B S hS F U ((chartScheme U).basicOpen (g i)))) (hb i).some⟩
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
  have hz : z ∈ (⨆ i ∈ Set.range g, (chartScheme U).basicOpen i) :=
    (iSup_basicOpen_of_span_eq_top (X := chartScheme U) ⊤ (Set.range g) hspan).ge
      (show z ∈ (⊤ : (chartScheme U).Opens) from trivial)
  simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range] at hz
  obtain ⟨a, ⟨i, rfl⟩, hi⟩ := hz
  refine ⟨openChart B S hS F U ((chartScheme U).basicOpen (g i)),
    openChartInclusion B S hS F U ((chartScheme U).basicOpen (g i)),
    ⟨_, 𝟙 _, _, ⟨isAffine_chartScheme_openChart_basicOpen B S hS F U hU (g i), key i⟩,
      Category.id_comp _⟩, ⟨z, hi⟩, ?_⟩
  rw [toScheme_map_toOver_map_openChartInclusion]
  rfl

include hF in
/-- **The charts over which the sections of `G` are free of rank `r` cover every chart over
which they are chartwise finite locally free of rank `r`.** -/
theorem basisPresieve_mem_topology_of_freeRankPresieve (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (r : ℕ)
    (h : ∀ U : SmallEtale B S hS F,
      Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
        IsAffine (chartScheme V) ∧
          Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
            (G.val.obj (op V)) r) ∈ SmallEtale.topology B S hS F U)
    (U : SmallEtale B S hS F) :
    Sieve.generate (basisPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U := by
  refine GrothendieckTopology.transitive _ (h U) _ ?_
  rintro Z f ⟨W, l, a, ⟨hWaff, hWflf⟩, rfl⟩
  rw [Sieve.pullback_comp]
  refine GrothendieckTopology.pullback_stable _ l
    (GrothendieckTopology.superset_covering _ ((Sieve.generate_le_iff _ _).2 ?_)
      (basisPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS F hF G hG r W hWaff
        hWflf))
  intro V v hV
  exact ⟨V, 𝟙 _, v ≫ a, hV, by simp⟩

/-! ### The rank form of Descent, Proposition 03DX (2) -/

include hF in
/-- **The chartwise reading of the rank implies the rank clause of Stacks 0409.**  If the affine
étale charts over which the sections of `G` form a finite locally free module of rank `r`
generate a covering sieve of every chart, then `G` is, over the members of a covering of every
chart, a coproduct of `r` copies of the structure sheaf. -/
theorem isFiniteLocallyFreeOfRank_of_freeRankPresieve (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (r : ℕ)
    (h : ∀ U : SmallEtale B S hS F,
      Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
        IsAffine (chartScheme V) ∧
          Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
            (G.val.obj (op V)) r) ∈ SmallEtale.topology B S hS F U) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) G r := by
  classical
  intro U
  refine ⟨Σ V : SmallEtale B S hS F, {f : V ⟶ U // basisPresieve B S hS F hF G r U f},
    fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine GrothendieckTopology.superset_covering _ ((Sieve.generate_le_iff _ _).2 ?_)
      (basisPresieve_mem_topology_of_freeRankPresieve B S hS F hF G hG r h U)
    intro V v hV
    exact Sieve.ofArrows_mk
      (fun i : Σ V : SmallEtale B S hS F,
        {f : V ⟶ U // basisPresieve B S hS F hF G r U f} => i.1)
      (fun i => i.2.1) ⟨V, ⟨v, hV⟩⟩
  · exact exists_isColimitCofan_of_basis B S hS F hF G hG i.1 i.2.2.1 i.2.2.2.some

include hF in
/-- **The rank form of Descent, Proposition 03DX (2).**  An `𝒪_F`-module cartesian on affine
charts is finite locally free of rank `r` in the sense of the rank clause of Stacks 0409 exactly
when the affine étale charts over which its sections form a finite locally free module of
rank `r` generate a covering sieve of every chart. -/
theorem isFiniteLocallyFreeOfRank_iff_freeRankPresieve (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) G r ↔
      ∀ U : SmallEtale B S hS F,
        Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
          IsAffine (chartScheme V) ∧
            Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
              (G.val.obj (op V)) r) ∈ SmallEtale.topology B S hS F U :=
  ⟨freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank B S hS F hF G r,
    isFiniteLocallyFreeOfRank_of_freeRankPresieve B S hS F hF G hG r⟩

end AlgebraicGeometry.Space

end
