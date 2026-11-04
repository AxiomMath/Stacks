module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocusChartConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Free plus finitely presented is finite free: the two étale loci of Stacks 0CZT agree

Stacks 0CZT defines its locus by *plain* freeness on an étale neighbourhood, which is
`AlgebraicGeometry.Space.etaleFreeLocus`; clause (4) of Stacks 0CZS says *finite* freeness, which
is `AlgebraicGeometry.Space.etaleFiniteFreeLocus`.  The inclusion
`AlgebraicGeometry.Space.etaleFiniteFreeLocus_subset_etaleFreeLocus` holds in general.  This file
proves the other inclusion for a module which is quasi-coherent and of finite presentation on
charts, and deduces the base-change clause of Stacks 0CZT at the plain-freeness locus.

## Main results

* `Stacks.SheafOfModules.isFree_reindex_iff`, `Stacks.SheafOfModules.isFree_over`,
  `Stacks.SheafOfModules.isFree_free` and
  `Stacks.SheafOfModules.isFiniteFree_of_isColimit_cofan_of_finite`: freeness of Stacks 03DE (1)
  under an equivalence of ringed sites, under restriction to a slice, for the free sheaf itself,
  and the passage to Stacks 03DE (2) once the index type is known to be finite.
* `AlgebraicGeometry.SmallEtale.isFree_of_isFree_associatedModule`: **Stacks 05VG for the clause
  03DE (1) at `τ = étale`, the reflection half** — a quasi-coherent module whose associated module
  on the small étale site is free is free.
* `isFree_chartSchemeModule_of_isFree_chartSmallEtaleRestriction`: if the 04M0 reading of the
  restriction of a module to a chart is free, so is the Zariski chart module of Stacks 03DX (2).
* `nonempty_basis_chartZariskiModuleStalk_of_over_iso_free`: a trivialization of the chart
  restriction on a Zariski open of the chart, of *arbitrary* index type, makes the Zariski stalk
  free with a basis indexed by that type.
* `finite_of_over_iso_free`: **the index type is finite** — the Zariski stalk of a module of finite
  presentation on charts is a finite module over the local ring of the chart, and a basis of a
  finite module over a nontrivial ring is finite.
* `exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFreeLocus`: from the plain-freeness locus to
  the source's Zariski-chart reading of clause (4) of Stacks 0CZS, at a chosen geometric point.
* `etaleFreeLocus_subset_etaleFiniteFreeLocus` and `etaleFreeLocus_eq_etaleFiniteFreeLocus`: **free
  implies finite free** for a module quasi-coherent and of finite presentation on charts, so that
  the two readings of the locus of Stacks 0CZT coincide.
* `etaleFreeLocus_modulePullback_eq_preimage_of_isPullback`: **the base-change clause of Stacks
  0CZT**, at the plain-freeness locus the source defines.

## References

* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v u

namespace Stacks.SheafOfModules

/-! ### Freeness of arbitrary rank under the operations of a ringed site -/

section Reindex

variable {C : Type u₁} [Category.{v} C] {C' : Type u₁} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{u})

/-- **Freeness, Stacks 03DE (1), is invariant under an equivalence of ringed sites.** -/
theorem isFree_reindex_iff (M : _root_.SheafOfModules.{u} R) :
    ((_root_.SheafOfModules.pushforward.{u} (𝟙 (reindexRing J' e R))).obj M).IsFree ↔ M.IsFree :=
  ⟨fun ⟨I, h⟩ => ⟨I, exists_isColimitCofan_of_reindex e R M h⟩,
    fun ⟨I, h⟩ => ⟨I, exists_isColimitCofan_reindex e R M h⟩⟩

end Reindex

section Over

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A free sheaf of modules restricts to a free sheaf on every slice** along which restriction
preserves colimits. -/
theorem isFree_over (M : _root_.SheafOfModules.{u} R) (U : C)
    [PreservesColimitsOfSize.{u, u} (_root_.SheafOfModules.overFunctor.{u} R U)]
    (h : M.IsFree) : (M.over U).IsFree := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := h
  exact ⟨I, fun i => (_root_.SheafOfModules.overFunctor R U).map (ι i),
    ⟨(Cofan.isColimitMapCoconeEquiv (_root_.SheafOfModules.overFunctor R U) _ _)
      (isColimitOfPreserves (_root_.SheafOfModules.overFunctor R U) hc)⟩⟩

/-- A free presentation whose index type is finite is a finite free presentation. -/
theorem isFiniteFree_of_isColimit_cofan_of_finite (M : _root_.SheafOfModules.{u} R) {I : Type u}
    [Finite I] (ι : I → (_root_.SheafOfModules.unit R ⟶ M))
    (hc : IsColimit (Cofan.mk M ι)) : _root_.SheafOfModules.IsFiniteFree R M := by
  obtain ⟨r, ⟨eq⟩⟩ := Finite.exists_equiv_fin I
  exact (_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit R M).2
    ⟨r, _, ⟨(Cofan.isColimitEquivOfEquiv eq.symm (Cofan.mk M ι)) hc⟩⟩

end Over

section Free

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J RingCat.{u})

/-- The free sheaf of modules on a type is free in the sense of Stacks 03DE (1). -/
theorem isFree_free (I : Type u) :
    (_root_.SheafOfModules.free.{u} (R := R) I).IsFree :=
  ⟨I, fun i => (_root_.SheafOfModules.freeCofan.{u} (R := R) I).inj i,
    ⟨_root_.SheafOfModules.isColimitFreeCofan.{u} (R := R) I⟩⟩

/-- **A free sheaf of modules is isomorphic to `SheafOfModules.free I` for some type `I`.** -/
theorem exists_nonempty_iso_free_of_isFree (M : _root_.SheafOfModules.{u} R) (h : M.IsFree) :
    ∃ I : Type u, Nonempty (M ≅ _root_.SheafOfModules.free.{u} (R := R) I) := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := h
  exact ⟨I, ⟨hc.coconePointUniqueUpToIso (_root_.SheafOfModules.isColimitFreeCofan I)⟩⟩

end Free

end Stacks.SheafOfModules

/-! ### Freeness across the comparison of Stacks 03DX (2) -/

namespace AlgebraicGeometry.SmallEtale

open AlgebraicGeometry.Space

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05VG for the clause 03DE (1) at `τ = étale`, the reflection half.**  If the
associated module of a quasi-coherent `𝒪_S`-module on the small étale site is free, the module is
free. -/
theorem isFree_of_isFree_associatedModule (M : S.Modules) [M.IsQuasicoherent]
    (h : ((associatedModule B S hS).obj M).IsFree) :
    (M : _root_.SheafOfModules.{u} S.ringCatSheaf).IsFree := by
  obtain ⟨I, ⟨e⟩⟩ := Stacks.SheafOfModules.exists_nonempty_iso_free_of_isFree _ _ h
  have := isEquivalence_associatedModuleQcohOnSite' B S hS
  let Mq : (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let Fq : (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
    ⟨_root_.SheafOfModules.free.{u} I,
      Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I⟩
  have eobj : (associatedModuleQcohOnSite B S hS).obj Fq ≅
      (associatedModuleQcohOnSite B S hS).obj Mq :=
    (ObjectProperty.ι _).preimageIso (associatedModuleFreeIso B S hS I ≪≫ e.symm)
  exact _root_.SheafOfModules.IsFree.of_iso
    ((ObjectProperty.ι _).mapIso ((associatedModuleQcohOnSite B S hS).preimageIso eobj))
    (Stacks.SheafOfModules.isFree_free S.ringCatSheaf I)

end AlgebraicGeometry.SmallEtale

namespace Stacks.SheafOfModules

/-- **Freeness, Stacks 03DE (1), is invariant under the comparison equivalence of Stacks 03DX (2)
at a representable algebraic space.** -/
theorem isFree_representedSmallEtaleModule_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) (U : AlgebraicGeometry.BigFppfOver B S hS)
    (M : _root_.SheafOfModules.{u}
      (AlgebraicGeometry.Space.representedSchemeStructureSheaf B S hS U)) :
    (AlgebraicGeometry.Space.representedSmallEtaleModule B S hS U M).IsFree ↔ M.IsFree :=
  isFree_reindex_iff
    (AlgebraicGeometry.Space.representedSmallEtaleEquivalence B S hS U)
    (AlgebraicGeometry.Space.representedSchemeStructureSheaf B S hS U) M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Freeness from the small étale site of a chart to the Zariski site of its scheme -/

/-- **If the 04M0 reading of the restriction of a module to a chart is free, so is the Zariski
chart module of Stacks 03DX (2).** -/
theorem isFree_chartSchemeModule_of_isFree_chartSmallEtaleRestriction
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (h : (chartSmallEtaleRestriction B S hS X M A).IsFree) :
    (chartSchemeModule B S hS X M hM A).IsFree := by
  have : (chartSchemeModule B S hS X M hM A).IsQuasicoherent :=
    isQuasicoherent_chartSchemeModule B S hS X M hM A
  refine _root_.AlgebraicGeometry.SmallEtale.isFree_of_isFree_associatedModule
    (associatedBigEtaleSite B) (chartScheme A)
    ((SmallEtale.toOver B S hS X.1).obj A).left.property
    (chartSchemeModule B S hS X M hM A) ?_
  refine SheafOfModules.IsFree.of_iso
    (associatedModuleChartSchemeModuleIso B S hS X M hM A).symm ?_
  refine (Stacks.SheafOfModules.isFree_representedSmallEtaleModule_iff B S hS _ _).1 ?_
  exact SheafOfModules.IsFree.of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A).symm h

/-! ### Cutting the index type down at the stalk of the chart -/

/-- **A trivialization of the chart restriction on a Zariski open of the chart, of arbitrary index
type, gives a basis of the Zariski stalk indexed by that type.** -/
theorem nonempty_basis_chartZariskiModuleStalk_of_over_iso_free
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2) (I : Type u)
    (W : (chartScheme N.chart).Opens) (hx : chartPoint B S hS X.1 N ∈ W)
    (e : (restrictToChart B S hS X.2 F N.chart).over W ≅ SheafOfModules.free I) :
    Nonempty (Module.Basis I ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F)) := by
  let M : (chartScheme N.chart).Modules := restrictToChart B S hS X.2 F N.chart
  have hiso : IsIso ((M.over W).freeHomEquiv.symm ((M.over W).freeHomEquiv e.inv)) := by
    rw [Equiv.symm_apply_apply]
    infer_instance
  let G : (M.over W).GeneratingSections :=
    { I := I
      s := (M.over W).freeHomEquiv e.inv
      epi := inferInstance }
  obtain ⟨g⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv W M G hx
  exact ⟨(Module.Basis.ofRepr g).map
    (chartZariskiModuleStalkStalkEquiv B S hS X.2 N F).symm⟩

/-- **The index type of a trivialization of the chart restriction of a module of finite
presentation on charts is finite.** -/
theorem finite_of_over_iso_free
    {X : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood xbar) (F : Modules.{u, u} B S hS X.1 X.2)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) (I : Type u)
    (W : (chartScheme N.chart).Opens) (hx : chartPoint B S hS X.1 N ∈ W)
    (e : (restrictToChart B S hS X.2 F N.chart).over W ≅ SheafOfModules.free I) :
    Finite I := by
  have : Module.FinitePresentation ↥(chartLocalRing B S hS X.1 N)
      ↥(chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
    finitePresentation_chartZariskiModuleStalk B S hS N F hfp
  obtain ⟨b⟩ := nonempty_basis_chartZariskiModuleStalk_of_over_iso_free B S hS N F I W hx e
  exact Module.Finite.finite_basis b

/-! ### Free implies finite free on an étale neighbourhood -/

/-- **From the plain-freeness locus of Stacks 0CZT to the source's Zariski-chart reading of
clause (4) of Stacks 0CZS.**  Let `M` be a quasi-coherent `𝒪_X`-module of finite presentation on
charts and let `x` be a point of `|X|` admitting an étale morphism `a : V ⟶ X` of algebraic spaces
through it along which the inverse image of `M` is free.  Then there is a geometric point `x̄` of
`X` above `x` at which `M` is *finite* free in an étale neighbourhood in the source's sense,
`AlgebraicGeometry.Space.IsFiniteFreeNearGeometricPoint`. -/
theorem exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFreeLocus
    {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (hfp : IsFinitePresentationOnCharts B S hS X.2 M)
    {x : points B S hS X.1} (hx : x ∈ etaleFreeLocus B S hS M) :
    ∃ xbar : GeometricPoint B S hS X.1, xbar.image = x ∧
      IsFiniteFreeNearGeometricPoint B S hS xbar M := by
  obtain ⟨V, a, hae, ⟨v, hv⟩, hfree⟩ := hx
  obtain ⟨vbar, hvbar⟩ := exists_geometricRepresentative B S hS V.1 v
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood V.2 vbar
  have hGqc : ((modulePullback B S hS a).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a M hM
  have ei : chartSmallEtaleRestriction B S hS V ((modulePullback B S hS a).obj M) N.chart ≅
      (modulePullback B S hS (chartToSpace B S hS V N.chart)).obj
        ((modulePullback B S hS a).obj M) :=
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS V N.chart)
          (isEtale_chartToSpace B S hS V N.chart)).app ((modulePullback B S hS a).obj M) ≪≫
        etaleModulePullbackChartToSpaceIso B S hS V ((modulePullback B S hS a).obj M)
          N.chart).symm
  have hsch := isFree_chartSchemeModule_of_isFree_chartSmallEtaleRestriction B S hS V
    ((modulePullback B S hS a).obj M) hGqc N.chart
    (SheafOfModules.IsFree.of_iso ei.symm (isFreeModule_modulePullback B S hS
      (chartToSpace B S hS V N.chart) ((modulePullback B S hS a).obj M) hfree))
  have hX : (restrictToChart B S hS X.2 M (chartOfEtaleSource B S hS hae N.chart)).IsFree :=
    SheafOfModules.IsFree.of_iso
      (restrictToChartEtaleSourceIso B S hS hae M hM N.chart).symm
      (SheafOfModules.IsFree.of_iso
        (restrictToChartIsoChartSchemeModule B S hS V ((modulePullback B S hS a).obj M) hGqc
          N.chart).symm hsch)
  obtain ⟨I, ι, ⟨hc⟩⟩ :=
    Stacks.SheafOfModules.isFree_over
      (restrictToChart B S hS X.2 M (chartOfEtaleSource B S hS hae N.chart)) ⊤ hX
  have : Finite I :=
    finite_of_over_iso_free B S hS (SmallEtaleNeighborhood.ofEtaleSource B S hS hae N) M hfp I ⊤
      trivial (hc.coconePointUniqueUpToIso (SheafOfModules.isColimitFreeCofan I))
  obtain ⟨r, ⟨e⟩⟩ := Stacks.SheafOfModules.exists_nonempty_iso_freeULift_of_isFiniteFree _ _
    (Stacks.SheafOfModules.isFiniteFree_of_isColimit_cofan_of_finite _ ι hc)
  exact ⟨geometricPointMap a.hom vbar, by rw [geometricPointMap_image, hvbar, hv],
    SmallEtaleNeighborhood.ofEtaleSource B S hS hae N, r, ⊤, trivial, ⟨e⟩⟩

/-- **Free implies finite free on an étale neighbourhood.**  For a quasi-coherent `𝒪_X`-module of
finite presentation on charts, every point of the plain-freeness locus of Stacks 0CZT lies in the
finite-free locus of clause (4) of Stacks 0CZS. -/
theorem etaleFreeLocus_subset_etaleFiniteFreeLocus {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 M) :
    etaleFreeLocus B S hS M ⊆ etaleFiniteFreeLocus B S hS M := by
  intro x hx
  obtain ⟨xbar, rfl, hnear⟩ :=
    exists_isFiniteFreeNearGeometricPoint_of_mem_etaleFreeLocus B S hS M hM hfp hx
  exact mem_etaleFiniteFreeLocus_of_isFiniteFreeNearGeometricPoint B S hS M hM xbar hnear

/-- **The two readings of the locus of Stacks 0CZT agree** for a quasi-coherent `𝒪_X`-module of
finite presentation on charts: plain freeness on an étale neighbourhood, which is how Stacks 0CZT
defines its locus, and the finite freeness of clause (4) of Stacks 0CZS, which its proof
invokes. -/
theorem etaleFreeLocus_eq_etaleFiniteFreeLocus {X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 M) :
    etaleFreeLocus B S hS M = etaleFiniteFreeLocus B S hS M :=
  Set.Subset.antisymm (etaleFreeLocus_subset_etaleFiniteFreeLocus B S hS M hM hfp)
    (etaleFiniteFreeLocus_subset_etaleFreeLocus B S hS M)

/-! ### The base-change clause of Stacks 0CZT -/

/-- **The base-change clause for the étale free locus.**  Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite presentation, let `F` be a quasi-coherent
`𝒪_X`-module of finite presentation on charts which is flat over `Y`, and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square.  Then the étale free locus of the inverse image `(g')^*F` on `|X'|` is the
inverse image under `|g'|` of the étale free locus of `F` on `|X|`.

The locus is `AlgebraicGeometry.Space.etaleFreeLocus`, the plain-freeness locus by which the
source defines it, and finite presentation of `F` is taken on the small étale site. -/
@[stacks 0CZT "the base-change clause: the etale free locus of (g')^*F on |X'| is the preimage \
under |g'| of the etale free locus of F on |X|, at the PLAIN-FREENESS locus the source defines \
and the openness clause carries, with finite presentation of F read on the small etale site"]
theorem etaleFreeLocus_modulePullback_eq_preimage_of_isPullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsFinitePresentationOnSite F]
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    etaleFreeLocus B S hS ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' etaleFreeLocus B S hS F := by
  have hqc : F.IsQuasicoherentOnSite := inferInstance
  have hfp : IsFinitePresentationOnCharts B S hS X.2 F :=
    isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X F hqc inferInstance
  have hqc' : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F hqc
  have hfp' : IsFinitePresentationOnCharts B S hS X'.2 ((modulePullback B S hS g').obj F) :=
    isFinitePresentationOnCharts_of_isFinitePresentationOnSite B S hS X' _ hqc'
      (isFinitePresentationOnSite_modulePullback B S hS g' F inferInstance)
  rw [etaleFreeLocus_eq_etaleFiniteFreeLocus B S hS _ hqc' hfp',
    etaleFreeLocus_eq_etaleFiniteFreeLocus B S hS F hqc hfp]
  exact etaleFiniteFreeLocus_modulePullback_eq_preimage_of_isPullback B S hS hpb F hf hfp hF

end AlgebraicGeometry.Space

end
