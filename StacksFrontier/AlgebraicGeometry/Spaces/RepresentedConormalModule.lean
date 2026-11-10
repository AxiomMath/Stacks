module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# The conormal module of a closed subspace of a scheme

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S`, with defining ideal
sheaf `𝓘_Z ⊆ 𝒪_X` on the small étale site of `X` ([Stacks, Tag 03MB]), and let `A` be an étale
scheme chart of `X`.  The base change `j : Z ×_X A ⟶ A` of the inclusion of `Z` is a closed
immersion of schemes, with ideal sheaf `I_j = Ker(𝒪_A ⟶ j_*𝒪)` on the Zariski site of `A`.
Restricting `𝓘_Z` to the Zariski opens of `A` gives exactly `I_j`, as sheaves of modules: over an
affine open `V` of `A` the sections of both are the kernel of `j` on functions over `V`
(`AlgebraicGeometry.Space.mem_openChartIdeal_iff`), and a morphism of sheaves of modules on a
scheme which is bijective over the affine opens is an isomorphism.

When `X` is the algebraic space represented by a scheme `U` of the site, and `A` is the identity
chart, this upgrades to a comparison of the conormal modules.  `𝓘_Z` is quasi-coherent, so by
[Stacks, Tag 03DX] it is the module associated to its restriction to the Zariski site of `U`,
which is `I_j`; the inverse image along a morphism of representable algebraic spaces of an
associated module is the associated module of the Zariski pullback; and so the conormal module
`𝒞_{Z/X} = i^*𝓘_Z` of [Stacks, Tag 04CN] is, read on the scheme `Z₀` representing `Z`, the
module associated to the scheme-level conormal sheaf `j^*I_j` of [Stacks, Tag 01R2].  In
particular `𝒞_{Z/X}` is finite locally free on the small étale site as soon as the scheme-level
conormal sheaf is finite locally free on `Z₀`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemePushforward`: the restriction of an `𝒪_X`-module to the
  Zariski site of the scheme of an étale chart, as a direct image.
* `AlgebraicGeometry.Space.chartSchemePushforwardDefiningIdealIso`: **the restriction of `𝓘_Z` to
  the Zariski site of a chart is the ideal sheaf of the base changed closed immersion.**
* `AlgebraicGeometry.Space.representedClosedObj`, `AlgebraicGeometry.Space.representedClosedHom`
  and `AlgebraicGeometry.Space.representedClosedMap`: the scheme representing a closed subspace of
  a representable algebraic space, its closed immersion, and its identification with the
  subspace.
* `AlgebraicGeometry.Space.conormalModuleRepresentedIso`: **the conormal module of a closed
  subspace of a representable algebraic space is the module associated to the scheme-level
  conormal sheaf.**

## Main results

* `AlgebraicGeometry.Scheme.Modules.hom_ext_of_val_app_affineOpens`: a morphism of sheaves of
  modules on a scheme is determined by its sections over the affine opens.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_of_representable`: the
  conormal module of a closed subspace of a representable algebraic space is finite locally free
  when the scheme-level conormal sheaf is.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A morphism of sheaves of modules on a scheme is determined by its sections over the affine
opens.**  The affine opens form a basis of the topology, and a morphism into a sheaf is
determined by its values on a basis. -/
theorem Scheme.Modules.hom_ext_of_val_app_affineOpens {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (a b : M ⟶ N)
    (h : ∀ U : X.affineOpens, a.val.app (op U.1) = b.val.app (op U.1)) : a = b := by
  refine (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_injective ?_
  apply Sheaf.hom_ext
  refine TopCat.Sheaf.hom_ext (B := fun U : X.affineOpens => U.1) _
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj N)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    (fun U => ?_)
  ext x
  exact ConcreteCategory.congr_hom (h U) x

end AlgebraicGeometry

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1)

/-- The restriction of an `𝒪_X`-module to the Zariski site of the scheme of an étale chart `A`,
read as the direct image along the inclusion of the Zariski opens of `A` into the small étale
site of `X`: its sections over an open `V` are the sections of the module over the étale chart
`V` cuts out (`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward`). -/
noncomputable abbrev chartSchemePushforward :=
  SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 A)

/-- The comparison `𝒪_A ⟶ (𝒪_X)|_A` of structure sheaves on the Zariski site of an étale chart. -/
noncomputable abbrev unitToChartPushforward :=
  SheafOfModules.unitToPushforwardObjUnit (chartSchemeRestrictionSheafHom B S hS X.2 A)

/-- Over an open `V` of the chart the comparison of structure sheaves is the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem unitToChartPushforward_val_app_apply (V : (chartScheme A).Opens)
    (a : Γ(chartScheme A, V)) :
    (unitToChartPushforward B S hS X A).val.app (op V) a = V.topIso.inv a := rfl

/-- The comparison of structure sheaves on the Zariski site of an étale chart is an isomorphism:
it is `AlgebraicGeometry.Scheme.Opens.topIso` over every open. -/
theorem isIso_unitToChartPushforward : IsIso (unitToChartPushforward B S hS X A) := by
  refine Scheme.Modules.isIso_of_isIso_app_affineOpens _ fun U => ?_
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective (fun a : Γ(chartScheme A, U.1) => U.1.topIso.inv a)
  exact ConcreteCategory.bijective_of_isIso U.1.topIso.inv

/-- The restriction of `𝒪_X` to the Zariski site of an étale chart `A` is `𝒪_A`. -/
noncomputable def chartUnitIso :
    SheafOfModules.unit (chartScheme A).ringCatSheaf ≅
      (chartSchemePushforward B S hS X A).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  @asIso _ _ _ _ (unitToChartPushforward B S hS X A) (isIso_unitToChartPushforward B S hS X A)

/-- The identification of structure sheaves is the comparison morphism. -/
theorem chartUnitIso_hom :
    (chartUnitIso B S hS X A).hom = unitToChartPushforward B S hS X A := rfl

/-- Over an open `V` of the chart, the inverse identification of structure sheaves is
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem chartUnitIso_inv_val_app_apply (V : (chartScheme A).Opens)
    (a : Γ(V.toScheme, ⊤)) :
    (chartUnitIso B S hS X A).inv.val.app (op V) a = V.topIso.hom a := by
  have h := congrArg (fun φ => φ.val.app (op V) (V.topIso.hom a))
    (chartUnitIso B S hS X A).hom_inv_id
  have h2 : (chartUnitIso B S hS X A).hom.val.app (op V) (V.topIso.hom a) = a := by
    rw [chartUnitIso_hom]
    exact (unitToChartPushforward_val_app_apply B S hS X A V _).trans
      (ConcreteCategory.congr_hom V.topIso.hom_inv_id a)
  exact (congrArg ((chartUnitIso B S hS X A).inv.val.app (op V)) h2).symm.trans h

variable (Z : ClosedSubspaces B S hS X.1)

/-- The structure morphism of the closed immersion `Z ×_X A ⟶ chartScheme A`. -/
noncomputable abbrev chartBaseChangeUnitMap :=
  SheafOfModules.unitToPushforwardObjUnit (chartBaseChangeHom B S hS X Z A).toRingCatSheafHom

/-- The restriction of the defining ideal sheaf `𝓘_Z` to the Zariski site of an étale chart,
mapped into the structure sheaf of the chart's scheme. -/
noncomputable def chartIdealToUnit :
    (chartSchemePushforward B S hS X A).obj (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      SheafOfModules.unit (chartScheme A).ringCatSheaf :=
  (chartSchemePushforward B S hS X A).map (definingIdealSheaf B S hS X Z).ι ≫
    (chartUnitIso B S hS X A).inv

/-- Over an open `V` of the chart, `AlgebraicGeometry.Space.chartIdealToUnit` reads a section of
`𝓘_Z` over the étale chart cut out by `V` as a function on `V`. -/
theorem chartIdealToUnit_val_app_apply (V : (chartScheme A).Opens)
    (x : (definingIdealSheaf B S hS X Z).obj (op (openChart B S hS X.1 A V))) :
    (chartIdealToUnit B S hS X A Z).val.app (op V) x = V.topIso.hom x.1 :=
  chartUnitIso_inv_val_app_apply B S hS X A V x.1

/-- Over an open `V`, the structure morphism of the base changed closed immersion is the map on
functions over `V`. -/
theorem chartBaseChangeUnitMap_val_app_apply (V : (chartScheme A).Opens)
    (y : Γ(chartScheme A, V)) :
    (chartBaseChangeUnitMap B S hS X A Z).val.app (op V) y =
      (chartBaseChangeHom B S hS X Z A).app V y := rfl

/-- **The restricted ideal sheaf is killed by the base changed closed immersion.**  Over an
affine open of the chart this is `AlgebraicGeometry.Space.mem_openChartIdeal_iff`, and a morphism
of sheaves of modules on a scheme is determined over the affine opens. -/
theorem chartIdealToUnit_comp_eq_zero :
    chartIdealToUnit B S hS X A Z ≫ chartBaseChangeUnitMap B S hS X A Z = 0 := by
  refine Scheme.Modules.hom_ext_of_val_app_affineOpens _ _ fun V => ?_
  ext x
  change (chartBaseChangeUnitMap B S hS X A Z).val.app (op V.1)
    ((chartIdealToUnit B S hS X A Z).val.app (op V.1) x) = 0
  exact (congrArg ((chartBaseChangeUnitMap B S hS X A Z).val.app (op V.1))
    (chartIdealToUnit_val_app_apply B S hS X A Z V.1 x)).trans
    ((mem_openChartIdeal_iff B S hS X Z A V _).1 (Ideal.mem_map_of_mem _ x.2))

/-- The restriction of `𝓘_Z` to the Zariski site of an étale chart, mapped into the sectionwise
kernel of the base changed closed immersion. -/
noncomputable def chartIdealToKer :
    (chartSchemePushforward B S hS X A).obj (definingIdealSheaf B S hS X Z).toSheafOfModules ⟶
      SheafOfModules.kerObj (chartBaseChangeUnitMap B S hS X A Z) :=
  SheafOfModules.kerLift _ (chartIdealToUnit_comp_eq_zero B S hS X A Z)

/-- **The restriction of `𝓘_Z` to the Zariski site of a chart is the sectionwise kernel of the
base changed closed immersion.**  Over an affine open of the chart the sections of both are the
kernel of the closed immersion on functions (`AlgebraicGeometry.Space.mem_openChartIdeal_iff`),
and a morphism of sheaves of modules on a scheme bijective over the affine opens is an
isomorphism. -/
theorem isIso_chartIdealToKer : IsIso (chartIdealToKer B S hS X A Z) := by
  refine Scheme.Modules.isIso_of_isIso_app_affineOpens _ fun V => ?_
  have key (x : (definingIdealSheaf B S hS X Z).obj (op (openChart B S hS X.1 A V.1))) :
      ((chartIdealToKer B S hS X A Z).val.app (op V.1) x).val = V.1.topIso.hom x.1 :=
    (SheafOfModules.kerLift_val_app _ (chartIdealToUnit_comp_eq_zero B S hS X A Z) (op V.1)
      x).trans (chartIdealToUnit_val_app_apply B S hS X A Z V.1 x)
  have hb := ConcreteCategory.bijective_of_isIso V.1.topIso.hom
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun x y hxy => ?_, fun z => ?_⟩
  · exact Subtype.ext (hb.1 ((key x).symm.trans ((congrArg Subtype.val hxy).trans (key y))))
  · have hz : (chartBaseChangeHom B S hS X Z A).app V.1 z.1 = 0 := z.2
    obtain ⟨x, hx, hxz⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1
      ((mem_openChartIdeal_iff B S hS X Z A V z.1).2 hz)
    exact ⟨⟨x, hx⟩, Subtype.ext ((key ⟨x, hx⟩).trans hxz)⟩

/-- **The restriction of the defining ideal sheaf `𝓘_Z ⊆ 𝒪_X` to the Zariski site of an étale
scheme chart `A` is the ideal sheaf of the closed immersion `Z ×_X A ⟶ A`**, as sheaves of
modules on the Zariski site of `A`.

This supplies the step which `AlgebraicGeometry.Space.chartIdealSheafIso` leaves open: that
comparison is with the Zariski sheaf of ideals `𝓘_Z` induces on the affine opens of the chart,
while here `𝓘_Z` itself is restricted along every Zariski open of the chart. -/
noncomputable def chartSchemePushforwardDefiningIdealIso :
    (chartSchemePushforward B S hS X A).obj (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      Stacks.ClosedImmersion.idealSheaf (chartBaseChangeHom B S hS X Z A).toLRSHom.toShHom :=
  @asIso _ _ _ _ _ (isIso_chartIdealToKer B S hS X A Z) ≪≫
    (Stacks.Conormal.idealSheafKerObjIso (chartBaseChangeHom B S hS X Z A)).symm

section Represented

variable (U : BigFppfOver B S hS)

/-- At the identity chart of a representable algebraic space `yoneda.obj U`, the restriction to
the Zariski site of the scheme underlying `U` is the right adjoint of the associated-module
functor of [Stacks, Tag 03DU], applied to the module read on the small étale site of that
scheme. -/
noncomputable def chartSchemePushforwardIdIsoRestrictModule
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    (chartSchemePushforward B S hS (schemeSpace U) (idEtaleChart B S hS U)).obj N ≅
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N) :=
  (restrictToChartSchemeIsoPushforward B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U) N).symm ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS U N

/-- **A quasi-coherent module on a representable algebraic space is the module associated to its
restriction to the Zariski site of the representing scheme.**  This is the counit of the
associated-module adjunction, an isomorphism at a quasi-coherent module by
[Stacks, Tag 03DX]. -/
noncomputable def isoAssociatedModuleChartPushforward
    (N : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    N ≅ (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        ((chartSchemePushforward B S hS (schemeSpace U) (idEtaleChart B S hS U)).obj N)) := by
  let E := representedSmallEtaleModuleEquivalence B S hS U
  have hG : (E.inverse.obj N).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app N).symm hN)
  have hc := _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property (E.inverse.obj N) hG
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule _ _ _ _ hG)
  exact (E.counitIso.app N).symm ≪≫ E.functor.mapIso
    ((@asIso _ _ _ _ _ hc).symm ≪≫
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
        (chartSchemePushforwardIdIsoRestrictModule B S hS U N).symm)

variable (Z : ClosedSubspaces B S hS (yoneda.obj U))

/-- The scheme cut out of `U` by a closed subspace of the algebraic space it represents. -/
noncomputable abbrev representedClosedObj : BigFppfOver B S hS :=
  Z.2.2.rep.pullback (idEtaleChart B S hS U).1.hom

/-- The closed immersion of the scheme cut out by `Z`, as a morphism of the big fppf site. -/
noncomputable abbrev representedClosedHom : representedClosedObj B S hS U Z ⟶ U :=
  Z.2.2.rep.snd (idEtaleChart B S hS U).1.hom

/-- The identification of the representing scheme of `Z` with `Z`. -/
noncomputable abbrev representedClosedMap :
    schemeSpace (representedClosedObj B S hS U Z) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (Z.2.2.rep.fst (idEtaleChart B S hS U).1.hom)

/-- The identification of the representing scheme of a closed subspace with the subspace is an
isomorphism: it is the base change of the closed immersion along the identity. -/
instance isIso_representedClosedMap_hom : IsIso (representedClosedMap B S hS U Z).hom :=
  (Z.2.2.rep.isPullback (idEtaleChart B S hS U).1.hom).isIso_fst_of_isIso
    (inferInstanceAs (IsIso (𝟙 (yoneda.obj U))))

/-- The representing scheme of `Z`, followed by the inclusion of `Z`, is the morphism of
representable algebraic spaces induced by the closed immersion of schemes. -/
theorem representedClosedMap_comp_subspaceInclusion :
    representedClosedMap B S hS U Z ≫ subspaceInclusion B S hS (schemeSpace U) Z =
      representedSpaceMap B S hS (representedClosedHom B S hS U Z) := by
  apply ObjectProperty.hom_ext
  exact (Z.2.2.rep.isPullback (idEtaleChart B S hS U).1.hom).w.trans (Category.comp_id _)

/-- The closed immersion of the representing scheme of `Z`, read on represented presheaves, is
the identification with `Z` followed by the inclusion of `Z`. -/
theorem yoneda_map_representedClosedHom :
    yoneda.map (representedClosedHom B S hS U Z) =
      Z.2.2.rep.fst (idEtaleChart B S hS U).1.hom ≫ Z.1.ι :=
  ((Z.2.2.rep.isPullback (idEtaleChart B S hS U).1.hom).w.trans (Category.comp_id _)).symm

/-- **The conormal module of a closed subspace of a representable algebraic space is the module
associated to the conormal sheaf of the corresponding closed immersion of schemes.**  Let `Z` be
a closed subspace of the algebraic space represented by `U`, represented in turn by the scheme
`Z₀` with closed immersion `j : Z₀ ⟶ U`.  Read on `Z₀`, the conormal module `𝒞_{Z/X}` of
[Stacks, Tag 04CN] is the module associated, by [Stacks, Tag 03DU], to the conormal sheaf
`j^*I_j` of [Stacks, Tag 01R2] of `j`.

The defining ideal sheaf of `Z` is the module associated to the ideal sheaf of `j`
(`AlgebraicGeometry.Space.isoAssociatedModuleChartPushforward` and
`AlgebraicGeometry.Space.chartSchemePushforwardDefiningIdealIso`), and the inverse image of an
associated module along a morphism of representable algebraic spaces is the associated module of
the Zariski pullback (`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`). -/
noncomputable def conormalModuleRepresentedIso :
    (modulePullback B S hS (representedClosedMap B S hS U Z)).obj
        (conormalModule B S hS (schemeSpace U) Z) ≅
      (representedSmallEtaleModuleEquivalence B S hS
          (representedClosedObj B S hS U Z)).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (representedClosedObj B S hS U Z))
          (representedClosedObj B S hS U Z).left.property).obj
          (Stacks.Thickenings.schemeConormalSheaf
            (chartBaseChangeHom B S hS (schemeSpace U) Z (idEtaleChart B S hS U)))) :=
  (modulePullbackCompIso B S hS (representedClosedMap B S hS U Z)
      (subspaceInclusion B S hS (schemeSpace U) Z)).app _ ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj
      (definingIdealSheaf B S hS (schemeSpace U) Z).toSheafOfModules)
      (representedClosedMap_comp_subspaceInclusion B S hS U Z)) ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS (representedClosedHom B S hS U Z))).mapIso
      (isoAssociatedModuleChartPushforward B S hS U _
          (isQuasicoherentOnSite_definingIdealSheaf B S hS (schemeSpace U) Z) ≪≫
        (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
            (chartSchemePushforwardDefiningIdealIso B S hS (schemeSpace U)
              (idEtaleChart B S hS U) Z))) ≪≫
    representedAssociatedModulePullbackIso B S hS (representedClosedHom B S hS U Z)
      (relativelyRepresentable_yoneda_map B S hS _) _

/-- **The conormal module of a closed subspace of a representable algebraic space is finite
locally free when the conormal sheaf of the corresponding closed immersion of schemes is.**  This
is `AlgebraicGeometry.Space.conormalModuleRepresentedIso` together with [Stacks, Tag 05VG] for
the associated module. -/
theorem isFiniteLocallyFreeOnSite_conormalModule_of_representable
    (h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Thickenings.schemeConormalSheaf
        (chartBaseChangeHom B S hS (schemeSpace U) Z (idEtaleChart B S hS U)))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalModule B S hS (schemeSpace U) Z) := by
  have hA := _root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
    (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj (representedClosedObj B S hS U Z))
    (representedClosedObj B S hS U Z).left.property _ h
  have hB := (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS
    (representedClosedObj B S hS U Z) _).2 hA
  have hC := SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (conormalModuleRepresentedIso B S hS U Z).symm hB
  exact (isFiniteLocallyFreeOnSite_modulePullback_iff B S hS (representedClosedMap B S hS U Z)
    (isEtale_of_isIso B S hS _) (isSurjective_of_isIso B S hS _) _).2 hC

end Represented

end AlgebraicGeometry.Space
