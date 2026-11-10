module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PiSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedIdealSheafOfClosedSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksFrontier.RingTheory.Localization.FreeAwayReduced

/-!
# Generic trivialization of a coherent module on a reduced Noetherian algebraic space

Let `Y` be a Noetherian algebraic space over a scheme `S` which is étale-locally reduced, and let
`𝒢` be a coherent `𝒪_Y`-module.  This file produces a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`
whose open complement `U = Y ∖ V(ℐ)` is nonempty, an integer `r ≥ 0` and a map

`ψ : ℐ^{⊕ r} ⟶ 𝒢`

which is bijective on the sections over every étale chart carrying the unit ideal of `ℐ`, that is,
an isomorphism over `U`.  This is the input of Stacks 07UQ, whose proof obtains it from a dense
open subspace which is a scheme (Properties of Spaces, Proposition 06NH), generic freeness of a
coherent module on it, and the surjectivity half of Stacks 07UM.

The argument is that one, carried out on the small étale site.

* A Noetherian algebraic space is decent, so it has a dense open subspace which is
  representable by a scheme; an affine open of that scheme is an étale chart `D` of `Y` whose
  structure morphism is an open immersion, with Noetherian reduced ring of functions `A`.
* The sections `M = 𝒢(D)` form a finite `A`-module, free over `A_f` for a nonzero `f ∈ A`
  (`Module.exists_ne_zero_free_localizedModule_away_of_isReduced`); the basic open `D_f` is again
  such a chart, and `𝒢(D_f) = M_f` is free over `𝒪(D_f) = A_f`, with a basis `b₁, …, b_r`.
* Let `U ⊆ Y` be the image of `D_f`, an open subspace, and `ℐ` the ideal sheaf of the
  complement.  Every étale chart of `U` factors uniquely through `D_f`, so the basis gives `r`
  sections of `𝒢|_U`, which over every affine chart of `U` form a basis because `𝒢` is
  cartesian on affine charts.
* By the "in particular" display of Stacks 07UM each section extends to a map `ℐⁿ ⟶ 𝒢`; summing
  over a common exponent gives `ψ : (ℐⁿ)^{⊕ r} ⟶ 𝒢`, bijective over the affine charts of `U`,
  hence over all charts of `U` because the affine charts are a dense subsite.

## Main results

* `AlgebraicGeometry.Space.exists_isAffine_isOpenImmersion_chart`: a decent algebraic space with
  a point has an affine étale chart with a point whose structure morphism is an open immersion.
* `AlgebraicGeometry.Space.exists_comp_eq_of_isOpenImmersion`: a morphism into an algebraic space
  whose points lie in the image of an open immersion from a scheme factors through it.
* `AlgebraicGeometry.Space.exists_generic_trivialization`: the generic trivialization.

## References

* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersion charts -/

/-- **A morphism into an algebraic space whose points lie in the image of an open immersion from
a scheme factors through that open immersion.**  The range of the open immersion is an open
subspace, isomorphic to the scheme, and a morphism whose points land in an open subspace factors
through it (Stacks 03IE). -/
theorem exists_comp_eq_of_isOpenImmersion {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z) {A : BigFppfOver B S hS}
    {g : yoneda.obj A ⟶ X} (hg : IsOpenImmersion B S hS g) (a : Z ⟶ X)
    (ha : Set.range (pointsMap B S hS Z a) ⊆ Set.range (pointsMap B S hS (yoneda.obj A) g)) :
    ∃ h : Z ⟶ yoneda.obj A, h ≫ g = a := by
  have _ : Mono g := mono_of_presheaf_isOpenImmersion hg
  have hH := isOpenSubspace_subfunctorRange B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS A) hg
  have hrange : Set.range (pointsMap B S hS (yoneda.obj A) g) ⊆
      Set.range (pointsMap B S hS (Subfunctor.range g).toFunctor (Subfunctor.range g).ι) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange g) y, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
  obtain ⟨a', ha'⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hZ
    (Subfunctor.range g) hH a).2 (ha.trans hrange)
  refine ⟨a' ≫ inv (Subfunctor.toRange g), ?_⟩
  calc (a' ≫ inv (Subfunctor.toRange g)) ≫ g
      = a' ≫ inv (Subfunctor.toRange g) ≫ Subfunctor.toRange g ≫ (Subfunctor.range g).ι := by
        rw [Subfunctor.toRange_ι, Category.assoc]
    _ = a := by rw [IsIso.inv_hom_id_assoc, ha']

/-- The inclusion of an open subscheme of a scheme of the site is an open immersion of
presheaves. -/
private theorem isOpenImmersion_yoneda_map_openSubHom (T : BigFppfOver B S hS)
    (O : T.left.obj.Opens) : IsOpenImmersion B S hS (yoneda.map (openSubHom _ O)) := by
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2 ?_
  rw [toScheme_map_openSubHom]
  exact Scheme.Opens.instIsOpenImmersionι O

/-- **A decent algebraic space with a point has an affine étale chart with a point whose
structure morphism is an open immersion.**  The space has a dense open subspace which is
representable by a scheme (Stacks 06NH); that subspace has a point, and an affine open of the
representing scheme around it is the required chart. -/
theorem exists_isAffine_isOpenImmersion_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hne : Nonempty (points B S hS X)) :
    ∃ D : SmallEtale B S hS X, IsAffine (chartScheme D) ∧ Nonempty (chartScheme D) ∧
      IsOpenImmersion B S hS D.1.hom := by
  obtain ⟨G, hGo, hGrep, hGd⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hX hdec
  obtain ⟨g⟩ := hGd.nonempty_iff.2 hne
  let e := G.toFunctor.reprW
  have hoi : IsOpenImmersion B S hS (e.hom ≫ G.ι) :=
    MorphismProperty.comp_mem _ _ _ (isOpenImmersion_of_isIso B S hS e.hom) hGo.2
  let C : SmallEtale B S hS X :=
    ⟨CostructuredArrow.mk (e.hom ≫ G.ι), presheaf_etale_of_isOpenImmersion B S hS hoi⟩
  let x : chartScheme C := pointsToScheme B S hS G.toFunctor.reprX (pointsMap B S hS _ e.inv g)
  obtain ⟨O, hO, hxO, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (chartScheme C).isBasis_affineOpens (show x ∈ (⊤ : (chartScheme C).Opens) from trivial)
  refine ⟨openChart B S hS X C O, hO, ⟨⟨x, hxO⟩⟩, ?_⟩
  exact MorphismProperty.comp_mem _ _ _ (isOpenImmersion_yoneda_map_openSubHom B S hS _ O) hoi

/-! ### A chart over which a coherent module is free -/

/-- A Noetherian algebraic space is decent: it is quasi-separated, hence Zariski locally
quasi-separated. -/
theorem isDecentSpace_of_isNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hN : IsNoetherian B S hS hZ X) : IsDecentSpace B S hS X :=
  isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZ X hX
    (isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZ X hX hN.2.1)

/-- The ring of functions of a nonempty chart is nontrivial. -/
private theorem nontrivial_chartRing_of_nonempty (Y : AlgebraicSpaces B S hS)
    {D : SmallEtale B S hS Y.1} (h : Nonempty (chartScheme D)) :
    Nontrivial (chartRing B S hS Y.1 Y.2 D) := by
  obtain ⟨x⟩ := h
  exact ((chartScheme D).presheaf.germ ⊤ x trivial).hom.domain_nontrivial

/-- **A coherent module on a nonempty reduced Noetherian algebraic space is free over some
nonempty affine étale chart whose structure morphism is an open immersion.**

An affine chart `D` which is an open immersion exists by
`AlgebraicGeometry.Space.exists_isAffine_isOpenImmersion_chart`; its ring of functions `A` is
reduced, Noetherian and nonzero, and the sections over it form a finite `A`-module, free over
`A_f` for some nonzero `f`.  The basic open of `f` is the required chart: its ring of functions is
`A_f`, the sections over it are the localization away from `f`, and it is nonempty because `f` is
a nonzero function on a reduced affine scheme. -/
theorem exists_free_isOpenImmersion_chart (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hne : Nonempty (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G) :
    ∃ D : SmallEtale B S hS Y.1, IsAffine (chartScheme D) ∧ Nonempty (chartScheme D) ∧
      IsOpenImmersion B S hS D.1.hom ∧
      Module.Free (chartRing B S hS Y.1 Y.2 D) (G.val.obj (op D)) ∧
      Module.Finite (chartRing B S hS Y.1 Y.2 D) (G.val.obj (op D)) := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS Y.1 Y.2).J G.val :=
    ((isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS Y.1 Y.2 G).1 hG).2
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G
      hG.toIsQuasicoherentOnSite
  obtain ⟨D, hDaff, hDne, hDoi⟩ := exists_isAffine_isOpenImmersion_chart B S hS Y.2
    (isDecentSpace_of_isNoetherian B S hS hZ Y.2 hN) hne
  have hDred : IsReduced (chartScheme D) :=
    (exists_atlas_iff_forall_etale B S hS Y.1 (fun V : Scheme.{u} => IsReduced V) Y.2).mp hred
      D.obj.left D.obj.hom D.property
  have hDnoeth : IsLocallyNoetherian (chartScheme D) := isLocallyNoetherian_chart B S hS hN.2.2 D
  have : _root_.IsReduced (chartRing B S hS Y.1 Y.2 D) := @IsReduced.component_reduced _ hDred ⊤
  have : IsNoetherianRing (chartRing B S hS Y.1 Y.2 D) :=
    @IsLocallyNoetherian.component_noetherian _ hDnoeth ⟨⊤, @isAffineOpen_top _ hDaff⟩
  have := nontrivial_chartRing_of_nonempty B S hS Y hDne
  have : Module.Finite (chartRing B S hS Y.1 Y.2 D) (G.val.obj (op D)) :=
    moduleFinite_sections_of_isFiniteType B S hS Y.1 Y.2 hcart hft hDaff
  obtain ⟨f, hf0, hfree⟩ := Module.exists_ne_zero_free_localizedModule_away_of_isReduced
    (chartRing B S hS Y.1 Y.2 D) (G.val.obj (op D))
  let D' := openChart B S hS Y.1 D ((chartScheme D).basicOpen f)
  let ι := openChartInclusion B S hS Y.1 D ((chartScheme D).basicOpen f)
  have hD'aff : IsAffine (chartScheme D') :=
    isAffine_chartScheme_openChart_basicOpen B S hS Y.1 D hDaff f
  let := chartAlgebra (hF := Y.2) ι
  let := chartSectionsModule G ι
  have := chartSections_isScalarTower G ι
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS Y.2 D hDaff f
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS Y.2 G hcart D
    hDaff f
  have hD'free : Module.Free (chartRing B S hS Y.1 Y.2 D') (G.val.obj (op D')) :=
    Module.Free.of_isLocalizedModule_of_free_localizedModule (Submonoid.powers f)
      (chartRing B S hS Y.1 Y.2 D') (chartRestrictLinear G ι)
  have hD'ne : Nonempty (chartScheme D') := by
    have hne' : ((chartScheme D).basicOpen f : Set (chartScheme D)).Nonempty := by
      by_contra hcon
      exact hf0 (@eq_zero_of_basicOpen_eq_bot _ hDred _ f (SetLike.coe_injective
        (Set.not_nonempty_iff_eq_empty.1 hcon)))
    obtain ⟨x, hx⟩ := hne'
    exact ⟨⟨x, hx⟩⟩
  exact ⟨D', hD'aff, hD'ne, MorphismProperty.comp_mem _ _ _
    (isOpenImmersion_yoneda_map_openSubHom B S hS _ _) hDoi, hD'free,
    moduleFinite_sections_of_isFiniteType B S hS Y.1 Y.2 hcart hft hD'aff⟩

/-! ### Extending a section over the open complement -/

/-- **A section of a quasi-coherent module over the complement `U = Y ∖ V(ℐ)` extends to a map
`ℐⁿ ⟶ 𝒢`**, by the surjectivity of the "in particular" display of Stacks 07UM: the map takes the
value of the section on the unit section of `ℐⁿ` over every étale chart of `U`. -/
theorem exists_idealPow_hom_eq_section (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ Y.1)
    (J : IdealSheaves B S hS Y.1 Y.2) (hJ : J.toSheafOfModules.IsQuasicoherentOnSite)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite]
    (s : ((restrictToIdealComplement B S hS Y J).obj G).sections) :
    ∃ (n : ℕ) (φ : idealPowModule J n
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            Y.1 Y.2).O)) ⟶ G),
      ∀ (P : SmallEtale B S hS (idealComplement B S hS Y J).1)
        (h : SheafOfModules.unitOf (1 : chartRing B S hS Y.1 Y.2 (pc B S hS Y J P)) ∈
          (idealPowSubmodule J n (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).obj
              (op (pc B S hS Y J P))),
        (φ.val.app (op (pc B S hS Y J P))).hom ⟨_, h⟩ = s.val (op P) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨z, rfl⟩ := (canonicalMapToSections_bijective B S hS Y J hZ hN hJ G).2 s
  obtain ⟨n, φ, rfl⟩ := Concrete.colimit_exists_rep (homSystem B S hS Y J
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
        Y.2).O)) G) z
  refine ⟨n, φ, fun P h => ?_⟩
  change _ = ((SheafOfModules.unitHomEquiv _ (canonicalMapToHomRestrict B S hS Y J _ G
    (Limits.colimit.ι (homSystem B S hS Y J _ G) n φ))).val (op P))
  refine Eq.trans ?_ (congrArg (fun t => (SheafOfModules.unitHomEquiv _ t).val (op P))
    (canonicalMapToHomRestrict_ι B S hS Y J _ G n φ)).symm
  refine Eq.trans ?_ (SheafOfModules.unitHomEquiv_apply_coe _ _ _).symm
  let O := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      Y.1 Y.2).O)
  let one : ((restrictToIdealComplement B S hS Y J).obj O).val.obj (op P) :=
    SheafOfModules.unitOf (1 : chartRing B S hS Y.1 Y.2 (pc B S hS Y J P))
  have hhom : ((idealPowRestrictIso B S hS Y J n O).hom.val.app (op P)).hom ⟨_, h⟩ = one := rfl
  have hinv : ((idealPowRestrictIso B S hS Y J n O).inv.val.app (op P)).hom one = ⟨_, h⟩ := by
    rw [← hhom]
    exact congrArg (fun k => (k.val.app (op P)).hom ⟨_, h⟩)
      (idealPowRestrictIso B S hS Y J n O).hom_inv_id
  change _ = ((restrictToIdealComplement B S hS Y J).map φ).val.app (op P)
    (((idealPowRestrictIso B S hS Y J n O).inv.val.app (op P)).hom one)
  rw [hinv]
  rfl

/-! ### Charts of the open complement of a sheaf of ideals -/

section IdealComplement

variable (Y : AlgebraicSpaces B S hS) (J : IdealSheaves B S hS Y.1 Y.2)

/-- The image in `Y` of a point of an étale chart of `U = Y ∖ V(ℐ)` lies in the unit locus of
`ℐ`. -/
theorem range_pointsMap_pc_subset (P : SmallEtale B S hS (idealComplement B S hS Y J).1) :
    Set.range (pointsMap B S hS _ (pc B S hS Y J P).1.hom) ⊆ idealUnitLocus B S hS Y J := by
  rintro _ ⟨y, rfl⟩
  rw [← range_pointsMap_idealComplementι B S hS Y J]
  exact ⟨_, (pointsMap_comp_apply B S hS P.1.hom (idealComplementι B S hS Y J).hom y).symm⟩

/-- **An étale chart of `Y` on which `ℐ` is the unit ideal is the postcomposition of an étale
chart of `U = Y ∖ V(ℐ)`**, by an equality of charts. -/
theorem exists_pc_eq_of_eq_top (W : SmallEtale B S hS Y.1) (hW : J.obj (op W) = ⊤) :
    ∃ P : SmallEtale B S hS (idealComplement B S hS Y J).1, pc B S hS Y J P = W := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS Y.2
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (idealComplementSubfunctor B S hS Y J)
    (isOpenSubspace_idealComplementSubfunctor B S hS Y J) W.1.hom).2 (by
      rintro _ ⟨y, rfl⟩
      exact (range_pointsMap_ι_openSubspaceOfPoints B S hS (idealUnitLocus B S hS Y J)).ge
        ⟨W, hW, y, rfl⟩)
  exact ⟨⟨CostructuredArrow.mk g, presheaf_etale_of_postcomp B S hS
      (presheaf_etale_idealComplementι B S hS Y J) W.property hg⟩,
    ObjectProperty.FullSubcategory.ext
      (congrArg (fun α : yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj W) ⟶ Y.1 =>
        (CostructuredArrow.mk α : CostructuredArrow yoneda Y.1)) hg)⟩

/-- A property of the étale charts of `Y` which holds on every chart of `U = Y ∖ V(ℐ)` holds on
every chart of `Y` carrying the unit ideal of `ℐ`. -/
theorem forall_eq_top_of_forall_pc {p : SmallEtale B S hS Y.1 → Prop}
    (h : ∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1, p (pc B S hS Y J P))
    (W : SmallEtale B S hS Y.1) (hW : J.obj (op W) = ⊤) : p W := by
  obtain ⟨P, rfl⟩ := exists_pc_eq_of_eq_top B S hS Y J W hW
  exact h P

/-- A morphism of modules restricts to a map bijective on the sections over an étale chart `P`
of `U = Y ∖ V(ℐ)` exactly when it is bijective on the sections over the composite chart of `Y`:
restriction to `U` is restriction of sections. -/
theorem bijective_restrictToIdealComplement_map_val_app_iff {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (φ : M ⟶ N) (P : SmallEtale B S hS (idealComplement B S hS Y J).1) :
    Function.Bijective (((restrictToIdealComplement B S hS Y J).map φ).val.app (op P)).hom ↔
      Function.Bijective (φ.val.app (op (pc B S hS Y J P))).hom :=
  Iff.rfl

end IdealComplement

/-! ### The generic trivialization -/

/-- A module over a ring `B` which is the base change of an `A`-module along `A ⟶ B` through a
bijective comparison map is a base change in the sense of `IsBaseChange`. -/
theorem isBaseChange_of_bijective_liftBaseChange {R T M N : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module T N]
    [IsScalarTower R T N] (f : M →ₗ[R] N)
    (h : Function.Bijective (LinearMap.liftBaseChange T f)) : IsBaseChange T f := by
  let e := LinearEquiv.ofBijective (LinearMap.liftBaseChange T f) h
  have h2 : f = (e.toLinearMap.restrictScalars R) ∘ₗ (TensorProduct.mk R T M 1) := by
    ext x
    simp [e]
  rw [h2]
  exact (TensorProduct.isBaseChange R M T).comp (IsBaseChange.ofEquiv e)

/-- **A power of a sheaf of ideals of `𝒪_Y`, taken as a submodule of `𝒪_Y`, lies in the sheaf of
ideals**, for a positive exponent. -/
theorem idealPowSubmodule_unit_le (Y : AlgebraicSpaces B S hS)
    (J : IdealSheaves B S hS Y.1 Y.2) (n : ℕ) :
    idealPowSubmodule J (n + 1)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
          Y.2).O)) ≤ J := by
  refine idealPowSubmodule_le J (n + 1) fun X a ha z => ?_
  have haJ : a ∈ J.obj X := SheafOfModules.Submodule.le_iff.1
    (Stacks.Sites.idealPow_succ_le_self J n) X ha
  have hcomm : a • z = SheafOfModules.unitVal z • SheafOfModules.unitOf a := by
    rw [SheafOfModules.unit_smul, SheafOfModules.unit_smul]
    exact congrArg SheafOfModules.unitOf
      ((chartRing_commRing B S hS Y.1 Y.2 X.unop).mul_comm a (SheafOfModules.unitVal z))
  rw [hcomm]
  exact (J.obj X).smul_mem _ haJ

/-- A chart on which a positive power of a sheaf of ideals is the unit ideal carries the unit
ideal of the sheaf of ideals itself. -/
theorem eq_top_of_idealPowSubmodule_unit_eq_top (Y : AlgebraicSpaces B S hS)
    (J : IdealSheaves B S hS Y.1 Y.2) (n : ℕ) (W : SmallEtale B S hS Y.1)
    (h : (idealPowSubmodule J (n + 1)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
          Y.2).O))).obj
        (op W) = ⊤) :
    J.obj (op W) = ⊤ := by
  have hle := SheafOfModules.Submodule.le_iff.1 (idealPowSubmodule_unit_le B S hS Y J n) (op W)
  rw [h] at hle
  exact top_le_iff.1 hle

/-- The sections of a finite product of `𝒪_Y`-modules over a chart are the product of the
sections, through the projections. -/
theorem bijective_pi_π_val_app_fin {Y : AlgebraicSpaces B S hS} {r : ℕ}
    (F : Fin r → Modules.{u, u} B S hS Y.1 Y.2) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Function.Bijective (fun x : (∏ᶜ F).val.obj U => fun i => ((Pi.π F i).val.app U).hom x) :=
  SheafOfModules.bijective_pi_π_val_app F U

/-- **The value of a sum of maps out of a power of the structure sheaf on a chart where all the
targets contain the unit section.**  For submodules `I ≤ K k` of `𝒪_Y` and maps
`φ k : K k ⟶ 𝒢`, the map `∑ k, π_k ≫ (I ⊆ K k) ≫ φ k` out of `I^{⊕ r}` sends a section `x` over a
chart `X` on which every `K k` contains `1` to `∑ k, x_k • φ k(1)`. -/
theorem val_app_sum_pi_π_comp_homOfLE {Y : AlgebraicSpaces B S hS}
    {G : Modules.{u, u} B S hS Y.1 Y.2}
    {I : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        Y.1 Y.2).O)).Submodule}
    {r : ℕ}
    {K : Fin r →
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
          Y.2).O)).Submodule}
    (hle : ∀ k, I ≤ K k) (φ : ∀ k, ((K k).toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2) ⟶ G)
    (X : SmallEtale B S hS Y.1)
    (h1 : ∀ k, SheafOfModules.unitOf (1 : chartRing B S hS Y.1 Y.2 X) ∈ (K k).obj (op X))
    (x : (∏ᶜ fun _ : Fin r =>
      (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)).val.obj (op X)) :
    ((∑ k, Pi.π (fun _ : Fin r => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) k ≫
        Stacks.SheafOfModules.Submodule.homOfLE (hle k) ≫ φ k).val.app (op X)).hom x =
      ∑ k, SheafOfModules.unitVal (((Pi.π (fun _ : Fin r =>
        (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) k).val.app (op X)).hom x).1 •
          ((φ k).val.app (op X)).hom ⟨_, h1 k⟩ := by
  refine (_root_.SheafOfModules.sum_val_app_apply Finset.univ _ _ x).trans
    (Finset.sum_congr rfl fun k _ => ?_)
  set y := ((Pi.π (fun _ : Fin r => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2))
    k).val.app (op X)).hom x
  have hy : ((Stacks.SheafOfModules.Submodule.homOfLE (hle k)).val.app (op X)).hom y =
      SheafOfModules.unitVal y.1 • ⟨_, h1 k⟩ := by
    refine Subtype.ext ?_
    change (y.1 : _) = SheafOfModules.unitVal y.1 •
      SheafOfModules.unitOf (1 : chartRing B S hS Y.1 Y.2 X)
    rw [SheafOfModules.unit_smul, mul_one]
  change ((φ k).val.app (op X)).hom
    (((Stacks.SheafOfModules.Submodule.homOfLE (hle k)).val.app (op X)).hom y) = _
  rw [hy]
  exact ((φ k).val.app (op X)).hom.map_smul _ _

/-- **A coherent module on a nonempty reduced Noetherian algebraic space is free over a nonempty
open subspace, with a basis of sections.**  There are a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`
with nonempty unit locus and sections `s₁, …, s_r` of `𝒢` over `U = Y ∖ V(ℐ)` which form a basis
of the sections of `𝒢` over every affine étale chart of `U`.

The open subspace is the image of a chart `D` over which `𝒢` is free
(`AlgebraicGeometry.Space.exists_free_isOpenImmersion_chart`), and the sections are the images
of a basis over `D`: every étale chart of `U` factors uniquely through `D`, and over an affine
one the sections of `𝒢` are the base change of those over `D`, because `𝒢` is quasi-coherent. -/
theorem exists_generic_basis (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hne : Nonempty (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G) :
    ∃ (J : IdealSheaves B S hS Y.1 Y.2) (r : ℕ)
      (sec : Fin r → ((restrictToIdealComplement B S hS Y J).obj G).sections),
      J.toSheafOfModules.IsQuasicoherentOnSite ∧ (idealUnitLocus B S hS Y J).Nonempty ∧
      ∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1, IsAffine (chartScheme P) →
        Function.Bijective (fun a : Fin r → chartRing B S hS Y.1 Y.2 (pc B S hS Y J P) =>
          ∑ k, a k • (show G.val.obj (op (pc B S hS Y J P)) from (sec k).val (op P))) := by
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G
      hG.toIsQuasicoherentOnSite
  obtain ⟨D, hDaff, hDne, hDoi, hfree, hfin⟩ :=
    exists_free_isOpenImmersion_chart B S hS hZ Y hN hred hne G hG
  have := nontrivial_chartRing_of_nonempty B S hS Y hDne
  obtain ⟨r, ⟨b⟩⟩ : ∃ r : ℕ,
      Nonempty (Module.Basis (Fin r) (chartRing B S hS Y.1 Y.2 D) (G.val.obj (op D))) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  -- the ideal sheaf of the complement of the image of `D`
  have hW₀open : IsOpen (Set.range (pointsMap B S hS _ D.1.hom)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hDoi
  obtain ⟨J, hJq, hJunit⟩ : ∃ J : IdealSheaves B S hS Y.1 Y.2,
      J.toSheafOfModules.IsQuasicoherentOnSite ∧
        idealUnitLocus B S hS Y J = Set.range (pointsMap B S hS _ D.1.hom) :=
    ⟨reducedIdealSheaf B S hS Y _ hW₀open.isClosed_compl,
      isQuasicoherentOnSite_reducedIdealSheaf B S hS Y _ hW₀open.isClosed_compl,
      compl_injective (idealZeroLocus_reducedIdealSheaf B S hS Y _ hW₀open.isClosed_compl)⟩
  have hlift : ∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1,
      Nonempty (pc B S hS Y J P ⟶ D) := by
    intro P
    obtain ⟨h, hh⟩ := exists_comp_eq_of_isOpenImmersion B S hS Y.2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) hDoi (pc B S hS Y J P).1.hom
      ((range_pointsMap_pc_subset B S hS Y J P).trans hJunit.le)
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage h) ?_)⟩
    rwa [Functor.map_preimage]
  have hsub : ∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1,
      Subsingleton (pc B S hS Y J P ⟶ D) := by
    intro P
    have _ : Mono D.1.hom := mono_of_presheaf_isOpenImmersion hDoi
    refine ⟨fun l₁ l₂ => ?_⟩
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply yoneda.map_injective
    apply (cancel_mono D.1.hom).1
    exact (CostructuredArrow.w l₁.hom).trans (CostructuredArrow.w l₂.hom).symm
  obtain ⟨lift⟩ : Nonempty (∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1,
      pc B S hS Y J P ⟶ D) := ⟨fun P => Classical.choice (hlift P)⟩
  obtain ⟨sec, hsec⟩ : ∃ sec : Fin r → ((restrictToIdealComplement B S hS Y J).obj G).sections,
      ∀ k P, (sec k).val (op P) = (G.val.map (lift P).op).hom (b k) :=
    ⟨fun k => ⟨fun P => (G.val.map (lift P.unop).op).hom (b k), fun {P₁ P₂} f => by
      have h := congrArg (fun m : pc B S hS Y J P₂.unop ⟶ D => (G.val.map m.op).hom (b k))
        ((hsub P₂.unop).elim
          ((smallEtalePostcomp B S hS (idealComplementι B S hS Y J)
            (isEtale_idealComplementι B S hS Y J)).map f.unop ≫ lift P₁.unop) (lift P₂.unop))
      exact (congrArg (fun φ => ModuleCat.Hom.hom φ (b k)) (G.val.map_comp (lift P₁.unop).op
        ((smallEtalePostcomp B S hS (idealComplementι B S hS Y J)
          (isEtale_idealComplementι B S hS Y J)).map f.unop).op)).symm.trans h⟩,
      fun _ _ => rfl⟩
  refine ⟨J, r, sec, hJq, ?_, fun P hP => ?_⟩
  · obtain ⟨x⟩ := hDne
    exact ⟨_, hJunit.ge ⟨(pointsEquivScheme B S hS _).symm x, rfl⟩⟩
  let := chartAlgebra (hF := Y.2) (lift P)
  let := chartSectionsModule G (lift P)
  have := chartSections_isScalarTower G (lift P)
  have hbc : IsBaseChange (chartRing B S hS Y.1 Y.2 (pc B S hS Y J P))
      (chartRestrictLinear G (lift P)) :=
    isBaseChange_of_bijective_liftBaseChange _ (hcart D (pc B S hS Y J P) hDaff hP (lift P))
  let cb := IsBaseChange.basis b hbc
  have heq : (fun a : Fin r → chartRing B S hS Y.1 Y.2 (pc B S hS Y J P) =>
      ∑ k, a k • (show G.val.obj (op (pc B S hS Y J P)) from (sec k).val (op P))) =
      cb.equivFun.symm := by
    funext a
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IsBaseChange.basis_apply]
    exact congrArg (a k • ·) (hsec k P)
  rw [heq]
  exact cb.equivFun.symm.bijective

/-- **Sections over the complement of a sheaf of ideals extend to a map out of a direct sum of
copies of a power of it.**  Given sections `s₁, …, s_r` of a quasi-coherent `𝒢` over
`U = Y ∖ V(𝒥)`, there are a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒥` which is the unit ideal over
every chart of `U` and a map `ψ : ℐ^{⊕ r} ⟶ 𝒢` sending a section `x` over a chart of `U` to
`∑ k, x_k • s_k`.

Each `s_k` extends to a map `𝒥ⁿᵏ ⟶ 𝒢` by Stacks 07UM, and `ℐ = 𝒥ⁿ` for an exponent `n ≥ 1`
dominating every `nₖ`. -/
theorem exists_pi_hom_eq_sum_sections (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ Y.1)
    (J : IdealSheaves B S hS Y.1 Y.2) (hJq : J.toSheafOfModules.IsQuasicoherentOnSite)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite] (r : ℕ)
    (sec : Fin r → ((restrictToIdealComplement B S hS Y J).obj G).sections) :
    ∃ I : (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule,
      (∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ → J.obj (op W) = ⊤) ∧
      I.toSheafOfModules.IsQuasicoherentOnSite ∧
      (∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1,
        I.obj (op (pc B S hS Y J P)) = ⊤) ∧
      ∃ ψ : (∏ᶜ fun _ : Fin r => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ⟶ G,
        ∀ (P : SmallEtale B S hS (idealComplement B S hS Y J).1)
          (x : (∏ᶜ fun _ : Fin r =>
            (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)).val.obj (op (pc B S hS Y J P))),
          (ψ.val.app (op (pc B S hS Y J P))).hom x = ∑ k, SheafOfModules.unitVal
            (((Pi.π (fun _ : Fin r => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2))
                k).val.app
              (op (pc B S hS Y J P))).hom x).1 •
                (show G.val.obj (op (pc B S hS Y J P)) from (sec k).val (op P)) := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  choose n φ hφ using fun k => exists_idealPow_hom_eq_section B S hS hZ Y hN J hJq G (sec k)
  have hM : ∃ M : ℕ, ∀ k, n k ≤ M + 1 := by
    refine ⟨∑ k, n k, fun k => ?_⟩
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ k)
    omega
  obtain ⟨M, hnM⟩ := hM
  refine ⟨idealPowSubmodule J (M + 1) _, eq_top_of_idealPowSubmodule_unit_eq_top B S hS Y J M,
    isQuasicoherentOnSite_idealPowModule B S hS Y J _ hZ hN hJq
      (isCoherent_structureSheaf B S hS Y.1 Y.2) (M + 1),
    fun P => idealPowSubmodule_obj_pc_eq_top B S hS Y J (M + 1) _ P,
    ∑ k, Pi.π _ k ≫ Stacks.SheafOfModules.Submodule.homOfLE
      (idealPowSubmodule_antitone J _ (hnM k)) ≫ φ k, fun P x => ?_⟩
  have h1 : ∀ k, SheafOfModules.unitOf (1 : chartRing B S hS Y.1 Y.2 (pc B S hS Y J P)) ∈
      (idealPowSubmodule J (n k) (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).obj (op (pc B S hS Y J P)) := fun k =>
    mem_idealPowSubmodule_pc B S hS Y J (n k) _ P _
  rw [val_app_sum_pi_π_comp_homOfLE B S hS _ φ (pc B S hS Y J P) h1 x]
  exact Finset.sum_congr rfl fun k _ => congrArg (_ • ·) (hφ k P (h1 k))

/-- **Generic trivialization of a coherent module on a reduced Noetherian algebraic space.**

Let `Y` be a Noetherian algebraic space over `S` with a point which is étale-locally reduced, and
let `𝒢` be a coherent `𝒪_Y`-module.  Then there are a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y`
with nonempty unit locus, an integer `r` and a map `ψ : ℐ^{⊕ r} ⟶ 𝒢` which is bijective on the
sections over every étale chart carrying the unit ideal of `ℐ`.

The sections of `AlgebraicGeometry.Space.exists_generic_basis` over `U = Y ∖ V(𝒥)` extend to
`ψ` by `AlgebraicGeometry.Space.exists_pi_hom_eq_sum_sections`, which is then bijective over the
affine charts of `U` because the sections form a basis there, hence over all charts of `U`
(Stacks 04JS); and a chart carrying the unit ideal of `ℐ ⊆ 𝒥` is a chart of `U`. -/
theorem exists_generic_trivialization (hZ : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hne : Nonempty (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G) :
    ∃ I : (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite ∧ (idealUnitLocus B S hS Y I).Nonempty ∧
      ∃ (r : ℕ) (ψ : (∏ᶜ fun _ : Fin r =>
          (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ⟶ G),
        ∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ →
          Function.Bijective (ψ.val.app (op W)).hom := by
  have : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  obtain ⟨J, r, sec, hJq, hJne, hbasis⟩ := exists_generic_basis B S hS hZ Y hN hred hne G hG
  have key := exists_pi_hom_eq_sum_sections B S hS hZ Y hN J hJq G r sec
  obtain ⟨I, hIJ, hIq, hItop, hrest⟩ := key
  obtain ⟨ψ, hψ⟩ := hrest
  -- bijectivity over every chart of the complement
  have hall : ∀ P : SmallEtale B S hS (idealComplement B S hS Y J).1,
      Function.Bijective (ψ.val.app (op (pc B S hS Y J P))).hom := by
    refine SmallEtale.bijective_app_of_bijective_app_of_isAffineChart B S hS
      (idealComplement B S hS Y J).1 (idealComplement B S hS Y J).2
      ((restrictToIdealComplement B S hS Y J).map ψ) (fun P hP => ?_)
    let e₁ : (∏ᶜ fun _ : Fin r =>
        (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)).val.obj (op (pc B S hS Y J P)) →
        (Fin r → chartRing B S hS Y.1 Y.2 (pc B S hS Y J P)) := fun x k =>
      SheafOfModules.unitVal (((Pi.π (fun _ : Fin r =>
        (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) k).val.app
          (op (pc B S hS Y J P))).hom x).1
    have he₁ : Function.Bijective e₁ := by
      have hπ := bijective_pi_π_val_app_fin B S hS
        (fun _ : Fin r => (I.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2))
        (op (pc B S hS Y J P))
      let ev : (Fin r → I.obj (op (pc B S hS Y J P))) ≃
          (Fin r → chartRing B S hS Y.1 Y.2 (pc B S hS Y J P)) :=
        Equiv.piCongrRight fun _ => Equiv.subtypeUnivEquiv fun z => by
          rw [hItop P]; exact Submodule.mem_top
      exact ev.bijective.comp hπ
    have heq : (ψ.val.app (op (pc B S hS Y J P))).hom =
        (fun a : Fin r → chartRing B S hS Y.1 Y.2 (pc B S hS Y J P) =>
          ∑ k, a k • (show G.val.obj (op (pc B S hS Y J P)) from (sec k).val (op P))) ∘ e₁ := by
      funext x
      exact hψ P x
    have hb : Function.Bijective (ψ.val.app (op (pc B S hS Y J P))).hom := by
      rw [heq]
      exact (hbasis P hP).comp he₁
    exact (bijective_restrictToIdealComplement_map_val_app_iff B S hS Y J ψ P).2 hb
  have hne' : (idealUnitLocus B S hS Y I).Nonempty := by
    obtain ⟨x, V, hV, hxV⟩ := hJne
    obtain ⟨P, hP⟩ := exists_pc_eq_of_eq_top B S hS Y J V hV
    refine ⟨x, V, ?_, hxV⟩
    rw [← hP]
    exact hItop P
  have hbij : ∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ →
      Function.Bijective (ψ.val.app (op W)).hom := by
    intro W hW
    exact forall_eq_top_of_forall_pc B S hS Y J
      (p := fun W => Function.Bijective (ψ.val.app (op W)).hom) hall W (hIJ W hW)
  exact ⟨I, hIq, hne', r, ψ, hbij⟩

end AlgebraicGeometry.Space

end
