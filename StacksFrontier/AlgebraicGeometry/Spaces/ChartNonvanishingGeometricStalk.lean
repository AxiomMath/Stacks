module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski

/-!
# The nonvanishing locus of a section on an étale chart, read on geometric stalks

Let `X` be an algebraic space, `F` a quasi-coherent `𝒪_X`-module and `V` an étale scheme chart
of `X`. A section `σ` of `F` over `V` gives a global section of the restriction `F|_V` of `F` to
the scheme of `V` (`AlgebraicGeometry.Space.chartRestrictionTopSection`), and so a nonvanishing
locus on that scheme: the points `v` at which the germ of `σ` is not in `𝔪_v (F|_V)_v`.

This file proves that this locus is read on the geometric stalks of `F`: `v` lies in it exactly
when the germ of `σ` at a geometric point over `v` is not in `𝔪_{x̄} F_{x̄}`. Since the geometric
stalk does not depend on the chart, the nonvanishing locus of the restriction of `σ` along a
morphism `h : Z ⟶ V` of étale charts is the inverse image under `h` of the nonvanishing locus of
`σ` (`AlgebraicGeometry.Space.mem_nonvanishingLocus_chartRestrictionTopSection_map_iff`). This is
the stability of the opens `X_s` used in the proof of [Stacks, Tag 0D35].

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionTopSection`: the global section of the chart
  restriction attached to a section over the chart.

## Main results

* `ModuleCat.one_tmul_mem_maximalIdeal_smul_top_iff`: along a local homomorphism of local rings
  `R ⟶ R'`, an element `z` of an `R`-module lies in `𝔪_R M` exactly when `1 ⊗ z` lies in
  `𝔪_{R'} (R' ⊗_R M)`.
* `AlgebraicGeometry.Space.chartZariskiStalkAddEquiv_germ`: the comparison of the two Zariski
  stalks of the chart restriction is the identity on germs.
* `AlgebraicGeometry.Space.mem_nonvanishingLocus_chartRestrictionTopSection_iff`: the
  nonvanishing criterion on the geometric stalk.
* `AlgebraicGeometry.Space.mem_nonvanishingLocus_chartRestrictionTopSection_map_iff`: stability
  under morphisms of étale charts.
* `AlgebraicGeometry.Space.surjective_chartRestrictionTopSection`: every global section of the
  chart restriction comes from a section over the chart.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open Stacks.ModuleStalk
open scoped ChangeOfRings

universe u u₁ u₂ v

/-! ### Membership in `𝔪 M` along a local homomorphism -/

namespace ModuleCat

/-- Along a local homomorphism `f : R ⟶ R'` of local rings, if `1 ⊗ z` lies in
`𝔪_{R'} (R' ⊗_R M)` then `z` lies in `𝔪_R M`. -/
private theorem mem_maximalIdeal_smul_top_of_one_tmul_mem {R : Type u₁} {R' : Type u₂}
    [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    {M : ModuleCat.{v} R} {z : M}
    (h : ((1 : R') ⊗ₜ[R,f] z : (ModuleCat.extendScalars f).obj M) ∈
      (IsLocalRing.maximalIdeal R' • ⊤ : Submodule R' ((ModuleCat.extendScalars f).obj M))) :
    z ∈ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R M) := by
  let : Algebra R R' := f.toAlgebra
  by_contra hz
  set N : Submodule R M := IsLocalRing.maximalIdeal R • ⊤
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hq : (Submodule.Quotient.mk z : M ⧸ N) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ IsLocalRing.maximalIdeal R) (M ⧸ N),
      φ (Submodule.Quotient.mk z) ≠ 0 := by
    by_contra! H
    exact hq ((Module.forall_dual_apply_eq_zero_iff _ _).1 H)
  let ι : R ⧸ IsLocalRing.maximalIdeal R →+* R' ⧸ IsLocalRing.maximalIdeal R' :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp f) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact map_nonunit f a ha)
  let l : M →ₗ[R] R' ⧸ IsLocalRing.maximalIdeal R' :=
    { toFun := fun m => ι (φ (Submodule.Quotient.mk m))
      map_add' := fun m m' => by
        rw [Submodule.Quotient.mk_add, map_add, map_add]
      map_smul' := fun r m => by
        rw [Submodule.Quotient.mk_smul, ← algebraMap_smul (R ⧸ IsLocalRing.maximalIdeal R) r,
          map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  let L : R' ⊗[R] M →ₗ[R'] R' ⧸ IsLocalRing.maximalIdeal R' := l.liftBaseChange R'
  have hL : ∀ t ∈ (IsLocalRing.maximalIdeal R' • ⊤ : Submodule R' (R' ⊗[R] M)), L t = 0 := by
    intro t ht
    refine Submodule.smul_induction_on ht (fun a ha t _ => ?_) (fun t t' h h' => ?_)
    · rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    · rw [map_add, h, h', add_zero]
  have h1 : L ((1 : R') ⊗ₜ[R] z) = ι (φ (Submodule.Quotient.mk z)) := by
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have h2 : ι (φ (Submodule.Quotient.mk z)) ≠ 0 :=
    fun h0 => hφ (ι.injective (h0.trans (map_zero ι).symm))
  exact h2 (h1 ▸ hL _ h)

/-- Along a local homomorphism `f : R ⟶ R'` of local rings, if `z` lies in `𝔪_R M` then `1 ⊗ z`
lies in `𝔪_{R'} (R' ⊗_R M)`. -/
private theorem one_tmul_mem_maximalIdeal_smul_top_of_mem {R : Type u₁} {R' : Type u₂}
    [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    {M : ModuleCat.{v} R} {z : M}
    (hz : z ∈ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R M)) :
    ((1 : R') ⊗ₜ[R, f] z : (ModuleCat.extendScalars f).obj M) ∈
      (IsLocalRing.maximalIdeal R' • ⊤ : Submodule R' ((ModuleCat.extendScalars f).obj M)) := by
  let : Algebra R R' := f.toAlgebra
  refine Submodule.smul_induction_on hz (fun a ha m _ => ?_) (fun m m' h h' => ?_)
  · let t : ↑((ModuleCat.extendScalars f).obj M) := (1 : R') ⊗ₜ[R, f] m
    have hmem : f a • t ∈
        (IsLocalRing.maximalIdeal R' • ⊤ : Submodule R' ((ModuleCat.extendScalars f).obj M)) :=
      Submodule.smul_mem_smul (map_nonunit f a ha) Submodule.mem_top
    exact (congrArg (· ∈ (IsLocalRing.maximalIdeal R' • ⊤ :
        Submodule R' ((ModuleCat.extendScalars f).obj M)))
      (TensorProduct.smul_tmul a
        (show ↑((ModuleCat.restrictScalars f).obj (ModuleCat.of R' R')) from (1 : R'))
        m).symm).mpr hmem
  · have e : ((1 : R') ⊗ₜ[R, f] (m + m') : (ModuleCat.extendScalars f).obj M) =
        ((1 : R') ⊗ₜ[R, f] m : (ModuleCat.extendScalars f).obj M) +
          ((1 : R') ⊗ₜ[R, f] m' : (ModuleCat.extendScalars f).obj M) :=
      TensorProduct.tmul_add _ _ _
    rw [e]
    exact Submodule.add_mem _ h h'

/-- **Membership in `𝔪 M` is detected after a local base change.** For a local homomorphism
`f : R ⟶ R'` of local rings and an `R`-module `M`, an element `z` of `M` lies in `𝔪_R M` exactly
when `1 ⊗ z` lies in `𝔪_{R'} (R' ⊗_R M)`. One direction is the locality of `f`; for the other,
a linear form on the residue vector space `M / 𝔪_R M` which does not vanish at `z` extends to an
`R'`-linear map `R' ⊗_R M ⟶ R' / 𝔪_{R'}` killing `𝔪_{R'} (R' ⊗_R M)` and not `1 ⊗ z`. -/
theorem one_tmul_mem_maximalIdeal_smul_top_iff {R : Type u₁} {R' : Type u₂} [CommRing R]
    [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    {M : ModuleCat.{v} R} (z : M) :
    ((1 : R') ⊗ₜ[R, f] z : (ModuleCat.extendScalars f).obj M) ∈
        (IsLocalRing.maximalIdeal R' • ⊤ : Submodule R' ((ModuleCat.extendScalars f).obj M)) ↔
      z ∈ (IsLocalRing.maximalIdeal R • ⊤ : Submodule R M) :=
  ⟨mem_maximalIdeal_smul_top_of_one_tmul_mem f, one_tmul_mem_maximalIdeal_smul_top_of_mem f⟩

end ModuleCat

/-- Membership in `I • ⊤` is invariant under a linear equivalence. -/
theorem LinearEquiv.mem_smul_top_iff {R : Type u₁} [CommRing R] {M M' : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (I : Ideal R) (m : M) :
    e m ∈ (I • ⊤ : Submodule R M') ↔ m ∈ (I • ⊤ : Submodule R M) := by
  have hmap : (I • ⊤ : Submodule R M).map (e : M →ₗ[R] M') = I • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two Zariski stalks of the chart restriction agree on germs -/

section Germ

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
  (F : Modules.{u, u} B S hS X hX)

/-- **The comparison of the stalk of the chart restriction at the point of the Zariski site with
its ordinary stalk is the identity on germs.** -/
theorem chartZariskiStalkAddEquiv_germ (W : (chartScheme V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W)
    (t : (restrictToChart B S hS hX F V.chart).val.obj (op W)) :
    chartZariskiStalkAddEquiv B S hS hX V F
        (Stacks.moduleStalkLargeGerm (chartZariskiPoint B S hS X V) (chartZariskiSheaf B S hS V)
          (restrictToChart B S hS hX F V.chart) W ⟨⟨hw⟩⟩ t) =
      TopCat.Presheaf.germ (restrictToChart B S hS hX F V.chart).val.presheaf W
        (chartPoint B S hS X V) hw t := by
  change Opens.pointFiberStalkHom (chartPoint B S hS X V)
      (restrictToChart B S hS hX F V.chart).val.presheaf
      (Stacks.moduleStalkLargeFiberAddEquiv (chartZariskiPoint B S hS X V)
        (chartZariskiSheaf B S hS V) (restrictToChart B S hS hX F V.chart)
        (Stacks.moduleStalkLargeGerm (chartZariskiPoint B S hS X V) (chartZariskiSheaf B S hS V)
          (restrictToChart B S hS hX F V.chart) W ⟨⟨hw⟩⟩ t)) = _
  exact (congrArg (ConcreteCategory.hom (Opens.pointFiberStalkHom (chartPoint B S hS X V)
      (restrictToChart B S hS hX F V.chart).val.presheaf))
      (Stacks.moduleStalkLargeFiberAddEquiv_germ (chartZariskiPoint B S hS X V)
        (chartZariskiSheaf B S hS V) (restrictToChart B S hS hX F V.chart) W ⟨⟨hw⟩⟩ t)).trans
    (Opens.pointFiberStalkHom_toPresheafModuleFiber (chartPoint B S hS X V) _ _ W ⟨⟨hw⟩⟩ t)

end Germ

/-! ### The global section attached to a section over the chart -/

variable (X : AlgebraicSpaces B S hS)

/-- The restriction `F|_V` of an `𝒪_X`-module to the scheme of an étale chart,
`AlgebraicGeometry.Space.restrictToChart`, read as an `𝒪_V`-module of the scheme. -/
noncomputable def chartRestrictionSchemeModule (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) : (chartScheme V).Modules :=
  restrictToChart.{u, u} B S hS X.2 F V

/-- **The global section of the chart restriction attached to a section over the chart.** A
section `σ` of `F` over an étale chart `V` restricts to the chart cut out by the whole of the
scheme of `V`, and the sheafification unit of `AlgebraicGeometry.Space.restrictToChart` carries
it to a global section of `F|_V`. -/
noncomputable def chartRestrictionTopSection (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (σ : F.val.obj (op V)) :
    Γ(chartRestrictionSchemeModule B S hS X F V, ⊤) := by
  let J := Opens.grothendieckTopology (chartScheme V)
  letI : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  exact (CategoryTheory.toSheafify J (chartRestrictionPresheaf B S hS X.2 F V).presheaf).app
    (op ⊤) (ULift.up (F.val.map (chartOpensTopHom B S hS X V).op σ))

/-- **Every global section of the chart restriction comes from a section over the chart**: the
presheaf which `AlgebraicGeometry.Space.restrictToChart` sheafifies is already a sheaf, so its
sheafification unit is bijective, and the chart cut out by the whole scheme is the chart. -/
theorem surjective_chartRestrictionTopSection (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    Function.Surjective (chartRestrictionTopSection B S hS X F V) := by
  let J := Opens.grothendieckTopology (chartScheme V)
  let : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  have hP : Presheaf.IsSheaf J (chartRestrictionPresheaf B S hS X.2 F V).presheaf :=
    (chartRestrictionSheaf B S hS X F V).isSheaf
  have := isIso_toSheafify J hP
  have hbij : Function.Bijective
      ((CategoryTheory.toSheafify J (chartRestrictionPresheaf B S hS X.2 F V).presheaf).app
        (op ⊤)) :=
    ConcreteCategory.bijective_of_isIso
      ((CategoryTheory.toSheafify J (chartRestrictionPresheaf B S hS X.2 F V).presheaf).app
        (op ⊤))
  intro t
  obtain ⟨⟨s⟩, hs⟩ := hbij.2 t
  refine ⟨F.val.map (inv (chartOpensTopHom B S hS X V)).op s, ?_⟩
  have e : F.val.map (chartOpensTopHom B S hS X V).op
      (F.val.map (inv (chartOpensTopHom B S hS X V)).op s) = s := by
    have hh : (inv (chartOpensTopHom B S hS X V)).op ≫ (chartOpensTopHom B S hS X V).op =
        𝟙 _ := by
      rw [← op_comp, IsIso.hom_inv_id, op_id]
    exact (PresheafOfModules.map_comp_apply F.val (inv (chartOpensTopHom B S hS X V)).op
      (chartOpensTopHom B S hS X V).op s).symm.trans
      ((PresheafOfModules.congr_map_apply F.val hh s).trans
        (ConcreteCategory.congr_hom (F.val.presheaf.map_id _) s))
  change (CategoryTheory.toSheafify J (chartRestrictionPresheaf B S hS X.2 F V).presheaf).app
    (op ⊤) (ULift.up (F.val.map (chartOpensTopHom B S hS X V).op
      (F.val.map (inv (chartOpensTopHom B S hS X V)).op s))) = t
  rwa [e]

/-- The Zariski germ, at the point under the chosen lift of a geometric point, of the global
section attached to a section over the chart is the germ of the section over the whole scheme
of the chart. -/
theorem chartZariskiSectionGerm_top {x : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood x)
    (F : Modules.{u, u} B S hS X.1 X.2) (σ : F.val.obj (op N.chart)) :
    Stacks.moduleStalkLargeGerm (chartZariskiPoint B S hS X.1 N) (chartZariskiSheaf B S hS N)
        (restrictToChart B S hS X.2 F N.chart) ⊤ ⟨⟨trivial⟩⟩
        (chartRestrictionTopSection B S hS X F N.chart σ) =
      chartZariskiSectionGerm B S hS X.2 N F ⊤ trivial
        (F.val.map (chartOpensTopHom B S hS X N.chart).op σ) :=
  rfl

/-! ### The nonvanishing criterion on the geometric stalk -/

/-- **The nonvanishing locus of a section over an étale chart, read on the geometric stalk.**
Let `F` be quasi-coherent, let `N` be a small étale neighbourhood of a geometric point `x̄` and
let `σ` be a section of `F` over its chart. The point of the chart under the lift of `x̄` lies
in the nonvanishing locus of `σ` exactly when the germ of `σ` in `F_{x̄}` is not in
`𝔪_{x̄} F_{x̄}`.

The Zariski stalk `(F|_V)_v` base changes to `F_{x̄}` (Stacks 05VP,
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`) along the local homomorphism
`𝒪_{V, v} ⟶ 𝒪_{X, x̄}`, carrying germs to germs, and membership in `𝔪 M` is detected after a
local base change (`ModuleCat.one_tmul_mem_maximalIdeal_smul_top_iff`). -/
theorem mem_nonvanishingLocus_chartRestrictionTopSection_iff {x : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (σ : F.val.obj (op N.chart)) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 x
    chartPoint B S hS X.1 N ∈ Stacks.Ample.nonvanishingLocus
        (chartRestrictionSchemeModule B S hS X F N.chart)
        (chartRestrictionTopSection B S hS X F N.chart σ) ↔
      geometricModuleStalkGerm B S hS X x F N σ ∉
        (IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS X.1 x) • ⊤ :
          Submodule ↥(etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x F)) := by
  let : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  have := isLocalHom_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N
  set s₀ := F.val.map (chartOpensTopHom B S hS X N.chart).op σ with hs₀
  set w := chartZariskiSectionGerm B S hS X.2 N F ⊤ trivial s₀ with hw
  -- the Zariski stalk at the point of the site, read as the ordinary stalk
  let e' : chartZariskiModuleStalk B S hS X.1 X.2 N F ≃ₗ[chartLocalRing B S hS X.1 N]
      TopCat.Presheaf.stalk (C := Ab.{u}) (chartRestrictionSchemeModule B S hS X F N.chart).presheaf
        (chartPoint B S hS X.1 N) :=
    { toFun := chartZariskiStalkAddEquiv B S hS X.2 N F
      invFun := (chartZariskiStalkAddEquiv B S hS X.2 N F).symm
      map_add' := map_add (chartZariskiStalkAddEquiv B S hS X.2 N F)
      map_smul' := chartZariskiStalkAddEquiv_smul B S hS X.2 N F
      left_inv := (chartZariskiStalkAddEquiv B S hS X.2 N F).left_inv
      right_inv := (chartZariskiStalkAddEquiv B S hS X.2 N F).right_inv }
  -- the germ of the global section is the image of `w` in the ordinary stalk
  have hgerm : ((chartRestrictionSchemeModule B S hS X F N.chart).presheaf.Γgerm
      (chartPoint B S hS X.1 N)).hom (chartRestrictionTopSection B S hS X F N.chart σ) = e' w :=
    (chartZariskiStalkAddEquiv_germ B S hS X.2 N F ⊤ trivial
      (chartRestrictionTopSection B S hS X F N.chart σ)).symm
  -- the geometric germ is the comparison of Stacks 05VP applied to `1 ⊗ w`
  have hcmp : chartStalkTensorComparison B S hS X.2 N F
      ((1 : ↥(etaleLocalRing B S hS X.1 x)) ⊗ₜ[↥(chartLocalRing B S hS X.1 N),
        chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N] w) =
      geometricModuleStalkGerm B S hS X x F N σ :=
    (chartStalkTensorComparison_germ B S hS X.2 N F ⊤ trivial s₀).trans
      (geometricModuleStalkGerm_map B S hS X x F (chartOpenNeighborhoodHom B S hS N ⊤ trivial) σ)
  have := isIso_chartStalkTensorComparison B S hS X.2 N F
  let c := (asIso (chartStalkTensorComparison B S hS X.2 N F)).toLinearEquiv
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, hgerm, ← hcmp]
  exact not_congr ((LinearEquiv.mem_smul_top_iff e' _ w).trans
    ((ModuleCat.one_tmul_mem_maximalIdeal_smul_top_iff
      (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N) w).symm.trans
      (LinearEquiv.mem_smul_top_iff c _ _).symm))

/-! ### Stability under morphisms of étale charts -/

/-- The small étale neighbourhood obtained by pushing a neighbourhood forward along a morphism
of étale charts. -/
noncomputable def SmallEtaleNeighborhood.push {x : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood x) {W : SmallEtale B S hS X.1} (h : N.chart ⟶ W) :
    SmallEtaleNeighborhood x where
  chart := W
  point := N.point ≫ (SmallEtale.toOver B S hS X.1).map h
  point_comp := (congrArg (fun k : yoneda.obj N.chart.obj.left ⟶ X.1 => k.app _ N.point)
    (CostructuredArrow.w h.hom)).trans N.point_comp

/-- The morphism of small étale neighbourhoods into the pushed neighbourhood. -/
noncomputable def SmallEtaleNeighborhood.toPush {x : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood x) {W : SmallEtale B S hS X.1} (h : N.chart ⟶ W) :
    N ⟶ SmallEtaleNeighborhood.push B S hS X N h where
  hom := h
  point_comp := rfl

/-- The point of the pushed neighbourhood is the image of the point of the neighbourhood. -/
theorem chartPoint_push {x : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood x)
    {W : SmallEtale B S hS X.1} (h : N.chart ⟶ W) :
    chartPoint B S hS X.1 (SmallEtaleNeighborhood.push B S hS X N h) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h)).base
        (chartPoint B S hS X.1 N) := by
  change ((BigFppfOver.toScheme B S hS).map (N.point ≫ _)).base _ = _
  rw [Functor.map_comp]
  rfl

/-- Every point of the scheme of an étale chart is the point of a small étale neighbourhood
obtained from a geometric representative. -/
private theorem exists_chartPoint_ofChartGeometricPoint_eq (V : SmallEtale B S hS X.1)
    (z : chartScheme V) :
    ∃ ybar, chartPoint B S hS X.1
      (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X V ybar) = z := by
  obtain ⟨ybar, hybar⟩ := exists_geometricRepresentative B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
    ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj V)).symm z)
  refine ⟨ybar, ?_⟩
  rw [chartPoint_ofChartGeometricPoint, hybar]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj V)).apply_symm_apply z

/-- **The nonvanishing locus of a restricted section is the inverse image of the nonvanishing
locus.** For a quasi-coherent `F`, a morphism `h : Z ⟶ W` of étale charts and a section `σ` of
`F` over `W`, a point `z` of the scheme of `Z` lies in the nonvanishing locus of the restriction
of `σ` to `Z` exactly when its image lies in the nonvanishing locus of `σ`. Both are read on the
geometric stalk at one geometric point over `z`
(`AlgebraicGeometry.Space.mem_nonvanishingLocus_chartRestrictionTopSection_iff`), where the two
germs agree. -/
theorem mem_nonvanishingLocus_chartRestrictionTopSection_map_iff
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] {Z W : SmallEtale B S hS X.1}
    (h : Z ⟶ W) (σ : F.val.obj (op W)) (z : chartScheme Z) :
    z ∈ Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F Z)
        (chartRestrictionTopSection B S hS X F Z (F.val.map h.op σ)) ↔
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h)).base z ∈
        Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F W)
          (chartRestrictionTopSection B S hS X F W σ) := by
  obtain ⟨ybar, hz⟩ := exists_chartPoint_ofChartGeometricPoint_eq B S hS X Z z
  set N := SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X Z ybar
  have h1 := mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X N F
    (F.val.map h.op σ)
  have h2 := mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X
    (SmallEtaleNeighborhood.push B S hS X N h) F σ
  have hz2 : chartPoint B S hS X.1 (SmallEtaleNeighborhood.push B S hS X N h) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map h)).base z := by
    rw [← hz]
    exact chartPoint_push B S hS X N h
  rw [hz] at h1
  rw [hz2] at h2
  refine h1.trans (Iff.trans ?_ h2.symm)
  exact Iff.of_eq (congrArg (fun t => t ∉ _)
    (geometricModuleStalkGerm_map B S hS X _ F (SmallEtaleNeighborhood.toPush B S hS X N h) σ))

/-- Every point of the scheme of an étale chart is the point of a small étale neighbourhood whose
chart is that chart, and a section lies in the nonvanishing locus there exactly when its germ at
the geometric point of that neighbourhood is not in `𝔪_{x̄} F_{x̄}`. -/
theorem exists_mem_nonvanishingLocus_chartRestrictionTopSection_iff
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS X.1)
    (z : chartScheme V) :
    ∃ (x : GeometricPoint B S hS X.1) (N : SmallEtaleNeighborhood x) (e : N.chart = V),
      letI : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 x
      ∀ σ : F.val.obj (op V),
        z ∈ Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
            (chartRestrictionTopSection B S hS X F V σ) ↔
          geometricModuleStalkGerm B S hS X x F N (e ▸ σ) ∉
            (IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS X.1 x) • ⊤ :
              Submodule ↥(etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x F)) := by
  obtain ⟨ybar, hz⟩ := exists_chartPoint_ofChartGeometricPoint_eq B S hS X V z
  refine ⟨_, SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X V ybar, rfl, fun σ => ?_⟩
  have h1 := mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X
    (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS X V ybar) F σ
  rwa [hz] at h1

/-- **A sum of sections can only fail to vanish where one of the summands does**, on an étale
chart. -/
theorem nonvanishingLocus_chartRestrictionTopSection_add_subset
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS X.1)
    (σ τ : F.val.obj (op V)) :
    Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V (σ + τ)) ⊆
      Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
          (chartRestrictionTopSection B S hS X F V σ) ∪
        Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
          (chartRestrictionTopSection B S hS X F V τ) := by
  intro z hz
  obtain ⟨x, N, rfl, hN⟩ := exists_mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X F
    V z
  rw [hN] at hz
  by_contra hc
  simp only [Set.mem_union, not_or, hN, not_not] at hc
  exact hz (map_add (geometricModuleStalkGerm B S hS X x F N) σ τ ▸ Submodule.add_mem _ hc.1 hc.2)

/-- **A multiple of a section can only fail to vanish where the section does**, on an étale
chart. -/
theorem nonvanishingLocus_chartRestrictionTopSection_smul_subset
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS X.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
      (op V)) (σ : F.val.obj (op V)) :
    Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V (r • σ)) ⊆
      Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V σ) := by
  intro z hz
  obtain ⟨x, N, rfl, hN⟩ := exists_mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X F
    V z
  rw [hN] at hz ⊢
  intro hc
  exact hz (geometricModuleStalkGerm_smul B S hS X x F N r σ ▸ Submodule.smul_mem _ _ hc)

/-- The zero section vanishes everywhere, on an étale chart. -/
theorem nonvanishingLocus_chartRestrictionTopSection_zero
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS X.1) :
    Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V 0) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨x, N, rfl, hN⟩ := exists_mem_nonvanishingLocus_chartRestrictionTopSection_iff B S hS X F
    V z
  rw [hN] at hz
  exact hz (map_zero (geometricModuleStalkGerm B S hS X x F N) ▸ Submodule.zero_mem _)

/-- **A linear combination of sections can only fail to vanish where one of them does**, on an
étale chart. -/
theorem nonvanishingLocus_chartRestrictionTopSection_sum_subset
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (V : SmallEtale B S hS X.1)
    {ι : Type*} (s : Finset ι)
    (r : ι →
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
        (op V)) (σ : ι → F.val.obj (op V)) :
    Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V (∑ i ∈ s, r i • σ i)) ⊆
      ⋃ i ∈ s, Stacks.Ample.nonvanishingLocus (chartRestrictionSchemeModule B S hS X F V)
        (chartRestrictionTopSection B S hS X F V (σ i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, nonvanishingLocus_chartRestrictionTopSection_zero]
    exact Set.empty_subset _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (nonvanishingLocus_chartRestrictionTopSection_add_subset B S hS X F V _ _).trans ?_
    rw [Finset.set_biUnion_insert]
    exact Set.union_subset_union
      (nonvanishingLocus_chartRestrictionTopSection_smul_subset B S hS X F V (r i) (σ i)) ih

end AlgebraicGeometry.Space

end
