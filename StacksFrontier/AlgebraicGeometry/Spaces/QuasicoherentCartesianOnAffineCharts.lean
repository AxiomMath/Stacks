module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# A quasi-coherent `𝒪_F`-module is cartesian on affine charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  A
quasi-coherent `𝒪_F`-module is cartesian on affine charts: for every morphism of affine étale
charts the base change comparison `AlgebraicGeometry.Space.sectionsBaseChange` is bijective.
Together with the converse this gives the chart criterion for quasi-coherence on the small étale
site of `F`.  The results are about a single module over an algebraic space; they are not the
equivalence of categories `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)` that Proposition 03DX (2) states for a
scheme.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleChartRings` is the presheaf of rings of regular functions on
  the affine étale charts of `F`, at the universe of the schemes.
* `Stacks.SheafOfModules.restrictionAlongContinuous` is restriction of sheaves of modules along a
  continuous functor of sites, over the restricted structure sheaf.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_uliftForPresentation`: bijectivity
  of the base change comparison descends from the universe lift of the sections.
* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_restriction`: the base change
  comparison of a restricted module along a morphism of the subsite is the base change comparison
  of the module itself.
* `AlgebraicGeometry.Space.isSheaf_of_cartesian_affineEtaleChart` and
  `AlgebraicGeometry.Space.isSheaf_of_cartesian_affineEtaleChart_over`: a cartesian presheaf of
  modules over `affineEtaleChartRings`, or over its restriction to a slice, is a sheaf.
* `AlgebraicGeometry.Space.isIso_restrictionBaseChange_affineEtaleChart_of_isQuasicoherentOnSite`:
  a quasi-coherent sheaf of modules over the chart rings is cartesian.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_uliftForPresentation_iff` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_uliftForPresentation_iff`: raising the
  universe of the sections of an `𝒪_F`-module changes no base change comparison.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse`: a
  quasi-coherent `𝒪_F`-module is cartesian on affine charts, at any universe of module sections;
  `AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite` and
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` are the case of
  sections in the universe of the schemes.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse`: an
  `𝒪_F`-module is quasi-coherent if and only if it is cartesian on affine charts, at any universe
  of module sections, and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts` at the universe of
  the schemes.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Restriction of sheaves of modules along a continuous functor of sites, over the restriction of
the structure sheaf, with the coefficient ring sheaf presented as a presheaf of commutative rings
together with its sheaf condition. -/
noncomputable abbrev restrictionAlongContinuous (G : D ⥤ C) [G.IsContinuous K J]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{r})
    (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    SheafOfModules.{max m r}
        (⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩ : Sheaf J RingCat.{r}) ⥤
      SheafOfModules.{max m r}
        ((G.sheafPushforwardContinuous RingCat.{r} K J).obj
          (⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩ : Sheaf J RingCat.{r})) :=
  _root_.SheafOfModules.pushforward (𝟙 _)

end Stacks.SheafOfModules

namespace Stacks.PresheafOfModules

/-- A map is bijective if and only if its conjugate by bijections is. -/
private theorem bijective_iff_of_comp_eq {α β γ δ : Type*} {φ : α → β} {ψ : γ → δ} {e : α → γ}
    {d : β → δ} (he : Function.Bijective e) (hd : Function.Bijective d) (h : d ∘ φ = ψ ∘ e) :
    Function.Bijective φ ↔ Function.Bijective ψ := by
  rw [← Function.Bijective.of_comp_iff _ he, ← h]
  exact (Function.Bijective.of_comp_iff' hd _).symm

/-- **Bijectivity of the base change comparison descends from the universe lift of the
sections**: if the base change comparison of `uliftForPresentation N` along `f` is an
isomorphism, the base change comparison of `N` along `f` is bijective. -/
theorem bijective_restrictionBaseChange_of_uliftForPresentation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Cᵒᵖ ⥤ CommRingCat.{r})
    (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat))
    (N : SheafOfModules.{max m r}
      (⟨R ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{r}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : IsIso (restrictionBaseChange.{u, v, r, max t m}
      (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max m r, t} N).val f)) :
    Function.Bijective (restrictionBaseChange.{u, v, r, m} N.val f) := by
  have hb : Function.Bijective (restrictionBaseChange.{u, v, r, max t m}
      (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max m r, t} N).val f) :=
    ConcreteCategory.bijective_of_isIso _
  let _ : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let d : ULift.{t} (N.val.obj Y) ≃ₗ[R.obj Y] (N.val.obj Y) := ULift.moduleEquiv
  let e : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (N.val.obj X)) ≃ₗ[R.obj Y]
      TensorProduct (R.obj X) (R.obj Y) (N.val.obj X) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R.obj Y) (R.obj Y))
      ULift.moduleEquiv
  let L₁ : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (N.val.obj X)) →ₗ[R.obj Y]
      (N.val.obj Y) :=
    d.toLinearMap ∘ₗ (restrictionBaseChange.{u, v, r, max t m}
      (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max m r, t} N).val f).hom
  let L₂ : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (N.val.obj X)) →ₗ[R.obj Y]
      (N.val.obj Y) :=
    (restrictionBaseChange.{u, v, r, m} N.val f).hom ∘ₗ e.toLinearMap
  have key : L₁ = L₂ := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b x =>
      refine Eq.trans ?_ (restrictionBaseChange_tmul N.val f b (ULift.down x)).symm
      refine (congrArg d (restrictionBaseChange_tmul.{u, v, r, max t m}
        (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max m r, t} N).val f b x)).trans ?_
      refine (map_smul d b _).trans ?_
      rfl
  exact (bijective_iff_of_comp_eq e.bijective d.bijective (congrArg (⇑) key)).1 hb

/-- **The base change comparison of a restricted module is the base change comparison of the
module itself**: if the base change comparison of the restriction of `M` along `G` is bijective
over `f`, the base change comparison of `M` is bijective over `G.map f`. -/
theorem bijective_restrictionBaseChange_of_restriction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (G : D ⥤ C)
    [G.IsContinuous K J]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{r})
    (h𝒪 : Presheaf.IsSheaf J (𝒪 ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m r}
      (⟨𝒪 ⋙ forget₂ CommRingCat RingCat, h𝒪⟩ : Sheaf J RingCat.{r}))
    {X Y : D} (f : X ⟶ Y)
    (h : Function.Bijective (restrictionBaseChange.{u₂, v₂, r, m} (R := G.op ⋙ 𝒪)
      ((Stacks.SheafOfModules.restrictionAlongContinuous.{r, m, u₁, v₁, u₂, v₂}
        (K := K) G 𝒪 h𝒪).obj M).val f.op)) :
    Function.Bijective (restrictionBaseChange.{u₁, v₁, r, m} (R := 𝒪) M.val (G.map f).op) := h

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

open Stacks.PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The rings of the affine étale charts -/

/-- The presheaf of rings of regular functions on the affine étale charts of `F`, at the universe
of the schemes: the restriction to the affine charts of the structure presheaf of the small étale
site. -/
abbrev affineEtaleChartRings : (AffineEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineEtale.inclusion B S hS F).op ⋙ structurePresheaf B S hS F

/-- The chart rings are flat along every morphism of the affine étale site. -/
theorem flat_affineEtaleChartRings_map {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    ((affineEtaleChartRings B S hS F).map f.op).hom.Flat := by
  change (((AffineEtale.toScheme B S hS F).map f).appTop).hom.Flat
  exact HasRingHomProperty.appTop (P := @Flat) _ (AffineEtale.flat_toScheme_map B S hS F f)

/-- A finite flat covering family of affine étale charts is faithfully flat on chart rings. -/
theorem faithfullyFlat_pi_affineEtaleChartRings {U : AffineEtale B S hS F}
    {I : Type v} [Finite I] (V : I → AffineEtale B S hS F) (g : ∀ i, V i ⟶ U)
    (hcover : ∀ x, ∃ i, x ∈ Set.range ((AffineEtale.toScheme B S hS F).map (g i)))
    (hflat : ∀ i, Flat ((AffineEtale.toScheme B S hS F).map (g i))) :
    (RingHom.pi
      (fun i => ((affineEtaleChartRings B S hS F).map (g i).op).hom)).FaithfullyFlat := by
  change (RingHom.pi
    (fun i => (((AffineEtale.toScheme B S hS F).map (g i)).appTop).hom)).FaithfullyFlat
  exact AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop
    (fun i => (AffineEtale.toScheme B S hS F).obj (V i))
    (fun i => (AffineEtale.toScheme B S hS F).map (g i)) hcover

/-- A fibre product square of affine étale charts becomes a pushout square of chart rings. -/
theorem isPushout_affineEtaleChartRings
    {X Y Z P : AffineEtale B S hS F}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout ((affineEtaleChartRings B S hS F).map a.op)
      ((affineEtaleChartRings B S hS F).map b.op)
      ((affineEtaleChartRings B S hS F).map fst.op)
      ((affineEtaleChartRings B S hS F).map snd.op) := by
  change IsPushout (((AffineEtale.toScheme B S hS F).map a).appTop)
    (((AffineEtale.toScheme B S hS F).map b).appTop)
    (((AffineEtale.toScheme B S hS F).map fst).appTop)
    (((AffineEtale.toScheme B S hS F).map snd).appTop)
  exact isPushout_appTop_of_isPullback
    (Functor.map_isPullback (AffineEtale.toScheme B S hS F) h)

/-- A fibre product square of a slice of the affine étale site becomes a pushout square of the
restricted chart rings. -/
theorem isPushout_affineEtaleChartRings_over (U : AffineEtale B S hS F)
    {X Y Z P : Over U}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout (((Over.forget U).op ⋙ affineEtaleChartRings B S hS F).map a.op)
      (((Over.forget U).op ⋙ affineEtaleChartRings B S hS F).map b.op)
      (((Over.forget U).op ⋙ affineEtaleChartRings B S hS F).map fst.op)
      (((Over.forget U).op ⋙ affineEtaleChartRings B S hS F).map snd.op) := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ AffineEtale.toScheme B S hS F) := by
    apply comp_preservesLimitsOfShape
  have _ : IsAffine ((Over.forget U ⋙ AffineEtale.toScheme B S hS F).obj X) :=
    AffineEtale.isAffine_toScheme B S hS F X.left
  have _ : IsAffine ((Over.forget U ⋙ AffineEtale.toScheme B S hS F).obj Y) :=
    AffineEtale.isAffine_toScheme B S hS F Y.left
  have _ : IsAffine ((Over.forget U ⋙ AffineEtale.toScheme B S hS F).obj Z) :=
    AffineEtale.isAffine_toScheme B S hS F Z.left
  change IsPushout (((Over.forget U ⋙ AffineEtale.toScheme B S hS F).map a).appTop)
    (((Over.forget U ⋙ AffineEtale.toScheme B S hS F).map b).appTop)
    (((Over.forget U ⋙ AffineEtale.toScheme B S hS F).map fst).appTop)
    (((Over.forget U ⋙ AffineEtale.toScheme B S hS F).map snd).appTop)
  exact isPushout_appTop_of_isPullback
    (Functor.map_isPullback (Over.forget U ⋙ AffineEtale.toScheme B S hS F) h)

/-! ### A cartesian module over the chart rings is a sheaf -/

/-- **A cartesian presheaf of modules over the chart rings of the affine étale site of `F` is a
sheaf.** -/
theorem isSheaf_of_cartesian_affineEtaleChart
    (M : PresheafOfModules.{max m (u + 1)}
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (AffineEtale B S hS F)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f)) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf := by
  refine isSheaf_of_cartesian_of_flat_covers.{u, u + 1, u, m, u, u + 1}
    (AffineEtale.toScheme B S hS F) (affineEtaleChartRings B S hS F) ?_ ?_ M hM
    (AffineEtale.precoverage B S hS F) ?_
  · intro U E _ hE
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS F))).mp hE
    exact faithfullyFlat_pi_affineEtaleChartRings B S hS F E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineEtaleChartRings B S hS F h
  · intro U P hP
    obtain ⟨E, rfl, hE⟩ := hP
    refine ⟨E, rfl, hE.2, ?_⟩
    obtain ⟨hs, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (AffineEtale.toScheme B S hS F))).mp hE.1.2
    exact (Scheme.presieve₀_mem_precoverage_iff _).mpr
      ⟨hs, fun i => by have := het i; infer_instance⟩

/-- **A cartesian presheaf of modules over the chart rings of a slice of the affine étale site of
`F` is a sheaf.** -/
theorem isSheaf_of_cartesian_affineEtaleChart_over (U : AffineEtale B S hS F)
    (M : PresheafOfModules.{max m (u + 1)}
      ((Over.forget U).op ⋙ affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
        (R := (Over.forget U).op ⋙ affineEtaleChartRings B S hS F) M f)) :
    Presheaf.IsSheaf ((AffineEtale.topology B S hS F).over U) M.presheaf := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ AffineEtale.toScheme B S hS F) := by
    apply comp_preservesLimitsOfShape
  refine isSheaf_of_cartesian_of_flat_refinements.{u, u + 1, u, m, u}
    (Over.forget U ⋙ AffineEtale.toScheme B S hS F)
    ((Over.forget U).op ⋙ affineEtaleChartRings B S hS F) ?_ ?_ M hM _ ?_
  · intro V E _ hE
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (Over.forget U ⋙ AffineEtale.toScheme B S hS F))).mp hE
    exact faithfullyFlat_pi_affineEtaleChartRings B S hS F (fun k => (E.X k).left)
      (fun k => (E.f k).left) hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineEtaleChartRings_over B S hS F U h
  · intro V T hT
    exact Stacks.Sites.exists_finite_flat_refinement_over
      (AffineEtale.toScheme B S hS F) (AffineEtale.precoverage B S hS F)
      (affineEtale_covering_finite_flat B S hS F) U T hT

/-! ### Quasi-coherent modules over the chart rings are cartesian -/

/-- A global presentation on a slice of the affine étale site makes the module cartesian there,
for the chart rings. -/
theorem isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation
    (hRing : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf (AffineEtale.topology B S hS F) RingCat.{u}))
    (U : AffineEtale B S hS F) (hM : (M.over U).HasGlobalPresentation)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
      (R := (Over.forget U).op ⋙ affineEtaleChartRings B S hS F) (M.over U).val f) := by
  apply isIso_restrictionBaseChange_of_hasGlobalPresentation.{u + 1, u, u, m}
    ((Over.forget U).op ⋙ affineEtaleChartRings B S hS F)
    (Sheaf.over (⟨affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
      Sheaf (AffineEtale.topology B S hS F) RingCat.{u}) U).property
    (fun N hN => isSheaf_of_cartesian_affineEtaleChart_over B S hS F U N hN)
    (M.over U) hM f

/-- Being cartesian over the chart rings is local on a covering of the affine étale site of
`F`. -/
theorem isIso_restrictionBaseChange_affineEtaleChart_of_cover
    (M : PresheafOfModules.{max m (u + 1)}
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf)
    {V : AffineEtale B S hS F} {I : Type (u + 1)} [Finite I]
    (W : I → AffineEtale B S hS F) (gw : ∀ i, W i ⟶ V)
    (hcover : Sieve.ofArrows W gw ∈ AffineEtale.topology B S hS F V)
    (hcart : ∀ (i : I) {X Y : AffineEtale B S hS F} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M a.op))
    {U : AffineEtale B S hS F} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f.op) := by
  classical
  have hsT : Presieve.IsSheaf (AffineEtale.topology B S hS F)
      (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (AffineEtale.topology B S hS F)
      M.presheaf (forget AddCommGrpCat)).mp hs
  have hcoverU : Sieve.ofArrows (fun i => pullback f (gw i))
      (fun i => pullback.fst f (gw i)) ∈ AffineEtale.topology B S hS F U := by
    refine (AffineEtale.topology B S hS F).superset_covering ?_
      ((AffineEtale.topology B S hS F).pullback_stable f hcover)
    intro Z h hh
    obtain ⟨Y, g₁, g₂, ⟨i⟩, hg⟩ := hh
    have hmem := (Sieve.ofArrows (fun i => pullback f (gw i))
        (fun i => pullback.fst f (gw i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  have hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows W gw) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcover)
  have hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback f (gw i)) (fun i => pullback.fst f (gw i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hsT _ hcoverU)
  exact isIso_restrictionBaseChange_of_cover M f W gw
    (flat_affineEtaleChartRings_map B S hS F f) hsfV hsfU
    (fun i => isPushout_affineEtaleChartRings B S hS F
      (IsPullback.of_hasPullback f (gw i)))
    (fun c => isPushout_affineEtaleChartRings B S hS F
      (IsPullback.of_hasPullback f _))
    (fun i => hcart i (pullback.snd f (gw i)) (𝟙 _) (pullback.snd f (gw i)) (by simp))
    (fun c => hcart c.1 (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1) ≫
      pullback.fst (gw c.1) (gw c.2)) (pullback.fst (gw c.1) (gw c.2))
      (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1)) rfl)

/-- A quasi-coherent sheaf of modules over the rings of regular functions on the affine étale
charts of `F` is cartesian. -/
theorem isIso_restrictionBaseChange_affineEtaleChart_of_isQuasicoherentOnSite
    (hRing : Presheaf.IsSheaf (AffineEtale.topology B S hS F)
      (affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨affineEtaleChartRings B S hS F ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf (AffineEtale.topology B S hS F) RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite)
    {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val f.op) := by
  classical
  obtain ⟨I, hI, W, g, hcover, hpres⟩ :=
    Stacks.SheafOfModules.exists_finite_globalPresentation_cover.{u + 1, u, u, m}
      (AffineEtale.precoverage B S hS F)
      (fun P hP => (affineEtale_covering_finite_flat B S hS F P hP).1) M hM V
  have hcart (i : I) {X Y : (Over (W i))ᵒᵖ} (a : X ⟶ Y) :=
    isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation B S hS F hRing M (W i)
      (hpres i) a
  have hcart' : ∀ (i : I) {X Y : AffineEtale B S hS F} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val a.op) := by
    intro i X Y x y a ha
    exact hcart i (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha))
  exact isIso_restrictionBaseChange_affineEtaleChart_of_cover B S hS F M.val M.isSheaf W g
    hcover hcart' f

/-! ### Raising the universe of the sections -/

/-- **Raising the universe of the sections of an `𝒪_F`-module changes no base change
comparison**: over a morphism of étale charts, the base change comparison of
`SheafOfModules.uliftForPresentation G` is bijective if and only if that of `G` is. -/
theorem bijective_sectionsBaseChange_uliftForPresentation_iff (G : Modules.{u, m} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    Function.Bijective
        (sectionsBaseChange (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, m, t} G) f) ↔
      Function.Bijective (sectionsBaseChange G f) := by
  let _ := chartAlgebra (hF := hF) f
  let d : ULift.{t} (G.val.obj (op V)) ≃ₗ[chartRing B S hS F hF V] (G.val.obj (op V)) :=
    ULift.moduleEquiv
  let e : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (ULift.{t} (G.val.obj (op U))) ≃ₗ[chartRing B S hS F hF V]
      TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V) (G.val.obj (op U)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) ULift.moduleEquiv
  have key : d.toLinearMap ∘ₗ sectionsBaseChange
      (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, m, t} G) f =
        sectionsBaseChange G f ∘ₗ e.toLinearMap := by
    let _ := chartSectionsModule G f
    have : IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (G.val.obj (op V)) := chartSections_isScalarTower G f
    refine TensorProduct.AlgebraTensorModule.ext fun b x => ?_
    refine (congrArg d (chartBaseChange_tmul _ f b x)).trans ?_
    refine (map_smul d b _).trans ?_
    exact (chartBaseChange_tmul G f b (ULift.down x)).symm
  exact bijective_iff_of_comp_eq e.bijective d.bijective (congrArg (⇑) key)

/-- **Raising the universe of the sections of an `𝒪_F`-module preserves and reflects being
cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_uliftForPresentation_iff (G : Modules.{u, m} B S hS F hF) :
    IsCartesianOnAffineCharts
        (_root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, m, t} G) ↔
      IsCartesianOnAffineCharts G :=
  forall₂_congr fun _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    forall_congr' fun f => bijective_sectionsBaseChange_uliftForPresentation_iff B S hS F hF G f

/-! ### The base change comparison as an adjoint transpose -/

/-- **The base change comparison of an `𝒪_F`-module is the adjoint transpose of its restriction
map.**  Over a morphism `f : V ⟶ U` of étale charts, `AlgebraicGeometry.Space.sectionsBaseChange`
agrees elementwise with `Stacks.PresheafOfModules.restrictionBaseChange` of the underlying
presheaf of modules along `f.op`: both send `b ⊗ x` to `b` acting on the restriction of `x`. -/
theorem sectionsBaseChange_apply_eq_restrictionBaseChange (G : Modules.{u, max u m} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (z : letI := chartAlgebra (hF := hF) f
      TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V) (G.val.obj (op U))) :
    sectionsBaseChange G f z =
      restrictionBaseChange.{u + 1, u, u, m} (R := structurePresheaf B S hS F) G.val f.op z := by
  have _ := chartAlgebra (hF := hF) f
  have _ := chartSectionsModule G f
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((map_add _ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add _ x y).symm
  | tmul b x =>
    refine (chartBaseChange_tmul G f b x).trans ?_
    exact (restrictionBaseChange_tmul.{u + 1, u, u, m} G.val f.op b x).symm

/-- The base change comparison of an `𝒪_F`-module over a morphism of étale charts is bijective
exactly when the adjoint transpose `Stacks.PresheafOfModules.restrictionBaseChange` of its
restriction map is an isomorphism. -/
theorem bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange
    (G : Modules.{u, max u m} B S hS F hF) {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    Function.Bijective (sectionsBaseChange G f) ↔
      IsIso (restrictionBaseChange.{u + 1, u, u, m} (R := structurePresheaf B S hS F)
        G.val f.op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Iff.of_eq (congrArg Function.Bijective
    (funext (sectionsBaseChange_apply_eq_restrictionBaseChange B S hS F hF G f)))

/-! ### The chart criterion for quasi-coherence -/

/-- **The base change comparison of a quasi-coherent `𝒪_F`-module over a morphism of affine étale
charts is bijective**, at an arbitrary universe of module sections. -/
theorem bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse
    (G : Modules.{u, m} B S hS F hF) (hG : G.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    Function.Bijective (sectionsBaseChange G f) := by
  have hds : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hcc : (AffineEtale.inclusion B S hS F).IsCocontinuous
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).1
  have hover : ∀ X : AffineEtale B S hS F,
      (Over.post (X := X) (AffineEtale.inclusion B S hS F)).IsContinuous
        ((AffineEtale.topology B S hS F).over X)
        ((SmallEtale.topology B S hS F).over ((AffineEtale.inclusion B S hS F).obj X)) :=
    fun X => by
      have _ := Stacks.Sites.overPost_isDenseSubsite
        (J := AffineEtale.topology B S hS F) (K := SmallEtale.topology B S hS F)
        (AffineEtale.inclusion B S hS F) X
      infer_instance
  set G' : Modules.{u, max (u + 1) m} B S hS F hF :=
    _root_.SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} G with hG'
  have h₀ : G'.IsQuasicoherentOnSite :=
    _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation hG
  have h₁ := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := SmallEtale.topology B S hS F) (K := AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) G' h₀
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation h₁
  have h₃ := isIso_restrictionBaseChange_affineEtaleChart_of_isQuasicoherentOnSite.{u, m}
    B S hS F _ _ h₂
    ((AffineEtale.inclusion B S hS F).preimage
      (X := (⟨V, hV⟩ : AffineEtale B S hS F)) (Y := ⟨U, hU⟩) f)
  have h₄ := bijective_restrictionBaseChange_of_uliftForPresentation.{u + 1, u, u, max (u + 1) m}
    (affineEtaleChartRings B S hS F) _ _ _ h₃
  have h₅ := bijective_restrictionBaseChange_of_restriction
    (J := SmallEtale.topology B S hS F) (K := AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (structurePresheaf B S hS F) _ G' _ h₄
  rw [(AffineEtale.inclusion B S hS F).map_preimage] at h₅
  have _ := chartAlgebra (hF := hF) f
  have _ := chartSectionsModule G' f
  have key : ∀ z, sectionsBaseChange G' f z =
      restrictionBaseChange.{u + 1, u, u, max (u + 1) m} (R := structurePresheaf B S hS F)
        G'.val f.op z :=
    sectionsBaseChange_apply_eq_restrictionBaseChange.{u, max (u + 1) m} B S hS F hF G' f
  rw [← bijective_sectionsBaseChange_uliftForPresentation_iff.{u, m, u + 1} B S hS F hF G f]
  rw [show (sectionsBaseChange G' f : _ → _) = _ from funext key]
  exact h₅

/-- **The base change comparison of a quasi-coherent `𝒪_F`-module over a morphism of affine étale
charts is bijective**, for module sections in the universe of the schemes. -/
theorem bijective_sectionsBaseChange_of_isQuasicoherentOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : G.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    Function.Bijective (sectionsBaseChange G f) :=
  bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse B S hS F hF G hG hU hV f

/-- **The forward half of the chart criterion, at an arbitrary universe of module sections**: a
quasi-coherent `𝒪_F`-module on the small étale site of an algebraic space is cartesian on affine
charts. -/
theorem isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse
    (G : Modules.{u, m} B S hS F hF) (hG : G.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts G := fun _ _ hU hV f =>
  bijective_sectionsBaseChange_of_isQuasicoherentOnSite_anyUniverse B S hS F hF G hG hU hV f

/-- **The chart criterion for quasi-coherence, at an arbitrary universe of module sections**: an
`𝒪_F`-module on the small étale site of an algebraic space is quasi-coherent if and only if it is
cartesian on affine charts. -/
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse
    (G : Modules.{u, m} B S hS F hF) :
    G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G :=
  ⟨isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse B S hS F hF G,
    isQuasicoherentOnSite_of_isCartesianOnAffineCharts_anyUniverse G⟩

/-- **The forward half of the chart criterion for quasi-coherence on the small étale site of an
algebraic space**: a quasi-coherent `𝒪_F`-module, with sections in the universe of the schemes, is
cartesian on affine charts. -/
@[stacks 03DX "quasi-coherent implies cartesian"]
theorem isCartesianOnAffineCharts_of_isQuasicoherentOnSite
    (G : Modules.{u, u} B S hS F hF) (hG : G.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts G :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite_anyUniverse B S hS F hF G hG

/-- **The chart criterion for quasi-coherence on the small étale site of an algebraic space**: an
`𝒪_F`-module, with sections in the universe of the schemes, is quasi-coherent if and only if it
is cartesian on affine charts.  The base `F` is an algebraic space, and the statement is a
criterion on a single module rather than the equivalence of categories
`QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` for a scheme `S`. -/
@[stacks 03DX "part (2)"]
theorem isQuasicoherentOnSite_iff_isCartesianOnAffineCharts
    (G : Modules.{u, u} B S hS F hF) :
    G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G :=
  isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse B S hS F hF G

end AlgebraicGeometry.Space

end
