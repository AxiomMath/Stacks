module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# A quasi-coherent module on the small étale site is cartesian between affine objects

Let `S` be a scheme contained in a big étale site `B`. For a quasi-coherent sheaf of modules `𝒢`
on the small étale site of `S` and a morphism `T ⟶ T'` of objects of that site whose underlying
schemes are affine, the base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective. This is
a step of Descent, Proposition 03DX (2) at `τ = étale`; that clause itself, an equivalence of
categories, is `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.affineChartRings` is the presheaf of rings of regular functions
  on the affine objects of the small étale site of `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.flat_affineChartRings_map`,
  `AlgebraicGeometry.SmallEtale.faithfullyFlat_pi_affineChartRings` and
  `AlgebraicGeometry.SmallEtale.isPushout_affineChartRings`: the chart rings are flat along every
  morphism, faithfully flat along a finite covering family, and turn fibre products into pushouts.
* `AlgebraicGeometry.SmallEtale.smallAffineEtale_covering_finite_flat`: the covering families of
  the small affine étale site are finite and flat on the underlying schemes.
* `AlgebraicGeometry.SmallEtale.isSheaf_of_cartesian_affineChart` and
  `AlgebraicGeometry.SmallEtale.isSheaf_of_cartesian_affineChart_over`: a cartesian presheaf of
  modules over the chart rings, or over their restriction to a slice, is a sheaf.
* `AlgebraicGeometry.SmallEtale.isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite`:
  Stacks 0H04 for the chart rings of the small affine étale site of `S`.
* `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`: a
  quasi-coherent sheaf of modules on the small étale site of a scheme is cartesian between affine
  objects.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The rings of the affine objects of the small étale site -/

/-- The presheaf of rings of regular functions on the affine objects of the small étale site of
`S`: the restriction of the structure presheaf along the inclusion of the affine subsite. -/
noncomputable abbrev affineChartRings : (SmallAffineEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (SmallAffineEtale.inclusion B S hS).op ⋙ commStructurePresheaf B S hS

/-- The restriction map of the chart rings along a morphism is the map of global functions of
the underlying morphism of affine schemes. -/
theorem affineChartRings_map {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    (affineChartRings B S hS).map f.op =
      ((SmallAffineEtale.toScheme B S hS).map f).appTop :=
  rfl

/-- The underlying morphism of schemes of a morphism of affine objects of the small étale site is
étale, both objects being étale over `S`. -/
theorem etale_smallAffineEtale_toScheme_map {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    Etale ((SmallAffineEtale.toScheme B S hS).map f) :=
  inferInstanceAs (Etale ((toScheme B S hS).map ((SmallAffineEtale.inclusion B S hS).map f)))

/-- The underlying morphism of schemes of a morphism of affine objects of the small étale site is
flat, an étale morphism of schemes being flat. -/
theorem flat_smallAffineEtale_toScheme_map {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    Flat ((SmallAffineEtale.toScheme B S hS).map f) :=
  (Etale.iff_flat_and_formallyUnramified.mp
    (etale_smallAffineEtale_toScheme_map B S hS f)).1

/-- The chart rings are flat along every morphism of the small affine étale site. -/
theorem flat_affineChartRings_map {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    ((affineChartRings B S hS).map f.op).hom.Flat := by
  rw [affineChartRings_map]
  exact HasRingHomProperty.appTop (P := @Flat) _ (flat_smallAffineEtale_toScheme_map B S hS f)

/-- A finite covering family of affine objects of the small étale site is faithfully flat on
chart rings. -/
theorem faithfullyFlat_pi_affineChartRings {U : SmallAffineEtale B S hS}
    {I : Type v} [Finite I] (V : I → SmallAffineEtale B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : ∀ x, ∃ i, x ∈ Set.range ((SmallAffineEtale.toScheme B S hS).map (g i)))
    (hflat : ∀ i, Flat ((SmallAffineEtale.toScheme B S hS).map (g i))) :
    (RingHom.pi
      (fun i => ((affineChartRings B S hS).map (g i).op).hom)).FaithfullyFlat := by
  have _ := hflat
  show (RingHom.pi
    (fun i => (((SmallAffineEtale.toScheme B S hS).map (g i)).appTop).hom)).FaithfullyFlat
  exact AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop
    (fun i => (SmallAffineEtale.toScheme B S hS).obj (V i))
    (fun i => (SmallAffineEtale.toScheme B S hS).map (g i)) hcover

/-- A fibre product square of affine objects of the small étale site becomes a pushout square of
chart rings. -/
theorem isPushout_affineChartRings
    {X Y Z P : SmallAffineEtale B S hS}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout ((affineChartRings B S hS).map a.op)
      ((affineChartRings B S hS).map b.op)
      ((affineChartRings B S hS).map fst.op)
      ((affineChartRings B S hS).map snd.op) :=
  Stacks.Sites.isPushout_schemeRings_of_isPullback (SmallAffineEtale.toScheme B S hS)
    (affineChartRings B S hS) rfl h

/-- A fibre product square of a slice of the small affine étale site becomes a pushout square of
the restricted chart rings. -/
theorem isPushout_affineChartRings_over (U : SmallAffineEtale B S hS)
    {X Y Z P : Over U}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout (((Over.forget U).op ⋙ affineChartRings B S hS).map a.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map b.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map fst.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map snd.op) := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ SmallAffineEtale.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have _ : ∀ V : Over U, AlgebraicGeometry.IsAffine
      ((Over.forget U ⋙ SmallAffineEtale.toScheme B S hS).obj V) :=
    fun V => SmallAffineEtale.isAffine_toScheme_obj B S hS V.left
  exact Stacks.Sites.isPushout_schemeRings_of_isPullback
    (Over.forget U ⋙ SmallAffineEtale.toScheme B S hS)
    ((Over.forget U).op ⋙ affineChartRings B S hS) rfl h

/-- The image under the underlying-scheme functor of an étale covering zero-hypercover of an
affine object is a flat covering. -/
private theorem presieve₀_map_mem_precoverage_flat {U : SmallAffineEtale B S hS}
    (E : PreZeroHypercover U) (hE : SmallAffineEtale.IsCovering B S hS ⟨U, E⟩) :
    (E.map (SmallAffineEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.precoverage @Flat ((SmallAffineEtale.toScheme B S hS).obj U) := by
  have _ := hE.2
  obtain ⟨hs, het⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (SmallAffineEtale.toScheme B S hS))).mp (BigEtaleSite.IsCovering.etale hE.1)
  exact (Scheme.presieve₀_mem_precoverage_iff _).mpr
    ⟨hs, fun i => by have := het i; infer_instance⟩

/-- The covering families of the small affine étale site of `S` are finite, and on the underlying
schemes they are flat coverings of affine schemes. -/
theorem smallAffineEtale_covering_finite_flat {U : SmallAffineEtale B S hS} (P : Presieve U)
    (hP : P ∈ SmallAffineEtale.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (SmallAffineEtale.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((SmallAffineEtale.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  have _ := hE.2
  refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_⟩
  rw [← PreZeroHypercover.presieve₀_map]
  exact presieve₀_map_mem_precoverage_flat B S hS E hE

/-! ### A cartesian module over the chart rings is a sheaf -/

/-- A cartesian presheaf of modules over the chart rings of the small affine étale site of `S` is
a sheaf. -/
theorem isSheaf_of_cartesian_affineChart
    (M : PresheafOfModules.{max m (u + 1)}
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (SmallAffineEtale B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f)) :
    Presheaf.IsSheaf (SmallAffineEtale.topology B S hS) M.presheaf := by
  refine isSheaf_of_cartesian_of_flat_covers.{u, u + 1, u, m, u, u + 1}
    (SmallAffineEtale.toScheme B S hS) (affineChartRings B S hS) ?_ ?_ M hM
    (SmallAffineEtale.precoverage B S hS) ?_
  · intro U E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (SmallAffineEtale.toScheme B S hS))).mp hE
    exact faithfullyFlat_pi_affineChartRings B S hS E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineChartRings B S hS h
  · intro U P hP
    obtain ⟨E, rfl, hE⟩ := hP
    exact ⟨E, rfl, hE.2, presieve₀_map_mem_precoverage_flat B S hS E hE⟩

/-- A cartesian presheaf of modules over the chart rings of a slice of the small affine étale site
of `S` is a sheaf. -/
theorem isSheaf_of_cartesian_affineChart_over (U : SmallAffineEtale B S hS)
    (M : PresheafOfModules.{max m (u + 1)}
      ((Over.forget U).op ⋙ affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
        (R := (Over.forget U).op ⋙ affineChartRings B S hS) M f)) :
    Presheaf.IsSheaf ((SmallAffineEtale.topology B S hS).over U) M.presheaf := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ SmallAffineEtale.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  refine isSheaf_of_cartesian_of_flat_refinements.{u, u + 1, u, m, u}
    (Over.forget U ⋙ SmallAffineEtale.toScheme B S hS)
    ((Over.forget U).op ⋙ affineChartRings B S hS) ?_ ?_ M hM _ ?_
  · intro V E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (Over.forget U ⋙ SmallAffineEtale.toScheme B S hS))).mp hE
    exact faithfullyFlat_pi_affineChartRings B S hS (fun k => (E.X k).left)
      (fun k => (E.f k).left) hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineChartRings_over B S hS U h
  · intro V T hT
    exact Stacks.Sites.exists_finite_flat_refinement_over
      (SmallAffineEtale.toScheme B S hS) (SmallAffineEtale.precoverage B S hS)
      (smallAffineEtale_covering_finite_flat B S hS) U T hT

/-! ### Stacks 0H04 for the chart rings -/

/-- A global presentation on a slice of the small affine étale site makes the module cartesian
there, for the chart rings. -/
theorem isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation
    (hRing : Presheaf.IsSheaf (SmallAffineEtale.topology B S hS)
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf (SmallAffineEtale.topology B S hS) RingCat.{u}))
    (U : SmallAffineEtale B S hS) (hM : (M.over U).HasGlobalPresentation)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
      (R := (Over.forget U).op ⋙ affineChartRings B S hS) (M.over U).val f) := by
  apply isIso_restrictionBaseChange_of_hasGlobalPresentation.{u + 1, u, u, m}
    ((Over.forget U).op ⋙ affineChartRings B S hS)
    (Sheaf.over (⟨affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
      Sheaf (SmallAffineEtale.topology B S hS) RingCat.{u}) U).property
    (fun N hN => isSheaf_of_cartesian_affineChart_over B S hS U N hN)
    (M.over U) hM f

/-- Being cartesian over the chart rings is local on a covering of the small affine étale site of
`S`. -/
theorem isIso_restrictionBaseChange_affineChart_of_cover
    (M : PresheafOfModules.{max m (u + 1)}
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf (SmallAffineEtale.topology B S hS) M.presheaf)
    {V : SmallAffineEtale B S hS} {I : Type (u + 1)} [Finite I]
    (W : I → SmallAffineEtale B S hS) (gw : ∀ i, W i ⟶ V)
    (hcover : Sieve.ofArrows W gw ∈ SmallAffineEtale.topology B S hS V)
    (hcart : ∀ (i : I) {X Y : SmallAffineEtale B S hS} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M a.op))
    {U : SmallAffineEtale B S hS} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f.op) := by
  classical
  have hsT : Presieve.IsSheaf (SmallAffineEtale.topology B S hS)
      (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (SmallAffineEtale.topology B S hS)
      M.presheaf (forget AddCommGrpCat)).mp hs
  have hcoverU : Sieve.ofArrows (fun i => pullback f (gw i))
      (fun i => pullback.fst f (gw i)) ∈ SmallAffineEtale.topology B S hS U := by
    refine (SmallAffineEtale.topology B S hS).superset_covering ?_
      ((SmallAffineEtale.topology B S hS).pullback_stable f hcover)
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
    (flat_affineChartRings_map B S hS f) hsfV hsfU
    (fun i => isPushout_affineChartRings B S hS (IsPullback.of_hasPullback f (gw i)))
    (fun c => isPushout_affineChartRings B S hS (IsPullback.of_hasPullback f _))
    (fun i => hcart i (pullback.snd f (gw i)) (𝟙 _) (pullback.snd f (gw i)) (by simp))
    (fun c => hcart c.1 (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1) ≫
      pullback.fst (gw c.1) (gw c.2)) (pullback.fst (gw c.1) (gw c.2))
      (pullback.snd f (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1)) rfl)

/-- Stacks 0H04 for the chart rings: a quasi-coherent sheaf of modules over the rings of
regular functions on the affine objects of the small étale site of `S` is cartesian. -/
theorem isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite
    (hRing : Presheaf.IsSheaf (SmallAffineEtale.topology B S hS)
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (M : SheafOfModules.{max m (u + 1)}
      (⟨affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat, hRing⟩ :
        Sheaf (SmallAffineEtale.topology B S hS) RingCat.{u}))
    (hM : M.IsQuasicoherentOnSite)
    {U V : SmallAffineEtale B S hS} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val f.op) := by
  classical
  obtain ⟨I, hI, W, g, hcover, hpres⟩ :=
    Stacks.SheafOfModules.exists_finite_globalPresentation_cover.{u + 1, u, u, m}
      (SmallAffineEtale.precoverage B S hS)
      (fun P hP => (smallAffineEtale_covering_finite_flat B S hS P hP).1) M hM V
  have hcart (i : I) {X Y : (Over (W i))ᵒᵖ} (a : X ⟶ Y) :=
    isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation B S hS hRing M (W i)
      (hpres i) a
  have _ := hI
  have hcart' : ∀ (i : I) {X Y : SmallAffineEtale B S hS} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val a.op) := by
    intro i X Y x y a ha
    exact hcart i (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha))
  exact isIso_restrictionBaseChange_affineChart_of_cover B S hS M.val M.isSheaf W g
    hcover hcart' f

/-! ### Cartesianness between affine objects -/

/-- A quasi-coherent sheaf of modules on the small étale site of a scheme is cartesian between
affine objects: for a morphism `f : T ⟶ T'` of objects of `S_étale` whose underlying schemes are
affine, the base-change comparison `Γ(T) ⊗_{Γ(T')} 𝒢(T') ⟶ 𝒢(T)` is bijective.

This is a step of Stacks 03DX (2) at `τ = étale`, whose statement as an equivalence of categories
is `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`. -/
@[stacks 03DX "quasi-coherent implies cartesian between affine objects of the small étale site"]
theorem bijective_restrictionBaseChange_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    {T T' : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    (hT' : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T'))
    (f : T ⟶ T') :
    Function.Bijective
      (restrictionBaseChange (R := commStructurePresheaf B S hS) G.val f.op) := by
  have hds : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have hcc : (SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  have hover : ∀ X : SmallAffineEtale B S hS,
      (Over.post (X := X) (SmallAffineEtale.inclusion B S hS)).IsContinuous
        ((SmallAffineEtale.topology B S hS).over X)
        ((topology B S hS).over ((SmallAffineEtale.inclusion B S hS).obj X)) :=
    fun X => by
      have _ := Stacks.Sites.overPost_isDenseSubsite
        (J := SmallAffineEtale.topology B S hS) (K := topology B S hS)
        (SmallAffineEtale.inclusion B S hS) X
      infer_instance
  have h₁ := Stacks.SheafOfModules.isQuasicoherentOnSite_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (structureSheaf B S hS) G hG
  have h₂ := _root_.SheafOfModules.isQuasicoherentOnSite_uliftForPresentation h₁
  have h₃ := isIso_restrictionBaseChange_affineChart_of_isQuasicoherentOnSite.{u, u}
    B S hS _ _ h₂
    ((SmallAffineEtale.inclusion B S hS).preimage
      (X := (⟨T, hT⟩ : SmallAffineEtale B S hS)) (Y := ⟨T', hT'⟩) f)
  have h₄ := bijective_restrictionBaseChange_of_uliftForPresentation
    (affineChartRings B S hS) _ _ _ h₃
  have h₅ := bijective_restrictionBaseChange_of_restriction
    (J := topology B S hS) (K := SmallAffineEtale.topology B S hS)
    (SmallAffineEtale.inclusion B S hS) (commStructurePresheaf B S hS) _ G _ h₄
  rwa [(SmallAffineEtale.inclusion B S hS).map_preimage] at h₅

end AlgebraicGeometry.SmallEtale

end
