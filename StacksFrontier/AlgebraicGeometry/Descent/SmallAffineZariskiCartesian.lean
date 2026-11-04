module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineSiteQuasiCoherentObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSmallSections
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Cartesian modules on the small affine Zariski site

Let `S` be a scheme contained in a big Zariski site `B`.  A presheaf of modules on the small
affine Zariski site of `S` — the affine opens of `S`, with the standard Zariski coverings of
Stacks 020T (4) — over the restriction of the sheaf of global functions is *cartesian* when
each of its restriction maps exhibits its target as a base change of its source, that is, when
every `𝓕(U') ⊗_{𝒪(U')} 𝒪(U) ⟶ 𝓕(U)` is an isomorphism.

This file proves that a cartesian presheaf of modules on that site is a sheaf, and conversely that
a quasi-coherent sheaf of modules on the ringed site is cartesian.

## Main definitions

* `AlgebraicGeometry.SmallAffineZariski.affineChartRings`: the presheaf of rings of global
  regular functions on the affine opens of `S`, which is the structure presheaf of
  `AlgebraicGeometry.smallAffineZariskiRingedSite`.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.flat_affineChartRings_map`,
  `AlgebraicGeometry.SmallAffineZariski.faithfullyFlat_pi_affineChartRings` and
  `AlgebraicGeometry.SmallAffineZariski.isPushout_affineChartRings`: the chart rings are flat
  along every morphism, faithfully flat along a finite covering family, and turn fibre products
  into pushouts of rings.
* `AlgebraicGeometry.SmallAffineZariski.covering_finite_flat`: the covering families of the
  small affine Zariski site are finite and flat on the underlying schemes.
* `AlgebraicGeometry.SmallAffineZariski.isSheaf_of_cartesian_affineChart` and
  `AlgebraicGeometry.SmallAffineZariski.isSheaf_of_cartesian_affineChart_over`: **a cartesian
  presheaf of modules over the chart rings, or over their restriction to a slice, is a sheaf.**
* `AlgebraicGeometry.SmallAffineZariski.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`
  is **Stacks 0H04 for the chart rings of the small affine Zariski site**: a quasi-coherent
  sheaf of modules on `(S_{affine, Zar}, 𝒪_affine)` is cartesian.

## Implementation notes

`AlgebraicGeometry.SmallAffineZariski.isSheaf_of_cartesian_affineChart` leaves the universe of
the sections free of the universes of the site, so it applies to sheaves of modules in the
universe of the schemes. The slice statement and everything downstream of it stay at the universe
`max m (u + 1)`, because a global presentation is indexed by the arrows of the site.

No `@[stacks]` attribute is claimed here: Stacks 0H04 is about the affine étale site of an
algebraic space, not about this site.

## References

* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020R](https://stacks.math.columbia.edu/tag/020R)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace AlgebraicGeometry.SmallAffineZariski

open Stacks.PresheafOfModules

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of rings of regular functions on the affine opens of `S`: the structure
presheaf of the small affine Zariski ringed site. -/
noncomputable abbrev affineChartRings : (SmallAffineZariski B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (smallAffineZariskiRingedSite B S hS).O.obj

/-- The restriction map of the chart rings along a morphism is the map of global functions of
the underlying morphism of affine schemes. -/
theorem affineChartRings_map {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    (affineChartRings B S hS).map f.op =
      ((SmallAffineZariski.toScheme B S hS).map f).appTop :=
  rfl

/-- The underlying morphism of schemes of a morphism of affine opens of `S` is an open
immersion. -/
theorem isOpenImmersion_toScheme_map {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    IsOpenImmersion ((SmallAffineZariski.toScheme B S hS).map f) :=
  isOpenImmersion_smallZariski_toScheme_map B S hS
    ((SmallAffineZariski.inclusion B S hS).map f)

/-- The underlying morphism of schemes of a morphism of affine opens of `S` is flat. -/
theorem flat_toScheme_map {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    Flat ((SmallAffineZariski.toScheme B S hS).map f) :=
  have := isOpenImmersion_toScheme_map B S hS f
  inferInstance

/-- The chart rings are flat along every morphism of the small affine Zariski site. -/
theorem flat_affineChartRings_map {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    ((affineChartRings B S hS).map f.op).hom.Flat :=
  flat_smallAffineZariskiRingedSite_O_map B S hS f.op

/-- A finite covering family of affine opens of `S` is faithfully flat on chart rings. -/
theorem faithfullyFlat_pi_affineChartRings {U : SmallAffineZariski B S hS}
    {I : Type v} [Finite I] (V : I → SmallAffineZariski B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : ∀ x, ∃ i, x ∈ Set.range ((SmallAffineZariski.toScheme B S hS).map (g i)))
    (hflat : ∀ i, Flat ((SmallAffineZariski.toScheme B S hS).map (g i))) :
    (RingHom.pi
      (fun i => ((affineChartRings B S hS).map (g i).op).hom)).FaithfullyFlat := by
  have _ := hflat
  show (RingHom.pi
    (fun i => (((SmallAffineZariski.toScheme B S hS).map (g i)).appTop).hom)).FaithfullyFlat
  exact AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop
    (fun i => (SmallAffineZariski.toScheme B S hS).obj (V i))
    (fun i => (SmallAffineZariski.toScheme B S hS).map (g i)) hcover

/-- A fibre product square of affine opens of `S` becomes a pushout square of chart rings. -/
theorem isPushout_affineChartRings
    {X Y Z P : SmallAffineZariski B S hS}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout ((affineChartRings B S hS).map a.op)
      ((affineChartRings B S hS).map b.op)
      ((affineChartRings B S hS).map fst.op)
      ((affineChartRings B S hS).map snd.op) :=
  Stacks.Sites.isPushout_schemeRings_of_isPullback (SmallAffineZariski.toScheme B S hS)
    (affineChartRings B S hS) rfl h

/-- A covering family of the small affine Zariski site of `S` is finite and, on the underlying
schemes, a flat covering. -/
private theorem finite_and_map_presieve₀_mem_flat {U : SmallAffineZariski B S hS}
    (E : PreZeroHypercover.{u + 1} U) (hE : SmallAffineZariski.IsCovering B S hS ⟨U, E⟩) :
    Finite E.I₀ ∧ (E.map (SmallAffineZariski.toScheme B S hS)).presieve₀ ∈
      Scheme.precoverage @Flat ((SmallAffineZariski.toScheme B S hS).obj U) := by
  obtain ⟨_, hstd, hfin, _⟩ := hE
  obtain ⟨hs, him⟩ := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (SmallAffineZariski.toScheme B S hS))).mp hstd
  exact ⟨hfin, (Scheme.presieve₀_mem_precoverage_iff _).mpr
    ⟨hs, fun i => by have := him i; infer_instance⟩⟩

/-- The covering families of the small affine Zariski site of `S` are finite, and on the
underlying schemes they are flat coverings of affine schemes. -/
theorem covering_finite_flat {U : SmallAffineZariski B S hS} (P : Presieve U)
    (hP : P ∈ SmallAffineZariski.precoverage B S hS U) :
    P.uncurry.Finite ∧ P.map (SmallAffineZariski.toScheme B S hS) ∈
      Scheme.precoverage @Flat ((SmallAffineZariski.toScheme B S hS).obj U) := by
  obtain ⟨E, rfl, hE⟩ := hP
  obtain ⟨hfin, hfl⟩ := finite_and_map_presieve₀_mem_flat B S hS E hE
  exact ⟨Precoverage.ofArrows_mem_finite _ _, by rwa [← PreZeroHypercover.presieve₀_map]⟩

/-! ### A cartesian module over the chart rings is a sheaf -/

/-- **A cartesian presheaf of modules over the chart rings of the small affine Zariski site of
`S` is a sheaf.**  The sections may live in any `Type (max m u)`, in particular in the universe
`Type u` of the structure sheaf. -/
theorem isSheaf_of_cartesian_affineChart
    (M : PresheafOfModules.{max m u}
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (SmallAffineZariski B S hS)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, m} M f)) :
    Presheaf.IsSheaf (SmallAffineZariski.topology B S hS) M.presheaf := by
  refine isSheaf_of_cartesian_of_flat_covers'.{u, u + 1, u, m, u, u + 1}
    (SmallAffineZariski.toScheme B S hS) (affineChartRings B S hS) ?_ ?_ M hM
    (SmallAffineZariski.precoverage B S hS) ?_
  · intro U E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (SmallAffineZariski.toScheme B S hS))).mp hE
    exact faithfullyFlat_pi_affineChartRings B S hS E.X E.f hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineChartRings B S hS h
  · intro U P hP
    obtain ⟨E, rfl, hE⟩ := hP
    obtain ⟨hfin, hfl⟩ := finite_and_map_presieve₀_mem_flat B S hS E hE
    exact ⟨E, rfl, inferInstance, hfl⟩

/-- A fibre product square of a slice of the small affine Zariski site becomes a pushout square
of the restricted chart rings. -/
theorem isPushout_affineChartRings_over (U : SmallAffineZariski B S hS)
    {X Y Z P : Over U}
    {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout (((Over.forget U).op ⋙ affineChartRings B S hS).map a.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map b.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map fst.op)
      (((Over.forget U).op ⋙ affineChartRings B S hS).map snd.op) := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ SmallAffineZariski.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  have _ : ∀ V : Over U, AlgebraicGeometry.IsAffine
      ((Over.forget U ⋙ SmallAffineZariski.toScheme B S hS).obj V) :=
    fun V => SmallAffineZariski.isAffine_toScheme_obj B S hS V.left
  exact Stacks.Sites.isPushout_schemeRings_of_isPullback
    (Over.forget U ⋙ SmallAffineZariski.toScheme B S hS)
    ((Over.forget U).op ⋙ affineChartRings B S hS) rfl h

/-- **A cartesian presheaf of modules over the chart rings of a slice of the small affine
Zariski site of `S` is a sheaf.** -/
theorem isSheaf_of_cartesian_affineChart_over (U : SmallAffineZariski B S hS)
    (M : PresheafOfModules.{max m (u + 1)}
      ((Over.forget U).op ⋙ affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y),
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
        (R := (Over.forget U).op ⋙ affineChartRings B S hS) M f)) :
    Presheaf.IsSheaf ((SmallAffineZariski.topology B S hS).over U) M.presheaf := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ SmallAffineZariski.toScheme B S hS) := by
    apply comp_preservesLimitsOfShape
  refine isSheaf_of_cartesian_of_flat_refinements.{u, u + 1, u, m, u}
    (Over.forget U ⋙ SmallAffineZariski.toScheme B S hS)
    ((Over.forget U).op ⋙ affineChartRings B S hS) ?_ ?_ M hM _ ?_
  · intro V E hfin hE
    have _ := hfin
    obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
      (E.map (Over.forget U ⋙ SmallAffineZariski.toScheme B S hS))).mp hE
    exact faithfullyFlat_pi_affineChartRings B S hS (fun k => (E.X k).left)
      (fun k => (E.f k).left) hcov hfl
  · intro _ _ _ _ _ _ _ _ h
    exact isPushout_affineChartRings_over B S hS U h
  · intro V T hT
    exact Stacks.Sites.exists_finite_flat_refinement_over
      (SmallAffineZariski.toScheme B S hS) (SmallAffineZariski.precoverage B S hS)
      (covering_finite_flat B S hS) U T hT

/-! ### Stacks 0H04 for the chart rings -/

/-- A global presentation on a slice of the small affine Zariski site makes the module cartesian
there, for the chart rings. -/
theorem isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation
    (M : SheafOfModules.{max m (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (U : SmallAffineZariski B S hS) (hM : (M.over U).HasGlobalPresentation)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)}
      (R := (Over.forget U).op ⋙ affineChartRings B S hS) (M.over U).val f) := by
  apply isIso_restrictionBaseChange_of_hasGlobalPresentation.{u + 1, u, u, m}
    ((Over.forget U).op ⋙ affineChartRings B S hS)
    (Sheaf.over (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O) U).property
    (fun N hN => isSheaf_of_cartesian_affineChart_over B S hS U N hN)
    (M.over U) hM f

/-- Being cartesian over the chart rings is local on a covering of the small affine Zariski site
of `S`. -/
theorem isIso_restrictionBaseChange_affineChart_of_cover
    (M : PresheafOfModules.{max m (u + 1)}
      (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat))
    (hs : Presheaf.IsSheaf (SmallAffineZariski.topology B S hS) M.presheaf)
    {V : SmallAffineZariski B S hS} {I : Type (u + 1)} [Finite I]
    (W : I → SmallAffineZariski B S hS) (gw : ∀ i, W i ⟶ V)
    (hcover : Sieve.ofArrows W gw ∈ SmallAffineZariski.topology B S hS V)
    (hcart : ∀ (i : I) {X Y : SmallAffineZariski B S hS} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M a.op))
    {U : SmallAffineZariski B S hS} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M f.op) := by
  classical
  have hsT : Presieve.IsSheaf (SmallAffineZariski.topology B S hS)
      (M.presheaf ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_comp (SmallAffineZariski.topology B S hS)
      M.presheaf (forget AddCommGrpCat)).mp hs
  have hcoverU : Sieve.ofArrows (fun i => pullback f (gw i))
      (fun i => pullback.fst f (gw i)) ∈ SmallAffineZariski.topology B S hS U := by
    refine (SmallAffineZariski.topology B S hS).superset_covering ?_
      ((SmallAffineZariski.topology B S hS).pullback_stable f hcover)
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

/-- **Stacks 0H04 for the chart rings of the small affine Zariski site**: a quasi-coherent sheaf
of modules over the rings of regular functions on the affine opens of `S` is cartesian. -/
theorem isIso_restrictionBaseChange_of_isQuasicoherentOnSite
    (M : SheafOfModules.{max m (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallAffineZariskiRingedSite B S hS).O))
    (hM : M.IsQuasicoherentOnSite)
    {U V : SmallAffineZariski B S hS} (f : U ⟶ V) :
    IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val f.op) := by
  classical
  obtain ⟨I, hI, W, g, hcover, hpres⟩ :=
    Stacks.SheafOfModules.exists_finite_globalPresentation_cover.{u + 1, u, u, m}
      (SmallAffineZariski.precoverage B S hS)
      (fun P hP => (covering_finite_flat B S hS P hP).1) M hM V
  have hcart (i : I) {X Y : (Over (W i))ᵒᵖ} (a : X ⟶ Y) :=
    isIso_restrictionBaseChange_chart_over_of_hasGlobalPresentation B S hS M (W i) (hpres i) a
  have _ := hI
  have hcart' : ∀ (i : I) {X Y : SmallAffineZariski B S hS} (x : X ⟶ W i) (y : Y ⟶ W i)
      (a : X ⟶ Y), a ≫ y = x →
      IsIso (restrictionBaseChange.{u + 1, u, u, max m (u + 1)} M.val a.op) :=
    fun i {_ _} x y a ha =>
      hcart i (Quiver.Hom.op (Over.homMk (U := Over.mk x) (V := Over.mk y) a ha))
  exact isIso_restrictionBaseChange_affineChart_of_cover B S hS M.val M.isSheaf W g
    hcover hcart' f

end AlgebraicGeometry.SmallAffineZariski

end
