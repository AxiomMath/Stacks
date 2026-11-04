module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsChart
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.IsoLocusAffineTests
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.GeometricallyIntegralFibres
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# The generic-rank functor on a chart is an isomorphism locus

Let `c` be a chart of Situation 05MP: an affine open `V` of the base, an affine open `U` of the
total space surjecting onto it, and a surjection `u : 𝒪_U^{⊕ n} ⟶ ℱ|_U`. Over `V` the functor
`H_n` of Stacks 05MR is the functor `F_iso` of Stacks 05MI for `u`, and `H_q` is empty for
`q > n`. The source deduces the first from Stacks 05L8 or 05IA; here it is the statement that a
surjection from a finite free module which is free of the same rank at the generic point of
every fibre is injective, the weakly associated points of the source being those generic points.
Since `𝒪_U^{⊕ n}` is of finite presentation, flat and pure over `V` (Stacks 05K5, for a flat
morphism of finite type with geometrically integral fibres), Theorem 05PF represents `F_iso`
by a closed immersion into `V`.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.Chart.condition_iff_isIso`: over the chart,
  `H_n` is `F_iso` for `u`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.Chart.isEmpty_of_condition`: over the chart,
  `H_q` is empty for `q > n`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.Chart.exists_closedImmersion`: over the chart,
  `H_n` is represented by a closed immersion into `V`, of finite presentation when `ℱ` is.

## References

* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
* [Stacks Project, Tag 05K5](https://stacks.math.columbia.edu/tag/05K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A finite free module is of finite presentation. -/
theorem isFinitePresentation_coproductUnit (Y : Scheme.{u}) (n : ℕ) :
    (∐ fun _ : Fin n => SheafOfModules.unit Y.ringCatSheaf : Y.Modules).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    (Stacks.StalkFreeBridge.coproductUnitIsoFree n).symm
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite Y
      (ULift.{u} (Fin n)))

/-- **A finite free module over a flat morphism of finite type with geometrically integral fibres
is universally pure** (Stacks 05K5 for `𝒪_X^{⊕ n}`): an associated point of a fibre of a base
change of a finite free module is the generic point of that fibre. -/
theorem universallyPure_coproductUnit {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [Flat f] [GeometricallyIntegral f] (n : ℕ) :
    IsUniversallyPureRelative.{u} f
      (∐ fun _ : Fin n => SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  rintro s D ⟨hAss, hDisjoint⟩
  have base_fiberι (s) (x : D.toT.fiber s) : D.toT.base (D.toT.fiberι s x) = s := by
    have hmem : D.toT.fiberι s x ∈ Set.range (D.toT.fiberι s) := ⟨x, rfl⟩
    rwa [D.toT.range_fiberι] at hmem
  obtain ⟨s', x', hx', hxi⟩ :=
    (Stacks.Divisors.mem_relativeAssassin D.toT (D.pulledBack _) D.xi).mp hAss
  obtain rfl : s' = D.t' :=
    ((base_fiberι s' x').symm.trans (congrArg D.toT.base hxi)).trans D.xi_liesOver
  have : Flat D.toT := Flat.isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  have : GeometricallyIntegral D.toT :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) D.isPullback inferInstance
  have fiberIso : (Scheme.Modules.pullback ((D.toT).fiberι D.t')).obj (D.pulledBack _) ≅
      (∐ fun _ : Fin n => SheafOfModules.unit ((D.toT).fiber D.t').ringCatSheaf :
        ((D.toT).fiber D.t').Modules) :=
    (Scheme.Modules.pullbackComp ((D.toT).fiberι D.t') D.toX).app _ ≪≫
      pullbackCoproductUnitIso ((D.toT).fiberι D.t' ≫ D.toX) n
  have hxWeak := mem_schemeWeaklyAssociatedPoints_of_coproductUnit
    (Stacks.Divisors.associatedPoints_subset _ (associatedPoints_subset_of_mono fiberIso.hom hx'))
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints, genericPoints_eq_singleton] at hxWeak
  have hxGeneric : x' = genericPoint ((D.toT).fiber D.t') := by simpa using hxWeak
  let z₀ : (D.toT).fiber D.t := genericPoint ((D.toT).fiber D.t)
  have hspec : D.t' ⤳ D.toT.base ((D.toT).fiberι D.t z₀) := by
    simpa [base_fiberι D.t z₀] using D.specializes
  obtain ⟨z', hz'z₀, hz't'⟩ := (Flat.generalizingMap D.toT) hspec
  let y' : (D.toT).fiber D.t' := (D.toT).fiberHomeo D.t' |>.symm ⟨z', hz't'⟩
  have hy' : D.toT.fiberι D.t' y' = z' := by simp [y']
  have hgenSpec : D.xi ⤳ z' := by
    rw [← hxi, hxGeneric, ← hy']
    exact (genericPoint_specializes y').map (D.toT.fiberι D.t').continuous
  have hmeet : D.toT.fiberι D.t z₀ ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
    ⟨(hgenSpec.trans hz'z₀).mem_closure, z₀, rfl⟩
  rwa [hDisjoint] at hmeet

namespace FreeAtGenericPointsSituation

namespace Chart

variable {D : FreeAtGenericPointsSituation.{u}} (c : D.Chart)

/-- The chart's open `U` of the total space is an affine scheme. -/
instance : IsAffine c.U.toScheme := c.isAffineOpen_U

/-- The chart's open `V` of the base is an affine scheme. -/
instance : IsAffine c.V.toScheme := c.isAffineOpen_V

/-- The isomorphism-locus situation of the chart's surjection, over the chart's base. -/
noncomputable abbrev isoSituation : Stacks.Flatness.ModuleMapBaseChangeSituation.{u} where
  S := c.V.toScheme
  X := c.U.toScheme
  f := c.g
  F := (∐ fun _ : Fin c.n => SheafOfModules.unit c.U.toScheme.ringCatSheaf :
    c.U.toScheme.Modules)
  G := (Scheme.Modules.pullback c.U.ι).obj D.F
  hom := c.u
  isQuasicoherentG :=
    letI : SheafOfModules.IsQuasicoherent (R := structureSheafRing D.X.toRingedSpace) D.F :=
      inferInstanceAs (SheafOfModules.IsQuasicoherent (R := D.X.ringCatSheaf) D.F)
    @SheafOfModules.modulePullback_isQuasicoherent _ _ c.U.ι.toLRSHom.toShHom D.F inferInstance

variable {T : Scheme.{u}} (a : T ⟶ c.V.toScheme)

/-- The base change of the chart's surjection, with source the free module. -/
noncomputable def baseChangeHom :
    (∐ fun _ : Fin c.n => SheafOfModules.unit (pullback c.g a).ringCatSheaf :
      (pullback c.g a).Modules) ⟶
      (Scheme.Modules.pullback (pullback.fst c.g a)).obj
        ((Scheme.Modules.pullback c.U.ι).obj D.F) :=
  (pullbackCoproductUnitIso (pullback.fst c.g a) c.n).inv ≫
    (Scheme.Modules.pullback (pullback.fst c.g a)).map c.u

/-- The base change of the chart's surjection is an epimorphism. -/
instance : Epi (c.baseChangeHom a) := by
  unfold baseChangeHom
  infer_instance

/-- The chart's surjection is an isomorphism after base change along `a` if and only if
`baseChangeHom a` is an isomorphism. -/
theorem isIsomorphismAfterBaseChange_iff :
    c.isoSituation.IsIsomorphismAfterBaseChange (Over.mk a) ↔ IsIso (c.baseChangeHom a) := by
  show IsIso ((Scheme.Modules.pullback (pullback.fst c.g a)).map c.u) ↔ _
  unfold baseChangeHom
  exact ⟨fun _ ↦ inferInstance, fun _ ↦
    IsIso.of_isIso_comp_left (pullbackCoproductUnitIso (pullback.fst c.g a) c.n).inv _⟩

/-- **Over the chart, `H_n` is `F_iso`.** -/
theorem condition_iff_isIso :
    D.Condition c.n (Over.mk (a ≫ c.V.ι)) ↔
      c.isoSituation.IsIsomorphismAfterBaseChange (Over.mk a) := by
  rw [c.isIsomorphismAfterBaseChange_iff, c.condition_iff]
  refine ⟨isIso_of_forall_exists_freeAtPointOfRank (pullback.snd c.g a) (c.baseChangeHom a),
    fun h t ↦ ?_⟩
  have : Surjective (pullback.snd c.g a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback c.g a)
      c.surjective_g
  obtain ⟨y, hy⟩ := (pullback.snd c.g a).surjective t
  exact ⟨y, hy, freeAtPointOfRank_of_isIso (c.baseChangeHom a) y⟩

/-- **Over the chart, `H_q` is empty for `q > n`.** -/
theorem isEmpty_of_condition {q : ℕ} (hq : c.n < q)
    (h : D.Condition q (Over.mk (a ≫ c.V.ι))) : IsEmpty T := by
  rw [c.condition_iff] at h
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨y, -, hy⟩ := h t
  exact absurd (le_of_freeAtPointOfRank_of_epi (c.baseChangeHom a) hy) (not_le.mpr hq)

/-- **Theorem 05PF on the chart.** Over the chart's base, the generic-rank functor of the
chart's rank is represented by a closed immersion. -/
theorem exists_closedImmersion :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ c.V.toScheme), IsClosedImmersion i ∧
      (D.F.IsFinitePresentation → LocallyOfFinitePresentation i) ∧
      ∀ (T : Scheme.{u}) (a : T ⟶ c.V.toScheme),
        D.Condition c.n (Over.mk (a ≫ c.V.ι)) ↔ ∃ b : T ⟶ Z, b ≫ i = a := by
  have : (∐ fun _ : Fin c.n => SheafOfModules.unit c.U.toScheme.ringCatSheaf :
      c.U.toScheme.Modules).IsFinitePresentation := isFinitePresentation_coproductUnit _ _
  have : Epi c.isoSituation.hom := c.epi
  have hflat : IsFlatOver c.isoSituation.f.toLRSHom.toShHom c.isoSituation.F := fun y ↦
    isFlatOverAt_of_free_stalk c.g _ y (Stacks.StalkFreeBridge.free_stalk_coproductUnit c.n y)
  have hpure : IsPureRelative c.isoSituation.f c.isoSituation.F := fun s D' _ _ ↦
    universallyPure_coproductUnit c.g c.n s D'
  obtain ⟨W, hW, ⟨e⟩⟩ :=
    Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion_of_affineTests
      c.isoSituation hflat hpure
  refine ⟨W.left, W.hom, hW, fun hfp ↦ ?_, fun T a ↦ ?_⟩
  · have : c.isoSituation.G.IsFinitePresentation :=
      @Stacks.SheafOfModules.modulePullback_isFinitePresentation c.U.toScheme.toRingedSpace
        D.X.toRingedSpace c.U.ι.toLRSHom.toShHom D.F hfp
    exact (Stacks.Flatness.finitePresentation_hom_of_representableBy_isomorphismFunctor
      c.isoSituation W.hom e).1
  · rw [c.condition_iff_isIso]
    exact ⟨fun h ↦ ⟨(e.homEquiv.symm ⟨h⟩).left, Over.w (e.homEquiv.symm ⟨h⟩)⟩,
      fun ⟨b, hb⟩ ↦ (e.homEquiv (Over.homMk b hb : Over.mk a ⟶ W)).down⟩

end Chart

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
