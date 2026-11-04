module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordDiagonalPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPointSetObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyPointLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibreFullSubcategory

/-!
# The Deligne–Mumford and quasi-Deligne–Mumford loci exist (Stacks 0DSM)

**Stacks 0DSM.** For an algebraic stack `𝒳` there are open substacks `𝒳'' ⊆ 𝒳' ⊆ 𝒳` such that
`𝒳''` is DM, `𝒳'` is quasi-DM, and these are the largest open substacks with these properties.

`StacksFrontier/AlgebraicGeometry/Stacks/DeligneMumfordLocus.lean` constructs the two loci as
suprema of object properties and reduces the lemma to four inputs: that a union of DM (resp.
quasi-DM) open substacks is DM (resp. quasi-DM), and that each locus is cut out by an open
substack. This file proves all four, and states the lemma with no hypothesis.

## The route

The source proves the local-global step through the structure theorems **Stacks 06N3** and
**Stacks 06MF**: a DM open substack has a surjective étale chart by a scheme, and the disjoint
union of the charts of the members is a chart of the union. This file does not use those
theorems. DM-ness is a property of the relative diagonal, and it can be tested on one object at
a time: by `AlgebraicGeometry.Stack.isDM_of_hasPropertyAtDiagonalPoints` it suffices that the
diagonal is unramified at the diagonal points `(x, x, id)`, where its fibre is the relative
automorphism presheaf of `x` (the converse half of **Stacks 0CL0**, parts (4) and (5)). That test
is local on the base of `x`
(`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_of_forall_point_local`, the local half of
**Stacks 045D**), and on a piece of the base where `x` lies in a DM open substack `𝒰` the
automorphism presheaf of `x` is that of `x` read in `𝒰`, the full subcategory seeing all morphisms
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheafFullSubcategoryIso`).
This is `AlgebraicGeometry.Stack.hasPropertyAtDiagonalPoints_of_cover`.

The union itself is the open substack `AlgebraicGeometry.Stack.openSubstackOfPoints` cut out by
the union of the point sets of the members (**Stacks 06FJ**, surjectivity). Its objects lie
locally in a member by the injectivity half of **Stacks 06FJ**
(`AlgebraicGeometry.Stack.OpenSubstack.exists_isOpenImmersion_property_of_pointsWithin_iUnion`).

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyDM_of_cover` and
  `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_cover`: an open substack covered, locally on
  the bases of its objects, by DM (resp. quasi-DM) open substacks is DM (resp. quasi-DM).
* `AlgebraicGeometry.Stack.exists_isAbsolutelyDM_openSubstack_le` and
  `AlgebraicGeometry.Stack.exists_isAbsolutelyQuasiDM_openSubstack_le`: a set of DM (resp.
  quasi-DM) open substacks has a DM (resp. quasi-DM) open substack containing all of them.
* `AlgebraicGeometry.Stack.isAbsolutelyDMLocalOnOpenSubstacks`,
  `AlgebraicGeometry.Stack.isAbsolutelyQuasiDMLocalOnOpenSubstacks`,
  `AlgebraicGeometry.Stack.exists_property_eq_dmLocus` and
  `AlgebraicGeometry.Stack.exists_property_eq_quasiDMLocus`: the four inputs of
  `AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`.
* `AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_openSubstacks`:
  **Stacks 0DSM**, with no hypothesis.

## References

* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.DiagonalFibre
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The diagonal test is local on a cover by open substacks.** Let `𝒲 ⊆ 𝒳` be an open substack
and let `s` be a set of open substacks of `𝒳` such that every object of `𝒲` lies, locally on a
flat and locally finitely presented cover of its base, in a member of `s`. If the relative
diagonal of the structure morphism of every member of `s` has `P` at the diagonal points, so has
that of `𝒲`. -/
theorem hasPropertyAtDiagonalPoints_of_cover
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (W : OpenSubstack 𝒳) (s : Set (OpenSubstack 𝒳))
    (hcov : ∀ (T : BigFppfOver B S hS) (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj),
      y ⋙ 𝒳.val.val.p = Over.map T.hom → W.property (y.obj (Over.mk (𝟙 T.left))) →
      ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
          Flat (B.inclusion.map j.left) ∧ LocallyOfFinitePresentation (B.inclusion.map j.left) ∧
          t ∈ Set.range (B.inclusion.map j.left) ∧ ∃ U ∈ s, U.property (y.obj V))
    (hP : ∀ U ∈ s,
      HasPropertyAtDiagonalPoints B S hS P (structureMorphism B S hS U.toAlgebraicStack)) :
    HasPropertyAtDiagonalPoints B S hS P (structureMorphism B S hS W.toAlgebraicStack) := by
  intro V x hx F hF hE
  refine prop_algebraicSpaceMap_of_forall_point_local B S hS P
    (relativeDiagonal.{u, u, u + 1} B S hS W.toAlgebraicStack.val _
      (structureMorphism B S hS W.toAlgebraicStack).hom).hom V _
    (by rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p]; exact hx)
    (fun t => ?_) F hF hE
  obtain ⟨V0, j, hflat, hlfp, ht, U, hUs, hU⟩ :=
    hcov V (x ⋙ W.property.ι) hx (x.obj (Over.mk (𝟙 V.left))).property t
  refine ⟨V0.left, j.left, hflat, hlfp, ht, fun G hG hEG => ?_⟩
  -- the restricted point, and its lift to `U`
  set x' : BigFppfOver B V0.left.1 V0.left.2 ⥤ W.toAlgebraicStack.val.val.obj :=
    Over.map j.left ⋙ x with hx'def
  have hx' : x' ⋙ W.toAlgebraicStack.val.val.p = Over.map (Over.mk (j.left ≫ V.hom)).hom := by
    rw [hx'def, Functor.assoc, hx, ← Over.mapComp_eq]
    rfl
  have hVj : V0.hom = j.left := by simpa using (Over.w j).symm
  have hxU : ∀ T, U.property (x'.obj T).obj := by
    intro T
    let k : (Over.map j.left).obj T ⟶ V0 := Over.homMk T.hom (by simp [hVj])
    exact OpenSubstack.prop_of_hom B S hS U (x.map k).hom hU
  let z : BigFppfOver B V0.left.1 V0.left.2 ⥤ U.toAlgebraicStack.val.val.obj :=
    U.property.lift (x' ⋙ W.property.ι) hxU
  have hz : z ⋙ U.toAlgebraicStack.val.val.p = Over.map (Over.mk (j.left ≫ V.hom)).hom := hx'
  -- the fibres at the diagonal points of `x'` and of `z` are the same presheaf
  have hq := (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val.isFiberedInGroupoids
  have hFX := (structureMorphism B S hS 𝒳).hom.hom.w
  have hFW := (structureMorphism B S hS W.toAlgebraicStack).hom.hom.w
  have hFU := (structureMorphism B S hS U.toAlgebraicStack).hom.hom.w
  have hYW : (x' ⋙ RelDiag hFW) ⋙ RelProdP _ _ _ = Over.map (Over.mk (j.left ≫ V.hom)).hom :=
    hx'
  have hYU : (z ⋙ RelDiag hFU) ⋙ RelProdP _ _ _ = Over.map (Over.mk (j.left ≫ V.hom)).hom := hz
  have hYX : ((z ⋙ U.property.ι) ⋙ RelDiag hFX) ⋙ RelProdP _ _ _ =
      Over.map (Over.mk (j.left ≫ V.hom)).hom := hz
  have iU := relVertHomPresheafFullSubcategoryIso hq 𝒳.val.isFiberedInGroupoids hFX U.property
    U.toAlgebraicStack.val.isFiberedInGroupoids z hFU hYU hYX
  have iW := relVertHomPresheafFullSubcategoryIso hq 𝒳.val.isFiberedInGroupoids hFX W.property
    W.toAlgebraicStack.val.isFiberedInGroupoids x' hFW hYW hYX
  obtain ⟨e1⟩ := (nonempty_equivalenceOver_fst_iff hq W.toAlgebraicStack.val.isFiberedInGroupoids
    hYW hFW G).mp hEG
  exact hP U hUs (Over.mk (j.left ≫ V.hom)) z hz G hG
    ((nonempty_equivalenceOver_fst_iff hq U.toAlgebraicStack.val.isFiberedInGroupoids hYU hFU
      G).mpr ⟨Functor.isoWhiskerRight (iU ≪≫ iW.symm) _ ≪≫ e1⟩)

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A cover by DM open substacks is DM.** An open substack `𝒲` of `𝒳` every object of which
lies, locally on a flat and locally finitely presented cover of its base, in a DM member of a
set `s` of open substacks of `𝒳`, is DM.

DM-ness over `S` is read off the relative diagonal at the diagonal points
(`AlgebraicGeometry.Stack.isDM_of_hasPropertyAtDiagonalPoints`), that test is local on the cover
(`AlgebraicGeometry.Stack.hasPropertyAtDiagonalPoints_of_cover`), and **Stacks 050N** passes
between DM over `S` and DM. -/
theorem isAbsolutelyDM_of_cover (W : OpenSubstack 𝒳) (s : Set (OpenSubstack 𝒳))
    (hcov : ∀ (T : BigFppfOver B S hS) (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj),
      y ⋙ 𝒳.val.val.p = Over.map T.hom → W.property (y.obj (Over.mk (𝟙 T.left))) →
      ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
          Flat (B.inclusion.map j.left) ∧ LocallyOfFinitePresentation (B.inclusion.map j.left) ∧
          t ∈ Set.range (B.inclusion.map j.left) ∧ ∃ U ∈ s, U.property (y.obj V))
    (hs : ∀ U ∈ s, AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  refine (AlgebraicStacks.isAbsolutelyDM_iff_isDMOver B S hS hZ _).mpr
    (isDM_of_hasPropertyAtDiagonalPoints B S hS _ ?_)
  exact hasPropertyAtDiagonalPoints_of_cover _ W s hcov fun U hU =>
    hasPropertyAtDiagonalPoints_of_isDM B S hS _
      ((AlgebraicStacks.isAbsolutelyDM_iff_isDMOver B S hS hZ _).mp (hs U hU))

/-- **A cover by quasi-DM open substacks is quasi-DM.** The quasi-DM twin of
`AlgebraicGeometry.Stack.isAbsolutelyDM_of_cover`. -/
theorem isAbsolutelyQuasiDM_of_cover (W : OpenSubstack 𝒳) (s : Set (OpenSubstack 𝒳))
    (hcov : ∀ (T : BigFppfOver B S hS) (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj),
      y ⋙ 𝒳.val.val.p = Over.map T.hom → W.property (y.obj (Over.mk (𝟙 T.left))) →
      ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
          Flat (B.inclusion.map j.left) ∧ LocallyOfFinitePresentation (B.inclusion.map j.left) ∧
          t ∈ Set.range (B.inclusion.map j.left) ∧ ∃ U ∈ s, U.property (y.obj V))
    (hs : ∀ U ∈ s, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack) :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W.toAlgebraicStack := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsStableUnderBaseChange :=
    Space.isLocallyQuasiFinite_isStableUnderBaseChange B S hS
  refine (AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver B S hS hZ _).mpr
    (isQuasiDM_of_hasPropertyAtDiagonalPoints B S hS _ ?_)
  exact hasPropertyAtDiagonalPoints_of_cover _ W s hcov fun U hU =>
    hasPropertyAtDiagonalPoints_of_isQuasiDM B S hS _
      ((AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver B S hS hZ _).mp (hs U hU))

/-- The covering hypothesis of `AlgebraicGeometry.Stack.isAbsolutelyDM_of_cover` holds for an
open substack every object of which already lies in a member of `s`: the cover is the identity. -/
theorem exists_flat_cover_mem_of_le_iSup (W : OpenSubstack 𝒳) (s : Set (OpenSubstack 𝒳))
    (hW : W.property ≤ ⨆ U : s, (U : OpenSubstack 𝒳).property)
    (T : BigFppfOver B S hS) (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
    (_hy : y ⋙ 𝒳.val.val.p = Over.map T.hom) (hyW : W.property (y.obj (Over.mk (𝟙 T.left))))
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
      Flat (B.inclusion.map j.left) ∧ LocallyOfFinitePresentation (B.inclusion.map j.left) ∧
      t ∈ Set.range (B.inclusion.map j.left) ∧ ∃ U ∈ s, U.property (y.obj V) := by
  obtain ⟨⟨U, hU⟩, hyU⟩ := (ObjectProperty.prop_iSup_iff _ _).1 (hW _ hyW)
  refine ⟨Over.mk (𝟙 T.left), 𝟙 _, ?_, ?_, ⟨t, rfl⟩, U, hU, hyU⟩
  · change Flat (B.inclusion.map (𝟙 T.left))
    rw [B.inclusion.map_id]
    infer_instance
  · change LocallyOfFinitePresentation (B.inclusion.map (𝟙 T.left))
    rw [B.inclusion.map_id]
    infer_instance

/-- The covering hypothesis of `AlgebraicGeometry.Stack.isAbsolutelyDM_of_cover` holds for an
open substack every point seen by an object of which lies in the union of the point sets of the
members of `s`: around each point the cover is an open subscheme of the base on which the object
lies in one member
(`AlgebraicGeometry.Stack.OpenSubstack.exists_isOpenImmersion_property_of_pointsWithin_iUnion`). -/
theorem exists_flat_cover_mem_of_le_pointsWithin (W : OpenSubstack 𝒳) (s : Set (OpenSubstack 𝒳))
    (hW : W.property ≤ pointsWithin 𝒳 (⋃ U : s, (U : OpenSubstack 𝒳).pointSet B S hS))
    (T : BigFppfOver B S hS) (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map T.hom) (hyW : W.property (y.obj (Over.mk (𝟙 T.left))))
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
      Flat (B.inclusion.map j.left) ∧ LocallyOfFinitePresentation (B.inclusion.map j.left) ∧
      t ∈ Set.range (B.inclusion.map j.left) ∧ ∃ U ∈ s, U.property (y.obj V) := by
  obtain ⟨V, j, hj, ht, ⟨U, hU⟩, hyU⟩ :=
    OpenSubstack.exists_isOpenImmersion_property_of_pointsWithin_iUnion
      (fun U : s => (U : OpenSubstack 𝒳)) T y hy (hW _ hyW) t
  have : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map j.left) := hj
  exact ⟨V, j, inferInstance, inferInstance, ht, U, hU, hyU⟩

/-- For any set `s` of open substacks there is an open substack whose objects lie in the point
set union of `s` and which contains every member of `s`. -/
private theorem exists_openSubstack_le_pointsWithin_iUnion (s : Set (OpenSubstack 𝒳)) :
    ∃ W : OpenSubstack 𝒳,
      W.property ≤ pointsWithin 𝒳 (⋃ U : s, (U : OpenSubstack 𝒳).pointSet B S hS) ∧
        ∀ U ∈ s, U.property ≤ W.property := by
  have hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val)
      (⋃ U : s, (U : OpenSubstack 𝒳).pointSet B S hS) := by
    let := pointTopology B S hS 𝒳.val
    exact isOpen_iUnion fun U => (U : OpenSubstack 𝒳).isOpen_pointSet B S hS
  refine ⟨openSubstackOfPoints 𝒳 _ hΩ, (openSubstackOfPoints_property 𝒳 _ hΩ).le,
    fun U hU x hx => ?_⟩
  rw [openSubstackOfPoints_property]
  exact fun q φ => Set.mem_iUnion.2 ⟨⟨U, hU⟩, U.pointsWithin_pointSet B S hS hx q φ⟩

/-- **A union of DM open substacks is DM.** For a set `s` of DM open substacks of `𝒳`, the open
substack of `𝒳` whose points are the union of the point sets of the members of `s` is DM, and it
contains every member of `s`. This is the step the source's proof of **Stacks 0DSM** isolates:
"if `𝒰` and `𝒱` are DM open substacks, the open substack `𝒲` with `|𝒲| = |𝒰| ∪ |𝒱|` is DM". -/
theorem exists_isAbsolutelyDM_openSubstack_le (s : Set (OpenSubstack 𝒳))
    (hs : ∀ U ∈ s, AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack) :
    ∃ W : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyDM B S hS hZ W.toAlgebraicStack ∧
      ∀ U ∈ s, U.property ≤ W.property := by
  obtain ⟨W, hW, hle⟩ := exists_openSubstack_le_pointsWithin_iUnion s
  exact ⟨W, isAbsolutelyDM_of_cover hZ W s
    (exists_flat_cover_mem_of_le_pointsWithin W s hW) hs, hle⟩

/-- **A union of quasi-DM open substacks is quasi-DM.** The quasi-DM twin of
`AlgebraicGeometry.Stack.exists_isAbsolutelyDM_openSubstack_le`. -/
theorem exists_isAbsolutelyQuasiDM_openSubstack_le (s : Set (OpenSubstack 𝒳))
    (hs : ∀ U ∈ s, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack) :
    ∃ W : OpenSubstack 𝒳, AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ W.toAlgebraicStack ∧
      ∀ U ∈ s, U.property ≤ W.property := by
  obtain ⟨W, hW, hle⟩ := exists_openSubstack_le_pointsWithin_iUnion s
  exact ⟨W, isAbsolutelyQuasiDM_of_cover hZ W s
    (exists_flat_cover_mem_of_le_pointsWithin W s hW) hs, hle⟩

variable (B S hS)

/-- **The local-global step of Stacks 0DSM for DM, proved.** An open substack whose objects are
the union of the objects of a set of DM open substacks is DM. This is the proposition
`AlgebraicGeometry.Stack.IsAbsolutelyDMLocalOnOpenSubstacks`, the hypothesis `hLocalDM` of
`AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`. -/
theorem isAbsolutelyDMLocalOnOpenSubstacks :
    IsAbsolutelyDMLocalOnOpenSubstacks.{u, w} B S hS hZ :=
  fun _ s W hW hs => isAbsolutelyDM_of_cover hZ W s (exists_flat_cover_mem_of_le_iSup W s hW.le) hs

/-- **The local-global step of Stacks 0DSM for quasi-DM, proved.** This is the proposition
`AlgebraicGeometry.Stack.IsAbsolutelyQuasiDMLocalOnOpenSubstacks`, the hypothesis
`hLocalQuasiDM` of
`AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`. -/
theorem isAbsolutelyQuasiDMLocalOnOpenSubstacks :
    IsAbsolutelyQuasiDMLocalOnOpenSubstacks.{u, w} B S hS hZ :=
  fun _ s W hW hs =>
    isAbsolutelyQuasiDM_of_cover hZ W s (exists_flat_cover_mem_of_le_iSup W s hW.le) hs

variable (𝒳)

/-- **The DM locus is an open substack.** There is an open substack of `𝒳` whose objects are
exactly those of `AlgebraicGeometry.Stack.dmLocus`. This is the hypothesis `hOpenDM` of
`AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`,
proved: the union of all DM open substacks is DM
(`AlgebraicGeometry.Stack.exists_isAbsolutelyDM_openSubstack_le`), so it is itself one of the
open substacks the supremum runs over. -/
theorem exists_property_eq_dmLocus :
    ∃ W : OpenSubstack 𝒳, W.property = dmLocus B S hS hZ 𝒳 := by
  obtain ⟨W, hW, hle⟩ := exists_isAbsolutelyDM_openSubstack_le hZ
    {U : OpenSubstack 𝒳 | AlgebraicStacks.IsAbsolutelyDM B S hS hZ U.toAlgebraicStack}
    fun _ hU => hU
  exact ⟨W, le_antisymm (le_dmLocus B S hS hZ 𝒳 W hW) (iSup_le fun U => hle U.1 U.2)⟩

/-- **The quasi-DM locus is an open substack.** This is the hypothesis `hOpenQuasiDM` of
`AlgebraicGeometry.Stack.exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack`,
proved. -/
theorem exists_property_eq_quasiDMLocus :
    ∃ W : OpenSubstack 𝒳, W.property = quasiDMLocus B S hS hZ 𝒳 := by
  obtain ⟨W, hW, hle⟩ := exists_isAbsolutelyQuasiDM_openSubstack_le hZ
    {U : OpenSubstack 𝒳 | AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ U.toAlgebraicStack}
    fun _ hU => hU
  exact ⟨W, le_antisymm (le_quasiDMLocus B S hS hZ 𝒳 W hW) (iSup_le fun U => hle U.1 U.2)⟩

/-- **Stacks 0DSM.** Let `𝒳` be an algebraic stack. There exist open substacks
`𝒳'' ⊆ 𝒳' ⊆ 𝒳` such that `𝒳''` is DM, `𝒳'` is quasi-DM, and these are the largest open
substacks with these properties.

Here `W''` is `𝒳''` and `W'` is `𝒳'`. DM and quasi-DM are the absolute notions of
**Stacks 050D**, parts (5) and (6), read over the terminal scheme `Spec ℤ`, which every big fppf
site contains (`AlgebraicGeometry.BigFppfSite.contains_terminal`); containment of open substacks
is containment of their objects. -/
@[stacks 0DSM]
theorem exists_nested_largest_isAbsolutelyDM_openSubstacks :
    ∃ W' W'' : OpenSubstack 𝒳,
      W''.property ≤ W'.property ∧
      AlgebraicStacks.IsAbsolutelyDM B S hS B.contains_terminal W''.toAlgebraicStack ∧
      AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal W'.toAlgebraicStack ∧
      (∀ V : OpenSubstack 𝒳,
        AlgebraicStacks.IsAbsolutelyDM B S hS B.contains_terminal V.toAlgebraicStack →
          V.property ≤ W''.property) ∧
      ∀ V : OpenSubstack 𝒳,
        AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal V.toAlgebraicStack →
          V.property ≤ W'.property :=
  exists_nested_largest_isAbsolutelyDM_isAbsolutelyQuasiDM_openSubstack B S hS
    B.contains_terminal 𝒳
    (isAbsolutelyDMLocalOnOpenSubstacks B S hS B.contains_terminal)
    (isAbsolutelyQuasiDMLocalOnOpenSubstacks B S hS B.contains_terminal)
    (exists_property_eq_dmLocus B S hS 𝒳 B.contains_terminal)
    (exists_property_eq_quasiDMLocus B S hS 𝒳 B.contains_terminal)

end AlgebraicGeometry.Stack

end
