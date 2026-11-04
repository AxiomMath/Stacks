module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.NowhereDenseImage
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.SuitableAffineOpens

/-!
# Finiteness over a dense open

A quasi-finite morphism of schemes becomes finite after restriction over a dense open subscheme
of its target, and so does a morphism locally of finite type whose inverse image of the generic
points of the target is exactly the finite set of generic points of the source, provided it is
quasi-compact or separated.

## Main results

* `AlgebraicGeometry.exists_dense_open_isFinite_of_quasiFinite`: **Stacks 03I1**, which is also
  **Stacks 03HZ**. A quasi-finite morphism of schemes is finite over a dense open subscheme of
  its target.
* `AlgebraicGeometry.exists_dense_open_isFinite`: **Stacks 0BAI.** A morphism locally of finite
  type carrying precisely the generic points of its source to the generic points of its target is
  finite over a dense open of the target, if it is quasi-compact or separated.

## Implementation notes

Quasi-finiteness is represented, as in
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/Defs.lean`, by the typeclasses
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.LocallyQuasiFinite` and
`AlgebraicGeometry.QuasiCompact`. Restriction over an open subscheme is Mathlib's morphism
restriction `f ∣_ U`.

Finiteness is Zariski local on the target, so a morphism finite over each member of a family of
opens is finite over their supremum. That is what reduces the statement to an affine target and,
inside that case, what assembles the neighbourhoods of the generic points. The locality is
`Stacks.Morphisms.isFinite_isZariskiLocalAtTarget` rather than instance synthesis, which cannot
solve for the affine-target parameter of `AlgebraicGeometry.HasAffineProperty` here.

Over an affine target the source is quasi-compact, so Tag 03J1,
`AlgebraicGeometry.exists_dense_open_isSeparated`, provides a separated dense open `V` of the
source. Its complement is closed nowhere dense, hence so is the closure of its image by Tag 03J2,
`AlgebraicGeometry.isNowhereDense_image_of_quasiFinite`; the complement `W` of that closure is a
dense open of the target over which the morphism is separated, because its source is an open
subscheme of `V`. Over `W` the morphism is quasi-finite and separated, so each generic point has
an affine open neighbourhood over which it is finite, by Tag 02NW,
`AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict`, and these
neighbourhoods cover a dense open since the generic points are dense.

Tag 0BAI uses its two alternative hypotheses in genuinely different ways, and both branches live
here because the separated branch shares
`exists_dense_open_isFinite_of_near_genericPoints` with Tag 03I1.  In the quasi-compact case the
locus where the morphism fails to be quasi-finite is a closed subscheme missing every point above
a generic point of the target, so Tag 02NE,
`AlgebraicGeometry.exists_open_nhds_disjoint_range_of_quasiCompact`, shrinks the target until the
morphism is locally quasi-finite, and Tag 03I1 above then finishes.  In the separated case one
works one generic point at a time: the fibre there is finite, so by Tag 02NW the morphism is
finite between suitable affine charts, and separatedness makes the inclusion of the chosen source
chart proper, which forces the whole inverse image of a small enough target neighbourhood into
that chart.

Tag 0BAI is placed in this module rather than beside its section neighbour Tag 02NW in
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/GenericallyFinite.lean` because Tag 03I1,
which its quasi-compact branch consumes, is proved here and this module imports that one.

## References

* [Stacks Project, Tag 0BAI](https://stacks.math.columbia.edu/tag/0BAI)
* [Stacks Project, Tag 02NE](https://stacks.math.columbia.edu/tag/02NE)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 03HZ](https://stacks.math.columbia.edu/tag/03HZ)
* [Stacks Project, Tag 03I1](https://stacks.math.columbia.edu/tag/03I1)
* [Stacks Project, Tag 03J1](https://stacks.math.columbia.edu/tag/03J1)
* [Stacks Project, Tag 03J2](https://stacks.math.columbia.edu/tag/03J2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Neither of these synthesizes at this Mathlib pin: the affine-target parameter of
-- `AlgebraicGeometry.HasAffineProperty` for `AlgebraicGeometry.IsFinite` cannot be solved for
-- without reducibility settings this development does not use. Restating them here, as in
-- `StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/BaseChangeDecomposition.lean`, makes them
-- available to instance search.
private instance isZariskiLocalAtTarget_isFinite :
    IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
  Stacks.Morphisms.isFinite_isZariskiLocalAtTarget

private instance : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  isZariskiLocalAtTarget_isFinite.toRespects

/-- Finiteness being Zariski local on the target, a morphism finite over each member of a family
of opens is finite over their supremum. -/
private lemma isFinite_restrict_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (W : ι → Y.Opens) (h : ∀ i, IsFinite (f ∣_ W i)) :
    IsFinite (f ∣_ ⨆ i, W i) := by
  classical
  let V : Y.Opens := ⨆ i, W i
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) (fun i => V.ι ⁻¹ᵁ W i)
  · calc
      ⨆ i, V.ι ⁻¹ᵁ W i = V.ι ⁻¹ᵁ V := (Scheme.Hom.preimage_iSup V.ι W).symm
      _ = ⊤ := V.ι_preimage_self
  · intro i
    have hEq : V.ι ''ᵁ (V.ι ⁻¹ᵁ W i) = W i := by
      simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right] using (le_iSup W i)
    let e : Arrow.mk ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ W i)) ≅ Arrow.mk (f ∣_ W i) :=
      morphismRestrictRestrict f V (V.ι ⁻¹ᵁ W i) ≪≫ morphismRestrictEq f hEq
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr (h i)

/-- The supremum of opens, each containing a generic point of the target, is dense. -/
private lemma dense_iSup_of_mem_genericPoints {Y : Scheme.{u}} (W : genericPoints Y → Y.Opens)
    (h : ∀ η, η.1 ∈ W η) : Dense ((⨆ η, W η : Y.Opens) : Set Y) := by
  apply (dense_iff_closure_eq.mpr (genericPoints.closure (α := Y))).mono
  intro η hη
  exact (le_iSup W ⟨η, hη⟩) (h ⟨η, hη⟩)

/-- The generic points being dense, a morphism finite over a neighbourhood of each generic point
of its target is finite over a dense open. -/
private lemma exists_dense_open_isFinite_of_near_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hnear : ∀ η : genericPoints Y, ∃ W : Y.Opens, η.1 ∈ W ∧ IsFinite (f ∣_ W)) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := by
  classical
  let W (η : genericPoints Y) : Y.Opens := (hnear η).choose
  exact ⟨⨆ η : genericPoints Y, W η,
    dense_iSup_of_mem_genericPoints W fun η => (hnear η).choose_spec.1,
    isFinite_restrict_iSup f W fun η => (hnear η).choose_spec.2⟩

/-- A morphism finite over a dense open of a dense open of the target is finite over a dense open
of the target. -/
private lemma exists_dense_open_isFinite_of_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Y.Opens) (hW : Dense (W : Set Y)) (T : W.toScheme.Opens)
    (hT : Dense (T : Set W.toScheme)) (h : IsFinite ((f ∣_ W) ∣_ T)) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := by
  refine ⟨W.ι ''ᵁ T, ?_, (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f W T)).mp h⟩
  have hWrange : DenseRange W.ι := by rwa [DenseRange, Scheme.Opens.range_ι]
  simpa only [Scheme.Hom.coe_image] using hWrange.dense_image W.ι.continuous hT

/-- A quasi-finite morphism to an affine scheme is finite over a dense open subscheme of its
target. -/
private lemma exists_dense_open_isFinite_of_isAffine_target {Y X : Scheme.{u}} (f : Y ⟶ X)
    [IsAffine X] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f] :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U) := by
  classical
  have hYcompact : IsCompact (Set.univ : Set Y) := by
    simpa only [Scheme.Hom.preimage_top, TopologicalSpace.Opens.coe_top] using
      Scheme.Hom.isCompact_preimage f (show IsCompact ((⊤ : X.Opens) : Set X) from isCompact_univ)
  let : CompactSpace Y := isCompact_univ_iff.mp hYcompact
  obtain ⟨V, hVdense, hVsep⟩ := exists_dense_open_isSeparated Y
  have hDnd : IsNowhereDense ((V : Set Y)ᶜ) :=
    (isClosed_isNowhereDense_iff_compl.mpr ⟨by simpa using V.2, by simpa using hVdense⟩).2
  let W : X.Opens := ⟨(closure (f.base '' (V : Set Y)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩
  have hWdense : Dense (W : Set X) :=
    (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure,
      (isNowhereDense_image_of_quasiFinite f _ V.2.isClosed_compl hDnd).closure⟩).2
  have hpreV : f ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra hyV
    exact hy (subset_closure ⟨y, hyV, rfl⟩)
  -- The source of `f ∣_ W` is an open subscheme of the separated scheme `V`, hence separated.
  have : IsSeparated (f ∣_ W) := by
    let j : (f ⁻¹ᵁ W).toScheme ⟶ V.toScheme := Y.homOfLE hpreV
    have : IsOpenImmersion j := inferInstance
    have hterm : IsSeparated (terminal.from (f ⁻¹ᵁ W).toScheme) := by
      simpa only [terminalIsTerminal.hom_ext (terminal.from (f ⁻¹ᵁ W).toScheme)
        (j ≫ terminal.from V.toScheme)] using
        (show IsSeparated (j ≫ terminal.from V.toScheme) from inferInstance)
    have : Scheme.IsSeparated (f ⁻¹ᵁ W).toScheme := ⟨hterm⟩
    infer_instance
  have hnear : ∀ η : genericPoints W.toScheme,
      ∃ T : W.toScheme.Opens, η.1 ∈ T ∧ IsFinite ((f ∣_ W) ∣_ T) := by
    intro η
    obtain ⟨T, hηT, hfinite⟩ :=
      (finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict (f ∣_ W) η.1 η.2).mp
        ((locallyQuasiFinite_iff_finite_preimage_singleton (f := f ∣_ W)).mp inferInstance η.1)
    exact ⟨T.1, hηT, hfinite⟩
  obtain ⟨T, hTdense, hTfinite⟩ := exists_dense_open_isFinite_of_near_genericPoints (f ∣_ W) hnear
  exact exists_dense_open_isFinite_of_restrict f W hWdense T hTdense hTfinite

/-- A dense open of an open subscheme has image dense in that open subscheme. -/
private lemma dense_open_image_subset_closure {X : Scheme.{u}} (A : X.Opens)
    (V : A.toScheme.Opens) (hV : Dense (V : Set A.toScheme)) :
    (A : Set X) ⊆ closure (A.ι ''ᵁ V : X.Opens) := by
  simpa only [hV.closure_eq, Set.image_univ, Scheme.Opens.range_ι, Scheme.Hom.coe_image] using
    image_closure_subset_closure_image A.ι.continuous (s := (V : Set A.toScheme))

/-- **Stacks Project, Tag 03I1.** A quasi-finite morphism of schemes is finite over a dense open
subscheme of its target. This is also the statement of [Stacks Project, Tag 03HZ], the remark
offering it as an alternative to [Stacks Project, Tag 02NW] and deferring its proof to here. -/
@[stacks 03I1, stacks 03HZ "the whole content of the remark: the alternative to Tag 02NW that it
states, namely that a quasi-finite morphism is finite over a dense open of the target, whose proof
the remark defers to Tag 03I1"]
theorem exists_dense_open_isFinite_of_quasiFinite {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f] :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U) := by
  classical
  have hUlocal (A : X.affineOpens) :
      ∃ V : A.1.toScheme.Opens, Dense (V : Set A.1.toScheme) ∧
        IsFinite ((f ∣_ (A : X.Opens)) ∣_ V) := by
    let : IsAffine A.1.toScheme := A.2
    exact exists_dense_open_isFinite_of_isAffine_target (f ∣_ (A : X.Opens))
  let Ulocal (A : X.affineOpens) : X.Opens := A.1.ι ''ᵁ (hUlocal A).choose
  refine ⟨⨆ A : X.affineOpens, Ulocal A, ?_, isFinite_restrict_iSup f Ulocal fun A => ?_⟩
  · refine dense_iff_closure_eq.mpr (Set.eq_univ_iff_forall.mpr fun x => ?_)
    obtain ⟨A, hxA⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ (⨆ A : X.affineOpens, (A : X.Opens)) from by rw [iSup_affineOpens_eq_top]; simp)
    exact closure_mono (le_iSup Ulocal A)
      (dense_open_image_subset_closure A.1 _ (hUlocal A).choose_spec.1 hxA)
  · exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f A.1 (hUlocal A).choose)).mp (hUlocal A).choose_spec.2

/-- A generic point of an irreducible component has an open neighbourhood whose closure is that
component and which contains no other generic point, namely the complement of the union of the
remaining components. -/
@[sga "1 IV 6.3" "special case"]
private lemma exists_open_component_neighborhood {Y : Scheme.{u}}
    (hY : (genericPoints Y).Finite) (η : genericPoints Y) :
    ∃ V : Y.Opens, (η : Y) ∈ V ∧ closure (V : Set Y) = closure ({η.1} : Set Y) ∧
      ∀ ξ : genericPoints Y, ξ.1 ∈ V → ξ = η := by
  have : Finite (genericPoints Y) := hY.to_subtype
  have : Finite (irreducibleComponents Y) := Finite.of_equiv _ (genericPoints.equiv)
  have hc : (irreducibleComponents Y).Finite := Set.toFinite _
  let s : Set Y := ⋃₀ (irreducibleComponents Y \ {closure {η.1}})
  have hs : IsClosed s := by
    dsimp [s]
    rw [Set.sUnion_eq_biUnion]
    exact hc.sdiff.isClosed_biUnion fun Z hZ =>
      isClosed_of_mem_irreducibleComponents Z hZ.1
  let V : Y.Opens := ⟨sᶜ, hs.isOpen_compl⟩
  refine ⟨V, ?_, ?_, ?_⟩
  · change η.1 ∉ s
    intro h
    obtain ⟨Z, hZ, hηZ⟩ := h
    have hsub : closure ({η.1} : Set Y) ⊆ Z :=
      closure_minimal (Set.singleton_subset_iff.mpr hηZ)
        (isClosed_of_mem_irreducibleComponents Z hZ.1)
    have heq : Z = closure ({η.1} : Set Y) :=
      Set.Subset.antisymm (η.2.2 hZ.1.1 hsub) hsub
    exact hZ.2 (by simp [heq])
  · exact closure_sUnion_irreducibleComponents_sdiff_singleton hc _ η.2
  · intro ξ hξ
    have hsub : closure ({ξ.1} : Set Y) ⊆ closure (V : Set Y) :=
      closure_mono (Set.singleton_subset_iff.mpr hξ)
    change closure ({ξ.1} : Set Y) ⊆ closure sᶜ at hsub
    dsimp [s] at hsub
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton hc _ η.2] at hsub
    have heq : closure ({ξ.1} : Set Y) = closure ({η.1} : Set Y) :=
      Set.Subset.antisymm hsub (ξ.2.2 η.2.1 hsub)
    apply genericPoints.component_injective
    exact Subtype.ext heq

/-- If a separated morphism is finite between chosen opens of the source and the target, the
inclusion of the chosen source open into the whole inverse image of the target open is proper. -/
private lemma proper_open_inclusion_of_finite_res {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)
    [IsFinite (f.resLE V U e)] : IsProper (X.homOfLE e) := by
  have : IsSeparated (f ∣_ V) := inferInstance
  have : IsProper ((X.homOfLE e) ≫ (f ∣_ V)) := by
    change IsProper (f.resLE V U e)
    infer_instance
  exact IsProper.of_comp (X.homOfLE e) (f ∣_ V)

/-- An open of a scheme is contained in a sub-open with proper inclusion as soon as it contains
only generic points already lying in that sub-open: the image of a proper inclusion is closed and
the generic points are dense. -/
private lemma open_le_of_proper_inclusion_generic {X : Scheme.{u}} (U T₀ T : X.Opens)
    (e : U ≤ T₀) (eT : T ≤ T₀) [IsProper (X.homOfLE e)]
    (hgeneric : ∀ η : X, η ∈ genericPoints X → η ∈ T → η ∈ U) : T ≤ U := by
  have hclosed : IsClosed (Set.range (X.homOfLE e)) :=
    (X.homOfLE e).isClosedMap.isClosed_range
  have hd : Dense (T.ι ⁻¹' genericPoints X) :=
    (dense_iff_closure_eq.mpr (genericPoints.closure (α := X))).preimage
      T.ι.isOpenEmbedding.isOpenMap
  have hsub : T.ι ⁻¹' genericPoints X ⊆
      (X.homOfLE eT) ⁻¹' Set.range (X.homOfLE e) := by
    intro x hx
    refine ⟨⟨x.1, hgeneric x.1 hx x.2⟩, ?_⟩
    exact Subtype.ext ((Scheme.homOfLE_apply e _).trans (Scheme.homOfLE_apply eT x).symm)
  intro x hx
  have hrange : (X.homOfLE eT) ⟨x, hx⟩ ∈ Set.range (X.homOfLE e) := by
    have hcl : closure (T.ι ⁻¹' genericPoints X) ⊆
        (X.homOfLE eT) ⁻¹' Set.range (X.homOfLE e) := by
      simpa only [(hclosed.preimage (X.homOfLE eT).continuous).closure_eq]
        using closure_mono hsub
    exact hcl (hd ⟨x, hx⟩)
  obtain ⟨u, hu⟩ := hrange
  have heq : x = u.1 := by
    have heq := congrArg Subtype.val hu.symm
    exact (Scheme.homOfLE_apply eT ⟨x, hx⟩).symm.trans
      (heq.trans (Scheme.homOfLE_apply e u))
  exact heq ▸ u.2

/-- A morphism finite between chosen opens is finite over any smaller target open whose entire
inverse image is contained in the chosen source open, the restriction being a base change. -/
private lemma finite_restrict_of_finite_on_source_open {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V)
    [IsFinite (f.resLE V U e)] (W : Y.Opens) (hWV : W ≤ V)
    (hTU : f ⁻¹ᵁ W ≤ U) : IsFinite (f ∣_ W) := by
  have H : IsPullback (X.homOfLE hTU) (f ∣_ W)
      (f.resLE V U e) (Y.homOfLE hWV) := by
    apply (IsOpenImmersion.isPullback (f ∣_ W) (X.homOfLE hTU)
      (Y.homOfLE hWV) (f.resLE V U e) ?_ ?_).flip
    · apply (cancel_mono V.ι).mp
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
        Scheme.homOfLE_ι, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.homOfLE_ι]
    · ext x
      simp only [Scheme.opensRange_homOfLE, Opens.map_coe, Set.mem_preimage,
        SetLike.mem_coe]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        Scheme.Hom.resLE_comp_ι]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
    H inferInstance

/-- A separated morphism locally of finite type whose inverse image of the generic points of the
target is the finite set of generic points of the source is finite over some open neighbourhood
of each generic point of the target. -/
private lemma finite_near_generic_of_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f]
    (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite)
    (hgeneric : f ⁻¹' genericPoints Y = genericPoints X)
    (η : genericPoints Y) :
    ∃ W : Y.Opens, η.1 ∈ W ∧ IsFinite (f ∣_ W) := by
  have hfib : (f ⁻¹' {η.1}).Finite := hX.subset (by
    intro x hx
    rw [← hgeneric]
    simp [show f x = η.1 by simpa using hx])
  obtain ⟨V, U, hUV, hηV, hfibU, hfin⟩ :=
    (finite_preimage_singleton_iff_exists_affine_opens_isFinite f η.1 η.2).mp hfib
  obtain ⟨V₀, hηV₀, hcl, huniq⟩ := exists_open_component_neighborhood hY η
  let W : Y.Opens := V.1 ⊓ V₀
  have hWV : W ≤ V.1 := inf_le_left
  have hTW : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V.1 := f.preimage_mono hWV
  have : IsFinite (f.resLE V.1 U.1 hUV) := hfin
  have : IsProper (X.homOfLE hUV) :=
    proper_open_inclusion_of_finite_res f V.1 U.1 hUV
  have hTU : f ⁻¹ᵁ W ≤ U.1 :=
    open_le_of_proper_inclusion_generic U.1 (f ⁻¹ᵁ V.1) (f ⁻¹ᵁ W)
      hUV hTW (by
        intro ξ hξ hξW
        have hξtarget : f ξ ∈ genericPoints Y := by rw [← hgeneric] at hξ; exact hξ
        have hξV₀ : f ξ ∈ V₀ := hξW.2
        have hfη : f ξ = η.1 := congrArg Subtype.val
          (huniq ⟨f ξ, hξtarget⟩ hξV₀)
        exact hfibU (by simp [Set.mem_preimage, hfη]))
  exact ⟨W, ⟨hηV, hηV₀⟩,
    finite_restrict_of_finite_on_source_open f V.1 U.1 hUV W hWV hTU⟩

/-- A morphism locally of finite type whose inverse image of the generic points of the target is
the set of generic points of the source is quasi-finite at every point above a generic point. -/
private lemma quasiFiniteAt_of_maps_to_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (hgeneric : f ⁻¹' genericPoints Y = genericPoints X)
    (η : genericPoints Y) (x : X) (hx : f x = η.1) : f.QuasiFiniteAt x := by
  have hfiber : f ⁻¹' {η.1} ⊆ genericPoints X := by
    rw [← hgeneric]
    intro z hz
    change f z = η.1 at hz
    simp [Set.mem_preimage, hz]
  have hqf : ∀ x : X, f x = η.1 → quasiFiniteAt f x :=
    ((quasiFiniteAt_over_genericPoint_tfae f η.1 η.2).out 1 2).mp hfiber
  exact (hqf x hx).2

/-- The restriction of a morphism locally of finite type over an open whose inverse image lies in
the quasi-finite locus is locally quasi-finite. -/
private lemma locallyQuasiFinite_restrict_of_preimage_le_quasiFiniteLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V : Y.Opens) (hV : f ⁻¹ᵁ V ≤ f.quasiFiniteLocus) :
    LocallyQuasiFinite (f ∣_ V) := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  apply top_le_iff.mp
  intro x hx
  change (f ∣_ V).QuasiFiniteAt x
  have hqx : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := hV x.2
  have hh : ((f ⁻¹ᵁ V).ι ≫ f).QuasiFiniteAt x :=
    (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion).2 hqx
  rw [← morphismRestrict_ι] at hh
  exact (Scheme.Hom.quasiFiniteAt_comp_iff (g := V.ι)).mp hh

/-- A quasi-compact morphism locally of finite type whose inverse image of the generic points of
the target is the set of generic points of the source is locally quasi-finite over a dense open:
the complement of the quasi-finite locus is a closed subscheme missing every point above a
generic point, so it can be shrunk away near each of them. -/
private lemma exists_dense_open_locallyQuasiFinite_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hgeneric : f ⁻¹' genericPoints Y = genericPoints X) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ LocallyQuasiFinite (f ∣_ V) := by
  classical
  let Q : X.Opens := f.quasiFiniteLocus
  let Z : Closeds X := ⟨(Q : Set X)ᶜ, Q.2.isClosed_compl⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  have : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have hnear (η : genericPoints Y) :
      ∃ W : Y.Opens, η.1 ∈ W ∧ (I.subschemeι ≫ f) ⁻¹ᵁ W = ⊥ := by
    apply exists_open_nhds_disjoint_range_of_quasiCompact
      (I.subschemeι ≫ f) η.1 η.2
    rintro ⟨i, hi⟩
    have hiZ : I.subschemeι i ∈ Z := by
      have hiI : I.subschemeι i ∈ (I.support : Set X) := by
        rw [← I.range_subschemeι]
        exact ⟨i, rfl⟩
      simpa only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        SetLike.mem_coe] using hiI
    have hfx : f (I.subschemeι i) = η.1 := by simpa only [Scheme.Hom.comp_apply] using hi
    have hiQ : I.subschemeι i ∈ Q :=
      quasiFiniteAt_of_maps_to_genericPoint f hgeneric η _ hfx
    exact hiZ hiQ
  let W (η : genericPoints Y) : Y.Opens := (hnear η).choose
  have hWQ (η : genericPoints Y) : f ⁻¹ᵁ W η ≤ Q := by
    intro x hx
    by_contra hn
    have hxZ : x ∈ Z := hn
    have hxI : x ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      simpa only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        SetLike.mem_coe] using hxZ
    obtain ⟨i, rfl⟩ := hxI
    have hi : i ∈ (I.subschemeι ≫ f) ⁻¹ᵁ W η := hx
    rw [(hnear η).choose_spec.2] at hi
    exact hi
  let V : Y.Opens := ⨆ η : genericPoints Y, W η
  have hd : Dense (V : Set Y) :=
    dense_iSup_of_mem_genericPoints W fun η => (hnear η).choose_spec.1
  have hVQ : f ⁻¹ᵁ V ≤ Q := by
    rw [Scheme.Hom.preimage_iSup]
    exact iSup_le hWQ
  exact ⟨V, hd, locallyQuasiFinite_restrict_of_preimage_le_quasiFiniteLocus f V hVQ⟩

/-- **Stacks 0BAI.** A locally finite type morphism carrying precisely the generic points of its
source to the generic points of its target is finite over a dense open of the target, if it is
quasi-compact or separated. -/
@[stacks 0BAI]
theorem exists_dense_open_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite)
    (hgeneric : f ⁻¹' genericPoints Y = genericPoints X)
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := by
  rcases hqc_or_sep with hqc | hsep
  · have : QuasiCompact f := hqc
    obtain ⟨V, hVdense, hVqf⟩ :=
      exists_dense_open_locallyQuasiFinite_of_quasiCompact f hgeneric
    have : LocallyQuasiFinite (f ∣_ V) := hVqf
    have : QuasiCompact (f ∣_ V) := inferInstance
    obtain ⟨W, hWdense, hWfinite⟩ := exists_dense_open_isFinite_of_quasiFinite (f ∣_ V)
    exact exists_dense_open_isFinite_of_restrict f V hVdense W hWdense hWfinite
  · have : IsSeparated f := hsep
    exact exists_dense_open_isFinite_of_near_genericPoints f
      (finite_near_generic_of_isSeparated f hX hY hgeneric)

end AlgebraicGeometry

end
