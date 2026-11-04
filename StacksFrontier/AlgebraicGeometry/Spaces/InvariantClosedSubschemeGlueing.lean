module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Closed subspaces glued from invariant closed subschemes of a chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `φ : U ⟶ X` be a
surjective étale chart by an object `U` of the site. This file records the form of the
correspondence of Stacks 07TW between closed subspaces of `X` and closed subschemes of `U`
invariant under `R = U ×_X U` in which it is used to *glue* a closed subspace of `X` out of a
closed subscheme of the chart: with nothing assumed beyond invariance, the subfunctor
`AlgebraicGeometry.Space.invariantSubspace` cut out by an invariant closed subscheme `C ⊆ U` is a
closed subspace of `X` whose inverse image along `φ` is the functor of points of `C`, and a closed
subspace is determined by its inverse image along `φ`.

Invariance is stated for the chosen representing object of `U ×_X U`; since the relation is
only given up to isomorphism at the point of use, it is also characterised here against an
arbitrary cartesian square on `φ` with itself.

## Main results

* `AlgebraicGeometry.Space.isClosedSubspace_invariantSubspace`: the subspace cut out by an
  invariant closed subscheme of the chart is a closed subspace.
* `AlgebraicGeometry.Space.isInvariantSubscheme_iff_of_isPullback`: invariance read against any
  cartesian square presenting `U ×_X U`.
* `AlgebraicGeometry.Space.eq_of_preimage_eq_of_isClosedSubspace`: two closed subspaces with the
  same inverse image along the chart are equal.
* `AlgebraicGeometry.Space.exists_preimage_eq_subschemePoints`: the inverse image along the chart
  of a closed subspace is the functor of points of an invariant closed subscheme of the chart.
* `AlgebraicGeometry.Space.preimage_preimage_eq_subschemePoints_pullback`: inverse images along
  compatible charts of two spaces and along a morphism between them correspond to pullback of
  subschemes.
* `AlgebraicGeometry.Space.exists_isPullback_yoneda_of_preimage_eq`: a subscheme of the chart
  presenting the inverse image of a subfunctor is a chart of that subfunctor.

## Implementation notes

The closedness of the glued subspace is Stacks 03I2 at closed immersions, through
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_invariantSubspace`, whose descent input is
discharged by `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`.

## References

* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Glueing

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **An invariant closed subscheme of a chart glues to a closed subspace.** For a surjective
étale chart `φ : U ⟶ X` of an algebraic space and a closed subscheme `C ⊆ U` invariant under
`U ×_X U`, the subfunctor of `X` cut out by `C` is a closed subspace of `X`. -/
theorem isClosedSubspace_invariantSubspace (hX : IsAlgebraicSpace B S hS X)
    (C : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hC : AlgebraicGeometry.IsClosedImmersion C.arrow)
    (hinv : IsInvariantSubscheme B S hS hs C) :
    IsClosedSubspace B S hS (invariantSubspace B S hS φ C) :=
  isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX C inferInstance hC hinv

include hs in
/-- **Invariance against an arbitrary presentation of the relation.** If `t, s : R ⟶ U`
exhibit `R` as the fibre product `U ×_X U` of the chart with itself, a subscheme of `U` is
invariant exactly when its pullbacks along `t` and along `s` agree. -/
theorem isInvariantSubscheme_iff_of_isPullback {R : BigFppfOver B S hS} (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)
    (C : Subobject ((BigFppfOver.toScheme B S hS).obj U)) :
    IsInvariantSubscheme B S hS hs C ↔
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map t)).obj C =
        (Subobject.pullback ((BigFppfOver.toScheme B S hS).map s)).obj C := by
  have hch := isPullback_yoneda_map_atlasRelation B S hS hs
  let e : yoneda.obj R ≅ yoneda.obj (atlasRelation B S hS hs) := hR.isoIsPullback _ _ hch
  let ε : R ≅ atlasRelation B S hS hs := Yoneda.fullyFaithful.preimageIso e
  have hε : yoneda.map ε.hom = e.hom := Yoneda.fullyFaithful.map_preimage e.hom
  have ht : ε.hom ≫ atlasRelationTarget B S hS hs = t := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hε]
    exact hR.isoIsPullback_hom_fst _ _ hch
  have hsrc : ε.hom ≫ atlasRelationSource B S hS hs = s := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hε]
    exact hR.isoIsPullback_hom_snd _ _ hch
  let F := BigFppfOver.toScheme B S hS
  have hinj : Function.Injective (Subobject.pullback (F.map ε.hom)).obj := by
    intro A A' h
    have h' := congrArg (Subobject.pullback (F.map ε.inv)).obj h
    rwa [← Subobject.pullback_comp, ← Subobject.pullback_comp, ← F.map_comp, ε.inv_hom_id,
      F.map_id, Subobject.pullback_id, Subobject.pullback_id] at h'
  rw [← ht, ← hsrc, F.map_comp, F.map_comp, Subobject.pullback_comp, Subobject.pullback_comp]
  exact hinj.eq_iff.symm

include hs he in
/-- **A closed subspace is determined by its inverse image along a surjective étale chart.** -/
theorem eq_of_preimage_eq_of_isClosedSubspace (hX : IsAlgebraicSpace B S hS X)
    {W W' : Subfunctor X} (hW : IsClosedSubspace B S hS W) (hW' : IsClosedSubspace B S hS W')
    (h : W.preimage φ = W'.preimage φ) : W = W' := by
  have hloc : ∀ {V : Subfunctor X}, IsClosedSubspace B S hS V →
      IsLocallyClosedSubspace B S hS V := fun hV =>
    ⟨hV.1, MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage _ isClosedImmersion_le_isImmersion) _ hV.2⟩
  obtain ⟨Z, ⟨hZ, hZinv⟩, rfl⟩ := exists_invariantSubspace_eq B S hS hs he hX W (hloc hW)
  obtain ⟨Z', ⟨hZ', hZ'inv⟩, rfl⟩ := exists_invariantSubspace_eq B S hS hs he hX W' (hloc hW')
  rw [preimage_invariantSubspace B S hS hs Z hZinv,
    preimage_invariantSubspace B S hS hs Z' hZ'inv] at h
  rw [subschemePoints_injective B S hS hZ hZ' h]

include hs in
/-- **The chart of a closed subspace.** The inverse image along a surjective étale chart `φ` of a
closed subspace `W ⊆ X` is the functor of points of a closed subscheme of the chart, invariant
under `U ×_X U`. -/
theorem exists_preimage_eq_subschemePoints {W : Subfunctor X} (hW : IsClosedSubspace B S hS W) :
    ∃ C : Subobject ((BigFppfOver.toScheme B S hS).obj U),
      AlgebraicGeometry.IsClosedImmersion C.arrow ∧ IsInvariantSubscheme B S hS hs C ∧
        W.preimage φ = subschemePoints B S hS C := by
  have hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)) := hW.2.property_snd φ
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)) := inferInstance
  have hciψ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (hW.2.rep.snd (yoneda.map (atlasRelationTarget B S hS hs) ≫ φ))) := hW.2.property_snd _
  have hmonoψ : Mono ((BigFppfOver.toScheme B S hS).map
      (hW.2.rep.snd (yoneda.map (atlasRelationTarget B S hS hs) ≫ φ))) := inferInstance
  have hpres : (Subobject.underlyingIso
        ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ))).symm.hom ≫
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ))).arrow =
      (BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ) :=
    Subobject.underlyingIso_arrow _
  refine ⟨Subobject.mk ((BigFppfOver.toScheme B S hS).map (hW.2.rep.snd φ)), ?_, ?_, ?_⟩
  · exact (property_toScheme_map_iff_of_presentation B S hS _ _ hpres
      (@AlgebraicGeometry.IsClosedImmersion.{u})).1 hci
  · exact (pullback_obj_mk_snd B S hS φ hW.2.rep (atlasRelationTarget B S hS hs) _ rfl).trans
      (pullback_obj_mk_snd B S hS φ hW.2.rep (atlasRelationSource B S hS hs) _
        (yoneda_map_atlasRelationSource_comp B S hS hs)).symm
  · rw [subschemePoints_eq_range B S hS _ _ hpres]
    exact (range_yoneda_snd_eq_preimage B S hS φ hW.2.rep).symm

end Glueing

section BaseChange

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U U' : BigFppfOver B S hS}

/-- **Inverse images along compatible charts.** Let `φ : U ⟶ X` and `φ' : U' ⟶ X'` be charts
and let `π : X' ⟶ X` and `m : U' ⟶ U` commute with them. If the inverse image of `W ⊆ X` along
`φ` is the functor of points of `C ⊆ U`, then the inverse image of `π⁻¹W` along `φ'` is the
functor of points of the pullback of `C` along `m`. -/
theorem preimage_preimage_eq_subschemePoints_pullback {φ : yoneda.obj U ⟶ X}
    {φ' : yoneda.obj U' ⟶ X'} (π : X' ⟶ X) (m : U' ⟶ U) (hm : yoneda.map m ≫ φ = φ' ≫ π)
    {W : Subfunctor X} {C : Subobject ((BigFppfOver.toScheme B S hS).obj U)}
    (hWC : W.preimage φ = subschemePoints B S hS C) :
    (W.preimage π).preimage φ' =
      subschemePoints B S hS
        ((Subobject.pullback ((BigFppfOver.toScheme B S hS).map m)).obj C) := by
  rw [subschemePoints_pullback, ← hWC, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp,
    hm]

/-- **A subscheme presenting the inverse image of a subfunctor is a chart of it.** If the inverse
image along `φ : U ⟶ X` of a subfunctor `W ⊆ X` is the functor of points of an immersed
subscheme `C ⊆ U`, presented by a morphism `i : V ⟶ U` of the site, then `V` maps to `W` and the
square formed with `i`, the inclusion of `W` and `φ` is cartesian. -/
theorem exists_isPullback_yoneda_of_preimage_eq {φ : yoneda.obj U ⟶ X} {W : Subfunctor X}
    {C : Subobject ((BigFppfOver.toScheme B S hS).obj U)}
    (hWC : W.preimage φ = subschemePoints B S hS C) {V : BigFppfOver B S hS} (i : V ⟶ U)
    (e : (BigFppfOver.toScheme B S hS).obj V ≅ (C : Scheme.{u}))
    (hei : e.hom ≫ C.arrow = (BigFppfOver.toScheme B S hS).map i) :
    ∃ k : yoneda.obj V ⟶ W.toFunctor, IsPullback k (yoneda.map i) W.ι φ := by
  have hmono : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (mono_toScheme_map_of_presentation B S hS i e hei)
  have key : W.preimage φ = Subfunctor.range (yoneda.map i) :=
    hWC.trans (subschemePoints_eq_range B S hS i e hei)
  have hkι : Subfunctor.lift (yoneda.map i) key.ge ≫ (W.preimage φ).ι = yoneda.map i :=
    Subfunctor.lift_ι _ _
  have hkiso := Subfunctor.isIso_lift key.ge key.le
  have h₁ := Subfunctor.isPullback_fromPreimage W φ
  refine ⟨Subfunctor.lift (yoneda.map i) key.ge ≫ W.fromPreimage φ, ?_⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, W.fromPreimage_ι φ, ← Category.assoc, hkι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) key.ge) ≪≫ h₁.isoPullback) ?_ ?_
  · simp [h₁.isoPullback_hom_fst]
  · simp [h₁.isoPullback_hom_snd, hkι]

end BaseChange

end AlgebraicGeometry.Space

end
