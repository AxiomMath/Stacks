module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact immersions of algebraic spaces are open in their scheme-theoretic image

Let `f : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and suppose `f` is quasi-compact. This file proves that the induced morphism from `Z`
to the scheme-theoretic image of `f` is an *open* immersion, and deduces that `f` factors as an
open immersion followed by a closed immersion.

The scheme-level statement is already available: a quasi-compact immersion of schemes is an open
immersion onto its scheme-theoretic image, which is `AlgebraicGeometry.isOpenImmersion_toImage`
(Stacks 01RG). Since being an open immersion is tested after every represented base change, and
is local on the target for the fppf topology, the whole problem is to see that the represented
base change of `f` along an étale chart of the image again has *full* scheme-theoretic image.

That is proved here by descent rather than by a direct comparison of ideal sheaves. Fix a
surjective étale chart `φ : U ⟶ C` of an algebraic space `C` and a quasi-compact immersion
`f : Z ⟶ C` whose scheme-theoretic image is all of `C`. The base change of `f` along `φ` is a
quasi-compact immersion `m` of schemes, and the scheme-theoretic image of `m` is a closed
subscheme of `U`. Its two pullbacks along the legs of the relation `R = U ×_C U` agree: both legs
are étale, hence flat, so by `AlgebraicGeometry.ker_pullback_snd_eq_comap` (Stacks 081I) each
pullback is the scheme-theoretic image of the corresponding base change of `m`, and the two base
changes agree because the two legs have the same composite with `φ`. So the subscheme is
invariant, and `AlgebraicGeometry.Space.invariantSubspace` of Stacks 07TW cuts out a closed
subspace of `C` through which `f` factors — the descent being available unconditionally at the
closed immersions through
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. Minimality of
the scheme-theoretic image of `f` then forces that closed subspace to be all of `C`, hence, the
functor of points of an immersed subscheme determining it, forces the scheme-theoretic image of
`m` to be all of `U`.

The factorization of a quasi-compact immersion is then immediate: the scheme-theoretic image is a
closed subspace of the target by Stacks 082X, the morphism to it is an open immersion, and the
morphism to its own scheme-theoretic image has full image, which is what the criterion above
needs.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_of_schemeTheoreticImageSubfunctor_eq_top`: a
  quasi-compact immersion of algebraic spaces whose scheme-theoretic image is the whole target is
  an open immersion.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top`: the
  morphism from an algebraic space to its scheme-theoretic image has full scheme-theoretic
  image.
* `AlgebraicGeometry.Space.isOpenImmersion_toSchemeTheoreticImage`: a quasi-compact immersion of
  algebraic spaces is an open immersion onto its scheme-theoretic image.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact`:
  **Stacks 081U.** A quasi-compact immersion of algebraic spaces factors as an open immersion
  followed by a closed immersion.

## Implementation notes

Of the four assertions of Stacks 088G only the first is proved here, and only under
quasi-compactness of the immersion: the source states it for an immersion which is quasi-compact
*or* has reduced source, and asserts in addition that the range of the induced morphism is an
open subspace, that this open subspace is scheme-theoretically dense in the image, and that the
image of the points of the source is topologically dense. The reduced-source case and those three
further assertions are not proved here, which is why the attribute on
`AlgebraicGeometry.Space.isOpenImmersion_toSchemeTheoreticImage` names the part it covers; they
are proved, by étale localization rather than by descent, in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ImmersionSchemeTheoreticallyDenseOpen.lean`. No
part of Stacks 082Z — the étale localization of the scheme-theoretic image — is claimed either:
what is established is the invariance of one particular closed subscheme of one particular
chart, not an identification of scheme-theoretic images after base change.

Stacks 081U, on the other hand, is proved in full: its hypotheses are exactly that the morphism is
an immersion and quasi-compact, so the quasi-compact case of Stacks 088G discharges it completely.
The factorization is stated as the existence of an intermediate algebraic space together with the
two morphisms, their properties, and the equation identifying their composite with the given
morphism; no closure is chosen in the statement, and the intermediate space produced by the proof
is the scheme-theoretic image.

The invariance argument is stated for an arbitrary representable morphism into the chart's target
rather than for the scheme-theoretic image alone, because the comparison of the two base changes,
`AlgebraicGeometry.Space.exists_isPullback_snd_comp`, is already available at that generality.

## References

* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The pullback, as a subobject, of the closed subscheme cut out by a quasi-coherent ideal is
the closed subscheme cut out by the inverse image of that ideal. -/
@[ega "I 4.4.1" "Closed case"]
private theorem Scheme.IdealSheafData.pullback_obj_mk_subschemeι {X Y : Scheme.{u}}
    (I : Y.IdealSheafData) (g : X ⟶ Y) :
    (Subobject.pullback g).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap g).subschemeι := by
  have hfac : (I.comapIso g).hom ≫ (pullbackSymmetry g I.subschemeι).hom ≫
      pullback.snd I.subschemeι g = (I.comap g).subschemeι := by
    rw [pullbackSymmetry_hom_comp_snd]
    exact Scheme.IdealSheafData.comapIso_hom_fst I g
  rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback I.subschemeι g)]
  refine Subobject.mk_eq_mk_of_comm _ _
    (I.comapIso g ≪≫ pullbackSymmetry g I.subschemeι).symm ?_
  rw [← hfac]
  simp

/-- A morphism which factors through a monomorphism factors through the subobject that the
monomorphism determines. -/
private theorem mk_factors_of_eq_comp {W Y Z : Scheme.{u}} (i : Z ⟶ Y) [Mono i] {k : W ⟶ Y}
    {l : W ⟶ Z} (h : l ≫ i = k) : (Subobject.mk i).Factors k :=
  h ▸ Subobject.factors_of_factors_right l (Subobject.mk_factors_self i)

/-- A subobject through which the identity factors is the whole object: its inclusion is a split
epimorphism, and a split epimorphism which is a monomorphism is an isomorphism. -/
private theorem isIso_of_mk_factors_id {Y Z : Scheme.{u}} (i : Z ⟶ Y) [Mono i]
    (h : (Subobject.mk i).Factors (𝟙 Y)) : IsIso i := by
  obtain ⟨g, hg⟩ : ∃ g : Y ⟶ Z, g ≫ i = 𝟙 Y := (Subobject.mk_factors_iff i (𝟙 Y)).mp h
  refine ⟨⟨g, ?_, hg⟩⟩
  exact (cancel_mono i).mp (by rw [Category.assoc, hg, Category.comp_id, Category.id_comp])

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Invariance of the scheme-theoretic image of a chart base change -/

section Invariance

variable {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a quasi-compact representable morphism `f` into `X`, the scheme-theoretic image of the
base change of `f` along a chart `p` pulls back, along a flat morphism `r` of the site over that
chart, to the scheme-theoretic image of the base change of `f` along `r ≫ p`.

Both base changes of `f` are compared through
`AlgebraicGeometry.Space.exists_isPullback_snd_comp`, and the scheme-theoretic images are then
identified by flat base change of the defining ideal sheaf, Stacks 081I. -/
@[ega "IV 2.3.2" "more general"]
private theorem pullback_obj_mk_imageι_snd {f : G ⟶ X}
    (hf : yoneda.relativelyRepresentable f) {U R : BigFppfOver B S hS}
    (p : yoneda.obj U ⟶ X) (r : R ⟶ U) (ψ : yoneda.obj R ⟶ X)
    (hψ : yoneda.map r ≫ p = ψ)
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map r))
    (hqc : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (hf.snd p))) :
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
        (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hf.snd p)).imageι) =
      Subobject.mk ((BigFppfOver.toScheme B S hS).map (hf.snd ψ)).imageι := by
  have _hflat := hflat
  have _hqc := hqc
  obtain ⟨l, hsq⟩ := exists_isPullback_snd_comp B S hS hf p r ψ hψ
  have hcan : IsPullback
      (pullback.fst ((BigFppfOver.toScheme B S hS).map (hf.snd p))
        ((BigFppfOver.toScheme B S hS).map r))
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (hf.snd p))
        ((BigFppfOver.toScheme B S hS).map r))
      ((BigFppfOver.toScheme B S hS).map (hf.snd p))
      ((BigFppfOver.toScheme B S hS).map r) :=
    IsPullback.of_hasPullback _ _
  have hcomp : (hsq.isoIsPullback _ _ hcan).hom ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map (hf.snd p))
        ((BigFppfOver.toScheme B S hS).map r) =
      (BigFppfOver.toScheme B S hS).map (hf.snd ψ) :=
    hsq.isoIsPullback_hom_snd _ _ hcan
  have hker : ((BigFppfOver.toScheme B S hS).map (hf.snd ψ)).ker =
      ((BigFppfOver.toScheme B S hS).map (hf.snd p)).ker.comap
        ((BigFppfOver.toScheme B S hS).map r) := by
    rw [← hcomp, Scheme.Hom.ker_comp_of_isIso]
    exact ker_pullback_snd_eq_comap ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map (hf.snd p))
  rw [Scheme.IdealSheafData.pullback_obj_mk_subschemeι, ← hker]

/-- The scheme-theoretic image, inside a surjective étale chart of `X`, of the base change along
that chart of a quasi-compact representable morphism into `X` is invariant under the relation of
the chart.

The two legs of the relation are étale, hence flat, and have the same composite with the chart, so
both pullbacks of the subscheme are the scheme-theoretic image of one and the same base change. -/
private theorem isInvariantSubscheme_mk_imageι {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    {f : G ⟶ X} (hf : yoneda.relativelyRepresentable f)
    (hqc : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (hf.snd φ))) :
    IsInvariantSubscheme B S hS hs
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hf.snd φ)).imageι) := by
  have _ := etale_atlasRelationTarget B S hS hs he
  have _ := etale_atlasRelationSource B S hS hs he
  exact (pullback_obj_mk_imageι_snd B S hS hf φ (atlasRelationTarget B S hS hs) _ rfl
      inferInstance hqc).trans
    (pullback_obj_mk_imageι_snd B S hS hf φ (atlasRelationSource B S hS hs) _
      (yoneda_map_atlasRelationSource_comp B S hS hs) inferInstance hqc).symm

end Invariance

/-! ### Open immersions onto a full scheme-theoretic image -/

section Criterion

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A quasi-compact immersion of algebraic spaces whose scheme-theoretic image is the whole
target is an open immersion.

Openness is tested on a surjective étale chart of the target, by Stacks 02WZ. On such a chart the
base change of the morphism is a quasi-compact immersion of schemes whose scheme-theoretic image
is a closed subscheme invariant under the relation of the chart, so it cuts out a closed subspace
of the target through which the morphism factors; minimality of the scheme-theoretic image makes
that subspace the whole target, and an immersed subscheme is determined by its functor of points,
so the scheme-theoretic image of the base change is the whole chart. Stacks 01RG then makes the
base change an open immersion. -/
theorem isOpenImmersion_of_schemeTheoreticImageSubfunctor_eq_top
    (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X) (hf : IsImmersion B S hS f)
    (hq : IsQuasiCompact B S hS f)
    (hfull : schemeTheoreticImageSubfunctor B S hS f = ⊤) :
    IsOpenImmersion B S hS f := by
  obtain ⟨U, φ, hs, he⟩ := hX.exists_atlas
  have hrep : yoneda.relativelyRepresentable f := hf.rep
  have him : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) := hf.property_snd φ
  have hqc : _root_.AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) :=
    (presheaf_quasiCompact_of_isQuasiCompact B S hS hrep hq).property_snd φ
  have _him := him
  have _hqc := hqc
  -- The scheme-theoretic image of the base change, as a subobject of the chart.
  have hZci : _root_.AlgebraicGeometry.IsClosedImmersion
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk
      ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι]
    infer_instance
  have hZim : _root_.AlgebraicGeometry.IsImmersion
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι).arrow :=
    have := hZci
    inferInstance
  have hinv := isInvariantSubscheme_mk_imageι B S hS hs he hrep hqc
  -- The closed subspace of `X` it cuts out.
  obtain ⟨hWalg, hWci⟩ := isAlgebraicSpace_and_presheaf_invariantSubspace B S hS hs he
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX _ hZim hZci hinv
  -- The morphism factors through that closed subspace.
  have hrange : Subfunctor.range f ≤
      invariantSubspace B S hS φ
        (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι) := by
    rintro T x ⟨z, rfl⟩ T' g f' hcomm
    have hnat : f.app (Opposite.op T') (Z.map g.op z) = X.map g.op (f.app T z) :=
      NatTrans.naturality_apply f g.op z
    have hw : yonedaEquiv.symm (Z.map g.op z) ≫ f = yoneda.map f' ≫ φ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        Equiv.apply_symm_apply, hnat, ← hcomm]
    have hlift : hrep.lift (yonedaEquiv.symm (Z.map g.op z)) f' hw ≫ hrep.snd φ = f' :=
      hrep.lift_snd _ _ _
    refine (mem_subschemePoints_iff B S hS f').2 (mk_factors_of_eq_comp _
      (l := (BigFppfOver.toScheme B S hS).map
          (hrep.lift (yonedaEquiv.symm (Z.map g.op z)) f' hw) ≫
        ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).toImage) ?_)
    rw [Category.assoc, Scheme.Hom.toImage_imageι, ← CategoryTheory.Functor.map_comp, hlift]
  -- Minimality of the scheme-theoretic image makes it the whole target.
  have hWtop : invariantSubspace B S hS φ
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι) = ⊤ :=
    top_unique (hfull ▸ schemeTheoreticImageSubfunctor_le B S hS f ⟨hWalg, hWci⟩ hrange)
  -- Hence the scheme-theoretic image of the base change is the whole chart.
  have hsp : subschemePoints B S hS
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι) = ⊤ := by
    rw [← preimage_invariantSubspace B S hS hs _ hinv, hWtop]
    exact le_antisymm le_top fun _ _ _ => trivial
  have hfactors : (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι).Factors
      (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) := by
    have hmem := (mem_subschemePoints_iff B S hS (𝟙 U)).1
      (by rw [hsp]; trivial : (𝟙 U) ∈ (subschemePoints B S hS
        (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι)).obj
          (Opposite.op U))
    rwa [CategoryTheory.Functor.map_id] at hmem
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)).imageι :=
    isIso_of_mk_factors_id _ hfactors
  have _hiso := hiso
  -- Stacks 01RG upgrades the base change to an open immersion.
  have hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hrep.snd φ)) := by
    rw [← Scheme.Hom.toImage_imageι ((BigFppfOver.toScheme B S hS).map (hrep.snd φ))]
    exact MorphismProperty.comp_mem (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) _ _
      (isOpenImmersion_toImage _ (Or.inl hqc)) inferInstance
  have _hsbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) := inferInstance
  have _hlat : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) f hrep U φ hs he).2 hopen

end Criterion

/-! ### The scheme-theoretic image of the morphism onto the scheme-theoretic image -/

section Full

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism is a base change of itself along the inclusion of a closed subspace it factors
through: the inclusion of a subfunctor is a monomorphism, so the commuting square with the
identity on the source is cartesian. -/
theorem isPullback_lift (f : Z ⟶ X) {W : Subfunctor X}
    (hfW : Subfunctor.range f ≤ W) :
    IsPullback (𝟙 Z) (Subfunctor.lift f hfW) f W.ι := by
  have hfac : Subfunctor.lift f hfW ≫ W.ι = f := Subfunctor.lift_ι _ _
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := 𝟙 Z) (snd := Subfunctor.lift f hfW) (eq := by rw [Category.id_comp, hfac])
    (fun s => s.fst) (fun s => by rw [Category.comp_id]) (fun s => ?_) (fun s m hm _ => ?_))
  · refine (cancel_mono W.ι).1 ?_
    rw [Category.assoc, hfac]
    exact s.condition
  · rw [← Category.comp_id m, hm]

/-- A closed subspace of the scheme-theoretic image of a morphism through which the morphism's
factorization through that image factors is the whole image.

Its composite with the inclusion of the image is a closed immersion into the target, so its range
is a closed subspace of the target through which the morphism factors; minimality of the
scheme-theoretic image makes that range the whole image, and the inclusion of a subfunctor being
injective on sections, every section of the image lies in the given closed subspace. -/
private theorem eq_top_of_isClosedSubspace_of_range_le (f : Z ⟶ X) {C : Subfunctor X}
    (hC : IsClosedSubspace B S hS C)
    (hCmin : ∀ W : Subfunctor X, IsClosedSubspace B S hS W → Subfunctor.range f ≤ W → C ≤ W)
    {g : Z ⟶ C.toFunctor} (hg : g ≫ C.ι = f) {D : Subfunctor C.toFunctor}
    (hD : IsClosedSubspace B S hS D) (hgD : Subfunctor.range g ≤ D) : D = ⊤ := by
  have hqClosed : IsClosedImmersion B S hS (D.ι ≫ C.ι) := by
    have _hci : MorphismProperty.IsStableUnderComposition
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})).toIsStableUnderComposition
    have _hmul : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have _hcomp : MorphismProperty.IsStableUnderComposition
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _ hD.2 hC.2
  have _hmono : Mono (D.ι ≫ C.ι) := inferInstance
  have hfac : (asIso (Subfunctor.toRange (D.ι ≫ C.ι))).hom ≫
      (Subfunctor.range (D.ι ≫ C.ι)).ι = D.ι ≫ C.ι := Subfunctor.toRange_ι _
  -- The range of that composite is a closed subspace of the target.
  have hD'closed : IsClosedSubspace B S hS (Subfunctor.range (D.ι ≫ C.ι)) := by
    refine ⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange (D.ι ≫ C.ι))) hD.1, ?_⟩
    refine (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (asIso (Subfunctor.toRange (D.ι ≫ C.ι))).hom (Subfunctor.range (D.ι ≫ C.ι)).ι).1 ?_
    rw [hfac]
    exact hqClosed
  -- The morphism factors through it, so minimality identifies it with the image.
  have hfeq : f = Subfunctor.lift g hgD ≫ (D.ι ≫ C.ι) := by
    rw [← Category.assoc, Subfunctor.lift_ι, hg]
  have hle := hCmin _ hD'closed (by rw [hfeq]; exact Subfunctor.range_comp_le _ _)
  have hge : Subfunctor.range (D.ι ≫ C.ι) ≤ C := by
    rintro T x ⟨y, rfl⟩
    exact (D.ι.app T y).2
  have heq := le_antisymm hle hge
  -- Every section of the image therefore lies in the closed subspace.
  refine le_antisymm le_top fun T x _ => ?_
  obtain ⟨y, hy⟩ := heq.le T x.2
  have hxy : D.ι.app T y = x := Subtype.ext hy
  rw [← hxy]
  exact y.2

/-- The scheme-theoretic image of the morphism from an algebraic space onto its scheme-theoretic
image is the whole of that image.

Were it a proper closed subspace of the image, its composite with the inclusion of the image would
be a closed subspace of the target through which the morphism factors and which is strictly
smaller than the image, contradicting minimality. -/
theorem schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top (f : Z ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) :
    schemeTheoreticImageSubfunctor B S hS (toSchemeTheoreticImage B S hS f) = ⊤ :=
  eq_top_of_isClosedSubspace_of_range_le B S hS f
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hX)
    (fun _ hW hfW => schemeTheoreticImageSubfunctor_le B S hS f hW hfW)
    (toSchemeTheoreticImage_ι B S hS f)
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (toSchemeTheoreticImage B S hS f)
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hX).1)
    (range_le_schemeTheoreticImageSubfunctor B S hS (toSchemeTheoreticImage B S hS f))

end Full

/-! ### Stacks 088G and Stacks 081U -/

section Factorization

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 088G**, the quasi-compact case of the first assertion. The morphism from the source
of a quasi-compact immersion of algebraic spaces over `S` onto its scheme-theoretic image is an
open immersion.

The morphism onto the image is again an immersion and again quasi-compact, being a base change of
the given morphism along the inclusion of the image, and its own scheme-theoretic image is all of
the image; so
`AlgebraicGeometry.Space.isOpenImmersion_of_schemeTheoreticImageSubfunctor_eq_top` applies. -/
@[ega "I 9.5.10" "open immersion"]
theorem isOpenImmersion_toSchemeTheoreticImage (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X)
    (hf : IsImmersion B S hS f) (hq : IsQuasiCompact B S hS f) :
    IsOpenImmersion B S hS (toSchemeTheoreticImage B S hS f) := by
  have hCclosed : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS f) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hX
  have hsq : IsPullback (𝟙 Z) (toSchemeTheoreticImage B S hS f) f
      (schemeTheoreticImageSubfunctor B S hS f).ι :=
    isPullback_lift B S hS f (range_le_schemeTheoreticImageSubfunctor B S hS f)
  have _hsbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact isOpenImmersion_of_schemeTheoreticImageSubfunctor_eq_top B S hS hCclosed.1
    (toSchemeTheoreticImage B S hS f) (MorphismProperty.of_isPullback hsq hf)
    (isQuasiCompact_of_isPullback B S hS hsq hq)
    (schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS f hX)

/-- **Stacks 081U.** An immersion of algebraic spaces over `S` which is quasi-compact factors as
an open immersion followed by a closed immersion.

The intermediate algebraic space is the scheme-theoretic image of the morphism: it is a closed
subspace of the target by Stacks 082X, and the morphism onto it is an open immersion by the
quasi-compact case of Stacks 088G. -/
@[stacks 081U]
theorem exists_isOpenImmersion_isClosedImmersion_comp_eq_of_isQuasiCompact
    (hX : IsAlgebraicSpace B S hS X) (f : Z ⟶ X) (hf : IsImmersion B S hS f)
    (hq : IsQuasiCompact B S hS f) :
    ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : Z ⟶ W) (i : W ⟶ X),
      IsAlgebraicSpace B S hS W ∧ IsOpenImmersion B S hS j ∧
        IsClosedImmersion B S hS i ∧ j ≫ i = f := by
  have hCclosed : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS f) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hX
  exact ⟨(schemeTheoreticImageSubfunctor B S hS f).toFunctor,
    toSchemeTheoreticImage B S hS f, (schemeTheoreticImageSubfunctor B S hS f).ι,
    hCclosed.1, isOpenImmersion_toSchemeTheoreticImage B S hS hX f hf hq, hCclosed.2,
    toSchemeTheoreticImage_ι B S hS f⟩

end Factorization

end Space

end AlgebraicGeometry

end
