module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.ChartRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# Restricting a flat relation of algebraic spaces to a scheme chart

Let `Z` be a presheaf on the big fppf site of a scheme `S` and let `j : R ⟶ U ×_Z U` be an
equivalence relation of algebraic spaces over `Z` whose target and source maps are flat and
locally of finite presentation.  Restricting `j` along a surjective étale scheme chart
`a : h_{U₀} ⟶ U` leaves the quotient sheaf unchanged (Stacks 046P) and produces a relation
*between objects of the site*: the restricted relation is an algebraic space, its map to
`h_{U₀} × h_{U₀}` is a monomorphism which is locally of finite type, hence separated and
locally quasi-finite, so the restricted relation is representable by Stacks 03XX.

This is the source's reduction of condition (1) of [Stacks, Tag 04S6] to condition (2), carried
out at the level at which this library states condition (1),
`AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`.  The étale analogue is
`AlgebraicGeometry.Space.exists_etaleSiteRelation_of_chart`, where representability of the
restricted relation comes from representability of the two legs; a flat leg of a relation of
algebraic spaces is *not* representable, and the monomorphism argument above is what replaces
it.

## Main results

* `AlgebraicGeometry.Space.exists_flatSiteRelation_of_chart`: an equivalence relation of
  algebraic spaces with flat, locally finitely presented legs restricts, along an étale chart
  `a : h_{U₀} ⟶ U` of its object space, to a pair of flat, locally finitely presented morphisms
  of objects of the site which is again an equivalence relation.
* `AlgebraicGeometry.Space.bootstrap04S6QuotientSheaf_of_siteRelation`: condition (1) of
  [Stacks, Tag 04S6] follows from the same statement for a relation between objects of the site,
  which is condition (2) of the tag.

## Implementation notes

The restricted relation is built as the iterated fibre product
`h_{U₀} ×_{a, U, t} R ×_{s, U, a} h_{U₀}` of presheaves, each stage of which is a fibre product
of algebraic spaces and therefore an algebraic space (Stacks 03XY); the comparison with the
chosen restriction `AlgebraicGeometry.Space.PreRelation.restriction` is
`CategoryTheory.Limits.isPullback_prodLift_of_isPullback`, exactly as in the étale case.

Flatness and local finite presentation of the restricted legs are read off the same squares: the
first projection of each stage is a base change of a leg along the étale chart, and the
comparison maps of the third stage are base changes of the chart itself, which is étale and
therefore flat and locally of finite presentation.

Nothing here carries a `@[stacks 04S6]` attribute: the statement proved is a *reduction* of
condition (1) to condition (2), not either condition.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An étale-local property of morphisms of schemes which holds on every étale chart of a
morphism *of objects of the site*, read through Yoneda, holds of that morphism of schemes. -/
private theorem property_of_holdsOnEveryEtaleChart_yoneda
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : BigFppfOver B S hS} (h : X ⟶ Y)
    (hf : HoldsOnEveryEtaleChart B S hS P (yoneda.map h)) :
    P ((BigFppfOver.toScheme B S hS).map h) :=
  MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
    (F := yoneda) (f := h)
    ((holdsOnEveryEtaleChart_iff_relative B S hS P hP
      (isAlgebraicSpace_yoneda B S hS X) (isAlgebraicSpace_yoneda B S hS Y) (yoneda.map h)
      (Functor.relativelyRepresentable.map yoneda h)).mp hf)


/-- A morphism of presheaves which is étale after every representable base change is flat and
locally of finite presentation. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_of_presheaf_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f :=
  have := isEtale_of_presheafEtale B S hS f hf
  ⟨isFlat_of_isEtale B S hS this, isLocallyOfFinitePresentation_of_isEtale B S hS this⟩

/-- An isomorphism of presheaves is flat and locally of finite presentation. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [IsIso f] :
    IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f :=
  have : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  isFlat_and_isLocallyOfFinitePresentation_of_presheaf_etale f
    (MorphismProperty.presheaf_of_isIso _ f)

/-- A composite of morphisms of algebraic spaces which are flat and locally of finite
presentation is again flat and locally of finite presentation. -/
private theorem isFlat_and_isLocallyOfFinitePresentation_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) {f : F ⟶ G} {g : G ⟶ H}
    (hf : IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f)
    (hg : IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g) :
    IsFlat B S hS (f ≫ g) ∧ IsLocallyOfFinitePresentation B S hS (f ≫ g) :=
  ⟨isFlat_comp B S hS hF hG hH f g hf.1 hg.1,
    isLocallyOfFinitePresentation_comp B S hS hF hG hH f g hf.2 hg.2⟩

/-- If `y : A ⟶ h_{U₀}` is flat and locally of finite presentation, so is the scheme morphism
`x : R₀ ⟶ U₀` whose Yoneda image is `y` precomposed with an isomorphism `h_{R₀} ≅ A`. -/
private theorem flat_and_locallyOfFinitePresentation_of_yoneda_map_eq
    {R₀ U₀ : BigFppfOver B S hS} {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hU : IsAlgebraicSpace B S hS (yoneda.obj U₀))
    (e : A ≅ yoneda.obj R₀) (x : R₀ ⟶ U₀) (y : A ⟶ yoneda.obj U₀)
    (hxy : yoneda.map x = e.inv ≫ y)
    (hy : IsFlat B S hS y ∧ IsLocallyOfFinitePresentation B S hS y) :
    Flat ((BigFppfOver.toScheme B S hS).map x) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map x) := by
  have _ : MorphismProperty.IsLocalAtTarget (@Flat.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have _ : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have h := isFlat_and_isLocallyOfFinitePresentation_comp (isAlgebraicSpace_yoneda B S hS R₀)
    hA hU
    (isFlat_and_isLocallyOfFinitePresentation_of_isIso e.inv) hy
  rw [← hxy] at h
  exact ⟨property_of_holdsOnEveryEtaleChart_yoneda (@Flat.{u} : MorphismProperty Scheme.{u})
      Flat.isEtaleLocalOnSourceAndTarget x h.1,
    property_of_holdsOnEveryEtaleChart_yoneda
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget x h.2⟩

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}

/-- The restriction of an equivalence relation of algebraic spaces with flat, locally finitely
presented target and source along a chart `a : h_{U₀} ⟶ U` from a representable presheaf is
represented by an object of the site, with flat and locally finitely presented target and
source.

The three fibre products of the proof are the stages of
`h_{U₀} ×_{a, U, t} R ×_{s, U, a} h_{U₀}`; representability of the result is
[Stacks, Tag 03XX] applied to the monomorphism to `h_{U₀ × U₀}`, which is locally of finite
type because the source map is locally of finite presentation. -/
theorem exists_flatSiteRelation_of_chart (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source]
    (hR : IsAlgebraicSpace B S hS R.left) (hU : IsAlgebraicSpace B S hS U.left)
    (htf : IsFlat B S hS j.target.left)
    (htp : IsLocallyOfFinitePresentation B S hS j.target.left)
    (hsf : IsFlat B S hS j.source.left)
    (hsp : IsLocallyOfFinitePresentation B S hS j.source.left)
    {U₀ : BigFppfOver B S hS} (a : yoneda.obj U₀ ⟶ U.left)
    (haet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ (R₀ : BigFppfOver B S hS) (t₀ s₀ : R₀ ⟶ U₀)
      (e : (PreRelation.restriction j (chartInSliceMap U a)).left ≅ yoneda.obj R₀),
      IsEquivalenceRelation t₀ s₀ ∧
        Flat ((BigFppfOver.toScheme B S hS).map t₀) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t₀) ∧
        Flat ((BigFppfOver.toScheme B S hS).map s₀) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map s₀) ∧
        (PreRelation.restrict j (chartInSliceMap U a)).target.left = e.hom ≫ yoneda.map t₀ ∧
        (PreRelation.restrict j (chartInSliceMap U a)).source.left =
          e.hom ≫ yoneda.map s₀ := by
  classical
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  set t := j.target.left with hts
  set s := j.source.left with hss
  -- the chart is étale, hence flat and locally of finite presentation
  have hyU : IsAlgebraicSpace B S hS (yoneda.obj U₀) := isAlgebraicSpace_yoneda B S hS U₀
  -- the three stages of the iterated fibre product
  have hP : IsPullback (pullback.fst a t) (pullback.snd a t) a t := IsPullback.of_hasPullback a t
  have hQ : IsPullback (pullback.fst s a) (pullback.snd s a) s a := IsPullback.of_hasPullback s a
  set π := pullback.fst a t with hπ
  set p := pullback.snd a t with hp
  set q := pullback.fst s a with hq
  set κ := pullback.snd s a with hκ
  have hR3 : IsPullback (pullback.fst p q) (pullback.snd p q) p q :=
    IsPullback.of_hasPullback p q
  set σ := pullback.fst p q with hσ
  set ρ := pullback.snd p q with hρ
  -- each stage is an algebraic space
  have hP₀ : IsAlgebraicSpace B S hS (pullback a t) :=
    isAlgebraicSpace_pullback B S hS a t hyU hR hU
  have hQ₀ : IsAlgebraicSpace B S hS (pullback s a) :=
    isAlgebraicSpace_pullback B S hS s a hR hyU hU
  have hR₀ : IsAlgebraicSpace B S hS (pullback p q) :=
    isAlgebraicSpace_pullback B S hS p q hP₀ hQ₀ hR
  -- the comparison maps of the stages are étale after every representable base change
  have hpet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p := presheaf_of_isPullback B S hS hP haet
  have hqet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q := presheaf_of_isPullback B S hS hQ.flip haet
  have hσet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf σ := presheaf_of_isPullback B S hS hR3.flip hqet
  have hρet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ρ := presheaf_of_isPullback B S hS hR3 hpet
  -- flatness and local finite presentation of the two composites
  have hπ : IsFlat B S hS π ∧ IsLocallyOfFinitePresentation B S hS π :=
    ⟨isFlat_of_isPullback B S hS hP haet htf,
      holdsOnEveryEtaleChart_of_isPullback B S hS hP haet htp⟩
  have hκ : IsFlat B S hS κ ∧ IsLocallyOfFinitePresentation B S hS κ :=
    ⟨isFlat_of_isPullback B S hS hQ.flip haet hsf,
      holdsOnEveryEtaleChart_of_isPullback B S hS hQ.flip haet hsp⟩
  have hσ := isFlat_and_isLocallyOfFinitePresentation_of_presheaf_etale σ hσet
  have hρ := isFlat_and_isLocallyOfFinitePresentation_of_presheaf_etale ρ hρet
  have ht := isFlat_and_isLocallyOfFinitePresentation_comp hR₀ hP₀ hyU hσ hπ
  have hs := isFlat_and_isLocallyOfFinitePresentation_comp hR₀ hQ₀ hyU hρ hκ
  -- the iterated fibre product is the restriction of `j` along the chart
  have hRt : t ≫ U.hom = R.hom := Over.w j.target
  have hRs : s ≫ U.hom = R.hom := Over.w j.source
  set g : chartInSlice U a ⟶ U := chartInSliceMap U a with hg
  let AO : Over Z := Over.mk (π ≫ a ≫ U.hom)
  let a₁ : AO ⟶ chartInSlice U a := Over.homMk π rfl
  let a₂ : AO ⟶ R := Over.homMk p (by
    show p ≫ R.hom = π ≫ a ≫ U.hom
    rw [← hRt, ← reassoc_of% hP.w])
  let DO : Over Z := Over.mk (κ ≫ a ≫ U.hom)
  let d₂ : DO ⟶ chartInSlice U a := Over.homMk κ rfl
  let d₁ : DO ⟶ R := Over.homMk q (by
    show q ≫ R.hom = κ ≫ a ≫ U.hom
    rw [← hRs, reassoc_of% hQ.w])
  let PO : Over Z := Over.mk (σ ≫ π ≫ a ≫ U.hom)
  let p₁ : PO ⟶ AO := Over.homMk σ rfl
  let p₂ : PO ⟶ DO := Over.homMk ρ (by
    show ρ ≫ κ ≫ a ≫ U.hom = σ ≫ π ≫ a ≫ U.hom
    rw [← reassoc_of% hQ.w, reassoc_of% hP.w, hRs, hRt, reassoc_of% hR3.w])
  have ha' : IsPullback a₁ a₂ g j.target := IsPullback.of_map_of_faithful (Over.forget Z) hP
  have hd' : IsPullback d₁ d₂ j.source g := IsPullback.of_map_of_faithful (Over.forget Z) hQ
  have hp' : IsPullback p₁ p₂ a₂ d₁ := IsPullback.of_map_of_faithful (Over.forget Z) hR3
  have hfin : IsPullback (prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂)) (p₁ ≫ a₂) (prod.map g g) j := by
    have h := isPullback_prodLift_of_isPullback ha' hd' hp'
    have hj : (prod.lift j.target j.source : R ⟶ U ⨯ U) = j :=
      prod.hom_ext (by simp) (by simp)
    rwa [hj] at h
  let iso := hfin.isoIsPullback _ _ (IsPullback.of_hasPullback (prod.map g g) j)
  have hfst : iso.hom ≫ PreRelation.restrict j g = prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂) :=
    IsPullback.isoIsPullback_hom_fst _ _ hfin (IsPullback.of_hasPullback _ _)
  have htgt : iso.hom.left ≫ (PreRelation.restrict j g).target.left = σ ≫ π := by
    have h : iso.hom ≫ (PreRelation.restrict j g).target = p₁ ≫ a₁ := by
      rw [PreRelation.target, ← Category.assoc, hfst, prod.lift_fst]
    simpa [p₁, a₁] using congrArg (fun k : PO ⟶ chartInSlice U a => k.left) h
  have hsrc : iso.hom.left ≫ (PreRelation.restrict j g).source.left = ρ ≫ κ := by
    have h : iso.hom ≫ (PreRelation.restrict j g).source = p₂ ≫ d₂ := by
      rw [PreRelation.source, ← Category.assoc, hfst, prod.lift_snd]
    simpa [p₂, d₂] using congrArg (fun k : PO ⟶ chartInSlice U a => k.left) h
  -- the restricted relation is an algebraic space with flat, finitely presented legs
  set e₀ : (PreRelation.restriction j g).left ≅ pullback p q :=
    ((Over.forget Z).mapIso iso).symm with he₀
  have he₀hom : e₀.inv = iso.hom.left := rfl
  have hA : IsAlgebraicSpace B S hS (PreRelation.restriction j g).left :=
    isAlgebraicSpace_of_iso B S hS e₀.symm hR₀
  have hiso := isFlat_and_isLocallyOfFinitePresentation_of_isIso e₀.hom
  have hAt : IsFlat B S hS (PreRelation.restrict j g).target.left ∧
      IsLocallyOfFinitePresentation B S hS (PreRelation.restrict j g).target.left := by
    have : (PreRelation.restrict j g).target.left = e₀.hom ≫ σ ≫ π := by
      rw [← htgt, ← he₀hom, ← Category.assoc, e₀.hom_inv_id, Category.id_comp]
    rw [this]
    exact isFlat_and_isLocallyOfFinitePresentation_comp hA hR₀ hyU hiso ht
  have hAs : IsFlat B S hS (PreRelation.restrict j g).source.left ∧
      IsLocallyOfFinitePresentation B S hS (PreRelation.restrict j g).source.left := by
    have : (PreRelation.restrict j g).source.left = e₀.hom ≫ ρ ≫ κ := by
      rw [← hsrc, ← he₀hom, ← Category.assoc, e₀.hom_inv_id, Category.id_comp]
    rw [this]
    exact isFlat_and_isLocallyOfFinitePresentation_comp hA hR₀ hyU hiso hs
  -- the restricted relation is a monomorphism, locally of finite type, hence representable
  have hrel' : IsEquivalenceRelation (PreRelation.restrict j g).target.left
      (PreRelation.restrict j g).source.left :=
    isEquivalenceRelation_left _ _ inferInstance
  obtain ⟨erel⟩ := hrel'.nonempty_equivalenceRelation
  have hjm : JointlyMono₂ (PreRelation.restrict j g).target.left
      (PreRelation.restrict j g).source.left := ⟨erel.right_cancellation⟩
  let py : yoneda.obj (U₀ ⨯ U₀) ≅ yoneda.obj U₀ ⨯ yoneda.obj U₀ :=
    PreservesLimitPair.iso yoneda U₀ U₀
  set m : (PreRelation.restriction j g).left ⟶ yoneda.obj (U₀ ⨯ U₀) :=
    prod.lift (PreRelation.restrict j g).target.left
      (PreRelation.restrict j g).source.left ≫ py.inv with hm
  have hmono : Mono m := by
    have hlift : Mono (prod.lift (PreRelation.restrict j g).target.left
        (PreRelation.restrict j g).source.left) := by
      refine ⟨fun {T} f₁ f₂ h => ?_⟩
      refine JointlyMono₂.right_cancellation (p₁ := (PreRelation.restrict j g).target.left)
        (p₂ := (PreRelation.restrict j g).source.left) f₁ f₂ ?_ ?_
      · simpa only [Category.assoc, prod.lift_fst] using congrArg (· ≫ prod.fst) h
      · simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) h
    rw [hm]
    exact mono_comp _ _
  have hmsnd : m ≫ yoneda.map (prod.snd : U₀ ⨯ U₀ ⟶ U₀) =
      (PreRelation.restrict j g).source.left := by
    rw [hm, Category.assoc, PreservesLimitPair.iso_inv_snd]
    simp
  have hmlft : IsLocallyOfFiniteType B S hS m := by
    refine isLocallyOfFiniteType_of_comp B S hS hA (isAlgebraicSpace_yoneda B S hS (U₀ ⨯ U₀))
      hyU m (yoneda.map (prod.snd : U₀ ⨯ U₀ ⟶ U₀)) ?_
    rw [hmsnd]
    exact isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hAs.2
  have hrep : (PreRelation.restriction j g).left.IsRepresentable :=
    isRepresentable_of_locallyQuasiFinite_separated B S hS _ _ hA
      (isAlgebraicSpace_yoneda B S hS (U₀ ⨯ U₀)) m
      (Functor.IsRepresentable.mk' (Iso.refl _))
      (isLocallyQuasiFinite_of_mono B S hS hA
        (isAlgebraicSpace_yoneda B S hS (U₀ ⨯ U₀)) m hmono hmlft)
      (isSeparated_of_mono B S hS m hmono)
  -- name the representing object and read off the two legs
  let _ : (PreRelation.restriction j g).left.IsRepresentable := hrep
  set R₀ := (PreRelation.restriction j g).left.reprX with hR₀X
  set e : (PreRelation.restriction j g).left ≅ yoneda.obj R₀ :=
    (PreRelation.restriction j g).left.reprW.symm with heX
  set t₀ : R₀ ⟶ U₀ :=
    yoneda.preimage (e.inv ≫ (PreRelation.restrict j g).target.left) with ht₀
  set s₀ : R₀ ⟶ U₀ :=
    yoneda.preimage (e.inv ≫ (PreRelation.restrict j g).source.left) with hs₀
  have hmt : yoneda.map t₀ = e.inv ≫ (PreRelation.restrict j g).target.left :=
    Functor.map_preimage _ _
  have hms : yoneda.map s₀ = e.inv ≫ (PreRelation.restrict j g).source.left :=
    Functor.map_preimage _ _
  have hetgt : (PreRelation.restrict j g).target.left = e.hom ≫ yoneda.map t₀ := by
    rw [hmt, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hesrc : (PreRelation.restrict j g).source.left = e.hom ≫ yoneda.map s₀ := by
    rw [hms, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  obtain ⟨htF, htP⟩ := flat_and_locallyOfFinitePresentation_of_yoneda_map_eq hA hyU e t₀
    _ hmt hAt
  obtain ⟨hsF, hsP⟩ := flat_and_locallyOfFinitePresentation_of_yoneda_map_eq hA hyU e s₀
    _ hms hAs
  refine ⟨R₀, t₀, s₀, e, ?_, htF, htP, hsF, hsP, hetgt, hesrc⟩
  refine isEquivalenceRelation_of_map_of_iso yoneda e t₀ s₀ ?_
  rw [← hetgt, ← hesrc]
  exact hrel'

/-- **Condition (1) of Stacks 04S6 follows from condition (2).** If the fppf quotient sheaf of
every equivalence relation *between objects of the big fppf site of `S`* whose target and source
are flat and locally of finite presentation is an algebraic space, then so is the fppf quotient
sheaf of every equivalence relation of *algebraic spaces* over a presheaf `Z` whose target and
source are flat and locally of finite presentation -- that is,
`AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` holds.

This is the source's reduction of condition (1) to condition (2): the relation is restricted
along an étale atlas of its object space, which leaves the quotient sheaf unchanged by
[Stacks, Tag 046P] (`AlgebraicGeometry.Space.isIso_restrictQuotientSheafMap_chartInSliceMap`)
and makes the relation representable by
`AlgebraicGeometry.Space.exists_flatSiteRelation_of_chart`. -/
theorem bootstrap04S6QuotientSheaf_of_siteRelation
    (hsite : letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
        hasSheafify_bigFppfOver B S hS
      ∀ {R₀ U₀ : BigFppfOver B S hS} (t₀ s₀ : R₀ ⟶ U₀), IsEquivalenceRelation t₀ s₀ →
        Flat ((BigFppfOver.toScheme B S hS).map t₀) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t₀) →
        Flat ((BigFppfOver.toScheme B S hS).map s₀) →
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map s₀) →
        IsAlgebraicSpace B S hS
          (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
            (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀)).obj) :
    Bootstrap04S6QuotientSheaf B S hS := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  intro Z R U j hR hU hrel htf htp hsf hsp
  have := hrel
  obtain ⟨U₀, a, hasurj, haet⟩ := hU.exists_atlas
  obtain ⟨R₀, t₀, s₀, e, hrel₀, htF, htP, hsF, hsP, hetgt, hesrc⟩ :=
    exists_flatSiteRelation_of_chart j hR hU htf htp hsf hsp a haet
  have hj : IsPreEquivalenceRelation j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1 hrel).2
  have halg : IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀)).obj :=
    hsite t₀ s₀ hrel₀ htF htP hsF hsP
  have hpre := quotientPresheafIsoPoints B S hS
    (PreRelation.restrict j (chartInSliceMap U a)) s₀ t₀ e hetgt hesrc
  have hiso : (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj ≅
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀)).obj :=
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).mapIso hpre)).symm
  have hrestrAlg : IsAlgebraicSpace B S hS
      (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hiso halg
  have _ : IsIso (restrictQuotientSheafMap j (chartInSliceMap U a)) :=
    isIso_restrictQuotientSheafMap_chartInSliceMap j hj hU.isSheaf a hasurj haet
  have hiso' : (quotientSheaf j).obj ≅
      (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj :=
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (asIso (restrictQuotientSheafMap j (chartInSliceMap U a)))).symm
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hiso' hrestrAlg

end AlgebraicGeometry.Space

end
