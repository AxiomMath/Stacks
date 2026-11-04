module

public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DenseOpenAdmissibleBlowup.AmpleFamily
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamilyIdealCovering
public import StacksFrontier.AlgebraicGeometry.RestrictIso
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticClosureQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DenseOpenShrinkFiniteCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDenseBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedOpenSubspaceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeCoverBlowupSiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# The cover of Stacks 0GUN repaired so that Stacks 0GTT applies to it

Stacks 0GTT needs the covering scheme of Stacks 0GUN to have finitely many irreducible
components, and the proof of Stacks 0GV5 gives no reason for that; it is false in general for a
finite surjective morphism of finite presentation, see the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/IrreducibleComponentsFiniteSurjection.lean`.

The repair carried out here replaces the cover `Y` of Stacks 0GUN by the **scheme-theoretic
closure** `T` of `W = f^{-1}(U)` inside `Y`, where `U ⊆ X` is the quasi-compact dense open over
which Stacks 0GUN's cover is finite étale.  Then

* `W ⟶ X` is étale, separated and quasi-compact, so `|W|` has finitely many irreducible
  components (`AlgebraicGeometry.Space.finite_genericPoints_of_isEtale_of_isQuasiCompactSpace`);
* `W ⟶ T` has dense range, so `|T|` has finitely many irreducible components
  (`AlgebraicGeometry.Space.finite_irreducibleComponents_of_denseRange`);
* `T ⟶ X` is finite, and surjective because its image is closed and contains the dense `|U|`;
* `T` restricted over `U` **is** `W`, as a scheme, so `T ⟶ X` is still finite and étale over
  `U`.  This is why the scheme-theoretic and not the reduced closure is taken: the reduced one
  would lose étaleness.

The only property of the cover lost in passing from `Y` to `T` is finite presentation, which
nothing downstream uses.

Once the cover has finitely many irreducible components, Stacks 0GTT applies to it and the
remaining steps of the proof of Stacks 0GV5 are the ones already proved: the shrinking of `U`
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_`
`isIntegralHom`), the passage of the blowing up into the site
(`AlgebraicGeometry.Space.admissibleBlowupObj`), the resolution property of the blowing up from
its ample family (Stacks 0GMM) and steps 3--5
(`AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_`
`hasResolutionProperty_of_schemeCover`).  So Stacks 0GV5 and, by substitution, the general-base
statement of Stacks 0GV6 become unconditional here.

## Main results

* `AlgebraicGeometry.Space.exists_finiteSchemeCover_finiteEtaleOverDenseOpen_`
  `finite_irreducibleComponents`: **the repaired cover.**  A quasi-compact, quasi-separated
  algebraic space whose point space has finitely many irreducible components is covered by a
  surjective finite morphism from a scheme whose own point space has finitely many irreducible
  components, finite and étale over a quasi-compact dense open subspace.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_fromPreimage_subspaceOfOpens_of_isIso`:
  a morphism of the site which restricts to an isomorphism of schemes over an open of its
  target is finite locally free over the open subspace that open cuts out.  This is what makes
  the blowing up of Stacks 0GTT finite locally free over the shrunken `U`.
* `AlgebraicGeometry.Space.exists_schemeCover_isProper_hasResolutionProperty_`
  `isFiniteLocallyFreeOverOpenSubspace`: **steps 1 and 2 of the proof of Stacks 0GV5,
  unconditionally** -- the hypothesis `hcover` of the Stacks 0GV5 assembly, in its scheme-cover
  form, proved.
* `AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty`
  and `AlgebraicGeometry.Space.forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_`
  `hasResolutionProperty`: **the conclusion of Stacks 0GV5, with no hypothesis beyond the
  tag's own**, in the two shapes the rest of the library consumes.
* `AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_resolutionProperty_`
  `unconditional`: **the general-base statement of Stacks 0GV6, with no hypothesis beyond the
  tag's own.**

The last of these is the only declaration here carrying a `stacks` attribute: it is the
`@[stacks 0GV6]` registration, and the tree's only one.

## References

* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two pieces of subfunctor bookkeeping -/

/-- Transporting the inclusion of a subfunctor along an equality of subfunctors. -/
private theorem eqToHom_comp_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G G' : Subfunctor F}
    (h : G = G') : eqToHom (congrArg Subfunctor.toFunctor h) ≫ G'.ι = G.ι := by
  subst h
  simp

/-- A morphism whose range lies in the range of a monomorphism factors through it. -/
private theorem exists_comp_eq_of_range_le {F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : P ⟶ G) [Mono t] (s : F ⟶ G) (h : Subfunctor.range s ≤ Subfunctor.range t) :
    ∃ k : F ⟶ P, k ≫ t = s :=
  ⟨Subfunctor.lift s h ≫ (rangeIsoOfMono B S hS t).inv, by
    rw [Category.assoc, rangeIsoOfMono_inv_comp B S hS t]
    exact Subfunctor.lift_ι _ _⟩

/-- A monomorphism whose range is a subfunctor `V` is, up to isomorphism, the inclusion of `V`. -/
private theorem exists_iso_comp_ι_eq_of_range_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : Subfunctor G} (t : F ⟶ G) [Mono t] (h : Subfunctor.range t = V) :
    ∃ e : F ≅ V.toFunctor, e.hom ≫ V.ι = t := by
  refine ⟨(rangeIsoOfMono B S hS t).trans (eqToIso (congrArg Subfunctor.toFunctor h)), ?_⟩
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [eqToHom_comp_ι B S hS h, rangeIsoOfMono_hom_ι B S hS t]

/-- **A commutative square whose top edge is a monomorphism onto the preimage of the subfunctor
on its right is cartesian.**  A section of the lower-left corner over a test object is a section
of the ambient presheaf carried into the subfunctor, hence lies in the preimage, hence in the
range of the monomorphism; and the monomorphism makes the factorisation unique.

This duplicates `isPullback_of_range_eq_preimage` of
`StacksFrontier/AlgebraicGeometry/Spaces/EffectiveCartierDivisorSerreCondition.lean`, which proves
it for an arbitrary category and is `private` there, hence unavailable here. -/
private theorem isPullback_of_range_eq_preimage
    {F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (V : Subfunctor G) (g : F ⟶ G) (t : P ⟶ F)
    [Mono t] (l : P ⟶ V.toFunctor) (hrange : Subfunctor.range t = V.preimage g)
    (hcomm : l ≫ V.ι = t ≫ g) :
    IsPullback l t V.ι g := by
  have hle : ∀ s : PullbackCone V.ι g, Subfunctor.range s.snd ≤ Subfunctor.range t := by
    intro s
    rw [hrange, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp, ← s.condition,
      Subfunctor.range_comp, Subfunctor.image_le_iff,
      (Subfunctor.preimage_eq_top_iff V V.ι).2 (le_of_eq (Subfunctor.range_ι V))]
    exact le_top
  choose k hk using fun s : PullbackCone V.ι g =>
    exists_comp_eq_of_range_le B S hS t s.snd (hle s)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm k (fun s => ?_) hk
    (fun s m hm₁ hm₂ => (cancel_mono t).1 (by rw [hm₂, hk s])))
  rw [← cancel_mono V.ι, Category.assoc, hcomm, ← Category.assoc, hk s, s.condition]

/-- The square cutting out the inverse image of a subfunctor is cartesian. -/
private theorem isPullback_fromPreimage {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : Subfunctor G) (g : F ⟶ G) :
    IsPullback (V.fromPreimage g) (V.preimage g).ι V.ι g :=
  isPullback_of_range_eq_preimage B S hS V g _ _ (Subfunctor.range_ι _)
    (Subfunctor.fromPreimage_ι V g)

/-- The first projection of the pullback is étale iff the top edge of any other pullback square
over the same cospan is. -/
private theorem isEtale_pullback_fst_iff_of_isPullback {X Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Z} {g : Y ⟶ Z} {a : W ⟶ X} {b : W ⟶ Y} (h : IsPullback a b f g) :
    IsEtale B S hS (pullback.fst f g) ↔ IsEtale B S hS a := by
  have e : ((IsPullback.of_hasPullback f g).isoIsPullback _ _ h).hom ≫ a = pullback.fst f g :=
    (IsPullback.of_hasPullback f g).isoIsPullback_hom_fst _ _ h
  constructor
  · intro he
    rw [(Iso.eq_inv_comp _).2 e]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) he
  · intro ha
    rw [← e]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS _) ha

/-- A morphism of the site over an open subscheme is a monomorphism after Yoneda. -/
private theorem mono_yoneda_map_openSiteObjectHom (T : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Mono (yoneda.map (openSiteObjectHom B S hS T Q)) :=
  mono_of_presheaf_isOpenImmersion
    (isOpenImmersion_yoneda_map B S hS _ (Scheme.Opens.instIsOpenImmersionι Q))

/-- The Yoneda image of the inclusion of an open subscheme has as range the open subspace it cuts
out. -/
private theorem range_yoneda_map_openSiteObjectHom (T : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    Subfunctor.range (yoneda.map (openSiteObjectHom B S hS T Q)) = subspaceOfOpens B S hS T Q :=
  range_yoneda_map_eq_subspaceOfOpens B S hS (openSiteObjectHom B S hS T Q)
    (Scheme.Opens.instIsOpenImmersionι Q) Q (by rw [map_openSiteObjectHom]; exact Q.range_ι)

/-! ### The repaired cover -/

/-- **The cover of Stacks 0GUN, replaced by the scheme-theoretic closure of its part over the
dense open, so that Stacks 0GTT applies to it.**

Let `X` be a quasi-compact and quasi-separated algebraic space over `S` whose point space has
finitely many irreducible components.  Then there are an object `T` of the big fppf site over
`S`, a morphism `g : h_T ⟶ X` and a quasi-compact open subspace `U ⊆ X` with dense point set
such that `g` is surjective and finite, is finite and étale over `U`, and `|h_T|` has finitely
many irreducible components.

Nothing is claimed about finite presentation of `g`: that is exactly the clause of Stacks 0GUN
which the passage to the closure gives up, and no consumer of this statement uses it.  See the
module documentation for the argument. -/
theorem exists_finiteSchemeCover_finiteEtaleOverDenseOpen_finite_irreducibleComponents
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hXqc : IsQuasiCompactSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hcomp : (irreducibleComponents (points B S hS X)).Finite) :
    ∃ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X) (U : Subfunctor X),
      IsSurjective B S hS g ∧ IsFinite B S hS g ∧
      IsOpenSubspace B S hS U ∧ IsQuasiCompactSpace B S hS U.toFunctor ∧
      Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)) ∧
      IsFinite B S hS (pullback.fst U.ι g) ∧ IsEtale B S hS (pullback.fst U.ι g) ∧
      (irreducibleComponents (points B S hS (yoneda.obj T))).Finite := by
  -- Stacks 0GUN: the finite, finitely presented cover by a scheme, finite étale over `U`.
  obtain ⟨⟨Y, f, U, hsurj, hfin, hfp, hUopen, hUqc, hUdense, -, hUet⟩, -⟩ :=
    exists_finiteSchemeCover_finiteEtaleOverDenseOpen_and_refining B S hS hZ X hX hXqc hXqs hcomp
  have hYalg : IsAlgebraicSpace B S hS (yoneda.obj Y) := isAlgebraicSpace_yoneda B S hS Y
  have hUalg : IsAlgebraicSpace B S hS U.toFunctor := hUopen.1
  have hfint : IsIntegralHom B S hS f := IsFinite.isIntegralHom B S hS hfin
  -- `Y` is quasi-compact and quasi-separated as a scheme, and `h_Y` is quasi-separated.
  obtain ⟨hYcompact, hYqsep⟩ := compactSpace_and_quasiSeparatedSpace_of_isFinitePresentation
    B S hS hZ Y f hX hXqc hXqs hfp
  have _ := hYcompact
  have _ := hYqsep
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj Y) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hYalg hXqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isIntegralHom B S hS f hYalg hX hfint))
  -- `W₀ = f⁻¹(U)`, an open subspace of `h_Y`, finite and étale over `U`.
  have hW₀open : IsOpenSubspace B S hS (U.preimage f) :=
    isOpenSubspace_preimage B S hS f U hX hYalg hUopen
  have hW₀alg : IsAlgebraicSpace B S hS (U.preimage f).toFunctor := hW₀open.1
  have hsqU : IsPullback (U.fromPreimage f) (U.preimage f).ι U.ι f :=
    isPullback_fromPreimage B S hS U f
  have hprefin : IsFinite B S hS (U.fromPreimage f) :=
    isFinite_of_isPullback B S hS hsqU.flip hfin
  have hpreet : IsEtale B S hS (U.fromPreimage f) :=
    (isEtale_pullback_fst_iff_of_isPullback B S hS hsqU).1 hUet
  have hW₀qc : IsQuasiCompactSpace B S hS (U.preimage f).toFunctor :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hUalg hUqc
      (isQuasiCompact_of_isAffineHom' B S hS _ hW₀alg hUalg
        (isAffineHom_of_isIntegralHom _ (IsFinite.isIntegralHom B S hS hprefin)))
  -- `W₀` read as an open subscheme `W` of `Y`, with its site object.
  set W : ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
    opensOfOpenSubspace B S hS Y (U.preimage f) hW₀open with hWdef
  set Wo : BigFppfOver B S hS := openSiteObject B S hS Y W with hWo
  set w : Wo ⟶ Y := openSiteObjectHom B S hS Y W with hw
  have hwrange : Subfunctor.range (yoneda.map w) = U.preimage f :=
    (range_yoneda_map_openSiteObjectHom B S hS Y W).trans
      ((congrArg _ hWdef).trans
        (subspaceOfOpens_opensOfOpenSubspace B S hS Y (U.preimage f) hW₀open))
  have _ : Mono (yoneda.map w) := mono_yoneda_map_openSiteObjectHom B S hS Y W
  -- the comparison isomorphism between the site object and the open subspace
  obtain ⟨eW, heW⟩ := exists_iso_comp_ι_eq_of_range_eq B S hS (yoneda.map w) hwrange
  -- `W.ι` is a quasi-compact morphism, so the scheme-theoretic closure is available.
  have hWcompactset : IsCompact (W : Set ((BigFppfOver.toScheme B S hS).obj Y)) := by
    rw [hWdef]
    exact isCompact_opensOfOpenSubspace B S hS Y (U.preimage f) hW₀open
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hYalg hYqs hW₀qc _)
  have hWcompact : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hWcompactset
  have hWopenι : _root_.AlgebraicGeometry.IsOpenImmersion W.ι :=
    Scheme.Opens.instIsOpenImmersionι W
  have hWimm : _root_.AlgebraicGeometry.IsImmersion W.ι := inferInstance
  have hWqc : QuasiCompact W.ι := quasiCompact_of_compactSpace W.ι
  -- the scheme-theoretic closure `T` of `W` in `Y`, as an object of the site
  set T : BigFppfOver B S hS := schemeImageObj B S hS w with hT
  set i : T ⟶ Y := schemeImageObjι B S hS w with hi
  set j : Wo ⟶ T := toSchemeImageObj B S hS w with hj
  have himap : (BigFppfOver.toScheme B S hS).map i = W.ι.imageι :=
    schemeImageObjι_toScheme B S hS w
  have hjmap : (BigFppfOver.toScheme B S hS).map j = W.ι.toImage :=
    toSchemeImageObj_toScheme B S hS w
  have hji : j ≫ i = w := toSchemeImageObj_comp_schemeImageObjι B S hS w
  have hjopen : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j) :=
    isOpenImmersion_toSchemeImageObj B S hS w hWimm (Or.inl hWqc)
  have _ : Mono (yoneda.map j) :=
    mono_of_presheaf_isOpenImmersion (isOpenImmersion_yoneda_map B S hS j hjopen)
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  -- `T` restricted over `U` is `W`: the key cartesian square
  have hjrange : Subfunctor.range (yoneda.map j) = (U.preimage f).preimage (yoneda.map i) := by
    have h1 : Subfunctor.range (yoneda.map j) =
        subspaceOfOpens B S hS T ((BigFppfOver.toScheme B S hS).map i ⁻¹ᵁ W) := by
      refine range_yoneda_map_eq_subspaceOfOpens B S hS j hjopen _ ?_
      change Set.range W.ι.toImage = ((W.ι.imageι ⁻¹ᵁ W : (W.ι.image).Opens) : Set _)
      rw [Scheme.Opens.preimage_imageι_ι_self W, Scheme.Hom.coe_opensRange]
    rw [h1, ← subspaceOfOpens_preimage_yoneda_map B S hS i W, hWdef,
      subspaceOfOpens_opensOfOpenSubspace B S hS Y (U.preimage f) hW₀open]
  have hsqW : IsPullback eW.hom (yoneda.map j) (U.preimage f).ι (yoneda.map i) :=
    isPullback_of_range_eq_preimage B S hS (U.preimage f) (yoneda.map i) (yoneda.map j) eW.hom
      hjrange (by rw [heW, ← hji, Functor.map_comp])
  have hkey : IsPullback (eW.hom ≫ U.fromPreimage f) (yoneda.map j) U.ι
      (yoneda.map i ≫ f) := hsqW.paste_horiz hsqU
  -- `h_W` is quasi-compact, and `h_W ⟶ X` is étale and separated: so `|h_W|` has finitely
  -- many irreducible components
  have hWspqc : IsQuasiCompactSpace B S hS (yoneda.obj Wo) :=
    isQuasiCompactSpace_of_iso B S hS eW.symm hW₀qc
  have hchartet : IsEtale B S hS (yoneda.map w ≫ f) := by
    rw [← heW, Category.assoc, ← hsqU.w, ← Category.assoc]
    exact isEtale_comp B S hS
      (isEtale_comp B S hS (isEtale_of_isIso B S hS eW.hom) hpreet)
      (isEtale_ι_of_isOpenSubspace hUopen)
  have hchartsep : IsSeparated B S hS (yoneda.map w ≫ f) := by
    rw [← heW, Category.assoc, ← hsqU.w, ← Category.assoc]
    refine isSeparated_comp B S hS _ _ ?_ (isSeparated_of_mono B S hS U.ι inferInstance)
    exact isSeparated_comp B S hS _ _
      (isSeparated_of_mono B S hS eW.hom (inferInstanceAs (Mono eW.hom)))
      (isSeparated_of_isIntegralHom B S hS _ hW₀alg hUalg
        (IsFinite.isIntegralHom B S hS hprefin))
  obtain ⟨-, hWcomp⟩ := finite_genericPoints_of_isEtale_of_isQuasiCompactSpace B S hS hZ hX
    hXqs hcomp Wo (yoneda.map w ≫ f) hchartet hchartsep hWspqc
  have hWschcomp : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj Wo)).Finite :=
    (finite_irreducibleComponents_points_yoneda_iff B S hS Wo).1 hWcomp
  -- `|T|` has finitely many irreducible components, `W` being dense in it
  have hTschcomp : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj T)).Finite := by
    refine finite_irreducibleComponents_of_denseRange (f := W.ι.toImage.base) ?_ ?_ hWschcomp
    · exact (W.ι.toImage).base.hom.continuous
    · exact Scheme.Opens.denseRange_toImage_ι W
  have hTcomp : (irreducibleComponents (points B S hS (yoneda.obj T))).Finite :=
    (finite_irreducibleComponents_points_yoneda_iff B S hS T).2 hTschcomp
  -- `T ⟶ X` is finite
  have hTfin : IsFinite B S hS (yoneda.map i ≫ f) := by
    refine isFinite_comp B S hS ?_ hfin
    refine (isFinite_yoneda_map_iff B S hS i).2 ?_
    exact ((_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
      ((BigFppfOver.toScheme B S hS).map i)).mp
      (isClosedImmersion_schemeImageObjι B S hS w)).1
  -- and surjective: its image is closed and contains the dense `|U|`
  have hTsurj : IsSurjective B S hS (yoneda.map i ≫ f) := by
    have hcc : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
        (x : points B S hS F), pointsMap B S hS G b (pointsMap B S hS F a x)
          = pointsMap B S hS F (a ≫ b) x := by
      intro F G H a b x
      rw [pointsMap_comp]
      rfl
    have hbig : ∀ q : points B S hS (yoneda.obj Wo),
        pointsMap B S hS (yoneda.obj T) (yoneda.map i ≫ f)
            (pointsMap B S hS (yoneda.obj Wo) (yoneda.map j) q)
          = pointsMap B S hS (yoneda.obj Y) f
            (pointsMap B S hS (U.preimage f).toFunctor (U.preimage f).ι
              (pointsMap B S hS (yoneda.obj Wo) eW.hom q)) := by
      intro q
      simp only [hcc]
      congr 1
      rw [← Category.assoc, ← Functor.map_comp, hji, ← heW]
    have hsub : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆
        Set.range (pointsMap B S hS (yoneda.obj T) (yoneda.map i ≫ f)) := by
      rintro x ⟨u, rfl⟩
      obtain ⟨y, hy⟩ := hsurj (pointsMap B S hS U.toFunctor U.ι u)
      have hymem : y ∈ Set.range (pointsMap B S hS (U.preimage f).toFunctor (U.preimage f).ι) := by
        rw [pointsRange_preimage B S hS f U, Set.mem_preimage, hy]
        exact Set.mem_range_self u
      obtain ⟨p, hp⟩ := hymem
      refine ⟨pointsMap B S hS (yoneda.obj Wo) (yoneda.map j)
        (pointsMap B S hS (U.preimage f).toFunctor eW.inv p), ?_⟩
      have hinv : pointsMap B S hS (yoneda.obj Wo) eW.hom
          (pointsMap B S hS (U.preimage f).toFunctor eW.inv p) = p := by
        rw [hcc, Iso.inv_hom_id, pointsMap_id, id_eq]
      rw [hbig, hinv, hp]
      exact hy
    have hclosed : IsClosed (Set.range (pointsMap B S hS (yoneda.obj T)
        (yoneda.map i ≫ f))) :=
      isClosed_range_pointsMap_of_isIntegralHom B S hS
        (ObjectProperty.homMk (yoneda.map i ≫ f) :
          (⟨yoneda.obj T, hTalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
        (IsFinite.isIntegralHom B S hS hTfin)
    have huniv : Set.range (pointsMap B S hS (yoneda.obj T) (yoneda.map i ≫ f)) = Set.univ := by
      rw [← hclosed.closure_eq, (hUdense.mono hsub).closure_eq]
    exact fun x => Set.eq_univ_iff_forall.mp huniv x
  -- and finite and étale over `U`
  refine ⟨T, yoneda.map i ≫ f, U, hTsurj, hTfin, hUopen, hUqc, hUdense,
    isFinite_of_isPullback B S hS (IsPullback.of_hasPullback U.ι (yoneda.map i ≫ f)).flip hTfin,
    ?_, hTcomp⟩
  exact (isEtale_pullback_fst_iff_of_isPullback B S hS hkey).2
    (isEtale_comp B S hS (isEtale_of_isIso B S hS eW.hom) hpreet)

/-! ### Finite local freeness over the admissible open of the blowing up -/

/-- **A morphism of the site whose restriction over an open subscheme `Q` of its target is an
isomorphism is finite locally free over the open subspace cut out by `Q`.**

The open subspace cut out by `Q` is the range of the Yoneda image of the open subscheme
(`AlgebraicGeometry.Space.range_yoneda_map_eq_subspaceOfOpens`), and its inverse image is the
range of the Yoneda image of the preimage open
(`AlgebraicGeometry.Space.subspaceOfOpens_preimage_yoneda_map`), so the comparison morphism of
inverse images is the Yoneda image of a morphism of the site whose morphism of schemes is the
restriction -- an isomorphism, hence finite locally free of rank one. -/
theorem isFiniteLocallyFree_presheaf_fromPreimage_subspaceOfOpens_of_isIso
    {T T' : BigFppfOver B S hS} (bh : T' ⟶ T)
    (Qs : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hiso : IsIso ((BigFppfOver.toScheme B S hS).map bh ∣_ Qs)) :
    (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      ((subspaceOfOpens B S hS T Qs).fromPreimage (yoneda.map bh)) := by
  have _ := mono_yoneda_map_openSiteObjectHom B S hS T Qs
  have _ := mono_yoneda_map_openSiteObjectHom B S hS T'
    ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs)
  have hQrange := range_yoneda_map_openSiteObjectHom B S hS T Qs
  have hQ'range : Subfunctor.range (yoneda.map (openSiteObjectHom B S hS T'
        ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs))) =
      (subspaceOfOpens B S hS T Qs).preimage (yoneda.map bh) := by
    rw [range_yoneda_map_openSiteObjectHom, subspaceOfOpens_preimage_yoneda_map B S hS bh Qs]
  -- the comparison morphism of the two open subspaces, as a morphism of the site
  have hle : Subfunctor.range (yoneda.map (openSiteObjectHom B S hS T'
        ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs)) ≫ yoneda.map bh) ≤
      Subfunctor.range (yoneda.map (openSiteObjectHom B S hS T Qs)) := by
    rw [Subfunctor.range_comp, hQ'range, hQrange, Subfunctor.image_le_iff]
  obtain ⟨μ, hμw⟩ := exists_comp_eq_of_range_le B S hS _ _ hle
  set m : openSiteObject B S hS T' ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs) ⟶
      openSiteObject B S hS T Qs := (yoneda (C := BigFppfOver B S hS)).preimage μ with hm
  have hmμ : yoneda.map m = μ := (yoneda (C := BigFppfOver B S hS)).map_preimage μ
  have hmw : m ≫ openSiteObjectHom B S hS T Qs =
      openSiteObjectHom B S hS T' ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs) ≫ bh := by
    refine (yoneda (C := BigFppfOver B S hS)).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hmμ, hμw]
  -- its morphism of schemes is the restriction of `bh` over `Qs`
  have _ : Mono Qs.ι := inferInstance
  have hmscheme : (BigFppfOver.toScheme B S hS).map m =
      (BigFppfOver.toScheme B S hS).map bh ∣_ Qs := by
    refine (cancel_mono Qs.ι).1 ?_
    have h1 : (BigFppfOver.toScheme B S hS).map m ≫ Qs.ι =
        (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS T'
          ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs)) ≫
          (BigFppfOver.toScheme B S hS).map bh := by
      rw [← map_openSiteObjectHom B S hS T Qs, ← Functor.map_comp, hmw, Functor.map_comp]
    have h2 : (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS T'
          ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs)) ≫
          (BigFppfOver.toScheme B S hS).map bh =
        ((BigFppfOver.toScheme B S hS).map bh ∣_ Qs) ≫ Qs.ι := by
      rw [map_openSiteObjectHom]
      exact (morphismRestrict_ι _ _).symm
    exact h1.trans h2
  -- the two cartesian squares over the same cospan
  have hsq₁ : IsPullback ((subspaceOfOpens B S hS T Qs).fromPreimage (yoneda.map bh))
      (((subspaceOfOpens B S hS T Qs).preimage (yoneda.map bh)).ι)
      (subspaceOfOpens B S hS T Qs).ι (yoneda.map bh) :=
    isPullback_fromPreimage B S hS _ _
  obtain ⟨eQ, heQ⟩ := exists_iso_comp_ι_eq_of_range_eq B S hS _ hQrange
  have hsq₂ : IsPullback (μ ≫ eQ.hom) (yoneda.map (openSiteObjectHom B S hS T'
        ((BigFppfOver.toScheme B S hS).map bh ⁻¹ᵁ Qs)))
      (subspaceOfOpens B S hS T Qs).ι (yoneda.map bh) := by
    refine isPullback_of_range_eq_preimage B S hS _ _ _ _ hQ'range ?_
    rw [Category.assoc, heQ, hμw]
  -- so the comparison of inverse images is the Yoneda image of `m` up to isomorphisms
  have hfac : (subspaceOfOpens B S hS T Qs).fromPreimage (yoneda.map bh) =
      (hsq₁.isoIsPullback _ _ hsq₂).hom ≫ μ ≫ eQ.hom :=
    (hsq₁.isoIsPullback_hom_fst _ _ hsq₂).symm
  have hμflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) (BigFppfOver.toScheme B S hS)).presheaf μ := by
    rw [← hmμ]
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) m).2 ?_
    rw [hmscheme]
    exact @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ 1
      (@Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso _ _ _ hiso)
  rw [hfac]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
    ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hμflf)

/-! ### Stacks 0GV5, unconditionally -/

/-- **Steps 1 and 2 of the proof of Stacks 0GV5, unconditionally**: the hypothesis `hschemeCover`
of `AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_`
`hasResolutionProperty_of_schemeCover`, proved.

A quasi-compact, quasi-separated algebraic space `X` over `S` whose point space has finitely
many irreducible components admits a quasi-compact open subspace `U` with dense point set and a
surjective proper morphism from a representable algebraic space whose scheme has the resolution
property of Stacks 0F86, finite locally free over `U`.

The cover is the scheme-theoretic closure of
`AlgebraicGeometry.Space.exists_finiteSchemeCover_finiteEtaleOverDenseOpen_`
`finite_irreducibleComponents`, blown up by Stacks 0GTT, with `U` shrunk by
`AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_`
`isIntegralHom` so that its inverse image lies in the open over which the blowing up is an
isomorphism.  The resolution property comes from the ample family by Stacks 0GMM. -/
theorem exists_schemeCover_isProper_hasResolutionProperty_isFiniteLocallyFreeOverOpenSubspace
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hcomp : (irreducibleComponents (points B S hS X.1)).Finite) :
    ∃ (U : OpenSubspaces B S hS X.1) (T : BigFppfOver B S hS)
      (g : representedAlgebraicSpace B S hS T ⟶ X),
      IsQuasiCompactSpace B S hS U.1.toFunctor ∧
      Dense (subspacePointSet B S hS X.1 U.1) ∧
      IsSurjective B S hS g.hom ∧ IsProper B S hS g.hom ∧
      IsQuasiCompactSpace B S hS (representedAlgebraicSpace B S hS T).1 ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
        (representedAlgebraicSpace B S hS T).1 ∧
      _root_.AlgebraicGeometry.HasResolutionProperty ((BigFppfOver.toScheme B S hS).obj T) ∧
      IsFiniteLocallyFreeOverOpenSubspace B S hS g U := by
  -- the repaired cover of Stacks 0GUN
  obtain ⟨T, g₀, U₀, hg₀surj, hg₀fin, hU₀open, hU₀qc, hU₀dense, -, hU₀et, hTcomp⟩ :=
    exists_finiteSchemeCover_finiteEtaleOverDenseOpen_finite_irreducibleComponents B S hS
      B.contains_terminal X.1 X.2 hXqc hXqs hcomp
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hg₀int : IsIntegralHom B S hS g₀ := IsFinite.isIntegralHom B S hS hg₀fin
  have hg₀proper : IsProper B S hS g₀ :=
    ((isFinite_iff_isAffineHom_and_isProper B S hS hTalg X.2 g₀).1 hg₀fin).2
  -- the covering scheme is quasi-compact, quasi-separated and has finitely many components
  have hTqcsp : IsQuasiCompactSpace B S hS (yoneda.obj T) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc
      (isQuasiCompact_of_isAffineHom' B S hS g₀ hTalg X.2
        (isAffineHom_of_isIntegralHom g₀ hg₀int))
  have hTqssp : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hTalg hXqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isSeparated_of_isIntegralHom B S hS g₀ hTalg X.2 hg₀int))
  have hTcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hTqcsp
  have hTqsep : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda B S hS B.contains_terminal T hTqssp
  have hTfincomp : Finite (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj T)) :=
    Set.finite_coe_iff.2 ((finite_irreducibleComponents_points_yoneda_iff B S hS T).1 hTcomp)
  -- Stacks 0GTT on the covering scheme
  obtain ⟨V, -, hVdense, T'sch, b, hb, J, N, hN⟩ :=
    Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily
      ((BigFppfOver.toScheme B S hS).obj T)
  -- the blowing up as an object of the site
  set T' : BigFppfOver B S hS := admissibleBlowupObj T hb with hT'
  set bh : T' ⟶ T := admissibleBlowupObjHom T hb with hbh
  have hbhmap : (BigFppfOver.toScheme B S hS).map bh = b :=
    toScheme_map_admissibleBlowupObjHom T hb
  have hbhproper : IsProper B S hS (yoneda.map bh) :=
    isProper_yoneda_map_admissibleBlowupObjHom T hb
  have hbhsurj : IsSurjective B S hS (yoneda.map bh) :=
    isSurjective_yoneda_map_admissibleBlowupObjHom T hb hVdense
  have hT'alg : IsAlgebraicSpace B S hS (yoneda.obj T') := isAlgebraicSpace_yoneda B S hS T'
  -- the shrinking of `U₀`
  set V' : Subfunctor (yoneda.obj T) := subspaceOfOpens B S hS T V with hV'
  have hV'open : IsOpenSubspace B S hS V' := isOpenSubspace_subspaceOfOpens B S hS T V
  have hV'dense : Dense (Set.range (pointsMap B S hS V'.toFunctor V'.ι)) := by
    rw [hV', range_pointsMap_subspaceOfOpens B S hS T V]
    exact (schemePointsHomeomorph B S hS T).dense_preimage hVdense
  obtain ⟨U, hUopen, hUqc, hUdense, -, hUpre, hUet⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_dense_le_preimage_le_of_isIntegralHom B S hS X.2
      hTalg hXqs hcomp hTcomp g₀ hg₀int U₀ hU₀open hU₀dense hU₀et V' hV'open hV'dense
  have hUalg : IsAlgebraicSpace B S hS U.toFunctor := hUopen.1
  have hQopen : IsOpenSubspace B S hS (U.preimage g₀) :=
    isOpenSubspace_preimage B S hS g₀ U X.2 hTalg hUopen
  -- the blowing up is an isomorphism over the shrunken open
  set Qs : ((BigFppfOver.toScheme B S hS).obj T).Opens :=
    opensOfOpenSubspace B S hS T (U.preimage g₀) hQopen with hQs
  have hQsV : Qs ≤ V := by
    rw [hQs]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem : y ∈ Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
      rw [← Subfunctor.homOfLe_ι hUpre, pointsMap_comp] at hy
      exact Set.range_comp_subset_range _ _ hy
    rw [hV', range_pointsMap_subspaceOfOpens B S hS T V] at hmem
    exact hmem
  have hbiso : IsIso ((BigFppfOver.toScheme B S hS).map bh ∣_ Qs) := by
    rw [hbhmap]
    exact Stacks.RestrictIso.isIso_morphismRestrict_of_le b hQsV
      (Stacks.BlowupAmpleFamily.isIso_morphismRestrict_of_isAdmissibleBlowup hb)
  have hQeq : subspaceOfOpens B S hS T Qs = U.preimage g₀ := by
    rw [hQs, subspaceOfOpens_opensOfOpenSubspace B S hS T (U.preimage g₀) hQopen]
  -- the two cartesian squares over `U` and their legs
  have hsqU : IsPullback (U.fromPreimage g₀) (U.preimage g₀).ι U.ι g₀ :=
    isPullback_fromPreimage B S hS U g₀
  have hsqb : IsPullback ((U.preimage g₀).fromPreimage (yoneda.map bh))
      (((U.preimage g₀).preimage (yoneda.map bh)).ι) (U.preimage g₀).ι (yoneda.map bh) :=
    isPullback_fromPreimage B S hS _ _
  have hsq : IsPullback ((U.preimage g₀).fromPreimage (yoneda.map bh) ≫ U.fromPreimage g₀)
      (((U.preimage g₀).preimage (yoneda.map bh)).ι) U.ι (yoneda.map bh ≫ g₀) :=
    hsqb.paste_horiz hsqU
  -- finite local freeness of the two legs, and of their composite
  have hprefin : IsFinite B S hS (U.fromPreimage g₀) :=
    isFinite_of_isPullback B S hS hsqU.flip hg₀fin
  have hpreet : IsEtale B S hS (U.fromPreimage g₀) :=
    (isEtale_pullback_fst_iff_of_isPullback B S hS hsqU).1 hUet
  have hpreflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (U.fromPreimage g₀) :=
    (isFiniteLocallyFree_presheaf_iff B S hS hQopen.1 hUalg (U.fromPreimage g₀)).2
      ⟨hprefin, isFlat_of_isEtale B S hS hpreet,
        isLocallyOfFinitePresentation_of_isEtale B S hS hpreet⟩
  have hbflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      ((U.preimage g₀).fromPreimage (yoneda.map bh)) := by
    rw [← hQeq]
    exact isFiniteLocallyFree_presheaf_fromPreimage_subspaceOfOpens_of_isIso B S hS bh Qs hbiso
  -- assembling the cover
  refine ⟨⟨U, hUopen⟩, T', ObjectProperty.homMk (yoneda.map bh ≫ g₀), hUqc, hUdense,
    isSurjective_comp B S hS hbhsurj hg₀surj,
    isProper_comp' B S hS _ _ hTalg X.2 hbhproper hg₀proper,
    isQuasiCompactSpace_yoneda_obj B S hS hN.compactSpace,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hT'alg hXqs
      (isQuasiSeparated_of_isSeparated B S hS
        (isProper_comp' B S hS _ _ hTalg X.2 hbhproper hg₀proper).1),
    Scheme.IsAmpleFamily.hasResolutionProperty hN, ?_⟩
  -- finite local freeness over the shrunken open
  refine (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS _).1 ?_
  have hsqA : IsPullback
      (pullback.fst (ObjectProperty.homMk (yoneda.map bh ≫ g₀) :
        representedAlgebraicSpace B S hS T' ⟶ X)
        (OpenSubspaces.toSpaceι (⟨U, hUopen⟩ : OpenSubspaces B S hS X.1))).hom
      (pullback.snd (ObjectProperty.homMk (yoneda.map bh ≫ g₀) :
        representedAlgebraicSpace B S hS T' ⟶ X)
        (OpenSubspaces.toSpaceι (⟨U, hUopen⟩ : OpenSubspaces B S hS X.1))).hom
      (yoneda.map bh ≫ g₀) U.ι :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _)
  rw [← hsqA.isoIsPullback_hom_snd _ _ hsq.flip]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
    (isFiniteLocallyFree_presheaf_comp B S hS _ _ hbflf hpreflf)

/-- **The conclusion of Stacks 0GV5, unconditionally.**  A quasi-compact, quasi-separated
algebraic space `X` over a scheme `S` whose point space has finitely many irreducible components
admits a quasi-compact open `U ⊆ X` with dense point set and a `U`-admissible blowing up
`X' ⟶ X` such that `X'` has the resolution property.

This is
`AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_`
`of_schemeCover` with its hypothesis discharged by
`AlgebraicGeometry.Space.exists_schemeCover_isProper_hasResolutionProperty_`
`isFiniteLocallyFreeOverOpenSubspace`.  No hypothesis beyond those of the tag remains. -/
theorem exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (hcomp : (irreducibleComponents (points B S hS X.1)).Finite) :
    ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
      Dense (subspacePointSet B S hS X.1 U.1) ∧
        ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
          HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty_of_schemeCover B S hS X
    hXqc hXqs hcomp fun hc =>
      exists_schemeCover_isProper_hasResolutionProperty_isFiniteLocallyFreeOverOpenSubspace
        B S hS X hXqc hXqs hc

/-- **The conclusion of Stacks 0GV5 in the shape in which Stacks 0GV6 consumes it,
unconditionally.**  The statement is literally the hypothesis `h0GV5` of
`AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_resolutionProperty`, of
`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian` and of
`AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_resolutionProperty_of_`
`isNoetherian`, so it discharges that binder in all of them by substitution. -/
theorem forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty :
    ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2 :=
  fun X hXqc hXqs hcomp =>
    exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty B S hS X hXqc hXqs hcomp

/-! ### Stacks 0GV6 over a general base scheme, unconditionally -/

/-- **Stacks 0GV6 for an algebraic space over an arbitrary base scheme, with no hypothesis
beyond the tag's own.**  For a quasi-compact, quasi-separated algebraic space `X` over a scheme
`S` of the site there are closed subspaces `Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t` of `X`, each of finite
presentation over `X`, with `Z₀ ⊆ X` a thickening, with `Z_t` carrying no points, and with a
`(Z_i ∖ Z_{i+1})`-admissible blowing up of `Z_i` whose source has the resolution property for
every `i < t`.

This is `AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_resolutionProperty`
with its hypothesis `h0GV5` discharged by
`AlgebraicGeometry.Space.forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_`
`hasResolutionProperty`, read over the terminal scheme.

**The index direction, and an erratum in the source.**  The tag's statement reads "for each
`i = 0, …, t - 1` there exists a `(Z_i ∖ Z_{i - 1})`-admissible blowing up", with the chain
`X ⊃ Z_0 ⊃ Z_1 ⊃ ⋯ ⊃ Z_t = ∅`.  That index cannot be meant.  The chain gives `Z_i ⊆ Z_{i - 1}`,
so `Z_i ∖ Z_{i - 1}` is empty for every `i ≥ 1`, and at `i = 0` it names a `Z_{-1}` the statement
never introduces.  A `∅`-admissible blowing up is one whose centre is disjoint from `∅`, that is
any blowing up at all, so the literal reading collapses the clause to "some blowing up of `Z_i`
has the resolution property" — strictly weaker than intended.  The tag's own proof settles it:
its induction produces blowing ups admissible with respect to `Z_{1, i} ∖ Z_{1, i + 1}`.  So the
sets meant are the strata `Z_i ∖ Z_{i + 1}`, which partition `Z_0`, and that is what is proved
here. -/
@[stacks 0GV6]
theorem exists_closedFiltration_admissibleBlowups_resolutionProperty_unconditional
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1) (hZ : ∀ i, IsClosedSubspace B S hS (Z i)),
      (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧
      IsThickening B S hS X (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, ∃ (U : OpenSubspaces B S hS (Z i).toFunctor) (Y : AlgebraicSpaces B S hS)
          (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ : AlgebraicSpaces B S hS)),
        Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ (Z i).ι)) =
            subspacePointSet B S hS X.1 (Z i) \ subspacePointSet B S hS X.1 (Z (i + 1)) ∧
          IsAdmissibleBlowup B S hS U f ∧
          HasResolutionProperty.{u, u} B S hS Y.1 Y.2 :=
  exists_closedFiltration_admissibleBlowups_resolutionProperty B S hS
    (forall_exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty B
      (⊤_ Scheme.{u}) B.contains_terminal) X hqc hqs


end AlgebraicGeometry.Space

end
