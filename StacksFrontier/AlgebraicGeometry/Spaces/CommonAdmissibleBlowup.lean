module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtensionFromOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAnyCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.GluingAlongOpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionAfterAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimageIsoCriterion

/-!
# Two admissible blowups which glue to a separated space

Let `S` be a scheme and let `Y` be a quasi-compact and quasi-separated algebraic space over
`S`.  Let `U ⟶ X₁` and `U ⟶ X₂` be open immersions of algebraic spaces over `Y`, with `U`, `X₁`
and `X₂` separated and of finite type over `Y`.  Stacks 088Q asserts that there are
`U`-admissible blowups `X₁' ⟶ X₁` and `X₂' ⟶ X₂` and open immersions `X₁' ⟶ X` and
`X₂' ⟶ X` into an algebraic space `X` separated and of finite type over `Y`, compatibly with
`U`.

The proof is the source's.  Let `X₁₂ ⊆ X₁ ×_Y X₂` be the scheme-theoretic image of `U`; its
projections are isomorphisms over `U` (Stacks 0CP3).  A `U`-admissible blowup `X_iⁱ ⟶ X_i`
makes the strict transform `X₁₂ⁱ` of `X₁₂` an open subspace of `X_iⁱ` (Stacks 087F), and
`X₁₂ⁱ ⟶ X₁₂` is the blowup in the inverse image of the centre (Stacks 0864).  The blowup
`X₁₂'` of `X₁₂` in the sum of the two inverse images dominates both (Stacks 085Y), and is the
restriction to `X₁₂ⁱ` of a `U`-admissible blowup `X_i' ⟶ X_iⁱ` (Stacks 086D).  The morphism
`X₁₂' ⟶ X₁' ×_Y X₂'` is a proper immersion (Stacks 04NX), hence a closed immersion, and
`X₁'` and `X₂'` glue along `X₁₂'` to a separated space of finite type over `Y`.  Compositions
of `U`-admissible blowups are `U`-admissible (Stacks 086C).

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`:
  Stacks 088Q.
* `AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_isBlowupAlong_preimage`:
  Stacks 087F and 0864 on one side of the construction.
* `AlgebraicGeometry.Space.isIso_fromPreimage_of_isBlowupAlong`: a blowup is an isomorphism
  over an open subspace disjoint from its centre.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback_of_isOpenImmersion`: Stacks
  086D for an open subspace given by an open immersion.
* `AlgebraicGeometry.Space.isClosedImmersion_lift_of_isProper`: a proper morphism
  `T ⟶ X₁ ×_Y X₂` whose first component is an open immersion is a closed immersion.

## References

* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 0864](https://stacks.math.columbia.edu/tag/0864)
* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 086C](https://stacks.math.columbia.edu/tag/086C)
* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
-/

/- `exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion` below proves Stacks 088Q from the
statements of Stacks 07VR and Stacks 0873, which it carries as the hypotheses `h07VR` and `h0873`.
They are what Stacks 087E needs, and they arrive through Stacks 087F
(`exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`), which passes them on
unchanged rather than discharging them.  Both are theorems of this library — Stacks 07VR is
`exists_integralFiniteSystem_of_isFinite` and Stacks 0873 is
`exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType` — so supplying them
yields Stacks 088Q with no hypotheses beyond the source's; that is
`exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion_unconditional` in
`CommonAdmissibleBlowupUnconditional.lean`.  Of the other inputs of the proof, Stacks 0864 is
`isBlowupAlong_strictTransform` and Stacks 0DVJ is
`exists_pushout_isElementaryDistinguishedSquare`, while Stacks 0865, 0866 and 0868 are used inside
Stacks 087E and 087F and are discharged there. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Preimages over which a morphism is an isomorphism -/

namespace CategoryTheory.Subfunctor

variable {C : Type*} [Category C] {E F G : C ⥤ Type u}

/-- A morphism which is an isomorphism over a subfunctor `W` of its target is an isomorphism
over every smaller subfunctor `U ≤ W`. -/
theorem isIso_fromPreimage_of_le (p : F ⟶ G) {U W : Subfunctor G} (hUW : U ≤ W)
    [IsIso (W.fromPreimage p)] : IsIso (U.fromPreimage p) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  have hb := (isIso_iff_bijective ((W.fromPreimage p).app T)).1 inferInstance
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h1 : p.app T x.1 = p.app T y.1 := congrArg Subtype.val hxy
    have h : (W.fromPreimage p).app T ⟨x.1, hUW _ x.2⟩ =
        (W.fromPreimage p).app T ⟨y.1, hUW _ y.2⟩ := Subtype.ext h1
    have h2 := congrArg Subtype.val (hb.1 h)
    exact Subtype.ext h2
  · obtain ⟨x, hx⟩ := hb.2 ⟨y.1, hUW _ y.2⟩
    have hpx : p.app T x.1 = y.1 := congrArg Subtype.val hx
    exact ⟨⟨x.1, show p.app T x.1 ∈ U.obj T from hpx ▸ y.2⟩, Subtype.ext hpx⟩

/-- **A morphism `s` onto the preimage of `W`.**  If `p : F ⟶ G` is an isomorphism over `W` and
`s : E ⟶ F` lies over an isomorphism `t : E ≅ W`, then `s` is an isomorphism of `E` onto the
preimage `p⁻¹(W)`. -/
theorem exists_iso_preimage_of_isIso_fromPreimage (p : F ⟶ G) (W : Subfunctor G)
    [IsIso (W.fromPreimage p)] (s : E ⟶ F) (t : E ⟶ W.toFunctor) [IsIso t]
    (h : s ≫ p = t ≫ W.ι) :
    ∃ ψ : E ≅ (W.preimage p).toFunctor, ψ.hom ≫ (W.preimage p).ι = s := by
  have hs : Subfunctor.range s ≤ W.preimage p := by
    rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, h]
    simpa only [Subfunctor.range_ι] using Subfunctor.range_comp_le t W.ι
  let s' : E ⟶ (W.preimage p).toFunctor := Subfunctor.lift s hs
  have hs'φ : s' ≫ W.fromPreimage p = t := by
    refine (cancel_mono W.ι).1 ?_
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.lift_ι, h]
  have : IsIso s' := by
    rw [show s' = t ≫ inv (W.fromPreimage p) by
      rw [← hs'φ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance
  exact ⟨asIso s', Subfunctor.lift_ι s hs⟩

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Blowups away from the centre -/

/-- Disjoint subspaces of `X` have disjoint inverse images along any morphism `f : Y ⟶ X`. -/
private theorem disjoint_subspacePointSet_preimage {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ X) {U Z : Subfunctor X}
    (h : Disjoint (subspacePointSet B S hS X U) (subspacePointSet B S hS X Z)) :
    Disjoint (subspacePointSet B S hS Y (U.preimage f))
      (subspacePointSet B S hS Y (Z.preimage f)) := by
  rw [subspacePointSet_preimage, subspacePointSet_preimage]
  exact h.preimage _

/-- **A blowup is an isomorphism over every open subspace disjoint from its centre.**  The
blowup `b : X' ⟶ X` of `X` in `Z` is an isomorphism over the open complement of `Z` (Stacks
085T, part (1)), hence over any open subspace `U` whose points avoid `Z`. -/
theorem isIso_fromPreimage_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (U : OpenSubspaces B S hS X.1)
    (hUZ : Disjoint (subspacePointSet B S hS X.1 U.1) (subspacePointSet B S hS X.1 Z.1)) :
    IsIso (U.1.fromPreimage b.hom) := by
  have := isIso_fromPreimage_openComplement hb
  exact Subfunctor.isIso_fromPreimage_of_le b.hom (le_openComplementOfClosedSubspace Z U hUZ)

/-- **A blowup followed by an isomorphism of the base is a blowup.**  If `f : X' ⟶ X` is the
blowup of `X` in `Z` and `φ : X ≅ A`, then `f ≫ φ` is the blowup of `A` in `φ(Z)`, the inverse
image of `Z` along `φ⁻¹`. -/
theorem IsBlowupAlong.comp_iso {X X' A : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {f : X' ⟶ X} (hf : IsBlowupAlong B S hS Z f)
    (φ : X ≅ A) : IsBlowupAlong B S hS (preimageClosedSubspace φ.inv Z) (f ≫ φ.hom) := by
  have hsq : IsPullback (f ≫ φ.hom) (𝟙 X') φ.inv f :=
    IsPullback.of_vert_isIso ⟨by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]⟩
  exact IsBlowupAlong.of_isPullback_of_isFlat hsq (isFlat_of_isIso _ X'.2) Z _ rfl hf

/-! ### Extending an admissible blowup from an open immersion -/

/-- **Stacks 086D for an open subspace given by an open immersion.**  Let `A` be a
quasi-compact and quasi-separated algebraic space over `S`, let `U ⊆ A` be a quasi-compact open
subspace and let `st : T ⟶ A` be an open immersion with `T` quasi-compact.  Every
`st⁻¹(U)`-admissible blowup `d : T' ⟶ T` is the restriction to `T` of a `U`-admissible blowup
`f : A' ⟶ A`: there is an open immersion `e : T' ⟶ A'` making the square `d, e, st, f`
cartesian.

This is `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback'` applied to the image of
`st`, an open subspace of `A` isomorphic to `T`, the blowup being transported along that
isomorphism. -/
theorem exists_isAdmissibleBlowup_isPullback_of_isOpenImmersion
    (hZ : B.Contains (⊤_ Scheme.{u})) {A T T' : AlgebraicSpaces B S hS}
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (U : OpenSubspaces B S hS A.1) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (st : T ⟶ A) (hst : IsOpenImmersion B S hS st.hom) (hTqc : IsQuasiCompactSpace B S hS T.1)
    (d : T' ⟶ T)
    (hd : IsAdmissibleBlowup B S hS
      ⟨U.1.preimage st.hom, isOpenSubspace_preimage B S hS st.hom U.1 A.2 T.2 U.2⟩ d) :
    ∃ (A' : AlgebraicSpaces B S hS) (f : A' ⟶ A) (e : T' ⟶ A'),
      IsAdmissibleBlowup B S hS U f ∧ IsOpenImmersion B S hS e.hom ∧ IsPullback d e st f := by
  have : Mono st.hom := mono_of_isOpenImmersion B S hS _ hst
  let V : OpenSubspaces B S hS A.1 :=
    ⟨Subfunctor.range st.hom, isOpenSubspace_range_of_open B S hS st.hom T.2 hst⟩
  let φ : T ≅ openSubspace B S hS A V :=
    ObjectProperty.isoMk _ (asIso (Subfunctor.toRange st.hom))
  have hφ : φ.inv.hom ≫ st.hom = V.1.ι := Subfunctor.inv_toRange_comp_of_mono st.hom
  have hφ' : φ.hom ≫ openSubspaceι B S hS A V = st :=
    ObjectProperty.hom_ext _ (Subfunctor.toRange_ι st.hom)
  have hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange st.hom)) hTqc
  obtain ⟨K, hKfp, hKdisj, hKb⟩ := hd
  have hb' : IsAdmissibleBlowup B S hS (openSubspaceRestrict B S hS A V U) (d ≫ φ.hom) := by
    refine ⟨preimageClosedSubspace φ.inv K, isFinitePresentation_ι_preimage φ.inv K hKfp, ?_,
      hKb.comp_iso φ⟩
    have heq : U.1.preimage V.1.ι = (U.1.preimage st.hom).preimage φ.inv.hom := by
      rw [← Subfunctor.preimage_comp, hφ]
    change Disjoint (subspacePointSet B S hS _ (U.1.preimage V.1.ι))
      (subspacePointSet B S hS _ (K.1.preimage φ.inv.hom))
    rw [heq]
    exact disjoint_subspacePointSet_preimage φ.inv.hom hKdisj
  obtain ⟨A', f, hf, e, hpb⟩ :=
    exists_isAdmissibleBlowup_isPullback' hZ hAqc hAqs U V hUqc hVqc (d ≫ φ.hom) hb'
  have hpb' : IsPullback d e st f := by
    refine hpb.of_iso (Iso.refl _) φ.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.refl_hom,
        Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hφ', Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  exact ⟨A', f, e, hf, isOpenImmersion_of_isPullback B S hS hpb' hst, hpb'⟩

/-! ### A proper morphism to a product with an open immersion as first component -/

/-- **A proper morphism to `X₁ ×_Y X₂` whose first component is an open immersion is a closed
immersion.**  Let `e₁ : T ⟶ X₁` be an open immersion and `e₂ : T ⟶ X₂` a morphism over `Y`,
with `X₂ ⟶ Y` separated, and let `q : X₁ ×_Y X₂ ⟶ Q` be separated.  If
`(e₁, e₂) ≫ q` is proper then `(e₁, e₂) : T ⟶ X₁ ×_Y X₂` is a closed immersion.

The morphism `(e₁, e₂)` is proper by Stacks 04NX, part (2).  It is an immersion: it factors as
the graph `T ⟶ T ×_Y X₂` of `e₂`, a closed immersion because `T ×_Y X₂ ⟶ T` is separated,
followed by the base change `T ×_Y X₂ ⟶ X₁ ×_Y X₂` of the open immersion `e₁`.  A proper
immersion has closed image, so it is a closed immersion. -/
theorem isClosedImmersion_lift_of_isProper {T X₁ X₂ Y Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hX₂ : IsAlgebraicSpace B S hS X₂) (hY : IsAlgebraicSpace B S hS Y)
    (hQ : IsAlgebraicSpace B S hS Q) {e₁ : T ⟶ X₁} {e₂ : T ⟶ X₂} {a₁ : X₁ ⟶ Y} {a₂ : X₂ ⟶ Y}
    (w : e₁ ≫ a₁ = e₂ ≫ a₂) (he₁ : IsOpenImmersion B S hS e₁)
    (ha₂ : IsSeparated B S hS a₂) (q : pullback a₁ a₂ ⟶ Q) (hq : IsSeparated B S hS q)
    (hp : IsProper B S hS (pullback.lift e₁ e₂ w ≫ q)) :
    IsClosedImmersion B S hS (pullback.lift e₁ e₂ w) := by
  have hP : IsAlgebraicSpace B S hS (pullback a₁ a₂) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a₁ a₂ hX₁ hX₂ hY
  have hcp : IsProper B S hS (pullback.lift e₁ e₂ w) :=
    isProper_of_comp_of_isSeparated B S hS hT hP hQ _ q hp hq
  -- The graph of `e₂`.
  have hΓw : 𝟙 T ≫ e₁ ≫ a₁ = e₂ ≫ a₂ := by rw [Category.id_comp, w]
  have hΓ : IsClosedImmersion B S hS (pullback.lift (𝟙 T) e₂ hΓw) :=
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst (e₁ ≫ a₁) a₂)
      (isSeparated_pullbackFst B S hS (e₁ ≫ a₁) ha₂) _ (pullback.lift_fst _ _ _)
  -- The base change of `e₁`.
  let m : pullback (e₁ ≫ a₁) a₂ ⟶ pullback a₁ a₂ :=
    pullback.lift (pullback.fst (e₁ ≫ a₁) a₂ ≫ e₁) (pullback.snd (e₁ ≫ a₁) a₂)
      (by rw [Category.assoc, pullback.condition])
  have hm₁ : m ≫ pullback.fst a₁ a₂ = pullback.fst (e₁ ≫ a₁) a₂ ≫ e₁ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd a₁ a₂ = pullback.snd (e₁ ≫ a₁) a₂ := pullback.lift_snd _ _ _
  have hmpb : IsPullback m (pullback.fst (e₁ ≫ a₁) a₂) (pullback.fst a₁ a₂) e₁ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd a₁ a₂) (h₂₂ := a₁) (v₁₃ := a₂) ?_ hm₁
      (IsPullback.of_hasPullback a₁ a₂).flip
    rw [hm₂]
    exact (IsPullback.of_hasPullback (e₁ ≫ a₁) a₂).flip
  have hmo : IsOpenImmersion B S hS m :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback hmpb.flip he₁
  have heq : pullback.lift e₁ e₂ w = pullback.lift (𝟙 T) e₂ hΓw ≫ m := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hm₁, pullback.lift_fst_assoc, Category.id_comp]
    · rw [pullback.lift_snd, Category.assoc, hm₂, pullback.lift_snd]
  have himm : IsImmersion B S hS (pullback.lift e₁ e₂ w) := by
    rw [heq]
    exact isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS hΓ)
      (isImmersion_of_isOpenImmersion B S hS hmo)
  -- A proper immersion has closed image.
  refine (isClosedImmersion_iff_isClosed_range_pointsMap B S hS hP _ himm).2 ?_
  have hcl := isClosedMap_pointsMap_of_pullback_fst_id B S hS (pullback.lift e₁ e₂ w)
    (hcp.2.2 (pullback a₁ a₂) hP (𝟙 _))
  let := pointTopology B S hS T
  let := pointTopology B S hS (pullback a₁ a₂)
  simpa using hcl Set.univ isClosed_univ

/-! ### One side of the construction: Stacks 087F and 0864 -/

/-- **Stacks 087F together with Stacks 0864.**  Let `p : X ⟶ A` be separated and of finite
type, with `A` quasi-compact and quasi-separated, and an isomorphism over a quasi-compact open
`U ⊆ A`.  There are a `U`-admissible blowup `b : A' ⟶ A`, with centre `Z`, in which `U` is
scheme-theoretically dense, and an open immersion `st : T ⟶ A'` from the strict transform `T`
of `X`, whose morphism `c : T ⟶ X` is the blowup of `X` in `p⁻¹(Z)` (Stacks 0864), with
`st ≫ b = c ≫ p`.

The hypotheses `h07VR` and `h0873` are the statements of Stacks 07VR and 0873,
as in `AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`;
Stacks 0864 is `AlgebraicGeometry.Space.isBlowupAlong_strictTransform`. -/
theorem exists_isBlowupAlong_isOpenImmersion_isBlowupAlong_preimage
    (hZ : B.Contains (⊤_ Scheme.{u})) {A X : AlgebraicSpaces B S hS} (p : X ⟶ A)
    (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hft : IsFiniteType B S hS p.hom) (hsep : IsSeparated B S hS p.hom)
    (hiso : IsIso (pullback.snd p.hom U.1.ι))
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    (h0873 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
      IsFiniteType B S hS f → IsSeparated B S hS f →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
        IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧
          IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ i ≫ f' = f) :
    ∃ (A' T : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1)
      (st : T ⟶ A') (c : T ⟶ X),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧ IsSchemeTheoreticallyDense B S hS (U.1.preimage b.hom) ∧
            IsOpenImmersion B S hS st.hom ∧
              IsBlowupAlong B S hS (preimageClosedSubspace p Z) c ∧ st ≫ b = c ≫ p := by
  obtain ⟨A', b, Z, hZfp, hUZ, hb, hdense, hopen⟩ :=
    exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp hZ p U hAqc hAqs hUqc hft
      hsep hiso h07VR h0873
  refine ⟨A', strictTransformSpace B S hS p b (Z.1.preimage b.hom), b, Z,
    strictTransformSpaceToBlowUp B S hS p b (Z.1.preimage b.hom),
    strictTransformSpaceι B S hS p b (Z.1.preimage b.hom) ≫
      strictTransformPullbackToSource B S hS p b,
    hZfp, hUZ, hb, hdense, hopen, isBlowupAlong_strictTransform B S hS p b Z hb, ?_⟩
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun k => strictTransformSpaceι B S hS p b (Z.1.preimage b.hom) ≫ k)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS p b).w.symm

/-! ### Stacks 088Q -/

/-- **Stacks 088Q**, over the two inputs of Stacks 087E: the statements of Stacks 07VR and
Stacks 0873 (`h07VR`, `h0873`).  Let `Y` be a quasi-compact and quasi-separated algebraic space
over `S` and let
`j₁ : U ⟶ X₁`, `j₂ : U ⟶ X₂` be open immersions of algebraic spaces over `Y`, with `U`, `X₁`
and `X₂` separated and of finite type over `Y`.  There are a commutative diagram
`X₁ ⟵ X₁' ⟶ X ⟵ X₂' ⟶ X₂` under `U` and over `Y`, in which `b_k : X_k' ⟶ X_k` is a
`U`-admissible blowup (`U` being the open subspace `j_k(U)` of `X_k`), `i_k : X_k' ⟶ X` is an
open immersion, and `X` is separated and of finite type over `Y`.  Moreover the morphisms
`u_k : U ⟶ X_k'` of the diagram are open immersions.

See the module documentation for the proof. -/
theorem exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y U X₁ X₂ : AlgebraicSpaces B S hS}
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hj₁ : IsOpenImmersion B S hS j₁.hom) (hj₂ : IsOpenImmersion B S hS j₂.hom)
    (hj : j₁ ≫ f₁ = j₂ ≫ f₂)
    (hUft : IsFiniteType B S hS (j₁ ≫ f₁).hom)
    (hX₁ft : IsFiniteType B S hS f₁.hom) (hX₁sep : IsSeparated B S hS f₁.hom)
    (hX₂ft : IsFiniteType B S hS f₂.hom) (hX₂sep : IsSeparated B S hS f₂.hom)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    (h0873 : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y),
      IsAlgebraicSpace B S hS X → IsAlgebraicSpace B S hS Y →
      IsFiniteType B S hS f → IsSeparated B S hS f →
      IsQuasiCompactSpace B S hS Y → IsAbsolutelyQuasiSeparated B S hS hZ Y →
      ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
        IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧
          IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ i ≫ f' = f) :
    ∃ (X₁' X₂' X : AlgebraicSpaces B S hS) (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
      (i₁ : X₁' ⟶ X) (i₂ : X₂' ⟶ X) (g : X ⟶ Y) (u₁ : U ⟶ X₁') (u₂ : U ⟶ X₂'),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₁.hom, @isOpenSubspace_range_of_open B S hS
        _ _ j₁.hom (mono_of_isOpenImmersion B S hS _ hj₁) U.2 hj₁⟩ b₁ ∧
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₂.hom, @isOpenSubspace_range_of_open B S hS
        _ _ j₂.hom (mono_of_isOpenImmersion B S hS _ hj₂) U.2 hj₂⟩ b₂ ∧
      IsOpenImmersion B S hS i₁.hom ∧ IsOpenImmersion B S hS i₂.hom ∧
      IsSeparated B S hS g.hom ∧ IsFiniteType B S hS g.hom ∧
      i₁ ≫ g = b₁ ≫ f₁ ∧ i₂ ≫ g = b₂ ≫ f₂ ∧
      u₁ ≫ b₁ = j₁ ∧ u₂ ≫ b₂ = j₂ ∧ u₁ ≫ i₁ = u₂ ≫ i₂ ∧
      IsOpenImmersion B S hS u₁.hom ∧ IsOpenImmersion B S hS u₂.hom := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  have : Mono j₁.hom := mono_of_isOpenImmersion B S hS _ hj₁
  have : Mono j₂.hom := mono_of_isOpenImmersion B S hS _ hj₂
  set U₁ : OpenSubspaces B S hS X₁.1 :=
    ⟨Subfunctor.range j₁.hom, isOpenSubspace_range_of_open B S hS j₁.hom U.2 hj₁⟩ with hU₁def
  set U₂ : OpenSubspaces B S hS X₂.1 :=
    ⟨Subfunctor.range j₂.hom, isOpenSubspace_range_of_open B S hS j₂.hom U.2 hj₂⟩ with hU₂def
  -- Quasi-compactness and quasi-separatedness.
  have hUqc : IsQuasiCompactSpace B S hS U.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y.1) (j₁ ≫ f₁).hom))
      (hUft.2 Y.1 Y.2 hYqc (𝟙 Y.1))
  have hX₁qc : IsQuasiCompactSpace B S hS X₁.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y.1) f₁.hom))
      (hX₁ft.2 Y.1 Y.2 hYqc (𝟙 Y.1))
  have hX₂qc : IsQuasiCompactSpace B S hS X₂.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y.1) f₂.hom))
      (hX₂ft.2 Y.1 Y.2 hYqc (𝟙 Y.1))
  have hX₁qs : IsAbsolutelyQuasiSeparated B S hS hZ X₁.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X₁.2 hYqs
      (isQuasiSeparated_of_isSeparated B S hS hX₁sep)
  have hX₂qs : IsAbsolutelyQuasiSeparated B S hS hZ X₂.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X₂.2 hYqs
      (isQuasiSeparated_of_isSeparated B S hS hX₂sep)
  have hU₁qc : IsQuasiCompactSpace B S hS U₁.1.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange j₁.hom)) hUqc
  have hU₂qc : IsQuasiCompactSpace B S hS U₂.1.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (Subfunctor.toRange j₂.hom)) hUqc
  -- The scheme-theoretic image `X₁₂` of `U` in `X₁ ×_Y X₂`.
  have hjh : j₁.hom ≫ f₁.hom = j₂.hom ≫ f₂.hom := congrArg (fun k => k.hom) hj
  have hP : IsAlgebraicSpace B S hS (pullback f₁.hom f₂.hom) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ X₁.2 X₂.2 Y.2
  set s : U.1 ⟶ pullback f₁.hom f₂.hom := pullback.lift j₁.hom j₂.hom hjh with hsdef
  set Zs := schemeTheoreticImageSubfunctor B S hS s with hZsdef
  have hZs : IsClosedSubspace B S hS Zs :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS s hP
  let X₁₂ : AlgebraicSpaces B S hS := ⟨Zs.toFunctor, hZs.1⟩
  let p₁ : X₁₂ ⟶ X₁ := ObjectProperty.homMk (Zs.ι ≫ pullback.fst f₁.hom f₂.hom)
  let p₂ : X₁₂ ⟶ X₂ := ObjectProperty.homMk (Zs.ι ≫ pullback.snd f₁.hom f₂.hom)
  have hpw : p₁ ≫ f₁ = p₂ ≫ f₂ := ObjectProperty.hom_ext _ (by
    change (Zs.ι ≫ pullback.fst f₁.hom f₂.hom) ≫ f₁.hom =
      (Zs.ι ≫ pullback.snd f₁.hom f₂.hom) ≫ f₂.hom
    rw [Category.assoc, Category.assoc, pullback.condition])
  let sU : U ⟶ X₁₂ :=
    ObjectProperty.homMk (Subfunctor.lift s (range_le_schemeTheoreticImageSubfunctor B S hS s))
  have hsU₁ : sU ≫ p₁ = j₁ := ObjectProperty.hom_ext _ (by
    change Subfunctor.lift s (range_le_schemeTheoreticImageSubfunctor B S hS s) ≫ Zs.ι ≫
      pullback.fst f₁.hom f₂.hom = j₁.hom
    rw [Subfunctor.lift_ι_assoc, hsdef, pullback.lift_fst])
  have hsU₂ : sU ≫ p₂ = j₂ := ObjectProperty.hom_ext _ (by
    change Subfunctor.lift s (range_le_schemeTheoreticImageSubfunctor B S hS s) ≫ Zs.ι ≫
      pullback.snd f₁.hom f₂.hom = j₂.hom
    rw [Subfunctor.lift_ι_assoc, hsdef, pullback.lift_snd])
  -- The projections are separated and of finite type, and isomorphisms over `U` (Stacks 0CP3).
  have hfst_ft : IsFiniteType B S hS (pullback.fst f₁.hom f₂.hom) :=
    (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f₁ f₂).flip hX₂ft
  have hsnd_ft : IsFiniteType B S hS (pullback.snd f₁.hom f₂.hom) :=
    (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f₁ f₂) hX₁ft
  have hfst_sep : IsSeparated B S hS (pullback.fst f₁.hom f₂.hom) :=
    isSeparated_pullbackFst B S hS f₁.hom hX₂sep
  have hsnd_sep : IsSeparated B S hS (pullback.snd f₁.hom f₂.hom) :=
    isSeparated_pullbackSnd B S hS f₂.hom hX₁sep
  have hZs_ft : IsFiniteType B S hS Zs.ι := isFiniteType_of_isClosedImmersion B S hS _ hZs.2
  have hZs_sep : IsSeparated B S hS Zs.ι := isSeparated_of_isClosedImmersion B S hS _ hZs.2
  have hp₁ft : IsFiniteType B S hS p₁.hom := isFiniteType_comp' B S hS _ _ hP X₁.2 hZs_ft hfst_ft
  have hp₂ft : IsFiniteType B S hS p₂.hom := isFiniteType_comp' B S hS _ _ hP X₂.2 hZs_ft hsnd_ft
  have hp₁sep : IsSeparated B S hS p₁.hom := isSeparated_comp B S hS _ _ hZs_sep hfst_sep
  have hp₂sep : IsSeparated B S hS p₂.hom := isSeparated_comp B S hS _ _ hZs_sep hsnd_sep
  have hX₁₂qc : IsQuasiCompactSpace B S hS X₁₂.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X₁.2 hX₁qc hp₁ft.2
  have hrange : ∀ {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : E ⟶ U.1) [Epi t],
      schemeTheoreticImageSubfunctor B S hS (t ≫ s) = Zs := by
    intro E t _
    simp only [hZsdef, schemeTheoreticImageSubfunctor]
    rw [Subfunctor.range_comp, Subfunctor.range_eq_top t, Subfunctor.image_top]
  have hiso₁ : IsIso (pullback.snd p₁.hom U₁.1.ι) := by
    have h := isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS hP X₁.2
      (pullback.fst f₁.hom f₂.hom) hfst_sep U₁.1 U₁.2
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X₁.2 hX₁qs hU₁qc U₁.1.ι)
      (inv (Subfunctor.toRange j₁.hom) ≫ s)
      (by rw [Category.assoc, hsdef, pullback.lift_fst, Subfunctor.inv_toRange_comp_of_mono])
    rwa [hrange] at h
  have hiso₂ : IsIso (pullback.snd p₂.hom U₂.1.ι) := by
    have h := isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS hP X₂.2
      (pullback.snd f₁.hom f₂.hom) hsnd_sep U₂.1 U₂.2
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X₂.2 hX₂qs hU₂qc U₂.1.ι)
      (inv (Subfunctor.toRange j₂.hom) ≫ s)
      (by rw [Category.assoc, hsdef, pullback.lift_snd, Subfunctor.inv_toRange_comp_of_mono])
    rwa [hrange] at h
  -- The open `U ⊆ X₁₂` is the inverse image of `U` under either projection.
  have hO : ∀ {X : AlgebraicSpaces B S hS} (p : X₁₂ ⟶ X) (j : U ⟶ X) [Mono j.hom]
      (hU : IsOpenSubspace B S hS (Subfunctor.range j.hom)),
      IsIso (pullback.snd p.hom (Subfunctor.range j.hom).ι) → sU ≫ p = j →
        (Subfunctor.range j.hom).preimage p.hom = Subfunctor.range sU.hom := by
    intro X p j _ _ hiso hsj
    have : IsIso ((Subfunctor.range j.hom).fromPreimage p.hom) :=
      Subfunctor.isIso_fromPreimage_of_isIso_of_isPullback _ p.hom
        (IsPullback.of_hasPullback p.hom (Subfunctor.range j.hom).ι).flip
    obtain ⟨ψ, hψ⟩ := Subfunctor.exists_iso_preimage_of_isIso_fromPreimage p.hom
      (Subfunctor.range j.hom) sU.hom (Subfunctor.toRange j.hom)
      (by rw [Subfunctor.toRange_ι]; exact congrArg (fun k => k.hom) hsj)
    rw [← hψ, Subfunctor.range_comp,
      @Subfunctor.range_eq_top _ _ _ _ ψ.hom (IsIso.epi_of_iso _), Subfunctor.image_top,
      Subfunctor.range_ι]
  have hO₁ : U₁.1.preimage p₁.hom = Subfunctor.range sU.hom := hO p₁ j₁ U₁.2 hiso₁ hsU₁
  have hO₂ : U₂.1.preimage p₂.hom = Subfunctor.range sU.hom := hO p₂ j₂ U₂.2 hiso₂ hsU₂
  -- Stacks 087F and 0864 on each side.
  obtain ⟨A₁, T₁, a₁, Zc₁, st₁, c₁, hZc₁fp, hU₁Zc₁, ha₁, hd₁, hst₁, hc₁, hsq₁⟩ :=
    exists_isBlowupAlong_isOpenImmersion_isBlowupAlong_preimage hZ p₁ U₁ hX₁qc hX₁qs hU₁qc
      hp₁ft hp₁sep hiso₁ h07VR h0873
  obtain ⟨A₂, T₂, a₂, Zc₂, st₂, c₂, hZc₂fp, hU₂Zc₂, ha₂, hd₂, hst₂, hc₂, hsq₂⟩ :=
    exists_isBlowupAlong_isOpenImmersion_isBlowupAlong_preimage hZ p₂ U₂ hX₂qc hX₂qs hU₂qc
      hp₂ft hp₂sep hiso₂ h07VR h0873
  -- The two centres on `X₁₂`, both away from `U`.
  set K₁ := preimageClosedSubspace p₁ Zc₁ with hK₁def
  set K₂ := preimageClosedSubspace p₂ Zc₂ with hK₂def
  have hK₁fp : IsFinitePresentation B S hS K₁.1.ι := isFinitePresentation_ι_preimage p₁ Zc₁ hZc₁fp
  have hK₂fp : IsFinitePresentation B S hS K₂.1.ι := isFinitePresentation_ι_preimage p₂ Zc₂ hZc₂fp
  have hOK₁ : Disjoint (subspacePointSet B S hS X₁₂.1 (Subfunctor.range sU.hom))
      (subspacePointSet B S hS X₁₂.1 K₁.1) := by
    rw [← hO₁]
    exact disjoint_subspacePointSet_preimage p₁.hom hU₁Zc₁
  have hOK₂ : Disjoint (subspacePointSet B S hS X₁₂.1 (Subfunctor.range sU.hom))
      (subspacePointSet B S hS X₁₂.1 K₂.1) := by
    rw [← hO₂]
    exact disjoint_subspacePointSet_preimage p₂.hom hU₂Zc₂
  -- The blowup `X₁₂'` of `X₁₂` in `K₁ + K₂` dominates both strict transforms (Stacks 085Y).
  obtain ⟨X₁₂', d₁, hd₁b⟩ := exists_isBlowupAlong (preimageClosedSubspace c₁ K₂)
  obtain ⟨X₁₂'', d₂', hd₂'b⟩ := exists_isBlowupAlong (preimageClosedSubspace c₂ K₁)
  have hβ : IsBlowupAlong B S hS (sumClosedSubspaces B S hS X₁₂ K₁ K₂) (d₁ ≫ c₁) :=
    hc₁.comp_sumClosedSubspaces hd₁b
  have hβ' : IsBlowupAlong B S hS (sumClosedSubspaces B S hS X₁₂ K₁ K₂) (d₂' ≫ c₂) := by
    rw [sumClosedSubspaces_comm]
    exact hc₂.comp_sumClosedSubspaces hd₂'b
  obtain ⟨ι, hι⟩ := hβ'.exists_iso hβ
  set d₂ := ι.inv ≫ d₂' with hd₂def
  have hd₂b : IsBlowupAlong B S hS (preimageClosedSubspace c₂ K₁) d₂ := hd₂'b.of_iso_over ι.symm
  have hdd : d₂ ≫ c₂ = d₁ ≫ c₁ := by rw [hd₂def, Category.assoc, ← hι, Iso.inv_hom_id_assoc]
  -- Stacks 086D on each side: extend `X₁₂' ⟶ X₁₂ᵏ` to a blowup of `Aₖ`.
  have hc₁p : IsProper B S hS c₁.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS K₁ c₁ hK₁fp hc₁
  have hc₂p : IsProper B S hS c₂.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS K₂ c₂ hK₂fp hc₂
  have ha₁p : IsProper B S hS a₁.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Zc₁ a₁ hZc₁fp ha₁
  have ha₂p : IsProper B S hS a₂.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Zc₂ a₂ hZc₂fp ha₂
  have hA₁qc : IsQuasiCompactSpace B S hS A₁.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X₁.2 hX₁qc ha₁p.2.1.2
  have hA₂qc : IsQuasiCompactSpace B S hS A₂.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X₂.2 hX₂qc ha₂p.2.1.2
  have hA₁qs : IsAbsolutelyQuasiSeparated B S hS hZ A₁.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ A₁.2 hX₁qs
      (isQuasiSeparated_of_isSeparated B S hS ha₁p.1)
  have hA₂qs : IsAbsolutelyQuasiSeparated B S hS hZ A₂.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ A₂.2 hX₂qs
      (isQuasiSeparated_of_isSeparated B S hS ha₂p.1)
  have hT₁qc : IsQuasiCompactSpace B S hS T₁.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X₁₂.2 hX₁₂qc hc₁p.2.1.2
  have hT₂qc : IsQuasiCompactSpace B S hS T₂.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS X₁₂.2 hX₁₂qc hc₂p.2.1.2
  set V₁ : OpenSubspaces B S hS A₁.1 :=
    ⟨U₁.1.preimage a₁.hom, isOpenSubspace_preimage B S hS a₁.hom U₁.1 X₁.2 A₁.2 U₁.2⟩ with hV₁def
  set V₂ : OpenSubspaces B S hS A₂.1 :=
    ⟨U₂.1.preimage a₂.hom, isOpenSubspace_preimage B S hS a₂.hom U₂.1 X₂.2 A₂.2 U₂.2⟩ with hV₂def
  have hV₁qc : IsQuasiCompactSpace B S hS V₁.1.toFunctor := by
    have := isIso_fromPreimage_of_isBlowupAlong ha₁ U₁ hU₁Zc₁
    exact isQuasiCompactSpace_of_iso B S hS (asIso (U₁.1.fromPreimage a₁.hom)).symm hU₁qc
  have hV₂qc : IsQuasiCompactSpace B S hS V₂.1.toFunctor := by
    have := isIso_fromPreimage_of_isBlowupAlong ha₂ U₂ hU₂Zc₂
    exact isQuasiCompactSpace_of_iso B S hS (asIso (U₂.1.fromPreimage a₂.hom)).symm hU₂qc
  have hadm : ∀ {X A T T' : AlgebraicSpaces B S hS} {Uk : OpenSubspaces B S hS X.1}
      {K : ClosedSubspaces B S hS X₁₂.1} (p : X₁₂ ⟶ X) (a : A ⟶ X) (st : T ⟶ A) (c : T ⟶ X₁₂)
      (d : T' ⟶ T) (V : OpenSubspaces B S hS A.1), V.1 = Uk.1.preimage a.hom →
      Uk.1.preimage p.hom = Subfunctor.range sU.hom → st.hom ≫ a.hom = c.hom ≫ p.hom →
      IsFinitePresentation B S hS K.1.ι →
      Disjoint (subspacePointSet B S hS X₁₂.1 (Subfunctor.range sU.hom))
        (subspacePointSet B S hS X₁₂.1 K.1) →
      IsBlowupAlong B S hS (preimageClosedSubspace c K) d →
      IsAdmissibleBlowup B S hS ⟨V.1.preimage st.hom,
        isOpenSubspace_preimage B S hS st.hom V.1 A.2 T.2 V.2⟩ d := by
    intro X A T T' Uk K p a st c d V hV hO hsq hfp hdisj hd
    refine ⟨preimageClosedSubspace c K, isFinitePresentation_ι_preimage c K hfp, ?_, hd⟩
    have heq : V.1.preimage st.hom = (Subfunctor.range sU.hom).preimage c.hom := by
      rw [hV, ← hO, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, hsq]
    have := disjoint_subspacePointSet_preimage c.hom hdisj
    rw [← heq] at this
    exact this
  have hd₁adm := hadm p₁ a₁ st₁ c₁ d₁ V₁ rfl hO₁ (congrArg (fun k => k.hom) hsq₁) hK₂fp hOK₂ hd₁b
  have hd₂adm := hadm p₂ a₂ st₂ c₂ d₂ V₂ rfl hO₂ (congrArg (fun k => k.hom) hsq₂) hK₁fp hOK₁ hd₂b
  obtain ⟨X₁', g₁, e₁, hg₁, he₁, hpb₁⟩ := exists_isAdmissibleBlowup_isPullback_of_isOpenImmersion
    hZ hA₁qc hA₁qs V₁ hV₁qc st₁ hst₁ hT₁qc d₁ hd₁adm
  obtain ⟨X₂', g₂, e₂, hg₂, he₂, hpb₂⟩ := exists_isAdmissibleBlowup_isPullback_of_isOpenImmersion
    hZ hA₂qc hA₂qs V₂ hV₂qc st₂ hst₂ hT₂qc d₂ hd₂adm
  -- The composites are `U`-admissible blowups (Stacks 086C).
  have hB₁ : IsAdmissibleBlowup B S hS U₁ (g₁ ≫ a₁) :=
    isAdmissibleBlowup_comp_of_isQuasiCompactSpace hZ hX₁qc hX₁qs U₁
      ⟨Zc₁, hZc₁fp, hU₁Zc₁, ha₁⟩ hg₁
  have hB₂ : IsAdmissibleBlowup B S hS U₂ (g₂ ≫ a₂) :=
    isAdmissibleBlowup_comp_of_isQuasiCompactSpace hZ hX₂qc hX₂qs U₂
      ⟨Zc₂, hZc₂fp, hU₂Zc₂, ha₂⟩ hg₂
  -- `U` lifts to the common blowup `X₁₂'`.
  set β := d₁ ≫ c₁ with hβdef
  have hUlift : IsPullbackDefined B S hS sU (sumClosedSubspaces B S hS X₁₂ K₁ K₂) := by
    refine isEffectiveCartierDivisor_of_isEmpty_points B S hS U _
      (isEmpty_points_preimage_of_disjoint_range B S hS sU.hom _ ?_)
    change Disjoint _ (subspacePointSet B S hS X₁₂.1 (sumClosedSubspaces B S hS X₁₂ K₁ K₂).1)
    rw [subspacePointSet_sumClosedSubspaces]
    have hsub : Set.range (pointsMap B S hS U.1 sU.hom) ⊆
        subspacePointSet B S hS X₁₂.1 (Subfunctor.range sU.hom) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨pointsMap B S hS U.1 (Subfunctor.toRange sU.hom) x, ?_⟩
      rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
    exact Disjoint.mono_left hsub (Disjoint.union_right hOK₁ hOK₂)
  obtain ⟨lU, hlU, -⟩ := hβ.existsUnique_lift sU hUlift
  set u₁ := lU ≫ e₁ with hu₁def
  set u₂ := lU ≫ e₂ with hu₂def
  have he₁B : e₁ ≫ g₁ ≫ a₁ = β ≫ p₁ := by
    rw [← Category.assoc, ← hpb₁.w, Category.assoc, hsq₁, hβdef, Category.assoc]
  have he₂B : e₂ ≫ g₂ ≫ a₂ = β ≫ p₂ := by
    rw [← Category.assoc, ← hpb₂.w, Category.assoc, hsq₂, ← Category.assoc, hdd]
  have hu₁ : u₁ ≫ g₁ ≫ a₁ = j₁ := by
    rw [hu₁def, Category.assoc, he₁B, ← Category.assoc, hlU, hsU₁]
  have hu₂ : u₂ ≫ g₂ ≫ a₂ = j₂ := by
    rw [hu₂def, Category.assoc, he₂B, ← Category.assoc, hlU, hsU₂]
  -- `U` is an open subspace of `X_k'`, scheme-theoretically dense in `X₁'`.
  have hU' : ∀ {X X' : AlgebraicSpaces B S hS} (b : X' ⟶ X) (j : U ⟶ X) (v : U ⟶ X')
      [Mono j.hom] (hU : IsOpenSubspace B S hS (Subfunctor.range j.hom)),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range j.hom, hU⟩ b → v ≫ b = j →
        ∃ ψ : U.1 ≅ ((Subfunctor.range j.hom).preimage b.hom).toFunctor,
          ψ.hom ≫ ((Subfunctor.range j.hom).preimage b.hom).ι = v.hom := by
    intro X X' b j v _ hU hb hvb
    obtain ⟨Kb, -, hKbU, hKb⟩ := hb
    have := isIso_fromPreimage_of_isBlowupAlong hKb ⟨Subfunctor.range j.hom, hU⟩ hKbU
    exact Subfunctor.exists_iso_preimage_of_isIso_fromPreimage b.hom _ v.hom
      (Subfunctor.toRange j.hom)
      (by rw [Subfunctor.toRange_ι]; exact congrArg (fun k => k.hom) hvb)
  obtain ⟨ψ₁, hψ₁⟩ := hU' (g₁ ≫ a₁) j₁ u₁ U₁.2 hB₁ hu₁
  obtain ⟨ψ₂, hψ₂⟩ := hU' (g₂ ≫ a₂) j₂ u₂ U₂.2 hB₂ hu₂
  have hu₁o : IsOpenImmersion B S hS u₁.hom := by
    rw [← hψ₁]
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
      (isOpenSubspace_preimage B S hS _ U₁.1 X₁.2 X₁'.2 U₁.2).2
  have hu₂o : IsOpenImmersion B S hS u₂.hom := by
    rw [← hψ₂]
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
      (isOpenSubspace_preimage B S hS _ U₂.1 X₂.2 X₂'.2 U₂.2).2
  have hD : IsSchemeTheoreticallyDense B S hS (U₁.1.preimage (g₁ ≫ a₁).hom) := by
    obtain ⟨Kg₁, -, -, hKg₁⟩ := hg₁
    have h : IsSchemeTheoreticallyDense B S hS ((U₁.1.preimage a₁.hom).preimage g₁.hom) :=
      isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense
        g₁ Kg₁ hKg₁ (U₁.1.preimage a₁.hom) hd₁
    rwa [← Subfunctor.preimage_comp] at h
  have hDe : U₁.1.preimage (g₁ ≫ a₁).hom ≤ Subfunctor.range e₁.hom := by
    calc U₁.1.preimage (g₁ ≫ a₁).hom = Subfunctor.range (U₁.1.preimage (g₁ ≫ a₁).hom).ι :=
          (Subfunctor.range_ι _).symm
      _ = Subfunctor.range (ψ₁.inv ≫ u₁.hom) := by rw [← hψ₁, Iso.inv_hom_id_assoc]
      _ ≤ Subfunctor.range u₁.hom := Subfunctor.range_comp_le _ _
      _ ≤ Subfunctor.range e₁.hom := Subfunctor.range_comp_le lU.hom e₁.hom
  -- The structure morphisms `qₖ : Xₖ' ⟶ Y`.
  have hg₁p : IsProper B S hS g₁.hom := by
    obtain ⟨Kg₁, hKg₁fp, -, hKg₁⟩ := hg₁
    exact isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Kg₁ g₁ hKg₁fp hKg₁
  have hg₂p : IsProper B S hS g₂.hom := by
    obtain ⟨Kg₂, hKg₂fp, -, hKg₂⟩ := hg₂
    exact isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Kg₂ g₂ hKg₂fp hKg₂
  have hB₁p : IsProper B S hS (g₁ ≫ a₁).hom := isProper_comp B S hS X₁'.2 A₁.2 X₁.2 _ _ hg₁p ha₁p
  have hB₂p : IsProper B S hS (g₂ ≫ a₂).hom := isProper_comp B S hS X₂'.2 A₂.2 X₂.2 _ _ hg₂p ha₂p
  set q₁ := (g₁ ≫ a₁) ≫ f₁ with hq₁def
  set q₂ := (g₂ ≫ a₂) ≫ f₂ with hq₂def
  have hq₁sep : IsSeparated B S hS q₁.hom := isSeparated_comp B S hS _ _ hB₁p.1 hX₁sep
  have hq₂sep : IsSeparated B S hS q₂.hom := isSeparated_comp B S hS _ _ hB₂p.1 hX₂sep
  have hq₁ft : IsFiniteType B S hS q₁.hom := isFiniteType_comp' B S hS _ _ X₁.2 Y.2 hB₁p.2.1 hX₁ft
  have hq₂ft : IsFiniteType B S hS q₂.hom := isFiniteType_comp' B S hS _ _ X₂.2 Y.2 hB₂p.2.1 hX₂ft
  have hw : e₁ ≫ q₁ = e₂ ≫ q₂ := by
    simp only [hq₁def, hq₂def, Category.assoc, reassoc_of% he₁B, reassoc_of% he₂B, hpw]
  have hwh : e₁.hom ≫ q₁.hom = e₂.hom ≫ q₂.hom := congrArg (fun k => k.hom) hw
  -- `X₁₂' ⟶ X₁' ×_Y X₂'` is a proper immersion, hence a closed immersion (Stacks 04NX).
  let qm : pullback q₁.hom q₂.hom ⟶ pullback f₁.hom f₂.hom :=
    pullback.map q₁.hom q₂.hom f₁.hom f₂.hom (g₁ ≫ a₁).hom (g₂ ≫ a₂).hom (𝟙 Y.1)
      (Category.comp_id _) (Category.comp_id _)
  have hqm₁ : qm ≫ pullback.fst f₁.hom f₂.hom = pullback.fst q₁.hom q₂.hom ≫ (g₁ ≫ a₁).hom :=
    pullback.lift_fst _ _ _
  have hqm₂ : qm ≫ pullback.snd f₁.hom f₂.hom = pullback.snd q₁.hom q₂.hom ≫ (g₂ ≫ a₂).hom :=
    pullback.lift_snd _ _ _
  have hqmsep : IsSeparated B S hS qm := by
    refine isSeparated_of_comp B S hS qm (pullback.fst f₁.hom f₂.hom ≫ f₁.hom) ?_
    have heq : qm ≫ pullback.fst f₁.hom f₂.hom ≫ f₁.hom = pullback.fst q₁.hom q₂.hom ≫ q₁.hom := by
      rw [← Category.assoc, hqm₁, Category.assoc]
      rfl
    rw [heq]
    exact isSeparated_comp B S hS _ _ (isSeparated_pullbackFst B S hS q₁.hom hq₂sep) hq₁sep
  have hd₁p : IsProper B S hS d₁.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS _ d₁
      (isFinitePresentation_ι_preimage c₁ K₂ hK₂fp) hd₁b
  have hβp : IsProper B S hS β.hom := isProper_comp B S hS X₁₂'.2 T₁.2 X₁₂.2 _ _ hd₁p hc₁p
  have hprop : IsProper B S hS (pullback.lift e₁.hom e₂.hom hwh ≫ qm) := by
    have heq : pullback.lift e₁.hom e₂.hom hwh ≫ qm = β.hom ≫ Zs.ι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hqm₁, pullback.lift_fst_assoc, Category.assoc]
        exact congrArg (fun k => k.hom) he₁B
      · rw [Category.assoc, hqm₂, pullback.lift_snd_assoc, Category.assoc]
        exact congrArg (fun k => k.hom) he₂B
    rw [heq]
    exact isProper_comp B S hS X₁₂'.2 X₁₂.2 hP _ _ hβp
      (isProper_of_isClosedImmersion B S hS X₁₂.2 hP _ hZs.2)
  have hc : IsClosedImmersion B S hS (pullback.lift e₁.hom e₂.hom hwh) :=
    isClosedImmersion_lift_of_isProper X₁₂'.2 X₁'.2 X₂'.2 Y.2 hP hwh he₁ hq₂sep qm hqmsep hprop
  -- Glue `X₁'` and `X₂'` along `X₁₂'` (Stacks 0DVJ).
  obtain ⟨W, i₁, i₂, hpo, hi₁, hi₂, Uw, ε, hi₂ε, hsqW⟩ :=
    exists_isPushout_isOpenImmersion_of_isOpenImmersion e₁ e₂ he₁ he₂
  let g : W ⟶ Y := hpo.desc q₁ q₂ hw
  have h₁ : i₁ ≫ g = q₁ := hpo.inl_desc _ _ _
  have h₂ : i₂ ≫ g = q₂ := hpo.inr_desc _ _ _
  have hpbW : IsPullback e₁.hom e₂.hom i₁.hom i₂.hom :=
    isPullback_of_isClosedImmersion_lift hpo.w he₁ hi₁ hi₂ g h₁ h₂ hwh hc _ hD hDe
  have hgsep : IsSeparated B S hS g.hom :=
    isSeparated_of_isPullback_of_isClosedImmersion_lift hpbW hi₁ ε hi₂ε hsqW g h₁ h₂ hq₁sep
      hq₂sep hwh hc
  have hgft : IsFiniteType B S hS g.hom := by
    refine isFiniteType_of_isElementaryDistinguishedSquare hZ hsqW g hYqc hYqs ?_ ?_
    · have heq : Uw.ι ≫ g.hom = ε.inv ≫ q₂.hom := by
        rw [← h₂]
        change Uw.ι ≫ g.hom = ε.inv ≫ i₂.hom ≫ g.hom
        rw [hi₂ε, Category.assoc, Iso.inv_hom_id_assoc]
      rw [heq]
      exact isFiniteType_comp' B S hS _ _ X₂'.2 Y.2
        (isFiniteType_of_isClosedImmersion B S hS _ (isClosedImmersion_of_isIso B S hS _)) hq₂ft
    · rw [show i₁.hom ≫ g.hom = q₁.hom from congrArg (fun k => k.hom) h₁]
      exact hq₁ft
  refine ⟨X₁', X₂', W, g₁ ≫ a₁, g₂ ≫ a₂, i₁, i₂, g, u₁, u₂, hB₁, hB₂, hi₁, hi₂, hgsep, hgft,
    h₁, h₂, hu₁, hu₂, ?_, hu₁o, hu₂o⟩
  rw [hu₁def, hu₂def, Category.assoc, Category.assoc, hpo.w]

end AlgebraicGeometry.Space

end
