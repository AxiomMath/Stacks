module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpacePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionFormalAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionPointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleOpenPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesTypesSupplement

/-!
# The local type of the completion of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed. **Stacks 0GVW**
records the local type of the completion `X_{/T}` of `X` along `T`:

1. if `|X_red| \ T ⟶ |X_red|` is quasi-compact and `X` is locally countably indexed, then
   `X_{/T}` is locally countably indexed;
2. if `|X_red| \ T ⟶ |X_red|` is quasi-compact and `X` is locally adic\*, then `X_{/T}` is
   locally adic\*;
3. if `X` is locally Noetherian, then `X_{/T}` is locally Noetherian.

All three are proved by exhibiting one and the same atlas of `X_{/T}` and reading off its
members' type from the affine case, **Stacks 0GVV**. Clause (3) carries no quasi-compactness
hypothesis, the source observing that for a Noetherian space the hypothesis holds automatically
because `|X_red|` is then the spectrum of a Noetherian ring.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyCountablyIndexed_completionAlong'`: **clause (1)**.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionAlong'`: **clause (2)**.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionAlong'`: **clause (3)**.
* `AlgebraicGeometry.FormalSpace.complementCompactOnCharts_of_isQuasiCompactULift`: the
  transfer of the quasi-compactness of `|X_red| \ T ⟶ |X_red|` to the affine charts.

## The atlas

The three clauses share one construction,
`AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_completionSheafULift`, which is
the source's descent step: a covering `{X_k ⟶ X}` as in Definition 0AIM gives the family
`{(X_k)_{/T_k} ⟶ X_{/T}}` with `T_k` the inverse image of `T`, and that family is again a
covering as in Definition 0AIM because the completion square of **Stacks 0GVT** is cartesian:

* each member is an affine formal algebraic space by clause (1) of Stacks 0GVV;
* each `(X_k)_{/T_k} ⟶ X_{/T}` is representable by algebraic spaces and étale, being a base
  change of `X_k ⟶ X` along `X_{/T} ⟶ X`,
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_isPullback` applied to
  `AlgebraicGeometry.Space.isPullback_completionSheafMapULift`; and
* the induced map from the coproduct is a surjection of sheaves, because the coproduct of the
  base changes of a jointly surjective family is again a surjection,
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

The type of the members is read off separately, through the hypothesis `hP` of that
construction, so that the three clauses can share it. The predicates of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Types` — condition (2) of Stacks 0AKX — are the
conjunction of being a formal algebraic space with such an atlas, and both conjuncts are
supplied by the *same* atlas, exactly as in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes` for Stacks 0GXY.

Each member of the atlas is the completion of the chart `X_k` along a set of points of `X_k`,
while the affine clauses of Stacks 0GVV are stated for the completion along a set of points of
a *reduction* of the chart. The two are identified by
`AlgebraicGeometry.FormalSpace.completionSheafULift_preimage_eq_completionAlong`, using the
reduction of the chart — which exists, the chart being affine, by Stacks 0AIN for
affine formal algebraic spaces — and
`AlgebraicGeometry.FormalSpace.image_preimage_pointsMapULift`, which says that the inverse
image of `T` in the reduction of the chart is, viewed in the chart, the inverse image of `T`
viewed in `X`. So no reduction has to be chosen and Stacks 0AIN in general is not used.

## The quasi-compactness hypothesis

The source's hypothesis on clauses (1) and (2) is that the morphism `|X_red| \ T ⟶ |X_red|` be
quasi-compact. The open subspace `|X_red| \ T` of the algebraic space `X_red` is the subfunctor
`AlgebraicGeometry.Space.completionSubfunctorULift B S hS Xred.obj Tᶜ` of the sections of `X_red`
all of whose points lie outside `T` — the construction of the open subspace attached to an open
set of points in Stacks 03BZ, which for presheaves of `Type u` is
`AlgebraicGeometry.Space.openSubspaceOfPoints` — and its set of points is exactly `Tᶜ`,
`AlgebraicGeometry.Space.range_pointsMapULift_completionSubfunctorULift_ι`. The hypothesis is
quasi-compactness of its inclusion in the sense of Stacks 03HE,
`AlgebraicGeometry.Space.IsQuasiCompactULift`, stated verbatim.

The step of the source's proof that uses it is the transfer to each chart:
`|X_{k,red}| \ T_k ⟶ |X_{k,red}|` is quasi-compact by base change, hence — the chart being
affine — `|X_{k,red}| \ T_k` is quasi-compact, which is what the affine clauses (3) and (4) of
Stacks 0GVV ask for. That is
`AlgebraicGeometry.FormalSpace.complementCompactOnCharts_of_isQuasiCompactULift`, with
conclusion `AlgebraicGeometry.FormalSpace.ComplementCompactOnCharts`: the base change of the
inclusion along `X_{k,red} ⟶ X_red` is a quasi-compact algebraic space (Stacks 0BGR), so its
points form a compact space (Stacks 03E4), and they map onto `|X_{k,red}| \ T_k` (Stacks 03H4).

## What is assumed

Nothing beyond the source's hypotheses: `T` closed in `|X_red|`, and for clauses (1) and (2)
the quasi-compactness of `|X_red| \ T ⟶ |X_red|`.

* Closedness of `T` is read in `|X_red|`, where the affine clauses of Stacks 0GVV ask for it;
  its image in `|X|` is closed because the inclusion of a reduction is a homeomorphism on
  points, `AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`.
* Clause (1) of Stacks 0GVV, which makes the members of the atlas affine formal algebraic
  spaces, is `AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine`.
* Clauses (3), (4) and (5) of Stacks 0GVV are proved, with no input.
* The set-theoretic condition of Stacks 0AIS for `X_{/T}`, a clause of the definition 0AIM of a
  formal algebraic space, is proved from the condition for `X` in Stacks 0GVR,
  `satisfiesSetTheoreticCondition_completionAlong_of_isFormalAlgebraicSpace`.
* The reduction `i : X_red ⟶ X` is any reduction of `X`; one exists by Stacks 0AIN, and the
  statements hold for every one.

The unprimed declarations are earlier forms of the three clauses, with the quasi-compactness
read on the charts and with further inputs, all of which are now discharged.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0GVQ](https://stacks.math.columbia.edu/tag/0GVQ)
* [Stacks Project, Tag 0GVR](https://stacks.math.columbia.edu/tag/0GVR)
* [Stacks Project, Tag 0GVT](https://stacks.math.columbia.edu/tag/0GVT)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
* [Stacks Project, Tag 0GVW](https://stacks.math.columbia.edu/tag/0GVW)
* [Stacks Project, Tag 0GXY](https://stacks.math.columbia.edu/tag/0GXY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The atlas of a completion -/

/-- **The atlas of a completion.** An atlas `{X_k ⟶ X}` as in Definition 0AIM all of whose
members have a property `P` induces one for the completion `X_{/T}` of `X` along a closed set
`T` of points of `X`, by the completions `(X_k)_{/T_k}` of the charts along the inverse images
`T_k` of `T`.

The completion square of Stacks 0GVT exhibits each `(X_k)_{/T_k} ⟶ X_{/T}` as a base change of
`X_k ⟶ X` along `X_{/T} ⟶ X`, which gives representability and étaleness and makes the family
jointly surjective because `{X_k ⟶ X}` is; the members are affine formal algebraic spaces by
`haff`, clause (1) of Stacks 0GVV. That they have `P` is read off separately, which is where
`hP` enters, so that the three clauses of Stacks 0GVW share this one construction. -/
theorem hasAffineEtaleAtlasWithProperty_completionSheafULift {X : FppfSheaf B S hS}
    (P : FppfSheaf B S hS → Prop) (T : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) T)
    (hatlas : HasAffineEtaleAtlasWithProperty B S hS X P)
    (haff : CompletionOfAffineIsAffine B S hS)
    (hP : ∀ (Y : FppfSheaf B S hS) (f : Y ⟶ X), IsRepresentableEtale B S hS f →
      IsAffineFormalAlgebraicSpace B S hS Y → P Y →
      P (Space.completionSheafULift B S hS Y
        (Space.pointsMapULift.{u + 1} B S hS Y.obj f.hom ⁻¹' T))) :
    HasAffineEtaleAtlasWithProperty B S hS (Space.completionSheafULift B S hS X T) P := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, g, hXiaff, hg, hcov, hXiP⟩ := hatlas
  let Ti : ∀ k : I, Set (Space.pointsULift.{u + 1} B S hS (Xi k).obj) := fun k ↦
    Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T
  have hsub : ∀ k, Ti k ⊆ Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T :=
    fun _ _ hx ↦ hx
  have hsup : ∀ k, Space.pointsMapULift.{u + 1} B S hS (Xi k).obj (g k).hom ⁻¹' T ⊆ Ti k :=
    fun _ _ hx ↦ hx
  have hsq : ∀ k, IsPullback
      (Space.completionSheafULiftInclusion B S hS (Xi k) (Ti k))
      (Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k))
      (g k)
      (Space.completionSheafULiftInclusion B S hS X T) := fun k ↦
    Space.isPullback_completionSheafMapULift B S hS (g k) (Ti k) T (hsub k) (hsup k)
  refine ⟨I, fun k ↦ Space.completionSheafULift B S hS (Xi k) (Ti k),
    fun k ↦ Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k), ?_, ?_, ?_,
    fun k ↦ hP (Xi k) (g k) (hg k) (hXiaff k) (hXiP k)⟩
  · intro k
    refine haff (Xi k) (hXiaff k) (Ti k) ?_
    let _instChart := Space.pointTopologyULift.{u + 1} B S hS (Xi k).obj
    let _instAmbient := Space.pointTopologyULift.{u + 1} B S hS X.obj
    exact hT.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS (g k).hom)
  · exact fun k ↦ isRepresentableEtale_of_isPullback B S hS (hsq k) (hg k)
  · let φ := Space.completionSheafULiftInclusion B S hS X T
    let e : ∀ k, Space.completionSheafULift B S hS (Xi k) (Ti k) ≅ pullback (g k) φ :=
      fun k ↦ (hsq k).isoPullback
    let t : (∐ fun k ↦ Space.completionSheafULift B S hS (Xi k) (Ti k)) ⟶
        (∐ fun k ↦ pullback (g k) φ) :=
      Sigma.desc fun k ↦ (e k).hom ≫ Sigma.ι (fun j ↦ pullback (g j) φ) k
    have hts : IsSplitEpi t :=
      ⟨⟨Sigma.desc fun k ↦ (e k).inv ≫ Sigma.ι
          (fun j ↦ Space.completionSheafULift B S hS (Xi j) (Ti j)) k, by
        refine Sigma.hom_ext _ _ fun k ↦ ?_
        simp [t]⟩⟩
    have hfac : (Sigma.desc fun k ↦
          Space.completionSheafMapULift B S hS (g k) (Ti k) T (hsub k)) =
        t ≫ Sigma.desc fun k ↦ pullback.snd (g k) φ := by
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      simp only [t, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
      exact ((hsq k).isoPullback_hom_snd).symm
    rw [hfac, Sheaf.isLocallySurjective_iff_epi]
    have _ : Epi t := hts.epi
    have _ : Epi (Sigma.desc fun k ↦ pullback.snd (g k) φ) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ g hcov)
    exact epi_comp t _

/-- The member of the atlas of `X_{/T}` cut out by a chart `f : Y ⟶ X` — the completion of `Y`
along the inverse image in `|Y|` of `T` viewed in `|X|` — is the completion of `Y` along the
inverse image of `T` in the points of a reduction of `Y`, which is the spelling in which the
affine clauses of Stacks 0GVV are stated. -/
theorem completionSheafULift_preimage_eq_completionAlong {X Xred : FppfSheaf B S hS}
    {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) {Y Yred : FppfSheaf B S hS}
    {j : Yred ⟶ Y} (hj : IsReduction B S hS Y Yred j) (f : Y ⟶ X) :
    Space.completionSheafULift B S hS Y
        (Space.pointsMapULift.{u + 1} B S hS Y.obj f.hom ⁻¹'
          (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)) =
      completionAlong j
        (Space.pointsMapULift.{u + 1} B S hS Yred.obj (reductionMap hj hi f).hom ⁻¹' T) :=
  congrArg (Space.completionSheafULift B S hS Y)
    (image_preimage_pointsMapULift hj hi f T).symm

/-! ### The quasi-compactness hypothesis -/

/-- The source's hypothesis that `|X_red| \ T ⟶ |X_red|` be quasi-compact, read in the form in
which the descent of Stacks 0GVW uses it: for every affine formal algebraic space `Y` over `S`
with a reduction `j : Y_red ⟶ Y`, mapping to `X` by a morphism representable by algebraic
spaces and étale, the complement of the inverse image of `T` in `|Y_red|` is quasi-compact.
That is the hypothesis of clauses (3) and (4) of Stacks 0GVV on the chart `Y`, and it is what
quasi-compactness of `|X_red| \ T ⟶ |X_red|` gives there by base change. See the section "The
quasi-compactness hypothesis" of this file. -/
abbrev ComplementCompactOnCharts {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj)) : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (j : Yred ⟶ Y) (hj : IsReduction B S hS Y Yred j),
    IsAffineFormalAlgebraicSpace B S hS Y → ∀ f : Y ⟶ X, IsRepresentableEtale B S hS f →
      @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj)
        (Space.pointsMapULift.{u + 1} B S hS Yred.obj (reductionMap hj hi f).hom ⁻¹' T)ᶜ

section SourceQuasiCompactness

attribute [local instance] Space.pointTopologyULift

/-! ### The source's quasi-compactness hypothesis

The open subspace `|X_red| \ T` of `X_red` is the subfunctor
`AlgebraicGeometry.Space.completionSubfunctorULift B S hS Xred.obj Tᶜ` of the sections of `X_red`
all of whose points lie outside `T`: this is the construction of the open subspace attached to an
open set of points in Stacks 03BZ (`AlgebraicGeometry.Space.openSubspaceOfPoints` in the value
universe of the site), it is an fppf sheaf by
`AlgebraicGeometry.Space.isSheaf_completionSubfunctorULift`, and its set of points is exactly
`Tᶜ` by `AlgebraicGeometry.Space.range_pointsMapULift_completionSubfunctorULift_ι`. The source's
hypothesis that `|X_red| \ T ⟶ |X_red|` be quasi-compact is therefore
`AlgebraicGeometry.Space.IsQuasiCompactULift` (Stacks 03HE) of the inclusion of that subfunctor,
and it gives `AlgebraicGeometry.FormalSpace.ComplementCompactOnCharts` by base change:
`AlgebraicGeometry.FormalSpace.complementCompactOnCharts_of_isQuasiCompactULift`. -/

/-- **The points of the subfunctor of sections with point-set image in `T` are exactly `T`.**
A field-valued point of the subfunctor is a section whose point-set image lies in `T`, tested at
the identity field-valued point of the field spectrum carrying it; conversely the section of a
field-valued point of `X` whose class lies in `T` has point-set image in `T`, every field-valued
point of its field spectrum restricting it to a point with the same class. -/
theorem _root_.AlgebraicGeometry.Space.range_pointsMapULift_completionSubfunctorULift_ι
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (T : Set (Space.pointsULift.{u + 1} B S hS X)) :
    Set.range (Space.pointsMapULift.{u + 1} B S hS
      (Space.completionSubfunctorULift B S hS X T).toFunctor
      (Space.completionSubfunctorULift B S hS X T).ι) = T := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Quot.ind with
    | _ p =>
      have hmem := p.value.2
        ({ carrier := p.carrier
           contained := p.contained
           toBase := p.toBase
           value := 𝟙 (p.siteObject B S hS
             (Space.completionSubfunctorULift B S hS X T).toFunctor) } :
          Space.FieldValuedPoint B S hS
            (yoneda.obj (p.siteObject B S hS
              (Space.completionSubfunctorULift B S hS X T).toFunctor)))
      have hval : X.map (𝟙 (p.siteObject B S hS
            (Space.completionSubfunctorULift B S hS X T).toFunctor)).op p.value.1 =
          p.value.1 := by
        simp
      exact Set.mem_of_eq_of_mem (congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
        Space.FieldValuedPointULift.{u + 1} B S hS X).class B S hS X) hval.symm) hmem
  · intro hx
    induction x using Quot.ind with
    | _ p =>
      let U : BigFppfOver B S hS := p.siteObject B S hS X
      let e : Space.FieldValuedPoint B S hS (yoneda.obj U) :=
        { carrier := p.carrier
          contained := p.contained
          toBase := p.toBase
          value := 𝟙 U }
      have himage : Space.HasImageInULift B S hS X T U p.value := by
        intro r
        have h := Space.class_restrict_eq_of_hasCommonExtension B S hS X U p.value
          (p := r) (q := e)
          ⟨r, Space.FieldValuedPoint.dominates_refl B S hS _ r, ⟨r.value, by
            show r.value ≫ 𝟙 U = r.value
            exact Category.comp_id _⟩⟩
        rw [h]
        have hval : X.map (𝟙 U).op p.value = p.value := by simp
        exact Set.mem_of_eq_of_mem (congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
          Space.FieldValuedPointULift.{u + 1} B S hS X).class B S hS X) hval) hx
      exact ⟨Space.FieldValuedPointULift.class B S hS _
        ⟨p.carrier, p.contained, p.toBase, ⟨p.value, himage⟩⟩, rfl⟩

/-- **Quasi-compactness of `|W| \ T ⟶ |W|` gives quasi-compactness of the complement of the
inverse image of `T` in every quasi-compact algebraic space mapping to `W`.** The base change of
the inclusion of the open subspace along `g : Z ⟶ W` is a quasi-compact algebraic space — an
fppf sheaf, being a fibre product of sheaves, with a surjective étale atlas by a quasi-compact
scheme, hence an algebraic space by Stacks 0BGR — so its points form a compact space (Stacks
03E4); and its points map onto the complement of `|g|⁻¹ T`, by Stacks 03H4 and because the open
subspace has exactly the points outside `T`. -/
theorem isCompact_compl_preimage_of_isQuasiCompactULift {Z W : FppfSheaf B S hS}
    (hZ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj)
    (hZqc : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Z.obj) (g : Z.obj ⟶ W.obj)
    (T : Set (Space.pointsULift.{u + 1} B S hS W.obj))
    (hqc : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSubfunctorULift B S hS W.obj Tᶜ).ι) :
    @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Z.obj)
      (Space.pointsMapULift.{u + 1} B S hS Z.obj g ⁻¹' T)ᶜ := by
  let ι := (Space.completionSubfunctorULift B S hS W.obj Tᶜ).ι
  let V : FppfSheaf B S hS :=
    ⟨_, Space.isSheaf_completionSubfunctorULift B S hS W Tᶜ⟩
  let gs : Z ⟶ W := ObjectProperty.homMk g
  let ιs : V ⟶ W := ObjectProperty.homMk ι
  have hsq : IsPullback (pullback.fst gs ιs).hom (pullback.snd gs ιs).hom g ι :=
    (IsPullback.of_hasPullback gs ιs).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hPsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback g ι) :=
    (Presheaf.isSheaf_of_iso_iff hsq.isoPullback).mp (pullback gs ιs).2
  obtain ⟨U, a, hUc, hs, he⟩ := hqc Z.obj hZ hZqc g
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g ι) :=
    Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS hPsheaf
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS U) a hs
      ((Space.isEtaleULift_iff_relative_etale B S hS a).mp he)
  have hPc : @CompactSpace _ (Space.pointTopologyULift.{u + 1} B S hS (pullback g ι)) :=
    Space.compactSpace_pointsULift_of_isQuasiCompactSpaceULift B S hS hPalg
      ⟨U, a, hUc, hs, he⟩
  have hι := Space.range_pointsMapULift_completionSubfunctorULift_ι B S hS W.obj Tᶜ
  have hrange : Set.range (Space.pointsMapULift.{u + 1} B S hS _ (pullback.fst g ι)) =
      (Space.pointsMapULift.{u + 1} B S hS Z.obj g ⁻¹' T)ᶜ := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      rw [Set.mem_compl_iff, Set.mem_preimage,
        Space.pointsMapULift_apply_comm B S hS pullback.condition v]
      exact (Set.ext_iff.mp hι _).mp ⟨_, rfl⟩
    · intro hy
      obtain ⟨b, hb⟩ := (Set.ext_iff.mp hι _).mpr hy
      obtain ⟨v, hv, -⟩ := Space.exists_pointsULift_of_isPullback B S hS
        (IsPullback.of_hasPullback g ι) y b hb.symm
      exact ⟨v, hv⟩
  rw [← hrange]
  exact isCompact_range (Space.continuous_pointsMapULift B S hS _)

/-- **The source's quasi-compactness hypothesis gives its transfer to the charts.** If
`|X_red| \ T ⟶ |X_red|` is quasi-compact then for every affine formal algebraic space `Y` with a
reduction `Y_red`, mapping to `X` by a morphism representable by algebraic spaces and étale, the
complement of the inverse image of `T` in `|Y_red|` is quasi-compact: `Y_red` is a quasi-compact
algebraic space — its points are those of `Y`, which form a compact space, the reduction being a
homeomorphism on points — so `isCompact_compl_preimage_of_isQuasiCompactULift` applies to the
induced morphism of reductions. This is the step of the proof of Stacks 0GVW that uses the
hypothesis. -/
theorem complementCompactOnCharts_of_isQuasiCompactULift {X Xred : FppfSheaf B S hS}
    {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hqc : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSubfunctorULift B S hS Xred.obj Tᶜ).ι) :
    ComplementCompactOnCharts B S hS hi T := by
  intro Y Yred j hj hYaff f _
  obtain ⟨V, a, hV, ha⟩ :=
    exists_compact_pointsSurjection_of_isAffineFormalAlgebraicSpace B S hS Y hYaff
  have hYc : CompactSpace (Space.pointsULift.{u + 1} B S hS Y.obj) :=
    @Function.Surjective.compactSpace _ _ _ _ _ (Space.continuous_pointsMapULift B S hS a)
      (Space.compactSpace_pointsULift_uliftYoneda.{u + 1} B S hS V hV) ha
  have hYredc : CompactSpace (Space.pointsULift.{u + 1} B S hS Yred.obj) :=
    (hj.isHomeomorph_pointsMapULift.homeomorph _).symm.compactSpace
  exact isCompact_compl_preimage_of_isQuasiCompactULift B S hS hj.algebraic
    (Space.isQuasiCompactSpaceULift_of_compactSpace_pointsULift B S hS hj.algebraic hYredc)
    (reductionMap hj hi f).hom T hqc

end SourceQuasiCompactness

/-! ### Clause (1): the completion of a locally countably indexed space -/

/-- The set-theoretic condition of Stacks 0AIS for all completions gives it for the completion
along a set of points of a reduction, that being a completion along the corresponding set of
points of the space itself. -/
private theorem satisfiesSetTheoreticCondition_completionAlong
    (hsetAll : ∀ (Y : FppfSheaf B S hS) (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)),
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y W))
    {Y Yred : FppfSheaf B S hS} (j : Yred ⟶ Y)
    (V : Set (Space.pointsULift.{u + 1} B S hS Yred.obj)) :
    SatisfiesSetTheoreticCondition B S hS (completionAlong j V) :=
  hsetAll Y (Space.pointsMapULift.{u + 1} B S hS Yred.obj j.hom '' V)

/-- The set-theoretic condition of Stacks 0AIS for the completion `X_{/T}` of a formal algebraic
space along a closed subset of a reduction: it is
`satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition`
of Stacks 0GVR, from the condition for `X` itself. -/
theorem satisfiesSetTheoreticCondition_completionAlong_of_isFormalAlgebraicSpace
    {X Xred : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i) (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    SatisfiesSetTheoreticCondition B S hS (completionAlong i T) :=
  satisfiesSetTheoreticCondition_completionSheafULift_of_satisfiesSetTheoreticCondition B S hS
    X hX.1 _ (hi.isClosed_image_pointsMapULift hT)

/-- The completion along a closed set of a reduction of a formal algebraic space with an atlas
with property `P` is a formal algebraic space with such an atlas, once the completion of each
chart along the inverse image of `T` in a reduction of the chart has `P`. -/
private theorem completionAlong_isFormalAlgebraicSpace_and_atlas {X Xred : FppfSheaf B S hS}
    {P : FppfSheaf B S hS → Prop} (hX : IsFormalAlgebraicSpace B S hS X)
    (hatlas : HasAffineEtaleAtlasWithProperty B S hS X P) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hP : ∀ (Y : FppfSheaf B S hS) (f : Y ⟶ X), IsRepresentableEtale B S hS f →
      IsAffineFormalAlgebraicSpace B S hS Y → P Y → ∀ (Yred : FppfSheaf B S hS) (j : Yred ⟶ Y)
        (hj : IsReduction B S hS Y Yred j), P (completionAlong j
          (Space.pointsMapULift.{u + 1} B S hS Yred.obj (reductionMap hj hi f).hom ⁻¹' T))) :
    IsFormalAlgebraicSpace B S hS (completionAlong i T) ∧
      HasAffineEtaleAtlasWithProperty B S hS (completionAlong i T) P := by
  have hatlas' : HasAffineEtaleAtlasWithProperty B S hS (completionAlong i T) P := by
    refine hasAffineEtaleAtlasWithProperty_completionSheafULift B S hS P
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T)
      (hi.isClosed_image_pointsMapULift hT) hatlas (completionOfAffineIsAffine B S hS) ?_
    intro Y f hf hYaff hYP
    obtain ⟨Yred, j, hj⟩ := exists_isReduction_of_isAffineFormalAlgebraicSpace B S hS Y hYaff
    rw [completionSheafULift_preimage_eq_completionAlong B S hS hi T hj f]
    exact hP Y f hf hYaff hYP Yred j hj
  exact ⟨isFormalAlgebraicSpace_of_hasAffineEtaleAtlasWithProperty B S hS
    (satisfiesSetTheoreticCondition_completionAlong_of_isFormalAlgebraicSpace B S hS hX hi T hT)
    hatlas', hatlas'⟩

/-- **Clause (1) of Stacks 0GVW, from the quasi-compactness on the charts.** If `X` is locally
countably indexed and the complement of the inverse image of `T` is quasi-compact on every
affine chart of `X`, then `X_{/T}` is locally countably indexed: the completions of the charts
of `X` along the inverse images of `T` form an atlas as in Definition 0AIM, and each of them is
a countably indexed affine formal algebraic space by clause (3) of Stacks 0GVV. The
set-theoretic condition of Stacks 0AIS for `X_{/T}` is
`satisfiesSetTheoreticCondition_completionAlong_of_isFormalAlgebraicSpace`. -/
theorem isLocallyCountablyIndexed_completionAlong_of_complementCompactOnCharts
    {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyCountablyIndexed B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : ComplementCompactOnCharts B S hS hi T) :
    IsLocallyCountablyIndexed B S hS (completionAlong i T) := by
  exact completionAlong_isFormalAlgebraicSpace_and_atlas B S hS hX.1 hX.2 hi T hT
    fun Y f hf hYaff hYP Yred j hj ↦ isCountablyIndexed_completionAlong' B S hS hYP hj _
      (isClosed_preimage_pointsMapULift (reductionMap hj hi f) T hT)
      (hqc Y Yred j hj hYaff f hf)

/-- **Clause (1) of Stacks 0GVW.** Let `S` be a scheme, let `X` be a formal algebraic space
over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed such that
the inclusion `|X_red| \ T ⟶ |X_red|` of the open subspace with points `|X_red| \ T` is
quasi-compact. If `X` is locally countably indexed then so is the completion `X_{/T}` of `X`
along `T`.

The open subspace `|X_red| \ T` is the subfunctor of the sections of `X_red` with point-set
image in `Tᶜ`, and the hypothesis `hqc` is quasi-compactness of its inclusion in the sense of
Stacks 03HE; see the section "The source's quasi-compactness hypothesis" of this file. It is
transferred to the charts by `complementCompactOnCharts_of_isQuasiCompactULift`, and the
statement follows from
`isLocallyCountablyIndexed_completionAlong_of_complementCompactOnCharts`. Nothing else is
assumed. -/
@[stacks 0GVW "clause (1): if the complement of `T` is quasi-compact and `X` is locally \
countably indexed then so is `X_{/T}` (`IsLocallyCountablyIndexed`, Stacks 0AKY). Binders \
are exactly the source's data: `T` closed in `|X_red|`, and quasi-compactness \
(Stacks 03HE, `Space.IsQuasiCompactULift`) of the inclusion of the open subspace \
`|X_red| \\ T` (the subfunctor of sections with point-set image in `Tᶜ`). The set-theoretic \
condition of 0AIS is proved (0GVR), clause (1) of 0GVV is proved \
(`completionOfAffineIsAffine`), clause (3) of 0GVV is proved \
(`isCountablyIndexed_completionAlong'`)."]
theorem isLocallyCountablyIndexed_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyCountablyIndexed B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSubfunctorULift B S hS Xred.obj Tᶜ).ι) :
    IsLocallyCountablyIndexed B S hS (completionAlong i T) :=
  isLocallyCountablyIndexed_completionAlong_of_complementCompactOnCharts B S hS hX hi T hT
    (complementCompactOnCharts_of_isQuasiCompactULift B S hS hi T hqc)

/-- **Clause (1) of Stacks 0GVW**, with the quasi-compactness hypothesis read on the charts
and with further inputs which are all proved.

`isLocallyCountablyIndexed_completionAlong'` is the source's statement: there `hqc` is
quasi-compactness of `|X_red| \ T ⟶ |X_red|`, and `hTX`, `haff`, `hspf` and `hset` are
discharged. -/
theorem isLocallyCountablyIndexed_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyCountablyIndexed B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hTX : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T))
    (hqc : ComplementCompactOnCharts B S hS hi T)
    (haff : CompletionOfAffineIsAffine B S hS)
    (hspf : CompletionOfCountablyIndexedIsCountableSpf B S hS)
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsLocallyCountablyIndexed B S hS (completionAlong i T) :=
  isLocallyCountablyIndexed_completionAlong_of_complementCompactOnCharts B S hS hX hi T hT hqc

/-! ### Clause (2): the completion of a locally adic\* space -/

/-- **Clause (2) of Stacks 0GVW, from the quasi-compactness on the charts.** If `X` is locally
adic\* and the complement of the inverse image of `T` is quasi-compact on every affine chart of
`X`, then `X_{/T}` is locally adic\*: the completions of the charts of `X` along the inverse
images of `T` form an atlas as in Definition 0AIM, and each of them is an adic\* affine formal
algebraic space by clause (4) of Stacks 0GVV. -/
theorem isLocallyAdicStar_completionAlong_of_complementCompactOnCharts
    {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : ComplementCompactOnCharts B S hS hi T) :
    IsLocallyAdicStar B S hS (completionAlong i T) := by
  exact completionAlong_isFormalAlgebraicSpace_and_atlas B S hS hX.1 hX.2 hi T hT
    fun Y f hf hYaff hYP Yred j hj ↦ isAdicStar_completionAlong' B S hS hYP hj _
      (isClosed_preimage_pointsMapULift (reductionMap hj hi f) T hT)
      (hqc Y Yred j hj hYaff f hf)

/-- **Clause (2) of Stacks 0GVW.** Let `S` be a scheme, let `X` be a formal algebraic space
over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed such that
the inclusion `|X_red| \ T ⟶ |X_red|` of the open subspace with points `|X_red| \ T` is
quasi-compact. If `X` is locally adic\* then so is the completion `X_{/T}` of `X` along `T`.

The hypothesis `hqc` is read as for clause (1), `isLocallyCountablyIndexed_completionAlong'`.
Nothing else is assumed. -/
@[stacks 0GVW "clause (2): if the complement of `T` is quasi-compact and `X` is locally adic* \
then so is `X_{/T}` (`IsLocallyAdicStar`, Stacks 0AKY). Binders are exactly the source's \
data: `T` closed in `|X_red|`, and quasi-compactness (Stacks 03HE, \
`Space.IsQuasiCompactULift`) of the inclusion of the open subspace `|X_red| \\ T` (the \
subfunctor of sections with point-set image in `Tᶜ`). The set-theoretic condition of 0AIS is \
proved (0GVR), clause (4) of 0GVV is proved (`isAdicStar_completionAlong'`)."]
theorem isLocallyAdicStar_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Space.completionSubfunctorULift B S hS Xred.obj Tᶜ).ι) :
    IsLocallyAdicStar B S hS (completionAlong i T) :=
  isLocallyAdicStar_completionAlong_of_complementCompactOnCharts B S hS hX hi T hT
    (complementCompactOnCharts_of_isQuasiCompactULift B S hS hi T hqc)

/-- **Clause (2) of Stacks 0GVW**, with the quasi-compactness hypothesis read on the charts
and with further inputs which are all proved.

`isLocallyAdicStar_completionAlong'` is the source's statement: there `hqc` is
quasi-compactness of `|X_red| \ T ⟶ |X_red|`, and `hTX`, `haff`, `hideal` and `hsetAll` are
discharged. -/
theorem isLocallyAdicStar_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hTX : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T))
    (hqc : ComplementCompactOnCharts B S hS hi T)
    (haff : CompletionOfAffineIsAffine B S hS)
    (hideal : CompletionOfAdicStarIsCompletionAlongFGIdeal B S hS)
    (hsetAll : ∀ (Y : FppfSheaf B S hS) (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)),
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y W)) :
    IsLocallyAdicStar B S hS (completionAlong i T) :=
  isLocallyAdicStar_completionAlong_of_complementCompactOnCharts B S hS hX hi T hT hqc

/-! ### Clause (3): the completion of a locally Noetherian space -/

/-- **Clause (3) of Stacks 0GVW.** Let `S` be a scheme, let `X` be a formal algebraic space
over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed. If `X` is
locally Noetherian then so is the completion `X_{/T}` of `X` along `T`: the completions of the
charts of `X` along the inverse images of `T` form an atlas as in Definition 0AIM, and each of
them is a Noetherian affine formal algebraic space by clause (5) of Stacks 0GVV. No
quasi-compactness hypothesis is needed, the source observing that it holds automatically
because `|X_red|` is then the spectrum of a Noetherian ring.

Nothing is assumed beyond the source's hypotheses: the set-theoretic condition of Stacks 0AIS
for `X_{/T}` is `satisfiesSetTheoreticCondition_completionAlong_of_isFormalAlgebraicSpace`
(Stacks 0GVR), and clause (5) of Stacks 0GVV is
`AlgebraicGeometry.FormalSpace.isNoetherian_completionAlong'`. -/
@[stacks 0GVW "clause (3): if `X` is locally Noetherian then so is `X_{/T}` \
(`IsLocallyNoetherian`, Stacks 0AKY); deliberately NO quasi-compactness hypothesis, as in the \
source. Binders are exactly the source's data: `T` closed in `|X_red|`. The \
set-theoretic condition of 0AIS is proved (0GVR), clause (5) of 0GVV is proved \
(`isNoetherian_completionAlong'`)."]
theorem isLocallyNoetherian_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    IsLocallyNoetherian B S hS (completionAlong i T) := by
  exact completionAlong_isFormalAlgebraicSpace_and_atlas B S hS hX.1 hX.2 hi T hT
    fun Y f hf hYaff hYP Yred j hj ↦ isNoetherian_completionAlong' B S hS hYP hj _
      (isClosed_preimage_pointsMapULift (reductionMap hj hi f) T hT)

/-- **Clause (3) of Stacks 0GVW**, with further inputs which are all proved.

`isLocallyNoetherian_completionAlong'` is the source's statement, with `hTX`, `haff`, `hideal`
and `hsetAll` discharged. -/
theorem isLocallyNoetherian_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hTX : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T))
    (haff : CompletionOfAffineIsAffine B S hS)
    (hideal : CompletionOfNoetherianIsCompletionAlongNoetherianIdeal B S hS)
    (hsetAll : ∀ (Y : FppfSheaf B S hS) (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)),
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y W)) :
    IsLocallyNoetherian B S hS (completionAlong i T) :=
  isLocallyNoetherian_completionAlong' B S hS hX hi T hT

end AlgebraicGeometry.FormalSpace

end
