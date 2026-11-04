module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# The completion of an algebraic space along a closed subset is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `T ⊆ |X|` be a closed subset. **Stacks 0AIZ** says that the completion `X_{/T}` of `X`
along `T` — the functor sending an object `U` of the big fppf site of `S` to the morphisms
`f : U ⟶ X` with `f(|U|) ⊆ T` — is a formal algebraic space over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf`: **Stacks 0AIZ**.

## The atlas

The proof is the source's: an étale covering `{X_i ⟶ X}` of `X` by affine schemes gives the
family `{(X_i)_{/T_i} ⟶ X_{/T}}` with `T_i` the inverse image of `T`, and that family is an
atlas as in Definition 0AIM because the completion square of Stacks 0APV is cartesian:

* each `(X_i)_{/T_i} ⟶ X_{/T}` is representable by algebraic spaces, which is Stacks 0APV,
  `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`;
* each is étale, because the square `AlgebraicGeometry.Space.isPullback_completionSheafMap` of
  Stacks 0APV exhibits it as a base change of `X_i ⟶ X` along `X_{/T} ⟶ X`; and
* the induced map from the coproduct is a surjection of sheaves, because the coproduct of the
  base changes of a jointly surjective family is again a surjection,
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

Each member is an affine formal algebraic space by the affine case of 0AIZ, which is formalized as
Stacks 0AIY, `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf`.

## What is assumed

Three things.

* The affine étale atlas of `X` itself: the charts `Spec A_i`, their étaleness and their joint
  surjectivity, read in the value universe `Type (u + 1)` of the formal algebraic spaces, that
  is for the sheafified universe lifts `AlgebraicGeometry.Space.sheafifiedULift`. Every
  algebraic space has an étale atlas by an object of the site — the field `exists_atlas` of
  `AlgebraicGeometry.IsAlgebraicSpace` — and the site's objects have affine étale coverings
  (`AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`), but neither statement is
  available in this universe-lifted sheaf form, so the atlas is carried as data, exactly as in
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSubspace` (Stacks 0GXY). This is
  the source's appeal to Properties of Spaces, Lemma 0BGL.

* The chart-level description of the set of points: that the inverse image of `T` on each chart
  is the set of points supported in a closed subset `T_i` of the chart, which is what makes the
  affine case applicable. This is the step of the source's proof reading the `U`-valued points
  of `X_{/T} ×_X X_i` as the morphisms `U ⟶ X_i` with image in `g_i^{-1}(T)`.

* The hypothesis `AlgebraicGeometry.FormalSpace.HasStageAtlas` of the affine case, per chart.
  That is the set-theoretic hypothesis already carried by Stacks 0AIY: the chosen
  big fppf site must carry an atlas for the colimit presenting the chart completion. See the
  implementation notes of
  `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan`.

The set-theoretic condition of Stacks 0AIS for `X_{/T}` is *not* assumed: it is one of the two
conjuncts of the conclusion, and the atlas supplies it through the assumed atlas of `X` only in
so far as the latter is carried, so it is a hypothesis of the shared atlas construction below
and is discharged in the statement of 0AIZ exactly as Stacks 0AJ1 does, by carrying it. It is
named `hset` there.

## Implementation notes

The charts are affine schemes `Spec A_i` lying in the site, presented as
`AlgebraicGeometry.FormalSpace.affineOver` with a structure morphism to `S`, which is the form
Stacks 0AIY consumes; every affine object of the site is of that form up to
isomorphism. Taking the charts in that form rather than as arbitrary affine objects of the site
lets the inverse image of `T` be rewritten into
`AlgebraicGeometry.FormalSpace.supportedPoints` and 0AIY be applied on the nose, with no
transport along an isomorphism of sheaves.

`AlgebraicGeometry.FormalSpace.HasAffineEtaleAtlasWithProperty` at the trivial property is used
to package the atlas, so that the construction can be reused at a nontrivial property for the
local types of `X_{/T}`.

## References

* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The atlas of the completion -/

variable {B S hS}

/-- **The completed charts of an étale covering cover the completion.** For an étale covering
`{Spec A_i ⟶ X}` of an algebraic space `X` over `S` by affine schemes lying in the site, read in
the value universe of the formal algebraic spaces, and a set `T` of points of `X`, each completed
chart `(Spec A_i)_{/T_i} ⟶ X_{/T}` is representable by algebraic spaces and étale, and together
they are jointly surjective.

The completion square of Stacks 0APV exhibits each completed chart as a base change of
`Spec A_i ⟶ X` along `X_{/T} ⟶ X`, which gives representability and étaleness, and makes the
family jointly surjective because the family `{Spec A_i ⟶ X}` is. -/
theorem completionSheafMap_atlas_isRepresentable_etale_surjective
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS (a i) T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS (a i) T).hom hfi) ∧
    Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ Space.completionSheafMap B S hS (a i) T) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨hrep, het⟩ := ha i
    refine ⟨Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
      (isAlgebraicSpace_yoneda B S hS (affineOver B S hS (hA i) (str i))) hX (a i) T, ?_⟩
    exact hasPropertyULift_isEtaleULift_of_isPullback B S hS _ _ _ _
      ((Space.isPullback_completionSheafMap B S hS (a i) T).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hrep _ het
  · set φ := Space.completionSheafInclusion B S hS X T with hφ
    set ψ := fun i ↦ Space.sheafifiedULiftMap B S hS (a i) with hψ
    have hbase : Sheaf.IsLocallySurjective (Sigma.desc fun i ↦ pullback.snd (ψ i) φ) :=
      Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ ψ hcov
    let e : ∀ i, Space.completionSheaf B S hS
        (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T) ≅ pullback (ψ i) φ := fun i ↦
      (Space.isPullback_completionSheafMap B S hS (a i) T).isoPullback
    let t : (∐ fun i ↦ Space.completionSheaf B S hS
          (yoneda.obj (affineOver B S hS (hA i) (str i)))
          (Space.pointsMap B S hS _ (a i) ⁻¹' T)) ⟶ (∐ fun i ↦ pullback (ψ i) φ) :=
      Sigma.desc fun i ↦ (e i).hom ≫ Sigma.ι (fun j ↦ pullback (ψ j) φ) i
    have hts : IsSplitEpi t :=
      ⟨⟨Sigma.desc fun i ↦ (e i).inv ≫ Sigma.ι
          (fun j ↦ Space.completionSheaf B S hS
            (yoneda.obj (affineOver B S hS (hA j) (str j)))
            (Space.pointsMap B S hS _ (a j) ⁻¹' T)) i, by
        apply Sigma.hom_ext
        intro i
        simp [t]⟩⟩
    have hfac : (Sigma.desc fun i ↦ Space.completionSheafMap B S hS (a i) T) =
        t ≫ Sigma.desc fun i ↦ pullback.snd (ψ i) φ := by
      apply Sigma.hom_ext
      intro i
      simp only [t, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
      exact ((Space.isPullback_completionSheafMap B S hS (a i) T).isoPullback_hom_snd).symm
    rw [hfac, Sheaf.isLocallySurjective_iff_epi]
    let _ : Epi t := hts.epi
    let _ : Epi (Sigma.desc fun i ↦ pullback.snd (ψ i) φ) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp hbase
    infer_instance

/-- **The atlas of the completion.** An étale covering of an algebraic space `X` over `S` by
affine schemes `Spec A_i` lying in the site, read in the value universe of the formal algebraic
spaces, induces an atlas of the completion `X_{/T}` along a set `T` of points of `X` by the
completions of the charts along the inverse images of `T`.

The completion square of Stacks 0APV exhibits each `(Spec A_i)_{/T_i} ⟶ X_{/T}` as a base
change of `Spec A_i ⟶ X` along `X_{/T} ⟶ X`, which gives representability and étaleness, and
makes the family jointly surjective because the family `{Spec A_i ⟶ X}` is. That each member is
an affine formal algebraic space is the affine case, Stacks 0AIY. The property `P` read off the
members is a hypothesis, so that the construction can be reused for the local types of
`X_{/T}`. -/
theorem hasAffineEtaleAtlasWithProperty_completionSheaf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (P : FppfSheaf B S hS → Prop)
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)))
    (hP : ∀ i, P (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS (hA i) (str i)))
      (Space.pointsMap B S hS _ (a i) ⁻¹' T))) :
    HasAffineEtaleAtlasWithProperty B S hS (Space.completionSheaf B S hS X T) P := by
  obtain ⟨hrep, hsurj⟩ :=
    completionSheafMap_atlas_isRepresentable_etale_surjective hX T hA str a ha hcov
  exact ⟨Ix, fun i ↦ Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS (hA i) (str i)))
      (Space.pointsMap B S hS _ (a i) ⁻¹' T),
    fun i ↦ Space.completionSheafMap B S hS (a i) T, haff, hrep, hsurj, hP⟩

/-! ### Stacks 0AIZ -/

/-- **Stacks 0AIZ.** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`T ⊆ |X|` be a closed subset. The completion `X_{/T}` of `X` along `T` — the fppf sheaf attached
to the functor sending `U` to the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` — is a formal
algebraic space over `S`: the completions of the affine charts of `X` along the inverse images
of `T` form an atlas of `X_{/T}`, and each of them is an affine formal algebraic space by the
affine case, Stacks 0AIY.

The affine étale charts of `X`, the description of the inverse image of `T` on each of them as
the points supported in a closed subset, the per-chart hypothesis `HasStageAtlas` of the
affine case and the set-theoretic condition of Stacks 0AIS are carried as hypotheses; see the
section "What is assumed" of this file. -/
@[stacks 0AIZ "assumes the affine étale charts of X as hA, str, a, ha, hcov, their \
closed point sets as hTi and hTpts, the affine case's HasStageAtlas as hstage, and the \
0AIS condition as hset"]
theorem isFormalAlgebraicSpace_completionSheaf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    (Ti : ∀ i, Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS (hA i) (str i))))
    (hTi : ∀ i, IsClosed (Ti i))
    (hTpts : ∀ i, Space.pointsMap B S hS _ (a i) ⁻¹' T =
      supportedPoints B S hS (affineOver B S hS (hA i) (str i)) (Ti i))
    (hstage : ∀ i, HasStageAtlas B S hS (hA i) (str i)
      (PrimeSpectrum.vanishingIdeal (Ti i)))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheaf B S hS X T)) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheaf B S hS X T) := by
  have haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)) := by
    intro i
    rw [hTpts i]
    exact (hasSomeSurjectivePresentation_completionSheaf B S hS (hA i) (str i) (Ti i)
      (hTi i) (hstage i)).1
  exact isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset
    (hasAffineEtaleAtlasWithProperty_completionSheaf hX T (fun _ ↦ True) hA str a ha hcov haff
      (fun _ ↦ trivial))

/-! ### Stacks 0AQ1 -/

section LocalTypes

/-- The chart data shared by the two clauses of Stacks 0AQ1: an affine étale atlas of `X`,
read in the value universe of the formal algebraic spaces. -/
private theorem isFormalAlgebraicSpace_and_atlas_of_chartProperty
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (P : FppfSheaf B S hS → Prop)
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)))
    (hP : ∀ i, P (Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS (hA i) (str i)))
      (Space.pointsMap B S hS _ (a i) ⁻¹' T)))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheaf B S hS X T)) :
    IsFormalAlgebraicSpace B S hS (Space.completionSheaf B S hS X T) ∧
      HasAffineEtaleAtlasWithProperty B S hS (Space.completionSheaf B S hS X T) P := by
  have hatlas := hasAffineEtaleAtlasWithProperty_completionSheaf hX T P hA str a ha hcov haff hP
  exact ⟨isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty B S hS hset hatlas, hatlas⟩

/-- **Stacks 0AQ1, part (1).** Let `S` be a scheme, let `X` be an algebraic space over `S` and
let `T ⊆ |X|` be a closed subset such that `X \ T ⟶ X` is quasi-compact. The completion `X_{/T}`
of `X` along `T` is *locally adic\**: the completions of the affine charts of `X` along the
inverse images of `T` form an atlas of `X_{/T}`, and each of them is an adic\* affine formal
algebraic space by the affine case, Stacks 0GBA (1), the complement of the inverse image of `T`
on a chart being quasi-compact.

The affine étale charts of `X` and the set-theoretic condition of Stacks 0AIS are carried as
hypotheses, as in `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf`
(Stacks 0AIZ); quasi-compactness of `X \ T ⟶ X` is carried in the form it is used in, namely
chartwise quasi-compactness of the complement `hqc`, which is the source's step transferring
the hypothesis from `X` to the charts. The hypothesis `HasStageAtlas` of Stacks 0AIY is *not*
needed here: being adic\* already contains being an affine formal algebraic space. -/
@[stacks 0AQ1 "part (1): locally adic star; assumes the affine étale charts of X as \
hA, str, a, ha, hcov, chartwise quasi-compactness of the complement as hqc, and the \
0AIS condition as hset"]
theorem isLocallyAdicStar_completionSheaf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    (hqc : ∀ i, @IsCompact _
      (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS (hA i) (str i))))
      (Space.pointsMap B S hS _ (a i) ⁻¹' T)ᶜ)
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheaf B S hS X T)) :
    IsLocallyAdicStar B S hS (Space.completionSheaf B S hS X T) := by
  have hP : ∀ i, IsAdicStar B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)) := by
    intro i
    let _ : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
    let _ : TopologicalSpace
        (Space.points B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))) :=
      Space.pointTopology B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
    exact isAdicStar_completionSheaf B S hS (hA i) (str i) _
      (hT.preimage (Space.continuous_pointsMap B S hS (a i))) (hqc i)
  exact isFormalAlgebraicSpace_and_atlas_of_chartProperty hX T (IsAdicStar B S hS) hA str a ha
    hcov (fun i ↦ (hP i).1.1) hP hset

/-- **Stacks 0AQ1, part (2).** Let `S` be a scheme, let `X` be a locally Noetherian algebraic
space over `S` and let `T ⊆ |X|` be a closed subset. The completion `X_{/T}` of `X` along `T` is
*locally Noetherian*: the completions of the affine charts of `X` along the inverse images of
`T` form an atlas of `X_{/T}`, and each of them is a Noetherian affine formal algebraic space by
the affine case, Stacks 0GBA (3), the chart rings being Noetherian.

The affine étale charts of `X` and the set-theoretic condition of Stacks 0AIS are carried as
hypotheses, as in `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf`
(Stacks 0AIZ); local Noetherianness of `X` is carried in the form it is used in, namely
Noetherianness of the chart rings `hNoeth`, which is the source's step transferring the
hypothesis from `X` to the charts. The hypothesis `HasStageAtlas` of Stacks 0AIY is *not* needed
here: being Noetherian already contains being an affine formal algebraic space. -/
@[stacks 0AQ1 "part (2): locally Noetherian; assumes the affine étale charts of X as \
hA, str, a, ha, hcov, Noetherianness of the chart rings as hNoeth, and the 0AIS \
condition as hset"]
theorem isLocallyNoetherian_completionSheaf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    {Ix : Type (u + 1)} {A : Ix → Type u} [∀ i, CommRing (A i)]
    (hNoeth : ∀ i, IsNoetherianRing (A i))
    (hA : ∀ i, B.Contains (AlgebraicGeometry.Spec (.of (A i))))
    (str : ∀ i, AlgebraicGeometry.Spec (.of (A i)) ⟶ S)
    (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X)
    (ha : ∀ i, ∃ hai : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (a i)).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (a i)).hom hai)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (a i)))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSheaf B S hS X T)) :
    IsLocallyNoetherian B S hS (Space.completionSheaf B S hS X T) := by
  have hP : ∀ i, IsNoetherian B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
        (Space.pointsMap B S hS _ (a i) ⁻¹' T)) := by
    intro i
    let _ : IsNoetherianRing (A i) := hNoeth i
    let _ : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
    let _ : TopologicalSpace
        (Space.points B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))) :=
      Space.pointTopology B S hS (yoneda.obj (affineOver B S hS (hA i) (str i)))
    exact isNoetherian_completionSheaf B S hS (hA i) (str i) _
      (hT.preimage (Space.continuous_pointsMap B S hS (a i)))
  exact isFormalAlgebraicSpace_and_atlas_of_chartProperty hX T (IsNoetherian B S hS) hA str a ha
    hcov (fun i ↦ (hP i).1.1) hP hset

end LocalTypes

end AlgebraicGeometry.FormalSpace

end
