module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# The local type of the completion of an algebraic space along a closed subspace

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊆ X` be a closed subspace. **Stacks 0GXY** records the local type of the completion
`X^∧_Z` of `X` along `Z`, the formal algebraic space `colim Z_n` of Stacks 0GXU:

1. `X^∧_Z` is locally weakly adic;
2. if `Z ⟶ X` is of finite presentation, `X^∧_Z` is locally adic\*;
3. if `X` is locally Noetherian, `X^∧_Z` is locally Noetherian.

All three are proved here by exhibiting one and the same atlas of `X^∧_Z` and reading off its
members' type from the affine case, Stacks 0GXX. The completion of `X` along `Z` is
`AlgebraicGeometry.Space.completionSubspace`; it is **not** the completion `X_{/T}` along the
point set `T = |Z|` of Stacks 0AIZ, which is `AlgebraicGeometry.Space.completionSheaf`, and by
Stacks 0H8N the canonical morphism between the two is an isomorphism only when `Z ⟶ X` is of
finite presentation.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyWeaklyAdic_completionSubspace`: clause (1) of
  Stacks 0GXY from an atlas of `X`, the chart identification and the set-theoretic condition.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSubspace`: clause (2) likewise.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSubspace`: clause (3) likewise.
* `AlgebraicGeometry.FormalSpace.isNoetherian_completionAlongIdeal`: **Stacks 0GXX (4)**, the
  affine case of clause (3).

## The atlas

The atlas is the one of the source's omitted proof: an étale covering `{X_i ⟶ X}` of `X` by
affine schemes gives the family `{(X_i)^∧_{Z_i} ⟶ X^∧_Z}` with `Z_i = f_i⁻¹(Z)`, and that
family is an atlas as in Definition 0AIM because the completion square of Stacks 0GXV is
cartesian:

* each `(X_i)^∧_{Z_i} ⟶ X^∧_Z` is representable by algebraic spaces, which is Stacks 0GXV,
  `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionSubspaceMap`;
* each is étale, because it is a base change of `X_i ⟶ X` along `X^∧_Z ⟶ X`, by
  `AlgebraicGeometry.Space.isPullback_completionSubspaceMap`; and
* the induced map from the coproduct is a surjection of sheaves, because the coproduct of the
  base changes of a jointly surjective family is again a surjection,
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

The members are affine formal algebraic spaces of the asserted type because over an affine
chart the completion is the completion of `Spec A` along the closed subscheme of an ideal
`I ⊆ A`, whose type is Stacks 0GXX:
`AlgebraicGeometry.FormalSpace.isWeaklyAdic_completionAlongIdeal` for clause (1),
`AlgebraicGeometry.FormalSpace.isAdicStar_completionAlongIdeal` for clause (3) — under `I.FG`,
which is what finite presentation of `Z ⟶ X` says on the chart — and
`AlgebraicGeometry.FormalSpace.isNoetherian_completionAlongIdeal` below for clause (4).

## What is assumed

Three things, in each of the three statements of this file; all three are proved, for an
arbitrary algebraic space `X` and closed subspace `Z`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAtlas`, which is where the
unconditional forms of the three clauses of Stacks 0GXY live.

* The atlas of `X` itself: the charts `X_i`, their étaleness and their joint surjectivity,
  read in the value universe `Type (u + 1)` of the formal algebraic spaces, that is for the
  sheafified universe lifts `AlgebraicGeometry.Space.sheafifiedULift`. It is supplied by
  `AlgebraicGeometry.FormalSpace.exists_affine_etale_atlas_sheafifiedULift`, from Stacks 03FX.

* The chart-level identification: that the completion of each chart along the inverse image of
  `Z` is the completion `AlgebraicGeometry.FormalSpace.completionAlongIdeal` of `Spec A` along
  the closed subscheme of an ideal. This is the first step of the source's omitted proof; it is
  `AlgebraicGeometry.Space.nonempty_completionSubspaceIsoCompletionAlongIdeal`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChartColimit`.

* The set-theoretic condition of Stacks 0AIS for `X^∧_Z`, which the source imposes as part of
  being a formal algebraic space. It is
  `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSubspace`.

Clause (3) assumes nothing more. Its affine input, Stacks 0GXX (4), is proved below from
`AdicCompletion.isNoetherianRing` (Stacks 0316): the `J`-adic completion of the Noetherian
chart ring is Noetherian, and it is adic with a finitely generated ideal of definition by
Stacks 0GXX (2). That clause of 0GXX is not proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal`, whose notes predate
Stacks 0316 in this library, so it is proved here.

## Implementation notes

The three types are the predicates of `StacksFrontier.AlgebraicGeometry.FormalSpace.Types`,
condition (2) of Stacks 0AKX: a formal algebraic space together with an atlas as in Definition
0AIM all of whose members have the corresponding affine type of Stacks 0AID. So each of the
three statements is `AlgebraicGeometry.FormalSpace.HasAffineEtaleAtlasWithProperty` at the
relevant property, together with `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace`; both
conjuncts are supplied by the *same* atlas, which is what
`hasAffineEtaleAtlasWithProperty_completionSubspace` below produces, so the three statements
differ only in the property read off the members.

The affine types of Stacks 0AID are stated for a presentation of the sheaf and so are
invariant under isomorphism of sheaves; the transport lemmas are the private
`*_of_iso` block below, each of which just replaces the comparison isomorphism of a
presentation by its composite with the given one.

## References

* [Stacks Project, Tag 0GXY](https://stacks.math.columbia.edu/tag/0GXY)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0GXV](https://stacks.math.columbia.edu/tag/0GXV)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0H8N](https://stacks.math.columbia.edu/tag/0H8N)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of the affine types along an isomorphism -/

/-- The set-theoretic condition of Stacks 0AIS is invariant under isomorphism: compose the
surjection from a representable sheaf with the isomorphism, and its kernel pair with the
induced isomorphism of kernel pairs. -/
private theorem satisfiesSetTheoreticCondition_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  obtain ⟨U, R, hU, hR, hUrep, hRrep, f, hf, g, hg⟩ := hY
  let f' : hU ⟶ X := f ≫ e.inv
  let t : pullback f f ⟶ pullback f' f' :=
    pullback.map f f f' f' (𝟙 hU) (𝟙 hU) e.inv (by simp [f']) (by simp [f'])
  exact ⟨U, R, hU, hR, hUrep, hRrep, f', epi_comp' hf inferInstance, g ≫ t,
    epi_comp' hg (by dsimp only [t]; infer_instance)⟩

/-- Being an affine formal algebraic space is invariant under isomorphism. -/
private theorem isAffineFormalAlgebraicSpace_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  obtain ⟨hset, I, pre, hI, hdir, D, hD, ⟨k⟩⟩ := hY
  exact ⟨satisfiesSetTheoreticCondition_of_iso B S hS e hset, I, pre, hI, hdir, D, hD,
    ⟨e ≪≫ k⟩⟩

/-- Being a McQuillan affine formal algebraic space, condition (4) of Stacks 0AIC, is
invariant under isomorphism: the presentation witnessing it is unchanged. -/
private theorem hasSomeSurjectivePresentation_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : HasSomeSurjectivePresentation B S hS Y) :
    HasSomeSurjectivePresentation B S hS X := by
  obtain ⟨haff, I, pre, hI, hdir, D, hD, ⟨k⟩, hsurj⟩ := hY
  exact ⟨isAffineFormalAlgebraicSpace_of_iso B S hS e haff, I, pre, hI, hdir, D, hD,
    ⟨e ≪≫ k⟩, hsurj⟩

/-- A ring presenting a sheaf presents any sheaf isomorphic to it. -/
private theorem isPresentingRing_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hY : IsPresentingRing B S hS A Y) : IsPresentingRing B S hS A X := by
  obtain ⟨hwa, ⟨pres⟩⟩ := hY
  exact ⟨hwa, ⟨{ pres with colimitIso := e ≪≫ pres.colimitIso }⟩⟩

/-- A presentable affine formal algebraic space satisfying a property of the presenting ring
keeps that property along an isomorphism. -/
private theorem hasPresentingRingWith_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (Q : ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A], Prop)
    (hY : HasSomeSurjectivePresentation B S hS Y ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A Y ∧ Q A) :
    HasSomeSurjectivePresentation B S hS X ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A X ∧ Q A := by
  obtain ⟨hpres, A, i1, i2, i3, i4, hpr, hQ⟩ := hY
  exact ⟨hasSomeSurjectivePresentation_of_iso B S hS e hpres, A, i1, i2, i3, i4,
    isPresentingRing_of_iso B S hS e A hpr, hQ⟩

/-- Being a weakly adic affine formal algebraic space is invariant under isomorphism. -/
private theorem isWeaklyAdic_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : IsWeaklyAdic B S hS Y) : IsWeaklyAdic B S hS X :=
  hasPresentingRingWith_of_iso B S hS e (fun A ↦ TopologicalRing.IsWeaklyAdic A) hY

/-- Being an adic\* affine formal algebraic space is invariant under isomorphism. -/
private theorem isAdicStar_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : IsAdicStar B S hS Y) : IsAdicStar B S hS X :=
  hasPresentingRingWith_of_iso B S hS e
    (fun A ↦ TopologicalRing.IsAdic A ∧
      ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG) hY

/-- Being a Noetherian affine formal algebraic space is invariant under isomorphism. -/
private theorem isNoetherian_of_iso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hY : IsNoetherian B S hS Y) : IsNoetherian B S hS X :=
  hasPresentingRingWith_of_iso B S hS e
    (fun A ↦ IsNoetherianRing A ∧ TopologicalRing.IsAdic A) hY

/-! ### Étaleness of a base change -/

/-- Étaleness of a morphism representable by algebraic spaces is stable under base change: a
base change of a base change along a universe-lifted scheme-valued point is a base change
along the composite point. -/
theorem hasPropertyULift_isEtaleULift_of_isPullback
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (p : H ⟶ F) (a' : H ⟶ G') (a : F ⟶ G) (g : G' ⟶ G)
    (h : IsPullback p a' a g)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a)
    (ha' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a')
    (hP : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) a ha) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) a' ha' := by
  intro U ξ V φ hφ
  have hpaste : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ p) (ξ ≫ g) a := by
    simpa using (IsPullback.paste_horiz (IsPullback.of_hasPullback ξ a').flip h).flip
  have hφa := hP U (ξ ≫ g) V (φ ≫ hpaste.isoPullback.hom)
    (MorphismProperty.RespectsIso.postcomp _ hpaste.isoPullback.hom φ hφ)
  dsimp only [ObjectProperty.homMk] at hφa ⊢
  simpa only [Category.assoc, hpaste.isoPullback_hom_fst] using hφa

/-! ### The atlas of the completion -/

/-- An fppf sheaf satisfying the set-theoretic condition of Stacks 0AIS which has an atlas as in
Definition 0AIM all of whose members have a given property is a formal algebraic space. This is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes`, to which it forwards, under the
name used here. -/
alias isFormalAlgebraicSpace_of_hasAffineEtaleAtlasWithProperty := isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty

/-- **The atlas of the completion.** An étale covering `{X_i ⟶ X}` of an algebraic space `X`
over `S`, read in the value universe of the formal algebraic spaces, induces an atlas of the
completion `X^∧_Z` of `X` along a subfunctor `Z` by the completions `(X_i)^∧_{Z_i}` of the
charts along the inverse images `Z_i = f_i⁻¹(Z)`.

The completion square of Stacks 0GXV exhibits each `(X_i)^∧_{Z_i} ⟶ X^∧_Z` as a base change of
`X_i ⟶ X` along `X^∧_Z ⟶ X`, which gives representability and étaleness, and makes the family
jointly surjective because the family `{X_i ⟶ X}` is.

This is the family itself, as conditions (1), (2) and (3) of Definition 0AIM; the type of its
members is read off from it separately by
`AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_completionSubspace`, and the
set-theoretic condition of Stacks 0AIS by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSubspace`, so that the
three clauses of Stacks 0GXY share this one construction. -/
private theorem isFormalAtlas_completionSubspace
    {X : AlgebraicSpaces B S hS} (Z : Subfunctor X.1)
    {Ix : Type (u + 1)} (Xi : Ix → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom))
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom))) :
    IsFormalAtlas B S hS (Space.completionSubspace B S hS X Z)
      (fun i ↦ Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom))
      (fun i ↦ Space.completionSubspaceMap B S hS (f i) Z) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨haff, ?_, ?_⟩
  · intro i
    obtain ⟨hrep, het⟩ := hf i
    exact ⟨Space.isRepresentableByAlgebraicSpacesULift_completionSubspaceMap B S hS (f i) Z,
      hasPropertyULift_isEtaleULift_of_isPullback B S hS _ _ _ _
        ((Space.isPullback_completionSubspaceMap B S hS (f i) Z).map
          (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hrep _ het⟩
  · set φ := Space.completionSubspaceToAmbient B S hS X Z
    set ψ := fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom
    let e : ∀ i, Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom) ≅
        pullback (ψ i) φ := fun i ↦
      (Space.isPullback_completionSubspaceMap B S hS (f i) Z).isoPullback
    let t : (∐ fun i ↦ Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom)) ⟶
        (∐ fun i ↦ pullback (ψ i) φ) :=
      Sigma.desc fun i ↦ (e i).hom ≫ Sigma.ι (fun j ↦ pullback (ψ j) φ) i
    have hts : IsSplitEpi t :=
      ⟨⟨Sigma.desc fun i ↦ (e i).inv ≫ Sigma.ι
          (fun j ↦ Space.completionSubspace B S hS (Xi j) (Z.preimage (f j).hom)) i,
        Sigma.hom_ext _ _ fun i ↦ by simp [t]⟩⟩
    have hfac : (Sigma.desc fun i ↦ Space.completionSubspaceMap B S hS (f i) Z) =
        t ≫ Sigma.desc fun i ↦ pullback.snd (ψ i) φ := by
      apply Sigma.hom_ext
      intro i
      simp only [t, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc]
      exact ((Space.isPullback_completionSubspaceMap B S hS (f i) Z).isoPullback_hom_snd).symm
    rw [hfac, Sheaf.isLocallySurjective_iff_epi]
    let : Epi t := hts.epi
    let : Epi (Sigma.desc fun i ↦ pullback.snd (ψ i) φ) :=
      (Sheaf.isLocallySurjective_iff_epi _).mp
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd φ ψ hcov)
    infer_instance

/-- The atlas of the completion, with the type of its members read off, and the completion a
formal algebraic space. -/
private theorem isFormalAndHasAffineEtaleAtlasWithProperty_completionSubspace
    {X : AlgebraicSpaces B S hS} (Z : Subfunctor X.1) (P : FppfSheaf B S hS → Prop)
    {Ix : Type (u + 1)} (Xi : Ix → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom))
    (haff : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom)))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSubspace B S hS X Z))
    (hP : ∀ i, P (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom))) :
    IsFormalAlgebraicSpace B S hS (Space.completionSubspace B S hS X Z) ∧
      HasAffineEtaleAtlasWithProperty B S hS (Space.completionSubspace B S hS X Z) P := by
  obtain ⟨h1, h2, h3⟩ := isFormalAtlas_completionSubspace B S hS Z Xi f hf hcov haff
  have hatlas : HasAffineEtaleAtlasWithProperty B S hS (Space.completionSubspace B S hS X Z) P :=
    ⟨Ix, _, _, h1, h2, h3, hP⟩
  exact ⟨isFormalAlgebraicSpace_of_hasAffineEtaleAtlasWithProperty B S hS hset hatlas, hatlas⟩

/-! ### Stacks 0GXY -/

/-- **Stacks 0GXY (1).** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z ⊆ X` be a closed subspace. The completion `X^∧_Z` of `X` along `Z` is *locally weakly
adic*: the completions of the affine charts of `X` along the inverse images of `Z` form an
atlas of `X^∧_Z`, and each of them is a weakly adic affine formal algebraic space by Stacks
0GXX (1).

The charts of `X` and the identification of their completions with completions of affine
schemes along ideals are carried as hypotheses, as is the set-theoretic condition of Stacks
0AIS; see the section "What is assumed" of this file. -/
@[stacks 0GXY "part (1): locally weakly adic; charts and 0AIS condition assumed"]
theorem isLocallyWeaklyAdic_completionSubspace
    {X : AlgebraicSpaces B S hS} (Z : Subfunctor X.1)
    {Ix : Type (u + 1)} (Xi : Ix → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom))
    (hchart : ∀ i, ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
      (hA : B.Contains (Spec (.of A))) (J : Ideal A),
      Nonempty (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom) ≅
        completionAlongIdeal B S hS str hA J))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSubspace B S hS X Z)) :
    IsLocallyWeaklyAdic B S hS (Space.completionSubspace B S hS X Z) := by
  have hP : ∀ i, IsWeaklyAdic B S hS
      (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom)) := by
    intro i
    obtain ⟨A, _, str, hA, J, ⟨k⟩⟩ := hchart i
    exact isWeaklyAdic_of_iso B S hS k (isWeaklyAdic_completionAlongIdeal B S hS str hA J)
  exact isFormalAndHasAffineEtaleAtlasWithProperty_completionSubspace B S hS Z
    (IsWeaklyAdic B S hS) Xi f hf hcov (fun i ↦ (hP i).1.1) hset hP

/-- **Stacks 0GXY (2).** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z ⊆ X` be a closed subspace with `Z ⟶ X` of finite presentation. The completion `X^∧_Z` of
`X` along `Z` is *locally adic\**: the completions of the affine charts of `X` along the
inverse images of `Z` form an atlas of `X^∧_Z`, and each of them is an adic\* affine formal
algebraic space by Stacks 0GXX (3), finite presentation of `Z ⟶ X` saying on an affine chart
`Spec A` that the ideal cutting out the inverse image of `Z` is finitely generated.

The charts of `X` and the identification of their completions with completions of affine
schemes along finitely generated ideals are carried as hypotheses, as is the set-theoretic
condition of Stacks 0AIS; see the section "What is assumed" of this file. -/
@[stacks 0GXY "part (2): locally adic star; charts and 0AIS condition assumed"]
theorem isLocallyAdicStar_completionSubspace
    {X : AlgebraicSpaces B S hS} (Z : Subfunctor X.1)
    {Ix : Type (u + 1)} (Xi : Ix → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom))
    (hchart : ∀ i, ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
      (hA : B.Contains (Spec (.of A))) (J : Ideal A), J.FG ∧
      Nonempty (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom) ≅
        completionAlongIdeal B S hS str hA J))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSubspace B S hS X Z)) :
    IsLocallyAdicStar B S hS (Space.completionSubspace B S hS X Z) := by
  have hP : ∀ i, IsAdicStar B S hS
      (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom)) := by
    intro i
    obtain ⟨A, _, str, hA, J, hJ, ⟨k⟩⟩ := hchart i
    exact isAdicStar_of_iso B S hS k (isAdicStar_completionAlongIdeal B S hS str hA J hJ)
  exact isFormalAndHasAffineEtaleAtlasWithProperty_completionSubspace B S hS Z
    (IsAdicStar B S hS) Xi f hf hcov (fun i ↦ (hP i).1.1) hset hP

section Noetherian

attribute [local instance] adicCompletionLimitTopology isTopologicalRing_adicCompletion
  isLinearTopology_adicCompletion

/-- **Stacks 0GXX (4).** For an affine scheme `X = Spec A` over `S` with `A` Noetherian and the
closed subscheme `Z ⊆ X` of an ideal `J ⊆ A`, the completion `X^∧_Z` of `X` along `Z` is a
Noetherian affine formal algebraic space: it is presented by the `J`-adic completion of `A`,
which is a Noetherian ring by Stacks 0316 and which is adic with the finitely generated ideal
of definition `J A^∧` by Stacks 0GXX (2), the ideal `J` being finitely generated because `A` is
Noetherian. -/
@[stacks 0GXX "clause (4): Noetherian", ega "I 10.8.6" "special case"]
theorem isNoetherian_completionAlongIdeal {A : Type u} [CommRing A] [IsNoetherianRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (J : Ideal A) :
    IsNoetherian B S hS (completionAlongIdeal B S hS str hA J) := by
  have hJ : J.FG := IsNoetherian.noetherian J
  obtain ⟨hpres, -, -, -, -, -, hpr, -⟩ :=
    isAdicStar_completionAlongIdeal B S hS str hA J hJ
  exact ⟨hpres, AdicCompletion J A, inferInstance, adicCompletionLimitTopology A J,
    isTopologicalRing_adicCompletion A J, isLinearTopology_adicCompletion A J,
    ⟨isWeaklyAdmissible_adicCompletion A J,
      ⟨adicCompletionWeakIdealPresentation B S hS str hA J⟩⟩, inferInstance,
    isAdic_adicCompletion J hJ⟩

end Noetherian

/-- **Stacks 0GXY (3).** Let `S` be a scheme, let `X` be a locally Noetherian algebraic space
over `S` and let `Z ⊆ X` be a closed subspace. The completion `X^∧_Z` of `X` along `Z` is
*locally Noetherian*: the completions of the affine charts of `X` along the inverse images of
`Z` form an atlas of `X^∧_Z`, and each of them is presented by the adic completion of the
Noetherian chart ring, which is adic with a finitely generated ideal of definition by Stacks
0GXX (2).

The charts of `X` and the identification of their completions with completions of Noetherian
affine schemes along ideals are carried as hypotheses, as is the set-theoretic condition of
Stacks 0AIS; see the section "What is assumed" of this file. -/
@[stacks 0GXY "part (3): locally Noetherian; charts and 0AIS condition assumed"]
theorem isLocallyNoetherian_completionSubspace
    {X : AlgebraicSpaces B S hS} (Z : Subfunctor X.1)
    {Ix : Type (u + 1)} (Xi : Ix → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        Sheaf.IsLocallySurjective
          (Sigma.desc fun i ↦ Space.sheafifiedULiftMap B S hS (f i).hom))
    (hchart : ∀ i, ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
      (hA : B.Contains (Spec (.of A))) (J : Ideal A) (_ : IsNoetherianRing A),
      Nonempty (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom) ≅
        completionAlongIdeal B S hS str hA J))
    (hset : SatisfiesSetTheoreticCondition B S hS (Space.completionSubspace B S hS X Z)) :
    IsLocallyNoetherian B S hS (Space.completionSubspace B S hS X Z) := by
  have hP : ∀ i, IsNoetherian B S hS
      (Space.completionSubspace B S hS (Xi i) (Z.preimage (f i).hom)) := by
    intro i
    obtain ⟨A, _, str, hA, J, _, ⟨k⟩⟩ := hchart i
    exact isNoetherian_of_iso B S hS k
      (isNoetherian_completionAlongIdeal B S hS str hA J)
  exact isFormalAndHasAffineEtaleAtlasWithProperty_completionSubspace B S hS Z
    (IsNoetherian B S hS) Xi f hf hcov (fun i ↦ (hP i).1.1) hset hP

end AlgebraicGeometry.FormalSpace

end
