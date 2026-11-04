module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitAdjointForm

/-!
# The presentation predicate of Stacks 09YQ, with the inverse images removed

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` is the hypothesis
`𝒢 = colim_i f_i^{-1}F_i` of [Stacks, Tag 09YQ], stated with the *inverse image*
`Stacks.EtaleCohomology.etaleAbelianInverseImage` along the projections of a limit cone. Every
tool this library has for a colimit of sites proves a *restriction* statement — restriction along
a functor of sites, with no left adjoint and no sheafification in it — and in particular
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange`, the second
half of [Stacks, Tag 0EYN] on Mathlib's small étale site of a limit of schemes with the
restrictions taken along base change along the projections, is of that shape. The two are
**adjoint, not the same statement**.

This file removes the inverse images from the predicate. At the canonical system — the system of
direct images of [Stacks, Tag 0EYN] with the counits as legs, which by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_coneDirectImageLeg` is
already known to satisfy the compatibility clause — the predicate of [Stacks, Tag 09YQ] is
*equivalent* to `Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent`, a statement
in which only direct images occur.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.existsUnique_desc_iff` — the
  universal-property clause of
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` is
  `Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` at the legs read
  in the vocabulary of the abstract inverse image.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_iff` — consequently the
  whole predicate is its compatibility clause together with that colimit assertion.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_directImageSystem_iff` —
  **the adjunction bridge**: at the system of direct images with the counit legs, the presentation
  hypothesis of [Stacks, Tag 09YQ] holds exactly when every family of maps of direct images
  `σ_i : f_{i, *}𝓕 ⟶ f_{i, *}𝒢` compatible with the identifications
  `Stacks.EtaleCohomology.coneDirectImageCompAb` is the family of direct images `f_{i, *}χ` of a
  unique `χ : 𝓕 ⟶ 𝒢`.

## Implementation notes

The morphism `χ` is the same on both sides of every equivalence here.

* The two inverse images this library carries — `Stacks.EtaleCohomology.smallEtalePullbackAb`,
  the abstract left adjoint of the direct image, and
  `Stacks.EtaleCohomology.etaleAbelianInverseImage`, the same functor built as a left Kan
  extension followed by sheafification — are compared by
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`, and
  `transportLeg_comp_iff` and `isCompatibleFamily_iff` say that factoring through the legs and
  compatibility with the transitions are the same conditions in the two vocabularies. That is the
  whole content of `existsUnique_desc_iff`: the quantifier over the target sheaf is untouched,
  and the family quantified over is carried across by
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.transportLeg`, a bijection whose inverse is
  `untransportLeg`.
* The inverse-image/direct-image adjunction then removes the inverse image altogether; that step
  is `Stacks.EtaleCohomology.LimitHigherDirectImage.isPullbackColimitPresentation_iff`, whose
  content is the right triangle identity and the hexagon
  `Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm`.
* The compatibility clause at the canonical system is
  `isCompatibleFamily_coneDirectImageLeg`, the cocone half of [Stacks, Tag 0EYN], so it is not a
  hypothesis of `isColimitPresentation_directImageSystem_iff` but a fact used in its proof.

**Why the round trip is done with a function equality.** `transportLeg_untransportLeg` and
`transportLeg_coneDirectImageLeg` are pointwise, and the family is a *function* of the index in
the predicates being related, so each is used through `funext` and `rw`: `simpa only` with the
pointwise form does not fire under the binder, the occurrence to rewrite being the function and
not its value.

**The two spellings of the projection.** `IsColimitPresentation` is stated with
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` and
`IsPullbackColimitPresentation` with `Cone.π.app`, and the comparison of inverse images along a
factorisation of a projection has the two names `conePullbackCompPi` and `conePullbackComp`; in
each pair the first is *defined* to be the second, so the equivalences below need no transport,
and the proofs go through by `exact` at default transparency. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationComparison`
for why both spellings exist.

**What is still owed for the degree-zero statement of [Stacks, Tag 09YQ].**
`IsDirectImageDescent` mentions only restrictions along base change, which is the shape of
`restrictionIsColimitAb_levelBaseChange`; what separates them is no longer the adjunction but the
*site crossing*. That statement is about the levels of
`Stacks.EtaleCohomology.affineEtaleSiteColimit`, categories of chosen pullback models of the
small **affine** étale sites of [Stacks, Tag 021B], while `IsDirectImageDescent` is about
Mathlib's small étale sites; and its transition datum is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition`, the conjugate
of the system's own on-the-nose cocone identity, while the transition datum of
`IsDirectImageCompatible` is `Stacks.EtaleCohomology.coneDirectImageCompAb`, the associativity of
fibre products.

**Those two isomorphisms are identified.** The coherence is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence`,
and with it that file's
`Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange` discharges
`IsDirectImageDescent` outright for every abelian sheaf on Mathlib's small étale site of the
limit. So at the system of direct images nothing is owed: by
`isColimitPresentation_directImageSystem_iff` below, the presentation predicate of
[Stacks, Tag 09YQ] *holds* at that system.

What is owed is the same passage at an **arbitrary** system, and there the obstruction is not the
site crossing at all but the identity law: see
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleSystemIdentityLaw.lean`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}

/-- **The universal-property clause of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` is
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`** at the legs read
in the vocabulary of the abstract inverse image `Stacks.EtaleCohomology.smallEtalePullbackAb`.

The two differ only by the comparison
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb` of the two inverse
images this library carries: the family quantified over is carried across by the bijection
`transportLeg`/`untransportLeg`, its compatibility by `isCompatibleFamily_iff`, and the
factorisation condition by `transportLeg_comp_iff`. The quantifier over the target sheaf, the
uniqueness of the factorisation, and the factoring morphism itself are untouched. -/
theorem existsUnique_desc_iff (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) :
    (∀ (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
        (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H),
        IsCompatibleFamily F H τ → ∃! χ : 𝒢 ⟶ H, ∀ i : Iᵒᵖ, ι i ≫ χ = τ i) ↔
      LimitHigherDirectImage.IsPullbackColimitPresentation c 𝒢 F (transportLeg F 𝒢 ι) := by
  constructor
  · intro h H τ' hτ'
    obtain ⟨τ, rfl⟩ : ∃ τ, transportLeg F H τ = τ' :=
      ⟨_, funext fun i => transportLeg_untransportLeg F H τ' i⟩
    exact (existsUnique_congr fun χ => forall_congr' (transportLeg_comp_iff F ι τ χ)).mp
      (h H τ ((isCompatibleFamily_iff F H τ).mpr fun a => hτ' a))
  · intro h H τ hτ
    exact (existsUnique_congr fun χ => forall_congr' (transportLeg_comp_iff F ι τ χ)).mpr
      (h H _ fun a => (isCompatibleFamily_iff F H τ).mp hτ a)

/-- **The presentation predicate of [Stacks, Tag 09YQ] is its compatibility clause together with
the colimit assertion of [Stacks, Tag 0EYM] in the abstract inverse-image vocabulary.** This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.existsUnique_desc_iff` with the first clause of
the structure carried along unchanged. -/
theorem isColimitPresentation_iff (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) :
    IsColimitPresentation F 𝒢 ι ↔
      IsCompatibleFamily F 𝒢 ι ∧
        LimitHigherDirectImage.IsPullbackColimitPresentation c 𝒢 F (transportLeg F 𝒢 ι) :=
  ⟨fun h => ⟨h.compatible, (existsUnique_desc_iff F 𝒢 ι).mp h.existsUnique_desc⟩,
    fun h => ⟨h.1, (existsUnique_desc_iff F 𝒢 ι).mpr h.2⟩⟩

/-- **The adjunction bridge: the presentation hypothesis of [Stacks, Tag 09YQ] at the system of
direct images is a descent statement for the direct images alone.** Let `(X_i, f_{i'i})` be an
inverse system of schemes, let `f_i : X ⟶ X_i` be the projections of a cone over it and let `𝓕`
be an abelian sheaf on Mathlib's small étale site of `X`. Then the counits
`ι_i : f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕` exhibit `𝓕 = colim_i f_i^{-1}f_{i, *}𝓕` in the vocabulary
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` and [Stacks, Tag 09YQ] ask
for — the *constructed* inverse image
`Stacks.EtaleCohomology.etaleAbelianInverseImage` along
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` — exactly when every family of maps of
direct images `σ_i : f_{i, *}𝓕 ⟶ f_{i, *}𝒢` compatible with the identifications
`Stacks.EtaleCohomology.coneDirectImageCompAb` along the factorisations `f_j = f_i ≫ f_{ji}` is
the family of direct images `f_{i, *}χ` of a unique `χ : 𝓕 ⟶ 𝒢`.

The right-hand side mentions no inverse image, no left adjoint and no sheafification:
`Stacks.EtaleCohomology.smallEtalePushforwardAb` is restriction along
`Stacks.EtaleCohomology.smallEtaleBaseChange` and `coneDirectImageCompAb` is a comparison of two
such restrictions. It is therefore the shape in which a colimit-of-sites descent statement —
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'`, which
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange` establishes
for base change along the projections of a limit cone — can discharge it. See the module
docstring for what separates the two: the site crossing to the levels of [Stacks, Tag 0EYL] and
the identification of the two transition data, not the adjunction.

Nothing is assumed: the compatibility clause of the predicate holds at this system by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_coneDirectImageLeg`, the
cocone half of [Stacks, Tag 0EYN]. -/
theorem isColimitPresentation_directImageSystem_iff
    (𝓕 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :
    IsColimitPresentation (c := c) (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕
        (coneDirectImageLeg 𝓕) ↔
      LimitHigherDirectImage.IsDirectImageDescent c 𝓕 := by
  have hleg : transportLeg (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕
      (coneDirectImageLeg 𝓕) = coneDirectImageCounit c 𝓕 :=
    funext fun i => transportLeg_coneDirectImageLeg 𝓕 i
  rw [isColimitPresentation_iff, hleg, ← LimitHigherDirectImage.isPullbackColimitPresentation_iff]
  exact and_iff_right (isCompatibleFamily_coneDirectImageLeg 𝓕)

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
