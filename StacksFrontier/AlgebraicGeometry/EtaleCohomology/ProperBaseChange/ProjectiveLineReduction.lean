module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma

/-!
# Reducing base change for proper morphisms to the projective line

To know that cohomology commutes with base change for every proper morphism of schemes it is
enough to know it for the projections `ℙ¹_S ⟶ S`: Chow's lemma, the closure of the condition
under composition and under descent along a proper surjection, its validity for finite
morphisms, and the finite surjective cover of `ℙⁿ_S` by an `n`-fold fibre power of `ℙ¹_S`
together produce it for every proper morphism.

## Main definitions

* `AlgebraicGeometry.projectiveLineTower` and `AlgebraicGeometry.projectiveLineTowerHom` — the
  `n`-fold fibre power of the projective line over `S`, built as an iterated projective line,
  and its projection to `S`.
* `Stacks.EtaleCohomology.BaseChangeZariskiLocalOnBase`,
  `Stacks.EtaleCohomology.BaseChangeForFinite`,
  `Stacks.EtaleCohomology.BaseChangeForComp`,
  `Stacks.EtaleCohomology.BaseChangeDescendsAlongProperSurjective`,
  `Stacks.EtaleCohomology.ChowModificationOverAffine`,
  `Stacks.EtaleCohomology.HasProjectiveLineTowerCover` — the six inputs of the reduction.

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_projectiveLineTowerHom` — cohomology
  commutes with base change for the projection of the `n`-fold power of the projective line.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_projectiveSpace` — and for `ℙⁿ_S ⟶ S`.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isAffine` — and for a proper
  morphism to an affine scheme.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_projectiveLine` — and for every
  proper morphism of schemes.

## Implementation notes

The `n`-fold fibre power of `ℙ¹_S` over `S` is realised as the iterated projective line
`projectiveLineTower S (n+1) = ℙ¹_{projectiveLineTower S n}`; this is the fibre power because
`ℙ¹_T ≅ ℙ¹_S ×_S T` for an `S`-scheme `T`, by
`AlgebraicGeometry.ProjectiveSpace.baseChangeIso`. Its projection to `S` is a composite of
projective lines, so the composition input applies to it directly and no product of schemes has
to be constructed.

Projective space is taken to be `AlgebraicGeometry.ProjectiveSpace`, the model that carries
`AlgebraicGeometry.ProjectiveSpace.instIsProperOver` and
`AlgebraicGeometry.ProjectiveSpace.baseChangeIso` and in which
`AlgebraicGeometry.HasChowModification` is stated. It is the same scheme as
`AlgebraicGeometry.projectiveSpaceOver`, with the same structure morphism, by `rfl`: both are
the pullback of `ℙⁿ_ℤ ⟶ Spec ℤ` along `S ⟶ Spec ℤ` with `Spec ℤ` the terminal scheme.

Six inputs of the source argument are absent from this library and are carried as explicit
hypotheses, one named `def` of `Prop` each.

* `BaseChangeZariskiLocalOnBase` is the use of Lemma 59.51.6
  ([Stacks, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)) made in the first paragraph of
  the source: higher direct images are formed locally on the base, so the condition for the
  restrictions of `f` over a family of affine opens covering the target gives the condition for
  `f`. Both halves of Tag 03Q8 are available here, exhibiting the direct image as the
  sheafification of the presheaf of cohomology over the étale base changes:
  `Stacks.HigherDirectImage.higherDirectImageComparison` for abelian sheaves and
  `Stacks.HigherDirectImage.derivedPushforwardComparison` for unbounded complexes. So is the
  locality of invertibility of a morphism of sheaves on a small étale site,
  `Stacks.EtaleCohomology.isIso_of_isIso_etaleRestrictionAt`. What is missing is the
  identification of the restriction of the base change map of a square with the base change map
  of the restricted square, which is clause (2) of
  [Stacks, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR); the keyed note on
  `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` records that none of that tag's clauses is
  proved here.
* `BaseChangeForFinite` is [Stacks, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E),
  `BaseChangeForComp` is [Stacks, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D) and
  `BaseChangeDescendsAlongProperSurjective` is
  [Stacks, Tag 0A4C](https://stacks.math.columbia.edu/tag/0A4C). Each is a separate lemma of the
  source with its own proof, and each is stated below exactly as the source states it. None is
  implied by the conclusion: the conclusion is a statement about a single morphism given the
  projective line, whereas these are closure properties of the condition that hold for every
  morphism of their kind, and their proofs in the source rest on
  [Stacks, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B) and on the composition spectral
  sequence, neither of which is used here.
* `ChowModificationOverAffine` is Chow's lemma,
  [Stacks, Tag 0202](https://stacks.math.columbia.edu/tag/0202), for a proper morphism with
  affine target, in the form `AlgebraicGeometry.HasChowModification` already present in this
  library. It is satisfiable because a proper morphism is separated and of finite type and an
  affine scheme is quasi-compact and quasi-separated, which are exactly the hypotheses of Tag
  0202.
* `HasProjectiveLineTowerCover` is the display in the last paragraph of the source: the morphism
  `((x₁:y₁), …, (xₙ:yₙ)) ↦ (F₀ : … : Fₙ)` where `∏(xᵢt + yᵢ) = F₀tⁿ + … + Fₙ` is a finite
  surjective morphism from the `n`-fold power of `ℙ¹_S` onto `ℙⁿ_S` over `S`. It is satisfiable:
  the morphism is the quotient by the symmetric group, module-finite on coordinate rings because
  the elementary symmetric functions generate the invariants, and surjective because a binary
  form of degree `n` over an algebraically closed field splits into linear factors. For `n = 0`
  it holds for the trivial reason that `ℙ⁰_S ⟶ S` is an isomorphism, the cover being its
  inverse.

What is *proved* here is the assembly: the induction producing the condition for the tower, the
descent producing it for `ℙⁿ_S ⟶ S`, the two applications of Chow's lemma over an affine base —
including the derivation, from Morphisms, Lemmas 29.42.4 and 29.42.7, that the immersions
occurring there are closed and hence finite, which the source performs and which is carried out
below rather than assumed — and the final localization on the base.

## References

* [Stacks Project, Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0A4C](https://stacks.math.columbia.edu/tag/0A4C)
* [Stacks Project, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D)
* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry

/-- The `n`-fold fibre power of the projective line over `S`, realised as an iterated
projective line: `ℙ¹_T ≅ ℙ¹_S ×_S T` for an `S`-scheme `T`, so the `(n+1)`-st stage is the
projective line over the `n`-th. -/
public def projectiveLineTower (S : Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => S
  | n + 1 => ProjectiveSpace 1 (projectiveLineTower S n)

/-- The projection of the `n`-fold fibre power of the projective line over `S` down to `S`, a
composite of `n` projective lines. -/
public def projectiveLineTowerHom (S : Scheme.{u}) : (n : ℕ) → projectiveLineTower S n ⟶ S
  | 0 => 𝟙 S
  | n + 1 => (ProjectiveSpace 1 (projectiveLineTower S n) ↘ projectiveLineTower S n) ≫
      projectiveLineTowerHom S n

/-- The projection of the `n`-fold fibre power of the projective line to `S` is proper, being a
composite of projective lines. -/
public instance isProper_projectiveLineTowerHom (S : Scheme.{u}) (n : ℕ) :
    IsProper (projectiveLineTowerHom S n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 S))
  | succ n ih =>
      have := ih
      change IsProper ((ProjectiveSpace 1 (projectiveLineTower S n) ↘
        projectiveLineTower S n) ≫ projectiveLineTowerHom S n)
      infer_instance

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **The localization of the condition on the base.** If cohomology commutes with base change
for the restriction of `f` over every affine open of the target, then it does so for `f`. This
is the use the source makes of Lemma 59.51.6. -/
public def BaseChangeZariskiLocalOnBase : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (∀ V : Y.affineOpens, CohomologyCommutesWithBaseChange.{u, v} (f ∣_ V.1)) →
      CohomologyCommutesWithBaseChange.{u, v} f

/-- **[Stacks, Tag 0A4E].** Cohomology commutes with base change for a finite morphism. -/
public def BaseChangeForFinite : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsFinite f → CohomologyCommutesWithBaseChange.{u, v} f

/-- **[Stacks, Tag 0A4D].** If cohomology commutes with base change for two proper morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`, then it does so for `g ∘ f`. -/
public def BaseChangeForComp : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), IsProper f → IsProper g →
    CohomologyCommutesWithBaseChange.{u, v} f → CohomologyCommutesWithBaseChange.{u, v} g →
      CohomologyCommutesWithBaseChange.{u, v} (f ≫ g)

/-- **[Stacks, Tag 0A4C].** If `f : X ⟶ Y` and `g : Y ⟶ Z` are proper, `f` is surjective, and
cohomology commutes with base change for `f` and for `g ∘ f`, then it does so for `g`. -/
public def BaseChangeDescendsAlongProperSurjective : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), IsProper f → IsProper g → Surjective f →
    CohomologyCommutesWithBaseChange.{u, v} f →
      CohomologyCommutesWithBaseChange.{u, v} (f ≫ g) →
        CohomologyCommutesWithBaseChange.{u, v} g

/-- **Chow's lemma, [Stacks, Tag 0202], for a proper morphism with affine target.** -/
public def ChowModificationOverAffine : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsAffine Y → IsProper f → HasChowModification f

/-- **The finite surjective cover of `ℙⁿ_S` by the `n`-fold power of `ℙ¹_S`**, the display in
the last paragraph of [Stacks, Tag 0A4F]. -/
public def HasProjectiveLineTowerCover : Prop :=
  ∀ (S : Scheme.{u}) (n : ℕ), ∃ c : projectiveLineTower S n ⟶ ProjectiveSpace n S,
    IsFinite c ∧ Surjective c ∧
      c ≫ (ProjectiveSpace n S ↘ S) = projectiveLineTowerHom S n

/-- **Cohomology commutes with base change for the projection of the `n`-fold power of the
projective line.** Induction on `n`: the projection of the `(n+1)`-st stage is the projective
line over the `n`-th stage followed by the projection of the `n`-th stage. -/
public theorem cohomologyCommutesWithBaseChange_projectiveLineTowerHom
    (hfin : BaseChangeForFinite.{u, v}) (hcomp : BaseChangeForComp.{u, v})
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (S : Scheme.{u}) (n : ℕ) :
    CohomologyCommutesWithBaseChange.{u, v} (projectiveLineTowerHom S n) := by
  induction n with
  | zero => exact hfin (𝟙 S) inferInstance
  | succ n ih =>
      show CohomologyCommutesWithBaseChange.{u, v}
        ((ProjectiveSpace 1 (projectiveLineTower S n) ↘ projectiveLineTower S n) ≫
          projectiveLineTowerHom S n)
      exact hcomp _ _ inferInstance (isProper_projectiveLineTowerHom S n)
        (hline (projectiveLineTower S n)) ih

/-- **Cohomology commutes with base change for `ℙⁿ_S ⟶ S`.** The `n`-fold power of the
projective line covers `ℙⁿ_S` by a finite surjective morphism over `S`, so the condition for
the projection of that power descends to `ℙⁿ_S ⟶ S`. -/
public theorem cohomologyCommutesWithBaseChange_projectiveSpace
    (hfin : BaseChangeForFinite.{u, v}) (hcomp : BaseChangeForComp.{u, v})
    (hdesc : BaseChangeDescendsAlongProperSurjective.{u, v})
    (hcover : HasProjectiveLineTowerCover.{u})
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (n : ℕ) (S : Scheme.{u}) :
    CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace n S ↘ S) := by
  obtain ⟨c, hcfin, hcsurj, hctri⟩ := hcover S n
  have : IsFinite c := hcfin
  refine hdesc c _ inferInstance inferInstance hcsurj (hfin c hcfin) ?_
  exact CohomologyCommutesWithBaseChange.of_eq hctri.symm
    (cohomologyCommutesWithBaseChange_projectiveLineTowerHom hfin hcomp hline S n)

/-- If cohomology commutes with base change for `g`, it does so for `i ≫ g` when `i` is a proper
immersion, since `i` is then a closed immersion and hence finite. -/
private theorem comp_of_isImmersion_of_isProper (hfin : BaseChangeForFinite.{u, v})
    (hcomp : BaseChangeForComp.{u, v}) {X Y Z : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ Z)
    [IsImmersion i] [IsProper i] [IsProper g] (h : CohomologyCommutesWithBaseChange.{u, v} g) :
    CohomologyCommutesWithBaseChange.{u, v} (i ≫ g) :=
  have : IsClosedImmersion i := .of_isPreimmersion i i.isClosedMap.isClosed_range
  hcomp i g inferInstance inferInstance (hfin i inferInstance) h

/-- **Cohomology commutes with base change for a proper morphism to an affine scheme.** Chow's
lemma provides `π : X' ⟶ X` proper and surjective together with an immersion of `X'` into
`ℙⁿ_Y` over `Y`. Both `X' ⟶ ℙⁿ_Y` and the induced `X' ⟶ ℙⁿ_X` are proper, by Morphisms, Lemma
29.42.7, hence closed immersions and so finite; each therefore composes with a projection of a
projective space to give the condition for `X' ⟶ Y` and for `π`, and the condition for `f`
follows by descent along `π`. -/
public theorem cohomologyCommutesWithBaseChange_of_isAffine
    (hfin : BaseChangeForFinite.{u, v}) (hcomp : BaseChangeForComp.{u, v})
    (hdesc : BaseChangeDescendsAlongProperSurjective.{u, v})
    (hchow : ChowModificationOverAffine.{u})
    (hcover : HasProjectiveLineTowerCover.{u})
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsProper f] :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  obtain ⟨n, X', π, i, hπ, hπsurj, hi, hcomm⟩ := hchow f ‹_› ‹_›
  have : IsProper π := hπ
  have : IsImmersion i := hi
  -- `X' ⟶ ℙⁿ_Y` is proper, hence a closed immersion, hence finite.
  have : IsProper (i ≫ (ProjectiveSpace n Y ↘ Y)) := hcomm ▸ inferInstance
  have : IsProper i := IsProper.of_comp i (ProjectiveSpace n Y ↘ Y)
  -- hence cohomology commutes with base change for `X' ⟶ Y`.
  have hXY : CohomologyCommutesWithBaseChange.{u, v} (π ≫ f) :=
    CohomologyCommutesWithBaseChange.of_eq hcomm.symm
      (comp_of_isImmersion_of_isProper hfin hcomp i _
        (cohomologyCommutesWithBaseChange_projectiveSpace hfin hcomp hdesc hcover hline n Y))
  -- the induced morphism `X' ⟶ ℙⁿ_X = X ×_Y ℙⁿ_Y` is proper, hence finite by the same route.
  set j : X' ⟶ pullback (ProjectiveSpace n Y ↘ Y) f := pullback.lift i π hcomm.symm with hj
  have hjfst : j ≫ pullback.fst (ProjectiveSpace n Y ↘ Y) f = i := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd (ProjectiveSpace n Y ↘ Y) f = π := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.fst (ProjectiveSpace n Y ↘ Y) f) := hjfst ▸ ‹IsImmersion i›
  have : IsImmersion j := IsImmersion.of_comp j (pullback.fst _ _)
  have : IsProper (j ≫ pullback.snd (ProjectiveSpace n Y ↘ Y) f) := hjsnd ▸ ‹IsProper π›
  have : IsProper j := IsProper.of_comp j (pullback.snd _ _)
  -- the second projection of that pullback is `ℙⁿ_X ⟶ X` up to the canonical isomorphism.
  have hsnd : CohomologyCommutesWithBaseChange.{u, v}
      (pullback.snd (ProjectiveSpace n Y ↘ Y) f) :=
    CohomologyCommutesWithBaseChange.of_eq (ProjectiveSpace.baseChangeIso_hom_over n f)
      (hcomp (ProjectiveSpace.baseChangeIso n f).hom _ inferInstance inferInstance
        (hfin _ inferInstance)
        (cohomologyCommutesWithBaseChange_projectiveSpace hfin hcomp hdesc hcover hline n X))
  have hπbc : CohomologyCommutesWithBaseChange.{u, v} π :=
    CohomologyCommutesWithBaseChange.of_eq hjsnd
      (comp_of_isImmersion_of_isProper hfin hcomp j _ hsnd)
  exact hdesc π f inferInstance inferInstance hπsurj hπbc hXY

/-- To prove that cohomology commutes with base change for every proper morphism of schemes it
suffices to prove it for the morphism `ℙ¹_S ⟶ S` for every scheme `S`, given the six inputs
`hfin`, `hcomp`, `hloc`, `hdesc`, `hchow` and `hcover`.  Those inputs are not needed:
[Stacks, Tag 0A4F] is
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_projectiveLine_unconditional`. -/
public theorem cohomologyCommutesWithBaseChange_of_projectiveLine
    (hfin : BaseChangeForFinite.{u, v}) (hcomp : BaseChangeForComp.{u, v})
    (hloc : BaseChangeZariskiLocalOnBase.{u, v})
    (hdesc : BaseChangeDescendsAlongProperSurjective.{u, v})
    (hchow : ChowModificationOverAffine.{u})
    (hcover : HasProjectiveLineTowerCover.{u})
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsProper f) :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  have := hf
  refine hloc f fun V ↦ ?_
  have : IsAffine V.1.toScheme := V.2
  exact cohomologyCommutesWithBaseChange_of_isAffine hfin hcomp hdesc hchow hcover hline _

end Stacks.EtaleCohomology

end
