module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# Types of fibre products of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `X ⟶ Y` and `Z ⟶ Y` be morphisms
of fppf sheaves on the big fppf site of `S`. **Stacks 0GBB** says that each of the five types
of Stacks 0AKY — locally countably indexed, locally countably indexed and classical, locally
weakly adic, locally adic\* and, under a finite type condition on the reductions, locally
Noetherian — passes from `X` and `Z` to `X ×_Y Z`.

All five clauses have the same proof. The charts of `X ×_Y Z` are the fibre products
`U ×_{Vⱼ} W` of a chart `U` of `Vⱼ ×_Y X` with a chart `W` of `Vⱼ ×_Y Z` over a chart `Vⱼ` of
`Y`, built in `StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover`; these are affine
formal algebraic spaces by Stacks 0AN3 and are representable étale over `X ×_Y Z`, and `U` and
`W` carry the type in question because they are affine formal algebraic spaces representable
étale over `X` and over `Z`. So only the affine case of the clause is left, which at the level
of rings is the corresponding clause of Stacks 0GB4.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAffineEtaleChartPropertyOfAtlas`: condition (2) implies
  condition (1) of **Stacks 0AKX** for a property of fppf sheaves.
* `AlgebraicGeometry.FormalSpace.AffineChartFibreProductStable`: the affine case of a clause.
* `AlgebraicGeometry.FormalSpace.HasChartPullbackCover`: the surjectivity assertion of
  Definition 0AIM for the family of chart fibre products of `X ×_Y Z`.
* `AlgebraicGeometry.FormalSpace.HasLocallyOfFiniteTypeReduction`: the hypothesis of clause (5)
  that the induced morphism `X_red ⟶ Y_red` is locally of finite type.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasWithProperty_pullback`: the common content
  of the five clauses, for an arbitrary property of fppf sheaves.

## Implementation notes

Five inputs of the source are explicit hypotheses because the library does not carry them.

* `h0AKX` is the implication from condition (2) to condition (1) of Stacks 0AKX. The five
  predicates of Stacks 0AKY are defined in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.Types` by condition (2), an atlas all of whose
  members have the type, and the proof needs condition (1) for the charts of `Vⱼ ×_Y X` and of
  `Vⱼ ×_Y Z`, which are not members of the given atlases.
* `h0AJ7` is the assertion of Stacks 0AJ7 that an affine formal algebraic space is separated,
  in the form of clause (2) of Stacks 0AJ6 which
  `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback` consumes. It is what
  makes the chart fibre products affine.
* `h0AJ3f` and `h0AJ3g` are the assertion of Stacks 0AJ3 that `Vⱼ ×_Y X` and `Vⱼ ×_Y Z` are
  formal algebraic spaces, so that they have atlases at all; this is the hypothesis
  `hpb` of `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`.
* `hPaff` is the affine case of the clause: Stacks 0AN3 identifies the chart fibre product with
  the formal spectrum of a completed tensor product, which the library does not carry, and the
  clause then follows from the corresponding clause of Stacks 0GB4, which it does.
* `hcover` is the surjectivity assertion of Definition 0AIM for the family of chart fibre
  products; it is the hypothesis of the same name of
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_pullback_snd_of_chartCovers`.
* `hset` is the set-theoretic condition of Stacks 0AIS for `X ×_Y Z`, the one part of
  Stacks 0AJ2 that the chart cover does not supply.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AKX, condition (2) implies condition (1)**, for a property `P` of fppf sheaves:
if a sheaf has an atlas as in Definition 0AIM all of whose members satisfy `P`, then every
affine formal algebraic space representable étale over it satisfies `P`. -/
abbrev HasAffineEtaleChartPropertyOfAtlas (P : FppfSheaf B S hS → Prop) : Prop :=
  ∀ T : FppfSheaf B S hS, HasAffineEtaleAtlasWithProperty B S hS T P →
    ∀ (U : FppfSheaf B S hS) (a : U ⟶ T), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → P U

/-- The affine case of a clause of Stacks 0GBB for a property `P` of fppf sheaves: the fibre
product of two affine formal algebraic spaces satisfying `P` over an affine formal algebraic
space satisfies `P`. -/
abbrev AffineChartFibreProductStable (P : FppfSheaf B S hS → Prop) : Prop :=
  ∀ {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsAffineFormalAlgebraicSpace B S hS W → P U → P W → P (pullback t s)

/-- The assertion of **Stacks 0AJ3** used in the proofs of Stacks 0ANG and 0GBB: the fibre
product of a morphism with an affine étale chart of its target is a formal algebraic space. -/
abbrev HasFormalChartPullbacks {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f)

/-- The surjectivity assertion of **Definition 0AIM** for the chart cover of `X ×_Y Z`: for
every affine étale covering `{Vⱼ ⟶ Y}` and all affine étale coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and
`{Wⱼₖ ⟶ Vⱼ ×_Y Z}`, the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` jointly cover `X ×_Y Z`. -/
abbrev HasChartPullbackCover {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v →
    ∀ {I : J → Type (u + 1)} {U : ∀ j, I j → FppfSheaf B S hS}
      (a : ∀ j i, U j i ⟶ pullback (v j) f), (∀ j, IsAffineEtaleCover B S hS (U j) (a j)) →
    ∀ {K : J → Type (u + 1)} {W : ∀ j, K j → FppfSheaf B S hS}
      (b : ∀ j k, W j k ⟶ pullback (v j) g), (∀ j, IsAffineEtaleCover B S hS (W j) (b j)) →
      Sheaf.IsLocallySurjective (Sigma.desc fun p : Σ j, I j × K j ↦
        chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2))

/-- The hypothesis of clause (5) of Stacks 0GBB: the morphism `X_red ⟶ Y_red` induced by `f` on
the reductions of Stacks 0AIN is locally of finite type. -/
abbrev HasLocallyOfFiniteTypeReduction {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (Xred Yred : FppfSheaf B S hS) (iX : Xred ⟶ X) (iY : Yred ⟶ Y) (fred : Xred ⟶ Yred),
    IsReduction B S hS X Xred iX ∧ IsReduction B S hS Y Yred iY ∧
      fred ≫ iY = iX ≫ f ∧ IsLocallyOfFiniteType B S hS fred

/-- An fppf sheaf satisfying the set-theoretic condition of Stacks 0AIS which has an atlas as
in Definition 0AIM all of whose members satisfy a property is a formal algebraic space. -/
theorem isFormalAlgebraicSpace_of_affineEtaleAtlasWithProperty {X : FppfSheaf B S hS}
    {P : FppfSheaf B S hS → Prop} (hset : SatisfiesSetTheoreticCondition B S hS X)
    (h : HasAffineEtaleAtlasWithProperty B S hS X P) : IsFormalAlgebraicSpace B S hS X := by
  obtain ⟨I, Xi, fi, haff, het, hsurj, -⟩ := h
  exact ⟨hset, I, Xi, fi, haff, het, hsurj⟩

/-- The common content of the five clauses of **Stacks 0GBB**: the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an atlas of `X ×_Y Z` as in Definition 0AIM all of whose members satisfy
`P`, so condition (2) of Stacks 0AKX for `P` passes from `X` and `Z` to `X ×_Y Z`. -/
theorem hasAffineEtaleAtlasWithProperty_pullback (P : FppfSheaf B S hS → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hXatlas : HasAffineEtaleAtlasWithProperty B S hS X P)
    (hZatlas : HasAffineEtaleAtlasWithProperty B S hS Z P)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas B S hS P)
    (h0AJ7 : ∀ V : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS V →
      IsSeparated B S hS V)
    (h0AJ3f : HasFormalChartPullbacks B S hS f) (h0AJ3g : HasFormalChartPullbacks B S hS g)
    (hPaff : AffineChartFibreProductStable B S hS P)
    (hcover : HasChartPullbackCover B S hS f g) :
    HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, J, V, v, hVaff, hVet, hVsurj⟩ := hY
  choose I U a hUaff hUet hUsurj using fun j ↦ (h0AJ3f (V j) (v j) (hVaff j) (hVet j)).2
  choose K W b hWaff hWet hWsurj using fun j ↦ (h0AJ3g (V j) (v j) (hVaff j) (hVet j)).2
  refine ⟨Σ j, I j × K j,
    fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ ?_, fun p ↦ ?_, ?_, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hVaff p.1))
      (h0AJ7 (V p.1) (hVaff p.1)) (hUaff p.1 p.2.1) (hWaff p.1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hVet p.1) (hUet p.1 p.2.1) (hWet p.1 p.2.2)
  · exact hcover v ⟨hVaff, hVet, hVsurj⟩ a (fun j ↦ ⟨hUaff j, hUet j, hUsurj j⟩) b
      fun j ↦ ⟨hWaff j, hWet j, hWsurj j⟩
  · have hP {T A : FppfSheaf B S hS} {t : T ⟶ Y} (hT : HasAffineEtaleAtlasWithProperty B S hS T P)
        (j : J) {c : A ⟶ pullback (v j) t} (hA : IsAffineFormalAlgebraicSpace B S hS A)
        (hc : IsRepresentableEtale B S hS c) : P A :=
      h0AKX _ hT _ _ hA (.comp B S hS hc
        (isRepresentableEtale_pullback_snd B S hS _ _ (hVet j)))
    exact hPaff _ _ (hUaff p.1 p.2.1) (hVaff p.1) (hWaff p.1 p.2.2)
      (hP hXatlas p.1 (hUaff p.1 p.2.1) (hUet p.1 p.2.1))
      (hP hZatlas p.1 (hWaff p.1 p.2.2) (hWet p.1 p.2.2))

end AlgebraicGeometry.FormalSpace

end
