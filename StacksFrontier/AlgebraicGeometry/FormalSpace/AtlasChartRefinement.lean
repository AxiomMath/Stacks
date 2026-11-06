module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Refining an atlas of a formal algebraic space against an affine étale chart

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with an atlas `{Xᵢ ⟶ X}` as in Definition **Stacks 0AIM**, and let `g : Y ⟶ X` be a
morphism from an affine formal algebraic space which is representable by algebraic spaces and
étale. The first half of the proof of the implication (2) ⟹ (1) of **Stacks 0AKX** refines the
atlas against the chart: the fibre products `Xᵢ ×_X Y` are formal algebraic spaces, so each has
an atlas `{Xᵢⱼ ⟶ Xᵢ ×_X Y}` as in Definition 0AIM, and the resulting family `{Xᵢⱼ ⟶ Y}` is a
jointly locally surjective family of representable étale morphisms out of affine formal
algebraic spaces, each member of which also maps to the atlas member `Xᵢ` representably and
étale.

This file proves exactly that, in
`AlgebraicGeometry.FormalSpace.exists_affineEtaleFamily_over_chart_of_atlas`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affineEtaleFamily_over_chart_of_atlas`: the refined
  family, together with its maps to the members of the atlas.

## What is assumed

Nothing. In particular the fibre products of the members of the atlas with the chart are formal
algebraic spaces by **Stacks 0AJ3** in the form
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`,
which this library proves outright: every one of the three sheaves involved — the base `X`, the
atlas member `Xᵢ` and the chart `Y` — is a formal algebraic space, so the weaker diagonal
hypothesis of **Stacks 0AJ2**, whose proof needs **Stacks 05ZH** at arbitrary order (not in
this library), is not what this step needs. Nothing below mentions a
property of affine formal algebraic spaces, so **Stacks 0AKQ** is left to the consumer: a
property which descends along a morphism of affine formal algebraic spaces representable by
algebraic spaces passes from `Xᵢ` to `Xᵢⱼ` along the maps `v` produced here.

What the implication (2) ⟹ (1) of Stacks 0AKX needs beyond this file is the *second* half of
its proof: quasi-compactness of `Y` cutting the family down to a finite one, and the finite
disjoint union of the resulting charts mapping to `Y` surjectively, flatly and representably.

## Implementation notes

Joint local surjectivity of the refined family is assembled from joint local surjectivity of
the base-changed atlas, `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`, and
of the atlases of the fibre products, by the identification of local surjectivity with
epimorphy: the induced morphism `∐_{i,j} Xᵢⱼ ⟶ ∐ᵢ (Xᵢ ×_X Y)` is an epimorphism because each
`∐ⱼ Xᵢⱼ ⟶ Xᵢ ×_X Y` is, and it composes with `∐ᵢ (Xᵢ ×_X Y) ⟶ Y` to the morphism in question.
This is the argument the third bullet of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover` makes for the atlas of a
sheaf with an étale cover by formal algebraic spaces.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The refinement of an atlas against an affine étale chart.** Let `X` be a formal algebraic
space over `S`, let `{Xᵢ ⟶ X}` be an atlas as in Definition **Stacks 0AIM**, and let
`g : Y ⟶ X` be a morphism from an affine formal algebraic space which is representable by
algebraic spaces and étale. Then there is a family `{Uₖ ⟶ Y}` of affine formal algebraic spaces
over `Y`, each map representable by algebraic spaces and étale, jointly locally surjective, and
each `Uₖ` moreover maps to the atlas member `X_{κ k}` by a morphism which is representable by
algebraic spaces and étale.

The members are the charts of the fibre products `Xᵢ ×_X Y`, which are formal algebraic spaces
by **Stacks 0AJ3**; the two maps out of a chart are its composites with the two projections of
the fibre product, each of which is a base change of a representable étale morphism. -/
theorem exists_affineEtaleFamily_over_chart_of_atlas
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS) (fi : ∀ i, Xi i ⟶ X)
    (hXiaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hXiet : ∀ i, IsRepresentableEtale B S hS (fi i))
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fi))
    {Y : FppfSheaf B S hS} (g : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hg : IsRepresentableEtale B S hS g) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (U : K → FppfSheaf B S hS) (w : ∀ k, U k ⟶ Y) (κ : K → I)
      (v : ∀ k, U k ⟶ Xi (κ k)),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (U k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k)) ∧
      (∀ k, IsRepresentableEtale B S hS (v k)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the fibre products of the atlas members with the chart, Stacks 0AJ3
  have hfib : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (fi i) g) := fun i ↦
    isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (fi i) g hX
      (hXiaff i) (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hY)
  choose J U a hUaff hUet hUcov using fun i ↦ (hfib i).2
  -- the two projections of a fibre product are representable étale
  have hsnd : ∀ i, IsRepresentableEtale B S hS (pullback.snd (fi i) g) := fun i ↦
    isRepresentableEtale_pullback_snd B S hS (fi i) g (hXiet i)
  have hfst : ∀ i, IsRepresentableEtale B S hS (pullback.fst (fi i) g) := fun i ↦
    isRepresentableEtale_of_isPullback B S hS
      (IsPullback.of_hasPullback (fi i) g).flip hg
  refine ⟨Σ i, J i, fun k ↦ U k.1 k.2, fun k ↦ a k.1 k.2 ≫ pullback.snd (fi k.1) g,
    fun k ↦ k.1, fun k ↦ a k.1 k.2 ≫ pullback.fst (fi k.1) g, fun k ↦ hUaff k.1 k.2,
    fun k ↦ IsRepresentableEtale.comp B S hS (hUet k.1 k.2) (hsnd k.1),
    fun k ↦ IsRepresentableEtale.comp B S hS (hUet k.1 k.2) (hfst k.1), ?_⟩
  -- joint local surjectivity, by the epimorphy of the two stages
  let q (i : I) : (∐ fun j ↦ U i j) ⟶ pullback (fi i) g := Sigma.desc (a i)
  let e : (∐ fun k : Σ i, J i ↦ U k.1 k.2) ⟶ (∐ fun i ↦ pullback (fi i) g) :=
    Sigma.desc fun k ↦ a k.1 k.2 ≫ Sigma.ι (fun i ↦ pullback (fi i) g) k.1
  have he : Epi e := by
    refine ⟨fun {T} k l hkl ↦ Sigma.hom_ext _ _ fun i ↦ ?_⟩
    have : Epi (q i) := (Sheaf.isLocallySurjective_iff_epi (q i)).mp (hUcov i)
    refine (cancel_epi (q i)).1 (Sigma.hom_ext _ _ fun j ↦ ?_)
    simpa [q, e] using congrArg (Sigma.ι (fun k : Σ i, J i ↦ U k.1 k.2) ⟨i, j⟩ ≫ ·) hkl
  have hcomp : e ≫ (Sigma.desc fun i ↦ pullback.snd (fi i) g)
      = Sigma.desc fun k : Σ i, J i ↦ a k.1 k.2 ≫ pullback.snd (fi k.1) g :=
    Sigma.hom_ext _ _ fun k ↦ by simp [e]
  have := (Sheaf.isLocallySurjective_iff_epi _).mp
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd g fi hcover)
  rw [← hcomp]
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr (epi_comp e _)

end AlgebraicGeometry.FormalSpace

end
