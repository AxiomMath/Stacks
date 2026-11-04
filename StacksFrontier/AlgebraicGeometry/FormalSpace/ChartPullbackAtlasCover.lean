module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleSource

/-!
# Atlases of the fibre product of a chart with a morphism

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a morphism of fppf
sheaves, and let `v : V ⟶ Y` be representable by algebraic spaces and étale. The proofs of
Stacks 0GBB and Stacks 0GBD choose a covering of `V ×_Y X` as in Definition 0AIM whose members
inherit a property of the members of a given atlas `{Xᵢ ⟶ X}` of `X`. This file constructs such
a covering: each `V ×_Y Xᵢ` is a formal algebraic space, being representable étale over the affine
formal algebraic space `Xᵢ` (the étale case of Stacks 0AJH), and the members of its atlases,
composed with the base change `V ×_Y Xᵢ ⟶ V ×_Y X` of `Xᵢ ⟶ X`, cover `V ×_Y X`. Each member
maps to some `Xᵢ` by a morphism representable by algebraic spaces, through which a property of
affine formal algebraic spaces descending along representable morphisms (Stacks 0AKQ) passes to
it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isAffineEtaleCover_of_isFormalAlgebraicSpace`: an atlas
  of a formal algebraic space is an affine étale covering.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_pullback_of_atlas`: the covering of
  `V ×_Y X` described above.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_pullback_of_isFormalAlgebraicSpace`:
  the same covering, for `X` a formal algebraic space, with the subordination forgotten.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An atlas as in Definition 0AIM of a formal algebraic space is an affine étale covering. -/
theorem exists_isAffineEtaleCover_of_isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X),
      IsAffineEtaleCover B S hS U a := by
  obtain ⟨-, I, U, a, haff, het, hsurj⟩ := hX
  exact ⟨I, U, a, haff, het, hsurj⟩

/-- The étale case of Stacks 0AJH follows from Stacks 0AIU, in the form of
`isFormalAlgebraicSpace_of_representable_over_affineFormal`; the set-theoretic condition of
Stacks 0AIS on the source is `satisfiesSetTheoreticCondition_of_representable_over_affineFormal`.
-/
theorem representableEtaleOverAffineIsFormal_of_colimitOfThickenings
    (hcolim : ColimitOfThickeningsIsFormalAlgebraicSpace B S hS) :
    RepresentableEtaleOverAffineIsFormal B S hS := fun f hY hf ↦
  isFormalAlgebraicSpace_of_representable_over_affineFormal B S hS f hY hf.1
    (satisfiesSetTheoreticCondition_of_representable_over_affineFormal B S hS f hY hf.1) hcolim

section

variable {X Y V Xi : FppfSheaf B S hS} (f : X ⟶ Y) (v : V ⟶ Y) (x : Xi ⟶ X)

/-- The base change `V ×_Y Xᵢ ⟶ V ×_Y X` of a morphism `x : Xᵢ ⟶ X`. -/
def pullbackCompMap : pullback v (x ≫ f) ⟶ pullback v f :=
  pullback.lift (pullback.fst v (x ≫ f)) (pullback.snd v (x ≫ f) ≫ x)
    (by simpa only [Category.assoc] using pullback.condition (f := v) (g := x ≫ f))

/-- `pullbackCompMap` commutes with the first projections to `V`. -/
@[reassoc (attr := simp)]
theorem pullbackCompMap_fst :
    pullbackCompMap B S hS f v x ≫ pullback.fst v f = pullback.fst v (x ≫ f) :=
  pullback.lift_fst _ _ _

/-- `pullbackCompMap` followed by the projection to `X` is the projection to `Xᵢ` then `x`. -/
@[reassoc (attr := simp)]
theorem pullbackCompMap_snd :
    pullbackCompMap B S hS f v x ≫ pullback.snd v f = pullback.snd v (x ≫ f) ≫ x :=
  pullback.lift_snd _ _ _

/-- `V ×_Y Xᵢ` is the base change of `x : Xᵢ ⟶ X` along `V ×_Y X ⟶ X`. -/
theorem isPullback_pullbackCompMap :
    IsPullback (pullback.snd v (x ≫ f)) (pullbackCompMap B S hS f v x) x
      (pullback.snd v f) := by
  refine IsPullback.of_bot ?_ (pullbackCompMap_snd B S hS f v x).symm
    (IsPullback.of_hasPullback v f).flip
  rw [pullbackCompMap_fst]
  exact (IsPullback.of_hasPullback v (x ≫ f)).flip

end

/-- **A covering of `V ×_Y X` subordinate to an atlas of `X`.** Let `f : X ⟶ Y` be a morphism of
fppf sheaves, let `v : V ⟶ Y` be representable étale, and let `{xᵢ : Xᵢ ⟶ X}` be an affine étale
covering. Then `V ×_Y X` has an affine étale covering `{aₗ : Uₗ ⟶ V ×_Y X}` each member of which
maps to a member `X_{ι l}` of the atlas by a representable étale morphism `rₗ`, compatibly with the
projection `V ×_Y X ⟶ X`.

The members are those of atlases of the formal algebraic spaces `V ×_Y Xᵢ` (Stacks 0AJ3, in
the form `isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal`, which is
where the étale case of Stacks 0AJH enters as `hEt`), and `rₗ` is the chart map followed by the
projection `V ×_Y Xᵢ ⟶ Xᵢ`. -/
theorem exists_affineEtaleCover_pullback_of_atlas
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y V : FppfSheaf B S hS} (f : X ⟶ Y) (v : V ⟶ Y) (hv : IsRepresentableEtale B S hS v)
    {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (x : ∀ i, Xi i ⟶ X)
    (hx : IsAffineEtaleCover B S hS Xi x) :
    ∃ (L : Type (u + 1)) (U : L → FppfSheaf B S hS) (a : ∀ l, U l ⟶ pullback v f)
      (ι : L → I) (r : ∀ l, U l ⟶ Xi (ι l)),
      IsAffineEtaleCover B S hS U a ∧ (∀ l, IsRepresentableEtale B S hS (r l)) ∧
        ∀ l, a l ≫ pullback.snd v f = r l ≫ x (ι l) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hT : ∀ i, IsFormalAlgebraicSpace B S hS (pullback v (x i ≫ f)) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt v
      (x i ≫ f) (hx.1 i) hv
  choose K W c hc using fun i ↦ exists_isAffineEtaleCover_of_isFormalAlgebraicSpace B S hS (hT i)
  refine ⟨Σ i, K i, fun l ↦ W l.1 l.2, fun l ↦ c l.1 l.2 ≫ pullbackCompMap B S hS f v (x l.1),
    fun l ↦ l.1, fun l ↦ c l.1 l.2 ≫ pullback.snd v (x l.1 ≫ f),
    ⟨fun l ↦ (hc l.1).1 l.2, fun l ↦ ?_, ?_⟩, fun l ↦ ?_, fun l ↦ ?_⟩
  · exact IsRepresentableEtale.comp B S hS ((hc l.1).2.1 l.2)
      (isRepresentableEtale_of_isPullback B S hS (isPullback_pullbackCompMap B S hS f v (x l.1))
        (hx.2.1 l.1))
  · exact Sheaf.isLocallySurjective_sigmaDesc_sigma_comp
      (fun i ↦ pullbackCompMap B S hS f v (x i)) c
      (isLocallySurjective_sigmaDesc_of_isPullback B S hS (pullback.snd v f)
        (fun i ↦ isPullback_pullbackCompMap B S hS f v (x i)) hx.2.2) fun i ↦ (hc i).2.2
  · exact IsRepresentableEtale.comp B S hS ((hc l.1).2.1 l.2)
      (isRepresentableEtale_pullback_snd B S hS v (x l.1 ≫ f) hv)
  · simp

/-- **An affine étale covering of `V ×_Y X`** for `X` a formal algebraic space: the covering of
`exists_affineEtaleCover_pullback_of_atlas` for an atlas of `X`. -/
theorem exists_affineEtaleCover_pullback_of_isFormalAlgebraicSpace
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y V : FppfSheaf B S hS} (f : X ⟶ Y) (v : V ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X)
    (hv : IsRepresentableEtale B S hS v) :
    ∃ (L : Type (u + 1)) (U : L → FppfSheaf B S hS) (a : ∀ l, U l ⟶ pullback v f),
      IsAffineEtaleCover B S hS U a := by
  obtain ⟨I, Xi, x, hx⟩ := exists_isAffineEtaleCover_of_isFormalAlgebraicSpace B S hS hX
  obtain ⟨L, U, a, -, -, hU, -⟩ :=
    exists_affineEtaleCover_pullback_of_atlas B S hS hEt f v hv x hx
  exact ⟨L, U, a, hU⟩

end AlgebraicGeometry.FormalSpace

end
