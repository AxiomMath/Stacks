module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms

/-!
# The chart fibre products cover the fibre product

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of fppf sheaves on the big fppf site of `S`. Given a covering `{Vⱼ ⟶ Y}` as in
Definition 0AIM and coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same kind, the
chart fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/PullbackChartCover.lean` form a covering of
`X ×_Y Z` as in Definition 0AIM, each member of which maps to `Z` through the chart `Wⱼₖ`. This
is the covering the proof of Stacks 0GBD runs on.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_chartPullbackMap`: the charts
  `U ×_V W` jointly cover `X ×_Y Z`.
* `AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_chartFactorization_pullback_snd`: the
  covering clause of condition (3) of Stacks 0ANG for `pr₂`.

## Implementation notes

That `U ×_V W` is again an affine formal algebraic space is clause (1) of Stacks 0AN3
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback`) applied to the chart
`V`, whose separatedness is Stacks 0AJ7
(`AlgebraicGeometry.FormalSpace.isSeparated_of_isAffineFormalAlgebraicSpace`).

The joint surjectivity of the chart fibre products is obtained by factoring each of them
through `U ×_X (X ×_Y Z)`. The family `{Uⱼᵢ ⟶ X}` covers `X`, so its base change
`{Uⱼᵢ ×_X (X ×_Y Z) ⟶ X ×_Y Z}` covers `X ×_Y Z`; and over a fixed member of it the chart
fibre products with varying `k` are the base change of `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` along a comparison
`Uⱼᵢ ×_X (X ×_Y Z) ⟶ Vⱼ ×_Y Z`. The two steps are composed by
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma_comp` after reindexing.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart cover of the fibre product -/

/-- The two comparison morphisms behind the joint surjectivity of the chart fibre products: for
a chart `a : U ⟶ V ×_Y X`, there is a morphism `U ×_X (X ×_Y Z) ⟶ V ×_Y Z` along which each chart
fibre product `U ×_V W` is the base change of the chart `b : W ⟶ V ×_Y Z`, by a morphism to
`U ×_X (X ×_Y Z)` whose composite with the projection to `X ×_Y Z` is the chart map of
`U ×_V W`. -/
private theorem exists_comparison_isPullback_chartPullbackMap
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y) {V U : FppfSheaf B S hS}
    (v : V ⟶ Y) (a : U ⟶ pullback v f) :
    ∃ cmp : pullback (a ≫ pullback.snd v f) (pullback.fst f g) ⟶ pullback v g,
      ∀ {W : FppfSheaf B S hS} (b : W ⟶ pullback v g),
        ∃ lift : pullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) ⟶
            pullback (a ≫ pullback.snd v f) (pullback.fst f g),
          IsPullback (pullback.snd (a ≫ pullback.fst v f) (b ≫ pullback.fst v g)) lift b cmp ∧
            lift ≫ pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) =
              chartPullbackMap B S hS f g v a b := by
  have hcmp : (pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) ≫ a ≫
      pullback.fst v f) ≫ v = (pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) ≫
        pullback.snd f g) ≫ g := by
    simp only [Category.assoc]
    rw [pullback.condition (f := v) (g := f), ← pullback.condition (f := f) (g := g)]
    simpa only [Category.assoc] using
      (pullback.condition (f := a ≫ pullback.snd v f) (g := pullback.fst f g)) =≫ f
  let cmp := pullback.lift _ _ hcmp
  have cmp_fst : cmp ≫ pullback.fst v g =
      pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) ≫ a ≫ pullback.fst v f :=
    pullback.lift_fst _ _ _
  have cmp_snd : cmp ≫ pullback.snd v g =
      pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) ≫ pullback.snd f g :=
    pullback.lift_snd _ _ _
  have hcmpPb : IsPullback (pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g)) cmp
      (a ≫ pullback.fst v f) (pullback.fst v g) := by
    have e : (a ≫ pullback.fst v f) ≫ v = (a ≫ pullback.snd v f) ≫ f := by
      simp only [Category.assoc, pullback.condition]
    refine IsPullback.of_bot ?_ cmp_fst.symm (IsPullback.of_hasPullback v g)
    rw [cmp_snd, e]
    exact (IsPullback.of_hasPullback (a ≫ pullback.snd v f) (pullback.fst f g)).paste_vert
      (IsPullback.of_hasPullback f g)
  refine ⟨cmp, fun {W} b ↦ ?_⟩
  let lift := pullback.lift (pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g))
    (chartPullbackMap B S hS f g v a b) (chartPullbackMap_comp_fst B S hS f g v a b).symm
  have lift_fst : lift ≫ pullback.fst (a ≫ pullback.snd v f) (pullback.fst f g) =
      pullback.fst (a ≫ pullback.fst v f) (b ≫ pullback.fst v g) := pullback.lift_fst _ _ _
  have lift_snd : lift ≫ pullback.snd (a ≫ pullback.snd v f) (pullback.fst f g) =
      chartPullbackMap B S hS f g v a b := pullback.lift_snd _ _ _
  refine ⟨lift, IsPullback.of_bot ?_ ?_ hcmpPb.flip, lift_snd⟩
  · rw [lift_fst]
    exact (IsPullback.of_hasPullback (a ≫ pullback.fst v f) (b ≫ pullback.fst v g)).flip
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, cmp_fst, ← Category.assoc lift, lift_fst]
      exact pullback.condition.symm
    · rw [Category.assoc, Category.assoc, cmp_snd, ← Category.assoc lift, lift_snd,
        chartPullbackMap_comp_snd]

/-- Joint local surjectivity is invariant under reindexing the family: a family of morphisms of
fppf sheaves is jointly locally surjective as soon as some reindexing of it is. -/
private theorem isLocallySurjective_sigmaDesc_reindex
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {Λ Λ' : Type (u + 1)} (e : Λ' → Λ) {A : Λ → FppfSheaf B S hS} {F : FppfSheaf B S hS}
    (c : ∀ l, A l ⟶ F)
    (h : Sheaf.IsLocallySurjective (Sigma.desc fun l' ↦ c (e l'))) :
    Sheaf.IsLocallySurjective (Sigma.desc c) := by
  rw [Sheaf.isLocallySurjective_iff_epi] at h ⊢
  constructor
  intro T α β hab
  refine (cancel_epi (Sigma.desc fun l' ↦ c (e l'))).1 (Sigma.hom_ext _ _ fun l' ↦ ?_)
  simpa only [← Category.assoc, Sigma.ι_comp_desc] using Sigma.ι A (e l') ≫= hab

/-- **The surjectivity assertion of Definition 0AIM for the chart cover of `X ×_Y Z`.** Let
`{Vⱼ ⟶ Y}` be a jointly locally surjective family, and for each `j` let `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and
`{Wⱼₖ ⟶ Vⱼ ×_Y Z}` be jointly locally surjective families. Then the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` jointly cover `X ×_Y Z`.

The family factors through the fibre products `Uⱼᵢ ×_X (X ×_Y Z)`: those cover `X ×_Y Z`,
being the base change along `X ×_Y Z ⟶ X` of the family `{Uⱼᵢ ⟶ X}`, which covers `X` because
`{Vⱼ ×_Y X ⟶ X}` is the base change of `{Vⱼ ⟶ Y}`; and over each of them the chart fibre
products with varying `k` cover, being the base change of `{Wⱼₖ ⟶ Vⱼ ×_Y Z}` along the
comparison `Uⱼᵢ ×_X (X ×_Y Z) ⟶ Vⱼ ×_Y Z`. -/
theorem isLocallySurjective_sigmaDesc_chartPullbackMap
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Y)
    (hv : Sheaf.IsLocallySurjective (Sigma.desc v))
    {I : J → Type (u + 1)} {U : ∀ j, I j → FppfSheaf B S hS}
    (a : ∀ j i, U j i ⟶ pullback (v j) f)
    (ha : ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (a j)))
    {K : J → Type (u + 1)} {W : ∀ j, K j → FppfSheaf B S hS}
    (b : ∀ j k, W j k ⟶ pullback (v j) g)
    (hb : ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (b j))) :
    Sheaf.IsLocallySurjective (Sigma.desc fun p : Σ j, I j × K j ↦
      chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2)) := by
  have hX : Sheaf.IsLocallySurjective (Sigma.desc fun q : Σ j, I j ↦
      a q.1 q.2 ≫ pullback.snd (v q.1) f) :=
    Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun j ↦ pullback.snd (v j) f) a
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hv) ha
  have hm : Sheaf.IsLocallySurjective (Sigma.desc fun q : Σ j, I j ↦
      pullback.snd (a q.1 q.2 ≫ pullback.snd (v q.1) f) (pullback.fst f g)) :=
    Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.fst f g) _ hX
  choose cmp hcmp using fun q : Σ j, I j ↦
    exists_comparison_isPullback_chartPullbackMap B S hS f g (v q.1) (a q.1 q.2)
  choose lift hlift hliftsnd using fun (q : Σ j, I j) (k : K q.1) ↦ hcmp q (b q.1 k)
  have hk : ∀ q : Σ j, I j, Sheaf.IsLocallySurjective (Sigma.desc fun k : K q.1 ↦
      lift q k) := fun q ↦
    isLocallySurjective_sigmaDesc_of_isPullback B S hS (cmp q) (hlift q) (hb q.1)
  have hcomp := Sheaf.isLocallySurjective_sigmaDesc_sigma_comp
    (fun q : Σ j, I j ↦
      pullback.snd (a q.1 q.2 ≫ pullback.snd (v q.1) f) (pullback.fst f g))
    lift hm hk
  simp only [hliftsnd] at hcomp
  exact isLocallySurjective_sigmaDesc_reindex B S hS
    (fun l : Σ q : Σ j, I j, K q.1 ↦ (⟨l.1.1, (l.1.2, l.2)⟩ : Σ j, I j × K j)) _ hcomp

/-- **Stacks 0GBD**, the covering of `X ×_Y Z` constructed in the source's proof: given a
covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and coverings `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` and
`{Wⱼₖ ⟶ Vⱼ ×_Y Z}` of the same type, the fibre products `Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form a covering of
`X ×_Y Z` as in Definition 0AIM, each member of which maps to `Z` through the affine formal
algebraic space `Wⱼₖ`, representable étale over `Z`.

This is every clause of condition (3) of Stacks 0ANG for `pr₂ : X ×_Y Z ⟶ Z` except the
property of the chart maps: that the chart fibre products are affine formal algebraic spaces
is Stacks 0AN3 clause (1) together with Stacks 0AJ7 for the chart `Vⱼ`, that they are
representable étale over `X ×_Y Z` is `isRepresentableEtale_chartPullbackMap`, that they
jointly cover `X ×_Y Z` is `isLocallySurjective_sigmaDesc_chartPullbackMap`, and that they map
to `Z` through `Wⱼₖ` is `chartPullbackMap_comp_snd`. -/
theorem exists_affineEtaleCover_chartFactorization_pullback_snd
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    {J : Type (u + 1)} (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y)
    (hV : IsAffineEtaleCover B S hS V v)
    {I : J → Type (u + 1)} (U : ∀ j, I j → FppfSheaf B S hS)
    (a : ∀ j i, U j i ⟶ pullback (v j) f) (hU : ∀ j, IsAffineEtaleCover B S hS (U j) (a j))
    {K : J → Type (u + 1)} (W : ∀ j, K j → FppfSheaf B S hS)
    (b : ∀ j k, W j k ⟶ pullback (v j) g) (hW : ∀ j, IsAffineEtaleCover B S hS (W j) (b j)) :
    ∃ (Λ : Type (u + 1)) (T N : Λ → FppfSheaf B S hS) (c : ∀ l, T l ⟶ pullback f g)
      (t : ∀ l, T l ⟶ N l) (w : ∀ l, N l ⟶ Z),
      IsAffineEtaleCover B S hS T c ∧ (∀ l, IsAffineFormalAlgebraicSpace B S hS (N l)) ∧
        (∀ l, IsRepresentableEtale B S hS (w l)) ∧
          ∀ l, c l ≫ pullback.snd f g = t l ≫ w l := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨Σ j, I j × K j, fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ W p.1 p.2.2,
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ pullback.snd (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ b p.1 p.2.2 ≫ pullback.snd (v p.1) g,
    ⟨fun p ↦ ?_, fun p ↦ ?_,
      isLocallySurjective_sigmaDesc_chartPullbackMap B S hS f g v hV.2.2 a
        (fun j ↦ (hU j).2.2) b fun j ↦ (hW j).2.2⟩,
    fun p ↦ (hW p.1).1 p.2.2, fun p ↦ ?_, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hV.1 p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hV.1 p.1))
      ((hU p.1).1 p.2.1) ((hW p.1).1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hV.2.1 p.1) ((hU p.1).2.1 p.2.1) ((hW p.1).2.1 p.2.2)
  · exact IsRepresentableEtale.comp B S hS ((hW p.1).2.1 p.2.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) g (hV.2.1 p.1))
  · exact chartPullbackMap_comp_snd B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2)

end AlgebraicGeometry.FormalSpace

end
