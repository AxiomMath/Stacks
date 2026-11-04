module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Diagonal

/-!
# Étale charts of the finite part of a morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `U` be a scheme of
the big fppf site étale over `Y`, and let `Z ⊂ U ×_Y X` be an open subspace finite over `U`.
The pair `(U ⟶ Y, Z)` is a section of the finite part `(X/Y)_fin` over `U`, so it is a
morphism `U ⟶ (X/Y)_fin`, and that morphism is representable by schemes and étale.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_isEtale_comp_baseMap` — Stacks 04QE: a morphism from a
  scheme to the finite part whose composite with the projection to `Y` is étale is itself
  étale.

## Implementation notes

The section of `(X/Y)_fin` over `U` and the morphism `U ⟶ (X/Y)_fin` are the same datum by the
Yoneda lemma and the identification of sections of Stacks 04PD, so the hypothesis of the lemma
is phrased as the morphism `p` from the presheaf represented by `U`; the hypothesis that
`U ⟶ Y` is étale is that the composite of `p` with the projection of Stacks 04PI is étale.

The proof is the formal argument of the source: for a morphism `q` from a scheme `T` to the
finite part, the fibre product `T ×_{(X/Y)_fin} U` is the fibre product of `T ×_Y U` with the
diagonal of `(X/Y)_fin` over `Y`, hence an open subscheme of `T ×_Y U` by Stacks 04PK, and
`T ×_Y U ⟶ T` is étale because `U ⟶ Y` is.

Both "étale" and "open immersion" here are representability by schemes together with the
corresponding property of each represented base change, which is what
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along the structure functor of
the site expresses.

## References

* [Stacks Project, Tag 04QE](https://stacks.math.columbia.edu/tag/04QE)
* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

private theorem pullback_relativeDiagonal
    {C : Type v} [Category.{u} C] [HasPullbacks C]
    {W A B F Y K : C} {i : W ⟶ A} {j : W ⟶ B}
    {a : A ⟶ F} {b : B ⟶ F} {g : F ⟶ Y}
    {k₁ : K ⟶ A} {k₂ : K ⟶ B}
    (hW : IsPullback i j a b)
    (hK : IsPullback k₁ k₂ (a ≫ g) (b ≫ g))
    (m : W ⟶ K) (hm₁ : m ≫ k₁ = i) (hm₂ : m ≫ k₂ = j)
    (e : K ⟶ pullback g g)
    (he₁ : e ≫ pullback.fst g g = k₁ ≫ a)
    (he₂ : e ≫ pullback.snd g g = k₂ ≫ b) :
    IsPullback (i ≫ a) m (pullback.diagonal g) e := by
  have hsq : (i ≫ a) ≫ pullback.diagonal g = m ≫ e := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, he₁]
      rw [← hm₁, ← Category.assoc]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, he₂, hW.w]
      rw [← hm₂, ← Category.assoc]
  let lift : ∀ (s : PullbackCone (pullback.diagonal g) e), s.pt ⟶ W := fun s =>
    hW.lift (s.snd ≫ k₁) (s.snd ≫ k₂) (by
      calc
        (s.snd ≫ k₁) ≫ a = s.fst := by
          simpa [he₁] using (congrArg (· ≫ pullback.fst g g) s.condition).symm
        _ = (s.snd ≫ k₂) ≫ b := by
          simpa [he₂] using congrArg (· ≫ pullback.snd g g) s.condition)
  refine ⟨⟨hsq⟩, ⟨PullbackCone.IsLimit.mk hsq lift ?_ ?_ ?_⟩⟩
  · intro s
    simpa [lift, he₁, hm₁] using (congrArg (· ≫ pullback.fst g g) s.condition).symm
  · intro s
    apply hK.hom_ext <;> simp [hm₁, hm₂, lift]
  · intro s l hl₁ hl₂
    apply hW.hom_ext <;>
      simp only [← hm₁, ← hm₂, lift, IsPullback.lift_fst, IsPullback.lift_snd] <;>
      rw [← Category.assoc, hl₂]

/-- Open immersions of the big fppf site over `S`, i.e. morphisms whose underlying morphism of
schemes is an open immersion, are stable under base change. -/
private theorem isStableUnderBaseChange_inverseImage_isOpenImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  refine ⟨fun hpb hg => ?_⟩
  change AlgebraicGeometry.IsOpenImmersion (BigFppfOver.toScheme B S hS |>.map _) at hg
  show AlgebraicGeometry.IsOpenImmersion (BigFppfOver.toScheme B S hS |>.map _)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb.map _) hg

/-- **Stacks 04QE.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `U` be
a scheme of the big fppf site. A morphism from the presheaf represented by `U` to the finite
part `(X/Y)_fin` — equivalently, a morphism `U ⟶ Y` together with an open subspace of
`U ×_Y X` finite over `U` — is representable by schemes and étale as soon as its composite
with the projection `(X/Y)_fin ⟶ Y` is. -/
@[stacks 04QE]
theorem isEtale_of_isEtale_comp_baseMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : yoneda.obj U ⟶
      (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (hp : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf
        (p ≫ (finiteOpenSubspacePresheaf B S hS f).baseMap)) :
    (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf p := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let _ : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Q
  let Popen : MorphismProperty C :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) Q
  let F := (finiteOpenSubspacePresheaf B S hS f).toFunctor
  let g := (finiteOpenSubspacePresheaf B S hS f).baseMap
  let P' := p ≫ g
  have hbase : P.presheaf P' := hp
  have _ : Popen.IsStableUnderBaseChange :=
    isStableUnderBaseChange_inverseImage_isOpenImmersion B S hS
  have hrep : yoneda.relativelyRepresentable p :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
      (relativelyRepresentable_diag_finiteOpenSubspacePresheaf B S hS f) p
  have hresult : ∀ ⦃V : C⦄ (q : yoneda.obj V ⟶ F), P (hrep.snd q) := by
    intro V q
    let i := hrep.fst q
    let j := hrep.snd q
    have hW : IsPullback i (yoneda.map j) p q := hrep.isPullback q
    let k₁ := hbase.rep.fst (q ≫ g)
    let k₂ := hbase.rep.snd (q ≫ g)
    have hK : IsPullback k₁ (yoneda.map k₂) P' (q ≫ g) :=
      hbase.rep.isPullback (q ≫ g)
    have hcomm : i ≫ P' = yoneda.map j ≫ (q ≫ g) := by
      simpa [P', Category.assoc] using congrArg (· ≫ g) hW.w
    let m := hbase.rep.lift i j hcomm
    have hm₂ : m ≫ k₂ = j := hbase.rep.lift_snd i j hcomm
    have heCond : (k₁ ≫ p) ≫ g = (yoneda.map k₂ ≫ q) ≫ g := by
      simpa only [P', Category.assoc] using hK.w
    let e := pullback.lift (k₁ ≫ p) (yoneda.map k₂ ≫ q) heCond
    have hgraph : IsPullback (i ≫ p) (yoneda.map m)
        (pullback.diagonal g) e :=
      pullback_relativeDiagonal hW hK (yoneda.map m) (hbase.rep.lift_fst i j hcomm)
        (by rw [← Functor.map_comp, hm₂]) e
        (pullback.lift_fst _ _ heCond) (pullback.lift_snd _ _ heCond)
    have hmOpenPresheaf : Popen.presheaf (yoneda.map m) :=
      (MorphismProperty.relative_isStableUnderBaseChange Popen).of_isPullback
        hgraph (isOpenImmersion_diagonal_finiteOpenSubspacePresheaf B S hS f)
    have _ : AlgebraicGeometry.IsOpenImmersion (Q.map m) :=
      (MorphismProperty.relative_map_iff (F := yoneda) (P := Popen)).mp hmOpenPresheaf
    have _ : Etale (Q.map k₂) := hbase.property_snd (q ≫ g)
    have : P (m ≫ k₂) := by
      show Etale (Q.map (m ≫ k₂))
      rw [Q.map_comp]
      infer_instance
    rwa [hm₂] at this
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.relative_of_snd (F := yoneda) hrep hresult

end AlgebraicGeometry.Space

end
