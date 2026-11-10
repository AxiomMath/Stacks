module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellation

/-!
# Cancellation of a representable étale factor

Let `S` be a scheme contained in a big fppf site `B`. If `q : W ⟶ X` and `k ≫ q` are morphisms
of fppf sheaves over `S` which are representable by algebraic spaces and étale, then so is `k`
(the form of Stacks 05W3 for fppf sheaves). The case of an affine formal algebraic space `W` is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp`; here `W` is arbitrary.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_pullback_diagonal`: the relative
  diagonal of a morphism representable by algebraic spaces is representable by algebraic spaces
  (Stacks 05LA), with values in `Type (max w u)`.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp'`: the cancellation.

## Implementation notes

The diagonal statement is the proof of
`Space.relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpaces`
read with universe-lifted scheme-valued points: the base change of the diagonal along a point
`(α, β)` of `F ×_G F` over `U` is the locus where the two sections `α`, `β` of the algebraic space
`U ×_G F` over `U` agree, the pullback of its diagonal along `(α, β)`.

## References

* [Stacks Project, Tag 05LA](https://stacks.math.columbia.edu/tag/05LA)
* [Stacks Project, Tag 05W3](https://stacks.math.columbia.edu/tag/05W3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 05LA, universe-lifted.** The relative diagonal of a morphism of presheaves which is
representable by algebraic spaces is representable by objects of the site. -/
theorem relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpacesULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) :
    (uliftYoneda.{w} (C := BigFppfOver B S hS)).relativelyRepresentable
      (pullback.diagonal a) := by
  classical
  intro U ξ
  set α : (uliftYoneda.{w}).obj U ⟶ F := ξ ≫ pullback.fst a a with hα
  set β : (uliftYoneda.{w}).obj U ⟶ F := ξ ≫ pullback.snd a a with hβ
  have hαβ : α ≫ a = β ≫ a := by rw [hα, hβ, Category.assoc, Category.assoc, pullback.condition]
  set V := Limits.pullback (α ≫ a) a
  have hV : IsAlgebraicSpaceULift.{w} B S hS V := ha U (α ≫ a)
  set j₁ : (uliftYoneda.{w}).obj U ⟶ V := pullback.lift (𝟙 _) α (Category.id_comp _)
  set j₂ : (uliftYoneda.{w}).obj U ⟶ V :=
    pullback.lift (𝟙 _) β ((Category.id_comp _).trans hαβ)
  have hj₁snd : j₁ ≫ pullback.snd (α ≫ a) a = α := pullback.lift_snd _ _ _
  have hj₂snd : j₂ ≫ pullback.snd (α ≫ a) a = β := pullback.lift_snd _ _ _
  have hj₁fst : j₁ ≫ pullback.fst (α ≫ a) a = 𝟙 _ := pullback.lift_fst _ _ _
  have hj₂fst : j₂ ≫ pullback.fst (α ≫ a) a = 𝟙 _ := pullback.lift_fst _ _ _
  obtain ⟨W, w', fst, hpb⟩ := hV.diagonal_representable (prod.lift j₁ j₂)
  have hcomp₁ : fst = (uliftYoneda.{w}).map w' ≫ j₁ := by
    simpa [diag] using congrArg (· ≫ Limits.prod.fst) hpb.w
  have hcomp₂ : fst = (uliftYoneda.{w}).map w' ≫ j₂ := by
    simpa [diag] using congrArg (· ≫ Limits.prod.snd) hpb.w
  have hwαβ : (uliftYoneda.{w}).map w' ≫ α = (uliftYoneda.{w}).map w' ≫ β :=
    calc _ = fst ≫ pullback.snd (α ≫ a) a := by rw [hcomp₁, Category.assoc, hj₁snd]
      _ = _ := by rw [hcomp₂, Category.assoc, hj₂snd]
  have hsqw : ((uliftYoneda.{w}).map w' ≫ α) ≫ pullback.diagonal a =
      (uliftYoneda.{w}).map w' ≫ ξ :=
    pullback.hom_ext (by simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hα])
      (by simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hwαβ, hβ])
  have key : ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)) (t₁ : T ⟶ F)
      (t₂ : T ⟶ (uliftYoneda.{w}).obj U),
      t₁ ≫ pullback.diagonal a = t₂ ≫ ξ → t₁ = t₂ ≫ α ∧ t₂ ≫ j₁ = t₂ ≫ j₂ := by
    intro T t₁ t₂ hcond
    have h₁ : t₁ = t₂ ≫ α := by simpa [hα] using congrArg (· ≫ pullback.fst a a) hcond
    have h₂ : t₁ = t₂ ≫ β := by simpa [hβ] using congrArg (· ≫ pullback.snd a a) hcond
    exact ⟨h₁, pullback.hom_ext (by simp only [Category.assoc, hj₁fst, hj₂fst])
      (by simp only [Category.assoc, hj₁snd, hj₂snd, ← h₁, h₂])⟩
  have hsq : IsPullback ((uliftYoneda.{w}).map w' ≫ α) ((uliftYoneda.{w}).map w')
      (pullback.diagonal a) ξ := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsqw
      (fun s => hpb.lift (s.snd ≫ j₁) s.snd ?_) ?_ (fun s => hpb.lift_snd _ _ _) ?_)
    · obtain ⟨-, hj⟩ := key s.pt s.fst s.snd s.condition
      exact prod.hom_ext (by simp only [Category.assoc, diag, prod.lift_fst, Category.comp_id])
        (by simp only [Category.assoc, diag, prod.lift_snd, Category.comp_id, hj])
    · intro s
      rw [← Category.assoc, hpb.lift_snd, (key s.pt s.fst s.snd s.condition).1]
    · intro s m _ hm₂
      have hL : m ≫ fst = s.snd ≫ j₁ := by rw [hcomp₁, ← Category.assoc, hm₂]
      exact hpb.hom_ext (hL.trans (hpb.lift_fst _ _ _).symm) (hm₂.trans (hpb.lift_snd _ _ _).symm)
  exact ⟨W, w', (uliftYoneda.{w}).map w' ≫ α, hsq⟩

/-- **Stacks 05LA, universe-lifted.** The relative diagonal of a morphism of presheaves which is
representable by algebraic spaces is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpacesULift_pullback_diagonal
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS (pullback.diagonal a) := by
  intro U ξ
  obtain ⟨W, snd, fst, hpb⟩ :=
    relativelyRepresentable_pullback_diagonal_of_isRepresentableByAlgebraicSpacesULift a ha ξ
  exact isAlgebraicSpaceULift_of_iso B S hS
    hpb.flip.isoPullback (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS W)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Cancellation of a representable étale factor** (Stacks 05W3 for fppf sheaves). Let
`k : U ⟶ W` and `q : W ⟶ X` be morphisms of fppf sheaves over `S`. If `q` and `k ≫ q` are
representable by algebraic spaces and étale, then so is `k`.

Representability is Stacks 0AMN, the relative diagonal of `q` being representable by Stacks
05LA (`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_pullback_diagonal`); the
étaleness is the argument of `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp`, by
Stacks 03FV along the section of `T ×_X W ⟶ T` given by a point `T ⟶ W`. -/
theorem isRepresentableEtale_of_comp' {U W X : FppfSheaf B S hS} (k : U ⟶ W) (q : W ⟶ X)
    (hq : IsRepresentableEtale B S hS q)
    (hkq : IsRepresentableEtale B S hS (k ≫ q)) : IsRepresentableEtale B S hS k := by
  obtain ⟨hkqrep, hkqet⟩ := hkq
  obtain ⟨hqrep, hqet⟩ := hq
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS k.hom :=
    Space.isRepresentableByAlgebraicSpacesULift_of_comp B S hS k.hom q.hom
      (Space.isRepresentableByAlgebraicSpacesULift_pullback_diagonal q.hom hqrep) hkqrep
  refine ⟨hrep, fun T ξ => ?_⟩
  dsimp only [ObjectProperty.homMk]
  let ξq := ξ ≫ q.hom
  let a := k.hom ≫ q.hom
  have hP1 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξq a) := hkqrep T ξq
  have hP2 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξq q.hom) := hqrep T ξq
  have hT := Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T
  let m : pullback ξq a ⟶ pullback ξq q.hom :=
    pullback.lift (pullback.fst ξq a) (pullback.snd ξq a ≫ k.hom)
      (by rw [pullback.condition]; simp [a])
  have hm1 : m ≫ pullback.fst ξq q.hom = pullback.fst ξq a := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd ξq q.hom = pullback.snd ξq a ≫ k.hom := pullback.lift_snd _ _ _
  have hmet : Space.IsEtaleULift.{u + 1} B S hS m :=
    Space.isEtaleULift_of_comp B S hS hP1 hP2 hT m (pullback.fst ξq q.hom)
      (by rw [hm1]; exact hkqet T ξq) (hqet T ξq)
  let σ : (uliftYoneda.{u + 1}).obj T ⟶ pullback ξq q.hom :=
    pullback.lift (𝟙 _) ξ (by simp [ξq])
  let j : pullback ξ k.hom ⟶ pullback ξq a :=
    pullback.lift (pullback.fst ξ k.hom) (pullback.snd ξ k.hom)
      (by simp only [ξq, a, ← Category.assoc, pullback.condition])
  have hR : IsPullback (pullback.snd ξq a) m k.hom (pullback.snd ξq q.hom) := by
    refine IsPullback.of_bot ?_ hm2.symm (IsPullback.of_hasPullback ξq q.hom).flip
    rw [hm1]
    exact (IsPullback.of_hasPullback ξq a).flip
  have hL : IsPullback j (pullback.fst ξ k.hom) m σ := by
    refine IsPullback.of_right ?_ ?_ hR
    · have h1 : j ≫ pullback.snd ξq a = pullback.snd ξ k.hom := pullback.lift_snd _ _ _
      have h2 : σ ≫ pullback.snd ξq q.hom = ξ := pullback.lift_snd _ _ _
      rw [h1, h2]
      exact (IsPullback.of_hasPullback ξ k.hom).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, Category.assoc]
        change pullback.lift _ _ _ ≫ pullback.fst ξq a =
          pullback.fst ξ k.hom ≫ pullback.lift _ _ _ ≫ pullback.fst ξq q.hom
        rw [pullback.lift_fst, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, hm2, Category.assoc]
        change (pullback.lift _ _ _ ≫ pullback.snd ξq a) ≫ k.hom =
          pullback.fst ξ k.hom ≫ pullback.lift _ _ _ ≫ pullback.snd ξq q.hom
        rw [pullback.lift_snd, pullback.lift_snd, pullback.condition]
  exact Space.isEtaleULift_of_isPullback B S hS (hrep T ξ) hP1 hT hP2 hL hmet

end AlgebraicGeometry.FormalSpace

end
