module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Factoring through an open subspace, and base change of the isomorphism locus

Two facts used to compare blowups over an open subspace.

* `AlgebraicGeometry.Space.exists_factorization_of_range_pointsMap_subset`: a morphism of
  presheaves on the big fppf site into `F` factors through an open subspace `P ⊆ F` as soon as
  its points land in the points of `P`.  This generalizes
  `AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset` from the inclusion of a second
  subfunctor to an arbitrary morphism.
* `CategoryTheory.Subfunctor.isIso_fromPreimage_of_isPullback`: if the comparison map
  `U.fromPreimage b` of a subfunctor `U` along `b` is an isomorphism, so is the comparison map of
  the base-changed subfunctor along the base change of `b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Subfunctor

/-- **The isomorphism locus of a morphism is stable under base change.**  Let
```
      pX      f
  Y -----> X -----> A
  |                 ^
  pB                | b
  v                 |
  B' --------------->
```
be a pullback square `pX ≫ f = pB ≫ b` and let `U` be a subfunctor of `A` such that the
comparison map `U.fromPreimage b` — from the inverse image of `U` along `b` to `U` itself — is
an isomorphism. Then the comparison map for the base-changed subfunctor `U.preimage f` of `X`
along `pX` is again an isomorphism.

The proof builds the inverse directly from the universal property of the pullback square: a
point of the inverse image of `U.preimage f` along `pX` pushes forward, via `pX` then `f`, into
`U`, and because `pX ≫ f = pB ≫ b` it pushes forward via `pB` into the inverse image of `U` along
`b`, where `U.fromPreimage b` being an isomorphism identifies it with a point of `U`; lifting the
pair back along the pullback square recovers the point of `Y`. -/
theorem isIso_fromPreimage_of_isPullback {C : Type*} [Category C] {X Y A B' : C ⥤ Type u}
    {f : X ⟶ A} {b : B' ⟶ A} {pX : Y ⟶ X} {pB : Y ⟶ B'} (sq : IsPullback pX pB f b)
    (U : Subfunctor A) (hU : IsIso (U.fromPreimage b)) :
    IsIso ((U.preimage f).fromPreimage pX) := by
  have hrangeToP : range (((U.preimage f).preimage pX).ι ≫ pB) ≤ U.preimage b := by
    rw [range_comp, range_ι, image_le_iff, ← preimage_comp U pB b, ← sq.w,
      preimage_comp]
  have hcomm : (U.preimage f).fromPreimage pX ≫ U.fromPreimage f =
      lift _ hrangeToP ≫ U.fromPreimage b := by
    rw [← cancel_mono U.ι]
    simp [fromPreimage_ι, fromPreimage_ι_assoc, sq.w]
  have hk : (U.fromPreimage f ≫ inv (U.fromPreimage b) ≫ (U.preimage b).ι) ≫ b =
      (U.preimage f).ι ≫ f := by
    rw [Category.assoc, Category.assoc, ← fromPreimage_ι, IsIso.inv_hom_id_assoc, fromPreimage_ι]
  have hrange_r : range (sq.lift _ _ hk.symm) ≤ (U.preimage f).preimage pX := by
    rw [← image_le_iff, ← range_comp, sq.lift_fst, range_ι]
  have heq : (U.preimage f).fromPreimage pX ≫ sq.lift _ _ hk.symm =
      ((U.preimage f).preimage pX).ι := by
    refine sq.hom_ext (by simp [fromPreimage_ι]) ?_
    simp [reassoc_of% hcomm]
  refine ⟨lift _ hrange_r, ?_, ?_⟩
  · rw [← cancel_mono ((U.preimage f).preimage pX).ι]
    simp [heq]
  · rw [← cancel_mono (U.preimage f).ι]
    simp [fromPreimage_ι]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism factors through an open subspace of its target as soon as its points do.**
Generalizes `AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset` from the inclusion of a
second subfunctor to an arbitrary morphism `g`: the same base-change argument shows the first
projection of the pullback of `g` and the open immersion `P.ι` is an isomorphism, and its
inverse composed with the other leg is the sought factorization. -/
theorem exists_factorization_of_range_pointsMap_subset {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : A ⟶ F) {P : Subfunctor F} (hP : IsOpenSubspace B S hS P)
    (hsub : Set.range (pointsMap B S hS A g) ⊆
      Set.range (pointsMap B S hS P.toFunctor P.ι)) :
    ∃ h : A ⟶ P.toFunctor, h ≫ P.ι = g := by
  have hsq : IsPullback (pullback.fst g P.ι) (pullback.snd g P.ι) g P.ι :=
    IsPullback.of_hasPullback g P.ι
  have hfst : IsOpenImmersion B S hS (pullback.fst g P.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hP.2
  have hpsurj : Function.Surjective
      (pointsMap B S hS (pullback g P.ι) (pullback.fst g P.ι)) := by
    intro z
    obtain ⟨x, hx⟩ := hsub ⟨z, rfl⟩
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq z x hx.symm
    exact ⟨w, hw⟩
  have : IsIso (pullback.fst g P.ι) :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hfst
      (presheafSurjective_of_isSurjective B S hS _ hfst.rep hpsurj)
  refine ⟨inv (pullback.fst g P.ι) ≫ pullback.snd g P.ι, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
