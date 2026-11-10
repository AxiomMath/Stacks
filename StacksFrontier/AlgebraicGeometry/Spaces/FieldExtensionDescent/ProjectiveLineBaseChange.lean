module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.CoordinateProjection

/-!
# The base change of a power of the projective line along a field extension

The contraction step of [Stacks, Tag 0AEM] is run over the algebraic closure of the ground field
and its conclusion is carried back by
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_algebraicClosure`, whose
hypothesis speaks of the *base change* `j^{-1}((ℙ¹_k)^I)` of the power of the projective line
over `k`, not of the power `(ℙ¹_{k̄})^I` over the algebraic closure. This file identifies the
two, compatibly with the coordinate projections, so that a statement proved over `k̄` about the
latter is a statement about the former.

For one factor the identification is the universal property of the cartesian square

```
ℙ¹_K ---> ℙ¹_k
 |          |
 v          v
Spec K --> Spec k
```

(`AlgebraicGeometry.isPullback_projectiveSpaceFieldExtensionMap`): a `T`-point of `ℙ¹_K` over
`Spec K` is the same datum as a `T`-point of `ℙ¹_k` over `Spec k`, for `T` a scheme over
`Spec K`. The comparison in that direction — compose with `ℙ¹_K ⟶ ℙ¹_k` — is manifestly natural,
and it is bijective in each degree by the universal property, so it is an isomorphism of
presheaves.

For a power the identification is the product comparison of the base-change functor, which
preserves limits (`CategoryTheory.OverShriek.preservesLimits_relocalizeRestrict`), composed with
the single-factor identification in each coordinate. Compatibility with the coordinate
projections is then immediate: both sides read coordinate `i` as the base change of the `i`-th
projection followed by the single-factor comparison.

## Main definitions

* `AlgebraicGeometry.Space.projectiveLineFieldExtensionIso`: **the base change of the projective
  line over `k` is the projective line over `K`.**
* `AlgebraicGeometry.Space.projectiveLinePowerFieldExtensionIso`: the same for a power.

## Main results

* `AlgebraicGeometry.Space.projectiveLinePowerFieldExtensionIso_hom_comp_π`: the identification
  reads coordinates as the base change of the coordinate projections.
* `AlgebraicGeometry.Space.relocalizeRestrict_map_coordinateProjection`: **the identification is
  compatible with the coordinate projections onto a finite subset of the coordinates.**

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K] [Algebra k K]
  (hk : B.Contains (Spec (CommRingCat.of k)))
  (hK : B.Contains (Spec (CommRingCat.of K)))

/-! ### One factor -/

/-- The cartesian square exhibiting `ℙ¹_K` as the base change of `ℙ¹_k`, with the structure
morphisms written as such. -/
theorem projectiveLineFieldExtensionStructureMorphism :
    projectiveSpaceFieldExtensionMap k K 1 ≫
        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
      (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘ Spec (CommRingCat.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  (isPullback_projectiveSpaceFieldExtensionMap k K 1).w

variable {B k K hk hK}

/-- A `T`-point of `ℙ¹_K` over `Spec K`, composed with the projection to `ℙ¹_k`, lies over the
structure morphism of `T` read over `Spec k`. -/
theorem projectiveLineFieldExtensionToFun_w
    {T : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ}
    (v : (Over.post (X := B.obj hK) B.inclusion).obj T.unop ⟶
      Over.mk (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘ Spec (CommRingCat.of K))) :
    (v.left ≫ projectiveSpaceFieldExtensionMap k K 1) ≫
        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
      B.inclusion.map (T.unop.hom ≫ fieldExtensionMap B k K hk hK) := by
  have hw : v.left ≫ (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘
      Spec (CommRingCat.of K)) = B.inclusion.map T.unop.hom := Over.w v
  rw [B.inclusion.map_comp, map_fieldExtensionMap, ← hw, Category.assoc,
    projectiveLineFieldExtensionStructureMorphism]
  exact (Category.assoc _ _ _).symm

/-- A `T`-point of `ℙ¹_k` over `Spec k`, for `T` a scheme over `Spec K`, and the structure
morphism of `T` agree over `Spec k`, which is what the universal property of the cartesian
square consumes. -/
theorem projectiveLineFieldExtensionInvFun_comm
    {T : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ}
    (u : (Over.post (X := B.obj hk) B.inclusion).obj
        ((Over.map (fieldExtensionMap B k K hk hK)).obj T.unop) ⟶
      Over.mk (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) :
    u.left ≫ (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
      B.inclusion.map T.unop.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  have hu : u.left ≫ (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
      Spec (CommRingCat.of k)) =
    B.inclusion.map (T.unop.hom ≫ fieldExtensionMap B k K hk hK) := Over.w u
  rwa [B.inclusion.map_comp, map_fieldExtensionMap] at hu

/-- The point of `ℙ¹_K` the universal property produces lies over the structure morphism
of `T`. -/
theorem projectiveLineFieldExtensionInvFun_w
    {T : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ}
    (u : (Over.post (X := B.obj hk) B.inclusion).obj
        ((Over.map (fieldExtensionMap B k K hk hK)).obj T.unop) ⟶
      Over.mk (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) :
    (isPullback_projectiveSpaceFieldExtensionMap k K 1).lift u.left
          (B.inclusion.map T.unop.hom) (projectiveLineFieldExtensionInvFun_comm u) ≫
        (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘ Spec (CommRingCat.of K)) =
      B.inclusion.map T.unop.hom :=
  (isPullback_projectiveSpaceFieldExtensionMap k K 1).lift_snd _ _ _

variable (B k K hk hK)

/-- **The sections of the projective line over `K` are the sections of the base change of the
projective line over `k`**, at every object of the big fppf site over `Spec K`: a `T`-point of
`ℙ¹_K` over `Spec K` is the same datum as a `T`-point of `ℙ¹_k` over `Spec k`, by the universal
property of the cartesian square exhibiting `ℙ¹_K` as the base change of `ℙ¹_k`. -/
def projectiveLineFieldExtensionEquiv (T : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ) :
    ((Over.post (X := B.obj hK) B.inclusion).obj T.unop ⟶
        Over.mk (projectiveSpaceOverRing 1 (CommRingCat.of K) ↘ Spec (CommRingCat.of K))) ≃
      ((Over.post (X := B.obj hk) B.inclusion).obj
          ((Over.map (fieldExtensionMap B k K hk hK)).obj T.unop) ⟶
        Over.mk (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) where
  toFun v := Over.homMk (v.left ≫ projectiveSpaceFieldExtensionMap k K 1)
    (projectiveLineFieldExtensionToFun_w v)
  invFun u := Over.homMk ((isPullback_projectiveSpaceFieldExtensionMap k K 1).lift u.left
    (B.inclusion.map T.unop.hom) (projectiveLineFieldExtensionInvFun_comm u))
    (projectiveLineFieldExtensionInvFun_w u)
  left_inv v := Over.OverMorphism.ext <|
    (isPullback_projectiveSpaceFieldExtensionMap k K 1).hom_ext
      ((isPullback_projectiveSpaceFieldExtensionMap k K 1).lift_fst _ _ _)
      (((isPullback_projectiveSpaceFieldExtensionMap k K 1).lift_snd _ _ _).trans (Over.w v).symm)
  right_inv _ := Over.OverMorphism.ext <|
    (isPullback_projectiveSpaceFieldExtensionMap k K 1).lift_fst _ _ _

/-- **The base change of the projective line over `k` along a field extension is the projective
line over `K`.** The identification is the universal property of the cartesian square exhibiting
`ℙ¹_K` as the base change of `ℙ¹_k`, read on sections; naturality holds because both sides
restrict a section along the same morphism of schemes. -/
def projectiveLineFieldExtensionIso :
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj
        (projectiveLineFunctor k B hk) ≅
      projectiveLineFunctor K B hK :=
  (NatIso.ofComponents
    (fun T => Equiv.toIso (projectiveLineFieldExtensionEquiv B k K hk hK T))
    (by
      intro T T' m
      ext v
      exact Over.OverMorphism.ext (Category.assoc _ _ _))).symm

/-! ### A power -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the products of presheaves on the big fppf site and their preservation
/-- **The base change of a power of the projective line over `k` along a field extension is the
corresponding power of the projective line over `K`**: base change preserves limits, so it
carries a product to the product of the base changes, and each factor is identified by
`AlgebraicGeometry.Space.projectiveLineFieldExtensionIso`. -/
def projectiveLinePowerFieldExtensionIso (α : Type v) [Small.{u} α] :
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).obj
        (projectiveLinePower k B hk α) ≅
      projectiveLinePower K B hK α :=
  PreservesProduct.iso (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK))
      (fun _ : α => projectiveLineFunctor k B hk) ≪≫
    Pi.mapIso fun _ : α => projectiveLineFieldExtensionIso B k K hk hK

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the products of presheaves on the big fppf site and their preservation
/-- The identification of the base change of a power of the projective line reads the coordinate
`a` as the base change of the `a`-th coordinate projection followed by the single-factor
identification. -/
theorem projectiveLinePowerFieldExtensionIso_hom_comp_π (α : Type v) [Small.{u} α] (a : α) :
    (projectiveLinePowerFieldExtensionIso B k K hk hK α).hom ≫
        Pi.π (fun _ : α => projectiveLineFunctor K B hK) a =
      (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map
          (Pi.π (fun _ : α => projectiveLineFunctor k B hk) a) ≫
        (projectiveLineFieldExtensionIso B k K hk hK).hom := by
  rw [projectiveLinePowerFieldExtensionIso, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the products of presheaves on the big fppf site and their preservation
/-- **The identification of the base change of a power of the projective line is compatible with
the coordinate projection onto a finite subset of the coordinates.** -/
theorem relocalizeRestrict_map_coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map
          (coordinateProjection k B hk n I) ≫
        (projectiveLinePowerFieldExtensionIso B k K hk hK I).hom =
      (projectiveLinePowerFieldExtensionIso B k K hk hK (Fin n)).hom ≫
        coordinateProjection K B hK n I := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Category.assoc, projectiveLinePowerFieldExtensionIso_hom_comp_π, ← Category.assoc,
    ← (OverShriek.relocalizeRestrict (fieldExtensionMap B k K hk hK)).map_comp,
    Pi.map'_comp_π, Category.comp_id, Category.assoc, Pi.map'_comp_π, Category.comp_id,
    projectiveLinePowerFieldExtensionIso_hom_comp_π]

end AlgebraicGeometry.Space

end
