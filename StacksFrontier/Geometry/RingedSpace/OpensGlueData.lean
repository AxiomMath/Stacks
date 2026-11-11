module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Glueing data of locally ringed spaces along open subspaces

This file records the notion of glueing data of Stacks, Schemes, Section 01JA, in the form
given there: a family of locally ringed spaces `X i`, open subspaces `U i j ⊆ X i` with
`U i i = X i`, and isomorphisms of locally ringed spaces `φ i j : U i j ≅ U j i` such that for
every triple `i, j, k`

1. `φ i j ⁻¹ (U j i ∩ U j k) = U i j ∩ U i k`, and
2. the triangle `φ j k ∘ φ i j = φ i k` of morphisms `U i j ∩ U i k ⟶ U k i ∩ U k j` commutes.

It also proves the consequence noted in the section, that `φ i i` is the identity.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.OpensGlueData`: glueing data of locally ringed spaces
  along open subspaces.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.OpensGlueData.φ_self`: the isomorphism `φ i i` is the
  identity of `X i`.

## Implementation notes

The open subspace `U i j` of `X i` is the locally ringed space `(X i).restrict` along the open
embedding of `U i j`, and its inclusion into `X i` is `(X i).ofRestrict _`. The domain of the
triangle in (2), the open subspace `U i j ∩ U i k` of `U i j`, is the restriction of `U i j` to
the preimage of `U i k` under the inclusion of `U i j`.

The two edges of the triangle out of `U i j ∩ U i k` are restrictions of `φ i j` and `φ i k`;
the first exists because of (1). Field `cocycle` states (2) by asking for these restrictions: a
morphism `ψ` into `U j k` through which the inclusion of `U i j ∩ U i k` followed by `φ i j`
factors, a morphism `ρ` into `U i k` through which the inclusion of `U i j ∩ U i k` into `X i`
factors, and the equality of the two composites `ψ ≫ φ j k` and `ρ ≫ φ i k` after the inclusion
into `X k`. The inclusions of open subspaces are monomorphisms, so `ψ` and `ρ` are the unique
such restrictions and the equality after the inclusion into `X k` is the equality of the two
edges as morphisms into `U k i ∩ U k j`; that is, `cocycle` is condition (2) as stated.

Mathlib's `AlgebraicGeometry.LocallyRingedSpace.GlueData` encodes the same data with abstract
open immersions `V i j ⟶ U i` and a cocycle stated on fibre products; this file keeps the
formulation of the Stacks Project.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Stacks 01JA.** A glueing data of locally ringed spaces: an index type `ι`, locally ringed
spaces `X i`, open subspaces `U i j ⊆ X i` with `U i i = X i`, and isomorphisms of locally ringed
spaces `φ i j : U i j ≅ U j i` such that for all `i, j, k`

* (1) `φ i j ⁻¹ (U j i ∩ U j k) = U i j ∩ U i k` (field `preimage_iff`, pointwise: a point of
  `U i j` is sent by `φ i j` into `U j k` if and only if it lies in `U i k`), and
* (2) the restrictions of `φ i j`, `φ j k` and `φ i k` to `U i j ∩ U i k`, `U j i ∩ U j k` and
  `U i j ∩ U i k` satisfy `φ j k ∘ φ i j = φ i k` (field `cocycle`, see the implementation notes
  of this file). -/
@[stacks 01JA "glueing data of locally ringed spaces, conditions (1) and (2); `φ_self` is φᵢᵢ = id"]
structure OpensGlueData where
  /-- The index set. -/
  ι : Type v
  /-- The locally ringed spaces to be glued. -/
  X : ι → LocallyRingedSpace.{u}
  /-- The open subspace `U i j` of `X i`. -/
  U : ∀ i, ι → Opens (X i).toTopCat
  /-- `U i i` is all of `X i`. -/
  U_self : ∀ i, U i i = ⊤
  /-- The isomorphism `φ i j : U i j ≅ U j i` of locally ringed spaces. -/
  φ : ∀ i j, (X i).restrict (U i j).isOpenEmbedding ≅ (X j).restrict (U j i).isOpenEmbedding
  /-- Condition (1): `φ i j ⁻¹ (U j i ∩ U j k) = U i j ∩ U i k`. -/
  preimage_iff : ∀ i j k (x : (X i).restrict (U i j).isOpenEmbedding),
    ((X j).ofRestrict (U j i).isOpenEmbedding).base ((φ i j).hom.base x) ∈ U j k ↔
      ((X i).ofRestrict (U i j).isOpenEmbedding).base x ∈ U i k
  /-- Condition (2): on `U i j ∩ U i k` the restriction of `φ i j` followed by the restriction
  of `φ j k` equals the restriction of `φ i k`. -/
  cocycle : ∀ i j k,
    ∃ (ψ : ((X i).restrict (U i j).isOpenEmbedding).restrict
        ((Opens.map ((X i).ofRestrict (U i j).isOpenEmbedding).base).obj
          (U i k)).isOpenEmbedding ⟶ (X j).restrict (U j k).isOpenEmbedding)
      (ρ : ((X i).restrict (U i j).isOpenEmbedding).restrict
        ((Opens.map ((X i).ofRestrict (U i j).isOpenEmbedding).base).obj
          (U i k)).isOpenEmbedding ⟶ (X i).restrict (U i k).isOpenEmbedding),
      ψ ≫ (X j).ofRestrict (U j k).isOpenEmbedding =
          ((X i).restrict (U i j).isOpenEmbedding).ofRestrict
            ((Opens.map ((X i).ofRestrict (U i j).isOpenEmbedding).base).obj
              (U i k)).isOpenEmbedding ≫
            (φ i j).hom ≫ (X j).ofRestrict (U j i).isOpenEmbedding ∧
      ρ ≫ (X i).ofRestrict (U i k).isOpenEmbedding =
          ((X i).restrict (U i j).isOpenEmbedding).ofRestrict
            ((Opens.map ((X i).ofRestrict (U i j).isOpenEmbedding).base).obj
              (U i k)).isOpenEmbedding ≫
            (X i).ofRestrict (U i j).isOpenEmbedding ∧
      ψ ≫ (φ j k).hom ≫ (X k).ofRestrict (U k j).isOpenEmbedding =
        ρ ≫ (φ i k).hom ≫ (X k).ofRestrict (U k i).isOpenEmbedding

namespace OpensGlueData

variable (D : OpensGlueData.{v, u})

/-- **Stacks 01JA**, the remark of the section: the isomorphism `φ i i` of a glueing data is the
identity of `U i i = X i`. -/
theorem φ_self (i : D.ι) : (D.φ i i).hom = 𝟙 _ := by
  set Y := (D.X i).restrict (D.U i i).isOpenEmbedding
  set V := (Opens.map ((D.X i).ofRestrict (D.U i i).isOpenEmbedding).base).obj (D.U i i)
  set r := Y.ofRestrict V.isOpenEmbedding
  obtain ⟨ψ, ρ, hψ, hρ, h⟩ := D.cocycle i i i
  have hψ' : ψ = r ≫ (D.φ i i).hom := by
    rw [← cancel_mono ((D.X i).ofRestrict (D.U i i).isOpenEmbedding), hψ, Category.assoc]
  have hρ' : ρ = r := by
    rw [← cancel_mono ((D.X i).ofRestrict (D.U i i).isOpenEmbedding), hρ]
  have hr : IsIso r := by
    have : Epi r.base := by
      rw [TopCat.epi_iff_surjective]
      intro y
      refine ⟨⟨y, ?_⟩, rfl⟩
      change ((D.X i).ofRestrict (D.U i i).isOpenEmbedding).base y ∈ D.U i i
      exact y.2
    exact LocallyRingedSpace.IsOpenImmersion.to_iso r
  rw [hψ', hρ', Category.assoc] at h
  have h' : (D.φ i i).hom ≫ (D.φ i i).hom = (D.φ i i).hom := by
    rw [← cancel_epi r, ← cancel_mono ((D.X i).ofRestrict (D.U i i).isOpenEmbedding),
      Category.assoc, Category.assoc]
    exact h
  rw [← cancel_mono (D.φ i i).hom, h', Category.id_comp]

end OpensGlueData

end AlgebraicGeometry.LocallyRingedSpace

end
