module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRationalEquivalenceCanonicalSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.ProperPushforwardChow

/-!
# The cap product with a first Chern class on the Chow group of a good algebraic space

In Situation 0EDT let `X/B` be good and let `𝒩` be an invertible `𝒪_X`-module. The cap product
`c₁(𝒩) ∩ - : Z_{k+1}(X) → Z_k(X)` of Stacks 0EQJ, at the canonical choices, carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero (Stacks 0EQY), and so
induces

`c₁(𝒩) ∩ - : CH_{k+1}(X) → CH_k(X)`,

characterised by `c₁(𝒩) ∩ [α] = [c₁(𝒩) ∩ α]`.

The Chow group here is `AlgebraicGeometry.Space.chowGroup`. In the namespace
`AlgebraicGeometry.Space`, Stacks 0EQY is the theorem
`isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule` for the
reading `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical` of rational equivalence;
the two readings agree by `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_iff`, so
the statement and the induced homomorphism transfer to `AlgebraicGeometry.Space.chowGroup`,
compatibly with the identification `AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup` of
the two Chow groups.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChow.canonicalFirstChernCapChow`:
  `c₁(𝒩) ∩ - : CH_{k+1}(X) → CH_k(X)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChow.isRationallyEquivalentToZero_firstChernCapCycleMap`:
  Stacks 0EQY for cycles rationally equivalent to zero.
* `AlgebraicGeometry.Space.PrivateChow.rationallyEquivalent_firstChernCapCycleMap`: the cap
  products of rationally equivalent cycles are rationally equivalent.
* `AlgebraicGeometry.Space.PrivateChow.canonicalFirstChernCapChow_chowClass`:
  `c₁(𝒩) ∩ [α] = [c₁(𝒩) ∩ α]`.
* `PrivateChow.chowGroupCanonicalEquivChowGroup_canonicalFirstChernCapCanonicalChowMap`:
  the homomorphism commutes with the identification of the two Chow groups.
* `AlgebraicGeometry.Space.PrivateChern.respectsRationalEquivalence_firstChernCapCycleMap` and
  `AlgebraicGeometry.Space.PrivateChern.chowDescend_firstChernCapCycleMap`: the same in the form
  of `AlgebraicGeometry.Space.PrivateChern.chowDescend`.

## References

* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

/- Stacks 0EQY is proved for the canonical reading of rational equivalence in
`FirstChernCapRationalEquivalenceCanonicalSummand.lean`, by
`isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule` and
`canonicalFirstChernCapCanonicalChowMap`. Nothing new about the cap product is proved here: this
file only transfers that statement, and the homomorphism it induces, to `chowGroup`, along the
comparison of the two readings of rational equivalence set up in `ProperPushforwardChow.lean`. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace PrivateChow

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQY, for cycles rationally equivalent to zero.** If `α ∈ Z_{k+1}(X)` is rationally
equivalent to zero, so is `c₁(𝒩) ∩ α ∈ Z_k(X)`, the cap product being that of Stacks 0EQJ at the
canonical choices. -/
theorem isRationallyEquivalentToZero_firstChernCapCycleMap (k : ℤ)
    {α : CycleGroup D sX (k + 1)}
    (hα : IsRationallyEquivalentToZero.{u + 1} D sX hX (k + 1) α) :
    IsRationallyEquivalentToZero.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α) :=
  (isRationallyEquivalentToZeroCanonical_iff.{u + 1} D sX hX k _).1
    (isRationallyEquivalentToZeroCanonical_firstChernCapCycleMap_canonicalFirstChernRule D sX hX
      k N hN ((isRationallyEquivalentToZeroCanonical_iff.{u + 1} D sX hX (k + 1) α).2 hα))

/-- **Stacks 0EQY.** The cap products with `c₁(𝒩)` of two rationally equivalent cycles are
rationally equivalent. -/
theorem rationallyEquivalent_firstChernCapCycleMap (k : ℤ) {α β : CycleGroup D sX (k + 1)}
    (h : RationallyEquivalent.{u + 1} D sX hX (k + 1) α β) :
    RationallyEquivalent.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α)
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) β) := by
  have h' := isRationallyEquivalentToZero_firstChernCapCycleMap D sX hX N hN k h
  rwa [map_sub] at h'

/-- The subgroup of cycles rationally equivalent to zero is carried into itself by the cap
product with `c₁(𝒩)`. -/
theorem rationalEquivalences_le_comap_firstChernCapCycleMap (k : ℤ) :
    rationalEquivalences.{u + 1} D sX hX (k + 1) ≤
      (rationalEquivalences.{u + 1} D sX hX k).comap
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)) :=
  fun _ hα => isRationallyEquivalentToZero_firstChernCapCycleMap D sX hX N hN k hα

/-- **The cap product with a first Chern class on Chow groups**,
`c₁(𝒩) ∩ - : CH_{k+1}(X) → CH_k(X)`: the homomorphism induced by the cap product of Stacks 0EQJ
at the canonical choices, which preserves rational equivalence by Stacks 0EQY. -/
def canonicalFirstChernCapChow (k : ℤ) :
    chowGroup.{u + 1} D sX hX (k + 1) →+ chowGroup.{u + 1} D sX hX k :=
  QuotientAddGroup.map _ _
    (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k))
    (rationalEquivalences_le_comap_firstChernCapCycleMap D sX hX N hN k)

/-- `c₁(𝒩) ∩ [α] = [c₁(𝒩) ∩ α]`. -/
@[simp]
theorem canonicalFirstChernCapChow_chowClass (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapChow D sX hX N hN k (chowClass.{u + 1} D sX hX (k + 1) α) =
      chowClass.{u + 1} D sX hX k
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k) α) :=
  rfl

/-- On classes of cycles the homomorphism is the cap product of Stacks 0EQJ into `CH_k(X)` at the
canonical choices, `AlgebraicGeometry.Space.canonicalFirstChernCap`. -/
theorem canonicalFirstChernCapChow_comp_chowClass (k : ℤ) :
    (canonicalFirstChernCapChow D sX hX N hN k).comp (chowClass.{u + 1} D sX hX (k + 1)) =
      canonicalFirstChernCap.{u, u + 1} D sX hX N hN k :=
  rfl

/-- The homomorphism commutes with the identification of the Chow group at the canonical
embeddings with `AlgebraicGeometry.Space.chowGroup`: it is the base's
`AlgebraicGeometry.Space.canonicalFirstChernCapCanonicalChowMap` read through
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
theorem chowGroupCanonicalEquivChowGroup_canonicalFirstChernCapCanonicalChowMap (k : ℤ)
    (x : chowGroupCanonical.{u + 1} D sX hX (k + 1)) :
    chowGroupCanonicalEquivChowGroup.{u + 1} D sX hX k
        (canonicalFirstChernCapCanonicalChowMap D sX hX k N hN x) =
      canonicalFirstChernCapChow D sX hX N hN k
        (chowGroupCanonicalEquivChowGroup.{u + 1} D sX hX (k + 1) x) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalencesCanonical.{u + 1} D sX hX (k + 1)) x
  rfl

end PrivateChow

namespace PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQY**, in the form `AlgebraicGeometry.Space.PrivateChern.chowDescend` takes as its
hypothesis: the cap product with `c₁(𝒩)` respects rational equivalence. -/
theorem respectsRationalEquivalence_firstChernCapCycleMap (k : ℤ) :
    RespectsRationalEquivalence.{u, u + 1} D sX hX sX hX
      (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)) :=
  PrivateChow.rationalEquivalences_le_comap_firstChernCapCycleMap D sX hX N hN k

/-- The homomorphism of Chow groups that `AlgebraicGeometry.Space.PrivateChern.chowDescend`
induces from the cap product with `c₁(𝒩)` is
`AlgebraicGeometry.Space.PrivateChow.canonicalFirstChernCapChow`. -/
theorem chowDescend_firstChernCapCycleMap (k : ℤ) :
    chowDescend.{u, u + 1} D sX hX sX hX
        (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k)) =
      PrivateChow.canonicalFirstChernCapChow D sX hX N hN k := by
  rw [chowDescend, dite_eq_left (respectsRationalEquivalence_firstChernCapCycleMap D sX hX N hN k)]
  rfl

end PrivateChern

end AlgebraicGeometry.Space

end
