module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethTruncationInline
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethUnbounded
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethBoundedComparison

/-!
# The relative Künneth map of the box product at a locally bounded complex

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes. This
file applies the truncation engine
`Stacks.Cohomology.BoxKunneth.isIso_of_isIso_stupidTrunc_of_inline` to
the relative Künneth map of [Stacks, Tag 0G4B]. The result: the map is invertible at a locally
bounded first complex with terms flat over `a^{-1}𝒪_S` as soon as it is invertible at the stupid
truncations `σ^{≤N}` of the two complexes, which have finitely many nonzero terms.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap_of_isIso_stupidTrunc`: **the
  reduction for the relative Künneth map `relativeBoxKunnethMap` of [Stacks, Tag 0G4B]**.
* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMapUnbounded_of_isIso_stupidTrunc`: the
  same for the Künneth map whose total complex is formed over `f^{-1}𝒪_S`, which the first is
  read through by `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap_iff`.

## Implementation notes

The naturality of the Künneth map in the two complexes, which is all that the engine consumes,
is `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMapUnbounded_natural_left` and `_right`. The
engine states the family and its two naturality conditions inline, as hypotheses, so these
lemmas are passed to it as they stand: both are elaborated at the same instance terms, and the
kernel meets no definition to unfold.

## References

* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry ComplexShape
open Stacks.DeRhamDirectImage Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]

/-- **The unbounded relative Künneth map is invertible at a locally bounded complex once it is at
the stupid truncations.** For `a`, `b` quasi-compact and quasi-separated, `F^•` locally bounded
with terms flat over `a^{-1}𝒪_S`, and both complexes strictly bounded below: if the map is
invertible at `(σ^{≤N}F^•, σ^{≤N}G^•)` for every `N`, it is invertible at `(F^•, G^•)`. -/
theorem isIso_relativeBoxKunnethMapUnbounded_of_isIso_stupidTrunc
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (hB : ∀ N : ℤ, IsIso (relativeBoxKunnethMapUnbounded a b (K.stupidTrunc (embeddingUpIntLE N))
      (L.stupidTrunc (embeddingUpIntLE N)))) :
    IsIso (relativeBoxKunnethMapUnbounded a b K L) :=
  isIso_of_isIso_stupidTrunc_of_inline (relativeBoxKunnethMapUnbounded a b)
    (relativeBoxKunnethMapUnbounded_natural_left a b)
    (relativeBoxKunnethMapUnbounded_natural_right a b) K L n₁ n₂ hK hKflat hB

/-- **The relative Künneth map of the box product is invertible at a locally bounded complex once
it is at the stupid truncations.** Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and
quasi-separated. Let `F^•` on `X/S` be locally bounded with terms flat over `a^{-1}𝒪_S`, and let
`F^•` and `G^•` be strictly bounded below by `n₁` and `n₂`. If

`Ra_*σ^{≤N}F^• ⊗^𝐋_{𝒪_S} Rb_*σ^{≤N}G^• ⟶ Rf_*Tot(σ^{≤N}F^• ⊠ σ^{≤N}G^•)`

is invertible for every `N`, then so is the map at `(F^•, G^•)`. The truncations have finitely
many nonzero terms. This is the passage from bounded to locally bounded complexes that
[Stacks, Tag 0FMC] needs over a base that is not quasi-compact. -/
theorem isIso_relativeBoxKunnethMap_of_isIso_stupidTrunc
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
    (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
    (hK : Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K))
    (hKflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i))
    (hB : ∀ N : ℤ, IsIso (relativeBoxKunnethMap a b (K.stupidTrunc (embeddingUpIntLE N))
      (L.stupidTrunc (embeddingUpIntLE N)) n₁ n₂)) :
    IsIso (relativeBoxKunnethMap a b K L n₁ n₂) :=
  (isIso_relativeBoxKunnethMap_iff a b K L n₁ n₂).2
    (isIso_relativeBoxKunnethMapUnbounded_of_isIso_stupidTrunc a b K L n₁ n₂ hK hKflat fun N =>
      (isIso_relativeBoxKunnethMap_iff a b _ _ n₁ n₂).1 (hB N))

end Stacks.Cohomology.BoxKunneth
