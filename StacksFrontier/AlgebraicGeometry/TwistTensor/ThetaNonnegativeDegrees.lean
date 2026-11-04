module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison

/-!
# Lemma 01O1's triangle is a condition on nonnegative degrees only

`StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison` proves the `θ`-assertion of
[Stacks, Tag 01O1] at the tag's own source `r^*(⨁_{n ∈ ℤ} 𝒪(nd))` over the degree-`d` locus, out
of the degree-one datum `α : r^*𝒪(d) ≅ ℒ` together with the commutativity of the characterising
triangle for the degreewise family `v`. That commutativity is stated there in **every integer
degree**, which is more than the tag's own data provides: the second leg of the tag's triangle is
the homogeneous-section map, and both spellings of it in this repository —
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ` and
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` — are indexed by `ℕ`.

**This file closes that index gap.** The negative homogeneous pieces of a graded `𝒪_S`-algebra of
Situation 01NN vanish, by the field `negative_isZero` of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`; the pullback functor on sheaves
of modules preserves zero morphisms, so it carries a zero module to a zero module; and a
morphism out of a zero module is unique. Hence in a negative degree the triangle commutes for
*every* degreewise family, and the commutativity in nonnegative degrees already implies the
commutativity in all of `ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.isZero_pullback_piece_mul_of_neg`: for a
  positive quadruple degree, the source of the second leg in a negative degree is a zero module.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen_of_nonneg`:
  **the `θ`-assertion from the triangle in nonnegative degrees alone.**
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.`
  `existsUnique_theta_of_degreeOpen_of_nonneg_situation`: the same for a quadruple over
  Situation 01NN's own algebra, where the vanishing hypothesis is discharged from that algebra's
  own field.

## Implementation notes

**The quadruple degree is required to be positive, and that is not a restriction at the tag.**
The vanishing argument needs `n * e < 0` for `n < 0`, hence `0 < e`. In Tag 01O1 the quadruple
degree *is* the positive `d` of the locus, so the hypothesis holds wherever the tag applies.
Against the statement of `existsUnique_theta_of_degreeOpen` this is a trade of `0 < e` for the
whole negative half of the triangle, which is why the forms below are the sharper ones for the
tag even though neither statement implies the other verbatim.

## What this file does not do

**The degree-one datum `α` and the triangle itself are still inputs, and this file produces
neither.** At the tag's own source they ask for the identification of the universal invertible
sheaf and the universal section map of a representation of `F_d` with `𝒪(d)|_{U_d}` and
`...RelativeProjTwists.TwistData.ψ`; the module docstring of
`StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison` records the obstruction to
that identification over a general base, and this file does not touch it. What is removed here is
one of the four discrepancies between the tag's data and the hypotheses of
`existsUnique_theta_of_degreeOpen`, namely the index set of the triangle.

The triangle itself is not an input everywhere: over an affine base
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_isAffine` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaAffineRepresentable` **proves** it, in every
integer degree, against the pullback of the universal quadruple's own `ψ` — at the cost of
presenting `θ` on the Laurent algebra of the pullback of the universal invertible module rather
than on `r^*(⨁_n 𝒪(nd))`.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeVeroneseTwists

open Stacks.AlgebraicGeometry.GradedVeronese
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : RelativeProjTwists.TwistData A)
  (d : ℕ) {T : Scheme.{u}} (g : T ⟶ (relativeProj A).scheme)

variable {S' : Scheme.{u}} {f : T ⟶ S'}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)} {e : ℤ}

/-- **In a negative degree the second leg of Lemma 01O1's triangle starts at a zero module.** If
the homogeneous pieces of `ℬ` vanish in negative degrees and the quadruple degree `e` is
positive, then `n * e` is negative for negative `n`, so `ℬ_{ne}` is a zero module, and so is its
pullback: the pullback functor on sheaves of modules preserves zero morphisms, so it sends an
identity that equals zero to an identity that equals zero. -/
public theorem isZero_pullback_piece_mul_of_neg
    (hB : ∀ m : ℤ, m < 0 → IsZero (B.piece m)) (he : 0 < e) {n : ℤ} (hn : n < 0) :
    IsZero ((pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e))) :=
  (pullbackFunctor (ringedSpaceHom f)).map_isZero (hB _ (mul_neg_of_neg_of_pos hn he))

/-- **Stacks Project, Tag 01O1.** *The comparison `θ`, the commutativity of its characterising
triangle and its uniqueness, from the triangle in nonnegative degrees alone.*

This is `...RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen` with the commutativity of
the triangle demanded only in the degrees `n ≥ 0`. In a negative degree the triangle commutes
whatever the family `v` is, because the source of `v n` is then a zero module by
`isZero_pullback_piece_mul_of_neg`, so the two sides of the equation are both the unique morphism
out of it.

This is the index set in which the tag's own second leg lives: both
`...RelativeProjTwists.TwistData.ψ` and `...MorphismToProjUniversal.IsCompatible` are families
indexed by `ℕ`. -/
public theorem existsUnique_theta_of_degreeOpen_of_nonneg
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) (P : Quadruple f B e)
    (he : 0 < e) (hB : ∀ m : ℤ, m < 0 → IsZero (B.piece m))
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e)) ⟶
      (pullbackTwistVeronese D (d : ℤ) g).piece n)
    (α : (pullbackTwistVeronese D (d : ℤ) g).piece 1 ≅ P.L)
    (hv : ∀ n : ℕ, v (n : ℤ) ≫ (laurentComparisonOfDegreeOpen D d g hg α).hom.app (n : ℤ) =
      P.twisting.app (n : ℤ)) :
    ∃ θ' : pullbackTwistVeronese D (d : ℤ) g ≅ laurent P.L,
      (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
        ∃! Θ : pullbackTwistVeronese D (d : ℤ) g ⟶ laurent P.L,
          ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n := by
  refine existsUnique_theta_of_degreeOpen D d g hg P v α (fun n => ?_)
  rcases lt_or_ge n 0 with hn | hn
  · exact (isZero_pullback_piece_mul_of_neg hB he hn).eq_of_src _ _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hv k

/-- **Stacks Project, Tag 01O1.** The `θ`-assertion from the triangle in nonnegative degrees
alone, for a quadruple over the graded algebra of Situation 01NN itself.

The vanishing of the negative homogeneous pieces is not a hypothesis here: it is the field
`negative_isZero` of `...RelativeProjBridge.SheafGradedAlgebra`, so
`existsUnique_theta_of_degreeOpen_of_nonneg` applies with nothing to supply. This is the form the
tag is stated at, where the graded algebra is the one of Situation 01NN. -/
public theorem existsUnique_theta_of_degreeOpen_of_nonneg_situation
    {A' : SheafGradedAlgebra.{u} S'}
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d)
    (P : Quadruple f (situationAlgebra A') e) (he : 0 < e)
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A').piece (n * e)) ⟶
      (pullbackTwistVeronese D (d : ℤ) g).piece n)
    (α : (pullbackTwistVeronese D (d : ℤ) g).piece 1 ≅ P.L)
    (hv : ∀ n : ℕ, v (n : ℤ) ≫ (laurentComparisonOfDegreeOpen D d g hg α).hom.app (n : ℤ) =
      P.twisting.app (n : ℤ)) :
    ∃ θ' : pullbackTwistVeronese D (d : ℤ) g ≅ laurent P.L,
      (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
        ∃! Θ : pullbackTwistVeronese D (d : ℤ) g ⟶ laurent P.L,
          ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n :=
  existsUnique_theta_of_degreeOpen_of_nonneg D d g hg P he
    (fun m hm => A'.negative_isZero m hm) v α hv

end Stacks.AlgebraicGeometry.RelativeVeroneseTwists

end
