module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PieceZeroUnit
public import StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Homogeneous pieces of `r^*(⨁_n 𝒪(nd))` over the degree-`d` locus

For a morphism `r : T ⟶ Proj_S(𝒜)` whose image lies in the relative degree-`d` locus, every
homogeneous piece of `r^*(⨁_{n ∈ ℤ} 𝒪(nd))` is an invertible `𝒪_T`-module, the piece in the
opposite degree being its tensor inverse.

## Main results

* `RelativeVeroneseTwists.isInvertible_pullbackTwistVeronese_piece_of_mem_degreeOpen`: every
  homogeneous piece of `r^*(⨁_n 𝒪(nd))` is invertible over the degree-`d` locus.
* `RelativeVeroneseTwists.isInvertible_pullbackTwistVeronese_piece_one_of_mem_degreeOpen`: the
  degree-one case, `r^*𝒪(d)`.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeVeroneseTwists

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A) (d : ℕ)
  {T : Scheme.{u}} (g : T ⟶ (relativeProj A).scheme)

/-- Every homogeneous piece of `g^*(⨁_{n ∈ ℤ} 𝒪(nd))` is an invertible `𝒪_T`-module, for any
morphism `g : T ⟶ Proj_S(𝒜)` whose image lies in the relative degree-`d` locus. -/
@[ega "II 2.5.8" "more general", ega "II 2.6.1" "more general"]
theorem isInvertible_pullbackTwistVeronese_piece_of_mem_degreeOpen
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((pullbackTwistVeronese D (d : ℤ) g).piece n) := by
  have hmul := isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen D d g hg
  have hinv := isInvertible_pullbackTwistVeronese_piece_zero D g (d : ℤ)
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨(pullbackTwistVeronese D (d : ℤ) g).piece (-n), ⟨?_⟩⟩
  refine (@asIso _ _ _ _ _ (hmul n (-n))) ≪≫ ?_
  refine eqToIso (congrArg (pullbackTwistVeronese D (d : ℤ) g).piece
    (show n + -n = 0 by ring)) ≪≫ ?_
  exact Stacks.AlgebraicGeometry.ProjRepresentsF1.pieceZeroIsoUnit
    (pullbackTwistVeronese D (d : ℤ) g) (isSheafStruct T) hinv (hmul 0 0)

/-- The pullback `g^*𝒪(d)` is invertible for any morphism `g : T ⟶ Proj_S(𝒜)` whose image lies in
the relative degree-`d` locus. -/
theorem isInvertible_pullbackTwistVeronese_piece_one_of_mem_degreeOpen
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((pullbackTwistVeronese D (d : ℤ) g).piece 1) :=
  isInvertible_pullbackTwistVeronese_piece_of_mem_degreeOpen D d g hg 1

end Stacks.AlgebraicGeometry.RelativeVeroneseTwists

end
