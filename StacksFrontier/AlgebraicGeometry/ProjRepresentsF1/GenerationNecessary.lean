module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos

/-!
# Degree-one generation is necessary for Tag 01O4's bijection

Tag 01O4 assumes that the graded algebra is generated in degree one over its degree-zero part.
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` does not record that assumption, and this
file measures what that costs: the degree-one piece of a pair's invertible sheaf is a quotient
of the pullback of `A₁`, so when `A₁` vanishes every pair has a zero invertible sheaf.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairDegreeOneMap`: the degree-one part of a pair's
  graded map, as a morphism of the pullback of `A₁` onto the pair's invertible sheaf. This is the
  morphism the field `degreeOneSurjective` is about, named so that it can be composed.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.epi_pairDegreeOneMap`: that morphism is an
  epimorphism, which is `degreeOneSurjective` itself.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isZero_L_of_isZero_piece_one`: a pair's invertible
  sheaf is a zero object as soon as the degree-one piece of the algebra is.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.eq_zero_of_isZero_piece_one_of_generated`: the other
  half of the measurement. Under the tag's own hypothesis a vanishing degree-one piece makes
  every positive-degree piece vanish too, over every affine open of the base — so the algebra
  sits in degree zero and its relative `Proj` is empty. Generation in degree one is therefore
  exactly what keeps the two results above from colliding.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

/-- An epimorphism out of a zero object has a zero object as target. -/
public theorem isZero_target_of_epi {C : Type*} [Category C] [HasZeroMorphisms C] {X Y : C}
    {e : X ⟶ Y} (he : Epi e) (hX : IsZero X) : IsZero Y := by
  have : Epi e := he
  exact (IsZero.iff_id_eq_zero Y).2 ((cancel_epi e).1 (hX.eq_of_src _ _))

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-- The degree-one part of a pair's graded map, read as a morphism out of the pullback of the
degree-one piece of the algebra and onto the pair's invertible sheaf: the adjoint transpose of
`ψ 1`, followed by the bundle's identification of the degree-one piece of the tensor algebra
with the sheaf itself. -/
public def pairDegreeOneMap {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) :
    (Scheme.Modules.pullback f).obj (A.piece 1) ⟶ P.L :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (P.ψ 1) ≫
    ((TA T P.L).tensorPieceIso 1).hom ≫
    (eqToHom (by rfl : SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) P.L 1 = P.L))

/-- **The tautological surjection of a pair.** The morphism of `pairDegreeOneMap` is an
epimorphism: this is the field `degreeOneSurjective`, with its morphism named. -/
public theorem epi_pairDegreeOneMap {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) :
    Epi (pairDegreeOneMap A TA P) :=
  P.degreeOneSurjective

/-- **The invertible sheaf of a pair is a quotient of the pullback of `A₁`.** So if the
degree-one piece of the graded algebra is a zero object, then so is the invertible sheaf of
every invertible degree-one quotient, on every test scheme. -/
public theorem isZero_L_of_isZero_piece_one {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f)
    (hA : IsZero (A.piece 1)) : IsZero P.L :=
  isZero_target_of_epi (epi_pairDegreeOneMap A TA P) (isZero_pullback_obj f hA)


/-! ### Generation in degree one excludes the vanishing -/

/-- A local section of a zero object vanishes. -/
public theorem eq_zero_of_isZero_piece {M : S.Modules} (hM : IsZero M) (U : S.Opens)
    (x : Γ(M, U)) : x = 0 := by
  have h : (𝟙 M : M ⟶ M).app U x = (0 : M ⟶ M).app U x := by
    rw [hM.eq_of_src (𝟙 M) 0]
  simpa using h

/-- **Generation in degree one excludes a vanishing degree-one piece.** If the degree-one piece
of the graded algebra is a zero object then, over every affine open of the base, the degree-zero
part is already the whole ring of homogeneous sections, so every piece of positive degree has
only the zero section.

Both halves of the argument are the two descriptions of the degree-zero subalgebra. The
generators that `IsGeneratedInDegreeOne` adjoins are the images of the degree-one sections, which
all vanish, so the subalgebra they generate is the degree-zero one; generation says that
subalgebra is everything; and an element that lies in both the degree-`0` and the degree-`n`
summand of a direct sum is zero when `n ≠ 0`. -/
public theorem eq_zero_of_isZero_piece_one_of_generated (hgen : IsGeneratedInDegreeOne A)
    (hA : IsZero (A.piece 1)) {U : S.Opens} (hU : IsAffineOpen U) {n : ℕ} (hn : n ≠ 0)
    (x : A.sectionPieces U n) : x = 0 := by
  have hbot : Algebra.adjoin (A.grading U 0) (A.grading U 1 : Set (A.sectionRing U)) ≤ ⊥ := by
    refine Algebra.adjoin_le ?_
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    rw [eq_zero_of_isZero_piece hA U z, map_zero]
    exact Subalgebra.zero_mem _
  have htop : (⊤ : Subalgebra (A.grading U 0) (A.sectionRing U)) ≤ ⊥ := hgen U hU ▸ hbot
  obtain ⟨r, hr⟩ :=
    Algebra.mem_bot.1 (htop (Algebra.mem_top (x := DirectSum.of (A.sectionPieces U) n x)))
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 r.2
  have key : (DirectSum.of (A.sectionPieces U) 0) z = (DirectSum.of (A.sectionPieces U) n) x :=
    hz.trans hr
  have hcomp := DFunLike.congr_fun key n
  rw [DirectSum.of_eq_of_ne 0 n z hn, DirectSum.of_eq_same n x] at hcomp
  exact hcomp.symm

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
