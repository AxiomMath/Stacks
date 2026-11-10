module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Homomorphisms of sheaf-level graded algebras on a scheme

Situation 01NN fixes a scheme `S` and a quasi-coherent, commutative, nonnegatively graded
`𝒪_S`-algebra, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Tag 07ZG starts from a
*homomorphism* of two such algebras over the same base, and this file introduces that vocabulary
and the one construction every statement of the tag rests on: the induced homomorphism of the
graded rings of sections over an open, and its compatibility with restriction.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom`: a degreewise morphism of
  sheaves of modules preserving the multiplication and the unit of local sections.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom`: the induced
  homomorphism `Γ(U, A) →+*ᵍ Γ(U, B)` of the graded rings of sections over an open.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.res_comp_sectionHom`: the
  induced homomorphisms commute with restriction of homogeneous sections. This is the naturality
  that makes the local triples of Tag 07ZG agree on overlaps, and it is used in exactly that way in
  `StacksDraft.AlgebraicGeometry.F3.Tag07ZG.MapDomain`.

## Implementation notes

The vocabulary is introduced here rather than imported because this repository has no form of
Tag 0FQW (graded algebras on a ringed site) and none of Tag 062R (the ringed site of a scheme);
`RelativeProjBridge` records that absence and introduces `SheafGradedAlgebra` for the same
reason. The shape chosen here mirrors `SheafGradedAlgebra` itself: the data is a family of
morphisms of `AlgebraicGeometry.Scheme.Modules`, and the laws are stated on sections over an
arbitrary open, which is the form every consumer uses.

Degree bookkeeping is the same as in
`StacksFrontier/AlgebraicGeometry/RelativeProjBridge/SectionRing.lean`: the pieces are indexed
by `ℤ` and the section ring is graded by `ℕ`, and the two spellings `(↑(i + j) : ℤ)` and
`(↑i + ↑j : ℤ)` are definitionally equal but not syntactically equal. So the two laws are
stated once, in the `ℤ` spelling, and transferred by `exact` rather than by `rw`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

variable {S : Scheme.{u}}

/-- A homomorphism of sheaf-level graded `𝒪_S`-algebras: a morphism of sheaves of modules in
each degree, compatible with the multiplication of local sections and with the unit. -/
@[ega "II 3.5.6" "special case"]
public structure SheafGradedAlgebraHom (A B : SheafGradedAlgebra S) where
  /-- The morphism of homogeneous pieces in each degree. -/
  app (n : ℤ) : A.piece n ⟶ B.piece n
  /-- The morphisms preserve products of local sections. -/
  app_mul (i j : ℤ) (U : S.Opens) (a : Γ(A.piece i, U)) (b : Γ(A.piece j, U)) :
    (app (i + j)).app U ((A.mul i j).app U a b) =
      (B.mul i j).app U ((app i).app U a) ((app j).app U b)
  /-- The morphisms preserve the unit. -/
  app_one (U : S.Opens) : (app 0).app U (A.one U) = B.one U

namespace SheafGradedAlgebraHom

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- The map on degree-`n` homogeneous sections over an open, as an additive homomorphism. -/
public noncomputable def sectionPieceHom (U : S.Opens) (n : ℕ) :
    A.sectionPieces U n →+ B.sectionPieces U n where
  toFun := (ψ.app (n : ℤ)).app U
  map_zero' := map_zero _
  map_add' := map_add _

/-- On a homogeneous section, `sectionPieceHom` is the degreewise morphism `ψ.app n` evaluated over
the open. -/
public theorem sectionPieceHom_apply (U : S.Opens) (n : ℕ) (a : A.sectionPieces U n) :
    ψ.sectionPieceHom U n a = (ψ.app (n : ℤ)).app U a := rfl

/-- The unit law in the `ℕ`-indexed spelling the graded ring of sections uses. -/
public theorem sectionPieceHom_one (U : S.Opens) :
    ψ.sectionPieceHom U 0 (A.one U) = B.one U := ψ.app_one U

/-- The product law in the `ℕ`-indexed spelling the graded ring of sections uses. -/
public theorem sectionPieceHom_mul (U : S.Opens) (i j : ℕ) (a : A.sectionPieces U i)
    (b : A.sectionPieces U j) :
    ψ.sectionPieceHom U (i + j) ((A.mul (i : ℤ) (j : ℤ)).app U a b) =
      (B.mul (i : ℤ) (j : ℤ)).app U (ψ.sectionPieceHom U i a) (ψ.sectionPieceHom U j b) :=
  ψ.app_mul (i : ℤ) (j : ℤ) U a b

/-- The induced homomorphism of the graded rings of sections over an open. -/
public noncomputable def sectionRingHom (U : S.Opens) :
    A.sectionRing U →+* B.sectionRing U :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (B.sectionPieces U) n).comp (ψ.sectionPieceHom U n))
    ((congrArg (DirectSum.of (B.sectionPieces U) 0) (ψ.sectionPieceHom_one U)).trans
      (DirectSum.one_def _).symm)
    (fun {i j} a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [DirectSum.of_mul_of]
      exact congrArg (DirectSum.of (B.sectionPieces U) (i + j))
        (ψ.sectionPieceHom_mul U i j a b))

/-- On a homogeneous element of degree `n`, the induced homomorphism of section rings is the
degreewise map `sectionPieceHom` in degree `n`. -/
public theorem sectionRingHom_of (U : S.Opens) {n : ℕ} (a : A.sectionPieces U n) :
    ψ.sectionRingHom U (DirectSum.of (A.sectionPieces U) n a) =
      DirectSum.of (B.sectionPieces U) n (ψ.sectionPieceHom U n a) :=
  DirectSum.toSemiring_of _ _ _ n a

/-- The induced homomorphism of the graded rings of sections, as a graded ring homomorphism. -/
public noncomputable def sectionHom (U : S.Opens) : A.grading U →+*ᵍ B.grading U where
  __ := ψ.sectionRingHom U
  map_mem := fun {_ _} hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (ψ.sectionRingHom_of U y).symm⟩

/-- The underlying ring homomorphism of `sectionHom` is `sectionRingHom`. -/
public theorem sectionHom_toRingHom (U : S.Opens) :
    (ψ.sectionHom U).toRingHom = ψ.sectionRingHom U := rfl

/-- On a homogeneous element of degree `n`, the graded ring homomorphism `sectionHom` is the
degreewise map `sectionPieceHom` in degree `n`. -/
public theorem sectionHom_of (U : S.Opens) {n : ℕ} (a : A.sectionPieces U n) :
    ψ.sectionHom U (DirectSum.of (A.sectionPieces U) n a) =
      DirectSum.of (B.sectionPieces U) n (ψ.sectionPieceHom U n a) :=
  ψ.sectionRingHom_of U a

/-- Restriction of homogeneous sections commutes with the degreewise maps: this is naturality of
the morphisms of sheaves of modules. -/
public theorem sectionPieceHom_resPiece {U V : S.Opens} (h : U ≤ V) (n : ℕ)
    (a : A.sectionPieces V n) :
    ψ.sectionPieceHom U n (A.resPiece h n a) =
      B.resPiece h n (ψ.sectionPieceHom V n a) :=
  PresheafOfModules.naturality_apply (ψ.app (n : ℤ)).val (homOfLE h).op a

/-- **The naturality of Tag 07ZG's homomorphism on section rings.** The graded ring homomorphism
induced on the sections over `V` followed by restriction to `U` is restriction to `U` followed by
the graded ring homomorphism induced on the sections over `U`.

This is the identity that makes the triples of Tag 07ZG attached to two nested affine opens of
the base agree. -/
public theorem res_comp_sectionHom {U V : S.Opens} (h : U ≤ V) :
    (B.res h).comp (ψ.sectionHom V) = (ψ.sectionHom U).comp (A.res h) := by
  refine GradedRingHom.ext fun x => ?_
  change (B.resRingHom h) (ψ.sectionRingHom V x) = ψ.sectionRingHom U (A.resRingHom h x)
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of n y =>
    rw [ψ.sectionRingHom_of, B.resRingHom_of, A.resRingHom_of, ψ.sectionRingHom_of]
    exact congrArg (DirectSum.of (B.sectionPieces U) n)
      (ψ.sectionPieceHom_resPiece h n y).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end SheafGradedAlgebraHom

end Stacks.AlgebraicGeometry.RelativeProjMapDomain

end
