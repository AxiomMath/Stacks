module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeScaling
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChart

/-!
# Tag 02NC over a base scheme: the chart comparison is compatible with restriction

Tag 02NC's proof glues the comparisons attached to the members of a covering of the base over
which `ℒ` is trivialized. Two compatibilities are needed for that glueing. One is that the
comparison over a single open does not depend on the section chosen there, which is
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul`. The other
is **compatibility with the chart transitions** — that passing from an open `V` of the base to a
smaller open `W` and comparing there is the same as comparing over `V` and restricting. This file
proves that, at the level of homogeneous sections and then at the level of the graded rings of
sections.

The content is the naturality of the formula `a ↦ a ⊗ x^d` in the open: the tensor pairing of
local sections is natural (`tensorSectionsAt_naturality`), and the powers of a local section
restrict to the powers of its restriction, which is proved here by induction on the degree.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.powSecAt_naturality`: **the powers of a local
  section of the twisting module restrict to the powers of its restriction.** The degree-zero case
  is the compatibility of the unit section of the Laurent algebra with restriction; the successor
  case is naturality of the Laurent multiplication and of the reindexing isomorphism.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.resPiece_psiPieceAt`: the comparison on
  degree-`d` homogeneous sections commutes with restriction of sections.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.res_comp_psiSectionAt`: **the comparison
  commutes with restriction, as an equality of homomorphisms of the graded rings of sections.**
  This is the square that the chart transitions of a relative homogeneous spectrum are built from,
  so it is the third of the inputs the glueing of Tag 02NC consumes.

## Why the restricted section, and not a second arbitrary one

The statements below compare the comparison over `V` attached to `x` with the comparison over `W`
attached to the **restriction** of `x`, not with the comparison attached to an arbitrary section
over `W`. That is the right form: an arbitrary trivializing section over `W` differs from the
restriction of `x` by a unit of the functions on `W`, and the comparison is insensitive to that by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul`. So the
two compatibilities are complementary, and together they say that the comparisons attached to a
family of trivializing sections over the members of a basis of the topology agree on nestings,
with no coherence condition on the family itself.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- **The powers of a local section of the twisting module restrict to the powers of its
restriction.**

The degree-zero power is the unit section of the Laurent algebra, which restricts to itself
because it is a global section; the successor step is naturality of the Laurent multiplication and
of the reindexing isomorphism, both of which are morphisms of sheaves of modules. This is the
naturality in the open that the compatibility of Tag 02NC's chart comparison with the chart
transitions rests on. -/
theorem powSecAt_naturality {U V : (Opens S)ᵒᵖ} (f : U ⟶ V) (x : (tp L 1).val.obj U) :
    ∀ d : ℕ, (tp L (d : ℤ)).val.map f (powSecAt L U x d) =
      powSecAt L V ((tp L 1).val.map f x) d
  | 0 =>
    PresheafOfModules.sections_property
      (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L) f
  | (d + 1) =>
    (PresheafOfModules.naturality_apply ((reix L (succ_cast d)).hom.val) f
        ((lmul L (d : ℤ) 1).app U (powSecAt L U x d) x)).trans
      (congrArg ((reix L (succ_cast d)).hom.val.app V)
        (((lmul L (d : ℤ) 1).naturality f (powSecAt L U x d) x).trans
          (congrArg (fun z => (lmul L (d : ℤ) 1).app V z ((tp L 1).val.map f x))
            (powSecAt_naturality f x d))))

variable (𝒜 : SheafGradedAlgebra S)

/-- **The comparison on degree-`d` homogeneous sections commutes with restriction.**

Both sides are the tensor pairing of a restricted section of `𝒜_d` with a restricted power of the
twisting section: the pairing is natural in the open, and the restricted power is the power of the
restriction. -/
theorem resPiece_psiPieceAt {W V : S.Opens} (h : W ≤ V) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    (twist 𝒜 L).resPiece h d (psiPieceAt L 𝒜 V x d a) =
      psiPieceAt L 𝒜 W ((tp L 1).val.map (homOfLE h).op x) d (𝒜.resPiece h d a) :=
  (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality S.sheaf.obj
      S.ringCatSheaf.property (𝒜.piece (d : ℤ)) (tp L (d : ℤ)) (homOfLE h).op a
      (powSecAt L (op V) x d)).trans
    (congrArg
      (fun z => tensorSectionsAt S.sheaf.obj S.ringCatSheaf.property (op W) (𝒜.piece (d : ℤ))
        (tp L (d : ℤ)) (𝒜.resPiece h d a) z)
      (powSecAt_naturality L (homOfLE h).op x d))

/-- **The comparison commutes with restriction, as an equality of homomorphisms of the graded
rings of sections.**

Restricting from `V` to `W` after comparing over `V` is comparing over `W`, with the restricted
section, after restricting from `V` to `W`. This is the square the chart transitions
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` of a relative homogeneous spectrum are
induced by, so it is the third of the inputs the glueing of Tag 02NC consumes. -/
theorem res_comp_psiSectionAt {W V : S.Opens} (h : W ≤ V) (x : (tp L 1).val.obj (op V)) :
    ((twist 𝒜 L).res h).comp (psiSectionAt L 𝒜 V x) =
      (psiSectionAt L 𝒜 W ((tp L 1).val.map (homOfLE h).op x)).comp (𝒜.res h) :=
  Stacks.GradedRing.gradedRingHom_ext (𝒜.grading V) fun d a ha => by
    obtain ⟨y, rfl⟩ := ha
    rw [GradedRingHom.comp_apply, GradedRingHom.comp_apply, psiSectionAt_of,
      show ((twist 𝒜 L).res h) (DirectSum.of ((twist 𝒜 L).sectionPieces V) d
          (psiPieceAt L 𝒜 V x d y)) =
        DirectSum.of ((twist 𝒜 L).sectionPieces W) d
          ((twist 𝒜 L).resPiece h d (psiPieceAt L 𝒜 V x d y)) from
        (twist 𝒜 L).resRingHom_of h (psiPieceAt L 𝒜 V x d y),
      show (𝒜.res h) (DirectSum.of (𝒜.sectionPieces V) d y) =
          DirectSum.of (𝒜.sectionPieces W) d (𝒜.resPiece h d y) from 𝒜.resRingHom_of h y]
    exact (congrArg (DirectSum.of ((twist 𝒜 L).sectionPieces W) d)
        (resPiece_psiPieceAt L 𝒜 h x d y)).trans
      (psiSectionAt_of L 𝒜 W ((tp L 1).val.map (homOfLE h).op x) (𝒜.resPiece h d y)).symm

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
