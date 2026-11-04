module

public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Tactic.TermCongr
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebra.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.AlgebraSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness conditions on algebra sheaves

Let `X` be a scheme and let `A` be a sheaf of commutative `𝒪_X`-algebras, in the sense of
`Stacks.RelativeSpec.AlgebraSheaf`.  Following the Stacks Project, each of the finiteness
conditions on `A` is tested on the sections over the affine opens of `X`: `A` is of finite
type, finite, or of finite presentation when the structural ring map `Γ(X, U) → A(U)` has the
corresponding property for every affine open `U`.  This matches the Stacks Project's phrasing
"for every affine open `Spec R ⊆ X` we have `A = Ã` where `A` is an `R`-algebra which is of
finite type (resp. finite, resp. of finite presentation)", because on an affine open the
sections of a quasi-coherent algebra are exactly that `R`-algebra.

This file introduces the two conditions of that family that appear in the conclusion of
[Stacks, Tag 0817] and are not already available: being *finite*, and being *of finite
presentation*.  Both are conditions on the structural ring map over an affine open, exactly as
in the statements of tags 05JS and 086N, and they join the existing
`Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType` (in
`StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebra.Basic`) and
`Stacks.RelativeSpec.AlgebraSheaf.IsIntegral` (in
`StacksFrontier.AlgebraicGeometry.IntegralApproximation.AlgebraSheaf`), which are of the same
shape.

The elementary implications between the four conditions are recorded.  The one that carries
mathematical content is `IsIntegral.isFinite_of_isFiniteType`: for an *integral* algebra sheaf,
finite type and finite are the same condition.  That is the sheaf-level form of
[Stacks, Tag 02JJ] and the hinge on which the proof of tag 0817 turns, since it is what converts
the finite type approximations produced by tag 05JT into the finite ones demanded by tag 0817,
and it is what makes "finite type quasi-coherent subalgebra" and "finite quasi-coherent
subalgebra" interchangeable in [Stacks, Tag 0817] (1).

Vocabulary: the sheaf of algebras of Stacks Tag 05JS is `Stacks.RelativeSpec.AlgebraSheaf`, and
its conditions there — quasi-coherent, of finite presentation, finite, of finite type — are the
predicates `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent`, `.IsFinitePresentation`,
`.IsFinite` and `.IsFiniteType`.  The integrality condition of the
`finite_finitely_presented_approximation` label of Stacks Tag 0817 is
`Stacks.RelativeSpec.AlgebraSheaf.IsIntegral`.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf.IsFinite`: the structural ring map is finite on every
  affine open.  This is the definition introduced for [Stacks, Tag 086N].
* `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation`: the structural ring map is of finite
  presentation on every affine open.  This is the definition introduced for
  [Stacks, Tag 05JS].

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFinite_of_isFiniteType`: an integral algebra
  sheaf of finite type is finite.
* `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFiniteType_iff_isFinite` and
  `Stacks.RelativeSpec.AlgebraSheaf.IsIntegral.isFinite_iff_isFiniteType`: for an integral
  algebra sheaf, finite type and finite are equivalent, in both orientations.
* `Stacks.RelativeSpec.AlgebraSheaf.isFinite_iff_isIntegral_and_isFiniteType`: an algebra sheaf
  is finite exactly when it is integral and of finite type.
* `Stacks.RelativeSpec.AlgebraSheaf.IsFinite.isFiniteType`,
  `Stacks.RelativeSpec.AlgebraSheaf.IsFinite.isIntegral` and
  `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation.isFiniteType`: the elementary
  implications.
* `Stacks.RelativeSpec.AlgebraSheaf.isIntegral_of_iso`,
  `Stacks.RelativeSpec.AlgebraSheaf.isFinite_of_iso` and
  `Stacks.RelativeSpec.AlgebraSheaf.isFinitePresentation_of_iso`: each of the three conditions
  depends only on the isomorphism class of the algebra sheaf.

## Implementation notes

The two definitions transcribe the Stacks definitions of tags 05JS and 086N with no change
beyond the names of the ambient notions, so that a statement written in the vocabulary of those
tags elaborates against them.  Each condition is quantified over all affine opens of `X`, not over
the members of a chosen cover; nothing here uses quasi-compactness or quasi-separatedness.

Every proof is the corresponding statement about ring maps, applied over one affine open at a
time.  No sheaf theory is involved: both conditions are defined pointwise on affine opens, so
the quantifier passes through.

The transports along an isomorphism `e : A ≅ B` all go through the same two observations, that
the sections of `e` over an open are surjective and injective, which come from the inverse of
`e` and are recorded separately as
`Stacks.RelativeSpec.AlgebraSheaf.surjective_app_of_iso` and
`Stacks.RelativeSpec.AlgebraSheaf.injective_app_of_iso`.  Surjectivity alone suffices for
integrality and for finiteness; finite presentation additionally needs the kernel of the
isomorphism to be finitely generated, which injectivity supplies by making it zero.  These
transports are what the subobject route to [Stacks, Tag 05JT] needs, since a construction
produces a concrete monomorphism while the properties have to hold of whichever representative
`CategoryTheory.Subobject.mk` selects.

## What is not done

Nothing here says that the conditions are local on `X`, i.e. that it suffices to test them on
the members of an affine cover.  For that one needs the restriction squares of
[Stacks, Tag 01LN] together with the fact that each of `RingHom.Finite`,
`RingHom.FiniteType` and `RingHom.FinitePresentation` is a local property of ring maps, and
neither connection is made here.

Nothing here transports `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` along an isomorphism
of algebra sheaves.  That is the one condition in the conclusion of [Stacks, Tag 0817] whose
transport is still missing, and unlike the three proved here it is not a condition on the
sections over an affine open: it is a condition on
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`, obtained by restricting scalars along the
structure morphism, and moving it along `e` would require the naturality of
`SheafOfModules.restrictScalars` in the ring morphism, which Mathlib does not have at this pin.
Transport of finite type is already available as
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_iso`.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 02JJ](https://stacks.math.columbia.edu/tag/02JJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-- An algebra sheaf is *finite* when its structural ring map is finite on the sections over
every affine open. -/
def IsFinite (A : AlgebraSheaf X) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → RingHom.Finite (A.hom.hom.app (op U)).hom

/-- An algebra sheaf is *of finite presentation* when its structural ring map is of finite
presentation on the sections over every affine open. -/
def IsFinitePresentation (A : AlgebraSheaf X) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → RingHom.FinitePresentation (A.hom.hom.app (op U)).hom

/-- A finite algebra sheaf is of finite type. -/
theorem IsFinite.isFiniteType {A : AlgebraSheaf X} (hA : A.IsFinite) : A.IsFiniteType :=
  fun U hU => (hA U hU).to_finiteType

/-- A finite algebra sheaf is integral. -/
theorem IsFinite.isIntegral {A : AlgebraSheaf X} (hA : A.IsFinite) : A.IsIntegral :=
  fun U hU => (hA U hU).to_isIntegral

/-- An algebra sheaf of finite presentation is of finite type. -/
theorem IsFinitePresentation.isFiniteType {A : AlgebraSheaf X} (hA : A.IsFinitePresentation) :
    A.IsFiniteType :=
  fun U hU => RingHom.FiniteType.of_finitePresentation (hA U hU)

/-- **An integral algebra sheaf of finite type is finite.**  This is the sheaf-level form of
[Stacks, Tag 02JJ]: over an affine open the structural ring map is integral and of finite type,
hence finite.

It is the step on which [Stacks, Tag 0817] turns.  Tag 05JT presents a quasi-coherent algebra
as a directed colimit of its finite type quasi-coherent subalgebras; this lemma says that when
the algebra is integral those subalgebras are automatically finite, which is the finiteness
demanded by tag 0817. -/
@[ega "II 6.1.2" "partial"]
theorem IsIntegral.isFinite_of_isFiniteType {A : AlgebraSheaf X} (hA : A.IsIntegral)
    (h : A.IsFiniteType) : A.IsFinite :=
  fun U hU => hA.finite_app_of_finiteType hU (h U hU)

/-- For an integral algebra sheaf, being of finite type and being finite are the same
condition. -/
theorem IsIntegral.isFiniteType_iff_isFinite {A : AlgebraSheaf X} (hA : A.IsIntegral) :
    A.IsFiniteType ↔ A.IsFinite :=
  ⟨hA.isFinite_of_isFiniteType, IsFinite.isFiniteType⟩

/-- For an integral algebra sheaf, being finite and being of finite type are the same
condition.  This is what makes "finite type quasi-coherent subalgebra" and "finite
quasi-coherent subalgebra" interchangeable in [Stacks, Tag 0817] (1). -/
@[ega "II 6.1.2" "partial"]
theorem IsIntegral.isFinite_iff_isFiniteType {A : AlgebraSheaf X} (hA : A.IsIntegral) :
    A.IsFinite ↔ A.IsFiniteType :=
  hA.isFiniteType_iff_isFinite.symm

/-- An algebra sheaf is finite if and only if it is integral and of finite type. -/
theorem isFinite_iff_isIntegral_and_isFiniteType {A : AlgebraSheaf X} :
    A.IsFinite ↔ A.IsIntegral ∧ A.IsFiniteType :=
  ⟨fun hA => ⟨hA.isIntegral, hA.isFiniteType⟩, fun ⟨hA, h⟩ => hA.isFinite_of_isFiniteType h⟩

section Transport

variable {A B : AlgebraSheaf X}

/-- The inverse of an isomorphism of algebra sheaves is a left inverse on sections over an open. -/
private theorem app_inv_app_hom (e : A ≅ B) (U : X.Opens) (x : A.right.1.obj (op U)) :
    (e.inv.right.hom.app (op U)).hom ((e.hom.right.hom.app (op U)).hom x) = x :=
  congr($(congrArg (fun f : A ⟶ A => f.right.hom.app (op U)) e.hom_inv_id).hom x)

/-- The sections of an isomorphism of algebra sheaves over an open are surjective: the inverse
isomorphism provides a preimage. -/
theorem surjective_app_of_iso (e : A ≅ B) (U : X.Opens) :
    Function.Surjective (e.hom.right.hom.app (op U)).hom :=
  fun y => ⟨_, app_inv_app_hom e.symm U y⟩

/-- The sections of an isomorphism of algebra sheaves over an open are injective: the inverse
isomorphism provides a left inverse. -/
theorem injective_app_of_iso (e : A ≅ B) (U : X.Opens) :
    Function.Injective (e.hom.right.hom.app (op U)).hom :=
  Function.LeftInverse.injective (app_inv_app_hom e U)

/-- The structural ring map of the target of an isomorphism of algebra sheaves, over an open, is
the structural ring map of the source followed by the isomorphism. -/
theorem app_eq_comp_of_iso (e : A ≅ B) (U : X.Opens) :
    (B.hom.hom.app (op U)).hom =
      (e.hom.right.hom.app (op U)).hom.comp (A.hom.hom.app (op U)).hom := by
  rw [← Under.w e.hom]; rfl

/-- Integrality of an algebra sheaf depends only on its isomorphism class. -/
theorem isIntegral_of_iso (e : A ≅ B) (hA : A.IsIntegral) : B.IsIntegral := by
  intro U hU
  rw [app_eq_comp_of_iso e U]
  exact RingHom.IsIntegral.trans _ _ (hA U hU)
    (RingHom.isIntegral_of_surjective _ (surjective_app_of_iso e U))

/-- Finiteness of an algebra sheaf depends only on its isomorphism class. -/
theorem isFinite_of_iso (e : A ≅ B) (hA : A.IsFinite) : B.IsFinite := by
  intro U hU
  rw [app_eq_comp_of_iso e U]
  exact RingHom.Finite.comp
    (RingHom.Finite.of_surjective _ (surjective_app_of_iso e U)) (hA U hU)

/-- Finite presentation of an algebra sheaf depends only on its isomorphism class. -/
theorem isFinitePresentation_of_iso (e : A ≅ B) (hA : A.IsFinitePresentation) :
    B.IsFinitePresentation := by
  intro U hU
  rw [app_eq_comp_of_iso e U]
  refine (hA U hU).comp_surjective (surjective_app_of_iso e U) ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (injective_app_of_iso e U)]
  exact Submodule.fg_bot

end Transport

end Stacks.RelativeSpec.AlgebraSheaf
