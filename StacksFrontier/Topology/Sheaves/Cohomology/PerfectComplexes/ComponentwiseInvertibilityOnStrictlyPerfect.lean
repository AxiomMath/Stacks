module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens

/-!
# A natural transformation invertible on the shifts of the structure sheaf

Let `X` be a ringed space and let `α : F ⟶ G` be a natural transformation between exact functors
out of `D(𝒪_X)`.  If `α` is invertible at every shift of the structure sheaf placed in every
degree, then it is invertible at every shift of every strictly perfect complex.

## Main results

* `Stacks.Cohomology.StrictlyPerfectInvertibility.isIso_app_of_isStrictlyPerfect`: the
  statement above.

## Implementation notes

The three closure properties of
`StacksFrontier/CategoryTheory/Triangulated/ComponentwiseInvertibility.lean` are what the proof
consumes, and the induction is
`Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex` applied to the property
"`α` is invertible at every shift of this object":

* a strictly perfect complex is bounded, which is the finiteness hypothesis of the induction;
* its terms are direct summands of finite free modules, so invertibility at each term follows
  from invertibility at `𝒪_X^{⊕ n}` — a finite biproduct of copies of `𝒪_X` — by
  `isIso_app_of_biproduct` and then `isIso_app_of_splitRetract`;
* the extension step of the induction is `isIso_app_middle_of_all_shifts` applied to the
  distinguished triangle `DerivedCategory.triangleOfSES` of the short exact sequence of
  complexes.

The property is quantified over all shifts because the extension step needs it at all shifts:
the inverse rotation used inside `isIso_app_middle_of_all_shifts` moves the vertices of the
triangle.

The four structural hypotheses on `F` and `G` — that each commutes with the shift and is exact —
are explicit arguments rather than instance binders.  The categories at both ends are derived
categories of a category of sheaves of modules, and the spelling of the structure sheaf of rings
differs between this file and the consumers of the statement, so the `HasShift` instance a
consumer has is the same one only after a semireducible definition is unfolded; instance search,
which works at `implicit` transparency, does not see that, while an explicit argument's type
ascription does.

The functors are composed with `DerivedCategory.singleFunctor _ i ⋙ shiftFunctor _ n` before the
biproduct and retract steps are applied, so that those steps are used on the module category
`OXMod X` rather than on its derived category; this is what makes `𝒪_X^{⊕ n}` a biproduct the
hypotheses speak about.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.DerivedCategory.BoundedInduction

universe u

namespace Stacks.Cohomology.StrictlyPerfectInvertibility

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- **Invertibility on the shifts of the structure sheaf spreads to strictly perfect
complexes.**  A natural transformation between exact functors out of `D(𝒪_X)` which is
invertible at `𝒪_X` placed in an arbitrary degree and shifted by an arbitrary amount is
invertible at every shift of every strictly perfect complex. -/
theorem isIso_app_of_isStrictlyPerfect {X : RingedSpace.{u, u}} {D : Type*} [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D] [HasFiniteBiproducts D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (OXMod.{u, u} X) ⥤ D)
    (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated) (α : F ⟶ G)
    (hunit : ∀ i n : ℤ, IsIso (α.app
      (((DerivedCategory.singleFunctor (OXMod.{u, u} X) i).obj (structureModule X))⟦n⟧)))
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (hK : IsStrictlyPerfect K) :
    ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) := by
  let _ : F.CommShift ℤ := hFs
  let _ : G.CommShift ℤ := hGs
  let _ : F.IsTriangulated := hFt
  let _ : G.IsTriangulated := hGt
  apply property_of_bounded_complex (fun A => ∀ n : ℤ, IsIso (α.app (A⟦n⟧)))
  · intro A B e h n
    exact (α.isIso_app_iff_of_iso ((shiftFunctor _ n).mapIso e)).mp (h n)
  · intro A hA n
    exact IsZero.isIso (F.map_isZero ((shiftFunctor _ n).map_isZero hA))
      (G.map_isZero ((shiftFunctor _ n).map_isZero hA)) _
  · intro S hS h₁ h₃
    exact isIso_app_middle_of_all_shifts F G α (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
  · exact hK.bounded
  · intro i n
    let H := DerivedCategory.singleFunctor (OXMod.{u, u} X) i ⋙ shiftFunctor _ n
    let β := Functor.whiskerLeft H α
    obtain ⟨m, ⟨r⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract (K.X i)).mp (hK.directSummand i)
    have hfree : IsIso (β.app (finiteFree X m)) :=
      isIso_app_of_biproduct (H ⋙ F) (H ⋙ G) (fun _ : Fin m => structureModule X) β
        (fun _ => hunit i n)
    exact isIso_app_of_splitRetract (H ⋙ F) (H ⋙ G) β r.i r.r r.retract hfree

end Stacks.Cohomology.StrictlyPerfectInvertibility

end
