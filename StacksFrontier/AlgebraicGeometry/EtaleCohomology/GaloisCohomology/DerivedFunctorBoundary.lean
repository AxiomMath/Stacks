module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The unit and the connecting morphisms of a right derived functor

Let `T : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives, so that the right derived functor `RT : D⁺(𝒜) ⥤ D⁺(ℬ)` and the higher right derived
functors `R ⁱ T = H ⁱ ∘ RT ∘ (·[0])` are available
(`CategoryTheory.Functor.rightDerivedPlus`). This file defines two canonical maps attached to
this family.

The first is the degree-zero unit `T(X) ⟶ R ⁰ T(X)`. It is `H ⁰` of the unit of `RT` at the
complex `X[0]`, with its source identified with `T(X)` and its target with `R ⁰ T(X)`; by
[Stacks, Tag 05TD] it is invertible exactly when `T` is left exact, which is
`isIso_rightDerivedZeroUnit` below.

The second is the connecting morphism `R ⁱ T(X₃) ⟶ R ⁱ⁺¹ T(X₁)` of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `𝒜`: the canonical boundary `X₃[0] ⟶ X₁[0]⟦1⟧` of the sequence,
pulled back along the fully faithful inclusion `ι : D⁺(𝒜) ⥤ D(𝒜)` and pushed through `RT`
(`rightDerivedSingleBoundary`), followed by `H ⁱ` (`rightDerivedPlusConnecting`).

## Main definitions

* `Stacks.RightDerivedPlus.rightDerivedZeroUnit` — the canonical map `T(X) ⟶ R ⁰ T(X)`.
* `Stacks.RightDerivedPlus.rightDerivedSingleBoundary` — the image under `RT` of the canonical
  boundary of a short exact sequence.
* `Stacks.RightDerivedPlus.rightDerivedPlusConnecting` — the connecting morphism
  `R ⁱ T(X₃) ⟶ R ⁱ⁺¹ T(X₁)`.

## Main results

* `Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit` — the degree-zero unit of a left exact
  functor is an isomorphism.

## References

* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedPlus

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The degree-zero unit from an additive functor to its right derived functor,
obtained from the unit on complexes concentrated in degree zero. -/
public noncomputable def rightDerivedZeroUnit (T : C ⥤ D) [T.Additive] (X : C) :
    T.obj X ⟶ (T.rightDerivedPlus 0).obj X :=
  (((Functor.associator (DerivedCategory.Plus.singleFunctor D 0)
        DerivedCategory.Plus.ι (DerivedCategory.homologyFunctor D 0)).symm.app
        (T.obj X) ≪≫
      (DerivedCategory.homologyFunctor D 0).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso D 0).app (T.obj X)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app
        (T.obj X)).inv ≫
    (DerivedCategory.Plus.homologyFunctor D 0).map
      ((CategoryTheory.Functor.mapSingleFunctorCompQhIso T).app X).inv ≫
    (DerivedCategory.Plus.homologyFunctor D 0).map
      (T.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) ≫
    (DerivedCategory.Plus.homologyFunctor D 0).map
      (T.rightDerivedFunctorPlus.map
        ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) 0).app X).inv))

/-- **A left exact functor is its own zeroth right derived functor**, in the normalized form:
the canonical map `T(X) ⟶ R ⁰ T(X)` is an isomorphism when `T` preserves finite limits. This is
part (3) of [Stacks, Tag 05TD]. -/
public lemma isIso_rightDerivedZeroUnit (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T]
    (X : C) : IsIso (rightDerivedZeroUnit T X) := by
  have h := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    T T.rightDerivedFunctorPlus T.rightDerivedFunctorPlusUnit).2.2.2 ‹_›
  have a2 : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      ((CategoryTheory.Functor.mapSingleFunctorCompQhIso T).app X).inv) := inferInstance
  have a4 : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (T.rightDerivedFunctorPlus.map
        ((CategoryTheory.Functor.singleFunctorPlusIsoCompQh (A := C) 0).app X).inv)) :=
    inferInstance
  unfold rightDerivedZeroUnit
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' a2 (IsIso.comp_isIso' (h X) a4))

/-- The image under the right derived functor of the canonical boundary
of a short exact sequence, with the shift commutation induced by its unit. -/
public noncomputable def rightDerivedSingleBoundary (T : C ⥤ D) [T.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) :
    T.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃) ⟶
      (T.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))⟦(1 : ℤ)⟧ :=
  letI := Functor.IsRightDerivedFunctor.commShift T.rightDerivedFunctorPlus
    T.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) ℤ
  ShiftedHom.map
    (DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)))
    T.rightDerivedFunctorPlus

/-- The standard connecting map on higher right derived functors, obtained
by taking homology of the derived boundary of a short exact sequence. -/
public noncomputable def rightDerivedPlusConnecting (T : C ⥤ D) [T.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (q : ℕ) :
    (T.rightDerivedPlus q).obj S.X₃ ⟶
      (T.rightDerivedPlus (q + 1)).obj S.X₁ :=
  (DerivedCategory.Plus.homologyFunctor D 0).shiftMap
    (rightDerivedSingleBoundary T hS) q (q + 1) (by omega)

end Stacks.RightDerivedPlus

end
