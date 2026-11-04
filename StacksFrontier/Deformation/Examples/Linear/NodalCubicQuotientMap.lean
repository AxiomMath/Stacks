module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicQuotient

/-!
# `Q₁ ↠ P'/(Y)`: the second step of the quotient condition

Tenth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. Layer nine
reduced `hquot` to the chain

`Q'/(z) ≅ Q₁/(z) ≅ P'/(Y)`.

This layer builds the map for the second step: the surjection `Q₁ ↠ P'/(Y)` that kills the
Artin–Schreier root, which exists because substituting `z = 0` into `z² + z − Y` leaves `−Y`.

## Mathlib does not cover this

Worth recording, since the obvious move is to look for it. `AdjoinRoot.quotMapOfEquivQuotMapCMapMk`
— with its `quotMapOfEquivQuotMapCMapSpanMk` alias and the
`quotAdjoinRootEquivQuotPolynomialQuot` family — describes `AdjoinRoot f` modulo an ideal
**mapped up from the base**, as `(AdjoinRoot f) ⧸ (I.map (of f)) ≃ AdjoinRoot (f.map (mk I))`.
Neither step of the chain above is of that form: the first quotients by the **root**, and the
second is the localization step. So both are hand-rolled, and this file does the first half of the
first: the map and its surjectivity.

## The two steps of `hquot`, and where they are

Both steps below are discharged: injectivity by `ker_qOneToQuotOmega` (layer eleven) and the
localization step, with `hquot` itself, by `bijective_quotientMap_omegaP` (layer twelve).

* **injectivity** of the map below. The kernel is `span {z}`: `Q₁` is free over `P'` on `{1, z}`
  (`free_QOne`), so an element is `a + b·z` and its image is `a mod Y`; so the kernel is
  `(Y)·1 + P'·z`, and `Y = z·(z + 1)` puts `(Y)` inside `span {z}`. That argument needs the
  coordinates from `AdjoinRoot.powerBasis'` and is not done here;
* the **localization step** `Q'/(z) ≅ Q₁/(z)`, which holds because `z + 1 ↦ 1` modulo `z`, so
  inverting it does nothing.

## Main results

* `Deformation.Examples.ArtinSchreier.qOneToQuotOmega`: the map `Q₁ → P'/(Y)` killing the root.
* `Deformation.Examples.ArtinSchreier.qOneToQuotOmega_root`: it kills `z`.
* `Deformation.Examples.ArtinSchreier.surjective_qOneToQuotOmega`: it is surjective.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-- `Y` dies in `P'/(Y)`. -/
theorem mk_omegaP_eq_zero :
    Ideal.Quotient.mk (Ideal.span {omegaP}) omegaP = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-- **The map `Q₁ → P'/(Y)` killing the Artin–Schreier root.** It exists because substituting
`z = 0` into the defining relation `z² + z − Y` of `Q₁` leaves `−Y`, which is zero in `P'/(Y)`.
This is the second step of the quotient condition's chain, in the form that is available without
injectivity. -/
def qOneToQuotOmega : QOne →+* (PBase ⧸ Ideal.span {omegaP}) :=
  AdjoinRoot.lift (Ideal.Quotient.mk (Ideal.span {omegaP})) 0 (by
    change Polynomial.eval₂ (Ideal.Quotient.mk (Ideal.span {omegaP})) 0 qPoly = 0
    rw [show qPoly = X ^ 2 + (X - C omegaP) from rfl]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    rw [mk_omegaP_eq_zero]
    ring)

/-- The map kills `z`. -/
theorem qOneToQuotOmega_root : qOneToQuotOmega zRoot = 0 :=
  AdjoinRoot.lift_root _

/-- The map restricts to the quotient map on `P'`, so `P'/(Y)` really is a quotient of `Q₁` as a
`P'`-algebra. -/
theorem qOneToQuotOmega_algebraMap (a : PBase) :
    qOneToQuotOmega (algebraMap PBase QOne a) =
      Ideal.Quotient.mk (Ideal.span {omegaP}) a :=
  AdjoinRoot.lift_of _

/-- **The map is surjective**, because it splits the structure map `P' → Q₁`. -/
theorem surjective_qOneToQuotOmega : Function.Surjective qOneToQuotOmega := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨algebraMap PBase QOne a, qOneToQuotOmega_algebraMap a⟩

end Deformation.Examples.ArtinSchreier

end
