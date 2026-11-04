module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology, the Euler characteristic and the degree are isomorphism invariants

Sheaf cohomology on a scheme over a field, the Euler characteristic of a coherent sheaf and the
degree of a finite locally free sheaf on a proper scheme of dimension at most one are all
invariants of the isomorphism class of the sheaf.

## Main definitions

* `AlgebraicGeometry.cohomologyOverFieldFunctor`: degree-`n` cohomology over `k` as a functor
  from modules on `X` to `k`-vector spaces, of which `AlgebraicGeometry.cohomologyOverField` is
  the value on objects.
* `AlgebraicGeometry.cohomologyOverFieldIso`: the isomorphism `Hⁿ(X, ℱ) ≅ Hⁿ(X, 𝒢)` of
  `k`-vector spaces induced by an isomorphism `ℱ ≅ 𝒢` of modules.

## Main results

* `AlgebraicGeometry.cohomologyOverFieldFunctor_obj`: the functor's value on objects is
  `AlgebraicGeometry.cohomologyOverField`, by `rfl`.
* `AlgebraicGeometry.eulerCharacteristic_eq_of_iso`: `χ(X, ℱ) = χ(X, 𝒢)` for `ℱ ≅ 𝒢`.
* `AlgebraicGeometry.curveDegree_eq_of_iso`: isomorphic finite locally free sheaves of the same
  rank have the same degree.
* `AlgebraicGeometry.invertibleCurveDegree_eq_of_iso`: the same for invertible sheaves.

## Implementation notes

`AlgebraicGeometry.cohomologyOverField` is the `n`-th right derived functor of evaluation at the
whole space, with scalars restricted along the structure morphism; both of those are functors, so
the isomorphism is their `CategoryTheory.Functor.mapIso`.

`AlgebraicGeometry.curveDegree` is an alternating sum of dimensions written out directly rather
than through `AlgebraicGeometry.eulerCharacteristic`, so its invariance needs no coherence
hypothesis; it carries the rank as an explicit argument and as a class, and the class does not
transport along an isomorphism by itself, so both instances are hypotheses.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Degree-`n` cohomology of modules on a scheme over `k`, as a functor to `k`-vector spaces:
the right-derived functor of evaluation on the whole space, followed by restriction of scalars
along the structure morphism. Its value on objects is `AlgebraicGeometry.cohomologyOverField`. -/
noncomputable def cohomologyOverFieldFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} k :=
  (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- The functor's value on objects is `AlgebraicGeometry.cohomologyOverField`. -/
theorem cohomologyOverFieldFunctor_obj (n : ℕ) (F : X.Modules) :
    (cohomologyOverFieldFunctor k f n).obj F = cohomologyOverField k f F n := rfl

/-- An isomorphism `ℱ ≅ 𝒢` of modules on a scheme over `k` induces an isomorphism
`Hⁿ(X, ℱ) ≅ Hⁿ(X, 𝒢)` of `k`-vector spaces. -/
noncomputable def cohomologyOverFieldIso {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    cohomologyOverField k f F n ≅ cohomologyOverField k f G n :=
  (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).mapIso
    (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).mapIso e)

/-- Isomorphic modules have cohomology of the same dimension in every degree. -/
theorem finrank_cohomologyOverField_eq_of_iso {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    Module.finrank k (cohomologyOverField k f F n) =
      Module.finrank k (cohomologyOverField k f G n) :=
  (cohomologyOverFieldIso k f e n).toLinearEquiv.finrank_eq

/-- **The Euler characteristic is an isomorphism invariant.** -/
theorem eulerCharacteristic_eq_of_iso [IsProper f] {F G : X.Modules} [F.IsCoherent]
    [G.IsCoherent] (e : F ≅ G) : eulerCharacteristic k f F = eulerCharacteristic k f G := by
  simp only [eulerCharacteristic_eq_finsum, finrank_cohomologyOverField_eq_of_iso k f e]

/-- **The degree of a finite locally free sheaf of constant rank is an isomorphism
invariant.** -/
theorem curveDegree_eq_of_iso [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    {E E' : X.Modules} (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' rank] (e : E ≅ E') :
    curveDegree k f hdim E rank = curveDegree k f hdim E' rank := by
  simp only [curveDegree, finrank_cohomologyOverField_eq_of_iso k f e]

/-- **The degree of an invertible sheaf is an isomorphism invariant.** -/
theorem invertibleCurveDegree_eq_of_iso [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    {L L' : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    invertibleCurveDegree k f hdim L = invertibleCurveDegree k f hdim L' := by
  simp only [invertibleCurveDegree, finrank_cohomologyOverField_eq_of_iso k f e]

end AlgebraicGeometry
