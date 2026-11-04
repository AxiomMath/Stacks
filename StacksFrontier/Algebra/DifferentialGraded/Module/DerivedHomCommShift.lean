module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomTriangles

/-!
# `Hom(K, -)` commutes with the translation

Let `K` be a cochain complex in a preadditive category `B` and let `E = End(K)` be its
endomorphism differential graded algebra. The shift comparisons
`CochainComplex.homShiftIso` of Tag 09LE assemble into a
`CategoryTheory.Functor.CommShift ℤ` for the functor
`Hom(K, -) : CochainComplex B ℤ ⥤ Mod_{(E, d)}`: they are natural in the target, and they are
compatible with `CategoryTheory.shiftFunctorZero` and `CategoryTheory.shiftFunctorAdd` at both
ends.

This is the first of the two halves of exactness asked of the functor being derived by Tag 09LK,
the second being preservation of distinguished triangles,
`CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`. The two fit together: the
third arrow of `CategoryTheory.Functor.mapTriangle` is formed with the degree-one component of
this `CommShift`, which is exactly the comparison the triangle statement already uses.

## Main definitions

* `CochainComplex.homComplexesCommShiftIso`: the comparison `Hom(K, -[n]) ≅ Hom(K, -)[n]`, as a
  natural isomorphism.
* `CochainComplex.homComplexesFunctorCommShift`: the resulting
  `(CochainComplex.homComplexesFunctor B K).CommShift ℤ`.

## Implementation notes

All three conditions are checked on underlying linear maps and reduce to the three identities
`CochainComplex.homShiftIso_hom_toFun_repPostcomp`,
`CochainComplex.homShiftIso_hom_toFun_zero` and `CochainComplex.homShiftIso_hom_toFun_add`, which
in turn reduce to identities between cochains. On the target side nothing more is needed: the
comparison isomorphisms of `DifferentialGradedModule.shiftMkCore` are the identity on underlying
modules, so neither `DifferentialGradedModule.shiftZeroInv` nor
`DifferentialGradedModule.shiftAddInv` contributes anything to the formulas.

There is no Koszul sign. The sign of the identification of axiom (B) against composition on the
left is `(-1)^{n·m}` in the degree `m` of the left factor, and the left factors occurring here
are the degree-zero cochains of the three chain maps `φ[n]`, `X[0] ⟶ X` and
`X[a + b] ⟶ (X[a])[b]`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose exactness clause
  this is part of; [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the shift comparison
  of the representable differential graded module.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

open CochainComplex.HomComplex DifferentialGradedModule

variable (B : Type u) [Category.{v} B] [Preadditive B] (K : CochainComplex B ℤ)

/-- **The shift comparison for `Hom(K, -)`, as a natural isomorphism.** On an object it is
`CochainComplex.homShiftIso`; its naturality is the naturality of the identification of
axiom (B) in the target. -/
noncomputable def homComplexesCommShiftIso (n : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex B ℤ) n ⋙ homComplexesFunctor B K ≅
      homComplexesFunctor B K ⋙
        CategoryTheory.shiftFunctor
          (DifferentialGradedModule (DGCategory.endAlgebra (dgCategory B) K)) n :=
  NatIso.ofComponents (fun X => homShiftIso K n X) (fun {_ _} φ =>
    DifferentialGradedModule.Hom.ext (LinearMap.ext fun z =>
      homShiftIso_hom_toFun_repPostcomp K n φ z))

/-- The component of `CochainComplex.homComplexesCommShiftIso` at `X` is the morphism
`(CochainComplex.homShiftIso K n X).hom`. -/
@[simp] theorem homComplexesCommShiftIso_hom_app (n : ℤ) (X : CochainComplex B ℤ) :
    (homComplexesCommShiftIso B K n).hom.app X = (homShiftIso K n X).hom := rfl

/-- **`Hom(K, -)` commutes with the translation.** The shift comparisons
`Hom(K, X[n]) ≅ Hom(K, X)[n]` of Tag 09LE are natural in `X` and compatible with
`CategoryTheory.shiftFunctorZero` and `CategoryTheory.shiftFunctorAdd`, so they make
`Hom(K, -) : CochainComplex B ℤ ⥤ Mod_{(E, d)}` a functor commuting with the shift by `ℤ`. -/
@[stacks 09LK "the functor Hom(K, -) being derived commutes with the translation: the shift \
comparisons Hom(K, X[n]) = Hom(K, X)[n] are natural in X and compatible with shiftFunctorZero \
and shiftFunctorAdd, which is the coherence Functor.mapTriangle is formed with"]
noncomputable instance homComplexesFunctorCommShift :
    (homComplexesFunctor B K).CommShift ℤ where
  commShiftIso := homComplexesCommShiftIso B K
  commShiftIso_zero := by
    ext X
    rw [homComplexesCommShiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    exact DifferentialGradedModule.Hom.ext
      (LinearMap.ext fun z => homShiftIso_hom_toFun_zero K X z)
  commShiftIso_add a b := by
    ext X
    rw [homComplexesCommShiftIso_hom_app, Functor.CommShift.isoAdd_hom_app,
      homComplexesCommShiftIso_hom_app, homComplexesCommShiftIso_hom_app]
    exact DifferentialGradedModule.Hom.ext
      (LinearMap.ext fun z => homShiftIso_hom_toFun_add K X a b z)

/-- The commutation isomorphism of `CochainComplex.homComplexesFunctor B K` with the shift by `n`
is `CochainComplex.homComplexesCommShiftIso B K n`. -/
@[simp] theorem commShiftIso_homComplexesFunctor (n : ℤ) :
    Functor.commShiftIso (homComplexesFunctor B K) n = homComplexesCommShiftIso B K n := rfl

end CochainComplex
