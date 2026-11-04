module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated

/-!
# Both sides of the canonical map of Stacks 08JD have the triangle property

Let `(C, O)` be a ringed site, let `M` be an object of `D(O)` and let

`Φ_L : M ⊗^L_O L^∨ ⟶ RSheafHom_O(L, M)`

be the canonical map of Stacks 08JD, read as a natural transformation of the dualized variable
`L`, i.e. of `D(O)ᵒᵖ`.  Its target, `RSheafHom(-, M)`, carries a distinguished triangle of `D(O)`
to a distinguished triangle: that is Stacks 08JC in the contravariant variable,
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`.  **This file proves the same
for its source** `M ⊗^L_O (-)^∨`: the derived dual has the triangle property, being Stacks 08JC
at the structure sheaf, and tensoring with a fixed object is exact, which is a field of the datum
of Stacks 06YU.

## Main results

* `AlgebraicGeometry.RingedSite.exists_distinguished_derivedDual`: the derived dual `(-)^∨`
  carries a distinguished triangle of `D(O)` to a distinguished triangle.
* `AlgebraicGeometry.RingedSite.exists_distinguished_tensorDualSourceFunctor`: the source of the
  canonical map of Stacks 08JD, as a functor of the dualized variable, carries a distinguished
  triangle of `D(O)` to a distinguished triangle.

## What this file does not contain, and what it sharpens

No assertion of Stacks 08JJ is proved here and no `@[stacks]` attribute is attached.  Stacks 08JC
is already covered by two declarations — the contravariant
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom` and the covariant
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_second` — and the statements
below are a specialization and a transport of the first, not a third member of that covering set.

What the two statements below settle is one half of the data that the conditional dévissage steps
of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated` ask for
as unavailable instance hypotheses.  Those steps are stated with
`CategoryTheory.Functor.IsTriangulated` for `AlgebraicGeometry.RingedSite.tensorDualSourceFunctor`
and for `RSheafHom(-, M)`, and that predicate is strictly stronger than the triangle property
proved here in exactly one respect: it is defined relative to a chosen
`CategoryTheory.Functor.CommShift`, and it then asserts that the image of a distinguished triangle
is distinguished **with the connecting morphism that the `CommShift` prescribes**, rather than
merely with some connecting morphism.

So the residual gap for the dévissage of the third assertion of Stacks 08JJ along a distinguished
triangle is *not* the triangle property of either side — both halves are now in the library,
unconditionally and for an arbitrary distinguished triangle — but a compatibility of the two sides
with the shift of `D(O)ᵒᵖ`, which is what makes the two connecting morphisms a commuting square
and so feeds the third hypothesis of the five lemma
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_of_five`.  The implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated` record that no
such `CommShift` exists for the derived internal Hom in either variable.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived dual carries a distinguished triangle to a distinguished triangle.**  For a
distinguished `T` of `D(O)` the two morphisms
`(T.obj₃)^∨ ⟶ (T.obj₂)^∨ ⟶ (T.obj₁)^∨` induced by `T.mor₂` and `T.mor₁` extend by a connecting
morphism to a distinguished triangle.

This is Stacks 08JC in the contravariant variable,
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, at the fixed object the
structure sheaf, the derived dual being the derived internal Hom into it. -/
theorem exists_distinguished_derivedDual
    (T : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ δ : derivedDual X T.obj₁ ⟶ (derivedDual X T.obj₃)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)).map T.mor₂.op)
        (((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)).map T.mor₁.op)
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  exists_distinguished_derivedSheafHom X (derivedStructureSheaf X) T hT

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The source of the canonical map of Stacks 08JD carries a distinguished triangle to a
distinguished triangle.**  For a distinguished `Tri` of `D(O)` and an arbitrary `M`, the two
morphisms `M ⊗^L_O (Tri.obj₃)^∨ ⟶ M ⊗^L_O (Tri.obj₂)^∨ ⟶ M ⊗^L_O (Tri.obj₁)^∨` extend by a
connecting morphism to a distinguished triangle.

The source functor `AlgebraicGeometry.RingedSite.tensorDualSourceFunctor` is the composite of the
derived dual with the derived tensor product by `M`.  The dual has the triangle property by
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedDual`, and the derived tensor product by
a fixed object is a shift-compatible exact functor — the `commShift_right` and `exact_right`
fields of the datum of Stacks 06YU, which are instances — so it carries the triangle the dual
produces to a distinguished one. -/
theorem exists_distinguished_tensorDualSourceFunctor
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (Tri : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hTri : Tri ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ δ : (tensorDualSourceFunctor X T M).obj (op Tri.obj₁) ⟶
        ((tensorDualSourceFunctor X T M).obj (op Tri.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk
        ((tensorDualSourceFunctor X T M).map Tri.mor₂.op)
        ((tensorDualSourceFunctor X T M).map Tri.mor₁.op)
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedDual X Tri hTri
  exact ⟨_, (T.tensor.obj M).map_distinguished _ hδ⟩

end AlgebraicGeometry.RingedSite

end
