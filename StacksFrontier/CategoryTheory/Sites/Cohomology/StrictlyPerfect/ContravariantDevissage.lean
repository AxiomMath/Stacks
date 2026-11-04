module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect

/-!
# The strictly perfect dévissage in a contravariant variable

Let `(C, O)` be a ringed site.  `Stacks.Cohomology.ProjectionFormulaPerfectDevissage`
.`isIso_app_of_isStrictlyPerfect` spreads the invertibility of a natural transformation from the
shifts of the structure sheaf to every shift of every strictly perfect complex, for natural
transformations between **covariant** exact functors out of `D(O)`.  This file restates it for a
natural transformation between two **contravariant** functors `D(O)ᵒᵖ ⥤ D(O)`.

Nothing mathematical is added: a contravariant functor `F : D(O)ᵒᵖ ⥤ D(O)` is the same thing as
the covariant `F.rightOp : D(O) ⥤ D(O)ᵒᵖ`, the opposite of a pretriangulated category is
pretriangulated, and `CategoryTheory.NatTrans.rightOp` turns `α : F ⟶ G` into
`α.rightOp : G.rightOp ⟶ F.rightOp` with `α.rightOp.app L = (α.app (op L)).op`, whose
invertibility is that of `α.app (op L)` by `CategoryTheory.isIso_op_iff`.  What the restatement
buys is that the dévissage becomes applicable without the caller having to perform that
translation, which is where the structural data have to be produced in the opposite category.

## Main results

* `Stacks.Cohomology.ContravariantDevissage.isIso_app_op_of_isStrictlyPerfect`: the engine, with
  the base case asked for at every shift of the structure sheaf placed in every degree.
* `Stacks.Cohomology.ContravariantDevissage.isIso_app_op_of_isStrictlyPerfect_of_singleUnit`: the
  same with the base case asked for only at the unshifted structure sheaf in each degree, the
  shifts there being redundant.

## Implementation notes

*The structural data are explicit arguments, and they are the data of the `rightOp` functors.*
`CategoryTheory.Functor.IsTriangulated` is defined relative to a chosen
`CategoryTheory.Functor.CommShift`, and for a contravariant functor the shift that matters is the
one of `D(O)ᵒᵖ`; so the hypotheses below are a `CommShift` and an `IsTriangulated` for
`F.rightOp` and `G.rightOp` as functors `D(O) ⥤ D(O)ᵒᵖ`, not for `F` and `G` themselves.  They
are explicit arguments rather than instances for the same reason as in the covariant engine: the
shift compatibility of the derived tensor product of [Stacks, Tag 06YU] arrives as a field of a
structure rather than as a global instance.

*No consumer is supplied here.*  The two intended consumers are the canonical map
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom` of [Stacks, Tag 08JD], contravariant
in the dualized object, and the derived internal Hom into a fixed object.  For neither of them
does this library contain the `CommShift` hypothesis below: the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated` record that no
`CommShift` exists for the derived internal Hom in either variable, and the conditional dévissage
steps of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualTriangulated` carry the
same data as unavailable instance hypotheses.  What *is* available unconditionally is the
triangle half, `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`
([Stacks, Tag 08JC], contravariant variable), which produces a distinguished triangle with an
existentially quantified connecting morphism; that is strictly weaker than
`Functor.IsTriangulated`, and the gap between them — a connecting morphism chosen compatibly on
the two sides of the natural transformation — is exactly what the five lemma
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_of_five` needs for its third square and
does not get.

*No `@[stacks]` attribute is attached*, and no assertion of any tag is proved here: what is
below is the covariant engine read through an equivalence of functor categories.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.Cohomology.ContravariantDevissage

open Stacks.Cohomology.ProjectionFormulaPerfectDevissage

universe u w

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Invertibility on the shifts of the structure sheaf spreads to strictly perfect complexes,
contravariantly.**  A natural transformation between two contravariant functors
`D(O)ᵒᵖ ⥤ D(O)` whose `rightOp` forms are shift-compatible exact functors `D(O) ⥤ D(O)ᵒᵖ`, and
which is invertible at the structure sheaf placed in an arbitrary degree and shifted by an
arbitrary amount, is invertible at every shift of every strictly perfect complex of `O`-modules
([Stacks, Tag 08FL]).

This is
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage.isIso_app_of_isStrictlyPerfect` applied to
`G.rightOp ⟶ F.rightOp`, whose target category is the pretriangulated category `D(O)ᵒᵖ`; the
component of `α.rightOp` at `L` is the opposite of the component of `α` at `op L`, and a
morphism is invertible exactly when its opposite is. -/
theorem isIso_app_op_of_isStrictlyPerfect
    (F G : (DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hGs : G.rightOp.CommShift ℤ) (hFs : F.rightOp.CommShift ℤ)
    (hGt : letI := hGs; G.rightOp.IsTriangulated)
    (hFt : letI := hFs; F.rightOp.IsTriangulated)
    (α : F ⟶ G)
    (hunit : ∀ i n : ℤ, IsIso (α.app (op ((singleUnit O i)⟦n⟧))))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K) (n : ℤ) :
    IsIso (α.app (op ((DerivedCategory.Q.obj K)⟦n⟧))) :=
  (isIso_op_iff _).1
    (isIso_app_of_isStrictlyPerfect O G.rightOp F.rightOp hGs hFs hGt hFt α.rightOp
      (fun i m => (isIso_op_iff _).2 (hunit i m)) K hK n)

/-- **The contravariant dévissage with its base case asked for only at the unshifted structure
sheaf in each degree.**  `isIso_app_op_of_isStrictlyPerfect` quantifies its base case over all
shifts because the extension step needs the induction hypothesis at all shifts; at the structure
sheaf the shifts are redundant, by
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage.singleUnitShiftIso`. -/
theorem isIso_app_op_of_isStrictlyPerfect_of_singleUnit
    (F G : (DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hGs : G.rightOp.CommShift ℤ) (hFs : F.rightOp.CommShift ℤ)
    (hGt : letI := hGs; G.rightOp.IsTriangulated)
    (hFt : letI := hFs; F.rightOp.IsTriangulated)
    (α : F ⟶ G)
    (hunit : ∀ i : ℤ, IsIso (α.app (op (singleUnit O i))))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K) (n : ℤ) :
    IsIso (α.app (op ((DerivedCategory.Q.obj K)⟦n⟧))) :=
  (isIso_op_iff _).1
    (isIso_app_of_isStrictlyPerfect_of_singleUnit O G.rightOp F.rightOp hGs hFs hGt hFt α.rightOp
      (fun i => (isIso_op_iff _).2 (hunit i)) K hK n)

end Stacks.Cohomology.ContravariantDevissage

end
