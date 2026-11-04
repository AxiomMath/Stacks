module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.RegularExt
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.TensorHomComparison

/-!
# The comparison `(- ⊗_A^𝐋 Hom(L, K)) ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K`

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K`, `L` be complexes of `O`-modules with endomorphism
differential graded `R`-algebras `A`, `B`, and let `Ω' = Hom(L, K)` be the differential graded
`(A, B)`-bimodule of `AlgebraicGeometry.RingedSite.homBimodule`. This file constructs the
comparison

`θ : - ⊗_A^𝐋 Ω' ⋙ - ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K`

of functors `D(A, d) ⥤ D(O)`. It comes from the universal property of `- ⊗_A^𝐋 K` as a total left
derived functor (Tag 09LX), applied to the transformation which at a differential graded
`A`-module `P` is

`(P ⊗_A^𝐋 Ω') ⊗_B^𝐋 L ⟶ (P ⊗_A Ω') ⊗_B^𝐋 L ⟶ (P ⊗_A Ω') ⊗_B L ⟶ P ⊗_A K`,

the two comparisons of the derived tensor products with the plain ones followed by the adjoint
of `x ⊗ φ ↦ (x ⊗ -) ∘ φ`, `AlgebraicGeometry.RingedSite.tensorHomComparison`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorHomComparisonComplexes`: the comparison
  `(P ⊗_A Ω') ⊗_B L ⟶ P ⊗_A K` of complexes, natural in `P`.
* `AlgebraicGeometry.RingedSite.tensorHomComparisonHomotopy`: the same on homotopy categories.
* `AlgebraicGeometry.RingedSite.tensorHomComparisonDerived`: the comparison `θ`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomComparisonDerived_app_comp_counit`: the defining
  identity of `θ`.

## References

* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The derived category `D(O)` at the standard model, on which the derived tensor products of
Tag 09LX are built. It is named explicitly because at equal universes instance search would
otherwise find the locally small model. -/
abbrev stdDerivedSite (X : AlgebraicGeometry.RingedSite.{u, u, u}) :=
  @DerivedCategory (TensorModO.{u, u, u, u, u} X) _ _ (HasDerivedCategory.standard _)

/-- The localization functor `K(O) ⥤ D(O)` at the standard model, on which the derived tensor
products of Tag 09LX are built. It is named explicitly because at equal universes instance search
would otherwise find the locally small model. -/
abbrev stdQh (X : AlgebraicGeometry.RingedSite.{u, u, u}) :
    _root_.HomotopyCategory (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ) ⥤
      @DerivedCategory (TensorModO.{u, u, u, u, u} X) _ _ (HasDerivedCategory.standard _) :=
  @DerivedCategory.Qh _ _ _ (HasDerivedCategory.standard _)

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, u} X R]
  (K L : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- The derived tensor product `- ⊗_A^𝐋 Hom(L, K) : D(A, d) ⥤ D(B, d)` of Tag 09LS, read between
the derived categories `DifferentialGradedModule.derivedCategory` on which the derived tensor
products with complexes of Tag 09LX are formed. The two derived categories of a differential
graded algebra in this library are one category at equal universes; this only fixes the
category instances. -/
abbrev derivedTensorHom :
    DifferentialGradedModule.derivedCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra ⥤
      DifferentialGradedModule.derivedCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra :=
  DifferentialGraded.Bimodule.derivedTensorFunctor (homBimodule X R K L)

/-- **The comparison `(P ⊗_A Hom(L, K)) ⊗_B L ⟶ P ⊗_A K` of complexes of `O`-modules**, natural
in the differential graded `A`-module `P`: the adjoint, under the tensor-Hom adjunction for `L`,
of `AlgebraicGeometry.RingedSite.tensorHomComparison`. -/
def tensorHomComparisonComplexes :
    DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L) ⋙
        dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R L).functor ⟶
      dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor where
  app M := ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, u, u, u, u, u} X R L).homEquiv
    _ _).symm (tensorHomComparison X R K L M)
  naturality M M' f := by
    change (dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R L).functor).map
        ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).map f) ≫ _ = _
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
      tensorHomComparison_naturality]

/-- The adjoint of the comparison of complexes is
`AlgebraicGeometry.RingedSite.tensorHomComparison`. -/
theorem tensorHomComparisonComplexes_homEquiv
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) :
    (tensorWithComplexComplexes_adj_homWithComplexOver.{u, u, u, u, u, u} X R L).homEquiv _ _
        ((tensorHomComparisonComplexes X R K L).app M) = tensorHomComparison X R K L M :=
  Equiv.apply_symm_apply _ _

/-- **The comparison on homotopy categories**, `(P ⊗_A Hom(L, K)) ⊗_B L ⟶ P ⊗_A K` as a
transformation of functors `K(A, d) ⥤ K(O)`. -/
def tensorHomComparisonHomotopy :
    DifferentialGraded.Bimodule.tensorHomotopyFunctor (homBimodule X R K L) ⋙
        tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L ⟶
      tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K :=
  CategoryTheory.Quotient.natTransLift _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (DifferentialGraded.Bimodule.tensorCompFunctor_quotient (homBimodule X R K L)).inv
        (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L))
        (eqToHom (tensorWithComplexHomotopy_spec.{u, u, u, u, u, u} X R L)) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (tensorHomComparisonComplexes X R K L)
        (HomotopyCategory.quotient _ _) ≫
      eqToHom (tensorWithComplexHomotopy_spec.{u, u, u, u, u, u} X R K).symm)

/-- The transformation of functors `K(A, d) ⥤ D(O)` from which the comparison `θ` is derived:
`(P ⊗_A^𝐋 Ω') ⊗_B^𝐋 L ⟶ (P ⊗_A Ω') ⊗_B^𝐋 L ⟶ (P ⊗_A Ω') ⊗_B L ⟶ P ⊗_A K`. -/
def tensorHomComparisonDerivedAux :
    (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra).Q ⋙
        (derivedTensorHom X R K L ⋙ tensorWithComplexDerived.{u, u, u, u, u, u} X R L) ⟶
      tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R K :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (DifferentialGraded.Bimodule.derivedTensorFunctorCounit (homBimodule X R K L))
      (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) ≫
    (show (DifferentialGraded.Bimodule.tensorHomotopyFunctor (homBimodule X R K L) ⋙
        (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q) ⋙
          tensorWithComplexDerived.{u, u, u, u, u, u} X R L ⟶
        DifferentialGraded.Bimodule.tensorHomotopyFunctor (homBimodule X R K L) ⋙
          tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R L from
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (DifferentialGraded.Bimodule.tensorHomotopyFunctor (homBimodule X R K L))
          (tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L)) ≫
    (show DifferentialGraded.Bimodule.tensorHomotopyFunctor (homBimodule X R K L) ⋙
        (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L ⋙ stdQh X) ⟶
        tensorWithComplexHomotopy.{u, u, u, u, u, u} X R K ⋙ stdQh X from
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorHomComparisonHomotopy X R K L) (stdQh X))

/-- **The comparison `θ : - ⊗_A^𝐋 Hom(L, K) ⋙ - ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K`** of functors
`D(A, d) ⥤ D(O)`, induced by `AlgebraicGeometry.RingedSite.tensorHomComparisonDerivedAux`
through the universal property of `- ⊗_A^𝐋 K` as a total left derived functor (Tag 09LX). -/
def tensorHomComparisonDerived :
    derivedTensorHom X R K L ⋙ tensorWithComplexDerived.{u, u, u, u, u, u} X R L ⟶
      tensorWithComplexDerived.{u, u, u, u, u, u} X R K :=
  (tensorWithComplexDerived.{u, u, u, u, u, u} X R K).leftDerivedLift
    (tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R K)
    (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) _
    (tensorHomComparisonDerivedAux X R K L)

/-- The defining identity of `θ`: at the class of a differential graded `A`-module, `θ` followed
by the comparison of `- ⊗_A^𝐋 K` with plain tensoring is
`AlgebraicGeometry.RingedSite.tensorHomComparisonDerivedAux`. -/
theorem tensorHomComparisonDerived_app_comp_counit
    (P : DifferentialGradedModule.HomotopyCategory.{u, u, u}
      (Rep.{u, u, u, u, u, u} X R K).algebra) :
    (tensorHomComparisonDerived X R K L).app
        ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj P) ≫
      (tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R K).app P =
      (tensorHomComparisonDerivedAux X R K L).app P :=
  Functor.leftDerived_fac_app _ _ _ _ _ P

end AlgebraicGeometry.RingedSite

end
