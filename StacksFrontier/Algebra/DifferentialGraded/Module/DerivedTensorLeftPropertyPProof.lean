module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorQuasiIsoDevissage

/-! # Derived tensoring with a bimodule with property (P) on the left

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule which has property (P) as a *left* differential graded
`A`-module. **Stacks Tag 0GZ2** asserts that `M ⊗_A^𝐋 N` is then computed by `M ⊗_A N` for every
differential graded `A`-module `M`: the comparison of Tag 09LS from the derived to the plain
tensor product is invertible.

The key input is that tensoring with such an `N` carries quasi-isomorphisms of differential
graded `A`-modules to quasi-isomorphisms.

## Main results

* `DifferentialGraded.Bimodule.leftPropertyPPreservesQuasiIso`: a bimodule with property (P) as a
  left differential graded `A`-module carries quasi-isomorphisms to quasi-isomorphisms.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_of_leftPropertyP`: **Tag 0GZ2** as
  the invertibility of the comparison of Tag 09LS, as an isomorphism of functors.
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftPropertyP'`:
  **Tag 0GZ2** in the form the source states it — for every differential graded `A`-module `M` the
  comparison `M ⊗_A^𝐋 N ⟶ M ⊗_A N` is an isomorphism in `D(B, d)`.
* `DifferentialGraded.Bimodule.derivedTensorIsoOfLeftPropertyP'`: the resulting isomorphism
  `- ⊗_A^𝐋 N ≅ - ⊗_A N` of functors `D(A, d) ⥤ D(B, d)`.

## References

* [Stacks Project, Tag 0GZ2](https://stacks.math.columbia.edu/tag/0GZ2); the construction it
  invokes is [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), the claim it needs is the
  second assertion of [Tag 09S3](https://stacks.math.columbia.edu/tag/09S3), property (P) is
  [Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), the identification of left modules with
  right modules over the opposite is [Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0) and the
  invariance of the relative tensor product under restriction of the right action is
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX).
-/


@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### Tensoring with the flipped bimodule -/

/-- The bimodule `N` with its right action restricted along `R → B` to the base ring in degree
zero. -/
abbrev restrictBase (N : Bimodule A B) : Bimodule A (degreeZero R R) :=
  Bimodule.restrictRight (baseHom B) N

/-- Restricting the right action to the base ring does not change the complex of `R`-modules
underlying the relative tensor product. -/
def tensorRestrictBaseForgetIso (N : Bimodule A B) :
    tensorCompFunctor (restrictBase N) ⋙ forgetToCochainComplex (degreeZero R R) ≅
      tensorCompFunctor N ⋙ forgetToCochainComplex B :=
  Functor.isoWhiskerRight (tensorCompFunctorRestrictRightIso (baseHom B) N)
      (forgetToCochainComplex (degreeZero R R)) ≪≫
    eqToIso (by
      rw [Functor.assoc, restrictScalarsFunctor_comp_forget])

/-- The left differential graded `A`-module read over `A^{opp}` is unchanged by restricting the
right action of the bimodule to the base ring. -/
theorem flipModule_restrictBase (N : Bimodule A B) :
    flipModule (restrictBase N) =
      (leftRightEquivalence R A).equivalence.functor.obj (toLeftModule A B N) := rfl

/-! ### Tensoring with a bimodule with property (P) preserves quasi-isomorphisms -/

/-- A differential graded `(A, B)`-bimodule with property (P) as a left differential graded
`A`-module carries quasi-isomorphisms of differential graded `A`-modules to quasi-isomorphisms. -/
theorem leftPropertyPPreservesQuasiIso (A B : DifferentialGradedAlgebra.{u, u} R) :
    LeftPropertyPPreservesQuasiIso A B := by
  intro N hP M M' f hf
  have hPfl : Nonempty (PropertyPFiltration (flipModule (restrictBase N))) := hP
  have hq : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map (flipMap f).rightHom) := by
    have h : @Eq (M.toCochainComplex ⟶ M'.toCochainComplex)
        (restrictScalarsHom (baseHom A) f).toCochainMap f.toCochainMap :=
      restrictScalarsHom_toCochainMap (baseHom A) f
    have h' : (forgetToCochainComplex (degreeZero R R)).map (flipMap f).rightHom =
        (forgetToCochainComplex A).map f := h
    rw [h']
    exact hf
  have hiso : IsIso (derivedTensorNatTrans (flipMap f)) :=
    quasiIsoInvertsDerivedTensor (oppAlgebra A) (degreeZero R R) (flipMap f) hq
  have hc : ∀ M'' : DifferentialGradedModule A, IsIso ((derivedTensorFunctorCounit (flip M'')).app
      ((toHomotopyCategory (oppAlgebra A)).obj (flipModule (restrictBase N)))) := fun M'' =>
    isIso_derivedTensorFunctorCounit_app_of_propertyP (flip M'') _ hPfl
  have hcl := hc M
  have hcr := hc M'
  have hcomp : IsIso ((derivedTensorFunctorCounit (flip M)).app
        ((toHomotopyCategory (oppAlgebra A)).obj (flipModule (restrictBase N))) ≫
      (ordinaryTensorNatTrans (flipMap f)).app
        ((toHomotopyCategory (oppAlgebra A)).obj (flipModule (restrictBase N)))) := by
    rw [← derivedTensorNatTrans_app_comp_counit]
    infer_instance
  have hord : IsIso ((ordinaryTensorNatTrans (flipMap f)).app
      ((toHomotopyCategory (oppAlgebra A)).obj (flipModule (restrictBase N)))) :=
    IsIso.of_isIso_comp_left ((derivedTensorFunctorCounit (flip M)).app
      ((toHomotopyCategory (oppAlgebra A)).obj (flipModule (restrictBase N)))) _
  have hplain : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map
      (tensorHomOfBimoduleHom (flipMap f) (flipModule (restrictBase N)))) := by
    rw [← isIso_q_map_toHomotopyCategory_map_iff (degreeZero R R)
      (tensorHomOfBimoduleHom (flipMap f) (flipModule (restrictBase N)))]
    rw [ordinaryTensorNatTrans_app, tensorHomotopyNatTrans_app, Functor.map_comp,
      Functor.map_comp] at hord
    have h3 : IsIso ((quasiIsomorphisms' (degreeZero R R)).Q.map
        ((toHomotopyCategory (degreeZero R R)).map
          ((tensorModuleNatTrans (flipMap f)).app (flipModule (restrictBase N)))) ≫
      (quasiIsomorphisms' (degreeZero R R)).Q.map
        ((tensorCompFunctor_quotient (flip M')).hom.app (flipModule (restrictBase N)))) :=
      IsIso.of_isIso_comp_left ((quasiIsomorphisms' (degreeZero R R)).Q.map
        ((tensorCompFunctor_quotient (flip M)).inv.app (flipModule (restrictBase N)))) _
    exact IsIso.of_isIso_comp_right
      ((quasiIsomorphisms' (degreeZero R R)).Q.map
        ((toHomotopyCategory (degreeZero R R)).map
          ((tensorModuleNatTrans (flipMap f)).app (flipModule (restrictBase N)))))
      ((quasiIsomorphisms' (degreeZero R R)).Q.map
        ((tensorCompFunctor_quotient (flip M')).hom.app (flipModule (restrictBase N))))
  have harr : Arrow.mk ((tensorCompFunctor (restrictBase N)).map f) ≅
      Arrow.mk (tensorHomOfBimoduleHom (flipMap f) (flipModule (restrictBase N))) :=
    Arrow.isoMk (tensorFlipIso (restrictBase N) M) (tensorFlipIso (restrictBase N) M')
      (tensorFlipIso_naturality (restrictBase N) f).symm
  have hV' : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map
      ((tensorCompFunctor (restrictBase N)).map f)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      ((forgetToCochainComplex (degreeZero R R)).mapArrow.mapIso harr)).mpr hplain
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk ((tensorRestrictBaseForgetIso N).app M) ((tensorRestrictBaseForgetIso N).app M')
      ((tensorRestrictBaseForgetIso N).hom.naturality f).symm)).mp hV'

/-! ### Stacks 0GZ2 -/

/-- For a differential graded `(A, B)`-bimodule `N` with property (P) as a left differential
graded `A`-module, the comparison `- ⊗_A^𝐋 N ⟶ - ⊗_A N` of Tag 09LS is an isomorphism of
functors. -/
theorem isIso_derivedTensorFunctorCounit_of_leftPropertyP (N : Bimodule A B)
    (hP : LeftPropertyP N) : IsIso (derivedTensorFunctorCounit N) :=
  isIso_derivedTensorFunctorCounit_of_preservesQuasiIso N
    (leftPropertyPPreservesQuasiIso A B N hP)

/-- For a differential graded `(A, B)`-bimodule `N` with property (P) as a left differential
graded `A`-module and every differential graded `A`-module `M`, the comparison
`M ⊗_A^𝐋 N ⟶ M ⊗_A N` of Tag 09LS is an isomorphism in `D(B, d)`. -/
@[stacks 0GZ2]
theorem isIso_derivedTensorFunctorCounit_app_of_leftPropertyP' (N : Bimodule A B)
    (hP : LeftPropertyP N) (M : DifferentialGradedModule A) :
    IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj M)) :=
  isIso_derivedTensorFunctorCounit_app_of_leftPropertyP
    (leftPropertyPPreservesQuasiIso A B) N hP M

/-- For a differential graded `(A, B)`-bimodule `N` with property (P) as a left differential
graded `A`-module, the isomorphism `- ⊗_A^𝐋 N ≅ - ⊗_A N` of functors `D(A, d) ⥤ D(B, d)`. -/
@[stacks 0GZ2 "as an isomorphism of functors"]
def derivedTensorIsoOfLeftPropertyP' (N : Bimodule A B) (hP : LeftPropertyP N) :
    (quasiIsomorphisms' A).Q ⋙ derivedTensorFunctor N ≅ tensorFunctorToDerivedCategory N :=
  derivedTensorIsoOfLeftPropertyP (leftPropertyPPreservesQuasiIso A B) N hP

end DifferentialGraded.Bimodule

end
