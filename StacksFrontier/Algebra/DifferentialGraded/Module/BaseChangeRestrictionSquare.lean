module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeBimoduleRepresents
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeUnitAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictLeft
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductHomPair
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIsoNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorRestrictRight

/-! # Restriction of scalars commutes with derived base change

Let `R → R'` be a map of commutative rings, let `(A, d)` be a differential graded `R`-algebra
and let `A' = A ⊗_R R'` be its base change. **Stacks 0BYZ, part (2)** asserts that if `A` is
K-flat as a complex of `R`-modules then the square
```
D(A, d) --- - ⊗_A^𝐋 A' ---> D(A', d)
   |                           |
restriction                restriction
   v                           v
 D(R)  --- - ⊗_R^𝐋 R' --->   D(R')
```
commutes. This file proves it, as
`DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare`.

The argument is the source's. For a differential graded `A`-module `M` the canonical map
`c_M : M|_R ⊗_R R' → M ⊗_A A'` is an isomorphism — over `R'`, and for every `M`, both sides
being the absolute tensor product `M ⊗_R R'` of `DifferentialGraded.absBalanceIso`. So the two
composites of the square left-derive isomorphic functors out of `K(A, d)`, and it remains to
know that the left-hand composite really is a left derived functor. That is where the K-flatness
of `A` enters: the comparison it carries is invertible at a differential graded `A`-module with
property (P), because such a module is K-flat as a complex of `R`-modules when `A` is, and
part (3) then applies over the base ring; and the modules with property (P) resolve every object
of `K(A, d)`, so a comparison invertible at them exhibits a left derived functor.

## Main definitions

* `DifferentialGraded.Bimodule.baseChangeStructureRightHom` and
  `DifferentialGraded.Bimodule.baseChangeStructureBimoduleHom`: the map `R ⊗_R R' → A ⊗_R R'`,
  as a homomorphism of right differential graded `R'`-modules and as a `R → A`-semilinear
  homomorphism of differential graded `(R, R')`-bimodules.
* `DifferentialGraded.Bimodule.baseChangeStructureTensorTrans`: the canonical map
  `c_M : M|_R ⊗_R (R ⊗_R R') ⟶ M ⊗_A (A ⊗_R R')` of the proof of Stacks 0BYZ, over `R'`,
  natural in `M`.
* `DifferentialGraded.Bimodule.baseChangeStructureDerivedTrans`: the comparison of the derived
  tensor functors that `c` induces by the universal property of Tag 09LS.
* `DifferentialGraded.Bimodule.propertyPObjects`: property (P), as a property of objects of
  `K(A, d)`.

## Main results

* `DifferentialGraded.Bimodule.isIso_baseChangeStructureTensorTrans_app`: **`c_M` is an
  isomorphism for every `M`**, nothing being assumed of `A`, of `M` or of `R'`.
* `DifferentialGraded.Bimodule.isIso_baseChangeStructureDerivedTrans`: the induced comparison of
  the derived tensor functors is invertible when `A` is K-flat over `R`.
* `DifferentialGraded.Bimodule.baseChangeBimoduleDerivedIso`: derived tensoring with the
  bimodule `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4 is derived base change followed by restriction of
  the action to `R'` — the top edge followed by the right-hand column.
* `DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare`: **Stacks 0BYZ, part (2).**

## Implementation notes

*Why `c_M` is an isomorphism for every `M`, when the source only claims it for property-(P)
modules.* The source's `c_M` is a map of differential graded `A'`-modules, and its `A'`-linearity
is not formalized in this tree; what is formalized is the map after restricting the right action
from `A'` to `R'`, and there both sides are the absolute tensor product `M ⊗_R R'` outright, by
`DifferentialGraded.absBalanceIso` over `A` and over `R`. The property-(P) hypothesis the source
attaches to the claim is needed for the *other* half of its claim — that `P` is K-flat as a
complex of `R`-modules — which is
`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration` and is what is used
here.

*Where the K-flatness of `A` is consumed.* Only in
`DifferentialGraded.Bimodule.isIso_derivedTensorRestrictTransQuotient_app_of_propertyP`, through
`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration` and
`DifferentialGraded.Bimodule.isIso_derivedTensorBimoduleCounit_app_of_kFlat`. The comparison of
the plain functors, the factorization of derived restriction and the K-flatness of `R` in degree
zero over itself cost nothing.

*Which spelling of `D(R)` and `D(R')` is used.* Both are derived categories of differential
graded modules over the base ring placed in degree zero (Tag 09JJ), `D(degreeZero R R, d)` and
`D(degreeZero R R', d)`; `DifferentialGradedModule.degreeZeroDerivedEquivalence` identifies them
with the derived categories of modules. The bottom edge of the square is derived base change of
`degreeZero R R`, which lands in `D(R ⊗_R R', d)`, followed by the equivalence
`DifferentialGradedModule.degreeZeroBaseChangeEquivalence` onto `D(R', d)` — restriction of
scalars along the unitor, which
`DifferentialGraded.Bimodule.derivedBaseChangeRestrictionSquare_bottom` records.

*Universes.* As everywhere in the bimodule stack of this tree, the base ring, the algebras and
the modules are taken in a single universe.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), part (2).
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), the derived tensor
  product and its universal property, and
  [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) the comparison with the plain one.
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change
  bimodule, and [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars.
* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP), resolutions by modules
  with property (P), and [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM), their
  orthogonality.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- `r ⊗ r' ↦ 1·r ⊗ r'`, from `R ⊗_R R'` to `A ⊗_R R'`: the tensor product of the structure
homomorphism `R → A` with the identity of `R'`, read as a homomorphism of right differential
graded `R'`-modules. -/
def baseChangeStructureRightHom :
    (baseChangeBimodule (degreeZero R R) (degreeZero R R')).rightModule ⟶
      (baseChangeBimodule A (degreeZero R R')).rightModule where
  toFun := (tensorHomPair (baseHom A)
    (idHom (degreeZero R R'))).toAlgebraHom.toLinearMap
  map_smul x a := by
    rw [baseChangeBimodule_op_smul, baseChangeBimodule_op_smul]
    change (tensorHomPair (baseHom A) (idHom (degreeZero R R'))).toAlgebraHom
        (_ * _) = _
    rw [map_mul, tensorHomPair_tmul, map_one]
    rfl
  map_grading n x hx :=
    (tensorHomPair (baseHom A) (idHom (degreeZero R R'))).map_grading n x hx
  map_d := by
    ext x
    exact (tensorHomPair (baseHom A) (idHom (degreeZero R R'))).map_d x

/-- **`R ⊗_R R' → A ⊗_R R'` is a homomorphism of differential graded `(R, R')`-bimodules over
the structure homomorphism `R → A`**: the left `R`-action is multiplication by `r ⊗ 1` on either
side, and the map sends `r ⊗ 1` to `1·r ⊗ 1`. -/
def baseChangeStructureBimoduleHom :
    baseChangeBimodule (degreeZero R R) (degreeZero R R') ⟶
      Bimodule.restrictLeft (baseHom A)
        (baseChangeBimodule A (degreeZero R R')) where
  rightHom := baseChangeStructureRightHom A R'
  map_left n p a x := by
    rw [baseChangeBimodule_leftAction (degreeZero R R) (degreeZero R R') n p a x]
    refine Eq.trans ?_ (baseChangeBimodule_leftAction A (degreeZero R R') n p
      ((baseHom A).gradingMap n a)
      ((baseChangeStructureRightHom A R').gradedMap p x)).symm
    change (tensorHomPair (baseHom A) (idHom (degreeZero R R'))).toAlgebraHom
        (_ * _) = _
    rw [map_mul, tensorHomPair_tmul, map_one, Hom.gradingMap_coe]
    rfl

/-- **The comparison of the plain tensor functors**: for a differential graded `A`-module `M`,
the comparison `M|_R ⊗_R (R ⊗_R R') ⟶ M ⊗_A (A ⊗_R R')` of right differential graded
`R'`-modules, natural in `M`. This is the canonical map `c_M` of the proof of Stacks 0BYZ, read
over `R'`. -/
def baseChangeStructureTensorTrans :
    restrictScalarsFunctor (baseHom A) ⋙
        tensorCompFunctor (baseChangeBimodule (degreeZero R R) (degreeZero R R')) ⟶
      tensorCompFunctor (baseChangeBimodule A (degreeZero R R')) :=
  tensorCompNatTransOfSemilinear (baseHom A)
    (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
    (baseChangeBimodule A (degreeZero R R'))
    (baseChangeStructureBimoduleHom A R')

/-- Unbalancing `M ⊗_R R'` over `R` and over `A` give the same element: the right action of `r`
on the restriction `M|_R` is the right action of `1·r` on `M`. -/
theorem absUnbalance_baseChangeStructureRightHom (M : DifferentialGradedModule.{u, u, u} A)
    (x : M.M) (y : (degreeZero R R).grading ᵍ⊗[R] (degreeZero R R').grading) :
    absUnbalance A (degreeZero R R') M x
        ((tensorHomPair (baseHom A) (idHom (degreeZero R R'))).toAlgebraHom y) =
      absUnbalance (degreeZero R R) (degreeZero R R')
        ((restrictScalarsFunctor (baseHom A)).obj M) x y := by
  induction y using gradedTensor_induction with
  | tmul r c =>
    rw [tensorHomPair_tmul, absUnbalance_tmul]
    exact (absUnbalance_tmul (degreeZero R R) (degreeZero R R')
      ((restrictScalarsFunctor (baseHom A)).obj M) x r c).symm
  | add z w hz hw =>
    rw [map_add ((tensorHomPair (baseHom A)
      (idHom (degreeZero R R'))).toAlgebraHom), map_add, map_add, hz, hw]
    rfl

/-- The comparison of the plain tensor functors on a pure tensor: `x ⊗ y ↦ x ⊗ (1·y)`. -/
theorem baseChangeStructureTensorTrans_app_pure (M : DifferentialGradedModule.{u, u, u} A)
    (x : ((restrictScalarsFunctor (baseHom A)).obj M).M)
    (y : (baseChangeBimodule (degreeZero R R) (degreeZero R R')).rightModule.M) :
    ((baseChangeStructureTensorTrans A R').app M).toFun
        (absRelativePureBilinear (degreeZero R R) (degreeZero R R')
          ((restrictScalarsFunctor (baseHom A)).obj M) x y) =
      absRelativePureBilinear A (degreeZero R R') M x
        ((baseChangeStructureRightHom A R').toFun y) :=
  tensorCompNatTransOfSemilinear_app_pure (baseHom A)
    (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
    (baseChangeBimodule A (degreeZero R R'))
    (baseChangeStructureBimoduleHom A R') M x y

/-- **The comparison of the plain tensor functors is the identification of both sides with
`M ⊗_R R'`.** Both `M|_R ⊗_R (R ⊗_R R')` and `M ⊗_A (A ⊗_R R')` are the absolute tensor product
`M ⊗_R R'` by `DifferentialGraded.absBalanceIso`, and the comparison is compatible with those
two identifications. -/
theorem baseChangeStructureTensorTrans_app_comp_absBalance
    (M : DifferentialGradedModule.{u, u, u} A) :
    (baseChangeStructureTensorTrans A R').app M ≫ (absBalanceIso A (degreeZero R R') M).hom =
      (absBalanceIso (degreeZero R R) (degreeZero R R')
        ((restrictScalarsFunctor (baseHom A)).obj M)).hom := by
  refine tensorObj_hom_ext' (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
    ((restrictScalarsFunctor (baseHom A)).obj M) _ _ fun x y => ?_
  change (absBalanceForward A (degreeZero R R') M).toFun
      (((baseChangeStructureTensorTrans A R').app M).toFun
        (absRelativePureBilinear (degreeZero R R) (degreeZero R R')
          ((restrictScalarsFunctor (baseHom A)).obj M) x y)) =
    (absBalanceForward (degreeZero R R) (degreeZero R R')
      ((restrictScalarsFunctor (baseHom A)).obj M)).toFun
      (absRelativePureBilinear (degreeZero R R) (degreeZero R R')
        ((restrictScalarsFunctor (baseHom A)).obj M) x y)
  rw [baseChangeStructureTensorTrans_app_pure]
  exact (absBalanceForward_pure A (degreeZero R R') M x _).trans
    ((absUnbalance_baseChangeStructureRightHom A R' M x y).trans
      (absBalanceForward_pure (degreeZero R R) (degreeZero R R')
        ((restrictScalarsFunctor (baseHom A)).obj M) x y).symm)

/-- **The comparison of the plain tensor functors is the composite of the two identifications
with `M ⊗_R R'`.** -/
theorem baseChangeStructureTensorTrans_app_eq (M : DifferentialGradedModule.{u, u, u} A) :
    (baseChangeStructureTensorTrans A R').app M =
      (absBalanceIso (degreeZero R R) (degreeZero R R')
          ((restrictScalarsFunctor (baseHom A)).obj M)).hom ≫
        (absBalanceIso A (degreeZero R R') M).inv :=
  (Iso.eq_comp_inv (absBalanceIso A (degreeZero R R') M)).2
    (baseChangeStructureTensorTrans_app_comp_absBalance A R' M)

/-- **The canonical map `c_M` is an isomorphism for every `M`**, no hypothesis on `A`, on `M` or
on `R'`: both sides are the absolute tensor product `M ⊗_R R'`. -/
instance isIso_baseChangeStructureTensorTrans_app
    (M : DifferentialGradedModule.{u, u, u} A) :
    IsIso ((baseChangeStructureTensorTrans A R').app M) := by
  rw [baseChangeStructureTensorTrans_app_eq]
  exact ((absBalanceIso (degreeZero R R) (degreeZero R R')
      ((restrictScalarsFunctor (baseHom A)).obj M)) ≪≫
    (absBalanceIso A (degreeZero R R') M).symm).isIso_hom

/-! ### Property (P) as a resolving class -/

/-- The differential graded modules with property (P), read as a property of objects of
`K(A, d)`. -/
def propertyPObjects : ObjectProperty (HomotopyCategory A) :=
  fun X => Nonempty (PropertyPFiltration X.as)

/-- **Stacks 09KP on the homotopy category.** Every object of `K(A, d)` receives a
quasi-isomorphism from an object with property (P). -/
theorem exists_propertyPObjects_resolution (X : HomotopyCategory A) :
    ∃ (Y : HomotopyCategory A) (_ : propertyPObjects A Y) (f : Y ⟶ X),
      quasiIsomorphisms' A f := by
  obtain ⟨P, f, hf, hFP⟩ := DifferentialGradedModule.exists_propertyP_resolution A X.as
  exact ⟨(toHomotopyCategory A).obj P, hFP, (toHomotopyCategory A).map f,
    (quasiIsomorphisms_map_iff' A f).2 hf⟩

/-- Plain tensoring inverts the quasi-isomorphisms between objects with property (P), those
being orthogonal on the left to the acyclic modules by Tag 09KM. -/
theorem isIso_tensorFunctorToDerivedCategory_map_of_propertyPObjects
    {B : DifferentialGradedAlgebra.{u, u} R} (N : Bimodule A B)
    {X Y : HomotopyCategory A} (f : X ⟶ Y) (hf : quasiIsomorphisms' A f)
    (hX : propertyPObjects A X) (hY : propertyPObjects A Y) :
    IsIso ((tensorFunctorToDerivedCategory N).map f) :=
  isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal N f hf
    (leftOrthogonal_acyclic_of_propertyP hX.some) (leftOrthogonal_acyclic_of_propertyP hY.some)

/-! ### The comparison of the derived tensor functors -/

/-- The comparison of the derived functors `- |_R ⊗_R^𝐋 (R ⊗_R R') ⟶ - ⊗_A^𝐋 (A ⊗_R R')`
attached by Tag 09LS to the comparison `c_M` of the plain ones. -/
def baseChangeStructureDerivedTrans :
    derivedRestriction (baseHom A) ⋙
        derivedTensorFunctor (baseChangeBimodule (degreeZero R R) (degreeZero R R')) ⟶
      derivedTensorFunctor (baseChangeBimodule A (degreeZero R R')) :=
  derivedTensorRestrictTrans (baseHom A)
    (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
    (baseChangeBimodule A (degreeZero R R'))
    (baseChangeStructureTensorTrans A R')

/-- **The comparison is invertible at a module with property (P).** *This is where the source's
K-flatness hypothesis on `A` is consumed*: a differential graded `A`-module `P` with property (P)
is K-flat as a complex of `R`-modules when `A` is
(`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration`), and restriction of
scalars does not change that complex, so the comparison of Tag 09LS for the base change of
`degreeZero R R` is invertible at `P|_R` by part (3). The two remaining factors are invertible
with no hypothesis: the factorization of derived restriction is an isomorphism, and `c_P` is one
for every `P`. -/
theorem isIso_derivedTensorRestrictTransQuotient_app_of_propertyP
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex)
    (M : DifferentialGradedModule.{u, u, u} A) (hM : Nonempty (PropertyPFiltration M)) :
    IsIso ((derivedTensorRestrictTransQuotient (baseHom A)
      (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
      (baseChangeBimodule A (degreeZero R R'))
      (baseChangeStructureTensorTrans A R')).app ((toHomotopyCategory A).obj M)) := by
  rw [derivedTensorRestrictTransQuotient_app]
  have h2 : IsIso ((derivedTensorFunctorCounit
      (baseChangeBimodule (degreeZero R R) (degreeZero R R'))).app
      ((restrictScalarsHomotopyFunctor (baseHom A)).obj
        ((toHomotopyCategory A).obj M))) :=
    isIso_derivedTensorBimoduleCounit_app_of_kFlat (degreeZero R R) (degreeZero R R')
      (kFlat_regularModule_degreeZero R)
      (restrictScalars (baseHom A) M)
      (kFlat_toCochainComplex_of_propertyPFiltration hA hM.some)
  have h3 : IsIso ((restrictTensorHomotopyTrans (baseHom A)
      (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
      (baseChangeBimodule A (degreeZero R R'))
      (baseChangeStructureTensorTrans A R')).app ((toHomotopyCategory A).obj M)) := by
    rw [restrictTensorHomotopyTrans_app]
    exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _)
      (IsIso.comp_isIso' inferInstance (NatIso.isIso_app_of_isIso _ _))
  infer_instance

/-- **The comparison of the derived tensor functors is invertible.** Both sides are left derived
functors of the same functor out of `K(A, d)`: the right-hand side by Tag 09LS, the left-hand
side because its comparison is invertible at the modules with property (P), which resolve every
object of `K(A, d)`. So the lift exhibiting the comparison is invertible, by the uniqueness of a
left derived functor. -/
theorem isIso_baseChangeStructureDerivedTrans
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex) :
    IsIso (baseChangeStructureDerivedTrans A R') := by
  have hLD : (derivedRestriction (baseHom A) ⋙
      derivedTensorFunctor
        (baseChangeBimodule (degreeZero R R) (degreeZero R R'))).IsLeftDerivedFunctor
      (derivedTensorRestrictTransQuotient (baseHom A)
        (baseChangeBimodule (degreeZero R R) (degreeZero R R'))
        (baseChangeBimodule A (degreeZero R R'))
        (baseChangeStructureTensorTrans A R')) (quasiIsomorphisms' A) :=
    LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
      (quasiIsomorphisms' A) (propertyPObjects A) (exists_propertyPObjects_resolution A)
      (tensorFunctorToDerivedCategory (baseChangeBimodule A (degreeZero R R')))
      (fun f hf hX hY => isIso_tensorFunctorToDerivedCategory_map_of_propertyPObjects A _ f hf
        hX hY)
      (quasiIsomorphisms' A).Q _ _
      (fun X hX => isIso_derivedTensorRestrictTransQuotient_app_of_propertyP A R' hA X.as hX)
  exact ((derivedTensorFunctor (baseChangeBimodule A (degreeZero R R'))
    ).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (derivedTensorFunctorCounit (baseChangeBimodule A (degreeZero R R')))
      (quasiIsomorphisms' A) _ _).1 hLD

/-! ### The commuting square -/

/-- **Derived tensoring with the bimodule `{}_A(A ⊗_R R')_{R'}` of Tag 0BZ4 is derived base
change followed by restriction of the action from `A ⊗_R R'` to `R'`**, that is the composite of
the top edge and the right-hand column of the square of Stacks 0BYZ, part (2). -/
def baseChangeBimoduleDerivedIso :
    derivedTensorFunctor (baseChangeBimodule A (degreeZero R R')) ≅
      derivedBaseChangeFunctor A R' ⋙
        derivedRestriction (tensorIncludeRightHom A (degreeZero R R')) :=
  eqToIso (congrArg derivedTensorFunctor (baseChangeBimodule_eq_restrictRight A R')) ≪≫
    derivedTensorFunctorRestrictRightIso (tensorIncludeRightHom A (degreeZero R R'))
      (baseChange A R')

/-- **Stacks 0BYZ, part (2).** *"Let `R → R'` be a ring map, let `(A, d)` be a differential
graded `R`-algebra, let `(A', d)` be the base change `A ⊗_R R'`. If `A` is K-flat as a complex of
`R`-modules, then the diagram*
```
D(A, d) --- - ⊗_A^𝐋 A' ---> D(A', d)
   |                           |
restriction                restriction
   v                           v
 D(R)  --- - ⊗_R^𝐋 R' --->   D(R')
```
*commutes."*

The two columns are restriction of scalars along the structure homomorphism `R → A` of
`DifferentialGradedAlgebra.baseHom` and along `r' ↦ 1 ⊗ r'`; the bottom edge is
derived base change of the base ring in degree zero, read in `D(R', d)` through
`DifferentialGradedAlgebra.degreeZeroBaseChangeUnitor`, whose derived restriction is the
equivalence `DifferentialGradedModule.degreeZeroBaseChangeEquivalence`.

Both composites are left derived functors of the same functor `K(A, d) ⥤ D(R', d)`,
`M ↦ M ⊗_R R'`: the comparison `c_M` of the plain functors is an isomorphism for every `M`
(`DifferentialGraded.Bimodule.isIso_baseChangeStructureTensorTrans_app`), and the left-hand
composite's own comparison is invertible at the modules with property (P) — which is where the
K-flatness of `A` is used, through
`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration` and part (3) in the
form `DifferentialGraded.Bimodule.isIso_derivedTensorBimoduleCounit_app_of_kFlat`. So the square
commutes by the uniqueness of a left derived functor. -/
@[stacks 0BYZ "part (2): the square of restriction and derived base change commutes. The left \
column is restriction along the structure homomorphism R -> A, the right column restriction \
along r' |-> 1 (x) r', and the bottom edge derived base change of R in degree zero read in \
D(R', d) through the unitor R (x)_R R' = R' of degreeZeroBaseChangeUnitor. Parts (1) and (3) \
are derivedBaseChangeFunctor_isLeftDerivedFunctor and isIso_derivedBaseChangeCounit_app_of_kFlat"]
def derivedBaseChangeRestrictionSquare
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex) :
    derivedBaseChangeFunctor A R' ⋙
        derivedRestriction (tensorIncludeRightHom A (degreeZero R R')) ≅
      derivedRestriction (baseHom A) ⋙
        derivedBaseChangeFunctor (degreeZero R R) R' ⋙
          derivedRestriction (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')) :=
  haveI := isIso_baseChangeStructureDerivedTrans A R' hA
  (baseChangeBimoduleDerivedIso A R').symm ≪≫
    (asIso (baseChangeStructureDerivedTrans A R')).symm ≪≫
    Functor.isoWhiskerLeft (derivedRestriction (baseHom A))
      (baseChangeBimoduleDerivedIso (degreeZero R R) R')

/-- The bottom edge of the square, read in `D(R', d)`, is derived base change of the base ring
in degree zero followed by the equivalence of
`DifferentialGradedModule.degreeZeroBaseChangeEquivalence` induced by the unitor
`R ⊗_R R' ≅ R'`. -/
theorem derivedBaseChangeRestrictionSquare_bottom :
    derivedBaseChangeFunctor (degreeZero R R) R' ⋙
        derivedRestriction (tensorIncludeRightHom (degreeZero R R) (degreeZero R R')) =
      derivedBaseChangeFunctor (degreeZero R R) R' ⋙
        (degreeZeroBaseChangeEquivalence R').functor :=
  rfl

end DifferentialGraded.Bimodule

end
