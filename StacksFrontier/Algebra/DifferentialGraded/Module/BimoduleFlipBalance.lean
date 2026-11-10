module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLeftPropertyPProof
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleRestrictLeft

/-! # Tensoring with the flip of a K-projective module preserves quasi-isomorphisms

Let `R` be a commutative ring and `(A, d)` a differential graded `R`-algebra. A right
differential graded `A`-module `X` is a differential graded `(A^{opp}, R)`-bimodule `X̂`
(`DifferentialGraded.Bimodule.flip`), and the relative tensor product `Y ⊗_{A^{opp}} X̂` of a right
differential graded `A^{opp}`-module `Y` with it is the tensor product of `X` with `Y` read as a
left module. This file proves that **when `X` is orthogonal on the left to the acyclic modules,
tensoring with `X̂` carries quasi-isomorphisms of right differential graded `A^{opp}`-modules to
quasi-isomorphisms**, so that `- ⊗^𝐋_{A^{opp}} X̂` is computed by the plain tensor product. This is
the balancing of the derived tensor product: it may be computed by resolving either variable.

The argument reads a right `A^{opp}`-module `Y` as a differential graded `(A, R)`-bimodule `Y̌`
(`DifferentialGraded.Bimodule.unflip`), whose left module read back over `A^{opp}` by Tag 0FQ0 is
`Y` again. The flip `X ⊗_A Y̌ ≅ Y ⊗_{A^{opp}} X̂` (`DifferentialGraded.Bimodule.tensorFlipIso`)
then turns `Y ⊗_{A^{opp}} X̂` into `X ⊗_A Y̌`, in which `Y̌` sits in the bimodule slot; there the
second assertion of Tag 09S3 applies, and the derived tensor product at `X` is the plain one
because `X` is orthogonal on the left to the acyclic modules.

## Main definitions

* `DifferentialGradedAlgebra.oppOppHom`: the identification of `A` with its double graded
  opposite, as a homomorphism of differential graded algebras.
* `DifferentialGraded.Bimodule.unflip`: a right differential graded `A^{opp}`-module, read as a
  differential graded `(A, R)`-bimodule, and `DifferentialGraded.Bimodule.unflipMap` its
  functoriality.
* `DifferentialGraded.Bimodule.flipModuleUnflipIso`: the left module of `unflip Y`, read back
  over `A^{opp}`, is `Y`.

## Main results

* `DifferentialGraded.Bimodule.tensorPreservesQuasiIso_flip_of_leftOrthogonal`: **tensoring with
  the flip of a module orthogonal on the left to the acyclic modules preserves
  quasi-isomorphisms.**
* `DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_flip_of_leftOrthogonal`: so the
  comparison of Tag 09LS from the derived to the plain tensor product with that flip is an
  isomorphism.

## References

* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3), the second assertion.
* [Stacks Project, Tag 0FQ0](https://stacks.math.columbia.edu/tag/0FQ0), left modules as right
  modules over the graded opposite, and [Tag 09JG](https://stacks.math.columbia.edu/tag/09JG), the
  graded opposite algebra.
* [Stacks Project, Tag 0GZ2](https://stacks.math.columbia.edu/tag/0GZ2), whose proof runs the same
  flip in the other direction.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedAlgebra

open DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R]

/-- The underlying linear map of `DifferentialGradedAlgebra.oppOppHom`: the inverses of the two
identifications of the underlying graded modules of the graded opposites. -/
def oppOppLinear (A : DifferentialGradedAlgebra.{u, u} R) :
    A.A →ₗ[R] (oppAlgebra (oppAlgebra A)).A :=
  (opposite R (oppAlgebra A)).equiv.symm.toLinearMap ∘ₗ (opposite R A).equiv.symm.toLinearMap

/-- `DifferentialGradedAlgebra.oppOppLinear` is the composite of the two inverse
identifications. -/
theorem oppOppLinear_apply (A : DifferentialGradedAlgebra.{u, u} R) (a : A.A) :
    oppOppLinear A a = (opposite R (oppAlgebra A)).equiv.symm ((opposite R A).equiv.symm a) :=
  rfl

/-- The inverse identification `B → B^{opp}` preserves the grading. -/
private theorem opposite_equiv_symm_mem {B : DifferentialGradedAlgebra.{u, u} R} {n : ℤ} {b : B.A}
    (hb : b ∈ B.grading n) : (opposite R B).equiv.symm b ∈ (oppAlgebra B).grading n := by
  rw [(opposite R B).mem_grading_iff, LinearEquiv.apply_symm_apply]
  exact hb

/-- `DifferentialGradedAlgebra.oppOppLinear` preserves the grading. -/
theorem oppOppLinear_mem (A : DifferentialGradedAlgebra.{u, u} R) (n : ℤ) (a : A.A)
    (ha : a ∈ A.grading n) : oppOppLinear A a ∈ (oppAlgebra (oppAlgebra A)).grading n :=
  opposite_equiv_symm_mem (opposite_equiv_symm_mem ha)

/-- `DifferentialGradedAlgebra.oppOppLinear` sends `1` to `1`. -/
theorem oppOppLinear_one (A : DifferentialGradedAlgebra.{u, u} R) : oppOppLinear A 1 = 1 := by
  rw [oppOppLinear_apply]
  apply (opposite R (oppAlgebra A)).equiv.injective
  rw [LinearEquiv.apply_symm_apply, (opposite R (oppAlgebra A)).map_one]
  apply (opposite R A).equiv.injective
  rw [LinearEquiv.apply_symm_apply, (opposite R A).map_one]

/-- `DifferentialGradedAlgebra.oppOppLinear` is multiplicative on homogeneous elements. -/
theorem oppOppLinear_mul_of_mem (A : DifferentialGradedAlgebra.{u, u} R) {n m : ℤ} {a b : A.A}
    (ha : a ∈ A.grading n) (hb : b ∈ A.grading m) :
    oppOppLinear A (a * b) = oppOppLinear A a * oppOppLinear A b := by
  have ha' := opposite_equiv_symm_mem ha
  have hb' := opposite_equiv_symm_mem hb
  have ha'' := opposite_equiv_symm_mem ha'
  have hb'' := opposite_equiv_symm_mem hb'
  rw [oppOppLinear_apply, oppOppLinear_apply, oppOppLinear_apply]
  apply (opposite R (oppAlgebra A)).equiv.injective
  rw [(opposite R (oppAlgebra A)).map_mul_of_mem n m _ _ ha'' hb'', LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  apply (opposite R A).equiv.injective
  rw [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul,
    (opposite R A).map_mul_of_mem m n _ _ hb' ha', LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, Units.smul_def, smul_smul, show m * n = n * m from mul_comm m n,
    ← Units.val_mul, ← Int.negOnePow_add, show n * m + n * m = 2 * (n * m) by ring,
    Int.negOnePow_two_mul, Units.val_one, one_smul]

/-- `DifferentialGradedAlgebra.oppOppLinear` is multiplicative. -/
theorem oppOppLinear_mul (A : DifferentialGradedAlgebra.{u, u} R) (a b : A.A) :
    oppOppLinear A (a * b) = oppOppLinear A a * oppOppLinear A b := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
  | @homogeneous n a =>
    induction b using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
    | @homogeneous m b => exact oppOppLinear_mul_of_mem A a.property b.property

/-- **A differential graded algebra maps to its double graded opposite**, by the inverses of the
identifications of the underlying graded modules: the two Koszul signs cancel. -/
def oppOppHom (A : DifferentialGradedAlgebra.{u, u} R) : A.Hom (oppAlgebra (oppAlgebra A)) where
  toAlgebraHom := AlgHom.ofLinearMap (oppOppLinear A) (oppOppLinear_one A) (oppOppLinear_mul A)
  map_grading n a ha := oppOppLinear_mem A n a ha
  map_d a := by
    change oppOppLinear A (A.d a) = (oppAlgebra (oppAlgebra A)).d (oppOppLinear A a)
    rw [oppOppLinear_apply, oppOppLinear_apply]
    apply (opposite R (oppAlgebra A)).equiv.injective
    rw [LinearEquiv.apply_symm_apply, (opposite R (oppAlgebra A)).map_d,
      LinearEquiv.apply_symm_apply]
    apply (opposite R A).equiv.injective
    rw [LinearEquiv.apply_symm_apply, (opposite R A).map_d, LinearEquiv.apply_symm_apply]

/-- The identification of `A` with its double graded opposite, read back to `A^{opp}`, is the
inverse of the identification of `A^{opp}` with `A`. -/
theorem equiv_oppOppHom_apply (A : DifferentialGradedAlgebra.{u, u} R) (a : A.A) :
    (opposite R (oppAlgebra A)).equiv ((oppOppHom A).toAlgebraHom a) =
      (opposite R A).equiv.symm a := by
  change (opposite R (oppAlgebra A)).equiv (oppOppLinear A a) = _
  rw [oppOppLinear_apply, LinearEquiv.apply_symm_apply]

end DifferentialGradedAlgebra

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- **A right differential graded `A^{opp}`-module, read as a differential graded
`(A, R)`-bimodule**: its flip, an `((A^{opp})^{opp}, R)`-bimodule, with the left action restricted
along `A → (A^{opp})^{opp}`. -/
abbrev unflip (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    Bimodule A (degreeZero R R) :=
  Bimodule.restrictLeft (oppOppHom A) (flip Y)

/-- The functoriality of `DifferentialGraded.Bimodule.unflip`. -/
def unflipMap {Y Y' : DifferentialGradedModule.{u, u, u} (oppAlgebra A)} (f : Y ⟶ Y') :
    unflip Y ⟶ unflip Y' where
  rightHom := (flipMap f).rightHom
  map_left n p a x := (flipMap f).map_left n p ((oppOppHom A).gradingMap n a) x

/-- The underlying map of `DifferentialGraded.Bimodule.unflipMap f` is that of `f`. -/
@[simp] theorem unflipMap_rightHom_toFun {Y Y' : DifferentialGradedModule.{u, u, u} (oppAlgebra A)}
    (f : Y ⟶ Y') : (unflipMap f).rightHom.toFun = f.toFun := rfl

/-- The left action of `A` on `unflip Y`, on homogeneous elements: the left action of the image
in the double graded opposite on the flip. -/
theorem leftActionTotal_unflip (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) {m n : ℤ}
    {a : A.A} (ha : a ∈ A.grading m) {y : Y.M} (hy : y ∈ Y.grading n) :
    leftActionTotal A (degreeZero R R) (unflip Y).rightModule (unflip Y).leftAction.1 a y =
      oppLeftActionRingHom Y ((oppOppHom A).toAlgebraHom a) y := by
  have h1 := leftActionTotal_eq_action_v (unflip Y) (⟨a, ha⟩ : A.grading m)
    (⟨y, hy⟩ : (unflip Y).rightModule.grading n)
  refine h1.trans ?_
  rw [Bimodule.restrictLeft_action]
  exact flip_leftAction Y ((oppOppHom A).gradingMap m ⟨a, ha⟩)
    (⟨y, hy⟩ : (flip Y).rightModule.grading n)

/-- The identification of the underlying module of the left module of `unflip Y`, read back over
`A^{opp}`, with that of `Y`. -/
abbrev unflipEquiv (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    (flipModule (unflip Y)).M ≃ₗ[R] Y.M :=
  flipUnderlying (unflip Y)

/-- The right action of `A^{opp}` on the left module of `unflip Y` read back over `A^{opp}` is
the right action on `Y`, on homogeneous elements. -/
theorem flipModule_unflip_smul_of_mem (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A))
    {m n : ℤ} {a : (oppAlgebra A).A} (ha : a ∈ (oppAlgebra A).grading m)
    {x : (flipModule (unflip Y)).M} (hx : x ∈ (flipModule (unflip Y)).grading n) :
    unflipEquiv Y (MulOpposite.op a • x) = MulOpposite.op a • unflipEquiv Y x := by
  have hx' : unflipEquiv Y x ∈ Y.grading n := (flipUnderlying_grading (unflip Y) n x).1 hx
  have haA : (opposite R A).equiv a ∈ A.grading m := ((opposite R A).mem_grading_iff m a).1 ha
  have h := flipUnderlying_action' (unflip Y) ha hx
  rw [leftActionTotal_unflip Y (y := flipUnderlying (unflip Y) x) haA hx'] at h
  refine h.trans ?_
  change (((m * n).negOnePow : ℤ) : R) •
      oppLeftActionRingHom Y ((oppOppHom A).toAlgebraHom ((opposite R A).equiv a))
        (unflipEquiv Y x) = _
  rw [oppLeftActionRingHom_apply_mem Y ((oppOppHom A).map_grading m _ haA) hx',
    equiv_oppOppHom_apply, LinearEquiv.symm_apply_apply, smul_smul, negOnePowR_self_mul,
    one_smul]

/-- The right action of `A^{opp}` on the left module of `unflip Y` read back over `A^{opp}` is
the right action on `Y`. -/
theorem flipModule_unflip_smul (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A))
    (a : (oppAlgebra A).A) (x : (flipModule (unflip Y)).M) :
    unflipEquiv Y (MulOpposite.op a • x) = MulOpposite.op a • unflipEquiv Y x := by
  induction a using DirectSum.Decomposition.inductionOn (oppAlgebra A).grading with
  | zero => simp
  | add a b hA hB =>
      rw [MulOpposite.op_add, add_smul, map_add, hA, hB, add_smul]
  | @homogeneous m a =>
      induction x using DirectSum.Decomposition.inductionOn (flipModule (unflip Y)).grading with
      | zero => simp
      | add x y hX hY => rw [smul_add, map_add, hX, hY, map_add, smul_add]
      | @homogeneous n x => exact flipModule_unflip_smul_of_mem Y a.property x.property

/-- The comparison from the left module of `unflip Y`, read back over `A^{opp}`, to `Y`: the
identification of the underlying modules. -/
def flipModuleUnflipHom (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    flipModule (unflip Y) ⟶ Y where
  toFun := (unflipEquiv Y).toLinearMap
  map_smul x a := flipModule_unflip_smul Y a x
  map_grading n x hx := (flipUnderlying_grading (unflip Y) n x).1 hx
  map_d := LinearMap.ext fun x => flipUnderlying_d (unflip Y) x

/-- The comparison from `Y` to the left module of `unflip Y`, read back over `A^{opp}`. -/
def flipModuleUnflipInv (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    Y ⟶ flipModule (unflip Y) where
  toFun := (unflipEquiv Y).symm.toLinearMap
  map_smul y a := by
    apply (unflipEquiv Y).injective
    change unflipEquiv Y ((unflipEquiv Y).symm _) =
      unflipEquiv Y (MulOpposite.op a • (unflipEquiv Y).symm y)
    rw [flipModule_unflip_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  map_grading n y hy := flipUnderlying_symm_grading (unflip Y) hy
  map_d := LinearMap.ext fun y => (flipUnderlying_symm_d (unflip Y) y).symm

/-- **The left module of `unflip Y`, read back over `A^{opp}` by Tag 0FQ0, is `Y`.** -/
def flipModuleUnflipIso (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    flipModule (unflip Y) ≅ Y where
  hom := flipModuleUnflipHom Y
  inv := flipModuleUnflipInv Y
  hom_inv_id := DifferentialGradedModule.Hom.ext
    (LinearMap.ext fun x => (unflipEquiv Y).symm_apply_apply x)
  inv_hom_id := DifferentialGradedModule.Hom.ext
    (LinearMap.ext fun y => (unflipEquiv Y).apply_symm_apply y)

/-! ### The flip of the tensor product, in the bimodule variable -/

variable (X : DifferentialGradedModule.{u, u, u} A)

/-- **The flip, read in the bimodule variable**: the relative tensor product of `Y` with `X̂` over
`A^{opp}` is the relative tensor product of `X` with `unflip Y` over `A`. -/
def tensorUnflipIso (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A)) :
    tensorObj (flip X) Y ≅ tensorObj (unflip Y) X :=
  (tensorCompFunctor (flip X)).mapIso (flipModuleUnflipIso Y).symm ≪≫
    (tensorFlipIso (unflip Y) X).symm

/-- `DifferentialGraded.Bimodule.tensorUnflipIso` on pure tensors. -/
theorem tensorUnflipIso_hom_pure (Y : DifferentialGradedModule.{u, u, u} (oppAlgebra A))
    {p q : ℤ} {y : Y.M} (hy : y ∈ Y.grading q) {x : X.M} (hx : x ∈ X.grading p) :
    (tensorUnflipIso X Y).hom.toFun
        (((tensorDGFunctor (flip X)).pure Y).toLinearMap y x) =
      (((q * p).negOnePow : ℤ) : R) • ((tensorDGFunctor (unflip Y)).pure X).toLinearMap x y := by
  change (phi (unflip Y) X).toFun (((tensorCompFunctor (flip X)).map
      (flipModuleUnflipInv Y)).toFun (((tensorDGFunctor (flip X)).pure Y).toLinearMap y x)) = _
  rw [tensorCompFunctor_map_pure' (flip X) (flipModuleUnflipInv Y) y x]
  change (phi (unflip Y) X).toFun (((tensorDGFunctor (flip X)).pure
      (flipModule (unflip Y))).toLinearMap ((flipUnderlying (unflip Y)).symm y) x) = _
  rw [phi_pure, phiLinear_apply_mem (unflip Y) X (flipUnderlying_symm_grading (unflip Y) hy) hx,
    tensorPureFlip_apply]
  exact congrArg (fun z => (((q * p).negOnePow : ℤ) : R) •
    ((tensorDGFunctor (unflip Y)).pure X).toLinearMap x z)
    ((flipUnderlying (unflip Y)).apply_symm_apply y)

/-- **The flip is natural in the bimodule variable.** -/
theorem tensorUnflipIso_naturality {Y Y' : DifferentialGradedModule.{u, u, u} (oppAlgebra A)}
    (f : Y ⟶ Y') :
    (tensorCompFunctor (flip X)).map f ≫ (tensorUnflipIso X Y').hom =
      (tensorUnflipIso X Y).hom ≫ tensorHomOfBimoduleHom (unflipMap f) X := by
  refine tensorObj_hom_ext' (flip X) Y _ _ fun y x => ?_
  change (tensorUnflipIso X Y').hom.toFun (((tensorCompFunctor (flip X)).map f).toFun
      (((tensorDGFunctor (flip X)).pure Y).toLinearMap y x)) =
    (tensorHomOfBimoduleHom (unflipMap f) X).toFun ((tensorUnflipIso X Y).hom.toFun
      (((tensorDGFunctor (flip X)).pure Y).toLinearMap y x))
  rw [tensorCompFunctor_map_pure' (flip X) f y x]
  induction y using DirectSum.Decomposition.inductionOn Y.grading with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | @homogeneous q y =>
    induction x using DirectSum.Decomposition.inductionOn X.grading with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | @homogeneous p x =>
      rw [tensorUnflipIso_hom_pure X Y' (f.map_grading q _ y.property) x.property,
        tensorUnflipIso_hom_pure X Y y.property x.property, map_smul]
      exact congrArg (fun z => (((q * p).negOnePow : ℤ) : R) • z)
        (tensorHomOfBimoduleHom_pure (unflipMap f) X (x : X.M) (y : Y.M)).symm

/-! ### Tensoring with the flip of a K-projective module -/

/-- At a module orthogonal on the left to the acyclic modules, tensoring with a homomorphism of
bimodules whose underlying map is a quasi-isomorphism gives a quasi-isomorphism: the second
assertion of Tag 09S3, read through the comparison of Tag 09LS, which is invertible there. -/
theorem quasiIso_tensorHomOfBimoduleHom_of_leftOrthogonal {B : DifferentialGradedAlgebra.{u, u} R}
    {N N' : Bimodule A B} (g : N ⟶ N')
    (hg : QuasiIso ((forgetToCochainComplex B).map g.rightHom))
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    QuasiIso ((forgetToCochainComplex B).map (tensorHomOfBimoduleHom g X)) := by
  have hiso : IsIso (derivedTensorNatTrans g) := quasiIsoInvertsDerivedTensor A B g hg
  have hnat : IsIso ((derivedTensorNatTrans g).app
      ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X))) := inferInstance
  have hc (M : Bimodule A B) : IsIso ((derivedTensorFunctorCounit M).app
      ((toHomotopyCategory A).obj X)) :=
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal M _ hX
  have hcomp : IsIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj X) ≫
      (ordinaryTensorNatTrans g).app ((toHomotopyCategory A).obj X)) := by
    rw [← derivedTensorNatTrans_app_comp_counit]
    infer_instance
  have hord : IsIso ((ordinaryTensorNatTrans g).app ((toHomotopyCategory A).obj X)) :=
    IsIso.of_isIso_comp_left ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj X)) _
  rw [← isIso_q_map_toHomotopyCategory_map_iff B (tensorHomOfBimoduleHom g X)]
  rw [ordinaryTensorNatTrans_app, tensorHomotopyNatTrans_app, Functor.map_comp,
    Functor.map_comp] at hord
  have h3 : IsIso ((quasiIsomorphisms' B).Q.map
      ((toHomotopyCategory B).map ((tensorModuleNatTrans g).app X)) ≫
      (quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient N').hom.app X)) :=
    IsIso.of_isIso_comp_left ((quasiIsomorphisms' B).Q.map
      ((tensorCompFunctor_quotient N).inv.app X)) _
  exact IsIso.of_isIso_comp_right
    ((quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map ((tensorModuleNatTrans g).app X)))
    ((quasiIsomorphisms' B).Q.map ((tensorCompFunctor_quotient N').hom.app X))

/-- **Tensoring with the flip of a module orthogonal on the left to the acyclic modules preserves
quasi-isomorphisms.** For such a right differential graded `A`-module `X` and a
quasi-isomorphism `f : Y ⟶ Y'` of right differential graded `A^{opp}`-modules, the flip turns
`f ⊗ X̂` into `X ⊗ unflip f`, which is a quasi-isomorphism by the second assertion of Tag 09S3. -/
theorem tensorPreservesQuasiIso_flip_of_leftOrthogonal
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    TensorPreservesQuasiIso (flip X) := by
  intro Y Y' f hf
  have hq : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map (unflipMap f).rightHom) := by
    have h : @Eq (Y.toCochainComplex ⟶ Y'.toCochainComplex)
        (restrictScalarsHom (baseHom (oppAlgebra A)) f).toCochainMap f.toCochainMap :=
      restrictScalarsHom_toCochainMap (baseHom (oppAlgebra A)) f
    have h' : (forgetToCochainComplex (degreeZero R R)).map (unflipMap f).rightHom =
        (forgetToCochainComplex (oppAlgebra A)).map f := h
    rw [h']
    exact hf
  have hplain := quasiIso_tensorHomOfBimoduleHom_of_leftOrthogonal X (unflipMap f) hq hX
  have harr : Arrow.mk ((tensorCompFunctor (flip X)).map f) ≅
      Arrow.mk (tensorHomOfBimoduleHom (unflipMap f) X) :=
    Arrow.isoMk (tensorUnflipIso X Y) (tensorUnflipIso X Y')
      (tensorUnflipIso_naturality X f).symm
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    ((forgetToCochainComplex (degreeZero R R)).mapArrow.mapIso harr)).2 hplain

/-- **The derived tensor product with the flip of a K-projective module is the plain one**: the
comparison of Tag 09LS is an isomorphism of functors. -/
theorem isIso_derivedTensorFunctorCounit_flip_of_leftOrthogonal
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    IsIso (derivedTensorFunctorCounit (flip X)) :=
  isIso_derivedTensorFunctorCounit_of_preservesQuasiIso (flip X)
    (tensorPreservesQuasiIso_flip_of_leftOrthogonal X hX)

end DifferentialGraded.Bimodule

end
