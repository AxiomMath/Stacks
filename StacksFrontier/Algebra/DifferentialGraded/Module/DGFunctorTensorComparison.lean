module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorPureSpan
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGNaturalTransformation
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective

/-!
# Comparing a functor of differential graded module categories with a tensor product

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let
`Φ : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)` be a functor of differential graded categories. Then `Φ(A)`
is a differential graded `(A, B)`-bimodule, a homogeneous `a ∈ A^n` acting through `Φ` of left
multiplication by `a`, and there is a natural comparison

`ψ_M : M ⊗_A Φ(A) ⟶ Φ(M)`,  `x ⊗ y ↦ Φ(ρ_x)(y)`,

where `ρ_x : A ⟶ M`, `b ↦ x b` is right multiplication by a homogeneous `x`. It is strictly
natural against homogeneous morphisms of every degree, and it is the unit isomorphism
`A ⊗_A Φ(A) ≅ Φ(A)` at the regular module.

## Main definitions

* `DifferentialGradedModule.regularLeftMul` and `DifferentialGradedModule.regularRightMul`: left
  multiplication on the regular module and right multiplication into a module, as homogeneous
  maps.
* `DifferentialGraded.Bimodule.ofDGFunctorRegular`: `Φ(A)` as a differential graded
  `(A, B)`-bimodule.
* `DifferentialGraded.Bimodule.dgFunctorTensorComparison`: the comparison `ψ`, as a
  transformation of functors of differential graded categories.

## Main results

* `DifferentialGraded.Bimodule.dgFunctorTensorComparisonHom_pure`: `ψ` on pure tensors.
* `DifferentialGraded.Bimodule.dgFunctorTensorComparisonHom_regular`: at the regular module `ψ`
  is the unit isomorphism.
* `DifferentialGraded.Bimodule.bijective_dgFunctorTensorComparisonHom_of_homogeneousIso`: `ψ` is
  bijective at every module homogeneously isomorphic to one at which it is bijective.
* `DifferentialGraded.Bimodule.isIso_dgFunctorTensorComparisonHom_shift_regular`: `ψ` is an
  isomorphism at every shift of the regular module.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM)
* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- Left multiplication by a homogeneous `a ∈ A^n` on the regular module, as a homogeneous right
`A`-linear map of degree `n`. -/
def regularLeftMul {n : ℤ} (a : A.grading n) :
    HomogeneousMap A (regularModule A) (regularModule A) n :=
  ⟨LinearMap.mulLeft R (a : A.A), fun i x hx => by
      change (a : A.A) * x ∈ A.grading (i + n)
      rw [add_comm]
      exact SetLike.mul_mem_graded a.property hx,
    fun c x => by
      change (a : A.A) * (MulOpposite.op c • x) = MulOpposite.op c • ((a : A.A) * x)
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_assoc]⟩

/-- Left multiplication by `a` sends `x` to `a x`. -/
@[simp] theorem regularLeftMul_apply {n : ℤ} (a : A.grading n) (x : A.A) :
    (regularLeftMul a).1 x = (a : A.A) * x := rfl

/-- Left multiplication, as an `R`-linear map in the multiplier. -/
def regularLeftMulₗ (n : ℤ) :
    A.grading n →ₗ[R] HomogeneousMap A (regularModule A) (regularModule A) n where
  toFun := regularLeftMul
  map_add' a b := Subtype.ext (LinearMap.ext fun x => add_mul (a : A.A) b x)
  map_smul' r a := Subtype.ext (LinearMap.ext fun x => smul_mul_assoc r (a : A.A) x)

/-- Right multiplication by a homogeneous `x ∈ M^p`, as a homogeneous right `A`-linear map
`A ⟶ M` of degree `p`, `b ↦ x b`. -/
def regularRightMul {M : DifferentialGradedModule.{u, u, u} A} {p : ℤ} (x : M.grading p) :
    HomogeneousMap A (regularModule A) M p :=
  ⟨{ toFun := fun b => MulOpposite.op b • (x : M.M)
     map_add' := fun b c => by simp only [MulOpposite.op_add, add_smul]
     map_smul' := fun r b => by
       simp only [MulOpposite.op_smul, smul_assoc, RingHom.id_apply] },
    fun i b hb => by
      change MulOpposite.op b • (x : M.M) ∈ M.grading (i + p)
      rw [add_comm]
      exact M.smul_mem p i x b x.property hb,
    fun c b => by
      change MulOpposite.op (b * c) • (x : M.M) = MulOpposite.op c • (MulOpposite.op b • (x : M.M))
      rw [MulOpposite.op_mul, mul_smul]⟩

/-- Right multiplication by `x` sends `b` to `x b`. -/
@[simp] theorem regularRightMul_apply {M : DifferentialGradedModule.{u, u, u} A} {p : ℤ}
    (x : M.grading p) (b : A.A) :
    (regularRightMul x).1 b = MulOpposite.op b • (x : M.M) := rfl

/-- Right multiplication, as an `R`-linear map in the element multiplied. -/
def regularRightMulₗ (M : DifferentialGradedModule.{u, u, u} A) (p : ℤ) :
    M.grading p →ₗ[R] HomogeneousMap A (regularModule A) M p where
  toFun := regularRightMul
  map_add' x y := Subtype.ext (LinearMap.ext fun b => smul_add (MulOpposite.op b) (x : M.M) y)
  map_smul' r x := Subtype.ext (LinearMap.ext fun b => smul_comm (MulOpposite.op b) r (x : M.M))

end DifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- Left multiplication by `1` is the identity of the regular module. -/
theorem regularLeftMul_one :
    regularLeftMul (A := A) ⟨1, SetLike.one_mem_graded A.grading⟩ = homogeneousMapId A _ :=
  Subtype.ext (LinearMap.ext fun x => one_mul x)

/-- Left multiplication by `a b` is the composite of left multiplication by `a` and by `b`. -/
theorem regularLeftMul_mul {n m : ℤ} (a : A.grading n) (b : A.grading m) :
    regularLeftMul (A := A) ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      homogeneousMapComp A rfl (regularLeftMul a) (regularLeftMul b) :=
  Subtype.ext (LinearMap.ext fun x => mul_assoc (a : A.A) b x)

/-- Left multiplication by `d a` is the Hom differential of left multiplication by `a`. -/
theorem regularLeftMul_d {n : ℤ} (a : A.grading n) :
    regularLeftMul (A := A) ⟨A.d a, A.d_mem n a a.property⟩ =
      homogeneousMapDifferential A (regularLeftMul a) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous i x =>
    change A.d (a : A.A) * x = A.d ((a : A.A) * x) -
      DifferentialGraded.gradedSign R n • ((a : A.A) * A.d x)
    rw [A.leibniz n i a x a.property x.property, ← Int.cast_smul_eq_zsmul R,
      DifferentialGraded.intCast_negOnePow]
    abel

variable (Φ : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- **The left action of `A` on `Φ(A)`.** A homogeneous `a ∈ A^n` acts through `Φ` of left
multiplication by `a`. -/
def dgFunctorRegularLeftAction :
    A.LeftAction (Φ.obj (regularModule A)).toCochainComplex where
  action n := (homogeneousMapToCochainₗ B _ _ n).comp
    ((Φ.mapₗ (regularModule A) (regularModule A) n).comp (regularLeftMulₗ n))
  map_one := by
    change homogeneousMapToCochain B (Φ.map (regularLeftMul _)) = _
    rw [regularLeftMul_one]
    change homogeneousMapToCochain B (Φ.map ((dgCategory A).id _)) = _
    rw [Φ.map_id]
    exact homogeneousMapToCochain_id B _
  map_mul n m a b := by
    change homogeneousMapToCochain B (Φ.map (regularLeftMul _)) = _
    rw [regularLeftMul_mul]
    change homogeneousMapToCochain B (Φ.map ((dgCategory A).comp rfl _ _)) = _
    rw [Φ.map_comp]
    exact homogeneousMapToCochain_comp B rfl _ _
  map_d n a := by
    change homogeneousMapToCochain B (Φ.map (regularLeftMul _)) = _
    rw [regularLeftMul_d]
    change homogeneousMapToCochain B (Φ.map ((dgCategory A).d _)) = _
    rw [Φ.map_d]
    exact homogeneousMapToCochain_d B _

/-- A homogeneous `a` acts on `Φ(A)` as `Φ` of left multiplication by `a`. -/
theorem dgFunctorRegularLeftAction_action (n : ℤ) (a : A.grading n) :
    (dgFunctorRegularLeftAction Φ).action n a =
      homogeneousMapToCochain B (Φ.map (regularLeftMul a)) :=
  rfl

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (Φ : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- **`Φ(A)` as a differential graded `(A, B)`-bimodule**, `A` acting through `Φ` of left
multiplication. -/
@[implicit_reducible]
def ofDGFunctorRegular : Bimodule A B where
  rightModule := Φ.obj (regularModule A)
  leftAction := ⟨dgFunctorRegularLeftAction Φ, fun n a =>
    isRightLinearCochain_homogeneousMapToCochain B _ (n := n) (Φ.map (regularLeftMul a))⟩

/-- The underlying right module of the bimodule `Φ(A)` is `Φ(A)`. -/
@[simp] theorem ofDGFunctorRegular_rightModule :
    (ofDGFunctorRegular Φ).rightModule = Φ.obj (regularModule A) := rfl

/-- The total left action of a homogeneous `a` on `Φ(A)` is `Φ` of left multiplication by `a`. -/
theorem leftActionTotal_ofDGFunctorRegular {n : ℤ} (a : A.grading n)
    (y : (Φ.obj (regularModule A)).M) :
    leftActionTotal A B (ofDGFunctorRegular Φ).rightModule (ofDGFunctorRegular Φ).leftAction.1
        (a : A.A) y = (Φ.map (regularLeftMul a)).1 y := by
  rw [leftActionTotal_apply]
  induction y using DirectSum.Decomposition.inductionOn (Φ.obj (regularModule A)).grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | @homogeneous q y =>
    rw [totalizeCochain_apply_of_eq B _ n q (q + n) rfl]
    rfl

end DifferentialGraded.Bimodule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- Right multiplication by `x a` is right multiplication by `x` after left multiplication by
`a`. -/
theorem regularRightMul_smul {M : DifferentialGradedModule.{u, u, u} A} {p n : ℤ}
    (x : M.grading p) (a : A.grading n) :
    regularRightMul
        (⟨MulOpposite.op (a : A.A) • (x : M.M), M.smul_mem p n x a x.property a.property⟩ :
          M.grading (p + n)) =
      homogeneousMapComp A rfl (regularRightMul x) (regularLeftMul a) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  change MulOpposite.op b • (MulOpposite.op (a : A.A) • (x : M.M)) =
    MulOpposite.op ((a : A.A) * b) • (x : M.M)
  rw [MulOpposite.op_mul, mul_smul]

/-- The Hom differential of right multiplication by `x` is right multiplication by `d x`: the
Leibniz rule of `M`. -/
theorem regularRightMul_d {M : DifferentialGradedModule.{u, u, u} A} {p : ℤ} (x : M.grading p) :
    regularRightMul (⟨M.d x, M.d_mem p x x.property⟩ : M.grading (p + 1)) =
      homogeneousMapDifferential A (regularRightMul x) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro b
  induction b using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add b c hb hc => simp only [map_add, hb, hc]
  | @homogeneous i b =>
    change MulOpposite.op (b : A.A) • M.d x = M.d (MulOpposite.op (b : A.A) • (x : M.M)) -
      DifferentialGraded.gradedSign R p • (MulOpposite.op (A.d b) • (x : M.M))
    rw [M.leibniz p i x b x.property b.property, ← Int.cast_smul_eq_zsmul R,
      DifferentialGraded.intCast_negOnePow]
    abel

/-- Right multiplication by the image of `x` under a homogeneous map `u` is `u` after right
multiplication by `x`. -/
theorem regularRightMul_map {M M' : DifferentialGradedModule.{u, u, u} A} {p n : ℤ}
    (u : HomogeneousMap A M M' n) (x : M.grading p) :
    regularRightMul (⟨u.1 x, u.2.1 p x x.property⟩ : M'.grading (p + n)) =
      homogeneousMapComp A (add_comm n p) u (regularRightMul x) :=
  Subtype.ext (LinearMap.ext fun b => (u.2.2 b x).symm)

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (Φ : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- The bilinear map `M × Φ(A) ⟶ Φ(M)`, `(x, y) ↦ Φ(ρ_x)(y)` on homogeneous `x`, extended
additively over the decomposition of `M`. -/
def dgFunctorTensorBilinear (M : DifferentialGradedModule.{u, u, u} A) :
    M.M →ₗ[R] (Φ.obj (regularModule A)).M →ₗ[R] (Φ.obj M).M :=
  (DirectSum.toModule R ℤ _ fun p =>
      (Submodule.subtype _).comp ((Φ.mapₗ (regularModule A) M p).comp (regularRightMulₗ M p))).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- On a homogeneous `x`, the bilinear map is `y ↦ Φ(ρ_x)(y)`. -/
theorem dgFunctorTensorBilinear_apply (M : DifferentialGradedModule.{u, u, u} A) {p : ℤ}
    (x : M.grading p) :
    dgFunctorTensorBilinear Φ M (x : M.M) = (Φ.map (regularRightMul x)).1 := by
  simp only [dgFunctorTensorBilinear, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_coe]
  rw [show DirectSum.of (fun i => M.grading i) p x = DirectSum.lof R ℤ (fun i => M.grading i) p x
    from rfl, DirectSum.toModule_lof]
  rfl

/-- The bilinear map of `DifferentialGraded.Bimodule.dgFunctorTensorBilinear` is a balanced
bilinear chain map out of `M` and the bimodule `Φ(A)`. -/
def dgFunctorTensorBalanced (M : DifferentialGradedModule.{u, u, u} A) :
    BalancedBilinearMap M (ofDGFunctorRegular Φ) (Φ.obj M) where
  toLinearMap := dgFunctorTensorBilinear Φ M
  map_grading p q x y := by
    rw [dgFunctorTensorBilinear_apply, add_comm]
    exact (Φ.map (regularRightMul x)).2.1 q y.1 y.property
  map_d p x y := by
    have h := congrArg (fun f : HomogeneousMap B _ _ (p + 1) => f.1 y)
      (congrArg Φ.map (regularRightMul_d x))
    change (Φ.map (regularRightMul _)).1 y = (Φ.map ((dgCategory A).d _)).1 y at h
    rw [Φ.map_d] at h
    change _ = (Φ.obj M).d ((Φ.map (regularRightMul x)).1 y) -
      DifferentialGraded.gradedSign R p •
        (Φ.map (regularRightMul x)).1 ((Φ.obj (regularModule A)).d y) at h
    rw [dgFunctorTensorBilinear_apply, dgFunctorTensorBilinear_apply Φ M
      (⟨M.d x, M.d_mem p x x.property⟩ : M.grading (p + 1)), h, ← Int.cast_smul_eq_zsmul R,
      DifferentialGraded.intCast_negOnePow]
    change _ = _ - _ + DifferentialGraded.gradedSign R p •
      (Φ.map (regularRightMul x)).1 ((Φ.obj (regularModule A)).d y)
    abel
  balance p q n x y a := by
    rw [dgFunctorTensorBilinear_apply Φ M
      (⟨MulOpposite.op (a : A.A) • (x : M.M), M.smul_mem p n x a x.property a.property⟩ :
        M.grading (p + n)), dgFunctorTensorBilinear_apply, regularRightMul_smul]
    change (Φ.map ((dgCategory A).comp rfl _ _)).1 y.1 = _
    rw [Φ.map_comp]
    rfl
  map_right x y b := by
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
    | @homogeneous p x =>
      rw [dgFunctorTensorBilinear_apply]
      exact (Φ.map (regularRightMul x)).2.2 b y

end DifferentialGraded.Bimodule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (Φ : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B))

/-- **The comparison `M ⊗_A Φ(A) ⟶ Φ(M)`**, `x ⊗ y ↦ Φ(ρ_x)(y)`, from the universal property of
the relative tensor product. -/
def dgFunctorTensorComparisonHom (M : DifferentialGradedModule.{u, u, u} A) :
    DifferentialGradedModule.Hom (tensorObj' (ofDGFunctorRegular Φ) M) (Φ.obj M) :=
  ((tensorDGFunctor (ofDGFunctorRegular Φ)).universal M (Φ.obj M)
    (dgFunctorTensorBalanced Φ M)).choose

/-- The comparison sends `x ⊗ y` to the value of the bilinear map at `(x, y)`. -/
theorem dgFunctorTensorComparisonHom_pure (M : DifferentialGradedModule.{u, u, u} A) (x : M.M)
    (y : (Φ.obj (regularModule A)).M) :
    (dgFunctorTensorComparisonHom Φ M).toFun
        (((tensorDGFunctor (ofDGFunctorRegular Φ)).pure M).toLinearMap x y) =
      dgFunctorTensorBilinear Φ M x y :=
  ((tensorDGFunctor (ofDGFunctorRegular Φ)).universal M (Φ.obj M)
    (dgFunctorTensorBalanced Φ M)).choose_spec.1 x y

/-- The bilinear map is natural against homogeneous maps of every degree. -/
theorem dgFunctorTensorBilinear_map {M M' : DifferentialGradedModule.{u, u, u} A} {n : ℤ}
    (u : (dgCategory A).Hom M M' n) (x : M.M) (y : (Φ.obj (regularModule A)).M) :
    dgFunctorTensorBilinear Φ M' (u.1 x) y = (Φ.map u).1 (dgFunctorTensorBilinear Φ M x y) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | @homogeneous p x =>
    rw [show u.1 (x : M.M) = ((⟨u.1 x, u.2.1 p x x.property⟩ : M'.grading (p + n)) : M'.M) from rfl,
      dgFunctorTensorBilinear_apply, dgFunctorTensorBilinear_apply, regularRightMul_map]
    change (Φ.map ((dgCategory A).comp (add_comm n p) u _)).1 y = _
    rw [Φ.map_comp]
    rfl

/-- **The comparison `ψ : - ⊗_A Φ(A) ⟶ Φ`, as a transformation of functors of differential
graded categories.** It is strictly natural against homogeneous morphisms of every degree. -/
def dgFunctorTensorComparison :
    DGCategory.DGNatTrans (tensorDGFunctor (ofDGFunctorRegular Φ)).functor Φ where
  app M := cocycleOfHom B (dgFunctorTensorComparisonHom Φ M)
  naturality {M M'} n u := by
    apply Subtype.ext
    refine tensorObj_linearMap_ext (ofDGFunctorRegular Φ) M _ _ fun x y => ?_
    change (dgFunctorTensorComparisonHom Φ M').toFun
        (((tensorDGFunctor (ofDGFunctorRegular Φ)).functor.map u).1
          (((tensorDGFunctor (ofDGFunctorRegular Φ)).pure M).toLinearMap x y)) =
      (Φ.map u).1 ((dgFunctorTensorComparisonHom Φ M).toFun
        (((tensorDGFunctor (ofDGFunctorRegular Φ)).pure M).toLinearMap x y))
    rw [(tensorDGFunctor (ofDGFunctorRegular Φ)).map_pure, dgFunctorTensorComparisonHom_pure,
      dgFunctorTensorComparisonHom_pure]
    exact dgFunctorTensorBilinear_map Φ u x y

/-- The component of `ψ` at `M` is the comparison map `M ⊗_A Φ(A) ⟶ Φ(M)`. -/
@[simp] theorem dgFunctorTensorComparison_app (M : DifferentialGradedModule.{u, u, u} A) :
    ((dgFunctorTensorComparison Φ).app M).1.1 = (dgFunctorTensorComparisonHom Φ M).toFun :=
  rfl

/-- At the regular module the bilinear map is the left action. -/
theorem dgFunctorTensorBilinear_regular (a : A.A) (y : (Φ.obj (regularModule A)).M) :
    dgFunctorTensorBilinear Φ (regularModule A) a y =
      leftActionTotal A B (ofDGFunctorRegular Φ).rightModule (ofDGFunctorRegular Φ).leftAction.1
        a y := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | @homogeneous n a =>
    rw [dgFunctorTensorBilinear_apply, leftActionTotal_ofDGFunctorRegular]
    congr 2

/-- **At the regular module the comparison is the unit isomorphism `A ⊗_A Φ(A) ≅ Φ(A)`.** -/
theorem dgFunctorTensorComparisonHom_regular :
    dgFunctorTensorComparisonHom Φ (regularModule A) =
      (tensorRegularIso (ofDGFunctorRegular Φ)).1.hom := by
  refine tensorObj_hom_ext' (ofDGFunctorRegular Φ) (regularModule A) _ _ fun a y => ?_
  rw [dgFunctorTensorComparisonHom_pure, (tensorRegularIso (ofDGFunctorRegular Φ)).2,
    dgFunctorTensorBilinear_regular]

/-- At the regular module the comparison `A ⊗_A Φ(A) ⟶ Φ(A)` is an isomorphism. -/
theorem isIso_dgFunctorTensorComparisonHom_regular :
    IsIso (show tensorObj' (ofDGFunctorRegular Φ) (regularModule A) ⟶ Φ.obj (regularModule A) from
      dgFunctorTensorComparisonHom Φ (regularModule A)) := by
  rw [dgFunctorTensorComparisonHom_regular]
  infer_instance

/-- **The comparison is bijective at every module homogeneously isomorphic to one at which it is
bijective.** If `σ : M ⟶ M'` is a homogeneous map of some degree `n` with a two-sided inverse
`τ` of degree `m = -n`, then strict naturality against `σ` exhibits `ψ_{M'}` as
`Φ(σ) ∘ ψ_M ∘ F(τ)`, for `F = - ⊗_A Φ(A)`. -/
theorem bijective_dgFunctorTensorComparisonHom_of_homogeneousIso
    {M M' : DifferentialGradedModule.{u, u, u} A} {n m : ℤ} (hnm : n + m = 0) (hmn : m + n = 0)
    (σ : (dgCategory A).Hom M M' n) (τ : (dgCategory A).Hom M' M m)
    (hστ : (dgCategory A).comp hnm σ τ = (dgCategory A).id M')
    (hτσ : (dgCategory A).comp hmn τ σ = (dgCategory A).id M)
    (h : Function.Bijective (dgFunctorTensorComparisonHom Φ M).toFun) :
    Function.Bijective (dgFunctorTensorComparisonHom Φ M').toFun := by
  let F := (tensorDGFunctor (ofDGFunctorRegular Φ)).functor
  have inv_of {X Y : DGCategory.Obj (dgCategory.{u, u, u} B)} {k l : ℤ} (hkl : k + l = 0)
      (hlk : l + k = 0) (f : (dgCategory B).Hom X Y k) (g : (dgCategory B).Hom Y X l)
      (hfg : (dgCategory B).comp hkl f g = (dgCategory B).id Y)
      (hgf : (dgCategory B).comp hlk g f = (dgCategory B).id X) :
      Function.Bijective f.1 :=
    Function.bijective_iff_has_inverse.mpr ⟨g.1,
      fun z => LinearMap.congr_fun (congrArg Subtype.val hgf) z,
      fun z => LinearMap.congr_fun (congrArg Subtype.val hfg) z⟩
  have hbij (G : DGCategory.DGFunctor (dgCategory.{u, u, u} A) (dgCategory.{u, u, u} B)) :
      Function.Bijective (G.map σ).1 :=
    inv_of hnm hmn (G.map σ) (G.map τ) (by rw [← G.map_comp, hστ, G.map_id])
      (by rw [← G.map_comp, hτσ, G.map_id])
  have hnat := congrArg (fun f => f.1) ((dgFunctorTensorComparison Φ).naturality σ)
  change (dgFunctorTensorComparisonHom Φ M').toFun ∘ₗ (F.map σ).1 =
    (Φ.map σ).1 ∘ₗ (dgFunctorTensorComparisonHom Φ M).toFun at hnat
  have hcomp : Function.Bijective
      ((dgFunctorTensorComparisonHom Φ M').toFun ∘ (F.map σ).1) := by
    rw [← LinearMap.coe_comp, hnat, LinearMap.coe_comp]
    exact (hbij Φ).comp h
  exact (Function.Bijective.of_comp_iff _ (hbij F)).mp hcomp

/-- **The comparison is an isomorphism at every shift of the regular module.** The identity of
the underlying module is a homogeneous isomorphism `A ⟶ A[n]` of degree `-n`, and the comparison
is the unit isomorphism at `A`. -/
theorem isIso_dgFunctorTensorComparisonHom_shift_regular (n : ℤ) :
    IsIso (show tensorObj' (ofDGFunctorRegular Φ) (shift (regularModule A) n) ⟶
        Φ.obj (shift (regularModule A) n) from
      dgFunctorTensorComparisonHom Φ (shift (regularModule A) n)) := by
  have h0 : Function.Bijective (dgFunctorTensorComparisonHom Φ (regularModule A)).toFun := by
    rw [dgFunctorTensorComparisonHom_regular]
    let e := (tensorRegularIso (ofDGFunctorRegular Φ)).1
    exact Function.bijective_iff_has_inverse.mpr ⟨e.inv.toFun,
      fun z => LinearMap.congr_fun (congrArg DifferentialGradedModule.Hom.toFun e.hom_inv_id) z,
      fun z => LinearMap.congr_fun (congrArg DifferentialGradedModule.Hom.toFun e.inv_hom_id) z⟩
  exact isIso_of_bijective _ (bijective_dgFunctorTensorComparisonHom_of_homogeneousIso Φ
    (neg_add_cancel n) (add_neg_cancel n) (homogeneousMapToShift (regularModule A) n)
    (homogeneousMapFromShift (regularModule A) n)
    (homogeneousMapToShift_comp_fromShift _ n) (homogeneousMapFromShift_comp_toShift _ n) h0)

end DifferentialGraded.Bimodule
