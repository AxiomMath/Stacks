module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensorUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedModule

/-!
# The unit of extension of scalars along a quasi-isomorphism

Let `(C, O)` be a ringed site and let `φ : A ⟶ B` be a unit-preserving homomorphism of sheaves of
differential graded `O`-algebras which induces an isomorphism on cohomology sheaves. For a K-flat
right differential graded `A`-module `P`, the unit

`P ⟶ P ⊗_A B`, `x ↦ x ⊗ 1`

of extension of scalars along `φ` is a quasi-isomorphism. This is the step of the proof of
[Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ) which uses that `φ` is a
quasi-isomorphism of left differential graded `A`-modules: the cone of the unit is `P` tensored
with the cone of `φ`, which is acyclic because `P` is K-flat.

## Main definitions

* `SheafOfModules.LeftDifferentialGradedModule.unitBimodule`: a left differential graded
  `A`-module is a differential graded `(A, (O, 0))`-bimodule, `(O, 0)` acting by scalars.
* `SheafOfModules.DifferentialGradedModule.opRegularHom`: `φ`, read as a homomorphism of right
  differential graded `A.op`-modules from `A.op` to `B` viewed as a left `A`-module.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_dgTensorFunctor_map_opRegularHom`: for a
  K-flat `P`, the map `A.op ⊗_{A.op} P ⟶ B ⊗_{A.op} P` induced by `φ` is a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.quasiIso_extensionUnit_of_isKFlat`: the unit
  `P ⟶ P ⊗_A B` is a quasi-isomorphism.

## Implementation notes

The relative tensor product is functorial, and commutes with cones, in its first variable only:
the cone comparison `SheafOfModules.TensorFunctorData.coneComplexIso` is stated for a tensor
product functor `- ⊗_A N` with a bimodule `N`. The variable in which `φ` sits is the second one,
so the two factors are interchanged first: `P ⊗_A N = N ⊗_{A.op} P` for every left differential
graded `A`-module `N` (`SheafOfModules.RelativeTensor.dgTensorOpIso`), and `P`, read as a left
differential graded `A.op`-module, is made a bimodule over `(A.op, (O, 0))` by letting the
structure sheaf act by scalars. Then `- ⊗_{A.op} P` is a tensor product functor, the cone of
`φ ⊗ 1` is `cone(φ) ⊗_{A.op} P = P ⊗_A cone(φ)`, and K-flatness of `P` makes it acyclic. The unit
`x ↦ x ⊗ 1` is `φ ⊗ 1` read through the unit isomorphism `A.op ⊗_{A.op} P = P` and the
interchange, which is checked on local sections.

## References

* [Stacks Project, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

open CategoryTheory.Sheaf DifferentialGradedModule unitDGAlgebra

namespace LeftDifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp)}

/-- The left action of a left differential graded module, at a section transported along an
equality of degrees. -/
theorem mul_castHom_heq (Q : LeftDifferentialGradedModule.{t, t, m} A) (i : ℤ) {n n' : ℤ}
    (h : n = n') (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U) (x : (Q.complex.X n).val.obj U) :
    HEq ((Q.mul i n').app U a (castHom Q.complex.X h U x)) ((Q.mul i n).app U a x) := by
  subst h
  rfl

/-- **A left differential graded `A`-module is a differential graded `(A, (O, 0))`-bimodule**:
the right action of `(O, 0)` is scalar multiplication in degree zero. -/
noncomputable def unitBimodule (Q : LeftDifferentialGradedModule.{t, t, m} A) :
    DifferentialGradedBimodule.{t, t, m} A (unitDGAlgebra Osharp) where
  complex := Q.complex
  rightMul := (ofComplex Q.complex).mul
  leftMul := Q.mul
  left_assoc i j n U a a' x := (Q.mul_assoc i j n U a a' x).symm
  right_assoc := (ofComplex Q.complex).mul_assoc
  left_right_assoc i n j U a x b := by
    change HEq (ofComplexMulApp Q.complex (i + n) j U ((Q.mul i n).app U a x) b)
      ((Q.mul i (n + j)).app U a (ofComplexMulApp Q.complex n j U x b))
    by_cases h : j = 0
    · rw [ofComplexMulApp_of _ h, ofComplexMulApp_of _ h]
      refine (heq_castHom _ _ U _).trans ?_
      refine HEq.trans ?_ (mul_castHom_heq Q i _ U a _).symm
      rw [(Q.mul i n).map_smul_right]
    · rw [ofComplexMulApp_of_ne _ h, ofComplexMulApp_of_ne _ h, map_zero]
      have h0 : ∀ (a b : ℤ) (_ : a = b),
          HEq (0 : (Q.complex.X a).val.obj U) (0 : (Q.complex.X b).val.obj U) := by
        rintro a b rfl
        rfl
      exact h0 _ _ (add_assoc i n j)
  one_left := Q.one_mul
  one_right := (ofComplex Q.complex).mul_one
  leibniz_left := Q.leibniz
  leibniz_right := (ofComplex Q.complex).leibniz

/-- The underlying complex of `Q.unitBimodule` is the underlying complex of `Q`. -/
@[simp]
theorem unitBimodule_complex (Q : LeftDifferentialGradedModule.{t, t, m} A) :
    Q.unitBimodule.complex = Q.complex :=
  rfl

end LeftDifferentialGradedModule

namespace DifferentialGradedModule

section OpRegular

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, m} R}

/-- A unit-preserving homomorphism `φ : A ⟶ B`, read as a homomorphism of right differential
graded `A.op`-modules from `A.op` to `B` viewed as a left `A`-module. -/
noncomputable def opRegularHom (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    regularModule A.op ⟶ (φ.toBimodule hφ).toLeftDifferentialGradedModule.opRight where
  toHomologicalComplex := φ.toHomologicalComplex
  map_mul n i U x y := by
    refine (congrArg (fun z => (φ.toHomologicalComplex.f (n + i)).val.app U z)
      (A.opMul_app n i U x y)).trans ?_
    refine Eq.trans ?_ ((φ.toBimodule hφ).toLeftDifferentialGradedModule.opRightMul_app n i U
      ((φ.toHomologicalComplex.f n).val.app U x) y).symm
    rw [gradedCast_hom_f_app, hom_f_app_zsmul, Int.mul_comm n i]
    exact congrArg (fun z => gradedCast (fun q ↦ ((B.complex.X q).val.obj U)) (Int.add_comm i n)
      (((i * n).negOnePow : ℤ) • z)) (φ.map_mul i n U y x)

/-- The underlying morphism of complexes of `opRegularHom φ hφ` is that of `φ`. -/
@[simp]
theorem opRegularHom_toHomologicalComplex (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    (opRegularHom φ hφ).toHomologicalComplex = φ.toHomologicalComplex :=
  rfl

end OpRegular

section KFlat

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J (Type u)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A B : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}

omit [HasWeakSheafify J (Type u)] in
/-- A K-flat right differential graded `A`-module `P`, read as a left `A.op`-module, has
acyclic tensor product with every acyclic right differential graded `A.op`-module. -/
theorem acyclic_dgTensor_opLeft_of_isKFlat {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsKFlat P) (Y : DifferentialGradedModule.{u, u, u} A.op)
    (hY : Y.complex.Acyclic) : (RelativeTensor.dgTensor Y P.opLeft).Acyclic := fun i =>
  (_root_.exactAt_iff_of_quasiIsoAt (RelativeTensor.dgTensorOpIso P Y).hom i).2
    (hP Y.unopLeft hY i)

omit [HasWeakSheafify J (Type u)] in
/-- **Tensoring a K-flat module with a quasi-isomorphism in the second variable.** For a
K-flat right differential graded `A`-module `P` and a unit-preserving quasi-isomorphism
`φ : A ⟶ B`, the map `A.op ⊗_{A.op} P ⟶ B ⊗_{A.op} P` induced by `φ` is a quasi-isomorphism. -/
theorem quasiIso_dgTensorFunctor_map_opRegularHom {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsKFlat P) (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (hqis : QuasiIso φ.toHomologicalComplex) :
    QuasiIso ((RelativeTensor.dgTensorFunctor P.opLeft).map (opRegularHom φ hφ)) := by
  let D' := RelativeTensor.tensorFunctorDataDgTensorRight P.opLeft.unitBimodule
  have hcone : (cone (opRegularHom φ hφ)).complex.Acyclic :=
    (acyclic_cone_iff_quasiIso _ (opRegularHom φ hφ)).2 hqis
  have hT : (D'.functor.obj (cone (opRegularHom φ hφ))).complex.Acyclic :=
    acyclic_dgTensor_opLeft_of_isKFlat hP _ hcone
  have hC : (cone (D'.functor.map (opRegularHom φ hφ))).complex.Acyclic := fun n =>
    (hT n).of_iso (D'.coneComplexIso (opRegularHom φ hφ)).symm
  exact (acyclic_cone_iff_quasiIso _ _).1 hC

omit [HasWeakSheafify J (Type u)] in
/-- A morphism into the tensor product with a left module which is propositionally equal to a
second one is a quasi-isomorphism as soon as a morphism into the tensor product with the second
one, agreeing with it on every local section, is. -/
theorem quasiIso_of_heq_app {P : DifferentialGradedModule.{u, u, u} A}
    {K : CochainComplex (SheafOfModules.{u} (toRingCat J Osharp)) ℤ}
    {N N' : LeftDifferentialGradedModule.{u, u, u} A} (h : N' = N)
    (k : K ⟶ RelativeTensor.dgTensor P N') (k' : K ⟶ RelativeTensor.dgTensor P N)
    (hk : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (K.X i).val.obj U),
      HEq ((k.f i).val.app U x) ((k'.f i).val.app U x)) [QuasiIso k] : QuasiIso k' := by
  subst h
  have e : k = k' := by
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    exact eq_of_heq (hk i U x)
  rw [← e]
  infer_instance

end KFlat

end DifferentialGradedModule

namespace RelativeTensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {A : GradedAlgebra.{u, u} (toRingCat J Osharp)}

/-- Local sections `x ⊗ y` of tensor products with two equal left graded modules, of equal
total degrees with corresponding indices and heterogeneously equal arguments, are
heterogeneously equal. -/
theorem tmul_heq_of_eq (P : GradedModule.{u, u, u} A) {N N' : LeftGradedModule.{u, u, u} A}
    (hN : N = N') {n n' : ℤ} (hn : n = n') {p : TensorIndex n} {p' : TensorIndex n'}
    (hp : p.1 = p'.1) (X : Cᵒᵖ) {x : (P.piece p.1.1).val.obj X}
    {x' : (P.piece p'.1.1).val.obj X} (hx : HEq x x') {y : (N.piece p.1.2).val.obj X}
    {y' : (N'.piece p'.1.2).val.obj X} (hy : HEq y y') :
    HEq (tmul P N n p X x y) (tmul P N' n' p' X x' y') := by
  subst hN
  exact tmul_heq.{u, u, u} P N hn hp X hx hy

end RelativeTensor

namespace DifferentialGradedModule

section Unit

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J (Type u)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A B : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}

omit [HasWeakSheafify J (Type u)] in
/-- **The unit of extension of scalars along a quasi-isomorphism is a quasi-isomorphism at a
K-flat module.** Let `φ : A ⟶ B` be a unit-preserving homomorphism of sheaves of differential
graded algebras inducing an isomorphism on cohomology sheaves, and let `P` be a K-flat right
differential graded `A`-module. Then `x ↦ x ⊗ 1 : P ⟶ P ⊗_A B` is a quasi-isomorphism. -/
theorem quasiIso_extensionUnit_of_isKFlat {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsKFlat P) (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (hqis : QuasiIso φ.toHomologicalComplex) :
    QuasiIso (extensionUnit φ hφ (RelativeTensor.tensorFunctorDataDgTensorRight
      (φ.toBimodule hφ)) P).toHomologicalComplex := by
  have := quasiIso_dgTensorFunctor_map_opRegularHom hP φ hφ hqis
  let k := (RelativeTensor.dgUnitorIso P.opLeft).inv ≫
    (RelativeTensor.dgTensorFunctor P.opLeft).map (opRegularHom φ hφ) ≫
      (RelativeTensor.dgTensorOpIso P
        (φ.toBimodule hφ).toLeftDifferentialGradedModule.opRight).hom
  have h₁ : QuasiIso (RelativeTensor.dgUnitorIso P.opLeft).inv := inferInstance
  have h₂ : QuasiIso (RelativeTensor.dgTensorOpIso P
      (φ.toBimodule hφ).toLeftDifferentialGradedModule.opRight).hom := inferInstance
  have : QuasiIso k :=
    quasiIso_comp _ _ (hφ := h₁) (hφ' := quasiIso_comp _ _ (hφ := this) (hφ' := h₂))
  refine quasiIso_of_heq_app (LeftDifferentialGradedModule.opRight_unopLeft _) k _ ?_
  intro i U x
  let Bl := (φ.toBimodule hφ).toLeftDifferentialGradedModule
  let q : TensorIndex i := ⟨(0, i), zero_add i⟩
  show HEq ((RelativeTensor.opSwap P Bl.opRight i).val.app U
      ((RelativeTensor.gradedTensorMapRight (RelativeTensor.gMap (opRegularHom φ hφ))
        (RelativeTensor.gN P.opLeft) i).val.app U
          (RelativeTensor.tmul (RelativeTensor.gP (regularModule A.op))
            (RelativeTensor.gN P.opLeft) i q U (A.op.one.eval U) x)))
    (castHom (RelativeTensor.dgTensor P Bl).X (add_zero i) U
      (RelativeTensor.tmul (RelativeTensor.gP P) (RelativeTensor.gN Bl) (i + 0)
        (RelativeTensor.tensorIndexPair i 0) U x (B.one.eval U)))
  refine HEq.trans (heq_of_eq ((congrArg
    (fun z => (RelativeTensor.opSwap P Bl.opRight i).val.app U z)
    (RelativeTensor.gradedTensorMapRight_tmul (RelativeTensor.gMap (opRegularHom φ hφ))
      (RelativeTensor.gN P.opLeft) i q U (A.op.one.eval U) x)).trans
    (RelativeTensor.opSwap_tmul P Bl.opRight i q U _ x))) ?_
  rw [show q.1.1 * q.1.2 = 0 from zero_mul _, Int.negOnePow_zero, Units.val_one, one_smul]
  refine HEq.trans ?_ (heq_castHom _ _ U _).symm
  exact RelativeTensor.tmul_heq_of_eq (RelativeTensor.gP P)
    (congrArg RelativeTensor.gN (LeftDifferentialGradedModule.opRight_unopLeft Bl))
    (add_zero i).symm rfl U HEq.rfl (heq_of_eq (hφ U))

end Unit

end DifferentialGradedModule

end SheafOfModules
