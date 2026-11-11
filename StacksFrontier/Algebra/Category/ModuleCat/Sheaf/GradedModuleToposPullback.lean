module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleOfScalarRestrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposInverseImageTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# Pull and push for sheaves of graded modules: the pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, `A` a sheaf of graded
`O_C`-algebras, `B` a sheaf of graded `O_D`-algebras and `φ : f⁻¹B ⟶ A` a homomorphism of
sheaves of graded `f⁻¹O_D`-algebras (`A` read over `f⁻¹O_D` along `f♯`). Following
[Stacks, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7), the functor

`f^* : Mod(B) ⥤ Mod(A)`

is the composite

`Mod(B) --f⁻¹--> Mod(f⁻¹B) --(- ⊗_{f⁻¹B} A)--> Mod(A)`,

so that `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`: the inverse image `f⁻¹N` is the right graded
`f⁻¹B`-module with pieces `f⁻¹N^n` and multiplication `f⁻¹ν_{n,m}`, `A` is a graded
`(f⁻¹B, A)`-bimodule through `φ`, and the graded tensor product of Section 0FR4 of the two is a
right graded `A`-module. Each step, and so the composite, is enhanced to homomorphisms
homogeneous of degree `n`, i.e. to a functor of graded categories
`f^* : Mod^gr(B) ⥤ Mod^gr(A)`, doing the same thing on objects.

## Main definitions

* `SheafOfModules.GradedAlgebra.UnitalHom.toBimodule`: `B` as a graded `(A, B)`-bimodule through
  a unital homomorphism `A ⟶ B`.
* `SheafOfModules.RelativeTensor.gradedTensorRightHom` and
  `SheafOfModules.RelativeTensor.gradedTensorRightFunctor`: the functor `- ⊗_A N` on right graded
  modules, and `SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree` its action on
  homomorphisms homogeneous of degree `d`.
* `Stacks.Sheaves.GradedModuleToposPullback.inverseImageAlgebra`, `scalarMap` and
  `restrictedAlgebra`: `f⁻¹B` and `A` as sheaves of graded `f⁻¹O_D`-algebras, the second along
  `f♯ : f⁻¹O_D ⟶ O_C`.
* `Stacks.Sheaves.GradedModuleToposPullback.tensorAlgebra`: the functor
  `- ⊗_{f⁻¹B, φ} A : Mod(f⁻¹B) ⥤ Mod(A)`.
* `Stacks.Sheaves.GradedModuleToposPullback.pullbackObj`: **`f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`**, and
  `pullbackFunctor` the functor `f^* : Mod(B) ⥤ Mod(A)`, which is `f⁻¹` followed by
  `- ⊗_{f⁻¹B, φ} A` on the nose.
* `Stacks.Sheaves.GradedModuleToposPullback.pullbackHomOfDegree`: `f^*` on homomorphisms
  homogeneous of degree `d`.

## Implementation notes

The graded tensor product `SheafOfModules.RelativeTensor.gradedTensorRight` is formed over a
sheaf of commutative rings which both algebras are algebras over; here that sheaf is `f⁻¹O_D`,
in the form `Stacks.Sheaves.RingedToposModules.RingedToposHom.inverseImageStructureSheaf`, whose
underlying sheaf of rings is the inverse-image sheaf of rings on the nose. The tensor product is
then a right graded module over `A` read over `f⁻¹O_D`, and
`SheafOfModules.GradedModule.ofScalarRestrict` makes it a right graded module over `A` itself,
with the same pieces and multiplication, which is what `Mod(A)` asks for.

The universe of the module sections of the source ringed topos is `max u v z`, the shape
`SheafOfModules.RelativeTensor.gradedTensorRight` needs, for a site `C : Type u` with
`Category.{v} C`; the target is arbitrary.

## References

* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t a m v u z v' u' w'

/-! ### An algebra as a bimodule through a unital homomorphism -/

namespace SheafOfModules.GradedAlgebra.UnitalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- **`B` as a graded `(A, B)`-bimodule through a unital homomorphism `φ : A ⟶ B`**: a
homogeneous section `a` of `A` acts on the left as `φ a`, and `B` acts on the right by its
multiplication. -/
def toBimodule (φ : UnitalHom A B) : GradedBimodule.{t, a, a} A B where
  piece := B.piece
  rightMul := B.mul
  leftMul n m := (B.mul n m).compLeft (φ.app n).val
  left_assoc i j n U x x' y := by
    change HEq ((B.mul i (j + n)).app U ((φ.app i).val.app U x)
        ((B.mul j n).app U ((φ.app j).val.app U x') y))
      ((B.mul (i + j) n).app U ((φ.app (i + j)).val.app U ((A.mul i j).app U x x')) y)
    rw [φ.map_mul]
    exact (B.mul_assoc i j n U _ _ y).symm
  right_assoc n i j U x b b' := B.mul_assoc n i j U x b b'
  left_right_assoc i n j U x y b := B.mul_assoc i n j U ((φ.app i).val.app U x) y b
  one_left n U y := by
    change HEq ((B.mul 0 n).app U ((φ.app 0).val.app U (A.one.eval U)) y) y
    rw [φ.map_one]
    exact B.one_mul n U y
  one_right n U y := B.mul_one n U y

/-- The pieces of `φ.toBimodule` are those of `B`. -/
theorem toBimodule_piece (φ : UnitalHom A B) (n : ℤ) : φ.toBimodule.piece n = B.piece n := rfl

/-- The left action on `φ.toBimodule` is multiplication by the image under `φ`. -/
theorem toBimodule_leftMul_app (φ : UnitalHom A B) (n k : ℤ) (U : Cᵒᵖ)
    (x : (A.piece n).val.obj U) (y : (B.piece k).val.obj U) :
    (φ.toBimodule.leftMul n k).app U x y = (B.mul n k).app U ((φ.app n).val.app U x) y := rfl

/-- The right action on `φ.toBimodule` is the multiplication of `B`. -/
theorem toBimodule_rightMul (φ : UnitalHom A B) (n k : ℤ) :
    φ.toBimodule.rightMul n k = B.mul n k := rfl

end SheafOfModules.GradedAlgebra.UnitalHom

/-! ### The functor `- ⊗_A N`, on homomorphisms and on homogeneous homomorphisms -/

namespace SheafOfModules.RelativeTensor

open Stacks CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A B : GradedAlgebra.{t, max u v z} (toRingCat J Osharp)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify J AddCommGrpCat.{max u v z}]

/-- Local sections `x ⊗ y` in equal summands of equal elements are equal. -/
theorem tmul_congr (P : GradedModule.{t, max u v z, max u v z} A)
    (L : LeftGradedModule.{t, max u v z, max u v z} A) {n : ℤ} {p p' : TensorIndex n}
    (hp : p = p') (X : Cᵒᵖ) {x : (P.piece p.1.1).val.obj X} {x' : (P.piece p'.1.1).val.obj X}
    {y : (L.piece p.1.2).val.obj X} {y' : (L.piece p'.1.2).val.obj X} (hx : HEq x x')
    (hy : HEq y y') : tmul P L n p X x y = tmul P L n p' X x' y' := by
  subst hp
  cases hx
  cases hy
  rfl

/-- Transport of the total degree of a local section `x ⊗ y`. -/
theorem castHom_tmul (P : GradedModule.{t, max u v z, max u v z} A)
    (L : LeftGradedModule.{t, max u v z, max u v z} A) {n n' : ℤ} (h : n = n')
    (p : TensorIndex n) (X : Cᵒᵖ) (x : (P.piece p.1.1).val.obj X)
    (y : (L.piece p.1.2).val.obj X) :
    castHom (fun k => gradedTensor P L k) h X (tmul P L n p X x y) =
      tmul P L n' ⟨p.1, h ▸ p.2⟩ X x y := by
  subst h
  rfl

variable {M M' M'' : GradedModule.{t, max u v z, max u v z} A}
  (N : GradedBimodule.{t, max u v z, max u v z} A B)

/-- The balanced family `(x, y) ↦ (h x) ⊗ y` attached to a homomorphism `h : M ⟶ M'`. -/
def mapBalancedRight (h : M ⟶ M') : BalancedRight M N (gradedTensorRight M' N) where
  app n :=
    { app := fun p => ((tmulBalanced M' N.toLeftGradedModule n).app p).compLeft (h.app p.1.1).val
      balanced := fun i X x a y => by
        change tmul M' N.toLeftGradedModule n (leftIndex i) X
            ((h.app (i.1.1 + i.1.2.1)).val.app X (M.smul i.1.1 i.1.2.1 X x a)) y =
          tmul M' N.toLeftGradedModule n (rightIndex i) X ((h.app i.1.1).val.app X x)
            (N.toLeftGradedModule.smul i.1.2.1 i.1.2.2 X a y)
        rw [h.map_smul]
        exact (tmulBalanced M' N.toLeftGradedModule n).balanced i X _ a y }
  map_smul n i p U x y b :=
    (gradedTensorRight_smul_tmul M' N n i p U ((h.app p.1.1).val.app U x) y b).symm

/-- **The homomorphism `M ⊗_A N ⟶ M' ⊗_A N` of right graded `B`-modules** induced by a
homomorphism `h : M ⟶ M'` of right graded `A`-modules. -/
def gradedTensorRightHom (h : M ⟶ M') : gradedTensorRight M N ⟶ gradedTensorRight M' N :=
  (mapBalancedRight N h).descRight

/-- `gradedTensorRightHom N h` sends `x ⊗ y` to `(h x) ⊗ y`. -/
theorem gradedTensorRightHom_tmul (h : M ⟶ M') (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((gradedTensorRightHom N h).app n).val X
        (tmul M N.toLeftGradedModule n p X x y) =
      tmul M' N.toLeftGradedModule n p X ((h.app p.1.1).val.app X x) y :=
  (mapBalancedRight N h).descRight_tmul n p X x y

/-- **The functor `- ⊗_A N : Mod(A) ⥤ Mod(B)`** of right graded modules, for a graded
`(A, B)`-bimodule `N`. -/
@[stacks 0FR4 "the functor - ⊗_A N : Mod(A) → Mod(B)"]
def gradedTensorRightFunctor :
    GradedModule.{t, max u v z, max u v z} A ⥤ GradedModule.{t, max u v z, max u v z} B where
  obj M := gradedTensorRight M N
  map h := gradedTensorRightHom N h
  map_id M := GradedModule.Hom.ext fun n => gradedTensor_hom_ext M N.toLeftGradedModule
    fun p X x y => gradedTensorRightHom_tmul N (𝟙 M) n p X x y
  map_comp h h' := GradedModule.Hom.ext fun n => gradedTensor_hom_ext _ N.toLeftGradedModule
    fun p X x y => by
      refine (gradedTensorRightHom_tmul N (h ≫ h') n p X x y).trans ?_
      refine Eq.trans ?_ (congrArg
        (PresheafOfModules.Hom.app ((gradedTensorRightHom N h').app n).val X)
        (gradedTensorRightHom_tmul N h n p X x y)).symm
      exact (gradedTensorRightHom_tmul N h' n p X _ y).symm

/-- `gradedTensorRightFunctor N` acts on objects by `gradedTensorRight`. -/
theorem gradedTensorRightFunctor_obj (M : GradedModule.{t, max u v z, max u v z} A) :
    (gradedTensorRightFunctor N).obj M = gradedTensorRight M N := rfl

/-- The balanced family `(x, y) ↦ (g x) ⊗ y` attached to a homomorphism `g : M ⟶ M'`
homogeneous of degree `d`, as a degree-zero family into the shift of `M' ⊗_A N` by `d`. -/
def homOfDegreeBalancedRight {d : ℤ} (g : GradedHomOfDegree M M' d) :
    BalancedRight M N ((gradedTensorRight M' N).shift d) where
  app n :=
    { app := fun p => ((tmulBalanced M' N.toLeftGradedModule (n + d)).app
          ⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩).compLeft
        (g.app p.1.1 (p.1.1 + d) rfl).val
      balanced := fun i X x a y => by
        change tmul M' N.toLeftGradedModule (n + d) ⟨(i.1.1 + i.1.2.1 + d, i.1.2.2), _⟩ X
            ((g.app (i.1.1 + i.1.2.1) (i.1.1 + i.1.2.1 + d) rfl).val.app X
              (M.smul i.1.1 i.1.2.1 X x a)) y =
          tmul M' N.toLeftGradedModule (n + d) ⟨(i.1.1 + d, i.1.2.1 + i.1.2.2), _⟩ X
            ((g.app i.1.1 (i.1.1 + d) rfl).val.app X x)
            (N.toLeftGradedModule.smul i.1.2.1 i.1.2.2 X a y)
        have hb := (tmulBalanced M' N.toLeftGradedModule (n + d)).balanced
          ⟨(i.1.1 + d, i.1.2.1, i.1.2.2), by have := i.2; dsimp only at this ⊢; omega⟩ X
          ((g.app i.1.1 (i.1.1 + d) rfl).val.app X x) a y
        refine Eq.trans ?_ hb
        refine tmul_congr M' N.toLeftGradedModule (Subtype.ext (by
          change (i.1.1 + i.1.2.1 + d, i.1.2.2) = (i.1.1 + d + i.1.2.1, i.1.2.2)
          exact Prod.ext (by dsimp only; omega) rfl)) X ?_ HEq.rfl
        refine (g.app_heq rfl (show i.1.1 + i.1.2.1 + d = i.1.1 + d + i.1.2.1 by
          omega) rfl X HEq.rfl).trans ?_
        exact heq_of_eq (g.map_mul i.1.1 (i.1.1 + d) rfl i.1.2.1 X x a) }
  map_smul n i p U x y b := by
    change tmul M' N.toLeftGradedModule (n + i + d) ⟨(p.1.1 + d, p.1.2 + i), _⟩ U
        ((g.app p.1.1 (p.1.1 + d) rfl).val.app U x)
        ((rightMulL N p.1.2 i).app U y b) =
      castHom (gradedTensorRight M' N).piece (by omega : n + d + i = n + i + d) U
        ((gradedTensorRight M' N).smul (n + d) i U
          (tmul M' N.toLeftGradedModule (n + d) ⟨(p.1.1 + d, p.1.2), _⟩ U
            ((g.app p.1.1 (p.1.1 + d) rfl).val.app U x) y) b)
    rw [gradedTensorRight_smul_tmul]
    refine Eq.trans ?_ (castHom_tmul M' N.toLeftGradedModule _ _ U _ _).symm
    exact tmul_congr M' N.toLeftGradedModule (Subtype.ext rfl) U HEq.rfl HEq.rfl

/-- **The homomorphism `M ⊗_A N ⟶ M' ⊗_A N` homogeneous of degree `d`** induced by a homomorphism
`g : M ⟶ M'` homogeneous of degree `d`: the action of `- ⊗_A N` on homogeneous morphisms,
determined by `x ⊗ y ↦ (g x) ⊗ y`. -/
@[stacks 0FR4 "- ⊗_A N : Mod^gr(A) → Mod^gr(B) on homogeneous homomorphisms of degree n"]
def gradedTensorRightHomOfDegree {d : ℤ} (g : GradedHomOfDegree M M' d) :
    GradedHomOfDegree (gradedTensorRight M N) (gradedTensorRight M' N) d :=
  (GradedHomOfDegree.shiftHomEquiv _ _ d).symm (homOfDegreeBalancedRight N g).descRight

end SheafOfModules.RelativeTensor

/-! ### The pullback along a morphism of ringed topoi -/

namespace Stacks.Sheaves.GradedModuleToposPullback

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedModuleInverseImage SheafOfModules.RelativeTensor

variable {X : RingedTopos.{v, u, max u v z}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v z} RingCat.{max u v z})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{max u v z})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v z})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The inverse image `f⁻¹O_D`, as the sheaf of rings underlying a sheaf of commutative rings on
the source. -/
abbrev baseRing : Sheaf X.J RingCat.{max u v z} :=
  CategoryTheory.Sheaf.toRingCat X.J f.inverseImageStructureSheaf

/-- **`f⁻¹B`**, the inverse image of a sheaf of graded `O_D`-algebras, a sheaf of graded
`f⁻¹O_D`-algebras. -/
abbrev inverseImageAlgebra
    (B : SheafOfModules.GradedAlgebra.{w', w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    SheafOfModules.GradedAlgebra.{max u v z, max u v z} (baseRing f) :=
  inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B

/-- The inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure map. -/
abbrev scalarMap : baseRing f ⟶ CategoryTheory.Sheaf.toRingCat X.J X.O :=
  f.fSharpInverseImage

/-- **`A` read as a sheaf of graded `f⁻¹O_D`-algebras** along `f♯ : f⁻¹O_D ⟶ O_C`. -/
abbrev restrictedAlgebra
    (A : SheafOfModules.GradedAlgebra.{max u v z, max u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.GradedAlgebra.{max u v z, max u v z} (baseRing f) :=
  SheafOfModules.GradedAlgebra.scalarRestrict (scalarMap f) A

variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify X.J AddCommGrpCat.{max u v z}]
  {A : SheafOfModules.GradedAlgebra.{max u v z, max u v z}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : SheafOfModules.GradedAlgebra.{w', w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- **The functor `- ⊗_{f⁻¹B, φ} A : Mod(f⁻¹B) ⥤ Mod(A)`**, for a homomorphism
`φ : f⁻¹B ⟶ A` of sheaves of graded `f⁻¹O_D`-algebras: the graded tensor product with `A`, read
as a graded `(f⁻¹B, A)`-bimodule through `φ`, a right graded `A`-module. -/
@[stacks 0FR7 "the functor - ⊗_{f⁻¹B} A : Mod(f⁻¹B) ⥤ Mod(A) of Section 0FR4, A a graded \
(f⁻¹B, A)-bimodule through φ : f⁻¹B → A"]
def tensorAlgebra
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A)) :
    SheafOfModules.GradedModule.{max u v z, max u v z, max u v z} (inverseImageAlgebra f B) ⥤
      SheafOfModules.GradedModule.{max u v z, max u v z, max u v z} A :=
  gradedTensorRightFunctor φ.toBimodule ⋙
    SheafOfModules.GradedModule.ofScalarRestrictFunctor (scalarMap f) A

/-- **The pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` of a right graded `B`-module** along a morphism of
ringed topoi `f` and a homomorphism `φ : f⁻¹B ⟶ A` of sheaves of graded `f⁻¹O_D`-algebras: the
graded tensor product of the inverse image `f⁻¹N`, a right graded `f⁻¹B`-module, with `A`, a
graded `(f⁻¹B, A)`-bimodule through `φ`. -/
@[stacks 0FR7 "f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A"]
def pullbackObj
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A))
    (N : SheafOfModules.GradedModule.{w', w', w'} B) :
    SheafOfModules.GradedModule.{max u v z, max u v z, max u v z} A :=
  (tensorAlgebra f φ).obj
    (inverseImageGradedModule f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N)

/-- The degree-`n` piece of `f^*N` is degree `n` of the graded tensor product
`f⁻¹N ⊗_{f⁻¹B} A`, with its `O_C`-module structure through `A`. -/
theorem pullbackObj_piece
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A))
    (N : SheafOfModules.GradedModule.{w', w', w'} B) (n : ℤ) :
    (pullbackObj f φ N).piece n =
      SheafOfModules.GradedModule.liftPiece (scalarMap f)
        (gradedTensorRight
          (inverseImageGradedModule f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) N)
          φ.toBimodule) n :=
  rfl

/-- **The pullback functor `f^* : Mod(B) ⥤ Mod(A)`** of right graded modules along a morphism of
ringed topoi and a homomorphism `φ : f⁻¹B ⟶ A`: the inverse image `f⁻¹ : Mod(B) ⥤ Mod(f⁻¹B)`
followed by `- ⊗_{f⁻¹B, φ} A : Mod(f⁻¹B) ⥤ Mod(A)`. -/
@[stacks 0FR7 "f^* : Mod(B) ⥤ Mod(A), the composite of f⁻¹ and - ⊗_{f⁻¹B, φ} A"]
def pullbackFunctor
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A)) :
    SheafOfModules.GradedModule.{w', w', w'} B ⥤
      SheafOfModules.GradedModule.{max u v z, max u v z, max u v z} A :=
  inverseImageGradedModuleFunctor f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
    tensorAlgebra f φ

/-- `f^*` acts on objects by `pullbackObj`. -/
theorem pullbackFunctor_obj
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A))
    (N : SheafOfModules.GradedModule.{w', w', w'} B) :
    (pullbackFunctor f φ).obj N = pullbackObj f φ N :=
  rfl

/-- **`- ⊗_{f⁻¹B, φ} A` on homomorphisms homogeneous of degree `d`.** -/
@[stacks 0FR7 "- ⊗_{f⁻¹B} A on homogeneous morphisms of degree n"]
def tensorAlgebraHomOfDegree
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A))
    {M M' : SheafOfModules.GradedModule.{max u v z, max u v z, max u v z}
      (inverseImageAlgebra f B)} {d : ℤ}
    (g : SheafOfModules.GradedHomOfDegree M M' d) :
    SheafOfModules.GradedHomOfDegree ((tensorAlgebra f φ).obj M) ((tensorAlgebra f φ).obj M') d :=
  SheafOfModules.GradedModule.ofScalarRestrictHomOfDegree (scalarMap f)
    (gradedTensorRightHomOfDegree φ.toBimodule g)

/-- **`f^*` as a functor of graded categories `Mod^gr(B) ⥤ Mod^gr(A)`, on homogeneous morphisms
of degree `d`**: the inverse image of a homomorphism homogeneous of degree `d`, followed by
`- ⊗_{f⁻¹B, φ} A`. On objects it is `pullbackObj`. -/
@[stacks 0FR7 "f^* as a functor of graded categories, on homogeneous morphisms of degree n"]
def pullbackHomOfDegree
    (φ : SheafOfModules.GradedAlgebra.UnitalHom (inverseImageAlgebra f B) (restrictedAlgebra f A))
    {N N' : SheafOfModules.GradedModule.{w', w', w'} B} {d : ℤ}
    (g : SheafOfModules.GradedHomOfDegree N N' d) :
    SheafOfModules.GradedHomOfDegree (pullbackObj f φ N) (pullbackObj f φ N') d :=
  tensorAlgebraHomOfDegree f φ
    (inverseImageGradedHomOfDegree f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) g)

end Stacks.Sheaves.GradedModuleToposPullback
