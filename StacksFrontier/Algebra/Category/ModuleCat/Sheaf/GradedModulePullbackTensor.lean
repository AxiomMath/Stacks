module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedZeroDifferential
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` of sheaves of graded modules, and the adjunction

Let `F : C ⥤ D` be a continuous functor of small sites, read as the functor underlying a
morphism of ringed sites `f : (D, K, O_D) ⟶ (C, J, O_C)` in the opposite direction, with
structure map `α : O_C ⟶ f_*O_D` of its sheaves of commutative rings. Let `B` be a sheaf of
graded `O_C`-algebras on the target, `A` a sheaf of graded `O_D`-algebras on the source and
`φ : f⁻¹B ⟶ A` a homomorphism of sheaves of graded algebras. Following the source, the
pullback of a right graded `B`-module `N` is

`f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`,

the relative tensor product of the inverse image `f⁻¹N`, a right graded `f⁻¹B`-module, with
`A`, read as a graded `(f⁻¹B, A)`-bimodule through `φ`. This file constructs it and proves the
identification of Tag 0FR8:

`Hom_{Mod^gr(A)}(f^*N, M) = Hom_{Mod^gr(B)}(N, f_*M)`,

in every homogeneous degree, together with the adjunction `f^* ⊣ f_*` it gives.

## Main definitions

* `SheafOfModules.GradedTensorPullback.gradedInverseImageAlgebra` is the inverse image `f⁻¹B` of
  a sheaf of graded algebras, and `gradedInverseImageModule` the inverse image `f⁻¹N` of a right
  graded `B`-module, a right graded `f⁻¹B`-module.
* `SheafOfModules.GradedTensorPullback.gradedBimodule` is `A` as a graded `(f⁻¹B, A)`-bimodule
  through `φ`.
* `SheafOfModules.GradedTensorPullback.tensorPullbackObj` is **the pullback
  `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`**, and `tensorPullbackFunctor` the pullback functor
  `f^* : Mod(B) ⥤ Mod(A)` it defines.
* `SheafOfModules.GradedTensorPullback.structureSemilinearHom` is `φ` read as a homomorphism
  `B ⟶ f_*A` along `f`, the datum the direct image `f_*` of right graded modules is formed
  with.

## Main results

* `SheafOfModules.GradedTensorPullback.isPullback_tensorPullbackUnit`: the unit `N ⟶ f^*N`
  exhibits `f⁻¹N ⊗_{f⁻¹B, φ} A` as the pullback of `N`: every `φ`-semilinear homomorphism out
  of `N` factors uniquely through it.
* `SheafOfModules.GradedTensorPullback.tensorPullbackHomOfDegreeEquiv` is **Tag 0FR8**:
  `Hom^n(f^*N, M) = Hom^n(N, f_*M)` in every homogeneous degree `n`, and
  `SheafOfModules.GradedTensorPullback.tensorPullbackPushforwardAdjunction` is the adjunction
  `f^* ⊣ f_*`.

## Implementation notes

A sheaf of graded algebras is a sheaf of differential graded algebras with zero differential,
and a right graded module a right differential graded module with zero differential
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedZeroDifferential.lean`). The inverse image
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInverseImage.lean` and the
pullback `f⁻¹M ⊗_{f⁻¹A'} A` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackConstruction.lean` are
applied to that reading. The inverse image of `B` has zero differential, being the inverse image
of the zero differential, so `φ` is a homomorphism of differential graded algebras; and the
relative tensor product of two modules with zero differential has zero differential
(`dgPullbackObj_d`), so its homomorphisms of differential graded modules into a graded module
read with zero differential are exactly its homomorphisms of graded modules. The universal
property of the differential graded pullback, proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackAdjunction.lean`, is
thereby the universal property of `tensorPullbackObj`, and the identification in every degree is
then `SheafOfModules.GradedModule.PullbackData.homOfDegreeEquiv` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullback.lean`.

The graded module `tensorPullbackObj φ N` is the relative tensor product
`SheafOfModules.RelativeTensor.gradedTensorRight` of the graded modules, and it is the graded
module underlying the differential graded pullback on the nose
(`ofDifferentialGraded_dgPullbackObj`).

**The setting.** The hypotheses are those of the differential graded construction: two small
sites in one universe, the functor continuous, representably flat and final, and the sites,
the rings, the algebra pieces and the module sections all in that universe. Representable
flatness is what makes the inverse image of sheaves of modules exact and strong monoidal, as for
the inverse image of a morphism of ringed topoi. The inverse image `f⁻¹` of sheaves of modules
here is the pullback of sheaves of modules along the morphism of ringed sites, so `f⁻¹B` is the
sheaf of graded `O_D`-algebras `f^*B`; by the source, a homomorphism `f⁻¹B ⟶ A` of graded
`f⁻¹O_C`-algebras is the same thing as a homomorphism `f^*B ⟶ A` of graded `O_D`-algebras, and
`f⁻¹N ⊗_{f⁻¹B} A = f^*N ⊗_{f^*B} A`. The existence of the left adjoint of the direct image of
sheaves of modules, which the inverse image is, is an instance and not a hypothesis.

## References

* [Stacks Project, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8)
* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf Functor
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.DifferentialGradedInverseImage Stacks.DifferentialGradedPullbackConstruction

universe u

namespace SheafOfModules.GradedTensorPullback

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))

/-! ### Inverse images -/

section InverseImage

variable (B : GradedAlgebra.{u, u} (toRingCat J Osharp))

/-- **The inverse image `f⁻¹B` of a sheaf of graded algebras**: its homogeneous pieces are the
inverse images of the homogeneous pieces of `B`, and its multiplication is the multiplication of
`B` conjugated by the tensorator of the inverse image. -/
noncomputable def gradedInverseImageAlgebra : GradedAlgebra.{u, u} (toRingCat K Psharp) :=
  (inverseImageAlgebra α hO hP B.withZeroDifferential).toGradedAlgebra

/-- The degree-`n` piece of `f⁻¹B` is the inverse image of the degree-`n` piece of `B`. -/
theorem gradedInverseImageAlgebra_piece (n : ℤ) :
    (gradedInverseImageAlgebra α hO hP B).piece n = (inverseImageModules α hO hP).obj (B.piece n) :=
  rfl

/-- The differential of the inverse image of `B`, read with zero differential, is zero. -/
theorem inverseImageAlgebra_withZeroDifferential_d (i j : ℤ) :
    (inverseImageAlgebra α hO hP B.withZeroDifferential).complex.d i j = 0 := by
  change (inverseImageModules α hO hP).map 0 = 0
  exact Functor.map_zero _ _ _

variable {B}

/-- **The inverse image `f⁻¹N` of a right graded `B`-module**, a right graded `f⁻¹B`-module: its
homogeneous pieces are the inverse images of those of `N`, and its action is the action of `N`
conjugated by the tensorator of the inverse image. -/
noncomputable def gradedInverseImageModule (N : GradedModule.{u, u, u} B) :
    GradedModule.{u, u, u} (gradedInverseImageAlgebra α hO hP B) :=
  GradedModule.ofDifferentialGraded (inverseImageModule α hO hP N.withZeroDifferential)

/-- The differential of the inverse image of `N`, read with zero differential, is zero. -/
theorem inverseImageModule_withZeroDifferential_d (N : GradedModule.{u, u, u} B) (i j : ℤ) :
    (inverseImageModule α hO hP N.withZeroDifferential).complex.d i j = 0 := by
  rw [inverseImageModule_complex]
  change (inverseImageModules α hO hP).map 0 = 0
  exact Functor.map_zero _ _ _

end InverseImage

/-! ### The structure map and the pullback -/

section Pullback

variable {B : GradedAlgebra.{u, u} (toRingCat J Osharp)}
  {A : GradedAlgebra.{u, u} (toRingCat K Psharp)}
  (φ : GradedAlgebra.UnitalHom (gradedInverseImageAlgebra α hO hP B) A)

/-- The homomorphism `φ : f⁻¹B ⟶ A`, read as a homomorphism of the sheaves of differential
graded algebras with zero differential. -/
noncomputable def zeroDifferentialStructureHom :
    inverseImageAlgebra α hO hP B.withZeroDifferential ⟶ A.withZeroDifferential :=
  DifferentialGradedAlgebra.Hom.mk
    { f := φ.app
      comm' := fun i j _ => by
        change φ.app i ≫ 0 = (inverseImageModules α hO hP).map 0 ≫ φ.app j
        rw [Functor.map_zero, comp_zero]
        exact zero_comp.symm }
    φ.map_mul

/-- The homomorphism `zeroDifferentialStructureHom φ` is unital, `φ` being so. -/
theorem isUnital_zeroDifferentialStructureHom :
    (zeroDifferentialStructureHom α hO hP φ).IsUnital :=
  φ.map_one

/-- The homomorphism `φ : f⁻¹B ⟶ A` read as a semilinear homomorphism `B ⟶ f_*A` of the sheaves
of differential graded algebras with zero differential. -/
noncomputable abbrev dgSemilinearHom :
    DifferentialGradedAlgebra.SemilinearHom F (Stacks.PullbackColimit.toRingCatPullback α)
      B.withZeroDifferential A.withZeroDifferential :=
  Stacks.DifferentialGradedPullbackConstruction.semilinearHom α hO hP
    (zeroDifferentialStructureHom α hO hP φ)
    (isUnital_zeroDifferentialStructureHom α hO hP φ)

/-- **The homomorphism `φ : f⁻¹B ⟶ A` read as a homomorphism `B ⟶ f_*A` along `f`**, by
adjunction: on a local section it is `φ` applied to the image of the section under the unit of
the adjunction between inverse and direct image of sheaves of modules. -/
noncomputable def structureSemilinearHom :
    GradedAlgebra.SemilinearHom F (Stacks.PullbackColimit.toRingCatPullback α) B A :=
  (dgSemilinearHom α hO hP φ).toGradedAlgebraHom

/-- **`A` as a graded `(f⁻¹B, A)`-bimodule through `φ`**: a homogeneous section `b` of `f⁻¹B`
acts on the left as `φ b`, and `A` acts on the right by its own multiplication. -/
noncomputable def gradedBimodule :
    GradedBimodule.{u, u, u} (gradedInverseImageAlgebra α hO hP B) A :=
  (pullbackBimodule α hO hP (zeroDifferentialStructureHom α hO hP φ)
    (isUnital_zeroDifferentialStructureHom α hO hP φ)).toGradedBimodule

/-- **The pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` of a right graded `B`-module `N`**, a right graded
`A`-module: the relative tensor product of the inverse image `f⁻¹N` with `A`, read as a graded
`(f⁻¹B, A)`-bimodule through `φ`. -/
noncomputable def tensorPullbackObj (N : GradedModule.{u, u, u} B) : GradedModule.{u, u, u} A :=
  RelativeTensor.gradedTensorRight (gradedInverseImageModule α hO hP N)
    (gradedBimodule α hO hP φ)

/-- The degree-`n` piece of `f^*N` is degree `n` of the graded relative tensor product of
`f⁻¹N` with `A`. -/
theorem tensorPullbackObj_piece (N : GradedModule.{u, u, u} B) (n : ℤ) :
    (tensorPullbackObj α hO hP φ N).piece n =
      RelativeTensor.gradedTensor (gradedInverseImageModule α hO hP N)
        (gradedBimodule α hO hP φ).toLeftGradedModule n :=
  rfl

/-- The differential graded pullback of `N` read with zero differential. -/
noncomputable abbrev dgPullbackObj (N : GradedModule.{u, u, u} B) :
    DifferentialGradedModule.{u, u, u} A.withZeroDifferential :=
  Stacks.DifferentialGradedPullbackConstruction.pullbackObj α hO hP
    (zeroDifferentialStructureHom α hO hP φ)
    (isUnital_zeroDifferentialStructureHom α hO hP φ) N.withZeroDifferential

/-- The graded module underlying the differential graded pullback is `f^*N`. -/
theorem ofDifferentialGraded_dgPullbackObj (N : GradedModule.{u, u, u} B) :
    GradedModule.ofDifferentialGraded (dgPullbackObj α hO hP φ N) =
      tensorPullbackObj α hO hP φ N :=
  rfl

/-- The pure tensor `0 ⊗ y` of the graded relative tensor product is zero. -/
theorem tmul_zero_left {A' : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (P : GradedModule.{u, u, u} A') (L : LeftGradedModule.{u, u, u} A') (n : ℤ)
    (p : TensorIndex n) (X : Dᵒᵖ) (y : (L.piece p.1.2).val.obj X) :
    RelativeTensor.tmul P L n p X 0 y = 0 := by
  unfold RelativeTensor.tmul
  rw [PresheafOfModules.app_tmul_zero_left (RelativeTensor.tensorSumι P L p) X y, map_zero,
    map_zero]

/-- The pure tensor `x ⊗ 0` of the graded relative tensor product is zero. -/
theorem tmul_zero_right {A' : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (P : GradedModule.{u, u, u} A') (L : LeftGradedModule.{u, u, u} A') (n : ℤ)
    (p : TensorIndex n) (X : Dᵒᵖ) (x : (P.piece p.1.1).val.obj X) :
    RelativeTensor.tmul P L n p X x 0 = 0 := by
  unfold RelativeTensor.tmul
  rw [PresheafOfModules.app_tmul_zero_right (RelativeTensor.tensorSumι P L p) X x, map_zero,
    map_zero]

/-- A pure tensor `x ⊗ y` of the graded relative tensor product whose first factor vanishes is
zero. -/
theorem tmul_eq_zero_of_left {A' : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (P : GradedModule.{u, u, u} A') (L : LeftGradedModule.{u, u, u} A') (n : ℤ)
    (p : SheafOfModules.TensorIndex n) (X : Dᵒᵖ) {x : (P.piece p.1.1).val.obj X}
    (y : (L.piece p.1.2).val.obj X) (hx : x = 0) :
    RelativeTensor.tmul P L n p X x y = 0 := by
  subst hx
  exact tmul_zero_left P L n p X y

/-- A pure tensor `x ⊗ y` of the graded relative tensor product whose second factor vanishes is
zero. -/
theorem tmul_eq_zero_of_right {A' : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (P : GradedModule.{u, u, u} A') (L : LeftGradedModule.{u, u, u} A') (n : ℤ)
    (p : SheafOfModules.TensorIndex n) (X : Dᵒᵖ) (x : (P.piece p.1.1).val.obj X)
    {y : (L.piece p.1.2).val.obj X} (hy : y = 0) :
    RelativeTensor.tmul P L n p X x y = 0 := by
  subst hy
  exact tmul_zero_right P L n p X x

/-- **The differential graded pullback of a module with zero differential has zero
differential**: on a pure tensor `x ⊗ y` the differential is `dx ⊗ y ± x ⊗ dy`, and both
differentials vanish. -/
theorem dgPullbackObj_d (N : GradedModule.{u, u, u} B) (i j : ℤ) :
    (dgPullbackObj α hO hP φ N).complex.d i j = 0 := by
  by_cases h : (ComplexShape.up ℤ).Rel i j
  · obtain rfl : i + 1 = j := h
    refine RelativeTensor.gradedTensor_hom_ext
      (P := RelativeTensor.gP (inverseImageModule α hO hP N.withZeroDifferential))
      (N := (pullbackBimodule α hO hP (zeroDifferentialStructureHom α hO hP φ)
        (isUnital_zeroDifferentialStructureHom α hO hP φ)).toGradedBimodule.toLeftGradedModule) ?_
    intro p X x y
    refine (pullbackObj_d_tmul α hO hP (zeroDifferentialStructureHom α hO hP φ)
      (isUnital_zeroDifferentialStructureHom α hO hP φ) N.withZeroDifferential i p X x y).trans ?_
    have e0 : ∀ {M M' : SheafOfModules.{u} (toRingCat K Psharp)} (z : M.val.obj X),
        (0 : M ⟶ M').val.app X z = 0 := fun _ => rfl
    have hx : ((inverseImageModule α hO hP N.withZeroDifferential).complex.d p.1.1
        (p.1.1 + 1)).val.app X x = 0 := by
      rw [inverseImageModule_withZeroDifferential_d]
      rfl
    refine Eq.trans ?_ (e0 _).symm
    refine (congrArg₂ (fun a b => a + (Int.negOnePow p.1.1 : ℤ) • b)
      (tmul_eq_zero_of_left (RelativeTensor.gP (inverseImageModule α hO hP N.withZeroDifferential))
        (pullbackBimodule α hO hP (zeroDifferentialStructureHom α hO hP φ)
          (isUnital_zeroDifferentialStructureHom α hO hP φ)).toGradedBimodule.toLeftGradedModule
        (i + 1) (RelativeTensor.tensorIndexShiftLeft p) X y hx)
      (tmul_eq_zero_of_right (RelativeTensor.gP (inverseImageModule α hO hP N.withZeroDifferential))
        (pullbackBimodule α hO hP (zeroDifferentialStructureHom α hO hP φ)
          (isUnital_zeroDifferentialStructureHom α hO hP φ)).toGradedBimodule.toLeftGradedModule
        (i + 1) (RelativeTensor.tensorIndexShiftRight p) X x (e0 y))).trans ?_
    rw [smul_zero]
    exact add_zero _
  · exact (dgPullbackObj α hO hP φ N).complex.shape i j h

/-- **The unit `N ⟶ f^*N` of the pullback**, a `φ`-semilinear homomorphism of right graded
modules. On local sections it is `x ↦ x ⊗ 1`, read through the unit of the adjunction between
the inverse image and the direct image of sheaves of modules. -/
noncomputable def tensorPullbackUnit (N : GradedModule.{u, u, u} B) :
    GradedModule.SemilinearHom (structureSemilinearHom α hO hP φ) N
      (tensorPullbackObj α hO hP φ N) :=
  GradedModule.SemilinearHom.ofDifferentialGraded (dgSemilinearHom α hO hP φ)
    (Stacks.DifferentialGradedPullbackConstruction.pullbackUnit α hO hP
      (zeroDifferentialStructureHom α hO hP φ)
      (isUnital_zeroDifferentialStructureHom α hO hP φ) N.withZeroDifferential)

/-- The universal property of the differential graded pullback of `N` read with zero
differential. -/
noncomputable abbrev dgIsPullback (N : GradedModule.{u, u, u} B) :=
  Stacks.DifferentialGradedPullbackConstruction.isPullback_pullbackUnit α hO hP
    (zeroDifferentialStructureHom α hO hP φ) (isUnital_zeroDifferentialStructureHom α hO hP φ)
    N.withZeroDifferential

/-- The degree-`i` piece of `f^*N` is the degree-`i` term of the differential graded
pullback. -/
theorem tensorPullbackObj_piece_eq (N : GradedModule.{u, u, u} B) (i : ℤ) :
    (tensorPullbackObj α hO hP φ N).piece i = (dgPullbackObj α hO hP φ N).complex.X i :=
  rfl

/-- On local sections the unit of `f^*N` is the unit of the differential graded pullback. -/
theorem tensorPullbackUnit_app (N : GradedModule.{u, u, u} B) (i : ℤ) (V : Cᵒᵖ)
    (x : (N.piece i).val.obj V) :
    (tensorPullbackUnit α hO hP φ N).app i V x =
      (Stacks.DifferentialGradedPullbackConstruction.pullbackUnit α hO hP
        (zeroDifferentialStructureHom α hO hP φ) (isUnital_zeroDifferentialStructureHom α hO hP φ)
        N.withZeroDifferential).app i V x :=
  rfl

/-- Postcomposing the unit of `f^*N` with the homomorphism underlying a morphism of
differential graded modules is postcomposing the differential graded unit with it. -/
theorem tensorPullbackUnit_postcomp_app (N : GradedModule.{u, u, u} B)
    {P' : GradedModule.{u, u, u} A}
    (h : dgPullbackObj α hO hP φ N ⟶ P'.withZeroDifferential) (i : ℤ) (V : Cᵒᵖ)
    (x : (N.piece i).val.obj V) :
    ((tensorPullbackUnit α hO hP φ N).postcomp
        ((forgetToGradedModule A.withZeroDifferential).map h)).app i V x =
      ((Stacks.DifferentialGradedPullbackConstruction.pullbackUnit α hO hP
        (zeroDifferentialStructureHom α hO hP φ) (isUnital_zeroDifferentialStructureHom α hO hP φ)
        N.withZeroDifferential).postcomp h).app i V x :=
  rfl

/-- **`f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` is the pullback of `N`**: every `φ`-semilinear homomorphism
of right graded modules out of `N` factors uniquely through the unit `N ⟶ f^*N` by a
homomorphism of right graded `A`-modules. -/
noncomputable def isPullback_tensorPullbackUnit (N : GradedModule.{u, u, u} B) :
    GradedModule.IsPullback (tensorPullbackUnit α hO hP φ N) where
  desc {P'} θ' := (forgetToGradedModule A.withZeroDifferential).map
    ((dgIsPullback α hO hP φ N).desc
      (GradedModule.SemilinearHom.withZeroDifferential (dgSemilinearHom α hO hP φ) θ'))
  fac {P'} θ' := by
    refine GradedModule.SemilinearHom.ext fun i V x => ?_
    have h := (dgIsPullback α hO hP φ N).fac
      (GradedModule.SemilinearHom.withZeroDifferential (dgSemilinearHom α hO hP φ) θ')
    have h' := congrArg (fun z => DifferentialGradedModule.SemilinearHom.app z i V x) h
    refine (tensorPullbackUnit_postcomp_app α hO hP φ N _ i V x).trans ?_
    exact h'
  uniq {P'} θ' h hh :=
    congrArg (forgetToGradedModule A.withZeroDifferential).map
      ((dgIsPullback α hO hP φ N).uniq
        (GradedModule.SemilinearHom.withZeroDifferential (dgSemilinearHom α hO hP φ) θ')
        (GradedModule.homWithZeroDifferential (dgPullbackObj_d α hO hP φ N) h)
        (DifferentialGradedModule.SemilinearHom.ext fun i V x =>
          congrArg (fun z => GradedModule.SemilinearHom.app z i V x) hh))

/-- **The pullback of every right graded `B`-module at once**, as the datum
`GradedModule.PullbackData`: the construction `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`, its
unit, and the universal property of the unit. -/
noncomputable def tensorPullbackData :
    GradedModule.PullbackData (structureSemilinearHom α hO hP φ) where
  obj N := tensorPullbackObj α hO hP φ N
  unit N := tensorPullbackUnit α hO hP φ N
  isPullback N := isPullback_tensorPullbackUnit α hO hP φ N

/-- The object of `tensorPullbackData` at `N` is `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`. -/
@[simp]
theorem tensorPullbackData_obj (N : GradedModule.{u, u, u} B) :
    (tensorPullbackData α hO hP φ).obj N = tensorPullbackObj α hO hP φ N :=
  rfl

/-- **The pullback functor `f^* : Mod(B) ⥤ Mod(A)` of sheaves of graded modules**, which sends
`N` to `f⁻¹N ⊗_{f⁻¹B, φ} A` and a homomorphism to the unique homomorphism of the pullbacks
compatible with the two units. -/
noncomputable def tensorPullbackFunctor :
    GradedModule.{u, u, u} B ⥤ GradedModule.{u, u, u} A :=
  (tensorPullbackData α hO hP φ).functor

/-- The pullback functor sends `N` to `f⁻¹N ⊗_{f⁻¹B, φ} A`. -/
@[simp]
theorem tensorPullbackFunctor_obj (N : GradedModule.{u, u, u} B) :
    (tensorPullbackFunctor α hO hP φ).obj N = tensorPullbackObj α hO hP φ N :=
  rfl

end Pullback

/-! ### The adjunction -/

section Adjunction

/-- **Tag 0FR8**: for a morphism of ringed sites `f`, a sheaf of graded `O_C`-algebras `B` on the
target, a sheaf of graded `O_D`-algebras `A` on the source and a homomorphism `φ : f⁻¹B ⟶ A` of
sheaves of graded algebras, the homomorphisms `f^*N ⟶ M` of right graded `A`-modules homogeneous
of degree `n`, for the pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` (`tensorPullbackObj`), are exactly
the homomorphisms `N ⟶ f_*M` of right graded `B`-modules homogeneous of degree `n`:

`Hom_{Mod^gr(B)}(N, f_*M) = Hom_{Mod^gr(A)}(f^*N, M)`.

Here `f_*M` is the direct image of `M`, degreewise, with `B` acting through `φ` read as a
homomorphism `B ⟶ f_*A` (`structureSemilinearHom`). -/
@[stacks 0FR8 "Hom_{Mod^gr(B)}(N, f_*M) = Hom_{Mod^gr(A)}(f^*N, M) in every homogeneous degree, \
for the explicit pullback f^*N = f^{-1}N ⊗_{f^{-1}B, φ} A"]
noncomputable def tensorPullbackHomOfDegreeEquiv {B : GradedAlgebra.{u, u} (toRingCat J Osharp)}
    {A : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (φ : GradedAlgebra.UnitalHom (gradedInverseImageAlgebra α hO hP B) A)
    (N : GradedModule.{u, u, u} B) (M : GradedModule.{u, u, u} A) (n : ℤ) :
    GradedHomOfDegree (tensorPullbackObj α hO hP φ N) M n ≃
      GradedHomOfDegree N (GradedModule.pushforwardObj (structureSemilinearHom α hO hP φ) M) n :=
  (tensorPullbackData α hO hP φ).homOfDegreeEquiv N M n

/-- **The pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A` is left adjoint to the direct image** on sheaves
of graded modules: the degree-zero case of Tag 0FR8, read as an adjunction `f^* ⊣ f_*`, so
natural in both `N` and `M`. -/
@[stacks 0FR8 "the adjunction f^* ⊣ f_*, for the explicit pullback \
f^*N = f^{-1}N ⊗_{f^{-1}B, φ} A"]
noncomputable def tensorPullbackPushforwardAdjunction
    {B : GradedAlgebra.{u, u} (toRingCat J Osharp)}
    {A : GradedAlgebra.{u, u} (toRingCat K Psharp)}
    (φ : GradedAlgebra.UnitalHom (gradedInverseImageAlgebra α hO hP B) A) :
    tensorPullbackFunctor α hO hP φ ⊣
      GradedModule.pushforwardFunctor (structureSemilinearHom α hO hP φ) :=
  (tensorPullbackData α hO hP φ).pullbackPushforwardAdjunction

end Adjunction

end SheafOfModules.GradedTensorPullback

end
