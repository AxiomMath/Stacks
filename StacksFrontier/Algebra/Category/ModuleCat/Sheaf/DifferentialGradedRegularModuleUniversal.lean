module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint

/-!
# The universal property of the regular differential graded module

A sheaf of differential graded algebras `D` acting on itself on the right is the right
differential graded `D`-module `SheafOfModules.DifferentialGradedModule.regularModule D`. This
file proves that it is free on one closed generator of degree zero: a homomorphism
`D ⟶ N` of right differential graded `D`-modules is the same thing as a global section of `N` of
degree zero killed by the differential, the homomorphism attached to such a section `x` being
left multiplication `a ↦ x · a`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.leftMulAdd`: left multiplication by a global
  degree-zero section, on sections of degree `n`.
* `SheafOfModules.DifferentialGradedModule.regularModuleHom`: the homomorphism out of the
  regular module attached to a closed global degree-zero section.
* `SheafOfModules.DifferentialGradedModule.regularModuleSection`: the closed global degree-zero
  section attached to a homomorphism out of the regular module, the image of the unit.
* `SheafOfModules.DifferentialGradedModule.regularModuleHomEquiv`: the bijection between
  homomorphisms `regularModule D ⟶ N` and closed global degree-zero sections of `N`.

## Main results

* `SheafOfModules.DifferentialGradedModule.leftMulAdd_d`: left multiplication by a closed global
  degree-zero section commutes with the differentials.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t a v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A morphism of cochain complexes commutes with transport along an equality of degrees. -/
theorem complexHom_f_castHom {K L : CochainComplex (SheafOfModules.{a} R) ℤ} (φ : K ⟶ L)
    {n n' : ℤ} (h : n = n') (U : Cᵒᵖ) (z : (K.X n).val.obj U) :
    (φ.f n').val.app U (castHom K.X h U z) = castHom L.X h U ((φ.f n).val.app U z) := by
  subst h; rfl

/-- The differential of a cochain complex commutes with transport along an equality of
degrees. -/
theorem castHom_complex_d (K : CochainComplex (SheafOfModules.{a} R) ℤ) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (K.X i).val.obj U) :
    (K.d j (j + 1)).val.app U (castHom K.X h U x) =
      castHom K.X (by rw [h]) U ((K.d i (i + 1)).val.app U x) := by
  subst h; rfl

namespace DifferentialGradedModule

variable {D : DifferentialGradedAlgebra.{t, a} R} (N : DifferentialGradedModule.{t, a, a} D)
  (x : (N.complex.X 0).sections)

/-- **Left multiplication by a global degree-zero section of `N`**, read on sections of degree
`n` of the algebra. -/
noncomputable def leftMulAdd (n : ℤ) (U : Cᵒᵖ) :
    (D.complex.X n).val.obj U →+ (N.complex.X n).val.obj U :=
  (castHom N.complex.X (zero_add n) U).comp ((N.mul 0 n).app U (x.eval U))

/-- Left multiplication by `x` on a section `b` of degree `n` is the product `x · b`, transported
along `0 + n = n`. -/
theorem leftMulAdd_apply (n : ℤ) (U : Cᵒᵖ) (b : (D.complex.X n).val.obj U) :
    leftMulAdd N x n U b =
      castHom N.complex.X (zero_add n) U ((N.mul 0 n).app U (x.eval U) b) :=
  rfl

/-- Left multiplication by a global degree-zero section is linear over the structure sheaf. -/
theorem leftMulAdd_smul (n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (b : (D.complex.X n).val.obj U) :
    leftMulAdd N x n U (r • b) = r • leftMulAdd N x n U b := by
  rw [leftMulAdd_apply, (N.mul 0 n).map_smul_right U r (x.eval U) b, castHom_smul,
    leftMulAdd_apply]

/-- Left multiplication by a global degree-zero section commutes with restriction of sections. -/
theorem leftMulAdd_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (b : (D.complex.X n).val.obj U) :
    (N.complex.X n).val.map f (leftMulAdd N x n U b) =
      leftMulAdd N x n V ((D.complex.X n).val.map f b) := by
  show (N.complex.X n).val.map f
        (castHom N.complex.X (zero_add n) U ((N.mul 0 n).app U (x.eval U) b)) =
      castHom N.complex.X (zero_add n) V
        ((N.mul 0 n).app V (x.eval V) ((D.complex.X n).val.map f b))
  rw [castHom_naturality, (N.mul 0 n).naturality f (x.eval U) b,
    PresheafOfModules.sections_property x f]

/-- Left multiplication by a global degree-zero section, as a morphism of presheaves of
modules. -/
noncomputable def leftMulPres (n : ℤ) : (D.complex.X n).val ⟶ (N.complex.X n).val where
  app U := ModuleCat.ofHom
    { toFun b := leftMulAdd N x n U b
      map_add' b b' := map_add (leftMulAdd N x n U) b b'
      map_smul' r b := leftMulAdd_smul N x n U r b }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun b =>
    (leftMulAdd_naturality N x n f b).symm)

/-- On sections over `U`, `leftMulPres N x n` is `leftMulAdd N x n U`. -/
@[simp]
theorem leftMulPres_app (n : ℤ) (U : Cᵒᵖ) (b : (D.complex.X n).val.obj U) :
    (leftMulPres N x n).app U b = leftMulAdd N x n U b :=
  rfl

variable (hx : ∀ U : Cᵒᵖ, (N.complex.d 0 (0 + 1)).val.app U (x.eval U) = 0)

include hx in
/-- **Left multiplication by a closed global degree-zero section commutes with the
differentials.** -/
theorem leftMulAdd_d (n : ℤ) (U : Cᵒᵖ) (b : (D.complex.X n).val.obj U) :
    (N.complex.d n (n + 1)).val.app U (leftMulAdd N x n U b) =
      leftMulAdd N x (n + 1) U ((D.complex.d n (n + 1)).val.app U b) := by
  have hl := N.leibniz 0 n U (x.eval U) b
  rw [← castHom_apply, ← castHom_apply] at hl
  rw [hx U, map_zero ((N.mul (0 + 1) n).app U), AddMonoidHom.zero_apply,
    map_zero (castHom N.complex.X (add_right_comm (0 : ℤ) 1 n) U),
    Int.negOnePow_zero, Units.val_one, one_zsmul] at hl
  show (N.complex.d n (n + 1)).val.app U
        (castHom N.complex.X (zero_add n) U ((N.mul 0 n).app U (x.eval U) b)) =
      castHom N.complex.X (zero_add (n + 1)) U
        ((N.mul 0 (n + 1)).app U (x.eval U) ((D.complex.d n (n + 1)).val.app U b))
  rw [castHom_complex_d, hl.trans (zero_add _), castHom_castHom]

include hx in
/-- Left multiplication by a closed global degree-zero section, as a morphism of cochain
complexes. -/
noncomputable def leftMulComplexHom : (regularModule D).complex ⟶ N.complex where
  f n := ⟨leftMulPres N x n⟩
  comm' n j hnj := by
    subst hnj
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
    exact leftMulAdd_d N x hx n U b

/-- In degree `n`, on sections over `U`, `leftMulComplexHom N x hx` is `leftMulAdd N x n U`. -/
@[simp]
theorem leftMulComplexHom_f (n : ℤ) (U : Cᵒᵖ) (b : (D.complex.X n).val.obj U) :
    ((leftMulComplexHom N x hx).f n).val.app U b = leftMulAdd N x n U b :=
  rfl

include hx in
/-- **The homomorphism out of the regular module attached to a closed global degree-zero
section**: left multiplication by that section. -/
noncomputable def regularModuleHom : regularModule D ⟶ N where
  toHomologicalComplex := leftMulComplexHom N x hx
  map_mul n i U b c := by
    change castHom N.complex.X (zero_add (n + i)) U
          ((N.mul 0 (n + i)).app U (x.eval U) ((D.mul n i).app U b c)) =
        (N.mul n i).app U
          (castHom N.complex.X (zero_add n) U ((N.mul 0 n).app U (x.eval U) b)) c
    refine Eq.trans ?_
      (mul_castHom_left N (zero_add n) U ((N.mul 0 n).app U (x.eval U) b) c).symm
    exact eq_of_heq ((heq_castHom N.complex.X (zero_add (n + i)) U _).trans
      ((N.mul_assoc 0 n i U (x.eval U) b c).symm.trans
        (heq_castHom N.complex.X (congrArg (· + i) (zero_add n)) U _).symm))

/-- In degree `n`, on sections over `U`, `regularModuleHom N x hx` is `leftMulAdd N x n U`. -/
@[simp]
theorem regularModuleHom_f (n : ℤ) (U : Cᵒᵖ) (b : (D.complex.X n).val.obj U) :
    ((regularModuleHom N x hx).toHomologicalComplex.f n).val.app U b = leftMulAdd N x n U b :=
  rfl

/-- **The closed global degree-zero section attached to a homomorphism out of the regular
module**: the image of the unit of the algebra. -/
noncomputable def regularModuleSection (φ : regularModule D ⟶ N) : (N.complex.X 0).sections :=
  PresheafOfModules.sectionsMap (φ.toHomologicalComplex.f 0).val D.one

/-- Over `U`, the section `regularModuleSection N φ` is the image under `φ` of the unit of the
algebra over `U`. -/
theorem regularModuleSection_eval (φ : regularModule D ⟶ N) (U : Cᵒᵖ) :
    (regularModuleSection N φ).eval U =
      (φ.toHomologicalComplex.f 0).val.app U (D.one.eval U) :=
  rfl

/-- The section `regularModuleSection N φ` is killed by the differential of `N`. -/
theorem regularModuleSection_closed (φ : regularModule D ⟶ N) (U : Cᵒᵖ) :
    (N.complex.d 0 (0 + 1)).val.app U ((regularModuleSection N φ).eval U) = 0 := by
  have h0 : ((regularModule D).complex.d 0 (0 + 1)).val.app U (D.one.eval U) = 0 :=
    D.one_closed U
  have hc := congrArg (fun θ : (regularModule D).complex.X 0 ⟶ N.complex.X (0 + 1) =>
      θ.val.app U (D.one.eval U)) (φ.toHomologicalComplex.comm' 0 (0 + 1) rfl)
  refine hc.trans ?_
  show (φ.toHomologicalComplex.f (0 + 1)).val.app U
      (((regularModule D).complex.d 0 (0 + 1)).val.app U (D.one.eval U)) = 0
  rw [h0, map_zero]

/-- **The regular module is free on one closed generator of degree zero.** -/
noncomputable def regularModuleHomEquiv :
    (regularModule D ⟶ N) ≃ { x : (N.complex.X 0).sections //
      ∀ U : Cᵒᵖ, (N.complex.d 0 (0 + 1)).val.app U (x.eval U) = 0 } where
  toFun φ := ⟨regularModuleSection N φ, regularModuleSection_closed N φ⟩
  invFun x := regularModuleHom N x.1 x.2
  left_inv φ := by
    refine DifferentialGradedModule.Hom.ext fun n => ?_
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
    change castHom N.complex.X (zero_add n) U
        ((N.mul 0 n).app U ((φ.toHomologicalComplex.f 0).val.app U (D.one.eval U)) b) =
      (φ.toHomologicalComplex.f n).val.app U b
    rw [← φ.map_mul 0 n U (D.one.eval U) b,
      ← complexHom_f_castHom φ.toHomologicalComplex (zero_add n) U]
    exact congrArg (fun z => (φ.toHomologicalComplex.f n).val.app U z)
      (eq_of_heq ((heq_castHom (regularModule D).complex.X (zero_add n) U _).trans
        (D.one_mul n U b)))
  right_inv x := by
    refine Subtype.ext (PresheafOfModules.sections_ext _ _ fun U => ?_)
    exact eq_of_heq ((heq_castHom N.complex.X (zero_add 0) U _).trans
      (N.mul_one 0 U (x.1.eval U)))

/-- Over `U`, the section attached to `φ` by `regularModuleHomEquiv N` is the image under `φ` of
the unit of the algebra over `U`. -/
@[simp]
theorem regularModuleHomEquiv_apply_eval (φ : regularModule D ⟶ N) (U : Cᵒᵖ) :
    ((regularModuleHomEquiv N φ).1).eval U =
      (φ.toHomologicalComplex.f 0).val.app U (D.one.eval U) :=
  rfl

end DifferentialGradedModule

end SheafOfModules

end
