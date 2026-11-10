module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHomSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorGradedShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleStructures
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring local homomorphisms, and the tensor product of two bimodules

Let `M₁` and `M₂` be right differential graded `𝒜`-modules, let `𝒩` be a differential graded
`(𝒜, ℬ)`-bimodule and let `T₁ = M₁ ⊗_𝒜 𝒩` and `T₂ = M₂ ⊗_𝒜 𝒩` be tensor products. A degree-`k`
local homomorphism `f : M₁|_U ⟶ M₂|_U` induces the degree-`k` local homomorphism
`f ⊗ 1 : T₁|_U ⟶ T₂|_U`, `x ⊗ y ↦ f(x) ⊗ y`. This transport is additive, compatible with
restriction, composition, identities and the differential of the internal hom.

Transporting left multiplication by the sections of a third algebra `𝒜''` acting on `M` on the
left, commuting with the right action, gives the left action `a (x ⊗ y) = (a x) ⊗ y` on
`M ⊗_𝒜 𝒩`. In particular the tensor product `𝒩 ⊗_{𝒜'} 𝒩'` of a differential graded
`(𝒜, 𝒜')`-bimodule with a differential graded `(𝒜', 𝒜'')`-bimodule is a differential graded
`(𝒜, 𝒜'')`-bimodule.

## Main definitions

* `SheafOfModules.IsTensorProduct.transport`: the local homomorphism `f ⊗ 1`.
* `SheafOfModules.DifferentialGradedBimodule.LeftStructure.leftMulHom`: left multiplication by
  a homogeneous local section, as a local homomorphism.
* `SheafOfModules.IsTensorProduct.leftStructure`: the left action on a tensor product.
* `SheafOfModules.DifferentialGradedBimodule.tensorBimodule`: the bimodule `𝒩 ⊗_{𝒜'} 𝒩'`.

## Main results

* `SheafOfModules.IsTensorProduct.transport_tmul`: `(f ⊗ 1)(x ⊗ y) = f(x) ⊗ y`.
* `SheafOfModules.IsTensorProduct.transport_comp`, `transport_id`, `transport_add`,
  `transport_restrict`, `transport_diffAt`: the transport is functorial, additive, compatible with
  restriction and commutes with the differential of the internal hom.
* `SheafOfModules.IsTensorProduct.leftStructure_leftMul_tmul`: `a (x ⊗ y) = (a x) ⊗ y`.
* `SheafOfModules.DifferentialGradedBimodule.tensorBimodule_toRightModule`: the right module
  underlying `𝒩 ⊗_{𝒜'} 𝒩'` is the tensor product of `𝒩` with `𝒩'`.

## References

* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a w w' w'' z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The values of a local homomorphism in two spellings of its target degree are heterogeneously
equal. -/
theorem LocalHom.app_heq {A : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, s} A}
    {n : ℤ} {U : C} (f : LocalHom K L n U) {i j j' : ℤ} (hij : i + n = j) (hij' : i + n = j')
    (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    HEq (f.app i j hij V x) (f.app i j' hij' V x) := by
  obtain rfl : j = j' := hij.symm.trans hij'
  rfl

/-- The differential of a complex of sheaves of modules in two spellings of its target degree
gives heterogeneously equal values. -/
theorem d_app_heq (X : CochainComplex (SheafOfModules.{s} R) ℤ) {i j j' : ℤ} (h : j = j')
    (U : Cᵒᵖ) (x : (X.X i).val.obj U) :
    HEq ((X.d i j).val.app U x) ((X.d i j').val.app U x) := by
  subst h; rfl

namespace IsTensorProduct

variable {A B : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A B}
  {M₁ : DifferentialGradedModule.{t, a, w} A} {M₂ : DifferentialGradedModule.{t, a, w'} A}
  {M₃ : DifferentialGradedModule.{t, a, w''} A}
  {T₁ T₂ T₃ : DifferentialGradedModule.{t, a, s} B}

/-- Transports of tensors `x ⊗ y` and `x' ⊗ y` with heterogeneously equal first factors agree. -/
private theorem castHom_tmul_eq_castHom (h : IsTensorProduct M₂ N T₂) {i i' kk : ℤ}
    (hi : i = i') (j : ℤ) (hk : i + j = kk) (hk' : i' + j = kk) (U : Cᵒᵖ)
    {x : (M₂.complex.X i).val.obj U} {x' : (M₂.complex.X i').val.obj U} (hx : HEq x x')
    (y : (N.complex.X j).val.obj U) :
    castHom T₂.complex.X hk U (h.tmul i j U x y) =
      castHom T₂.complex.X hk' U (h.tmul i' j U x' y) :=
  castHom_heq T₂.complex.X _ _ _ (h.tmul_heq_left hi j U hx y)

/-- The balanced bilinear family `(x, y) ↦ f(x) ⊗ y` of degree `k` attached to a degree-`k`
local homomorphism `f : M₁|_U ⟶ M₂|_U` and a tensor product `T₂ = M₂ ⊗_𝒜 𝒩`. -/
def transportBilinear (h₂ : IsTensorProduct M₂ N T₂) {k : ℤ} {U : C} (f : LocalHom M₁ M₂ k U) :
    LocalBalancedBilinear M₁ N T₂ k U where
  app i j kk hijk V :=
    castHom₂ (M₁.complex.X i) (N.complex.X j) T₂.complex.X (show i + k + j = kk by omega)
      (Opposite.op V.left) ((h₂.tmul (i + k) j (Opposite.op V.left)).comp (f.app i (i + k) rfl V))
  map_smul_left i j kk hijk V r x y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply, f.map_smul]
    rw [h₂.tmul_smul_left, castHom_smul]
  map_smul_right i j kk hijk V r x y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [h₂.tmul_smul_right, castHom_smul]
  naturality i j kk hijk {V W} q x y := by
    have e1 := castHom₂_apply (M₁.complex.X i) (N.complex.X j) T₂.complex.X
      (show i + k + j = kk by omega) (Opposite.op V.left)
      ((h₂.tmul (i + k) j (Opposite.op V.left)).comp (f.app i (i + k) rfl V)) x y
    have e2 := castHom₂_apply (M₁.complex.X i) (N.complex.X j) T₂.complex.X
      (show i + k + j = kk by omega) (Opposite.op W.left)
      ((h₂.tmul (i + k) j (Opposite.op W.left)).comp (f.app i (i + k) rfl W))
      ((M₁.complex.X i).val.map q.left.op x) ((N.complex.X j).val.map q.left.op y)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at e1 e2
    rw [e1, castHom_naturality, h₂.tmul_naturality, f.naturality]
    exact e2.symm
  balanced i p j kk hijk V x a y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    refine castHom_heq T₂.complex.X _ _ _ (HEq.trans ?_
      (h₂.tmul_balanced (i + k) p j (Opposite.op V.left) (f.app i (i + k) rfl V x) a y))
    refine h₂.tmul_heq_left (show i + p + k = i + k + p by omega) j (Opposite.op V.left) ?_ y
    exact (f.app_heq rfl (by omega) V _).trans (heq_of_eq (f.isLinear i (i + k) rfl p V x a))
  map_rightMul i j p kk hijk V x y b := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [mul_app_castHom]
    exact castHom_heq T₂.complex.X _ _ _
      (h₂.tmul_rightMul (i + k) j p (Opposite.op V.left) _ y b).symm

/-- The bilinear map `(x, y) ↦ f x ⊗ y` sends `x` and `y` to the tensor product of `f x` with `y`,
cast to degree `kk`. -/
@[simp]
theorem transportBilinear_app (h₂ : IsTensorProduct M₂ N T₂) {k : ℤ} {U : C}
    (f : LocalHom M₁ M₂ k U) (i j kk : ℤ) (hijk : i + j + k = kk) (V : Over U)
    (x : (M₁.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (h₂.transportBilinear f).app i j kk hijk V x y =
      castHom T₂.complex.X (show i + k + j = kk by omega) (Opposite.op V.left)
        (h₂.tmul (i + k) j (Opposite.op V.left) (f.app i (i + k) rfl V x) y) :=
  castHom₂_apply (M₁.complex.X i) (N.complex.X j) T₂.complex.X _ (Opposite.op V.left) _ x y

/-- **The tensor product `f ⊗ 1 : T₁|_U ⟶ T₂|_U` of a degree-`k` local homomorphism
`f : M₁|_U ⟶ M₂|_U` with the identity of `𝒩`**, for tensor products `T₁ = M₁ ⊗_𝒜 𝒩` and
`T₂ = M₂ ⊗_𝒜 𝒩`: the degree-`k` local homomorphism determined by `x ⊗ y ↦ f(x) ⊗ y`. -/
noncomputable def transport (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} (f : LocalHom M₁ M₂ k U) : LocalHom T₁ T₂ k U :=
  (h₁.universal T₂ k U).symm (h₂.transportBilinear f)

/-- Composing `f ⊗ 1` with the multiplication map returns the family `(x, y) ↦ f(x) ⊗ y`. -/
theorem universal_transport (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} (f : LocalHom M₁ M₂ k U) :
    h₁.universal T₂ k U (h₁.transport h₂ f) = h₂.transportBilinear f :=
  (h₁.universal T₂ k U).apply_symm_apply _

/-- **`(f ⊗ 1)(x ⊗ y) = f(x) ⊗ y`.** -/
theorem transport_tmul (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} (f : LocalHom M₁ M₂ k U) (i j kk : ℤ) (hijk : i + j + k = kk) (V : Over U)
    (x : (M₁.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (h₁.transport h₂ f).app (i + j) kk hijk V (h₁.tmul i j (Opposite.op V.left) x y) =
      castHom T₂.complex.X (show i + k + j = kk by omega) (Opposite.op V.left)
        (h₂.tmul (i + k) j (Opposite.op V.left) (f.app i (i + k) rfl V x) y) := by
  have h := congrArg (fun β => LocalBalancedBilinear.app β i j kk hijk V x y)
    (h₁.universal_transport h₂ f)
  simp only [h₁.universal_app, transportBilinear_app] at h
  exact h

/-- The tensor product `f ⊗ 1` is compatible with restriction along a morphism of the site. -/
theorem transport_restrict (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U U' : C} (q : U' ⟶ U) (f : LocalHom M₁ M₂ k U) :
    (h₁.transport h₂ f).restrict q = h₁.transport h₂ (f.restrict q) := by
  refine (h₁.universal T₂ k U').injective
    (LocalBalancedBilinear.ext fun i j kk hijk V x y => ?_)
  rw [h₁.universal_restrict T₂ k q (h₁.transport h₂ f) i j kk hijk V x y,
    h₁.universal_transport h₂ f, h₁.universal_transport h₂ (f.restrict q),
    transportBilinear_app, transportBilinear_app]
  rfl

/-- The tensor product `f ⊗ 1` is additive in `f`. -/
theorem transport_add (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} (f g : LocalHom M₁ M₂ k U) :
    h₁.transport h₂ (f + g) = h₁.transport h₂ f + h₁.transport h₂ g := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [LocalHom.add_app, transport_tmul, transport_tmul, transport_tmul, LocalHom.add_app,
    h₂.tmul_add_left, castHom_add]

/-- The tensor product `0 ⊗ 1` is zero. -/
theorem transport_zero (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} : h₁.transport h₂ (0 : LocalHom M₁ M₂ k U) = 0 := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [transport_tmul, LocalHom.zero_app', LocalHom.zero_app', h₂.tmul_zero_left, map_zero]

/-- The tensor product `1 ⊗ 1` of the identity is the identity. -/
theorem transport_id (h₁ : IsTensorProduct M₁ N T₁) {U : C} :
    h₁.transport h₁ (LocalHom.id M₁ U) = LocalHom.id T₁ U := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [transport_tmul, LocalHom.id_app, LocalHom.id_app, h₁.tmul_castHom_left, castHom_castHom]

/-- **The tensor product with the identity of `𝒩` is compatible with composition**:
`(g ∘ f) ⊗ 1 = (g ⊗ 1) ∘ (f ⊗ 1)`. -/
theorem transport_comp (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    (h₃ : IsTensorProduct M₃ N T₃) {k l kl : ℤ} {U : C} (f : LocalHom M₁ M₂ k U)
    (g : LocalHom M₂ M₃ l U) (h : k + l = kl) :
    h₁.transport h₃ (f.comp g h) = (h₁.transport h₂ f).comp (h₂.transport h₃ g) h := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [transport_tmul, LocalHom.comp_app (h₁.transport h₂ f) (h₂.transport h₃ g) h
      (show i + j + k = i + j + k from rfl) (show i + j + k + l = kk by omega),
    transport_tmul,
    (h₂.transport h₃ g).toLocalGradedHom.app_castHom_source (show i + k + j = i + j + k by omega)
      (show i + k + j + l = kk by omega),
    transport_tmul]
  refine h₃.castHom_tmul_eq_castHom (by omega) j _ _ _ ?_ y
  rw [LocalHom.comp_app f g h rfl (show i + k + l = i + kl by omega)]
  exact g.app_heq _ _ V _

/-- **The tensor product with the identity of `𝒩` commutes with the differential of the internal
hom**: `d(f ⊗ 1) = d(f) ⊗ 1`, by the Leibniz rule of the multiplication maps, the two terms
`± f(x) ⊗ d y` cancelling. -/
theorem transport_diffAt (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂)
    {k : ℤ} {U : C} (f : LocalHom M₁ M₂ k U) :
    (h₁.transport h₂ f).diffAt = h₁.transport h₂ f.diffAt := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [h₁.transport_tmul h₂ f.diffAt, LocalHom.diffAt_app, LocalHom.diffAt_app,
    h₁.transport_tmul h₂ f, h₁.tmul_d_castHom i j, map_add, map_zsmul,
    (h₁.transport h₂ f).toLocalGradedHom.app_castHom_source (add_right_comm i 1 j)
      (show i + 1 + j + k = kk by omega),
    (h₁.transport h₂ f).toLocalGradedHom.app_castHom_source (add_assoc i j 1).symm
      (show i + (j + 1) + k = kk by omega),
    h₁.transport_tmul h₂ f, h₁.transport_tmul h₂ f,
    d_castHom_app T₂.complex (show i + k + j = i + j + k by omega)
      (show i + k + j + 1 = kk by omega),
    h₂.tmul_d_castHom (i + k) j, h₂.tmul_sub_left]
  simp only [map_add, map_sub, map_zsmul, AddMonoidHom.zsmul_apply, castHom_castHom]
  have hA := h₂.castHom_tmul_eq_castHom (by omega) j (show i + (k + 1) + j = kk by omega)
    (show i + k + 1 + j = kk by omega) (Opposite.op V.left)
    (d_app_heq M₂.complex (by omega) _ (f.app i (i + k) rfl V x)) y
  have hC := h₂.castHom_tmul_eq_castHom (by omega) j (show i + (k + 1) + j = kk by omega)
    (show i + 1 + k + j = kk by omega) (Opposite.op V.left)
    (f.app_heq (j := i + (k + 1)) (by omega) (by omega) V
      ((M₁.complex.d i (i + 1)).val.app (Opposite.op V.left) x)) y
  rw [hA, hC, Int.negOnePow_add, Units.val_mul, mul_smul, smul_add,
    smul_comm ((k.negOnePow : ℤˣ) : ℤ) ((i.negOnePow : ℤˣ) : ℤ)]
  abel

/-- The tensor product `f ⊗ 1` is linear in `f` over the sheaf of rings, when its rings of
sections are commutative. -/
theorem transport_smul [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
    (h₁ : IsTensorProduct M₁ N T₁) (h₂ : IsTensorProduct M₂ N T₂) {k : ℤ} {U : C}
    (r : R.obj.obj (Opposite.op U)) (f : LocalHom M₁ M₂ k U) :
    h₁.transport h₂ (r • f) = r • h₁.transport h₂ f := by
  refine h₁.localHom_ext fun i j kk hijk V x y => ?_
  rw [LocalHom.smul_app, transport_tmul, transport_tmul, LocalHom.smul_app, h₂.tmul_smul_left,
    castHom_smul]

end IsTensorProduct

/-! ### Left multiplication as a local homomorphism -/

/-- The restriction of a local section over `U` along a morphism `U' ⟶ U` of the site. -/
noncomputable def restrictAlong (F : SheafOfModules.{s} R) {U U' : C} (g : U' ⟶ U)
    (a : F.val.obj (Opposite.op U)) : F.val.obj (Opposite.op U') :=
  F.val.map g.op a

/-- Restriction of local sections is additive. -/
theorem restrictAlong_add (F : SheafOfModules.{s} R) {U U' : C} (g : U' ⟶ U)
    (a a' : F.val.obj (Opposite.op U)) :
    restrictAlong F g (a + a') = restrictAlong F g a + restrictAlong F g a' :=
  map_add _ _ _

/-- Restriction of local sections is semilinear along the restriction of the ring of sections. -/
theorem restrictAlong_smul (F : SheafOfModules.{s} R) {U U' : C} (g : U' ⟶ U)
    (r : R.obj.obj (Opposite.op U)) (a : F.val.obj (Opposite.op U)) :
    restrictAlong F g (r • a) = R.obj.map g.op r • restrictAlong F g a :=
  PresheafOfModules.map_smul _ _ _ _

/-- Restricting along `g` and then along `g'` is restricting along `g' ≫ g`. -/
theorem restrictAlong_comp (F : SheafOfModules.{s} R) {U U' U'' : C} (g : U' ⟶ U)
    (g' : U'' ⟶ U') (a : F.val.obj (Opposite.op U)) :
    restrictAlong F g' (restrictAlong F g a) = restrictAlong F (g' ≫ g) a :=
  (PresheafOfModules.map_comp_apply F.val g.op g'.op a).symm

/-- Restricting a local section from `U` to `V` and then to `W` along a morphism of the slice
site over `U` is restricting it from `U` to `W`. -/
theorem map_restrictAlong_over (F : SheafOfModules.{s} R) {U : C} {V W : Over U} (q : W ⟶ V)
    (a : F.val.obj (Opposite.op U)) :
    F.val.map q.left.op (restrictAlong F V.hom a) = restrictAlong F W.hom a := by
  rw [← Over.w q]
  exact restrictAlong_comp F V.hom q.left a

/-- Restriction of local sections commutes with a morphism of sheaves of modules. -/
theorem restrictAlong_homSections {F G : SheafOfModules.{s} R} (φ : F ⟶ G) {U U' : C}
    (g : U' ⟶ U) (a : F.val.obj (Opposite.op U)) :
    restrictAlong G g (φ.val.app (Opposite.op U) a) =
      φ.val.app (Opposite.op U') (restrictAlong F g a) :=
  homSections_naturality φ g.op a

/-- Restricting the value over `U` of a global section gives its value over `U'`. -/
theorem restrictAlong_sections (F : SheafOfModules.{s} R) {U U' : C} (g : U' ⟶ U)
    (a : F.sections) :
    restrictAlong F g (a.eval (Opposite.op U)) = a.eval (Opposite.op U') :=
  PresheafOfModules.sections_property _ _

/-- Restriction along the identity is the identity. -/
theorem restrictAlong_id (F : SheafOfModules.{s} R) {U : C} (a : F.val.obj (Opposite.op U)) :
    restrictAlong F (𝟙 U) a = a := by
  rw [restrictAlong, op_id, PresheafOfModules.map_id]
  rfl

namespace DifferentialGradedBimodule.LeftStructure

variable {A A' : DifferentialGradedAlgebra.{t, a} R} {M : DifferentialGradedModule.{t, a, w} A'}
  (S : LeftStructure A M)

/-- **Left multiplication `x ↦ a x` by a homogeneous section `a` of degree `p` of `𝒜` over `U`**,
as a degree-`p` local homomorphism `M|_U ⟶ M|_U` of right differential graded `𝒜'`-modules: it
is `𝒜'`-linear because the two actions commute. -/
noncomputable def leftMulHom {p : ℤ} {U : C} (a : (A.complex.X p).val.obj (Opposite.op U)) :
    LocalHom M M p U where
  app i j hij V := (castHom M.complex.X (show p + i = j by omega) (Opposite.op V.left)).comp
    ((S.leftMul p i).app (Opposite.op V.left) (restrictAlong (A.complex.X p) V.hom a))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [(S.leftMul p i).map_smul_right, castHom_smul]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [castHom_naturality, (S.leftMul p i).naturality, map_restrictAlong_over]
    rfl
  isLinear i j hij b V x c := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [mul_app_castHom]
    exact castHom_heq M.complex.X _ _ _ (S.left_right_assoc p i b (Opposite.op V.left) _ x c).symm

/-- Left multiplication by `a` sends `x` to the product of the restriction of `a` with `x`, cast
to degree `j`. -/
theorem leftMulHom_app {p : ℤ} {U : C} (a : (A.complex.X p).val.obj (Opposite.op U)) (i j : ℤ)
    (hij : i + p = j) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (S.leftMulHom a).app i j hij V x =
      castHom M.complex.X (show p + i = j by omega) (Opposite.op V.left)
        ((S.leftMul p i).app (Opposite.op V.left) (restrictAlong (A.complex.X p) V.hom a) x) :=
  rfl

/-- Left multiplication is additive in the multiplier. -/
theorem leftMulHom_add {p : ℤ} {U : C} (a a' : (A.complex.X p).val.obj (Opposite.op U)) :
    S.leftMulHom (a + a') = S.leftMulHom a + S.leftMulHom a' :=
  LocalHom.ext fun i j hij V x => by
    rw [LocalHom.add_app, leftMulHom_app, leftMulHom_app, leftMulHom_app, restrictAlong_add,
      map_add, AddMonoidHom.add_apply, map_add]

/-- Left multiplication is linear in the multiplier over the sheaf of rings. -/
theorem leftMulHom_smul [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] {p : ℤ} {U : C}
    (r : R.obj.obj (Opposite.op U)) (a : (A.complex.X p).val.obj (Opposite.op U)) :
    S.leftMulHom (r • a) = r • S.leftMulHom a :=
  LocalHom.ext fun i j hij V x => by
    rw [LocalHom.smul_app, leftMulHom_app, leftMulHom_app, restrictAlong_smul,
      (S.leftMul p i).map_smul_left, castHom_smul]

/-- Left multiplication is compatible with restriction along a morphism of the site. -/
theorem leftMulHom_restrict {p : ℤ} {U U' : C} (q : U' ⟶ U)
    (a : (A.complex.X p).val.obj (Opposite.op U)) :
    (S.leftMulHom a).restrict q = S.leftMulHom (restrictAlong (A.complex.X p) q a) :=
  LocalHom.ext fun i j hij V x => by
    change (S.leftMulHom a).app i j hij (Over.mk (V.hom ≫ q)) x = _
    rw [leftMulHom_app, leftMulHom_app, restrictAlong_comp]
    rfl

/-- Left multiplication by a product is the composite of the left multiplications:
`(a a') x = a (a' x)`. -/
theorem leftMulHom_comp {i j : ℤ} {U : C} (a : (A.complex.X i).val.obj (Opposite.op U))
    (a' : (A.complex.X j).val.obj (Opposite.op U)) (h : j + i = i + j) :
    (S.leftMulHom a').comp (S.leftMulHom a) h =
      S.leftMulHom ((A.mul i j).app (Opposite.op U) a a') :=
  LocalHom.ext fun q kk hkk V x => by
    rw [LocalHom.comp_app _ _ h (show q + j = q + j from rfl) (show q + j + i = kk by omega),
      leftMulHom_app, leftMulHom_app, leftMulHom_app]
    have hmul : restrictAlong (A.complex.X (i + j)) V.hom ((A.mul i j).app (Opposite.op U) a a') =
        (A.mul i j).app (Opposite.op V.left) (restrictAlong (A.complex.X i) V.hom a)
          (restrictAlong (A.complex.X j) V.hom a') :=
      (A.mul i j).naturality V.hom.op a a'
    rw [hmul]
    refine castHom_heq M.complex.X _ _ _ (HEq.trans ?_
      (S.left_assoc i j q (Opposite.op V.left) _ _ x))
    have e : ∀ {m m' : ℤ} (hm : m = m') {y : (M.complex.X m).val.obj (Opposite.op V.left)}
        {y' : (M.complex.X m').val.obj (Opposite.op V.left)}, HEq y y' →
        HEq ((S.leftMul i m).app (Opposite.op V.left) (restrictAlong (A.complex.X i) V.hom a) y)
          ((S.leftMul i m').app (Opposite.op V.left)
            (restrictAlong (A.complex.X i) V.hom a) y') := by
      intro m m' hm y y' hy
      subst hm
      rw [eq_of_heq hy]
    exact e (by omega) (heq_castHom M.complex.X _ _ _)

/-- Left multiplication by the unit is the identity. -/
theorem leftMulHom_one {U : C} : S.leftMulHom (A.one.eval (Opposite.op U)) = LocalHom.id M U :=
  LocalHom.ext fun i j hij V x => by
    rw [leftMulHom_app, LocalHom.id_app, restrictAlong_sections]
    exact castHom_heq M.complex.X _ _ _ (S.one_left i (Opposite.op V.left) x)

/-- **The differential of left multiplication by `a` is left multiplication by `d a`**: this is
the Leibniz rule of the left action. -/
theorem leftMulHom_diffAt {p : ℤ} {U : C} (a : (A.complex.X p).val.obj (Opposite.op U)) :
    (S.leftMulHom a).diffAt =
      S.leftMulHom ((A.complex.d p (p + 1)).val.app (Opposite.op U) a) :=
  LocalHom.ext fun i j hij V x => by
    rw [LocalHom.diffAt_app, leftMulHom_app, leftMulHom_app, leftMulHom_app,
      d_castHom_app M.complex (show p + i = i + p by omega) (show p + i + 1 = j by omega),
      S.leibniz_left p i, ← castHom_apply, ← castHom_apply, map_add, map_zsmul, castHom_castHom,
      castHom_castHom, restrictAlong_homSections]
    abel

end DifferentialGradedBimodule.LeftStructure

/-! ### The left action on a tensor product -/

namespace IsTensorProduct

open DifferentialGradedBimodule

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  {A A' A'' : DifferentialGradedAlgebra.{t, a} R} {M : DifferentialGradedModule.{t, a, w} A'}
  {N : DifferentialGradedBimodule.{t, a, z} A' A''} {T : DifferentialGradedModule.{t, a, s} A''}
  (hT : IsTensorProduct M N T) (S : LeftStructure A M)

/-- The left action `a (x ⊗ y) = (a x) ⊗ y` of a homogeneous section `a` of `𝒜` on the tensor
product `T = M ⊗_{𝒜'} 𝒩`, on sections over `U`: the transport through `- ⊗_{𝒜'} 𝒩` of left
multiplication by `a` on `M`, evaluated over the terminal object of the slice site. -/
def leftActSections (p m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X p).val.obj U) :
    (T.complex.X m).val.obj U →+ (T.complex.X (p + m)).val.obj U :=
  (castHom T.complex.X (show m + p = p + m by omega) U).comp
    ((hT.transport hT (S.leftMulHom (U := U.unop) a)).app m (m + p) rfl (Over.mk (𝟙 U.unop)))

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The left action of `a` on a section `x` of the tensor product is the transport of left
multiplication by `a`, applied to `x` over the terminal object of the slice site. -/
theorem leftActSections_apply (p m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X p).val.obj U)
    (x : (T.complex.X m).val.obj U) :
    hT.leftActSections S p m U a x =
      castHom T.complex.X (show m + p = p + m by omega) U
        ((hT.transport hT (S.leftMulHom (U := U.unop) a)).app m (m + p) rfl
          (Over.mk (𝟙 U.unop)) x) :=
  rfl

/-- The left action on the tensor product, as a bilinear map of sheaves of modules. -/
def leftAct (p m : ℤ) : BilinearMap (A.complex.X p) (T.complex.X m) (T.complex.X (p + m)) where
  app U := AddMonoidHom.mk' (hT.leftActSections S p m U) fun a a' => by
    ext x
    simp only [AddMonoidHom.add_apply, leftActSections_apply]
    rw [S.leftMulHom_add, transport_add, LocalHom.add_app, map_add]
  map_smul_left U r a x := by
    simp only [AddMonoidHom.mk'_apply, leftActSections_apply]
    rw [S.leftMulHom_smul, transport_smul, LocalHom.smul_app, castHom_smul]
    have hr : R.obj.map (Over.mk (𝟙 U.unop)).hom.op r = r := by
      change R.obj.map (𝟙 U.unop).op r = r
      rw [op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [hr]
  map_smul_right U r a x := by
    simp only [AddMonoidHom.mk'_apply, leftActSections_apply]
    rw [(hT.transport hT (S.leftMulHom (U := U.unop) a)).map_smul, castHom_smul]
  naturality {U V} g a x := by
    simp only [AddMonoidHom.mk'_apply, leftActSections_apply]
    rw [castHom_naturality]
    refine congrArg (castHom T.complex.X _ V) ?_
    have hA := (hT.transport hT (S.leftMulHom (U := U.unop) a)).naturality m (m + p) rfl
      (Over.homMk g.unop (Category.comp_id g.unop) :
        Over.mk g.unop ⟶ Over.mk (𝟙 U.unop)) x
    refine hA.trans ?_
    refine (LocalGradedHom.app_mk_congr
      (hT.transport hT (S.leftMulHom (U := U.unop) a)).toLocalGradedHom m (m + p) rfl
      (Category.id_comp g.unop).symm _).trans ?_
    change ((hT.transport hT (S.leftMulHom (U := U.unop) a)).restrict g.unop).app m (m + p) rfl
      (Over.mk (𝟙 V.unop)) ((T.complex.X m).val.map g x) = _
    refine LocalHom.app_congr ?_ m (m + p) rfl (Over.mk (𝟙 V.unop)) _
    rw [transport_restrict, S.leftMulHom_restrict]
    rfl

/-- The left action on the tensor product, on sections over `U`, is `leftActSections`. -/
theorem leftAct_app (p m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X p).val.obj U)
    (x : (T.complex.X m).val.obj U) :
    (hT.leftAct S p m).app U a x =
      castHom T.complex.X (show m + p = p + m by omega) U
        ((hT.transport hT (S.leftMulHom (U := U.unop) a)).app m (m + p) rfl
          (Over.mk (𝟙 U.unop)) x) :=
  rfl

/-- **The left differential graded `𝒜`-module structure on a tensor product `M ⊗_{𝒜'} 𝒩`**
induced by one on `M` commuting with the right action of `𝒜'`: `a (x ⊗ y) = (a x) ⊗ y`. -/
def leftStructure : LeftStructure A T where
  leftMul := hT.leftAct S
  left_assoc i j n U a a' x := by
    rw [leftAct_app, leftAct_app, leftAct_app]
    refine (heq_castHom T.complex.X _ _ _).trans (HEq.trans ?_ (heq_castHom T.complex.X _ _ _).symm)
    have h1 := (hT.transport hT (S.leftMulHom (U := U.unop) a)).toLocalGradedHom.app_castHom_source
      (show n + j = j + n by omega) (show n + j + i = j + n + i by omega)
      (show j + n + i = j + n + i from rfl) (Over.mk (𝟙 U.unop))
      ((hT.transport hT (S.leftMulHom (U := U.unop) a')).app n (n + j) rfl (Over.mk (𝟙 U.unop)) x)
    have h2 := LocalHom.comp_app (hT.transport hT (S.leftMulHom (U := U.unop) a'))
      (hT.transport hT (S.leftMulHom (U := U.unop) a)) (show j + i = i + j by omega)
      (show n + j = n + j from rfl) (show n + j + i = j + n + i by omega) (Over.mk (𝟙 U.unop)) x
    have h3 : (hT.transport hT (S.leftMulHom (U := U.unop) a')).comp
        (hT.transport hT (S.leftMulHom (U := U.unop) a)) (show j + i = i + j by omega) =
        hT.transport hT (S.leftMulHom (U := U.unop) ((A.mul i j).app U a a')) := by
      rw [← transport_comp, S.leftMulHom_comp]
    exact (heq_of_eq (h1.trans (h2.symm.trans (LocalHom.app_congr h3 n (j + n + i) (by omega)
      (Over.mk (𝟙 U.unop)) x)))).trans
      (LocalHom.app_heq _ _ _ _ _)
  left_right_assoc i n j U a x b := by
    rw [leftAct_app, leftAct_app, mul_app_castHom]
    refine (heq_castHom T.complex.X _ _ _).trans (HEq.trans ?_ (heq_castHom T.complex.X _ _ _).symm)
    exact (heq_of_eq ((hT.transport hT (S.leftMulHom (U := U.unop) a)).isLinear n (n + i) rfl j
      (Over.mk (𝟙 U.unop)) x b)).symm.trans (LocalHom.app_heq _ _ _ _ _)
  one_left n U x := by
    rw [leftAct_app]
    refine (heq_castHom T.complex.X _ _ _).trans ?_
    have hid : hT.transport hT (S.leftMulHom (U := U.unop) (A.one.eval U)) =
        LocalHom.id T U.unop :=
      (congrArg (hT.transport hT) (S.leftMulHom_one (U := U.unop))).trans hT.transport_id
    have h := LocalHom.app_congr hid n (n + 0) rfl (Over.mk (𝟙 U.unop)) x
    rw [LocalHom.id_app] at h
    exact (heq_of_eq h).trans (heq_castHom T.complex.X _ _ _)
  leibniz_left n m U a x := by
    have h := LocalHom.app_congr (hT.transport_diffAt hT (S.leftMulHom (U := U.unop) a))
      m (m + (n + 1)) rfl (Over.mk (𝟙 U.unop)) x
    rw [LocalHom.diffAt_app, S.leftMulHom_diffAt] at h
    have hd : (T.complex.d (m + n) (m + (n + 1))).val.app U
          ((hT.transport hT (S.leftMulHom (U := U.unop) a)).app m (m + n) rfl
            (Over.mk (𝟙 U.unop)) x) =
        (hT.transport hT (S.leftMulHom (U := U.unop)
          ((A.complex.d n (n + 1)).val.app U a))).app m (m + (n + 1)) rfl
            (Over.mk (𝟙 U.unop)) x +
        ((n.negOnePow : ℤˣ) : ℤ) • (hT.transport hT (S.leftMulHom (U := U.unop) a)).app (m + 1)
          (m + (n + 1)) (by omega) (Over.mk (𝟙 U.unop)) ((T.complex.d m (m + 1)).val.app U x) :=
      eq_add_of_sub_eq h
    rw [leftAct_app, leftAct_app, leftAct_app, ← castHom_apply, ← castHom_apply,
      d_castHom_app T.complex (show m + n = n + m by omega) (show m + (n + 1) = n + m + 1 by omega),
      hd, map_add, map_zsmul]
    simp only [castHom_castHom]
    congr 2
    exact castHom_heq T.complex.X _ _ _ (LocalHom.app_heq _ _ _ _ _)

/-- On sections, the left action on the tensor product is the transport of left multiplication,
evaluated over the terminal object of the slice site. -/
theorem leftStructure_leftMul_eq (p m : ℤ) (U : C) (a : (A.complex.X p).val.obj (Opposite.op U))
    (x : (T.complex.X m).val.obj (Opposite.op U)) :
    ((hT.leftStructure S).leftMul p m).app (Opposite.op U) a x =
      castHom T.complex.X (show m + p = p + m by omega) (Opposite.op U)
        ((hT.transport hT (S.leftMulHom a)).app m (m + p) rfl (Over.mk (𝟙 U)) x) :=
  rfl

/-- **The left action on a tensor product on elementary tensors**: `a (x ⊗ y) = (a x) ⊗ y`. -/
theorem leftStructure_leftMul_tmul (p i j : ℤ) (U : Cᵒᵖ) (a : (A.complex.X p).val.obj U)
    (x : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    HEq (((hT.leftStructure S).leftMul p (i + j)).app U a (hT.tmul i j U x y))
      (hT.tmul (p + i) j U ((S.leftMul p i).app U a x) y) := by
  rw [leftStructure_leftMul_eq hT S p (i + j) U.unop a]
  refine (heq_castHom T.complex.X _ _ _).trans ?_
  refine (heq_of_eq (hT.transport_tmul hT (S.leftMulHom (U := U.unop) a) i j (i + j + p) rfl
    (Over.mk (𝟙 U.unop)) x y)).trans ?_
  refine (heq_castHom T.complex.X _ _ _).trans ?_
  refine hT.tmul_heq_left (by omega) j U ?_ y
  rw [S.leftMulHom_app]
  refine (heq_castHom M.complex.X _ _ _).trans ?_
  have hr : restrictAlong (A.complex.X p) (Over.mk (𝟙 U.unop)).hom a = a :=
    restrictAlong_id (A.complex.X p) (U := U.unop) a
  rw [hr]
  rfl

end IsTensorProduct

/-! ### The tensor product of two bimodules -/

namespace DifferentialGradedBimodule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' A'' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **The tensor product `𝒩 ⊗_{𝒜'} 𝒩'` of a differential graded `(𝒜, 𝒜')`-bimodule `𝒩` with a
differential graded `(𝒜', 𝒜'')`-bimodule `𝒩'`**, a differential graded `(𝒜, 𝒜'')`-bimodule: the
right differential graded `𝒜''`-module `𝒩 ⊗_{𝒜'} 𝒩'` with the left action
`a (x ⊗ y) = (a x) ⊗ y`. -/
@[sga "4 IV 12.12" "more general"]
def tensorBimodule (N : DifferentialGradedBimodule.{u, u, u} A A')
    (N' : DifferentialGradedBimodule.{u, u, u} A' A'') :
    DifferentialGradedBimodule.{u, u, u} A A'' :=
  ofLeftStructure
    (((DifferentialGradedModule.tensorData N').isTensorProduct N.toRightModule).leftStructure
      N.leftStructure)

/-- The right differential graded `𝒜''`-module underlying `𝒩 ⊗_{𝒜'} 𝒩'` is the tensor product of
`𝒩`, read as a right differential graded `𝒜'`-module, with `𝒩'`. -/
theorem tensorBimodule_toRightModule (N : DifferentialGradedBimodule.{u, u, u} A A')
    (N' : DifferentialGradedBimodule.{u, u, u} A' A'') :
    (tensorBimodule N N').toRightModule =
      (DifferentialGradedModule.tensorData N').functor.obj N.toRightModule :=
  rfl

end DifferentialGradedBimodule

end SheafOfModules

end
