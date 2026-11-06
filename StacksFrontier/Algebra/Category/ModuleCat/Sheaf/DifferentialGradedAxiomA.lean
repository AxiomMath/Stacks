module

public import Mathlib.CategoryTheory.Center.Linear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.CategoryTheory.DifferentialGraded.Biproduct
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Axiom (A) for sheaf differential graded modules

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The right
differential graded `A`-modules are the objects of a differential graded category over the ring
of global sections of the structure sheaf of `X`: a homogeneous morphism of degree `n` is a
cochain of the underlying complexes of sheaves of modules which commutes with the right action of
the homogeneous sections of `A`, the differential is the graded commutator with the differentials
of the two modules, and composition is componentwise composition. This file constructs that
differential graded category and proves axiom (A) for it: it has a zero object and binary
differential graded direct sums.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsActionLinear`: the predicate on a cochain of the
  underlying complexes saying that it commutes with the right action of `A`.
* `SheafOfModules.DifferentialGradedModule.HomogeneousMap`: the homogeneous right-linear maps of
  a fixed degree, i.e. the action-linear cochains.
* `SheafOfModules.DifferentialGradedModule.DGCategoryData`: a differential graded category over
  the global sections of the structure sheaf, together with the identification of its objects
  with right differential graded modules and of its homogeneous morphisms with the homogeneous
  right-linear maps, and the formulas for the differential, the composition and the identity.
* `SheafOfModules.DifferentialGradedModule.dgCategoryData`: the canonical such datum.

## Main results

* `SheafOfModules.DifferentialGradedModule.actionLinear_zero`,
  `actionLinear_add`, `actionLinear_neg`, `actionLinear_sub`,
  `actionLinear_comp`, `actionLinear_id`, `actionLinear_delta` and `actionLinear_ofHom`: the
  action-linear cochains contain the cochain of a morphism and the identity, and are stable
  under the additive operations, under composition and under the commutator with the
  differentials.
* `SheafOfModules.DifferentialGradedModule.existsDGCategoryData`: the canonical datum exists.
* `SheafOfModules.DifferentialGradedModule.hasZeroObject`: there is an object with a unique
  homogeneous morphism to and from every object in every degree.
* `SheafOfModules.DifferentialGradedModule.hasBinaryBiproducts`: any two objects admit a
  differential graded direct sum.

## Implementation notes

The objects of the differential graded category are the right differential graded modules, and
its homogeneous morphisms are exactly the action-linear cochains of their underlying complexes of
sheaves of modules; the differential is the usual commutator, Mathlib's
`CochainComplex.HomComplex.δ`. Accordingly the two main results assert axiom (A) in *that*
category, and not in the differential graded category of the underlying complexes nor in the
ordinary category of closed degree-zero maps.

The ground ring is the ring `limit X.O.obj` of global sections of the structure sheaf, and this is
why the statements are about a ringed site rather than about an arbitrary sheaf of rings on a
site: `DGCategory` requires a commutative ground ring, and it is the structure sheaf of a ringed
site, being `CommRingCat`-valued, that supplies the commutativity. An arbitrary
`Sheaf J RingCat` does not, and assuming a commutative ring of global sections separately would
change the statements. Linearity of the homogeneous morphisms over that ring comes from the
`CategoryTheory.Linear` structure on sheaves of modules induced by the ring morphism from global
sections into the centre of that category.

The ringed site itself is `AlgebraicGeometry.RingedSite`, with its sheaf of rings
`AlgebraicGeometry.RingedSite.ringSheaf`; it is referred to only by its fully qualified names.

Both direct sums are produced from `SheafOfModules.DifferentialGradedModule.hasProducts`, which
is the degreewise product and carries no hypothesis on the site: finite products, a zero object
and binary biproducts of right differential graded modules follow from it, and their structure
morphisms are closed of degree zero because they are morphisms of differential graded modules.
No sheafification hypothesis and no infinite direct sum is needed, so the two results hold with
the universe of the module sections left free.

## References

* [Stacks Project, Tag 0FS4](https://stacks.math.columbia.edu/tag/0FS4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

open CochainComplex.HomComplex

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A homogeneous cochain of right differential graded modules commutes with the action. -/
def IsActionLinear {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : Cochain M.complex N.complex n) : Prop :=
  ∀ (p q m : ℤ) (hpq : p + n = q) (U : X.Cᵒᵖ)
      (x : (M.complex.X p).val.obj U) (a : (A.complex.X m).val.obj U),
    HEq (((f.v (p + m) (q + m) (by omega)).val.app U) ((M.mul p m).app U x a))
      ((N.mul q m).app U (((f.v p q hpq).val.app U) x) a)

/-- Homogeneous right-linear maps of sheaf differential graded modules. -/
abbrev HomogeneousMap (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :=
  {f : Cochain M.complex N.complex n // IsActionLinear A f}

/-- A differential graded category realizing the homogeneous right-linear maps of sheaf
differential graded modules. The differential agrees with the Hom-complex commutator on
underlying cochains. -/
structure DGCategoryData where
  /-- The differential graded category over the global sections of the structure sheaf. -/
  category : DGCategory.{max u w, max u v (w + 1)}
    ((limit X.O.obj : CommRingCat.{u}))
  /-- Its objects are the right differential graded modules. -/
  objects : category.Obj = DifferentialGradedModule.{u, v, w} A
  /-- Its degree-`n` morphisms are the homogeneous right-linear maps of degree `n`. -/
  homs : ∀ (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ),
    category.Hom (objects.symm ▸ M) (objects.symm ▸ N) n = HomogeneousMap A M N n
  /-- The identification of degree-`n` morphisms with homogeneous right-linear maps is additive.
  Without this the identification is a bare equality of types, which does not relate the additive
  structure of the differential graded category's `Hom` group to that of the cochains, and no
  functor of differential graded categories out of or into this category can be shown additive.
  It is recorded on underlying cochains so that it does not depend on the additive structure of
  `SheafOfModules.DifferentialGradedModule.HomogeneousMap`. -/
  homs_add : ∀ (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ)
      (f g : category.Hom (objects.symm ▸ M) (objects.symm ▸ N) n),
    (homs M N n ▸ (f + g)).val = (homs M N n ▸ f).val + (homs M N n ▸ g).val
  /-- Its differential is the Hom-complex commutator. -/
  differential : ∀ (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ)
      (f : category.Hom (objects.symm ▸ M) (objects.symm ▸ N) n),
    HEq ((homs M N (n + 1) ▸ category.d f).val)
      (δ n (n + 1) ((homs M N n ▸ f).val))
  /-- Its composition is composition of cochains. -/
  composition : ∀ (M N P : DifferentialGradedModule.{u, v, w} A)
      (m n k : ℤ) (h : m + n = k)
      (g : category.Hom (objects.symm ▸ N) (objects.symm ▸ P) m)
      (f : category.Hom (objects.symm ▸ M) (objects.symm ▸ N) n),
    HEq ((homs M P k ▸ category.comp h g f).val)
      (Cochain.comp ((homs M N n ▸ f).val) ((homs N P m ▸ g).val)
        (by omega : n + m = k))
  /-- Its identities are the identity cochains. -/
  identity : ∀ (M : DifferentialGradedModule.{u, v, w} A),
    HEq ((homs M M 0 ▸ category.id (objects.symm ▸ M)).val)
      (Cochain.ofHom (𝟙 M.complex))

private noncomputable def globalSectionsMap (U : X.Cᵒᵖ) :
    (limit X.O.obj : CommRingCat.{u}) →+* (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U :=
  ((forget₂ CommRingCat RingCat).map (limit.π X.O.obj U)).hom

private lemma globalSectionsMap_natural {U V : X.Cᵒᵖ} (f : U ⟶ V) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom.comp
        (globalSectionsMap (X := X) U) =
      globalSectionsMap (X := X) V := by
  ext r
  exact congrArg (fun g : CommRingCat.of _ ⟶ _ => g.hom r) (limit.w X.O.obj f)

private noncomputable def globalScalarEndo (r : (limit X.O.obj : CommRingCat.{u})) :
    CatCenter (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  asHom.app M := ⟨{
    app U := by
      letI : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
        inferInstanceAs (CommRing (X.O.obj.obj U))
      exact ModuleCat.ofHom (globalSectionsMap (X := X) U r •
        LinearMap.id (M := M.val.obj U))
    naturality {U V} f := by
      ext x
      change globalSectionsMap (X := X) V r • (M.val.map f).hom x =
        (M.val.map f).hom (globalSectionsMap (X := X) U r • x)
      rw [(M.val.map f).hom.map_smul, ModuleCat.restrictScalars.smul_def]
      have hs := congrArg (fun g : (limit X.O.obj : CommRingCat.{u}) →+*
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V => g r)
        (globalSectionsMap_natural (X := X) f)
      have hs' : globalSectionsMap (X := X) V r =
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom
            (globalSectionsMap (X := X) U r) := by
        simpa only [RingHom.comp_apply] using hs.symm
      rw [hs']
      rfl }⟩
  asHom.naturality {M N} f := by
    change f ≫ _ = _ ≫ f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    exact ((f.val.app U).hom.map_smul _ x).symm

private lemma catCenter_ext_app
    {a b : CatCenter (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : ∀ (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ)
      (x : M.val.obj U),
      ConcreteCategory.hom ((a.app M).val.app U) x =
        ConcreteCategory.hom ((b.app M).val.app U) x) : a = b := by
  apply CatCenter.ext
  intro M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  exact h M U x

private noncomputable def globalSectionsCenter :
    (limit X.O.obj : CommRingCat.{u}) →+*
      CatCenter (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  toFun := globalScalarEndo
  map_one' := by
    apply catCenter_ext_app
    intro M U x
    change globalSectionsMap (X := X) U 1 • x = x
    simp only [map_one, one_smul]
  map_mul' r s := by
    apply catCenter_ext_app
    intro M U x
    change globalSectionsMap (X := X) U (r * s) • x =
      globalSectionsMap (X := X) U r • (globalSectionsMap (X := X) U s • x)
    rw [map_mul, mul_smul]
  map_zero' := by
    apply catCenter_ext_app
    intro M U x
    change globalSectionsMap (X := X) U 0 • x = 0
    rw [map_zero, zero_smul]
  map_add' r s := by
    apply catCenter_ext_app
    intro M U x
    change globalSectionsMap (X := X) U (r + s) • x =
      globalSectionsMap (X := X) U r • x + globalSectionsMap (X := X) U s • x
    rw [map_add, add_smul]

private noncomputable instance globalSectionsLinear :
    Linear (limit X.O.obj : CommRingCat.{u})
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Linear.ofRingMorphism globalSectionsCenter

/-- The zero cochain commutes with the action. -/
lemma actionLinear_zero (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    IsActionLinear A (0 : Cochain M.complex N.complex n) := by
  intro p q m hpq U x a
  show HEq (0 : (N.complex.X (q + m)).val.obj U)
    (((N.mul q m).app U) (0 : (N.complex.X q).val.obj U) a)
  simp

/-- The sum of two cochains commuting with the action commutes with the action. -/
lemma actionLinear_add {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f g : Cochain M.complex N.complex n)
    (hf : IsActionLinear A f) (hg : IsActionLinear A g) :
    IsActionLinear A (f + g) := by
  intro p q m hpq U x a
  apply heq_of_eq
  simp only [Cochain.add_v, SheafOfModules.add_val, PresheafOfModules.add_app,
    ModuleCat.hom_add, LinearMap.add_apply]
  rw [eq_of_heq (hf p q m hpq U x a), eq_of_heq (hg p q m hpq U x a)]
  simp only [map_add, AddMonoidHom.add_apply]

private lemma sheaf_hom_app_comp
    {S T V : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : S ⟶ T) (g : T ⟶ V) (U : X.Cᵒᵖ) (x : S.val.obj U) :
    ConcreteCategory.hom ((f ≫ g).val.app U) x =
      ConcreteCategory.hom (g.val.app U) (ConcreteCategory.hom (f.val.app U) x) := by
  simp [SheafOfModules.comp_val, PresheafOfModules.comp_app]

/-- A multiple of an action-linear cochain by a global section of the structure sheaf is
action-linear. -/
private lemma actionLinear_smul {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (r : (limit X.O.obj : CommRingCat.{u})) (f : Cochain M.complex N.complex n)
    (hf : IsActionLinear A f) : IsActionLinear A (r • f) := by
  intro p q m hpq U x a
  apply heq_of_eq
  show (f.v (p + m) (q + m) (by omega)).val.app U
      (globalSectionsMap (X := X) U r • (M.mul p m).app U x a) =
    (N.mul q m).app U ((f.v p q hpq).val.app U
      (globalSectionsMap (X := X) U r • x)) a
  rw [map_smul, map_smul, eq_of_heq (hf p q m hpq U x a),
    (N.mul q m).map_smul_left]

/-- An integer multiple of a morphism of sheaves of modules acts on local sections by the
integer multiple of its action. -/
lemma sheaf_hom_app_zsmul {S T : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (r : ℤ) (f : S ⟶ T) (U : X.Cᵒᵖ) (x : S.val.obj U) :
    ConcreteCategory.hom ((r • f).val.app U) x =
      r • ConcreteCategory.hom (f.val.app U) x := by
  let : (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hv : (r • f).val = r • f.val :=
    (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_zsmul
  rw [hv]
  have heval : (r • f.val).app U = r • f.val.app U := by
    show (PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj U).map
      (r • f.val) = _
    rw [Functor.map_zsmul]
    rfl
  rw [heval]
  simp

private lemma cochain_app_cast
    {F G : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {n : ℤ} (f : Cochain F G n) (U : X.Cᵒᵖ) {i i' j j' : ℤ}
    (hi : i' = i) (hj : j = j') (h : i + n = j) (h' : i' + n = j')
    (x : (F.X i').val.obj U) :
    (f.v i j h).val.app U (hi ▸ x) =
      gradedCast (fun q ↦ (G.X q).val.obj U) hj.symm
        ((f.v i' j' h').val.app U x) := by
  subst i
  subst j
  simp [gradedCast]

private lemma differential_app_cast
    {F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {i j j' : ℤ} (h : j = j') (U : X.Cᵒᵖ) (x : (F.X i).val.obj U) :
    gradedCast (fun q ↦ (F.X q).val.obj U) h
        (ConcreteCategory.hom ((F.d i j).val.app U) x) =
      ConcreteCategory.hom ((F.d i j').val.app U) x := by
  subst j'
  rfl

private lemma gradedCast_zsmul
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {i j : ℤ} (h : i = j) (U : X.Cᵒᵖ) (r : ℤ)
    (x : (F.X i).val.obj U) :
    gradedCast (fun q ↦ (F.X q).val.obj U) h (r • x) =
      r • gradedCast (fun q ↦ (F.X q).val.obj U) h x := by
  cases h
  rfl

private lemma gradedCast_eq_transport
    {ι : Type*} (B : ι → Type*) {i j : ι} (h h' : i = j)
    (x : B i) : gradedCast B h x = h' ▸ x := by
  cases h
  cases h'
  rfl

private lemma moduleMul_gradedCast_left
    {M : DifferentialGradedModule.{u, v, w} A}
    {i i' m : ℤ} (h : i = i') (U : X.Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) (a : (A.complex.X m).val.obj U) :
    gradedCast (fun q ↦ (M.complex.X q).val.obj U)
        (congrArg (fun q : ℤ ↦ q + m) h) ((M.mul i m).app U x a) =
      ((M.mul i' m).app U)
        (gradedCast (fun q ↦ (M.complex.X q).val.obj U) h x) a := by
  cases h
  rfl

/-- The commutator of an action-linear cochain with the differentials is action-linear. -/
lemma actionLinear_delta {M N : DifferentialGradedModule.{u, v, w} A}
    {n : ℤ} (f : Cochain M.complex N.complex n) (hf : IsActionLinear A f) :
    IsActionLinear A (δ n (n + 1) f) := by
  intro p q m hpq U x a
  subst q
  apply heq_of_eq
  rw [δ_v n (n + 1) rfl f (p + m) (p + (n + 1) + m) (by omega)
      (p + n + m) (p + m + 1) (by omega) (by omega),
    δ_v n (n + 1) rfl f p (p + (n + 1)) (by omega)
      (p + n) (p + 1) (by omega) (by omega)]
  simp only [SheafOfModules.add_val, SheafOfModules.comp_val, PresheafOfModules.add_app,
    PresheafOfModules.comp_app, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.coe_comp, Function.comp_apply, map_add, AddMonoidHom.add_apply]
  have hleft := sheaf_hom_app_zsmul (X := X) (r := (n + 1).negOnePow)
    (f := M.complex.d (p + m) (p + m + 1) ≫
      f.v (p + m + 1) (p + (n + 1) + m) (by omega)) U ((M.mul p m).app U x a)
  have hright := sheaf_hom_app_zsmul (X := X) (r := (n + 1).negOnePow)
    (f := M.complex.d p (p + 1) ≫ f.v (p + 1) (p + (n + 1)) (by omega)) U x
  simp only [Units.smul_def]
  rw [hleft, hright]
  simp only [sheaf_hom_app_comp (X := X)]
  have hfa :
      ConcreteCategory.hom ((f.v (p + m) (p + n + m) (by omega)).val.app U)
          (((M.mul p m).app U) x a) =
        ((N.mul (p + n) m).app U)
          (ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U) x) a :=
    eq_of_heq (hf p (p + n) m (by omega) U x a)
  have hf1 := eq_of_heq (hf (p + 1) (p + (n + 1)) m (by omega) U
    ((M.complex.d p (p + 1)).val.app U x) a)
  have hf2 := eq_of_heq (hf p (p + n) (m + 1) (by omega) U x
    ((A.complex.d m (m + 1)).val.app U a))
  have hN := N.leibniz (p + n) m U
    (ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U) x) a
  have hM := M.leibniz p m U x a
  have hidx : p + n + m + 1 = p + (n + 1) + m := by omega
  have hNcast := congrArg
    (gradedCast (fun q ↦ (N.complex.X q).val.obj U) hidx) hN
  rw [differential_app_cast (F := N.complex) hidx U _] at hNcast
  have hco1 := cochain_app_cast (f := f) U
    (i := p + m + 1) (i' := p + 1 + m)
    (j := p + (n + 1) + m) (j' := p + (n + 1) + m)
    (hi := add_right_comm p 1 m)
    (hj := rfl) (h := by omega) (h' := by omega)
    (((M.mul (p + 1) m).app U) ((M.complex.d p (p + 1)).val.app U x) a)
  have hco2 := cochain_app_cast (f := f) U
    (i := p + m + 1) (i' := p + (m + 1))
    (j := p + (n + 1) + m) (j' := p + n + (m + 1))
    (hi := (add_assoc p m 1).symm)
    (hj := by omega) (h := by omega) (h' := by omega)
    (((M.mul p (m + 1)).app U) x ((A.complex.d m (m + 1)).val.app U a))
  simp only [gradedCast] at hco1 hco2
  rw [hfa, hNcast, hM]
  simp only [map_add, map_zsmul]
  simp_all only [Int.negOnePow_add, Int.negOnePow_one, mul_neg, _root_.mul_one, Units.val_neg,
    neg_smul, comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, map_add, LinearMap.map_smul_of_tower, smul_add, Units.val_mul,
    gradedCast_add, gradedCast_trans, gradedCast_zsmul, id_eq, AddMonoidHom.neg_apply,
    AddMonoidHom.smul_apply]
  have hco1match :
      (ConcreteCategory.hom ((f.v (p + m + 1) (p + (n + 1) + m) (by omega)).val.app U))
          (gradedCast (fun q ↦ (M.complex.X q).val.obj U)
            (add_right_comm p 1 m)
            (((M.mul (p + 1) m).app U) ((M.complex.d p (p + 1)).val.app U x) a)) =
        (((N.mul (p + (n + 1)) m).app U)
          ((ConcreteCategory.hom ((f.v (p + 1) (p + (n + 1)) (by omega)).val.app U))
            ((M.complex.d p (p + 1)).val.app U x)) a) := by
    convert hco1 using 1
    congr 1
    exact gradedCast_eq_transport (fun q ↦ (M.complex.X q).val.obj U)
      (add_right_comm p 1 m) (by omega) _
  rw [hco1match]
  have hco2match :
      (ConcreteCategory.hom ((f.v (p + m + 1) (p + (n + 1) + m) (by omega)).val.app U))
          (gradedCast (fun q ↦ (M.complex.X q).val.obj U)
            (add_assoc p m 1).symm
            (((M.mul p (m + 1)).app U) x ((A.complex.d m (m + 1)).val.app U a))) =
        gradedCast (fun q ↦ (N.complex.X q).val.obj U)
          (show p + n + (m + 1) = p + (n + 1) + m by omega)
          ((ConcreteCategory.hom
            ((f.v (p + (m + 1)) (p + n + (m + 1)) (by omega)).val.app U))
            (((M.mul p (m + 1)).app U) x ((A.complex.d m (m + 1)).val.app U a))) := by
    convert hco2 using 1
    · congr 1
      exact gradedCast_eq_transport (fun q ↦ (M.complex.X q).val.obj U)
        (add_assoc p m 1).symm (by omega) _
    · rw [hf2]
  rw [hco2match]
  rw [hf2]
  simp_all +arith only [gradedCast]
  have hbase : p + n + 1 = p + (n + 1) := by omega
  have hout1 : p + n + 1 + m = p + (n + 1) + m :=
    (add_right_comm (p + n) 1 m).trans hidx
  have hfirst :
      gradedCast (fun q ↦ (N.complex.X q).val.obj U)
          hout1
          (((N.mul (p + n + 1) m).app U)
            ((N.complex.d (p + n) (p + n + 1)).val.app U
              ((ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U)) x)) a) =
        ((N.mul (p + (n + 1)) m).app U)
          ((N.complex.d (p + n) (p + (n + 1))).val.app U
            ((ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U)) x)) a := by
    calc
      _ = gradedCast (fun q ↦ (N.complex.X q).val.obj U)
            (congrArg (fun q : ℤ ↦ q + m) hbase)
            (((N.mul (p + n + 1) m).app U)
              ((N.complex.d (p + n) (p + n + 1)).val.app U
                ((ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U)) x)) a) := by
          exact gradedCast_proof_irrel (fun q ↦ (N.complex.X q).val.obj U)
            hout1 (congrArg (fun q : ℤ ↦ q + m) hbase) _
      _ = ((N.mul (p + (n + 1)) m).app U)
            (gradedCast (fun q ↦ (N.complex.X q).val.obj U) hbase
              ((N.complex.d (p + n) (p + n + 1)).val.app U
                ((ConcreteCategory.hom ((f.v p (p + n) (by omega)).val.app U)) x))) a :=
          moduleMul_gradedCast_left (A := A) (M := N) hbase U _ _
      _ = _ := by rw [differential_app_cast (F := N.complex) hbase U _]
  simp only [gradedCast] at hfirst
  rw [hfirst]
  simp [smul_smul, mul_comm]
  abel

/-- A composite of action-linear cochains is action-linear. -/
lemma actionLinear_comp {M N P : DifferentialGradedModule.{u, v, w} A}
    {m n k : ℤ} (f : Cochain M.complex N.complex n)
    (g : Cochain N.complex P.complex m) (h : n + m = k)
    (hf : IsActionLinear A f) (hg : IsActionLinear A g) :
    IsActionLinear A (f.comp g h) := by
  intro p q l hpq U x a
  apply heq_of_eq
  rw [Cochain.comp_v f g h (p + l) (p + n + l) (q + l) (by omega) (by omega),
    Cochain.comp_v f g h p (p + n) q rfl (by omega)]
  simp only [sheaf_hom_app_comp (X := X)]
  rw [eq_of_heq (hf p (p + n) l rfl U x a)]
  exact eq_of_heq (hg (p + n) q l (by omega) U _ a)

/-- The identity cochain is action-linear. -/
lemma actionLinear_id (M : DifferentialGradedModule.{u, v, w} A) :
    IsActionLinear A (Cochain.ofHom (𝟙 M.complex)) := by
  intro p q m hpq U x a
  rcases (show p = q by omega) with rfl
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f]
  rfl

/-- The negative of an action-linear cochain is action-linear. -/
lemma actionLinear_neg {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : Cochain M.complex N.complex n) (hf : IsActionLinear A f) :
    IsActionLinear A (-f) := by
  have h := actionLinear_smul A (-1 : (limit X.O.obj : CommRingCat.{u})) f hf
  rwa [neg_one_smul] at h

/-- The difference of two action-linear cochains is action-linear. -/
lemma actionLinear_sub {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f g : Cochain M.complex N.complex n)
    (hf : IsActionLinear A f) (hg : IsActionLinear A g) :
    IsActionLinear A (f - g) := by
  rw [sub_eq_add_neg]
  exact actionLinear_add A _ _ hf (actionLinear_neg A g hg)

private noncomputable def actionLinearSubmodule
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    _root_.Submodule (limit X.O.obj : CommRingCat.{u})
      (Cochain M.complex N.complex n) where
  carrier := IsActionLinear A
  zero_mem' := actionLinear_zero A M N n
  add_mem' := fun hf hg => actionLinear_add A _ _ hf hg
  smul_mem' := fun r _ hf => actionLinear_smul A r _ hf

private noncomputable instance homogeneousMapAddCommGroup
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    AddCommGroup (HomogeneousMap A M N n) :=
  inferInstanceAs (AddCommGroup (actionLinearSubmodule A M N n))

private noncomputable instance homogeneousMapModule
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    Module (limit X.O.obj : CommRingCat.{u}) (HomogeneousMap A M N n) :=
  inferInstanceAs (Module (limit X.O.obj : CommRingCat.{u}) (actionLinearSubmodule A M N n))

@[implicit_reducible] private noncomputable def homogeneousDGCategory :
    DGCategory.{max u w, max u v (w + 1)} (limit X.O.obj : CommRingCat.{u}) where
  Obj := DifferentialGradedModule.{u, v, w} A
  Hom := HomogeneousMap A
  addCommGroup _ _ _ := inferInstance
  module _ _ _ := inferInstance
  d f := ⟨δ _ _ f.val, actionLinear_delta A f.val f.property⟩
  d_add f g := Subtype.ext (δ_add _ _ f.val g.val)
  d_smul r f := Subtype.ext (δ_smul _ _ r f.val)
  d_d f := Subtype.ext (δ_δ _ _ _ f.val)
  comp h g f := ⟨f.val.comp g.val (by omega),
    actionLinear_comp A f.val g.val (by omega) f.property g.property⟩
  comp_add_left h g₁ g₂ f := Subtype.ext (Cochain.comp_add f.val g₁.val g₂.val (by omega))
  comp_add_right h g f₁ f₂ := Subtype.ext (Cochain.add_comp f₁.val f₂.val g.val (by omega))
  comp_smul_left h r g f := Subtype.ext (Cochain.comp_smul f.val r g.val (by omega))
  comp_smul_right h r g f := Subtype.ext (Cochain.smul_comp r f.val g.val (by omega))
  leibniz {x y z m n k} h g f := by
    apply Subtype.ext
    change δ k (k + 1) (f.val.comp g.val (by omega)) =
      f.val.comp (δ m (m + 1) g.val) (by omega) +
        (-1 : (limit X.O.obj : CommRingCat.{u})) ^ m.natAbs •
          (δ n (n + 1) f.val).comp g.val (by omega)
    have hd := δ_comp f.val g.val (by omega : n + m = k) (n + 1) (m + 1) (k + 1)
      (by omega) (by omega) (by omega)
    rw [Units.smul_def] at hd
    change _ = _ + (m.negOnePow : ℤ) • _ at hd
    have hs : (m.negOnePow : ℤ) = (-1 : ℤ) ^ m.natAbs := Int.coe_negOnePow ℤ m
    rw [hs] at hd
    simpa only [← Int.cast_smul_eq_zsmul (limit X.O.obj : CommRingCat.{u}),
      Int.cast_pow, Int.cast_neg, Int.cast_one] using hd
  assoc h₁ h₂ h₃ h₄ e g f := Subtype.ext
    (Cochain.comp_assoc f.val g.val e.val (by omega) (by omega) (by omega))
  id M := ⟨Cochain.ofHom (𝟙 M.complex), actionLinear_id A M⟩
  id_comp f := Subtype.ext (Cochain.comp_id f.val)
  comp_id f := Subtype.ext (Cochain.id_comp f.val)
  d_id M := Subtype.ext (δ_ofHom (p := (1 : ℤ)) (𝟙 M.complex))

/-- The differential graded category of sheaf differential graded modules with its canonical
homogeneous maps and operations exists. -/
theorem existsDGCategoryData : Nonempty (DGCategoryData A) := by
  refine ⟨{ category := homogeneousDGCategory A
            objects := rfl
            homs := by intros; rfl
            homs_add := ?_
            differential := ?_
            composition := ?_
            identity := ?_ }⟩
  all_goals intros; rfl

/-- The canonical differential graded category of right modules over a sheaf of differential
graded algebras. -/
noncomputable def dgCategoryData : DGCategoryData A :=
  Classical.choice (existsDGCategoryData A)

/-- The object of the differential graded category `D.category` corresponding to a sheaf
differential graded module `M`. -/
abbrev moduleObject (D : DGCategoryData.{u, v, w} A)
    (M : DifferentialGradedModule.{u, v, w} A) : D.category.Obj :=
  D.objects.symm ▸ M

/-- The homogeneous morphisms of degree `n` from `M` to `N` in `D.category` are equivalent to
the homogeneous maps of degree `n` from `M` to `N` commuting with the action. -/
def moduleHomEquiv (D : DGCategoryData.{u, v, w} A)
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    D.category.Hom (moduleObject A D M) (moduleObject A D N) n ≃
      HomogeneousMap A M N n := Equiv.cast (D.homs M N n)

/-- The cochain underlying a homogeneous morphism of `D.category`. -/
abbrev underlyingCochain (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : D.category.Hom (moduleObject A D M) (moduleObject A D N) n) :
    Cochain M.complex N.complex n := (moduleHomEquiv A D M N n f).val

/-- The cochain underlying a sum of homogeneous morphisms is the sum of the cochains. -/
theorem underlyingCochain_add (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f g : D.category.Hom (moduleObject A D M) (moduleObject A D N) n) :
    underlyingCochain A D (f + g) = underlyingCochain A D f + underlyingCochain A D g :=
  D.homs_add M N n f g

/-- A homogeneous morphism of `D.category` is determined by its underlying cochain. -/
lemma underlyingCochain_injective (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ} :
    Function.Injective (underlyingCochain A D (M := M) (N := N) (n := n)) :=
  Subtype.val_injective.comp (moduleHomEquiv A D M N n).injective

/-- The cochain underlying the composite `g ∘ f` in `D.category` is the composite of the
underlying cochains of `f` and `g`. -/
lemma underlyingCochain_comp (D : DGCategoryData.{u, v, w} A)
    {M N P : DifferentialGradedModule.{u, v, w} A} {m n k : ℤ} (h : m + n = k)
    (g : D.category.Hom (moduleObject A D N) (moduleObject A D P) m)
    (f : D.category.Hom (moduleObject A D M) (moduleObject A D N) n) :
    underlyingCochain A D (D.category.comp h g f) =
      (underlyingCochain A D f).comp (underlyingCochain A D g) (by omega) :=
  eq_of_heq (D.composition M N P m n k h g f)

/-- The cochain underlying the zero morphism of `D.category` is zero. -/
lemma underlyingCochain_zero (D : DGCategoryData.{u, v, w} A)
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    underlyingCochain A D (0 : D.category.Hom
      (moduleObject A D M) (moduleObject A D N) n) = 0 := by
  let z := (moduleHomEquiv A D N N 0).symm ⟨0, actionLinear_zero A N N 0⟩
  have hz : underlyingCochain A D z = 0 :=
    congrArg Subtype.val ((moduleHomEquiv A D N N 0).apply_symm_apply _)
  have h := underlyingCochain_comp A D (show 0 + n = n by omega) z
    (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) n)
  simpa only [DGCategory.comp_zero_right, hz, Cochain.comp_zero] using h

/-- The cochain underlying the identity of `D.category` is the identity cochain. -/
lemma underlyingCochain_id (D : DGCategoryData.{u, v, w} A)
    (M : DifferentialGradedModule.{u, v, w} A) :
    underlyingCochain A D (D.category.id (moduleObject A D M)) = Cochain.ofHom (𝟙 M.complex) :=
  eq_of_heq (D.identity M)

/-- The degree-zero cochain of a morphism of differential graded modules commutes with the
action. -/
lemma actionLinear_ofHom {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) : IsActionLinear A (Cochain.ofHom f.toHomologicalComplex) := by
  intro p q m hpq U x a
  obtain rfl : p = q := by omega
  simpa only [Cochain.ofHom_v, heq_eq_eq] using f.map_mul p m U x a

private noncomputable def moduleMap (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    D.category.Hom (moduleObject A D M) (moduleObject A D N) 0 :=
  (moduleHomEquiv A D M N 0).symm
    ⟨Cochain.ofHom f.toHomologicalComplex, actionLinear_ofHom A f⟩

private lemma underlyingCochain_moduleMap (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    underlyingCochain A D (moduleMap A D f) = Cochain.ofHom f.toHomologicalComplex :=
  congrArg Subtype.val ((moduleHomEquiv A D M N 0).apply_symm_apply _)

private lemma moduleMap_closed (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    D.category.d (moduleMap A D f) = 0 := by
  apply underlyingCochain_injective A D
  rw [underlyingCochain_zero]
  show (D.homs M N (0 + 1) ▸ D.category.d (moduleMap A D f)).val = 0
  rw [eq_of_heq (D.differential M N 0 (moduleMap A D f))]
  show δ 0 1 (underlyingCochain A D (moduleMap A D f)) = 0
  rw [underlyingCochain_moduleMap, δ_ofHom]

private lemma moduleMap_comp (D : DGCategoryData.{u, v, w} A)
    {M N P : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) (g : N ⟶ P) :
    D.category.comp rfl (moduleMap A D g) (moduleMap A D f) =
      moduleMap A D (f ≫ g) := by
  apply underlyingCochain_injective A D
  rw [underlyingCochain_comp, underlyingCochain_moduleMap,
    underlyingCochain_moduleMap, underlyingCochain_moduleMap, ← Cochain.ofHom_comp]
  rfl

private lemma moduleMap_id (D : DGCategoryData.{u, v, w} A)
    (M : DifferentialGradedModule.{u, v, w} A) :
    moduleMap A D (𝟙 M) = D.category.id (moduleObject A D M) := by
  apply underlyingCochain_injective A D
  rw [underlyingCochain_moduleMap]
  exact (underlyingCochain_id A D M).symm

private lemma moduleMap_zero (D : DGCategoryData.{u, v, w} A)
    (M N : DifferentialGradedModule.{u, v, w} A) :
    moduleMap A D (0 : M ⟶ N) = 0 := by
  apply underlyingCochain_injective A D
  rw [underlyingCochain_zero, underlyingCochain_moduleMap]
  exact Cochain.ofHom_zero (F := M.complex) (G := N.complex)

/-! ### Finite direct sums of right differential graded modules

Right differential graded modules have arbitrary products, formed degreewise and without any
hypothesis on the site; finite products, a zero object and binary biproducts follow. -/

private instance hasFiniteProductsOfProducts :
    HasFiniteProducts (DifferentialGradedModule.{u, v, w} A) :=
  hasFiniteProducts_of_hasProducts.{w} _

private theorem hasZeroObjectOfProducts :
    HasZeroObject (DifferentialGradedModule.{u, v, w} A) :=
  hasZeroObject_of_hasTerminal_object

private instance hasBinaryBiproductsOfProducts :
    HasBinaryBiproducts (DifferentialGradedModule.{u, v, w} A) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private lemma exists_isZero_degree_id :
    ∃ Z : DifferentialGradedModule.{u, v, w} A, ∀ n : ℤ, 𝟙 (Z.complex.X n) = 0 := by
  obtain ⟨Z, hZ⟩ := (hasZeroObjectOfProducts.{u, v, w} A).zero
  refine ⟨Z, fun n => ?_⟩
  have h : (𝟙 Z) = (0 : Z ⟶ Z) := hZ.eq_of_src _ _
  have h' := congrArg (fun t : Z ⟶ Z => t.toHomologicalComplex.f n) h
  simpa only [id_f, zero_f] using h'

private lemma zero_cochain_from {Z M : DifferentialGradedModule.{u, v, w} A}
    (hZ : ∀ n : ℤ, 𝟙 (Z.complex.X n) = 0) (n : ℤ) :
    Subsingleton (Cochain Z.complex M.complex n) := by
  refine ⟨fun f g => ?_⟩
  apply Cochain.ext
  intro p q hpq
  calc
    f.v p q hpq = 𝟙 _ ≫ f.v p q hpq := (Category.id_comp _).symm
    _ = 0 := by rw [hZ, zero_comp]
    _ = 𝟙 _ ≫ g.v p q hpq := by rw [hZ, zero_comp]
    _ = g.v p q hpq := Category.id_comp _

private lemma zero_cochain_to {Z M : DifferentialGradedModule.{u, v, w} A}
    (hZ : ∀ n : ℤ, 𝟙 (Z.complex.X n) = 0) (n : ℤ) :
    Subsingleton (Cochain M.complex Z.complex n) := by
  refine ⟨fun f g => ?_⟩
  apply Cochain.ext
  intro p q hpq
  calc
    f.v p q hpq = f.v p q hpq ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = 0 := by rw [hZ, comp_zero]
    _ = g.v p q hpq ≫ 𝟙 _ := by rw [hZ, comp_zero]
    _ = g.v p q hpq := Category.comp_id _

/-- The zero differential graded module has unique homogeneous maps to and from every object in
every degree. -/
@[stacks 0FS4 "axiom_a"]
theorem hasZeroObject :
    ∃ Z : (dgCategoryData A).category.Obj,
      (∀ (M : (dgCategoryData A).category.Obj) (n : ℤ),
        Nonempty ((dgCategoryData A).category.Hom Z M n) ∧
          Subsingleton ((dgCategoryData A).category.Hom Z M n)) ∧
      (∀ (M : (dgCategoryData A).category.Obj) (n : ℤ),
        Nonempty ((dgCategoryData A).category.Hom M Z n) ∧
          Subsingleton ((dgCategoryData A).category.Hom M Z n)) := by
  let D := dgCategoryData A
  obtain ⟨Z, hZ⟩ := exists_isZero_degree_id A
  refine ⟨moduleObject A D Z, ?_, ?_⟩
  · intro M n
    obtain ⟨M, rfl⟩ := (Equiv.cast D.objects.symm).surjective M
    have := zero_cochain_from (A := A) (Z := Z) (M := M) hZ n
    exact ⟨⟨0⟩, Function.Injective.subsingleton (underlyingCochain_injective A D)⟩
  · intro M n
    obtain ⟨M, rfl⟩ := (Equiv.cast D.objects.symm).surjective M
    have := zero_cochain_to (A := A) (Z := Z) (M := M) hZ n
    exact ⟨⟨0⟩, Function.Injective.subsingleton (underlyingCochain_injective A D)⟩

private lemma biprod_degree_total (M N : DifferentialGradedModule.{u, v, w} A) (p : ℤ) :
    (biprod.fst : M ⊞ N ⟶ M).toHomologicalComplex.f p ≫
        (biprod.inl : M ⟶ M ⊞ N).toHomologicalComplex.f p +
      (biprod.snd : M ⊞ N ⟶ N).toHomologicalComplex.f p ≫
        (biprod.inr : N ⟶ M ⊞ N).toHomologicalComplex.f p = 𝟙 _ := by
  have h := congrArg (fun t : (M ⊞ N) ⟶ (M ⊞ N) => t.toHomologicalComplex.f p)
    (biprod.total (X := M) (Y := N))
  simpa only [add_f, comp_f, id_f] using h

private lemma biprod_degree_hom_ext {M N : DifferentialGradedModule.{u, v, w} A}
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (p : ℤ)
    (φ ψ : (M ⊞ N).complex.X p ⟶ Z)
    (hl : (biprod.inl : M ⟶ M ⊞ N).toHomologicalComplex.f p ≫ φ =
      (biprod.inl : M ⟶ M ⊞ N).toHomologicalComplex.f p ≫ ψ)
    (hr : (biprod.inr : N ⟶ M ⊞ N).toHomologicalComplex.f p ≫ φ =
      (biprod.inr : N ⟶ M ⊞ N).toHomologicalComplex.f p ≫ ψ) : φ = ψ := by
  have key : ∀ θ : (M ⊞ N).complex.X p ⟶ Z,
      (biprod.fst : M ⊞ N ⟶ M).toHomologicalComplex.f p ≫
          ((biprod.inl : M ⟶ M ⊞ N).toHomologicalComplex.f p ≫ θ) +
        (biprod.snd : M ⊞ N ⟶ N).toHomologicalComplex.f p ≫
          ((biprod.inr : N ⟶ M ⊞ N).toHomologicalComplex.f p ≫ θ) = θ := by
    intro θ
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      biprod_degree_total A M N p, Category.id_comp]
  rw [← key φ, ← key ψ, hl, hr]

private lemma biprod_hom_ext (D : DGCategoryData.{u, v, w} A)
    {M N P : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f g : D.category.Hom (moduleObject A D (M ⊞ N)) (moduleObject A D P) n)
    (hl : D.category.comp (add_zero n) f (moduleMap A D (biprod.inl : M ⟶ M ⊞ N)) =
      D.category.comp (add_zero n) g (moduleMap A D (biprod.inl : M ⟶ M ⊞ N)))
    (hr : D.category.comp (add_zero n) f (moduleMap A D (biprod.inr : N ⟶ M ⊞ N)) =
      D.category.comp (add_zero n) g (moduleMap A D (biprod.inr : N ⟶ M ⊞ N))) : f = g := by
  apply underlyingCochain_injective A D
  apply Cochain.ext
  intro p q hpq
  have key : ∀ {L : DifferentialGradedModule.{u, v, w} A} (ι : L ⟶ M ⊞ N),
      D.category.comp (add_zero n) f (moduleMap A D ι) =
        D.category.comp (add_zero n) g (moduleMap A D ι) →
      ι.toHomologicalComplex.f p ≫ (underlyingCochain A D f).v p q hpq =
        ι.toHomologicalComplex.f p ≫ (underlyingCochain A D g).v p q hpq := fun ι hι => by
    have h := congrArg (fun t => (underlyingCochain A D t).v p q hpq) hι
    simpa only [underlyingCochain_comp, underlyingCochain_moduleMap,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h
  exact biprod_degree_hom_ext A p _ _ (key _ hl) (key _ hr)

private lemma biprodBiproductData (D : DGCategoryData.{u, v, w} A)
    (M N : DifferentialGradedModule.{u, v, w} A) :
    Nonempty (DGCategory.BinaryBiproductData D.category
      (moduleObject A D M) (moduleObject A D N)) := by
  let i := moduleMap A D (biprod.inl : M ⟶ M ⊞ N)
  let j := moduleMap A D (biprod.inr : N ⟶ M ⊞ N)
  let p := moduleMap A D (biprod.fst : M ⊞ N ⟶ M)
  let q := moduleMap A D (biprod.snd : M ⊞ N ⟶ N)
  have hip : D.category.comp rfl p i = D.category.id (moduleObject A D M) := by
    rw [moduleMap_comp, biprod.inl_fst, moduleMap_id]
  have hjp : D.category.comp rfl p j = 0 := by
    rw [moduleMap_comp, biprod.inr_fst, moduleMap_zero]
  have hiq : D.category.comp rfl q i = 0 := by
    rw [moduleMap_comp, biprod.inl_snd, moduleMap_zero]
  have hjq : D.category.comp rfl q j = D.category.id (moduleObject A D N) := by
    rw [moduleMap_comp, biprod.inr_snd, moduleMap_id]
  refine ⟨{
    pt := moduleObject A D (M ⊞ N)
    inl := i
    inr := j
    fst := p
    snd := q
    inl_closed := moduleMap_closed A D _
    inr_closed := moduleMap_closed A D _
    fst_closed := moduleMap_closed A D _
    snd_closed := moduleMap_closed A D _
    inl_fst := hip
    inr_fst := hjp
    inl_snd := hiq
    inr_snd := hjq
    fst_inl_add_snd_inr := ?_ }⟩
  apply biprod_hom_ext A D
  · show D.category.comp rfl (D.category.comp rfl i p + D.category.comp rfl j q) i = _
    rw [D.category.comp_add_left,
      ← D.category.assoc rfl rfl rfl rfl,
      ← D.category.assoc rfl rfl rfl rfl, hip, hiq,
      D.category.comp_id, D.category.comp_zero_right]
    simp only [add_zero, D.category.id_comp]
    rfl
  · show D.category.comp rfl (D.category.comp rfl i p + D.category.comp rfl j q) j = _
    rw [D.category.comp_add_left,
      ← D.category.assoc rfl rfl rfl rfl,
      ← D.category.assoc rfl rfl rfl rfl, hjp, hjq,
      D.category.comp_zero_right, D.category.comp_id]
    simp only [zero_add, D.category.id_comp]
    rfl

/-- Any two right differential graded modules admit a differential graded direct sum with closed
degree-zero structure maps. -/
@[stacks 0FS4 "axiom_a"]
theorem hasBinaryBiproducts
    (M N : (dgCategoryData A).category.Obj) :
    Nonempty (DGCategory.BinaryBiproductData (dgCategoryData A).category M N) := by
  let D := dgCategoryData A
  obtain ⟨M, rfl⟩ := (Equiv.cast D.objects.symm).surjective M
  obtain ⟨N, rfl⟩ := (Equiv.cast D.objects.symm).surjective N
  exact biprodBiproductData A D M N

end SheafOfModules.DifferentialGradedModule
