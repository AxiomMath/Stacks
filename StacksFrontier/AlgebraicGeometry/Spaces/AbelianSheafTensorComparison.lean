module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafDerivedTensor
public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The tensor product of abelian sheaves is the tensor product over the constant sheaf `ℤ`

On a site `(C, J)` the abelian sheaves are the modules over the constant sheaf of rings `ℤ`,
`Stacks.Cohomology.intModulesEquivAbelianSheaves`. This file identifies the two tensor products
across that equivalence and deduces that **every cochain complex of abelian sheaves receives a
quasi-isomorphism from a K-flat one**.

## Main definitions

* `Stacks.Cohomology.intTensorModIso`: the sections over `V` of the tensor product of two abelian
  presheaves, as a tensor product over `ℤ`.
* `Stacks.Cohomology.modTensorComparison`: `τ`, the comparison of the two objectwise tensor
  products.
* `Stacks.Cohomology.abelianSheafTensorComparison`: **`ε`, the comparison of the two tensor
  products across the equivalence.**
* `Stacks.Cohomology.derivedMonoidalAbelianSheavesOfKFlat`: **the derived category of abelian
  sheaves on a site is monoidal.**

## Main results

* `Stacks.Cohomology.isLocallySurjective_modTensorComparison` and
  `Stacks.Cohomology.isLocallyInjective_modTensorComparison`: `τ` is locally bijective.
* `Stacks.Cohomology.w_modTensorComparison`: sheafification inverts `τ`.
* `Stacks.Cohomology.abelianSheafTensorComparison_naturality_left` and
  `Stacks.Cohomology.abelianSheafTensorComparison_naturality_right`: **the two naturality squares
  of `ε`.**
* `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves` and
  `Stacks.Cohomology.Leray.exists_kFlat_resolution_abelianSheaf`: **K-flat resolutions exist for
  the abelian sheaves of a site, and of a topological space.**

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonoidalClosed.FunctorCategory

universe u v

namespace Stacks.Cohomology

/-! ### The kernel of the comparison of tensor products, over a commutative ring -/

/-- **An induction principle for the kernel of the comparison from the tensor product over `ℤ`
to the tensor product over a commutative ring `R`.** A property of elements of `M ⊗[ℤ] N` which
holds on the elements `(a • m) ⊗ₜ n - m ⊗ₜ (a • n)` and is closed under `0`, addition and the
`R`-action holds on the whole kernel. -/
theorem intTensor_eq_zero_induction {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (P : TensorProduct ℤ M N → Prop)
    (hgen : ∀ (a : R) (m : M) (n : N), P ((a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)))
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (r : R) x, P x → P (r • x))
    (x : TensorProduct ℤ M N)
    (hx : TensorProduct.mapOfCompatibleSMul R ℤ R M N x = 0) : P x := by
  rw [← LinearMap.mem_ker,
    TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul R M] at hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨a, m, n, rfl⟩ := h; exact hgen a m n
  | zero => exact hzero
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul r x _ hx => exact hsmul r x hx

section Site

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u}] [HasSheafify J RingCat.{u}]
  [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal
  AddCommGrpCat.symmetricCategoryTransported
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf
  Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- The presheaf of abelian groups of sections of a module over the constant sheaf of
commutative rings `ℤ`. -/
abbrev modAbelianPresheaf
    (A : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf _).obj A.val

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The abelian sheaf attached to a module by
`Stacks.Cohomology.intModulesEquivAbelianSheaves` has
`Stacks.Cohomology.modAbelianPresheaf` as its underlying presheaf. -/
theorem val_functor_intModulesEquivAbelianSheaves_obj
    (A : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    ((intModulesEquivAbelianSheaves J).functor.obj A).obj = modAbelianPresheaf J A := rfl

/-- Two morphisms out of a tensor product of abelian groups agree if they agree on pure tensors. -/
private theorem uliftInt_tensor_hom_ext {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} {V : Cᵒᵖ}
    {Z : AddCommGrpCat.{u}} {f g : (P ⊗ Q).obj V ⟶ Z}
    (h : ∀ (a : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj (P.obj V))
      (b : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj (Q.obj V)),
      f (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b) = g (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b)) :
    f = g := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul a b => exact h a b

/-- The counit of `AddCommGrpCat.uliftIntEquivalence` is natural, read on elements. -/
private theorem uliftInt_counit_map {X Y : AddCommGrpCat.{u}} (φ : X ⟶ Y)
    (a : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj X) :
    (AddCommGrpCat.uliftIntEquivalence.{u}.counitIso.app Y).addCommGroupIsoToAddEquiv
        (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map φ a) =
      φ ((AddCommGrpCat.uliftIntEquivalence.{u}.counitIso.app X).addCommGroupIsoToAddEquiv a) :=
  NatTrans.naturality_apply AddCommGrpCat.uliftIntEquivalence.{u}.counitIso.hom φ a

variable (A B : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J))

/-- **The sections of a module over the constant sheaf of commutative rings `ℤ` are a module over
the sections of that sheaf of commutative rings.** This is the module structure the sheaf of
modules carries, named at the sheaf of *commutative* rings rather than at the sheaf of rings
underlying it. -/
instance module_modAbelianPresheaf_obj (V : Cᵒᵖ) :
    Module ((constIntCommSheaf J).obj.obj V) ((modAbelianPresheaf J A).obj V) :=
  inferInstanceAs (Module ((constIntCommSheaf J).obj.obj V) (A.val.obj V))

/-- **The sections of a module over the constant sheaf of commutative rings `ℤ` are the sections
of the module over a universe-lifted copy of `ℤ` that the transported monoidal structure on
abelian groups tensors over.** This is the counit of `AddCommGrpCat.uliftIntEquivalence`, read as
an additive equivalence. -/
def modSectionsCounit (V : Cᵒᵖ) :
    (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj
        ((modAbelianPresheaf J A).obj V) : Type u) ≃+ ((modAbelianPresheaf J A).obj V) :=
  (AddCommGrpCat.uliftIntEquivalence.{u}.counitIso.app
    ((modAbelianPresheaf J A).obj V)).addCommGroupIsoToAddEquiv

/-- **The sections over `V` of the tensor product of the two underlying abelian presheaves are
the tensor product over `ℤ` of the sections.** The tensor product of abelian groups is the
transported one, so its sections are a tensor product over a universe-lifted copy of `ℤ` of the
images of the sections under the quasi-inverse of `AddCommGrpCat.uliftIntEquivalence`; the base
is changed by `AddCommGrpCat.tensorProductULiftIntEquiv` and the two factors by
`Stacks.Cohomology.modSectionsCounit`. -/
def intTensorModIso (V : Cᵒᵖ) :
    (modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).obj V ≅
      AddCommGrpCat.of (TensorProduct ℤ ((modAbelianPresheaf J A).obj V)
        ((modAbelianPresheaf J B).obj V)) :=
  AddEquiv.toAddCommGrpIso
    ((AddCommGrpCat.tensorProductULiftIntEquiv _ _).symm.trans
      (TensorProduct.congr (modSectionsCounit J A V).toIntLinearEquiv
        (modSectionsCounit J B V).toIntLinearEquiv).toAddEquiv)

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.intTensorModIso` on a pure tensor. -/
theorem intTensorModIso_hom_tmul (V : Cᵒᵖ)
    (a : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj ((modAbelianPresheaf J A).obj V))
    (b : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj ((modAbelianPresheaf J B).obj V)) :
    (intTensorModIso J A B V).hom (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b) =
      modSectionsCounit J A V a ⊗ₜ[ℤ] modSectionsCounit J B V b := rfl

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.intTensorModIso` is natural in `V`: the restriction maps of the tensor
product of the two abelian presheaves become the tensor product over `ℤ` of the restriction
maps. -/
theorem intTensorModIso_hom_naturality {V W : Cᵒᵖ} (f : V ⟶ W) :
    (modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).map f ≫ (intTensorModIso J A B W).hom =
      (intTensorModIso J A B V).hom ≫ AddCommGrpCat.ofHom
        (TensorProduct.map ((modAbelianPresheaf J A).map f).hom.toIntLinearMap
          ((modAbelianPresheaf J B).map f).hom.toIntLinearMap).toAddMonoidHom := by
  refine uliftInt_tensor_hom_ext fun a b => ?_
  show (intTensorModIso J A B W).hom
      ((AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
          ((modAbelianPresheaf J A).map f) a) ⊗ₜ[AddCommGrpCat.ULiftInt.{u}]
        (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
          ((modAbelianPresheaf J B).map f) b)) =
    TensorProduct.map ((modAbelianPresheaf J A).map f).hom.toIntLinearMap
      ((modAbelianPresheaf J B).map f).hom.toIntLinearMap
      ((intTensorModIso J A B V).hom (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b))
  rw [intTensorModIso_hom_tmul, intTensorModIso_hom_tmul, TensorProduct.map_tmul]
  exact congrArg₂ (· ⊗ₜ[ℤ] ·) (uliftInt_counit_map _ a) (uliftInt_counit_map _ b)

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.intTensorModIso` is natural in `V`, read on sections. -/
theorem intTensorModIso_hom_naturality_apply {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : (modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).obj V) :
    (intTensorModIso J A B W).hom
        ((modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).map f x) =
      TensorProduct.map ((modAbelianPresheaf J A).map f).hom.toIntLinearMap
        ((modAbelianPresheaf J B).map f).hom.toIntLinearMap
        ((intTensorModIso J A B V).hom x) :=
  congrArg (fun k => AddCommGrpCat.Hom.hom k x) (intTensorModIso_hom_naturality J A B f)

/-! ### The comparison of the two objectwise tensor products -/

/-- The presheaf-level tensor product `U ↦ A(U) ⊗_{ℤ} B(U)` of presheaves of modules over the
constant sheaf of commutative rings `ℤ`, as a bifunctor: the curried tensor of the monoidal
product on presheaves of modules. -/
noncomputable def constIntPresheafTensor :
    PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)).obj ⥤
      PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)).obj ⥤
        PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)).obj :=
  letI : MonoidalCategory
      (PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)).obj) :=
    (inferInstance : MonoidalCategory
      (PresheafOfModules ((constIntCommSheaf J).obj ⋙ forget₂ CommRingCat RingCat)))
  MonoidalCategory.curriedTensor
    (PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (constIntCommSheaf J)).obj)

/-- The presheaf of abelian groups of sections of the objectwise tensor product over the constant
sheaf of commutative rings `ℤ`. -/
abbrev modPresheafTensor : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf _).obj
    (((constIntPresheafTensor J).obj A.val).obj B.val)

/-- **The comparison `τ` from the objectwise tensor product of the two underlying abelian
presheaves to the objectwise tensor product over the constant sheaf of commutative rings `ℤ`.**
Over `V` it is `TensorProduct.mapOfCompatibleSMul`, read through
`Stacks.Cohomology.intTensorModIso`. -/
def modTensorComparison :
    modAbelianPresheaf J A ⊗ modAbelianPresheaf J B ⟶ modPresheafTensor J A B where
  app V := (intTensorModIso J A B V).hom ≫ AddCommGrpCat.ofHom
    (TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj V) ℤ
      ((constIntCommSheaf J).obj.obj V) ((modAbelianPresheaf J A).obj V)
      ((modAbelianPresheaf J B).obj V)).toAddMonoidHom
  naturality V W f := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
        exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    | tmul a b =>
        change (TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj W) ℤ
              ((constIntCommSheaf J).obj.obj W) (A.val.obj W) (B.val.obj W))
            ((intTensorModIso J A B W).hom
              ((modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).map f
                (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b))) =
          (modPresheafTensor J A B).map f
            ((TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj V) ℤ
              ((constIntCommSheaf J).obj.obj V) (A.val.obj V) (B.val.obj V))
              ((intTensorModIso J A B V).hom (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b)))
        have h := intTensorModIso_hom_naturality_apply J A B f
          (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b)
        rw [h, intTensorModIso_hom_tmul, TensorProduct.map_tmul]
        rfl

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.modTensorComparison` on a pure tensor. -/
theorem modTensorComparison_app_tmul (V : Cᵒᵖ)
    (a : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj ((modAbelianPresheaf J A).obj V))
    (b : AddCommGrpCat.uliftIntEquivalence.{u}.inverse.obj ((modAbelianPresheaf J B).obj V)) :
    (modTensorComparison J A B).app V (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b) =
      modSectionsCounit J A V a ⊗ₜ[(constIntCommSheaf J).obj.obj V] modSectionsCounit J B V b :=
  rfl

/-! ### Local surjectivity -/

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`τ` is objectwise surjective.** -/
theorem surjective_modTensorComparison_app (V : Cᵒᵖ) :
    Function.Surjective ((modTensorComparison J A B).app V) := by
  have hsurj : Function.Surjective (TensorProduct.mapOfCompatibleSMul
      ((constIntCommSheaf J).obj.obj V) ℤ ((constIntCommSheaf J).obj.obj V)
      ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V)) :=
    TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _
  intro t
  obtain ⟨s, hs⟩ := hsurj t
  obtain ⟨x, hx⟩ :=
    (ConcreteCategory.bijective_of_isIso (intTensorModIso J A B V).hom).surjective s
  refine ⟨x, ?_⟩
  show TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj V) ℤ
    ((constIntCommSheaf J).obj.obj V) ((modAbelianPresheaf J A).obj V)
    ((modAbelianPresheaf J B).obj V) ((intTensorModIso J A B V).hom x) = t
  rwa [hx]

/-- **`τ` is locally surjective.** -/
instance isLocallySurjective_modTensorComparison :
    Presheaf.IsLocallySurjective J (modTensorComparison J A B) :=
  Presheaf.isLocallySurjective_of_surjective J _ (surjective_modTensorComparison_app J A B)

/-! ### Local injectivity -/

/-- The restriction maps of the objectwise tensor product over `ℤ` of the two underlying abelian
presheaves, as `ℤ`-linear maps. -/
def intTensorRestrict {V W : Cᵒᵖ} (f : V ⟶ W) :
    TensorProduct ℤ ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V) →ₗ[ℤ]
      TensorProduct ℤ ((modAbelianPresheaf J A).obj W) ((modAbelianPresheaf J B).obj W) :=
  TensorProduct.map ((modAbelianPresheaf J A).map f).hom.toIntLinearMap
    ((modAbelianPresheaf J B).map f).hom.toIntLinearMap

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.intTensorRestrict` on a pure tensor. -/
@[simp]
theorem intTensorRestrict_tmul {V W : Cᵒᵖ} (f : V ⟶ W) (m : (modAbelianPresheaf J A).obj V)
    (n : (modAbelianPresheaf J B).obj V) :
    intTensorRestrict J A B f (m ⊗ₜ[ℤ] n) =
      ((modAbelianPresheaf J A).map f) m ⊗ₜ[ℤ] ((modAbelianPresheaf J B).map f) n := rfl

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `Stacks.Cohomology.intTensorRestrict` is compatible with composition. -/
theorem intTensorRestrict_comp {V W X : Cᵒᵖ} (f : V ⟶ W) (g : W ⟶ X)
    (y : TensorProduct ℤ ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V)) :
    intTensorRestrict J A B (f ≫ g) y =
      intTensorRestrict J A B g (intTensorRestrict J A B f y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul m n => rw [intTensorRestrict_tmul, intTensorRestrict_tmul, intTensorRestrict_tmul,
      Functor.map_comp, Functor.map_comp]; rfl

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The restriction maps of the objectwise tensor product over `ℤ` are semilinear** over the
restriction maps of the constant sheaf of commutative rings `ℤ`, the action being on the left
factor. -/
theorem intTensorRestrict_smul {V W : Cᵒᵖ} (f : V ⟶ W) (r : (constIntCommSheaf J).obj.obj V)
    (y : TensorProduct ℤ ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V)) :
    intTensorRestrict J A B f (r • y) =
      ((constIntCommSheaf J).obj.map f r) • intTensorRestrict J A B f y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul m n =>
      rw [TensorProduct.smul_tmul', intTensorRestrict_tmul, intTensorRestrict_tmul,
        TensorProduct.smul_tmul']
      exact congrArg (· ⊗ₜ[ℤ] ((modAbelianPresheaf J B).map f) n) (A.val.map_smul f r m)

/-- The sieve of restrictions on which an element of the objectwise tensor product over `ℤ`
vanishes. -/
def intTensorVanishingSieve {V : Cᵒᵖ}
    (y : TensorProduct ℤ ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V)) :
    Sieve V.unop where
  arrows _ g := intTensorRestrict J A B g.op y = 0
  downward_closed {_ _ f} hf g := by
    rw [show ((g ≫ f).op : V ⟶ _) = f.op ≫ g.op from rfl, intTensorRestrict_comp, hf, map_zero]

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The sections of the constant sheaf of commutative rings `ℤ` are locally integers**: on the
image sieve of a section under the unit of sheafification, its restriction is an integer. -/
theorem exists_intCast_of_imageSieve {V : Cᵒᵖ} (a : (constIntCommSheaf J).obj.obj V) {W : C}
    (g : W ⟶ V.unop)
    (hg : Presheaf.imageSieve
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)))) a g) :
    ∃ z : ℤ, (constIntCommSheaf J).obj.map g.op a =
      (z : (constIntCommSheaf J).obj.obj (Opposite.op W)) := by
  obtain ⟨t, ht⟩ := hg
  refine ⟨t.down, ?_⟩
  have h1 : t = ((t.down : ℤ) : ULift.{u} ℤ) := by cases t; rfl
  have h2 := map_intCast
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)))).app
      (Opposite.op W)).hom t.down
  rw [← h1] at h2
  exact ht.symm.trans h2

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The sieve on which a generator `(a • m) ⊗ₜ n - m ⊗ₜ (a • n)` of the kernel of `τ` vanishes
is covering.** -/
theorem intTensorVanishingSieve_generator_mem {V : Cᵒᵖ}
    (a : (constIntCommSheaf J).obj.obj V) (m : (modAbelianPresheaf J A).obj V)
    (n : (modAbelianPresheaf J B).obj V) :
    intTensorVanishingSieve J A B ((a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)) ∈ J V.unop := by
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)))) a)
  intro Y g hg
  obtain ⟨z, hz⟩ := exists_intCast_of_imageSieve J a g hg
  have hsmA : ((modAbelianPresheaf J A).map g.op) (a • m) =
      ((constIntCommSheaf J).obj.map g.op a) • ((modAbelianPresheaf J A).map g.op m) :=
    A.val.map_smul g.op a m
  have hsmB : ((modAbelianPresheaf J B).map g.op) (a • n) =
      ((constIntCommSheaf J).obj.map g.op a) • ((modAbelianPresheaf J B).map g.op n) :=
    B.val.map_smul g.op a n
  show intTensorRestrict J A B g.op ((a • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (a • n)) = 0
  rw [map_sub, intTensorRestrict_tmul, intTensorRestrict_tmul, hsmA, hsmB,
    hz, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, TensorProduct.smul_tmul, sub_self]

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **An element of the objectwise tensor product over `ℤ` killed by the comparison to the tensor
product over the constant sheaf of commutative rings `ℤ` vanishes on a covering sieve.** -/
theorem intTensorVanishingSieve_mem {V : Cᵒᵖ}
    (y : TensorProduct ℤ ((modAbelianPresheaf J A).obj V) ((modAbelianPresheaf J B).obj V))
    (hy : TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj V) ℤ
      ((constIntCommSheaf J).obj.obj V) ((modAbelianPresheaf J A).obj V)
      ((modAbelianPresheaf J B).obj V) y = 0) :
    intTensorVanishingSieve J A B y ∈ J V.unop := by
  refine intTensor_eq_zero_induction
    (fun y => intTensorVanishingSieve J A B y ∈ J V.unop)
    (intTensorVanishingSieve_generator_mem J A B) ?_ ?_ ?_ y hy
  · exact J.superset_covering (fun _ g _ => show intTensorRestrict J A B g.op 0 = 0 from map_zero _)
      (J.top_mem V.unop)
  · intro y₁ y₂ h₁ h₂
    refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
    intro Y g hg
    show intTensorRestrict J A B g.op (y₁ + y₂) = 0
    rw [map_add, show intTensorRestrict J A B g.op y₁ = 0 from hg.1,
      show intTensorRestrict J A B g.op y₂ = 0 from hg.2, add_zero]
  · intro r y h
    refine J.superset_covering ?_ h
    intro Y g hg
    show intTensorRestrict J A B g.op (r • y) = 0
    rw [intTensorRestrict_smul, show intTensorRestrict J A B g.op y = 0 from hg, smul_zero]

/-- **`τ` is locally injective.** -/
instance isLocallyInjective_modTensorComparison :
    Presheaf.IsLocallyInjective J (modTensorComparison J A B) where
  equalizerSieve_mem {V} x₁ x₂ h := by
    have key : TensorProduct.mapOfCompatibleSMul ((constIntCommSheaf J).obj.obj V) ℤ
        ((constIntCommSheaf J).obj.obj V) ((modAbelianPresheaf J A).obj V)
        ((modAbelianPresheaf J B).obj V)
        ((intTensorModIso J A B V).hom x₁ - (intTensorModIso J A B V).hom x₂) = 0 := by
      rwa [map_sub, sub_eq_zero]
    refine J.superset_covering ?_ (intTensorVanishingSieve_mem J A B _ key)
    intro Y g hg
    have hg' : intTensorRestrict J A B g.op ((intTensorModIso J A B V).hom x₁) -
        intTensorRestrict J A B g.op ((intTensorModIso J A B V).hom x₂) = 0 := by
      rwa [← map_sub]
    change (modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).map g.op x₁ =
      (modAbelianPresheaf J A ⊗ modAbelianPresheaf J B).map g.op x₂
    refine (ConcreteCategory.bijective_of_isIso
      (intTensorModIso J A B (Opposite.op Y)).hom).injective ?_
    rwa [intTensorModIso_hom_naturality_apply, intTensorModIso_hom_naturality_apply,
      ← sub_eq_zero]

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`τ` is inverted by sheafification.** -/
theorem w_modTensorComparison : J.W (modTensorComparison J A B) :=
  J.W_of_isLocallyBijective _

/-! ### Naturality of the comparison in each variable -/

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`τ` is natural in the first variable.** -/
theorem modTensorComparison_naturality_left
    {A₁ A₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)} (f : A₁ ⟶ A₂)
    (B₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    (((PresheafOfModules.toPresheaf _).map f.val) ▷ modAbelianPresheaf J B₁) ≫
        modTensorComparison J A₂ B₁ =
      modTensorComparison J A₁ B₁ ≫ (PresheafOfModules.toPresheaf _).map
        (((constIntPresheafTensor J).map f.val).app
          B₁.val) := by
  refine NatTrans.ext (funext fun V => uliftInt_tensor_hom_ext fun a b => ?_)
  show (modTensorComparison J A₂ B₁).app V
      ((AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
          (((PresheafOfModules.toPresheaf _).map f.val).app V) a)
        ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b) =
      ((PresheafOfModules.toPresheaf _).map
        (((constIntPresheafTensor J).map f.val).app
          B₁.val)).app V
      ((modTensorComparison J A₁ B₁).app V (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b))
  rw [modTensorComparison_app_tmul J A₂ B₁ V
      (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
        (((PresheafOfModules.toPresheaf _).map f.val).app V) a) b,
    modTensorComparison_app_tmul J A₁ B₁ V a b]
  exact congrArg (· ⊗ₜ[_] modSectionsCounit J B₁ V b) (uliftInt_counit_map _ a)

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`τ` is natural in the second variable.** -/
theorem modTensorComparison_naturality_right
    (A₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J))
    {B₁ B₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)}
    (g : B₁ ⟶ B₂) :
    (modAbelianPresheaf J A₁ ◁ ((PresheafOfModules.toPresheaf _).map g.val)) ≫
        modTensorComparison J A₁ B₂ =
      modTensorComparison J A₁ B₁ ≫ (PresheafOfModules.toPresheaf _).map
        ((((constIntPresheafTensor J).obj A₁.val).map
          g.val)) := by
  refine NatTrans.ext (funext fun V => uliftInt_tensor_hom_ext fun a b => ?_)
  show (modTensorComparison J A₁ B₂).app V
      (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}]
        (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
          (((PresheafOfModules.toPresheaf _).map g.val).app V) b)) =
      ((PresheafOfModules.toPresheaf _).map
        ((((constIntPresheafTensor J).obj
          A₁.val).map g.val))).app V
      ((modTensorComparison J A₁ B₁).app V (a ⊗ₜ[AddCommGrpCat.ULiftInt.{u}] b))
  rw [modTensorComparison_app_tmul J A₁ B₂ V a
      (AddCommGrpCat.uliftIntEquivalence.{u}.inverse.map
        (((PresheafOfModules.toPresheaf _).map g.val).app V) b),
    modTensorComparison_app_tmul J A₁ B₁ V a b]
  exact congrArg (modSectionsCounit J A₁ V a ⊗ₜ[_] ·) (uliftInt_counit_map _ b)

/-! ### The comparison `ε` of the two tensor products -/

/-- **An abelian sheaf of modules is the sheafification of its own presheaf of sections**, by the
counit of the sheafification adjunction. -/
def modSheafifyCounitIso :
    (presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J A) ≅
      (intModulesEquivAbelianSheaves J).functor.obj A :=
  (asIso (sheafificationAdjunction J AddCommGrpCat.{u}).counit).app
    ((intModulesEquivAbelianSheaves J).functor.obj A)

/-- **Sheafification inverts `τ`.** -/
instance isIso_presheafToSheaf_map_modTensorComparison :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map (modTensorComparison J A B)) :=
  (J.W_iff _).mp (w_modTensorComparison J A B)

/-- **`σ`: the tensor product of the two sheafified presheaves of sections is the abelian sheaf
underlying the tensor product over the constant sheaf of commutative rings `ℤ`.** It is the
tensorator of sheafification followed by the sheafification of `τ`. -/
def modSheafTensorComparisonIso :
    (presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J A) ⊗
        (presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J B) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj (modPresheafTensor J A B) :=
  Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u}) (modAbelianPresheaf J A)
      (modAbelianPresheaf J B) ≪≫
    asIso ((presheafToSheaf J AddCommGrpCat.{u}).map (modTensorComparison J A B))

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The forward map of `Stacks.Cohomology.modSheafTensorComparisonIso`. -/
theorem modSheafTensorComparisonIso_hom :
    (modSheafTensorComparisonIso J A B).hom =
      Functor.LaxMonoidal.μ (presheafToSheaf J AddCommGrpCat.{u}) (modAbelianPresheaf J A)
          (modAbelianPresheaf J B) ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map (modTensorComparison J A B) := rfl

/-- **`ε`: the tensor product of abelian sheaves is the tensor product over the constant sheaf of
commutative rings `ℤ`, across `Stacks.Cohomology.intModulesEquivAbelianSheaves`.** -/
def abelianSheafTensorComparison :
    (intModulesEquivAbelianSheaves J).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J)).obj A).obj B) ≅
      ((intModulesEquivAbelianSheaves J).functor.obj A) ⊗
        ((intModulesEquivAbelianSheaves J).functor.obj B) :=
  (modSheafTensorComparisonIso J A B).symm ≪≫
    MonoidalCategory.tensorIso (modSheafifyCounitIso J A) (modSheafifyCounitIso J B)

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `σ` is natural in the first variable. -/
theorem modSheafTensorComparisonIso_naturality_left
    {A₁ A₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)} (f : A₁ ⟶ A₂)
    (B₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    ((presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf _).map f.val) ▷
        (presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J B₁)) ≫
        (modSheafTensorComparisonIso J A₂ B₁).hom =
      (modSheafTensorComparisonIso J A₁ B₁).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf _).map
          (((constIntPresheafTensor J).map f.val).app
            B₁.val)) := by
  rw [modSheafTensorComparisonIso_hom, modSheafTensorComparisonIso_hom]
  simp only [Functor.LaxMonoidal.μ_natural_left_assoc, Category.assoc, ← Functor.map_comp]
  rw [modTensorComparison_naturality_left, Functor.map_comp]

omit [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `σ` is natural in the second variable. -/
theorem modSheafTensorComparisonIso_naturality_right
    (A₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J))
    {B₁ B₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)}
    (g : B₁ ⟶ B₂) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J A₁) ◁
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf _).map g.val)) ≫
        (modSheafTensorComparisonIso J A₁ B₂).hom =
      (modSheafTensorComparisonIso J A₁ B₁).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf _).map
          ((((constIntPresheafTensor J).obj A₁.val)).map
            g.val)) := by
  rw [modSheafTensorComparisonIso_hom, modSheafTensorComparisonIso_hom]
  simp only [Functor.LaxMonoidal.μ_natural_right_assoc, Category.assoc, ← Functor.map_comp]
  rw [modTensorComparison_naturality_right, Functor.map_comp]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The counit comparison is natural in the first variable. -/
theorem modSheafifyCounitIso_tensor_naturality_left
    {A₁ A₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)} (f : A₁ ⟶ A₂)
    (B₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    ((presheafToSheaf J AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf _).map f.val) ▷
        (presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J B₁)) ≫
        (MonoidalCategory.tensorIso (modSheafifyCounitIso J A₂)
          (modSheafifyCounitIso J B₁)).hom =
      (MonoidalCategory.tensorIso (modSheafifyCounitIso J A₁)
          (modSheafifyCounitIso J B₁)).hom ≫
        ((intModulesEquivAbelianSheaves J).functor.map f ▷
          (intModulesEquivAbelianSheaves J).functor.obj B₁) := by
  have hc : (presheafToSheaf J AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map f.val) ≫ (modSheafifyCounitIso J A₂).hom =
      (modSheafifyCounitIso J A₁).hom ≫ (intModulesEquivAbelianSheaves J).functor.map f :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).counit.naturality
      ((intModulesEquivAbelianSheaves J).functor.map f)
  rw [MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorIso_hom,
    MonoidalCategory.whiskerRight_comp_tensorHom, MonoidalCategory.tensorHom_comp_whiskerRight,
    hc]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The counit comparison is natural in the second variable. -/
theorem modSheafifyCounitIso_tensor_naturality_right
    (A₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J))
    {B₁ B₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)}
    (g : B₁ ⟶ B₂) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj (modAbelianPresheaf J A₁) ◁
        (presheafToSheaf J AddCommGrpCat.{u}).map
          ((PresheafOfModules.toPresheaf _).map g.val)) ≫
        (MonoidalCategory.tensorIso (modSheafifyCounitIso J A₁)
          (modSheafifyCounitIso J B₂)).hom =
      (MonoidalCategory.tensorIso (modSheafifyCounitIso J A₁)
          (modSheafifyCounitIso J B₁)).hom ≫
        ((intModulesEquivAbelianSheaves J).functor.obj A₁ ◁
          (intModulesEquivAbelianSheaves J).functor.map g) := by
  have hc : (presheafToSheaf J AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map g.val) ≫ (modSheafifyCounitIso J B₂).hom =
      (modSheafifyCounitIso J B₁).hom ≫ (intModulesEquivAbelianSheaves J).functor.map g :=
    (sheafificationAdjunction J AddCommGrpCat.{u}).counit.naturality
      ((intModulesEquivAbelianSheaves J).functor.map g)
  rw [MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorIso_hom,
    MonoidalCategory.whiskerLeft_comp_tensorHom, MonoidalCategory.tensorHom_comp_whiskerLeft,
    hc]

/-- Naturality of `σ.inv ≫ τ` from the naturality of `σ.hom` and of `τ`. -/
private theorem map_comp_inv_comp_eq {D : Type*} [Category D] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : D}
    (σ₁ : X₁ ≅ Y₁) (σ₂ : X₂ ≅ Y₂) (τ₁ : X₁ ⟶ Z₁) (τ₂ : X₂ ⟶ Z₂)
    {a : X₁ ⟶ X₂} {b : Y₁ ⟶ Y₂} {d : Z₁ ⟶ Z₂} (h₁ : a ≫ σ₂.hom = σ₁.hom ≫ b)
    (h₂ : a ≫ τ₂ = τ₁ ≫ d) : b ≫ σ₂.inv ≫ τ₂ = σ₁.inv ≫ τ₁ ≫ d := by
  have h : b ≫ σ₂.inv = σ₁.inv ≫ a := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h, Category.assoc, h₂]

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **`ε` is natural in the first variable.** -/
theorem abelianSheafTensorComparison_naturality_left
    {A₁ A₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)} (f : A₁ ⟶ A₂)
    (B₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)) :
    (intModulesEquivAbelianSheaves J).functor.map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J)).map f).app B₁) ≫
        (abelianSheafTensorComparison J A₂ B₁).hom =
      (abelianSheafTensorComparison J A₁ B₁).hom ≫
        (((curriedTensor (Sheaf J AddCommGrpCat.{u})).map
            ((intModulesEquivAbelianSheaves J).functor.map f)).app
          ((intModulesEquivAbelianSheaves J).functor.obj B₁)) := by
  exact map_comp_inv_comp_eq _ _ _ _ (modSheafTensorComparisonIso_naturality_left J f B₁)
    (modSheafifyCounitIso_tensor_naturality_left J f B₁)

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- **`ε` is natural in the second variable.** -/
theorem abelianSheafTensorComparison_naturality_right
    (A₁ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J))
    {B₁ B₂ : Stacks.SheafOfModules.DerivedMonoidal.Mod.{u} (constIntCommSheaf J)}
    (g : B₁ ⟶ B₂) :
    (intModulesEquivAbelianSheaves J).functor.map
        ((((Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J)).obj A₁)).map g) ≫
        (abelianSheafTensorComparison J A₁ B₂).hom =
      (abelianSheafTensorComparison J A₁ B₁).hom ≫
        (((curriedTensor (Sheaf J AddCommGrpCat.{u})).obj
            ((intModulesEquivAbelianSheaves J).functor.obj A₁)).map
          ((intModulesEquivAbelianSheaves J).functor.map g)) := by
  exact map_comp_inv_comp_eq _ _ _ _ (modSheafTensorComparisonIso_naturality_right J A₁ g)
    (modSheafifyCounitIso_tensor_naturality_right J A₁ g)

/-! ### K-flat resolutions of complexes of abelian sheaves -/

/-- **Every cochain complex of abelian sheaves on a site receives a quasi-isomorphism from a
complex that is K-flat for the tensor product of abelian sheaves.** -/
theorem exists_kFlat_resolution_abelianSheaves
    (G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :
    ∃ (P : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Sheaf J AddCommGrpCat.{u})) P ∧
        QuasiIso f :=
  CochainComplex.KFlatBifunctor.exists_kFlat_resolution_of_equivalence
    (Stacks.SheafOfModules.Tensor.sheafTensor (constIntCommSheaf J))
    (curriedTensor (Sheaf J AddCommGrpCat.{u})) (intModulesEquivAbelianSheaves J)
    (abelianSheafTensorComparison J)
    (abelianSheafTensorComparison_naturality_left J)
    (abelianSheafTensorComparison_naturality_right J)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution (constIntCommSheaf J)) G

/-- **The derived category of abelian sheaves on a site is monoidal**, with the monoidal structure
`Stacks.Cohomology.derivedMonoidalAbelianSheaves` built from the K-flat resolutions of
`Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves`. -/
@[instance_reducible] def derivedMonoidalAbelianSheavesOfKFlat
    [HasDerivedCategory.{v} (Sheaf J AddCommGrpCat.{u})] :
    MonoidalCategory (DerivedCategory (Sheaf J AddCommGrpCat.{u})) :=
  derivedMonoidalAbelianSheaves J (exists_kFlat_resolution_abelianSheaves J)

end Site

namespace Leray

attribute [local instance] abelianSheafMonoidalCategory

/-- **Every cochain complex of abelian sheaves on a topological space receives a
quasi-isomorphism from a K-flat one.** -/
theorem exists_kFlat_resolution_abelianSheaf (X : TopCat.{u})
    (G : CochainComplex (AbelianSheaf X) ℤ) :
    ∃ (P : CochainComplex (AbelianSheaf X) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (AbelianSheaf X)) P ∧ QuasiIso f :=
  let := hasSheafify_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  let := wEqualsLocallyBijective_ringCat.{u, u, u} (Opens.grothendieckTopology X)
  exists_kFlat_resolution_abelianSheaves (Opens.grothendieckTopology X) G

end Leray

end Stacks.Cohomology

end
