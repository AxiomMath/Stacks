module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RepresentationTheory.Rep.Iso
public import StacksFrontier.Deformation.Representation.DeformationCategory
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Dual-number module structures on self-extensions

The dual-number module structure on the middle term of a self-extension `A → B → A`, its
freeness and base-change properties, and the presentation of the kernel of a base change
along the augmentation of a square-zero extension.
-/

@[expose] public noncomputable section

open CategoryTheory
open Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

universe u w m

namespace Deformation

/-- The opposite-scalar action of a commutative ring on itself, used to form the
square-zero extension of a commutative ring by one of its own modules. -/
@[instance_reducible]
def coefficientOppositeModule {k : Type*} [CommRing k] : Module kᵐᵒᵖ k :=
  Module.compHom k {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

attribute [local instance] coefficientOppositeModule

/-- The two scalar actions of a commutative ring on itself agree. -/
theorem coefficientCentralScalar {k : Type*} [CommRing k] : IsCentralScalar k k :=
  ⟨fun _ _ ↦ rfl⟩

attribute [local instance] coefficientCentralScalar

-- The deformation category of a representation is spelled through
-- `deformationCategoryProjection` and `squareZeroExtensionRestriction`, and the module over the
-- monoid algebra through `Rep.toModuleMonoidAlgebra`, so the `Module` and `IsHomLift` instance
-- arguments of a goal about them are only found after unfolding those heads.
attribute [local implicit_reducible] Rep.equivalenceModuleMonoidAlgebra
  Rep.toModuleMonoidAlgebra deformationCategoryProjection representationProjection
  squareZeroExtensionRestriction

/-- The `ε`-coordinate of a product of dual numbers. -/
theorem dualNumber_snd_mul {k : Type*} [CommRing k] (r s : DualNumber k) :
    (r * s).snd = r.fst * s.snd + r.snd * s.fst := by
  show r.fst * s.snd + s.fst * r.snd = _
  rw [mul_comm s.fst r.snd]

/-- The dual number `ε` is square-zero. -/
theorem dualNumber_eps_mul_eps {k : Type*} [CommRing k] :
    (DualNumber.eps : DualNumber k) * DualNumber.eps = 0 := by
  apply TrivSqZeroExt.ext <;>
    simp only [TrivSqZeroExt.fst_mul, dualNumber_snd_mul,
      DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, mul_zero,
      add_zero, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero]

/-- The endomorphism `f ∘ g` of the middle term of a complex `A → B → A` whose
composite `g ∘ f` vanishes is itself square-zero. -/
lemma extensionEnd_squareZero
    {k : Type w} {A B : Type*} [CommSemiring k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0) :
    (f.comp g).comp (f.comp g) = 0 := by
  ext x
  simp only [LinearMap.comp_apply]
  have hx : g (f (g x)) = 0 := by
    have hx' := congrArg (fun q : A →ₗ[k] A => q (g x)) hgf
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hx'
  simp [hx]

/-- The middle term of a short exact sequence `A → B → A` with finite-dimensional
ends is finite-dimensional. -/
lemma extensionMiddle_finite
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [Module.Finite k A]
    [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) : Module.Finite k B := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg)
  let lift : A × A →ₗ[k] B :=
    { toFun := fun p ↦ f p.1 + s p.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro a x
        show f (a • x.1) + s (a • x.2) = a • (f x.1 + s x.2)
        rw [map_smul, map_smul, smul_add] }
  have hlift : Function.Surjective lift := by
    intro b
    let y : A := g b
    have hsy : g (s y) = y := by
      have h := congrArg (fun q : A →ₗ[k] A => q y) hs
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    have hrange : b - s y ∈ LinearMap.range f := by
      rw [hfg, LinearMap.mem_ker, map_sub, hsy]
      simp [y]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.1 hrange
    refine ⟨(x, y), ?_⟩
    dsimp [lift]
    rw [hx]
    simp
  exact Module.Finite.of_surjective lift hlift

/-- A short exact sequence `0 → A → B → A → 0` of vector spaces splits: its middle
term is linearly equivalent to `A × A`. -/
noncomputable def extensionMiddleEquiv
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A)
    (hf : Function.Injective f)
    (hgf : g.comp f = 0)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) : (A × A) ≃ₗ[k] B := by
  let s := Classical.choose (g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg))
  have hs := Classical.choose_spec (g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg))
  let lift : A × A →ₗ[k] B :=
    { toFun := fun p ↦ s p.1 + f p.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro a x
        change s (a • x.1) + f (a • x.2) = a • (s x.1 + f x.2)
        rw [map_smul, map_smul, smul_add] }
  have hsg (x : A) : g (s x) = x := by
    have h := congrArg (fun q : A →ₗ[k] A => q x) hs
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have hgf_apply (x : A) : g (f x) = 0 := by
    have h := congrArg (fun q : A →ₗ[k] A => q x) hgf
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hsurj : Function.Surjective lift := by
    intro b
    let x : A := g b
    have hrange : b - s x ∈ LinearMap.range f := by
      rw [hfg, LinearMap.mem_ker, map_sub, hsg]
      simp [x]
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hrange
    refine ⟨(x, y), ?_⟩
    dsimp [lift]
    rw [hy]
    simp
  have hinj : Function.Injective lift := by
    intro p q hpq
    have hfirst : p.1 = q.1 := by
      have h := congrArg g hpq
      change g (s p.1 + f p.2) = g (s q.1 + f q.2) at h
      rw [map_add, map_add, hsg, hsg, hgf_apply, hgf_apply] at h
      simpa using h
    have hsecond : f p.2 = f q.2 := by
      have h := congrArg (fun z : B => z - s p.1) hpq
      change (s p.1 + f p.2) - s p.1 = (s q.1 + f q.2) - s p.1 at h
      rw [hfirst] at h
      simpa only [add_sub_cancel_left] using h
    exact Prod.ext hfirst (hf hsecond)
  exact (LinearEquiv.ofBijective lift ⟨hinj, hsurj⟩ : (A × A) ≃ₗ[k] B)

/-- The dual numbers act on the middle term of a complex `A → B → A` with vanishing
composite, with `ε` acting as `f ∘ g`. -/
@[instance_reducible]
noncomputable def extensionDualNumberModule
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0) :
    Module (DualNumber k) B := by
  let N : B →ₗ[k] B := f.comp g
  have hN : N.comp N = 0 := extensionEnd_squareZero f g hgf
  refine {
    smul := fun r x => r.fst • x + r.snd • N x
    one_smul := by
      intro x
      change (1 : DualNumber k).fst • x + (1 : DualNumber k).snd • N x = x
      simp
    mul_smul := by
      intro r s x
      change (r * s).fst • x + (r * s).snd • N x =
        r.fst • (s.fst • x + s.snd • N x) + r.snd • N (s.fst • x + s.snd • N x)
      simp only [dualNumber_snd_mul, TrivSqZeroExt.fst_mul]
      simp only [smul_add, add_smul, smul_smul]
      have hn : N (N x) = 0 := by
        have hn' := congrArg (fun q : B →ₗ[k] B => q x) hN
        simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hn'
      rw [map_add, map_smul, map_smul, hn, smul_zero, add_zero]
      simp only [smul_smul]
      rw [mul_comm (r.snd) (s.fst)]
      abel
    smul_zero := by
      intro r
      change r.fst • (0 : B) + r.snd • N 0 = 0
      simp
    smul_add := by
      intro r x y
      change r.fst • (x + y) + r.snd • N (x + y) =
        (r.fst • x + r.snd • N x) + (r.fst • y + r.snd • N y)
      rw [map_add, smul_add, smul_add]
      abel
    add_smul := by
      intro r s x
      change (r + s).fst • x + (r + s).snd • N x =
        (r.fst • x + r.snd • N x) + (s.fst • x + s.snd • N x)
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul]
      abel
    zero_smul := by
      intro x
      change (0 : DualNumber k).fst • x + (0 : DualNumber k).snd • N x = 0
      simp }

/-- The dual-number action on the middle term, written out on a general scalar. -/
theorem extensionDualNumberModule_smul
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (r : DualNumber k) (x : B) :
    letI := extensionDualNumberModule f g hgf
    r • x = r.fst • x + r.snd • (f.comp g) x := rfl

/-- In the dual-number action on the middle term, `ε` acts as `f ∘ g`. -/
theorem extensionDualNumberModule_eps_smul
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0) (x : B) :
    letI := extensionDualNumberModule f g hgf
    (DualNumber.eps : DualNumber k) • x = f (g x) := by
  show (DualNumber.eps).fst • x + (DualNumber.eps).snd • (f.comp g) x = _
  simp

/-- In the dual-number action on the middle term, a scalar from the base field acts
as it does on the underlying vector space. -/
theorem extensionDualNumberModule_inl_smul
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (a : k) (x : B) :
    letI := extensionDualNumberModule f g hgf
    (TrivSqZeroExt.inl a : DualNumber k) • x = a • x := by
  show (TrivSqZeroExt.inl a).fst • x + (TrivSqZeroExt.inl a).snd • (f.comp g) x = _
  simp

/-- The middle term of a short exact sequence `A → B → A` is finite over the dual
numbers for the action in which `ε` acts as `f ∘ g`. -/
theorem extensionDualNumberModule_finite
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [Module.Finite k A]
    [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    letI := extensionDualNumberModule f g hgf
    Module.Finite (DualNumber k) B := by
  let : Module (DualNumber k) B := extensionDualNumberModule f g hgf
  let : IsScalarTower k (DualNumber k) B :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      exact extensionDualNumberModule_inl_smul f g hgf a x
  let : Module.Finite k B := extensionMiddle_finite f g hfg hg
  exact Module.Finite.of_restrictScalars_finite k (DualNumber k) B

/-- For a split short exact sequence `0 → A → B → A → 0`, the dual-number module `B`
is isomorphic to `A ⊗ k[ε]` presented as the pair `A × A`. -/
noncomputable def extensionDualNumberModuleEquiv
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (hf : Function.Injective f)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g)
    (h0 : (LinearMap.fst k A A).comp (LinearMap.inr k A A) = 0) :
    letI := extensionDualNumberModule f g hgf
    letI := extensionDualNumberModule (LinearMap.inr k A A)
      (LinearMap.fst k A A) h0
    (A × A) ≃ₗ[DualNumber k] B := by
  letI := extensionDualNumberModule f g hgf
  letI := extensionDualNumberModule (LinearMap.inr k A A)
    (LinearMap.fst k A A) h0
  let s := Classical.choose (g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg))
  have hs := Classical.choose_spec (g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hg))
  have hsg (x : A) : g (s x) = x := by
    have h := congrArg (fun q : A →ₗ[k] A => q x) hs
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have hgf_apply (x : A) : g (f x) = 0 := by
    have h := congrArg (fun q : A →ₗ[k] A => q x) hgf
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  let lift : (A × A) →ₗ[DualNumber k] B :=
    { toFun := fun p ↦ s p.1 + f p.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro r p
        change s (r • p).1 + f (r • p).2 = r • (s p.1 + f p.2)
        rw [extensionDualNumberModule_smul f g hgf r (s p.1 + f p.2),
          extensionDualNumberModule_smul (LinearMap.inr k A A)
            (LinearMap.fst k A A) h0 r p]
        simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.fst_apply,
          Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_zero, add_zero]
        change s (r.fst • p.1) + f (r.fst • p.2 + r.snd • p.1) =
          r.fst • (s p.1 + f p.2) + r.snd • f (g (s p.1 + f p.2))
        simp only [map_add, map_smul, hsg, hgf_apply, smul_add, add_zero]
        abel }
  have hsurj : Function.Surjective lift := by
    intro b
    let x : A := g b
    have hrange : b - s x ∈ LinearMap.range f := by
      rw [hfg, LinearMap.mem_ker, map_sub, hsg]
      simp [x]
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hrange
    refine ⟨(x, y), ?_⟩
    change s x + f y = b
    rw [hy]
    simp
  have hinj : Function.Injective lift := by
    intro p q hpq
    have hfirst : p.1 = q.1 := by
      have h := congrArg g hpq
      change g (s p.1 + f p.2) = g (s q.1 + f q.2) at h
      rw [map_add, map_add, hsg, hsg, hgf_apply, hgf_apply] at h
      simpa using h
    have hsecond : f p.2 = f q.2 := by
      have h := congrArg (fun z : B => z - s p.1) hpq
      change (s p.1 + f p.2) - s p.1 = (s q.1 + f q.2) - s p.1 at h
      rw [hfirst] at h
      simpa only [add_sub_cancel_left] using h
    exact Prod.ext hfirst (hf hsecond)
  exact LinearEquiv.ofBijective lift ⟨hinj, hsurj⟩

/-- The comparison map from the dual-number module `A × A` to the base change of `A`
along the inclusion of the base field into the dual numbers. -/
noncomputable def extensionPairTensorMap
    {k : Type w} {A : Type*} [Field k]
    [AddCommGroup A] [Module k A]
    (h0 : (LinearMap.fst k A A).comp (LinearMap.inr k A A) = 0) :
    letI := extensionDualNumberModule (LinearMap.inr k A A)
      (LinearMap.fst k A A) h0
    (TensorProduct k (DualNumber k) A) →ₗ[DualNumber k] (A × A) := by
  letI := extensionDualNumberModule (LinearMap.inr k A A)
    (LinearMap.fst k A A) h0
  letI : IsScalarTower k (DualNumber k) (A × A) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      exact extensionDualNumberModule_inl_smul _ _ h0 a x
  letI : SMulCommClass (DualNumber k) k (A × A) :=
    SMulCommClass.symm k (DualNumber k) (A × A)
  let bilinear : DualNumber k →ₗ[DualNumber k] A →ₗ[k] (A × A) :=
    { toFun := fun r =>
        { toFun := fun x => (r.fst • x, r.snd • x)
          map_add' := by intro x y; ext <;> simp [smul_add]
          map_smul' := by
            intro a x
            apply Prod.ext <;> exact smul_comm _ _ _ }
      map_add' := by
        intro r s
        ext x <;> simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul]
      map_smul' := by
        intro c r
        apply LinearMap.ext
        intro x
        change ((c * r).fst • x, (c * r).snd • x) =
          c • (r.fst • x, r.snd • x)
        rw [extensionDualNumberModule_smul (LinearMap.inr k A A)
          (LinearMap.fst k A A) h0 c (r.fst • x, r.snd • x)]
        apply Prod.ext <;>
          simp only [TrivSqZeroExt.fst_mul, dualNumber_snd_mul,
            LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inr_apply,
            Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            smul_zero, add_zero, add_smul, ← mul_smul, mul_comm] }
  exact TensorProduct.AlgebraTensorModule.lift bilinear

/-- The comparison map of `extensionPairTensorMap` is an isomorphism: `A × A` with the
`ε`-action by the second inclusion is the free dual-number module on `A`. -/
noncomputable def extensionPairTensorEquiv
    {k : Type w} {A : Type*} [Field k]
    [AddCommGroup A] [Module k A]
    (h0 : (LinearMap.fst k A A).comp (LinearMap.inr k A A) = 0) :
    letI := extensionDualNumberModule (LinearMap.inr k A A)
      (LinearMap.fst k A A) h0
    (TensorProduct k (DualNumber k) A) ≃ₗ[DualNumber k] (A × A) := by
  letI := extensionDualNumberModule (LinearMap.inr k A A)
    (LinearMap.fst k A A) h0
  let e : TensorProduct k (DualNumber k) A ≃ₗ[k] A × A :=
    (TensorProduct.prodLeft k k k k A).trans
      ((TensorProduct.lid k A).prodCongr (TensorProduct.lid k A))
  have hmap : ⇑(extensionPairTensorMap h0) = ⇑e := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a =>
      change (r.fst • a, r.snd • a) = e (r ⊗ₜ[k] a)
      rcases r with ⟨r, s⟩
      rfl
  exact LinearEquiv.ofBijective (extensionPairTensorMap h0) (hmap ▸ e.bijective)

/-- The middle term of a split short exact sequence `A → B → A` is free over the dual
numbers for the action in which `ε` acts as `f ∘ g`. -/
theorem extensionDualNumberModule_free
    {k : Type w} {A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (hf : Function.Injective f)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    letI := extensionDualNumberModule f g hgf
    Module.Free (DualNumber k) B := by
  let := extensionDualNumberModule f g hgf
  have h0 : (LinearMap.fst k A A).comp (LinearMap.inr k A A) = 0 := by ext; rfl
  exact Module.Free.of_equiv ((extensionPairTensorEquiv h0).trans
    (extensionDualNumberModuleEquiv f g hgf hf hfg hg h0))

/-- The quotient map of a short exact sequence `A → B → A` exhibits `A` as the base
change of the dual-number module `B` along the augmentation to the base field. -/
theorem extensionDualNumberModule_isBaseChange
    {k A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [Algebra (DualNumber k) k] [Module (DualNumber k) A]
    [IsScalarTower (DualNumber k) k A]
    (hmap : ∀ r : DualNumber k, algebraMap (DualNumber k) k r = r.fst)
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (hfg : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g)
    (gd : letI := extensionDualNumberModule f g hgf; B →ₗ[DualNumber k] A)
    (hgd : ∀ x, gd x = g x) :
    letI := extensionDualNumberModule f g hgf
    IsBaseChange k gd := by
  let := extensionDualNumberModule f g hgf
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have hgs (x : A) : g (s x) = x := LinearMap.congr_fun hs x
  apply IsBaseChange.iff_lift_unique.2
  intro Q _ _ _ _ h
  have hscalar (r : DualNumber k) (z : Q) : r • z = r.fst • z := by
    rw [← IsScalarTower.algebraMap_smul k, hmap]
  let hk : B →ₗ[k] Q :=
    { h.toAddHom with
      map_smul' := fun a x ↦ by
        show h (a • x) = a • h x
        rw [← extensionDualNumberModule_inl_smul f g hgf a x, map_smul,
          hscalar, TrivSqZeroExt.fst_inl] }
  have hkill (v : A) : h (f v) = 0 := by
    obtain ⟨z, rfl⟩ := hg v
    rw [← extensionDualNumberModule_eps_smul f g hgf, map_smul, hscalar,
      DualNumber.fst_eps, zero_smul]
  have hcomp (x : B) : hk (s (g x)) = h x := by
    have hx : x - s (g x) ∈ LinearMap.range f := by
      rw [hfg, LinearMap.mem_ker, map_sub, hgs, sub_self]
    obtain ⟨v, hv⟩ := hx
    have heq : x = s (g x) + f v := by rw [hv]; abel
    conv_rhs => rw [heq, map_add, hkill, add_zero]
    rfl
  refine ⟨hk.comp s, ?_, ?_⟩
  · ext x
    exact (congrArg (fun a ↦ hk (s a)) (hgd x)).trans (hcomp x)
  · intro l hl
    ext v
    obtain ⟨z, rfl⟩ := hg v
    have hh := LinearMap.congr_fun hl z
    change l (gd z) = h z at hh
    rw [hgd] at hh
    exact hh.trans (hcomp z).symm

/-- If `f` and `g` are equivariant then so is the square-zero endomorphism `f ∘ g` of
the middle term. -/
theorem extensionEnd_commutes_with_representation
    {k : Type w} {Γ A B : Type*} [Field k] [Group Γ]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (ρA : Representation k Γ A) (ρB : Representation k Γ B)
    (f : A →ₗ[k] B) (g : B →ₗ[k] A)
    (hf : ∀ γ, f.comp (ρA γ) = (ρB γ).comp f)
    (hg : ∀ γ, g.comp (ρB γ) = (ρA γ).comp g) :
    ∀ γ, (f.comp g).comp (ρB γ) = (ρB γ).comp (f.comp g) := by
  intro γ
  rw [LinearMap.comp_assoc, hg γ, ← LinearMap.comp_assoc,
    hf γ, LinearMap.comp_assoc]

/-- The representation on the middle term of an equivariant short exact sequence
`A → B → A`, viewed as a representation over the dual numbers. -/
noncomputable def extensionLiftedRepresentation
    {k : Type w} {Γ A B : Type*} [Field k] [Group Γ]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (ρA : Representation k Γ A) (ρB : Representation k Γ B)
    (f : A →ₗ[k] B) (g : B →ₗ[k] A) (hgf : g.comp f = 0)
    (hf : ∀ γ, f.comp (ρA γ) = (ρB γ).comp f)
    (hg : ∀ γ, g.comp (ρB γ) = (ρA γ).comp g) :
    letI := extensionDualNumberModule f g hgf
    Representation (DualNumber k) Γ B := by
  let N : B →ₗ[k] B := f.comp g
  have hN := extensionEnd_commutes_with_representation ρA ρB f g hf hg
  letI := extensionDualNumberModule f g hgf
  refine {
    toFun := fun γ =>
      { toFun := ρB γ
        map_add' := (ρB γ).map_add
        map_smul' := ?_ }
    map_one' := ?_
    map_mul' := ?_ }
  · intro r x
    change ρB γ (r.fst • x + r.snd • N x) =
      r.fst • ρB γ x + r.snd • N (ρB γ x)
    have hcomm : N (ρB γ x) = ρB γ (N x) := by
      have hcomm' := congrArg (fun q : B →ₗ[k] B => q x) (hN γ)
      simpa only [N, LinearMap.comp_apply] using hcomm'
    rw [map_add, map_smul, map_smul, hcomm]
  · ext x
    simp
  · intro γ δ
    ext x
    simp

/-- A base change along the augmentation of a square-zero extension is surjective. -/
theorem squareZero_baseChange_surjective
    {k W M N ι : Type*} [CommRing k]
    [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]
    [AddCommGroup M] [Module (TrivSqZeroExt k W) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k W) k] [Module (TrivSqZeroExt k W) N]
    [IsScalarTower (TrivSqZeroExt k W) k N]
    (hmap : ∀ r : TrivSqZeroExt k W,
      algebraMap (TrivSqZeroExt k W) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k W) M)
    (g : M →ₗ[TrivSqZeroExt k W] N) (hg : IsBaseChange k g) :
    Function.Surjective g := by
  intro v
  let c := hg.basis b
  let z : ι →₀ TrivSqZeroExt k W :=
    (c.repr v).mapRange TrivSqZeroExt.inl (by simp)
  refine ⟨b.repr.symm z, c.repr.injective ?_⟩
  ext i
  rw [hg.basis_repr_comp_apply]
  simp only [LinearEquiv.apply_symm_apply, hmap, z]
  rfl

/-- An element of a free module over a square-zero extension dies in the base change
along the augmentation exactly when every coordinate is in the square-zero ideal. -/
theorem squareZero_baseChange_ker_iff
    {k W M N ι : Type*} [CommRing k]
    [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]
    [AddCommGroup M] [Module (TrivSqZeroExt k W) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k W) k] [Module (TrivSqZeroExt k W) N]
    [IsScalarTower (TrivSqZeroExt k W) k N]
    (hmap : ∀ r : TrivSqZeroExt k W,
      algebraMap (TrivSqZeroExt k W) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k W) M)
    (g : M →ₗ[TrivSqZeroExt k W] N) (hg : IsBaseChange k g) (x : M) :
    g x = 0 ↔ ∀ i, (b.repr x i).fst = 0 := by
  rw [← (hg.basis b).repr.map_eq_zero_iff]
  simp only [Finsupp.ext_iff, Finsupp.zero_apply, hg.basis_repr_comp_apply, hmap]

/-- For the square-zero extension by the rank-two module `k × k`, the kernel of the
base change along the augmentation is spanned by the two coordinate radicals. -/
theorem squareZero_pair_baseChange_exact
    {k M N ι : Type*} [Field k]
    [AddCommGroup M] [Module (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k (k × k)) k]
    [Module (TrivSqZeroExt k (k × k)) N]
    [IsScalarTower (TrivSqZeroExt k (k × k)) k N]
    (hmap : ∀ r : TrivSqZeroExt k (k × k),
      algebraMap (TrivSqZeroExt k (k × k)) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k (k × k)) M)
    (g : M →ₗ[TrivSqZeroExt k (k × k)] N) (hg : IsBaseChange k g)
    (x : M) :
    g x = 0 ↔ ∃ y z : M,
      (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • y +
        (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • z = x := by
  rw [squareZero_baseChange_ker_iff hmap b g hg]
  constructor
  · intro hx
    let y : ι →₀ TrivSqZeroExt k (k × k) :=
      (b.repr x).mapRange (fun r ↦ TrivSqZeroExt.inl r.snd.1) (by simp)
    let z : ι →₀ TrivSqZeroExt k (k × k) :=
      (b.repr x).mapRange (fun r ↦ TrivSqZeroExt.inl r.snd.2) (by simp)
    refine ⟨b.repr.symm y, b.repr.symm z, b.repr.injective ?_⟩
    ext i
    all_goals simp [y, z, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx i]
    all_goals rfl
  · rintro ⟨y, z, rfl⟩ i
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_inr, zero_mul, add_zero]

/-- The two coordinate radicals of the rank-two square-zero extension act
independently: a vanishing combination of them forces both terms into the kernel. -/
theorem squareZero_pair_radical_independent
    {k M N ι : Type*} [Field k]
    [AddCommGroup M] [Module (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k (k × k)) k]
    [Module (TrivSqZeroExt k (k × k)) N]
    [IsScalarTower (TrivSqZeroExt k (k × k)) k N]
    (hmap : ∀ r : TrivSqZeroExt k (k × k),
      algebraMap (TrivSqZeroExt k (k × k)) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k (k × k)) M)
    (g : M →ₗ[TrivSqZeroExt k (k × k)] N) (hg : IsBaseChange k g)
    (x y : M)
    (h : (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • x +
      (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • y = 0) :
    g x = 0 ∧ g y = 0 := by
  rw [squareZero_baseChange_ker_iff hmap b g hg,
    squareZero_baseChange_ker_iff hmap b g hg]
  constructor <;> intro i
  · have hi := congrArg (fun z : M ↦ ((b.repr z) i).snd.1) h
    simpa [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul] using hi
  · have hi := congrArg (fun z : M ↦ ((b.repr z) i).snd.2) h
    simpa [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul] using hi

/-- Each coordinate radical of the rank-two square-zero extension annihilates the
kernel of the base change along the augmentation. -/
theorem squareZero_pair_radical_annihilates_kernel
    {k M N ι : Type*} [Field k]
    [AddCommGroup M] [Module (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k (k × k)) k]
    [Module (TrivSqZeroExt k (k × k)) N]
    [IsScalarTower (TrivSqZeroExt k (k × k)) k N]
    (hmap : ∀ r : TrivSqZeroExt k (k × k),
      algebraMap (TrivSqZeroExt k (k × k)) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k (k × k)) M)
    (g : M →ₗ[TrivSqZeroExt k (k × k)] N) (hg : IsBaseChange k g)
    (x : M) (hx : g x = 0) :
    (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • x = 0 ∧
      (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • x = 0 := by
  obtain ⟨y, z, h⟩ := (squareZero_pair_baseChange_exact hmap b g hg x).1 hx
  rw [← h]
  constructor <;> simp [smul_add, smul_smul, TrivSqZeroExt.inr_mul_inr]

/-- For a free module over the rank-two square-zero extension, the kernel of the base
change along the augmentation is a pair of copies of the base change, exhibited by
an explicit injection with a section. -/
theorem exists_squareZero_pair_kernelMap
    {k M N ι : Type*} [Field k]
    [AddCommGroup M] [Module (TrivSqZeroExt k (k × k)) M] [Module k M]
    [SMulCommClass k (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k (k × k)) k]
    [Module (TrivSqZeroExt k (k × k)) N]
    [IsScalarTower (TrivSqZeroExt k (k × k)) k N]
    (hmap : ∀ r : TrivSqZeroExt k (k × k),
      algebraMap (TrivSqZeroExt k (k × k)) k r = r.fst)
    (b : Module.Basis ι (TrivSqZeroExt k (k × k)) M)
    (g : M →ₗ[TrivSqZeroExt k (k × k)] N) (hg : IsBaseChange k g)
    (gk : M →ₗ[k] N) (hgk : ∀ x, gk x = g x) :
    ∃ f : (N × N) →ₗ[k] M,
      Function.Injective f ∧ LinearMap.range f = LinearMap.ker gk ∧
        ∃ s : N →ₗ[k] M, (∀ v, gk (s v) = v) ∧
          ∀ v : N × N, f v =
            (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • s v.1 +
              (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • s v.2 := by
  have hsurj : Function.Surjective gk := by
    intro v
    obtain ⟨x, hx⟩ := squareZero_baseChange_surjective hmap b g hg v
    exact ⟨x, (hgk x).trans hx⟩
  obtain ⟨s, hs⟩ := gk.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurj)
  have hgs (v : N) : gk (s v) = v := LinearMap.congr_fun hs v
  let j₁ : M →ₗ[k] M :=
    { toFun := fun x ↦ (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • x
      map_add' := smul_add _
      map_smul' := fun a x ↦
        (smul_comm a (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) x).symm }
  let j₂ : M →ₗ[k] M :=
    { toFun := fun x ↦ (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • x
      map_add' := smul_add _
      map_smul' := fun a x ↦
        (smul_comm a (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) x).symm }
  let f : (N × N) →ₗ[k] M :=
    j₁.comp (s.comp (LinearMap.fst k N N)) +
      j₂.comp (s.comp (LinearMap.snd k N N))
  have hf (v : N × N) : f v = j₁ (s v.1) + j₂ (s v.2) := rfl
  refine ⟨f, ?_, ?_, s, hgs, hf⟩
  · apply (LinearMap.ker_eq_bot).1
    apply LinearMap.ker_eq_bot'.2
    intro v hv
    have hv' : j₁ (s v.1) + j₂ (s v.2) = 0 := (hf v).symm.trans hv
    obtain ⟨h₁, h₂⟩ := squareZero_pair_radical_independent hmap b g hg _ _ hv'
    apply Prod.ext
    · exact (hgs v.1).symm.trans ((hgk _).trans h₁)
    · exact (hgs v.2).symm.trans ((hgk _).trans h₂)
  · apply le_antisymm
    · rintro x ⟨v, rfl⟩
      apply LinearMap.mem_ker.2
      rw [hgk, hf]
      show g ((TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • s v.1 +
        (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • s v.2) = 0
      rw [map_add, map_smul, map_smul]
      have hscalar (r : TrivSqZeroExt k (k × k)) (z : N) : r • z = r.fst • z := by
        rw [← IsScalarTower.algebraMap_smul k, hmap]
      rw [hscalar, hscalar]
      simp
    · intro x hx
      have hxg : g x = 0 := (hgk x).symm.trans (LinearMap.mem_ker.1 hx)
      obtain ⟨y, z, h⟩ := (squareZero_pair_baseChange_exact hmap b g hg x).1 hxg
      have hker (w : M) : g (w - s (gk w)) = 0 := by
        rw [← hgk, map_sub, hgs, sub_self]
      have key (j : M →ₗ[k] M) (w : M) (h : j (w - s (gk w)) = 0) : j (s (gk w)) = j w := by
        rw [map_sub, sub_eq_zero] at h
        exact h.symm
      have hjy := key j₁ y
        (squareZero_pair_radical_annihilates_kernel hmap b g hg _ (hker y)).1
      have hjz := key j₂ z
        (squareZero_pair_radical_annihilates_kernel hmap b g hg _ (hker z)).2
      refine ⟨(gk y, gk z), ?_⟩
      rw [hf]
      show j₁ (s (gk y)) + j₂ (s (gk z)) = x
      rw [hjy, hjz]
      exact h

/-- The pair presentation of the kernel is natural in an endomorphism lying over an
endomorphism of the base change. -/
theorem squareZero_pair_kernelMap_equivariant
    {k M N ι : Type*} [Field k]
    [AddCommGroup M] [Module (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup N] [Module k N]
    [Algebra (TrivSqZeroExt k (k × k)) k]
    [Module (TrivSqZeroExt k (k × k)) N]
    [IsScalarTower (TrivSqZeroExt k (k × k)) k N]
    (hmap : ∀ r : TrivSqZeroExt k (k × k),
      algebraMap (TrivSqZeroExt k (k × k)) k r = r.fst)
    (basis : Module.Basis ι (TrivSqZeroExt k (k × k)) M)
    (g : M →ₗ[TrivSqZeroExt k (k × k)] N) (hg : IsBaseChange k g)
    (s : N →+ M) (hs : ∀ v, g (s v) = v)
    (a : M →ₗ[TrivSqZeroExt k (k × k)] M) (b : N →+ N)
    (hab : ∀ x, g (a x) = b (g x)) (v : N × N) :
    a ((TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • s v.1 +
      (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • s v.2) =
      (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • s (b v.1) +
        (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • s (b v.2) := by
  have hker (u : N) : g (a (s u) - s (b u)) = 0 := by
    rw [map_sub, hab, hs, hs, sub_self]
  have he (u : N) (c : TrivSqZeroExt k (k × k)) (hc : c • (a (s u) - s (b u)) = 0) :
      c • a (s u) = c • s (b u) := by
    rwa [smul_sub, sub_eq_zero] at hc
  rw [map_add, map_smul, map_smul,
    he v.1 _ (squareZero_pair_radical_annihilates_kernel hmap basis g hg _ (hker v.1)).1,
    he v.2 _ (squareZero_pair_radical_annihilates_kernel hmap basis g hg _ (hker v.2)).2]

/-- The pair presentation of the kernel is compatible with a map to a dual-number
module that collapses the two coordinates by prescribed scalars. -/
theorem squareZero_pair_kernelMap_naturality
    {k M M' V : Type*} [Field k]
    [AddCommGroup M] [Module k M] [Module (TrivSqZeroExt k (k × k)) M]
    [AddCommGroup M'] [Module k M'] [Module (DualNumber k) M']
    [AddCommGroup V] [Module k V]
    (g : M →ₗ[k] V) (g' : M' →ₗ[k] V)
    (s : V →ₗ[k] M) (hs : ∀ v, g (s v) = v)
    (f : (V × V) →ₗ[k] M)
    (hf : ∀ v, f v =
      (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k)) • s v.1 +
        (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k)) • s v.2)
    (f' : V →ₗ[k] M')
    (hf' : ∀ z, f' (g' z) = (DualNumber.eps : DualNumber k) • z)
    (l : M →ₗ[k] M') (hlg : ∀ z, g' (l z) = g z)
    (a b : k)
    (hl₁ : ∀ z, l ((TrivSqZeroExt.inr (1, 0) :
      TrivSqZeroExt k (k × k)) • z) = a • ((DualNumber.eps : DualNumber k) • l z))
    (hl₂ : ∀ z, l ((TrivSqZeroExt.inr (0, 1) :
      TrivSqZeroExt k (k × k)) • z) = b • ((DualNumber.eps : DualNumber k) • l z))
    (v : V × V) : l (f v) = f' (a • v.1 + b • v.2) := by
  calc
    l (f v) = a • ((DualNumber.eps : DualNumber k) • l (s v.1)) +
        b • ((DualNumber.eps : DualNumber k) • l (s v.2)) := by
          rw [hf, map_add, hl₁, hl₂]
    _ = a • f' (g' (l (s v.1))) + b • f' (g' (l (s v.2))) := by
          rw [hf', hf']
    _ = f' (a • v.1 + b • v.2) := by
          rw [hlg, hlg, hs, hs, map_add, map_smul, map_smul]

end Deformation
