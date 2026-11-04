module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Blowup.Basic

/-!
# Strict transform of a module along an affine blowup

The strict transform of a module along the affine blowup algebra `R[I/a]` is the base change with
its `a`-power torsion removed.

## Main definitions

* `strictTransform I a M`: the strict transform of an `R`-module `M`, a module over `R[I/a]`.
* `strictTransformIdeal I a S`: for a commutative `R`-algebra `S`, the ideal of `R[I/a] ⊗[R] S`
  consisting of the elements killed by a power of the image of `a`; its carrier is the one used in
  the definition of `strictTransform I a S`.
* `strictTransformAlg I a S`: the strict transform of `S`, as an `R[I/a]`-algebra, namely the
  quotient of `R[I/a] ⊗[R] S` by `strictTransformIdeal I a S`.
* `strictTransformAlg.linearEquivStrictTransform`: the identification of `strictTransformAlg I a S`
  with `strictTransform I a S` as `R[I/a]`-modules, which transfers module-level results about the
  strict transform to the algebra.
* `strictTransform.instModuleStrictTransformAlg`: for an `S`-module `M`, the strict transform of
  `M` is a module over `strictTransformAlg I a S`.

## References

* [Stacks Project, Tag 0535](https://stacks.math.columbia.edu/tag/0535)
-/

@[expose] public section

universe u v w

section  -- tag 053H
variable {R : Type u} [CommRing R]

/-- The strict transform of an `R`-module `M` along the affine blowup algebra `R → R[I/a]`:
the scalar extension `R[I/a] ⊗[R] M`, modulo the elements annihilated by some power of the
image of `a`. -/
@[stacks 053H]
noncomputable def strictTransform (I : Ideal R) (a : R) [Fact (a ∈ I)]
    (M : Type v) [AddCommGroup M] [Module R M] :=
  (TensorProduct R (Blowup I a) M) ⧸
    Submodule.torsion' (Blowup I a) (TensorProduct R (Blowup I a) M)
      (Submonoid.powers (algebraMap R (Blowup I a) a))

/-- The strict transform is an additive commutative group. -/
noncomputable instance strictTransform.instAddCommGroup (I : Ideal R) (a : R)
    [Fact (a ∈ I)] (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (strictTransform I a M) := by
  unfold strictTransform
  infer_instance

/-- The strict transform is a module over the affine blowup algebra `R[I/a]`. -/
noncomputable instance strictTransform.instModule (I : Ideal R) (a : R)
    [Fact (a ∈ I)] (M : Type v) [AddCommGroup M] [Module R M] :
    Module (Blowup I a) (strictTransform I a M) := by
  unfold strictTransform
  infer_instance

/-- The strict transform is a module over the base ring `R`, being a quotient of the scalar
extension. -/
noncomputable instance strictTransform.instModuleBase (I : Ideal R) (a : R)
    [Fact (a ∈ I)] (M : Type v) [AddCommGroup M] [Module R M] :
    Module R (strictTransform I a M) := by
  unfold strictTransform
  infer_instance

/-- The action of `R[I/a]` on the strict transform extends that of `R`. -/
instance strictTransform.instIsScalarTowerBase (I : Ideal R) (a : R)
    [Fact (a ∈ I)] (M : Type v) [AddCommGroup M] [Module R M] :
    IsScalarTower R (Blowup I a) (strictTransform I a M) := by
  unfold strictTransform
  infer_instance

/-- The canonical map from the scalar extension to its strict transform. -/
noncomputable def strictTransform.mkQ (I : Ideal R) (a : R) [Fact (a ∈ I)]
    (M : Type v) [AddCommGroup M] [Module R M] :
    TensorProduct R (Blowup I a) M →ₗ[Blowup I a] strictTransform I a M := by
  unfold strictTransform
  exact Submodule.mkQ _

/-- The canonical map to the strict transform is surjective. -/
theorem strictTransform.mkQ_surjective (I : Ideal R) (a : R) [Fact (a ∈ I)]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Surjective (strictTransform.mkQ I a M) :=
  Submodule.mkQ_surjective _

end

section StrictTransformAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)]
  (S : Type v) [CommRing S] [Algebra R S]

/-- The submodule of `a`-power torsion elements of the scalar extension `R[I/a] ⊗[R] M`, that is,
the submodule by which `strictTransform I a M` is the quotient. -/
noncomputable def strictTransform.torsionSubmodule (M : Type w) [AddCommGroup M] [Module R M] :
    Submodule (Blowup I a) (TensorProduct R (Blowup I a) M) :=
  Submodule.torsion' (Blowup I a) (TensorProduct R (Blowup I a) M)
    (Submonoid.powers (algebraMap R (Blowup I a) a))

/-- An element of the scalar extension is `a`-power torsion exactly when some power of the image
of `a` kills it. -/
theorem strictTransform.mem_torsionSubmodule_iff (M : Type w) [AddCommGroup M] [Module R M]
    {x : TensorProduct R (Blowup I a) M} :
    x ∈ strictTransform.torsionSubmodule I a M ↔
      ∃ n : ℕ, (algebraMap R (Blowup I a) a) ^ n • x = 0 := by
  constructor
  · rintro ⟨⟨_, n, rfl⟩, h⟩
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨⟨_, n, rfl⟩, h⟩

/-- The ideal of `a`-power torsion elements of the base change `R[I/a] ⊗[R] S` of a commutative
`R`-algebra `S`, that is, of the elements killed by some power of the image of `a`.

Its carrier is by definition the carrier of the `a`-power torsion submodule occurring in
`strictTransform I a S`; it is an ideal because the scalar action of `R[I/a]` commutes with
multiplication. -/
noncomputable def strictTransformIdeal : Ideal (TensorProduct R (Blowup I a) S) :=
  { strictTransform.torsionSubmodule I a S with
    smul_mem' := fun c x hx => by
      obtain ⟨n, hn⟩ := (strictTransform.mem_torsionSubmodule_iff I a S).mp hx
      refine (strictTransform.mem_torsionSubmodule_iff I a S).mpr ⟨n, ?_⟩
      rw [smul_comm, hn, smul_zero] }

/-- The ideal `strictTransformIdeal I a S` has the same elements as the `a`-power torsion submodule
used to define the strict transform of `S` as a module. -/
theorem mem_strictTransformIdeal_iff_mem_torsionSubmodule
    {x : TensorProduct R (Blowup I a) S} :
    x ∈ strictTransformIdeal I a S ↔ x ∈ strictTransform.torsionSubmodule I a S :=
  Iff.rfl

/-- Membership in `strictTransformIdeal I a S` means being killed by a power of the image of
`a`. -/
theorem mem_strictTransformIdeal_iff {x : TensorProduct R (Blowup I a) S} :
    x ∈ strictTransformIdeal I a S ↔
      ∃ n : ℕ, (algebraMap R (Blowup I a) a) ^ n • x = 0 :=
  strictTransform.mem_torsionSubmodule_iff I a S

/-- The strict transform of a commutative `R`-algebra `S` along the affine blowup algebra
`R → R[I/a]`, as a ring: the scalar extension `R[I/a] ⊗[R] S` modulo the ideal of elements
annihilated by some power of the image of `a`. -/
noncomputable def strictTransformAlg :=
  (TensorProduct R (Blowup I a) S) ⧸ strictTransformIdeal I a S

/-- The strict transform algebra is a commutative ring, being a quotient of the commutative ring
`R[I/a] ⊗[R] S`. -/
noncomputable instance strictTransformAlg.instCommRing : CommRing (strictTransformAlg I a S) :=
  inferInstanceAs
    (CommRing ((TensorProduct R (Blowup I a) S) ⧸ strictTransformIdeal I a S))

/-- The strict transform algebra is an `R[I/a]`-algebra. -/
noncomputable instance strictTransformAlg.instAlgebraBlowup :
    Algebra (Blowup I a) (strictTransformAlg I a S) :=
  inferInstanceAs
    (Algebra (Blowup I a) ((TensorProduct R (Blowup I a) S) ⧸ strictTransformIdeal I a S))

/-- The strict transform algebra is an `R`-algebra. -/
noncomputable instance strictTransformAlg.instAlgebra : Algebra R (strictTransformAlg I a S) :=
  inferInstanceAs
    (Algebra R ((TensorProduct R (Blowup I a) S) ⧸ strictTransformIdeal I a S))

/-- The `R`-algebra structure on the strict transform algebra is the one induced from
`R[I/a]`. -/
instance strictTransformAlg.instIsScalarTower :
    IsScalarTower R (Blowup I a) (strictTransformAlg I a S) :=
  inferInstanceAs
    (IsScalarTower R (Blowup I a)
      ((TensorProduct R (Blowup I a) S) ⧸ strictTransformIdeal I a S))

/-- The quotient map from the scalar extension to the strict transform algebra. -/
noncomputable def strictTransformAlg.mk :
    TensorProduct R (Blowup I a) S →ₐ[Blowup I a] strictTransformAlg I a S :=
  Ideal.Quotient.mkₐ (Blowup I a) (strictTransformIdeal I a S)

/-- The quotient map to the strict transform algebra is surjective. -/
theorem strictTransformAlg.mk_surjective :
    Function.Surjective (strictTransformAlg.mk I a S) :=
  Ideal.Quotient.mk_surjective

/-- Two elements of the scalar extension have the same class in the strict transform algebra
exactly when their difference is `a`-power torsion. -/
theorem strictTransformAlg.mk_eq_mk_iff {x y : TensorProduct R (Blowup I a) S} :
    strictTransformAlg.mk I a S x = strictTransformAlg.mk I a S y ↔
      x - y ∈ strictTransformIdeal I a S :=
  Submodule.Quotient.eq _

/-- The class of `x` in the strict transform algebra vanishes exactly when `x` is `a`-power
torsion. -/
theorem strictTransformAlg.mk_eq_zero_iff {x : TensorProduct R (Blowup I a) S} :
    strictTransformAlg.mk I a S x = 0 ↔ x ∈ strictTransformIdeal I a S :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The `R[I/a]`-linear map from the strict transform of `S` as a module to the strict transform
algebra, sending the class of `x` to the class of `x`. -/
noncomputable def strictTransformAlg.ofStrictTransform :
    strictTransform I a S →ₗ[Blowup I a] strictTransformAlg I a S :=
  Submodule.liftQ (strictTransform.torsionSubmodule I a S)
    (strictTransformAlg.mk I a S).toLinearMap fun _ hx =>
      (strictTransformAlg.mk_eq_zero_iff I a S).mpr
        ((mem_strictTransformIdeal_iff_mem_torsionSubmodule I a S).mpr hx)

/-- The comparison map sends the class of `x` in the strict transform to the class of `x` in the
strict transform algebra. -/
@[simp]
theorem strictTransformAlg.ofStrictTransform_mkQ (x : TensorProduct R (Blowup I a) S) :
    strictTransformAlg.ofStrictTransform I a S (strictTransform.mkQ I a S x) =
      strictTransformAlg.mk I a S x :=
  rfl

/-- The strict transform algebra of `S` and the strict transform of `S` as a module are quotients
of `R[I/a] ⊗[R] S` by the same set of elements, hence are identified as `R[I/a]`-modules. -/
noncomputable def strictTransformAlg.linearEquivStrictTransform :
    strictTransformAlg I a S ≃ₗ[Blowup I a] strictTransform I a S :=
  (LinearEquiv.ofBijective (strictTransformAlg.ofStrictTransform I a S)
    ⟨fun u v huv => by
      obtain ⟨x, rfl⟩ := strictTransform.mkQ_surjective I a S u
      obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a S v
      rw [strictTransformAlg.ofStrictTransform_mkQ, strictTransformAlg.ofStrictTransform_mkQ,
        strictTransformAlg.mk_eq_mk_iff] at huv
      exact (Submodule.Quotient.eq _).mpr
        ((mem_strictTransformIdeal_iff_mem_torsionSubmodule I a S).mp huv),
      fun z => by
      obtain ⟨x, rfl⟩ := strictTransformAlg.mk_surjective I a S z
      exact ⟨strictTransform.mkQ I a S x, rfl⟩⟩).symm

section ModuleAction

variable (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The action of the scalar extension `R[I/a] ⊗[R] S` on the scalar extension `R[I/a] ⊗[R] M` of
an `S`-module `M`, as an `R`-algebra map to the endomorphism ring: the element `b ⊗ s` acts by
multiplication by `b` on the left factor and through the action of `s` on `M`. -/
noncomputable def strictTransform.baseChangeEnd :
    TensorProduct R (Blowup I a) S →ₐ[R] Module.End R (TensorProduct R (Blowup I a) M) :=
  Algebra.TensorProduct.lift (Algebra.lsmul R R (TensorProduct R (Blowup I a) M))
    ((Module.End.lTensorAlgHom R M (Blowup I a)).comp (Algebra.lsmul R R M))
    fun b s => LinearMap.ext fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c m => simp [TensorProduct.smul_tmul', TensorProduct.liftAux_tmul]
      | add u v hu hv =>
        simp only [Module.End.mul_apply, map_add] at hu hv ⊢
        rw [hu, hv]

/-- The endomorphism attached to `b ⊗ s`. -/
@[simp]
theorem strictTransform.baseChangeEnd_tmul (b : Blowup I a) (s : S) :
    strictTransform.baseChangeEnd I a S M (b ⊗ₜ[R] s) =
      Algebra.lsmul R R (TensorProduct R (Blowup I a) M) b *
        Module.End.lTensorAlgHom R M (Blowup I a) (Algebra.lsmul R R M s) :=
  rfl

/-- The scalar extension `R[I/a] ⊗[R] M` of an `S`-module `M` is a module over the scalar
extension `R[I/a] ⊗[R] S`.

This is deliberately not an instance: for `M = S` it would compete with the action of
`R[I/a] ⊗[R] S` on itself by multiplication. -/
@[instance_reducible]
noncomputable def strictTransform.baseChangeModule :
    Module (TensorProduct R (Blowup I a) S) (TensorProduct R (Blowup I a) M) :=
  Module.compHom _ (strictTransform.baseChangeEnd I a S M).toRingHom

attribute [local instance] strictTransform.baseChangeModule

/-- The element `b ⊗ s` of `R[I/a] ⊗[R] S` acts on `R[I/a] ⊗[R] M` by `c ⊗ m ↦ (b * c) ⊗ (s • m)`.
-/
@[simp]
theorem strictTransform.baseChange_smul_tmul (b c : Blowup I a) (s : S) (m : M) :
    (b ⊗ₜ[R] s) • (c ⊗ₜ[R] m) = (b * c) ⊗ₜ[R] (s • m) :=
  rfl

/-- The action of `R[I/a] ⊗[R] S` on `R[I/a] ⊗[R] M` extends the action of `R[I/a]`. -/
theorem strictTransform.baseChangeIsScalarTower :
    IsScalarTower (Blowup I a) (TensorProduct R (Blowup I a) S)
      (TensorProduct R (Blowup I a) M) :=
  ⟨fun b t x => by
    have h : strictTransform.baseChangeEnd I a S M (b • t) =
        Algebra.lsmul R R (TensorProduct R (Blowup I a) M) b *
          strictTransform.baseChangeEnd I a S M t := by
      rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
        strictTransform.baseChangeEnd_tmul, map_one, map_one, mul_one,
        Algebra.algebraMap_self_apply]
    exact congrArg (fun f : Module.End R (TensorProduct R (Blowup I a) M) => f x) h⟩

attribute [local instance] strictTransform.baseChangeIsScalarTower

/-- The actions of `R[I/a]` and of `R[I/a] ⊗[R] S` on `R[I/a] ⊗[R] M` commute. -/
theorem strictTransform.baseChangeSMulCommClass :
    SMulCommClass (Blowup I a) (TensorProduct R (Blowup I a) S)
      (TensorProduct R (Blowup I a) M) :=
  ⟨fun b t x => by
    rw [← smul_assoc, Algebra.smul_def,
      mul_comm (algebraMap (Blowup I a) (TensorProduct R (Blowup I a) S) b) t, mul_smul,
      algebraMap_smul]⟩

attribute [local instance] strictTransform.baseChangeSMulCommClass

/-- The actions of `R[I/a] ⊗[R] S` and of `R[I/a]` on `R[I/a] ⊗[R] M` commute. -/
theorem strictTransform.baseChangeSMulCommClass' :
    SMulCommClass (TensorProduct R (Blowup I a) S) (Blowup I a)
      (TensorProduct R (Blowup I a) M) :=
  SMulCommClass.symm _ _ _

attribute [local instance] strictTransform.baseChangeSMulCommClass'

/-- The `a`-power torsion submodule is stable under the action of the scalar extension
`R[I/a] ⊗[R] S`: if `aⁿ` kills `x`, then it kills `t • x` as well. -/
theorem strictTransform.torsionSubmodule_le_comap (t : TensorProduct R (Blowup I a) S) :
    strictTransform.torsionSubmodule I a M ≤
      (strictTransform.torsionSubmodule I a M).comap
        (Algebra.lsmul (Blowup I a) (Blowup I a) (TensorProduct R (Blowup I a) M) t) := by
  intro x hx
  obtain ⟨n, hn⟩ := (strictTransform.mem_torsionSubmodule_iff I a M).mp hx
  refine (strictTransform.mem_torsionSubmodule_iff I a M).mpr ⟨n, ?_⟩
  change (algebraMap R (Blowup I a) a) ^ n • (t • x) = 0
  rw [smul_comm, hn, smul_zero]

/-- The `R[I/a]`-linear endomorphism of the strict transform of `M` induced by an element of the
scalar extension `R[I/a] ⊗[R] S`. -/
noncomputable def strictTransform.actEnd (t : TensorProduct R (Blowup I a) S) :
    strictTransform I a M →ₗ[Blowup I a] strictTransform I a M :=
  Submodule.mapQ (strictTransform.torsionSubmodule I a M) (strictTransform.torsionSubmodule I a M)
    (Algebra.lsmul (Blowup I a) (Blowup I a) (TensorProduct R (Blowup I a) M) t)
    (strictTransform.torsionSubmodule_le_comap I a S M t)

/-- The scalar extension `R[I/a] ⊗[R] S` acts on the strict transform of an `S`-module `M`. -/
noncomputable instance strictTransform.instSMulTensorProduct :
    SMul (TensorProduct R (Blowup I a) S) (strictTransform I a M) :=
  ⟨fun t x => strictTransform.actEnd I a S M t x⟩

/-- The action of `R[I/a] ⊗[R] S` on the strict transform is induced by its action on the scalar
extension. -/
@[simp]
theorem strictTransform.smul_mkQ (t : TensorProduct R (Blowup I a) S)
    (x : TensorProduct R (Blowup I a) M) :
    t • strictTransform.mkQ I a M x = strictTransform.mkQ I a M (t • x) :=
  rfl

/-- The strict transform of an `S`-module `M` is a module over the scalar extension
`R[I/a] ⊗[R] S`, the action being induced by the action on `R[I/a] ⊗[R] M`. -/
noncomputable instance strictTransform.instModuleTensorProduct :
    Module (TensorProduct R (Blowup I a) S) (strictTransform I a M) where
  one_smul x := by
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
    simp only [strictTransform.smul_mkQ, one_smul]
  mul_smul t t' x := by
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
    simp only [strictTransform.smul_mkQ, mul_smul]
  smul_zero t := map_zero (strictTransform.actEnd I a S M t)
  smul_add t x y := map_add (strictTransform.actEnd I a S M t) x y
  add_smul t t' x := by
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
    simp only [strictTransform.smul_mkQ, add_smul, map_add]
  zero_smul x := by
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
    simp only [strictTransform.smul_mkQ, zero_smul, map_zero]

/-- The action of `R[I/a] ⊗[R] S` on the strict transform of `M` extends that of `R[I/a]`. -/
instance strictTransform.instIsScalarTowerTensorProduct :
    IsScalarTower (Blowup I a) (TensorProduct R (Blowup I a) S) (strictTransform I a M) where
  smul_assoc b t x := by
    obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
    simp only [strictTransform.smul_mkQ, map_smul, smul_assoc]

/-- Every element of `strictTransformIdeal I a S` annihilates the strict transform of an
`S`-module `M`: if `aⁿ` kills `t`, then `aⁿ` kills `t • w`, so `t • w` is `a`-power torsion. -/
theorem strictTransform.isTorsionBySet_strictTransformIdeal :
    Module.IsTorsionBySet (TensorProduct R (Blowup I a) S) (strictTransform I a M)
      (strictTransformIdeal I a S) := by
  intro x t
  obtain ⟨y, rfl⟩ := strictTransform.mkQ_surjective I a M x
  obtain ⟨n, hn⟩ := (mem_strictTransformIdeal_iff I a S).mp t.2
  rw [strictTransform.smul_mkQ]
  refine (Submodule.Quotient.mk_eq_zero (strictTransform.torsionSubmodule I a M)).mpr
    ((strictTransform.mem_torsionSubmodule_iff I a M).mpr ⟨n, ?_⟩)
  rw [← smul_assoc, hn, zero_smul]

/-- The strict transform of an `S`-module `M` is a module over the strict transform algebra of `S`,
since the `a`-power torsion of `R[I/a] ⊗[R] S` annihilates it. -/
noncomputable instance strictTransform.instModuleStrictTransformAlg :
    Module (strictTransformAlg I a S) (strictTransform I a M) :=
  (strictTransform.isTorsionBySet_strictTransformIdeal I a S M).module

/-- The class of `t` in the strict transform algebra acts on the strict transform as `t` does. -/
@[simp]
theorem strictTransformAlg.mk_smul (t : TensorProduct R (Blowup I a) S)
    (x : strictTransform I a M) :
    strictTransformAlg.mk I a S t • x = t • x :=
  rfl

/-- The action of the strict transform algebra of `S` on the strict transform of `M` extends the
action of `R[I/a]`. -/
instance strictTransform.instIsScalarTowerStrictTransformAlg :
    IsScalarTower (Blowup I a) (strictTransformAlg I a S) (strictTransform I a M) where
  smul_assoc b z x := by
    obtain ⟨t, rfl⟩ := strictTransformAlg.mk_surjective I a S z
    rw [← map_smul, strictTransformAlg.mk_smul, strictTransformAlg.mk_smul, smul_assoc]

end ModuleAction

end StrictTransformAlgebra
