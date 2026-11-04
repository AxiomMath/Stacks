module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.ExtClass
public import StacksFrontier.RingTheory.Rig.LiftingGeneral

/-!
# The obstruction class of Stacks 0GAP as an element of `Ext¹`

Let `A` be a ring, `I` an ideal of `A`, `B` an `I`-adically complete `A`-algebra of finite type
modulo `I` with a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`, and `C` an
`A`-algebra. Stacks 0GAP attaches to an `A`-algebra map `ψₘ : B → C/IᵐC` an obstruction class

`o(ψₘ) ∈ Ext¹_B(NL^∧_{B/A}, IᵐC / I²ᵐC)`

by choosing a lift `ψ : A⟨x₁, …, x_r⟩ → C` of `ψₘ`, observing that `ψ(J) ⊆ IᵐC` forces
`ψ(J²) ⊆ I²ᵐC`, and taking the class of the resulting `B`-linear map

`o(ψ) : J/J² → IᵐC/I²ᵐC`, `g ↦ ψ(g)`

under the identification `Ext¹_B(NL^∧_{B/A}, N) = Coker (Hom_B(⨁ B dxᵢ, N) → Hom_B(J/J², N))`
of Stacks 0ALN part (1).

This file builds all of that: the `B`-module `IᵐC/I²ᵐC`, the `B`-linear map `o(ψ)`, its
`C/IᵐC`-linear extension over `J/J² ⊗_B C/IᵐC`, and the class `o(ψ)` as a term of the Ext group
of the completed naive cotangent complex.

## The `B`-module structure

The `B`-action on `IᵐC/I²ᵐC` is the one Stacks 0GAP uses implicitly and is not the restriction
of anything: `B` does not map to `C`, only to `C/IᵐC`, and `IᵐC/I²ᵐC` is a module over
`C/IᵐC` because `IᵐC · IᵐC ⊆ I²ᵐC`. So the structure is assembled in three steps, carried by
`Rig.ObstructionLift`, which bundles the lift `ψ` with the bound `ψ(J) ⊆ IᵐC`:

* `Rig.ObstructionLift.base` is `C/IᵐC` and `Rig.ObstructionLift.residue` is the induced
  `A`-algebra map `B → C/IᵐC`, which exists exactly because `ψ(J) ⊆ IᵐC`;
* `Rig.ObstructionLift.target` is `IᵐC/I²ᵐC`, a `C`-module annihilated by `IᵐC`
  (`Rig.ObstructionLift.isTorsionBySet`) and therefore a `base`-module;
* `B` acts through `residue`, and the scalar tower `B → base → target` holds by construction.

Both `base` and `target` are type synonyms depending on the `ObstructionLift`, so that these
instances are unambiguous.

## Main definitions

* `Rig.ObstructionLift`: a lift `ψ` of `ψₘ` together with `ψ(J) ⊆ IᵐC`.
* `Rig.ObstructionLift.target`, `Rig.ObstructionLift.base`, `Rig.ObstructionLift.residue`.
* `Rig.ObstructionLift.obstruction`: the `B`-linear map `o(ψ) : J/J² → IᵐC/I²ᵐC`.
* `Rig.ObstructionLift.obstructionBaseChange`: its `C/IᵐC`-linear extension over
  `(C/IᵐC) ⊗_B J/J²`.
* `Rig.ObstructionLift.extClass`: the class `o(ψₘ)` in
  `Ext¹_B(NL^∧_{B/A}, IᵐC/I²ᵐC)`.

## Main results

* `Rig.ObstructionLift.obstruction_mk`: `o(ψ)` sends the class of `g ∈ J` to the class of
  `ψ(g)`. This is the defining formula of Stacks 0GAP.
* `Rig.ObstructionLift.obstructionBaseChange_tmul`: the base-changed map on `c ⊗ [g]`.
* `Rig.ObstructionLift.extClass_eq_zero_iff_exists_linearMap`: the class vanishes exactly when
  `o(ψ)` factors through the differential of `NL^∧_{B/A}`.
* `Rig.ObstructionLift.extClass_eq_zero_iff_exists_delta`: and exactly when there are
  `δ₁, …, δ_r ∈ IᵐC` with `ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I²ᵐC` for all `g ∈ J`, which is the form
  the lifting argument of `StacksFrontier/RingTheory/Rig/LiftingGeneral.lean` consumes.
* `Rig.exists_algHom_quotient_of_extClass_eq_zero`: **Stacks 0GAP**, the claim of the remark
  with the hypothesis stated as the vanishing of the Ext class.

## References

* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
* [Stacks Project, Tag 0AJR](https://stacks.math.columbia.edu/tag/0AJR)
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.Extension
open scoped TensorProduct
open RestrictedPowerSeries

namespace Rig

universe u v

/-- The `S`-linear map `P.Cotangent → T` determined by a `P.Ring`-linear map `P.ker → T` that
vanishes on products. This is the universal property of the conormal module, in the form
`Rig.cotangentMapOfDerivation` already uses for derivations. -/
public def cotangentMapOfKerMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) {T : Type*} [AddCommGroup T] [Module P.Ring T] [Module S T]
    [IsScalarTower P.Ring S T] (f : P.ker →ₗ[P.Ring] T)
    (hf : ∀ x y : P.ker, f (x * y) = 0) :
    P.Cotangent →ₗ[S] T :=
  LinearMap.extendScalarsOfSurjective P.algebraMap_surjective
    ((Ideal.Cotangent.lift f hf).comp P.cotangentEquivCotangentKer.toLinearMap)

/-- `cotangentMapOfKerMap P f hf` sends the class of `g ∈ P.ker` to `f g`. -/
@[simp]
public theorem cotangentMapOfKerMap_mk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) {T : Type*} [AddCommGroup T] [Module P.Ring T] [Module S T]
    [IsScalarTower P.Ring S T] (f : P.ker →ₗ[P.Ring] T)
    (hf : ∀ x y : P.ker, f (x * y) = 0) (g : P.ker) :
    cotangentMapOfKerMap P f hf (Algebra.Extension.Cotangent.mk g) = f g := by
  simp [cotangentMapOfKerMap, LinearMap.extendScalarsOfSurjective_apply, LinearMap.comp_apply,
    Algebra.Extension.cotangentEquivCotangentKer_apply, Algebra.Extension.Cotangent.val_mk,
    Ideal.Cotangent.lift_toCotangent]

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- A lift to `A⟨x₁, …, x_r⟩` of an `A`-algebra map `B → C/IᵐC`, packaged with the bound
`ψ(J) ⊆ IᵐC` that it satisfies and that makes `IᵐC/I²ᵐC` a `B`-module. This is the choice
Stacks 0GAP makes at the start of the construction of `o(ψₘ)`. -/
public structure ObstructionLift (P : CompletedPolynomialPresentation I B)
    (C : Type (max u v)) [CommRing C] [Algebra A C] (m : ℕ) where
  /-- The lift `ψ : A⟨x₁, …, x_r⟩ → C`. -/
  lift : P.completedPolynomialRing →ₐ[A] C
  /-- `ψ(J) ⊆ IᵐC`. -/
  lift_mem : ∀ g ∈ P.ker, lift g ∈ (I.map (algebraMap A C)) ^ m

namespace ObstructionLift

variable {P : CompletedPolynomialPresentation I B} {C : Type (max u v)} [CommRing C]
  [Algebra A C] {m : ℕ} (D : ObstructionLift P C m)

/-- `C / IᵐC`, the base over which the obstruction module is a module. It is a type synonym
carrying the `ObstructionLift`, so that the `B`-algebra structure through `residue` can be an
instance. -/
public def base (_D : ObstructionLift P C m) : Type (max u v) :=
  C ⧸ (I.map (algebraMap A C)) ^ m

/-- `C/IᵐC` is a commutative ring. -/
instance : CommRing D.base :=
  inferInstanceAs (CommRing (C ⧸ (I.map (algebraMap A C)) ^ m))

/-- `C/IᵐC` is an `A`-algebra. -/
instance : Algebra A D.base :=
  inferInstanceAs (Algebra A (C ⧸ (I.map (algebraMap A C)) ^ m))

/-- `C/IᵐC` is a `C`-algebra through the projection. -/
instance : Algebra C D.base :=
  inferInstanceAs (Algebra C (C ⧸ (I.map (algebraMap A C)) ^ m))

/-- The projection `C → C/IᵐC`. -/
public def mkBase (c : C) : D.base := Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ m) c

/-- The class of `c` in `C/IᵐC` vanishes exactly when `c ∈ IᵐC`. -/
public theorem mkBase_eq_zero_iff (c : C) :
    D.mkBase c = 0 ↔ c ∈ (I.map (algebraMap A C)) ^ m :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Two elements of `C` have the same class in `C/IᵐC` exactly when their difference lies in
`IᵐC`. -/
public theorem mkBase_eq_iff (c c' : C) :
    D.mkBase c = D.mkBase c' ↔ c - c' ∈ (I.map (algebraMap A C)) ^ m :=
  Ideal.Quotient.eq

/-- The reduction `B → C/IᵐC` of the lift: it exists because `ψ` kills `J` modulo `IᵐC`. -/
public def residue : B.carrier →ₐ[A] D.base :=
  AlgHom.liftOfSurjective P.toAlgHom P.toAlgHom_surjective
    ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ m)).comp D.lift)
    (by
      intro x hx
      rw [RingHom.mem_ker]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (D.lift_mem x hx))

/-- The reduction `residue` sends the image of `β ∈ A⟨x₁, …, x_r⟩` in `B` to the class of
`ψ(β)` in `C/IᵐC`. -/
@[simp]
public theorem residue_toAlgHom (β : P.completedPolynomialRing) :
    D.residue (P.toAlgHom β) = D.mkBase (D.lift β) :=
  AlgHom.liftOfSurjective_apply _ _ _ _ β

/-- `C/IᵐC` is a `B`-algebra through the reduction `residue`. -/
instance : Algebra B.carrier D.base := RingHom.toAlgebra D.residue.toRingHom

/-- The structure map `B → C/IᵐC` is the reduction `residue`. -/
public theorem algebraMap_base (b : B.carrier) :
    algebraMap B.carrier D.base b = D.residue b := rfl

/-- `IᵐC / I²ᵐC`, as a quotient of the ideal `IᵐC` of `C`. It is a type synonym carrying the
`ObstructionLift`, so that the `B`-module structure through `residue` can be an instance. -/
public def target (_D : ObstructionLift P C m) : Type (max u v) :=
  ↥((I.map (algebraMap A C)) ^ m) ⧸
    Submodule.comap ((I.map (algebraMap A C)) ^ m).subtype
      ((I.map (algebraMap A C)) ^ (2 * m))

/-- `IᵐC/I²ᵐC` is an additive commutative group. -/
instance : AddCommGroup D.target :=
  inferInstanceAs (AddCommGroup (↥((I.map (algebraMap A C)) ^ m) ⧸
    Submodule.comap ((I.map (algebraMap A C)) ^ m).subtype
      ((I.map (algebraMap A C)) ^ (2 * m))))

/-- `IᵐC/I²ᵐC` is a `C`-module. -/
instance : Module C D.target :=
  inferInstanceAs (Module C (↥((I.map (algebraMap A C)) ^ m) ⧸
    Submodule.comap ((I.map (algebraMap A C)) ^ m).subtype
      ((I.map (algebraMap A C)) ^ (2 * m))))

/-- The projection `IᵐC → IᵐC/I²ᵐC`, as a `C`-linear map. -/
public def mkTarget : ↥((I.map (algebraMap A C)) ^ m) →ₗ[C] D.target :=
  Submodule.mkQ (Submodule.comap ((I.map (algebraMap A C)) ^ m).subtype
    ((I.map (algebraMap A C)) ^ (2 * m)))

/-- The class of `y ∈ IᵐC` in `IᵐC/I²ᵐC` vanishes exactly when `y ∈ I²ᵐC`. -/
public theorem mkTarget_eq_zero_iff (y : ↥((I.map (algebraMap A C)) ^ m)) :
    D.mkTarget y = 0 ↔ (y : C) ∈ (I.map (algebraMap A C)) ^ (2 * m) :=
  Submodule.Quotient.mk_eq_zero _

/-- The projection `IᵐC → IᵐC/I²ᵐC` is surjective. -/
public theorem mkTarget_surjective : Function.Surjective D.mkTarget :=
  Submodule.mkQ_surjective _

/-- The product of two elements of `Iᵐ` lies in `I²ᵐ`. -/
private theorem mul_mem_pow_two_mul {R : Type*} [CommRing R] {J : Ideal R} {m : ℕ} {a b : R}
    (ha : a ∈ J ^ m) (hb : b ∈ J ^ m) : a * b ∈ J ^ (2 * m) := by
  rw [two_mul, pow_add]
  exact Ideal.mul_mem_mul ha hb

/-- `IᵐC/I²ᵐC` is annihilated by `IᵐC`, so it is a module over `C/IᵐC`. -/
public theorem isTorsionBySet :
    Module.IsTorsionBySet C D.target
      (((I.map (algebraMap A C)) ^ m : Ideal C) : Set C) := by
  intro x c
  obtain ⟨y, rfl⟩ := D.mkTarget_surjective x
  rw [← map_smul, D.mkTarget_eq_zero_iff]
  exact mul_mem_pow_two_mul c.2 y.2

/-- `IᵐC/I²ᵐC` is a `C/IᵐC`-module, since `IᵐC` annihilates it. -/
instance : Module D.base D.target := D.isTorsionBySet.module

/-- The class of `c` in `C/IᵐC` acts on `IᵐC/I²ᵐC` as `c` does. -/
public theorem mkBase_smul (c : C) (x : D.target) : D.mkBase c • x = c • x := rfl

/-- `IᵐC/I²ᵐC` is a `B`-module through the reduction `B → C/IᵐC`. -/
instance : Module B.carrier D.target := Module.compHom D.target (algebraMap B.carrier D.base)

/-- An element `b ∈ B` acts on `IᵐC/I²ᵐC` as its reduction `residue b` does. -/
public theorem smul_target (b : B.carrier) (x : D.target) : b • x = D.residue b • x := rfl

/-- The actions of `B` and `C/IᵐC` on `IᵐC/I²ᵐC` form a scalar tower. -/
instance : IsScalarTower B.carrier D.base D.target :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The `A⟨x₁, …, x_r⟩`-module structure on `IᵐC/I²ᵐC` through the lift `ψ`: a restricted power
series acts by the scalar it is sent to in `C`. -/
instance : Module P.extension.Ring D.target :=
  Module.compHom D.target D.lift.toRingHom

/-- The structure map `A⟨x₁, …, x_r⟩ → B` of the extension is the surjection of the
presentation. -/
public theorem algebraMap_extension_apply (β : P.completedPolynomialRing) :
    algebraMap P.extension.Ring B.carrier β = P.toAlgHom β := rfl

/-- A restricted power series `β` acts on `IᵐC/I²ᵐC` as `ψ(β)` does. -/
public theorem smul_target_ring (β : P.extension.Ring) (x : D.target) :
    β • x = D.lift β • x := rfl

/-- The actions of `A⟨x₁, …, x_r⟩` and `B` on `IᵐC/I²ᵐC` form a scalar tower. -/
instance : IsScalarTower P.extension.Ring B.carrier D.target :=
  IsScalarTower.of_algebraMap_smul fun β x => by
    have key : ∀ γ : P.completedPolynomialRing,
        D.residue (P.toAlgHom γ) • x = D.lift γ • x := by
      intro γ
      rw [D.residue_toAlgHom, D.mkBase_smul]
    exact key β

/-- The lift `ψ`, read as a map `J → IᵐC` and then into `IᵐC/I²ᵐC`: this is `o(ψ)` before
descending along `J → J/J²`. -/
public def kerMap : P.extension.ker →ₗ[P.extension.Ring] D.target where
  toFun g := D.mkTarget ⟨D.lift g.1, D.lift_mem g.1 g.2⟩
  map_add' g h := by
    rw [← map_add D.mkTarget]
    exact congrArg D.mkTarget (Subtype.ext (map_add D.lift g.1 h.1))
  map_smul' r g := by
    rw [D.smul_target_ring, ← map_smul D.mkTarget]
    exact congrArg D.mkTarget (Subtype.ext (map_mul D.lift r g.1))

/-- `kerMap` sends `g ∈ J` to the class of `ψ(g)` in `IᵐC/I²ᵐC`. -/
public theorem kerMap_apply (g : P.extension.ker) :
    D.kerMap g = D.mkTarget ⟨D.lift g.1, D.lift_mem g.1 g.2⟩ := rfl

/-- `kerMap` vanishes on products, since `ψ(J²) ⊆ I²ᵐC`. -/
public theorem kerMap_mul (x y : P.extension.ker) : D.kerMap (x * y) = 0 := by
  have hmem : ∀ a b : P.completedPolynomialRing, a ∈ P.ker → b ∈ P.ker →
      D.lift (a * b) ∈ (I.map (algebraMap A C)) ^ (2 * m) := fun a b ha hb => by
    rw [map_mul]
    exact mul_mem_pow_two_mul (D.lift_mem a ha) (D.lift_mem b hb)
  exact (D.mkTarget_eq_zero_iff _).mpr (hmem x.1 y.1 x.2 y.2)

/-- **Stacks 0GAP**, the obstruction map. The `B`-linear map

`o(ψ) : J/J² → IᵐC/I²ᵐC`, `g ↦ ψ(g)`,

well defined because `ψ(J) ⊆ IᵐC` forces `ψ(J²) ⊆ I²ᵐC`. The `B`-action on the target is
through `residue`, i.e. through the reduction of `ψ` modulo `IᵐC`. -/
@[stacks 0GAP "the obstruction map o(ψ) : J/J² → IᵐC/I²ᵐC"]
public def obstruction : P.extension.Cotangent →ₗ[B.carrier] D.target :=
  cotangentMapOfKerMap P.extension D.kerMap D.kerMap_mul

/-- **Stacks 0GAP**, the defining formula of the obstruction map: it sends the class of `g ∈ J`
to the class of `ψ(g)` in `IᵐC/I²ᵐC`. -/
@[simp]
public theorem obstruction_mk (g : P.extension.ker) :
    D.obstruction (Algebra.Extension.Cotangent.mk g)
      = D.mkTarget ⟨D.lift g.1, D.lift_mem g.1 g.2⟩ :=
  cotangentMapOfKerMap_mk P.extension D.kerMap D.kerMap_mul g

/-- **Stacks 0GAP**, the `C`-linear extension of the obstruction map. Since the `B`-action on
`IᵐC/I²ᵐC` factors through `C/IᵐC`, the `B`-linear map `o(ψ)` extends to a `C/IᵐC`-linear map

`(C/IᵐC) ⊗_B J/J² → IᵐC/I²ᵐC`.

This is the extension the remark records after constructing `o(ψ)`. -/
@[stacks 0GAP "the C-linear extension of o(ψ) over J/J² ⊗_B C"]
public def obstructionBaseChange :
    D.base ⊗[B.carrier] P.extension.Cotangent →ₗ[D.base] D.target :=
  LinearMap.liftBaseChange D.base D.obstruction

/-- `obstructionBaseChange` sends `c ⊗ z` to `c • o(ψ)(z)`. -/
@[simp]
public theorem obstructionBaseChange_tmul (c : D.base) (z : P.extension.Cotangent) :
    D.obstructionBaseChange (c ⊗ₜ z) = c • D.obstruction z :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- `obstructionBaseChange` sends `1 ⊗ z` to `o(ψ)(z)`. -/
@[simp]
public theorem obstructionBaseChange_one_tmul (z : P.extension.Cotangent) :
    D.obstructionBaseChange (1 ⊗ₜ z) = D.obstruction z :=
  LinearMap.liftBaseChange_one_tmul _ _ _

/-- The `B`-action of the image of `β ∈ A⟨x₁, …, x_r⟩` on a class in `IᵐC/I²ᵐC` is
multiplication by `ψ(β)`. -/
public theorem toAlgHom_smul_mkTarget (β : P.completedPolynomialRing)
    (y : ↥((I.map (algebraMap A C)) ^ m)) :
    P.toAlgHom β • D.mkTarget y
      = D.mkTarget ⟨D.lift β * y.1, Ideal.mul_mem_left _ _ y.2⟩ := by
  rw [D.smul_target, D.residue_toAlgHom, D.mkBase_smul, ← map_smul]
  rfl

end ObstructionLift

section ExtClass

variable {P : CompletedPolynomialPresentation I B} {C : Type (max u v)} [CommRing C]
  [Algebra A C] {m : ℕ}

attribute [local instance] HasDerivedCategory.standard

/-- The completed naive cotangent complex vanishes in degrees at most `-2`. -/
public theorem CompletedNaiveCotangentComplex.isZero_X_of_le
    (K : CompletedNaiveCotangentComplex P) (i : ℤ) (hi : i ≤ -2) :
    Limits.IsZero (K.cochainComplex.X i) :=
  HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- The completed naive cotangent complex vanishes in positive degrees. -/
public theorem CompletedNaiveCotangentComplex.isZero_X_of_pos
    (K : CompletedNaiveCotangentComplex P) (i : ℤ) (hi : 0 < i) :
    Limits.IsZero (K.cochainComplex.X i) :=
  HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- The degree-zero term of the completed naive cotangent complex is projective, being free. -/
public theorem CompletedNaiveCotangentComplex.projective_X_zero
    (K : CompletedNaiveCotangentComplex P) : Projective (K.cochainComplex.X 0) := by
  have hfree := K.free_X_zero
  have hproj : Module.Projective B.carrier (K.cochainComplex.X 0) := by
    have := hfree; infer_instance
  exact (IsProjective.iff_projective (R := B.carrier) (K.cochainComplex.X 0)).mp hproj

namespace ObstructionLift

variable (D : ObstructionLift P C m) (K : CompletedNaiveCotangentComplex P)

/-- `o(ψ)`, read as a map out of the degree `-1` term of the completed naive cotangent complex
through the identification of that term with `J/J²`. -/
public def obstructionHom : K.cochainComplex.X (-1) ⟶ ModuleCat.of B.carrier D.target :=
  K.degreeNegOneIso.hom ≫ ModuleCat.ofHom (D.obstruction.comp ULift.moduleEquiv.toLinearMap)

/-- **Stacks 0GAP**, the obstruction class

`o(ψₘ) ∈ Ext¹_B(NL^∧_{B/A}, IᵐC/I²ᵐC)`,

the image of `o(ψ)` under the identification of `Ext¹` with
`Coker (Hom_B(⨁ B dxᵢ, -) → Hom_B(J/J², -))` of Stacks 0ALN part (1). -/
@[stacks 0GAP "the obstruction class o(ψₘ) in Ext¹_B(NL^∧_{B/A}, IᵐC/I²ᵐC)"]
public def extClass :
    DerivedCategory.Ext (DerivedCategory.Q.obj K.cochainComplex)
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj
        (ModuleCat.of B.carrier D.target)) 1 :=
  TwoTermComplexExt.extClassShifted K.cochainComplex (ModuleCat.of B.carrier D.target)
    (fun i hi => K.isZero_X_of_le i hi) (D.obstructionHom K)

/-- **Stacks 0GAP**: the obstruction class vanishes exactly when `o(ψ)` factors through the
differential of `NL^∧_{B/A}`, i.e. exactly when there is a `B`-linear
`h : ⨁ i, B dxᵢ → IᵐC/I²ᵐC` with `h ∘ d = o(ψ)`. This is the cokernel description of
Stacks 0ALN part (1), read on the completed naive cotangent complex. -/
@[stacks 0GAP "the vanishing of o(ψₘ) as a factorization through d"]
public theorem extClass_eq_zero_iff_exists_linearMap :
    D.extClass K = 0 ↔
      ∃ h : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] D.target,
        ∀ z, h (K.differential z) = D.obstruction z := by
  rw [extClass, TwoTermComplexExt.extClassShifted_eq_zero_iff _ _ _
    (fun i hi => K.isZero_X_of_pos i hi) K.projective_X_zero]
  constructor
  · rintro ⟨h0, hh0⟩
    rw [K.cochainComplex_d, obstructionHom] at hh0
    have hh0' : ModuleCat.ofHom K.liftedDifferential ≫ (K.degreeZeroIso.inv ≫ h0)
        = ModuleCat.ofHom (D.obstruction.comp ULift.moduleEquiv.toLinearMap) :=
      (cancel_epi K.degreeNegOneIso.hom).mp (by simpa only [Category.assoc] using hh0)
    refine ⟨(ModuleCat.Hom.hom (K.degreeZeroIso.inv ≫ h0)).comp
      ULift.moduleEquiv.symm.toLinearMap, fun z => ?_⟩
    simpa using congrArg (fun (f : _ ⟶ _) => (ModuleCat.Hom.hom f) (ULift.up z)) hh0'
  · rintro ⟨h, hh⟩
    refine ⟨K.degreeZeroIso.hom ≫ ModuleCat.ofHom (h.comp ULift.moduleEquiv.toLinearMap), ?_⟩
    rw [K.cochainComplex_d, obstructionHom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
    obtain ⟨z⟩ := w
    simpa using hh z

/-- Two classes in `IᵐC/I²ᵐC` agree exactly when their representatives agree modulo `I²ᵐC`. -/
public theorem mkTarget_eq_mkTarget_iff
    (y z : ↥((I.map (algebraMap A C)) ^ m)) :
    D.mkTarget y = D.mkTarget z ↔ (y : C) - (z : C) ∈ (I.map (algebraMap A C)) ^ (2 * m) := by
  rw [← sub_eq_zero, ← map_sub, D.mkTarget_eq_zero_iff]
  exact Iff.rfl

/-- The value of a candidate factorisation on the differential of the class of `g ∈ J`:
if `h(dxᵢ)` is the class of `yᵢ`, then `h(d[g]) = [∑ i, ψ(∂g/∂xᵢ) yᵢ]`. -/
private theorem apply_differential_mk
    (h : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] D.target)
    (y : Fin P.variableCount → ↥((I.map (algebraMap A C)) ^ m))
    (hy : ∀ i, h (Pi.single i 1) = D.mkTarget (y i)) (g : P.extension.ker) :
    h (K.differential (Algebra.Extension.Cotangent.mk g))
      = D.mkTarget (∑ i, (D.lift (K.partialDeriv i g.1)) • y i) := by
  classical
  rw [K.differential_mk g]
  have hsplit : (fun i => P.toAlgHom (K.partialDeriv i g.1))
      = ∑ i, P.toAlgHom (K.partialDeriv i g.1) •
        (Pi.single i 1 : Fin P.variableCount → B.carrier) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsplit, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hy i, D.toAlgHom_smul_mkTarget]
  rfl

/-- **Stacks 0GAP**: the obstruction class vanishes exactly when there are
`δ₁, …, δ_r ∈ IᵐC` with

`ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I²ᵐC`  for every `g ∈ J`.

The `δᵢ` are representatives of the values `h(dxᵢ)` of the factorisation `h` of the previous
theorem; this is the form in which the lifting argument consumes the vanishing. -/
@[stacks 0GAP "the vanishing of o(ψₘ) on representatives"]
public theorem extClass_eq_zero_iff_exists_delta :
    D.extClass K = 0 ↔
      ∃ δ : Fin P.variableCount → C, (∀ i, δ i ∈ (I.map (algebraMap A C)) ^ m) ∧
        ∀ g ∈ P.ker, D.lift g - ∑ i, D.lift (K.partialDeriv i g) * δ i
          ∈ (I.map (algebraMap A C)) ^ (2 * m) := by
  classical
  rw [D.extClass_eq_zero_iff_exists_linearMap K]
  have hcoe : ∀ (c : Fin P.variableCount → C)
      (y : Fin P.variableCount → ↥((I.map (algebraMap A C)) ^ m)),
      ((∑ i, c i • y i : ↥((I.map (algebraMap A C)) ^ m)) : C) = ∑ i, c i * (y i : C) := by
    intro c y
    rw [AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  constructor
  · rintro ⟨h, hh⟩
    choose y hy using fun i => D.mkTarget_surjective (h (Pi.single i 1))
    refine ⟨fun i => (y i : C), fun i => (y i).2, fun g hg => ?_⟩
    have h1 := D.apply_differential_mk K h y (fun i => (hy i).symm) ⟨g, hg⟩
    rwa [hh (Algebra.Extension.Cotangent.mk ⟨g, hg⟩), D.obstruction_mk,
      D.mkTarget_eq_mkTarget_iff, hcoe] at h1
  · rintro ⟨δ, hδ, hrel⟩
    refine ⟨∑ i, LinearMap.smulRight
      (LinearMap.proj i : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] B.carrier)
      (D.mkTarget ⟨δ i, hδ i⟩), fun z => ?_⟩
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    have hy : ∀ i, (∑ j, LinearMap.smulRight
        (LinearMap.proj j : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] B.carrier)
        (D.mkTarget ⟨δ j, hδ j⟩)) (Pi.single i 1) = D.mkTarget ⟨δ i, hδ i⟩ := by
      intro i
      simp [Pi.single_apply]
    rw [D.apply_differential_mk K _ (fun i => ⟨δ i, hδ i⟩) hy g, D.obstruction_mk,
      D.mkTarget_eq_mkTarget_iff, hcoe]
    simpa using ((I.map (algebraMap A C)) ^ (2 * m)).neg_mem (hrel g.1 g.2)

end ObstructionLift

/-- **Stacks 0GAP**, the claim of the remark with its hypothesis in the form the remark states
it: the vanishing of the obstruction class in `Ext¹_B(NL^∧_{B/A}, I^{n'}C/I^{2n'}C)`.

Let `A` be a Noetherian ring, `I` a finitely generated ideal, `B` an `I`-adically complete
`A`-algebra of finite type modulo `I` with a completed polynomial presentation
`B = A⟨x₁, …, x_r⟩ / J`, and `C` an `I`-adically complete `A`-algebra. Let
`ψₙ : B → C/IⁿC` be an `A`-algebra map and `D` a continuous lift of it to `A⟨x₁, …, x_r⟩`
with `D.lift(J) ⊆ I^{n'}C`, for some `n' ≤ n`. If `o(ψ_{n'}) = 0` in
`Ext¹_B(NL^∧_{B/A}, I^{n'}C/I^{2n'}C)`, then there is an `A`-algebra homomorphism
`ψ'_{2n'} : B → C/I^{2n'}C` agreeing with `ψₙ` as maps into `C/I^{n'}C`.

Arbitrary `I`, no regularity hypothesis, and no Cramer relation assumed. -/
@[stacks 0GAP "the claim, with the hypothesis as the vanishing of the Ext class"]
public theorem exists_algHom_quotient_of_extClass_eq_zero [IsNoetherianRing A] (hI : I.FG)
    [IsAdicComplete (I.map (algebraMap A C)) C] (n n' : ℕ) (hn' : n' ≤ n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (D : ObstructionLift P C n')
    (hcont : @Continuous _ _ (limitTopology I (Fin P.variableCount))
      ((I.map (algebraMap A C)).adicTopology)
      (D.lift.comp (adicCompletionAlgEquiv I (Fin P.variableCount)).toAlgHom))
    (hred : ∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n)
        (D.lift (adicCompletionAlgEquiv I (Fin P.variableCount) g))
      = ψn (P.restrictedToAlgHom g))
    (hvanish : D.extClass (completedNaiveCotangentComplex B P) = 0) :
    ∃ ψ₂ : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (show n' ≤ 2 * n' by omega))).comp ψ₂
        = (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn')).comp ψn := by
  classical
  obtain ⟨δ, hδ, hrel⟩ :=
    (D.extClass_eq_zero_iff_exists_delta (completedNaiveCotangentComplex B P)).mp hvanish
  set e := adicCompletionAlgEquiv I (Fin P.variableCount) with he
  have hderiv' : ∀ (i : Fin P.variableCount) (w : RestrictedPowerSeries I (Fin P.variableCount)),
      (completedNaiveCotangentComplex B P).partialDeriv i (e w)
        = e (partialDerivative I i w) := by
    intro i w
    rw [CompletedNaiveCotangentComplex.partialDeriv_eq]
    exact congrArg (e ∘ partialDerivative I i) (e.symm_apply_apply w)
  refine exists_algHom_quotient_of_obstruction_factors hI P n n' hn' ψn
    (D.lift.comp e.toAlgHom) hcont hred δ hδ ?_
  intro g hg
  have h1 := hrel (e g) hg
  simp only [hderiv'] at h1
  exact h1

end ExtClass

end Rig

end
