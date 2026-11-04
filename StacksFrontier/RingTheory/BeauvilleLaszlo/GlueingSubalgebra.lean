module

public import StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence
import all StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence

/-!
# The glued algebra of an algebra glueing datum

Let `(R → S, f)` be a Beauville--Laszlo glueing pair. An algebra glueing datum consists of an
`S`-algebra `A'`, an `R_f`-algebra `A₁` and a ring `A''` that is simultaneously the localization
of `A'` away from `f` and the base change `S ⊗[R] A₁`. This file builds the algebra of compatible
pairs of such a datum and shows that it glues the datum, which is the ring-theoretic content of
Stacks 0F9Q.

## Main definitions

* `glueingSubalgebra R A' A₁ A''` is the algebra of compatible pairs of an algebra glueing
  datum: the subalgebra of `A' × A₁` on which the two maps to the overlap `A''` agree.

## Main results

* `glueingSubalgebra_spec` (the ring-theoretic content of Stacks 0F9Q): the algebra of
  compatible pairs of an algebra glueing datum is a glueable `R`-module, and its two coordinate
  projections exhibit `A₁` as its localization away from `f` and `A'` as its base change to `S`.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

namespace BeauvilleLaszlo

section GlueingSubalgebra

open scoped TensorProduct

variable (R A' A₁ A'' : Type*) [CommRing R] [CommRing A'] [CommRing A₁] [CommRing A'']
  [Algebra R A'] [Algebra R A₁] [Algebra R A''] [Algebra A' A''] [Algebra A₁ A'']
  [IsScalarTower R A' A''] [IsScalarTower R A₁ A'']

/-- The algebra of compatible pairs of an algebra glueing datum: the subalgebra of `A' × A₁`
cut out by the condition that the two induced elements of the overlap `A''` agree. It is the
equalizer of the two `R`-algebra maps `A' × A₁ →ₐ[R] A''` given by the two coordinates. -/
public def glueingSubalgebra : Subalgebra R (A' × A₁) :=
  AlgHom.equalizer ((IsScalarTower.toAlgHom R A' A'').comp (AlgHom.fst R A' A₁))
    ((IsScalarTower.toAlgHom R A₁ A'').comp (AlgHom.snd R A' A₁))

/-- A pair of elements is a compatible pair exactly when its two images in the overlap agree. -/
@[simp]
public theorem mem_glueingSubalgebra {x : A' × A₁} :
    x ∈ glueingSubalgebra R A' A₁ A'' ↔
      algebraMap A' A'' x.1 = algebraMap A₁ A'' x.2 :=
  Iff.rfl

/-- The first coordinate of a compatible pair, as an `R`-algebra map to the generic part. -/
public def glueingGenericHom : glueingSubalgebra R A' A₁ A'' →ₐ[R] A' :=
  (AlgHom.fst R A' A₁).comp (glueingSubalgebra R A' A₁ A'').val

/-- The second coordinate of a compatible pair, as an `R`-algebra map to the local part. -/
public def glueingLocalHom : glueingSubalgebra R A' A₁ A'' →ₐ[R] A₁ :=
  (AlgHom.snd R A' A₁).comp (glueingSubalgebra R A' A₁ A'').val

/-- The generic projection of the glued algebra is the first coordinate. -/
@[simp]
public theorem glueingGenericHom_apply (x : glueingSubalgebra R A' A₁ A'') :
    glueingGenericHom R A' A₁ A'' x = (x : A' × A₁).1 := rfl

/-- The local projection of the glued algebra is the second coordinate. -/
@[simp]
public theorem glueingLocalHom_apply (x : glueingSubalgebra R A' A₁ A'') :
    glueingLocalHom R A' A₁ A'' x = (x : A' × A₁).2 := rfl

/-- The generic part is an algebra over the glued algebra, via the first coordinate. -/
public instance glueingAlgebraGeneric : Algebra (glueingSubalgebra R A' A₁ A'') A' :=
  (glueingGenericHom R A' A₁ A'').toRingHom.toAlgebra

/-- The local part is an algebra over the glued algebra, via the second coordinate. -/
public instance glueingAlgebraLocal : Algebra (glueingSubalgebra R A' A₁ A'') A₁ :=
  (glueingLocalHom R A' A₁ A'').toRingHom.toAlgebra

/-- The structure map of `glueingAlgebraGeneric` is the first coordinate projection. -/
public theorem algebraMap_glueingSubalgebra_generic :
    algebraMap (glueingSubalgebra R A' A₁ A'') A' =
      (glueingGenericHom R A' A₁ A'').toRingHom := rfl

/-- The structure map of `glueingAlgebraLocal` is the second coordinate projection. -/
public theorem algebraMap_glueingSubalgebra_local :
    algebraMap (glueingSubalgebra R A' A₁ A'') A₁ =
      (glueingLocalHom R A' A₁ A'').toRingHom := rfl

/-- The glued algebra, its generic part and `R` form a tower of scalars. -/
public instance glueingIsScalarTowerGeneric :
    IsScalarTower R (glueingSubalgebra R A' A₁ A'') A' :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The glued algebra, its local part and `R` form a tower of scalars. -/
public instance glueingIsScalarTowerLocal :
    IsScalarTower R (glueingSubalgebra R A' A₁ A'') A₁ :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end GlueingSubalgebra

section GlueingSubalgebraSpec

open CategoryTheory
open scoped TensorProduct

/-- **Beauville--Laszlo glueing for algebras**, the ring-theoretic content of the proof of
Stacks 0F9Q. Let `(R → S, f)` be a Beauville--Laszlo glueing pair, let `A₁` be an `R_f`-algebra,
let `A'` be an `S`-algebra, and let `A''` be a ring that is simultaneously the localization of
`A'` away from `f` and the base change `S ⊗[R] A₁`. Then the glued algebra
`A = glueingSubalgebra R A' A₁ A''` of compatible pairs is a glueable `R`-module, `A₁` is the
localization of `A` away from `f`, and `A'` is the base change of `A` to `S`.

The algebra structures `Algebra A A'` and `Algebra A A₁` used in the three conclusions are the
ones induced by the two coordinate projections `glueingGenericHom` and `glueingLocalHom`
(see `algebraMap_glueingSubalgebra_generic` and `algebraMap_glueingSubalgebra_local`). -/
public theorem glueingSubalgebra_spec
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (f : R)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Bijective (quotientPowMap f n (algebraMap R S)))
    (hglue : (beauvilleLaszloSequence f (algebraMap R S)).ShortExact)
    {A' A₁ A'' : Type*} [CommRing A'] [CommRing A₁] [CommRing A'']
    [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
    [Algebra R A₁] [Algebra (Localization.Away f) A₁]
    [IsScalarTower R (Localization.Away f) A₁]
    [Algebra R A''] [Algebra S A''] [Algebra A' A''] [Algebra A₁ A'']
    [IsScalarTower R A' A''] [IsScalarTower R A₁ A''] [IsScalarTower R S A'']
    [IsScalarTower S A' A'']
    [IsLocalization.Away (algebraMap R A' f) A'']
    [Algebra.IsPushout R S A₁ A''] :
    (beauvilleLaszloModuleSequence (S := S)
        (glueingSubalgebra R A' A₁ A'') f).ShortExact ∧
      Algebra.IsPushout R (Localization.Away f) (glueingSubalgebra R A' A₁ A'') A₁ ∧
      IsLocalization.Away
        (algebraMap R (glueingSubalgebra R A' A₁ A'') f) A₁ ∧
      Algebra.IsPushout R S (glueingSubalgebra R A' A₁ A'') A' := by
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S f))
      (IsScalarTower.toAlgHom S A' A'').toLinearMap := by
    have he : Algebra.algebraMapSubmonoid A' (Submonoid.powers (algebraMap R S f)) =
        Submonoid.powers (algebraMap R A' f) := by
      change (Submonoid.powers (algebraMap R S f)).map (algebraMap S A') = _
      rw [Submonoid.map_powers, ← IsScalarTower.algebraMap_apply R S A' f]
    rw [isLocalizedModule_iff_isLocalization, he]
    infer_instance
  let mk₁ := LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) A'
  let e₁ := IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S f)) mk₁
    (IsScalarTower.toAlgHom S A' A'').toLinearMap
  let e₂ := Algebra.IsPushout.equiv R S A₁ A''
  let α := e₁.trans e₂.symm.toLinearEquiv
  have he₁ (a : A') : e₁ (mk₁ a) = algebraMap A' A'' a :=
    IsLocalizedModule.linearEquiv_apply (Submonoid.powers (algebraMap R S f)) mk₁
      (IsScalarTower.toAlgHom S A' A'').toLinearMap a
  have hα (a : A₁) : α.symm ((1 : S) ⊗ₜ[R] a) = e₁.symm (algebraMap A₁ A'' a) := by
    rw [LinearEquiv.symm_apply_eq]
    change (1 : S) ⊗ₜ[R] a = e₂.symm (e₁ (e₁.symm (algebraMap A₁ A'' a)))
    rw [LinearEquiv.apply_symm_apply]
    exact (Algebra.IsPushout.equiv_symm_algebraMap_right R S A₁ A'' a).symm
  have hcarrier : Subalgebra.toSubmodule (glueingSubalgebra R A' A₁ A'') =
      LinearMap.ker (difference f α) := by
    refine SetLike.ext fun x ↦ ?_
    rw [LinearMap.mem_ker, Subalgebra.mem_toSubmodule, mem_glueingSubalgebra,
      show difference f α x = mk₁ x.1 - α.symm ((1 : S) ⊗ₜ[R] x.2) from rfl,
      sub_eq_zero, hα, LinearEquiv.eq_symm_apply, he₁]
  let E : glueingSubalgebra R A' A₁ A'' ≃ₗ[R] kernel f α :=
    (Subalgebra.toSubmoduleEquiv (glueingSubalgebra R A' A₁ A'')).symm.trans
      (LinearEquiv.ofEq _ _ hcarrier)
  have hone : (beauvilleLaszloModuleSequence (S := S)
      (glueingSubalgebra R A' A₁ A'') f).ShortExact :=
    submodule_prod_glueable f hquot hglue
      (Subalgebra.toSubmodule (glueingSubalgebra R A' A₁ A''))
  have : IsLocalizedModule (Submonoid.powers f) (localProjection f α) :=
    localProjection_isLocalizedModule f α
  have hloc : IsLocalizedModule (Submonoid.powers f)
      (IsScalarTower.toAlgHom R (glueingSubalgebra R A' A₁ A'') A₁).toLinearMap :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f) (localProjection f α) E
  have htwo : Algebra.IsPushout R (Localization.Away f)
      (glueingSubalgebra R A' A₁ A'') A₁ :=
    ⟨IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f) _⟩
  have hthree : IsLocalization.Away
      (algebraMap R (glueingSubalgebra R A' A₁ A'') f) A₁ := by
    have h := isLocalizedModule_iff_isLocalization.mp hloc
    rwa [show Algebra.algebraMapSubmonoid (glueingSubalgebra R A' A₁ A'') (Submonoid.powers f) =
      Submonoid.powers (algebraMap R (glueingSubalgebra R A' A₁ A'') f) from
      Submonoid.map_powers _ _] at h
  have hgen : Function.Bijective (extendScalars (S := S) (genericProjection f α)) :=
    genericProjection_baseChange_bijective f α hquot hglue
  have hgenEq : extendScalars (S := S) (glueingGenericHom R A' A₁ A'').toLinearMap =
      (extendScalars (S := S) (genericProjection f α)).comp
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) E).toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ rfl
  have hgenBij : Function.Bijective
      (extendScalars (S := S) (glueingGenericHom R A' A₁ A'').toLinearMap) := by
    rw [hgenEq]
    exact hgen.comp
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) E).bijective
  have hfour : Algebra.IsPushout R S (glueingSubalgebra R A' A₁ A'') A' := by
    refine ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hgenBij) fun x ↦ ?_⟩
    rw [LinearEquiv.ofBijective_apply, extendScalars_tmul, one_smul]
    rfl
  exact ⟨hone, htwo, hthree, hfour⟩

end GlueingSubalgebraSpec

end BeauvilleLaszlo

end
