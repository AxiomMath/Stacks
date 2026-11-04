module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleLocalization
public import StacksFrontier.RingTheory.TraceElement.Construction

/-!
# Transporting the canonical element of a relative dualizing module

For a finite-open factorization `A → C → B` with `B` flat over `A` and `C` a finitely presented
`A`-module, `Stacks.Discriminant.dualizingModule.traceCandidate` is the element of
`ω_{B/A} = Hom_A(C, A) ⊗_C B` corresponding to the structure map `C → B` under
`B ⊗_A Hom_A(C, A) ≅ Hom_A(C, B)`. This file shows that it is carried to the corresponding
element by the three operations that move between factorizations: arbitrary base change of the
base ring, transport along an isomorphism of the target, and replacement of the intermediate
algebra by an isomorphic one.

## Main results

* `Stacks.Discriminant.dualizingModule.traceCandidate_eq_sum`: the canonical element is
  `∑ λᵢ ⊗ bᵢ` for every finite family with `∑ λᵢ(c) bᵢ` the image of `c` in `B`.
* `Stacks.Discriminant.dualizingModule.baseChange_traceCandidate`: the base change map of
  Tag 0BVB carries the canonical element to the canonical element.
* `Stacks.Discriminant.dualizingModule.retargetEquiv_traceCandidate`: so does the transport
  along an isomorphism of the target.
* `Stacks.Discriminant.dualizingModule.middleEquiv` and
  `Stacks.Discriminant.dualizingModule.middleEquiv_traceCandidate`: an isomorphism of the
  intermediate algebras compatible with the maps to the target identifies the dualizing
  modules, carrying the canonical element to the canonical element.

## Implementation notes

All three statements reduce to `traceCandidate_eq_sum`: the canonical element is determined by
any finite family presenting the structure map, and each operation carries a presenting family
to a presenting family.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

namespace FiniteOpenFactorization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The intermediate algebra of a base-changed factorization is finitely presented when the
original one is. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) [Module.FinitePresentation A F.middle]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    Module.FinitePresentation A₁ (baseChange F A₁).middle :=
  inferInstanceAs (Module.FinitePresentation A₁ (A₁ ⊗[A] F.middle))

end FiniteOpenFactorization

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The canonical element is `∑ λᵢ ⊗ bᵢ` for every finite family `(λᵢ, bᵢ)` with
`∑ λᵢ(c) bᵢ` the image of `c` in `B` for all `c`. -/
theorem traceCandidate_eq_sum (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.Flat A B] [Module.FinitePresentation A F.middle]
    {ι : Type*} [Fintype ι] (b : ι → B) (l : ι → Module.Dual A F.middle)
    (h : ∀ c : F.middle, ∑ i, l i c • b i = algebraMap F.middle B c) :
    traceCandidate F = ∑ i, dualizingModule.tmul F (l i) (b i) := by
  have hx : (dualBaseChangeEquiv A B F.middle).symm
      ((Algebra.linearMap F.middle B).restrictScalars A) = ∑ i, b i ⊗ₜ l i := by
    rw [LinearEquiv.symm_apply_eq]
    ext c
    simp [map_sum, h]
  rw [traceCandidate, hx, map_sum]
  simp

/-- The canonical element is presented by a finite family indexed by a finite type. -/
theorem exists_traceCandidate_eq_sum (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.Flat A B] [Module.FinitePresentation A F.middle] :
    ∃ (ι : Type (max v u w)) (_ : Fintype ι) (b : ι → B) (l : ι → Module.Dual A F.middle),
      (∀ c : F.middle, ∑ i, l i c • b i = algebraMap F.middle B c) ∧
        traceCandidate F = ∑ i, dualizingModule.tmul F (l i) (b i) := by
  obtain ⟨S, hS, hτ⟩ := exists_traceCandidate_repr F
  refine ⟨S, inferInstance, fun p ↦ p.1.1, fun p ↦ p.1.2, fun c ↦ ?_, ?_⟩
  · rw [← hS c]
    exact Finset.sum_coe_sort S (fun p ↦ p.2 c • p.1)
  · rw [hτ]
    exact (Finset.sum_coe_sort S (fun p ↦ dualizingModule.tmul F p.2 p.1)).symm

/-- **The canonical element commutes with base change.** For `B` flat over `A` and an
intermediate algebra finitely presented over `A`, the base change map of Tag 0BVB carries the
canonical element of `ω_{B/A}` to the canonical element of `ω_{B₁/A₁}`, `B₁ = A₁ ⊗_A B`, for an
arbitrary `A`-algebra `A₁`. -/
theorem baseChange_traceCandidate (F : FiniteOpenFactorization.{u, v, w} A B)
    [Module.Flat A B] [Module.FinitePresentation A F.middle]
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    dualizingModule.baseChange F A₁ (traceCandidate F) =
      traceCandidate (FiniteOpenFactorization.baseChange F A₁) := by
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  obtain ⟨ι, _, b, l, hl, hτ⟩ := exists_traceCandidate_eq_sum F
  rw [hτ, map_sum]
  simp only [baseChange_tmul]
  symm
  have key : ∀ x : A₁ ⊗[A] F.middle, ∑ i, ((l i).baseChange A₁ x) • ((1 : A₁) ⊗ₜ[A] b i) =
      Algebra.TensorProduct.map (AlgHom.id A A₁) (IsScalarTower.toAlgHom A F.middle B) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]
    | tmul a c =>
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
          ← hl c, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Module.Dual.baseChange_apply_tmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one, TensorProduct.tmul_smul]
  exact traceCandidate_eq_sum (FiniteOpenFactorization.baseChange F A₁)
    (fun i ↦ (1 : A₁) ⊗ₜ b i) (fun i ↦ (l i).baseChange A₁) key

/-- **The canonical element is carried along an isomorphism of the target.** -/
theorem retargetEquiv_traceCandidate
    {D : Type x} [CommRing D] [Algebra A D] [Algebra B D]
    (F : FiniteOpenFactorization.{u, x, w} A D) (e : D ≃ₐ[A] B)
    (he : ∀ b : B, e (algebraMap B D b) = b)
    [Module.Flat A D] [Module.Flat A B] [Module.FinitePresentation A F.middle] :
    letI : Module B (dualizingModule F) :=
      Module.compHom _ (algebraMap B D)
    letI : AddCommGroup (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instAddCommGroup (retargetFactorization F e)
    letI : Module B (dualizingModule (retargetFactorization F e)) :=
      dualizingModule.instModule (retargetFactorization F e)
    dualizingModule_retargetEquiv F e he (traceCandidate F) =
      traceCandidate (retargetFactorization F e) := by
  let : Module B (dualizingModule F) :=
    Module.compHom _ (algebraMap B D)
  obtain ⟨ι, _, b, l, hl, hτ⟩ := exists_traceCandidate_eq_sum F
  rw [hτ, map_sum]
  simp only [dualizingModule_retargetEquiv_tmul]
  symm
  refine traceCandidate_eq_sum (retargetFactorization F e) (fun i ↦ e (b i)) l fun c ↦ ?_
  have := congrArg e (hl c)
  simp only [map_sum, map_smul] at this
  exact this

section MiddleEquiv

variable (F : FiniteOpenFactorization.{u, v, w} A B) (G : FiniteOpenFactorization.{u, v, x} A B)
  (r : F.middle ≃ₐ[A] G.middle)
  (hr : ∀ c, algebraMap G.middle B (r c) = algebraMap F.middle B c)

include hr in
/-- An isomorphism of intermediate algebras compatible with the maps to the target exhibits the
target as the pushout of the target along it. -/
theorem isPushout_middleEquiv :
    letI : Algebra F.middle G.middle := r.toAlgHom.toRingHom.toAlgebra
    letI : IsScalarTower F.middle G.middle B := IsScalarTower.of_algebraMap_eq fun c ↦ (hr c).symm
    Algebra.IsPushout F.middle B G.middle B := by
  let : Algebra F.middle G.middle := r.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower F.middle G.middle B := IsScalarTower.of_algebraMap_eq fun c ↦ (hr c).symm
  let e : G.middle ≃ₗ[F.middle] F.middle :=
    { r.symm.toLinearEquiv.toAddEquiv with
      map_smul' := fun c x ↦ by
        show r.symm (r c * x) = c * r.symm x
        rw [map_mul, AlgEquiv.symm_apply_apply] }
  have heq : (IsScalarTower.toAlgHom F.middle G.middle B).toLinearMap =
      (Algebra.linearMap F.middle B).comp e.toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    show algebraMap G.middle B x = algebraMap F.middle B (r.symm x)
    rw [← hr, AlgEquiv.apply_symm_apply]
  exact ⟨heq ▸ IsBaseChange.comp_equiv e (Algebra.linearMap F.middle B)
    (IsBaseChange.linearMap F.middle B)⟩

/-- **Changing the intermediate algebra along an isomorphism.** An isomorphism of the
intermediate algebras of two finite-open factorizations, compatible with the maps to the target,
identifies their relative dualizing modules. -/
noncomputable def middleEquiv : dualizingModule G ≃ₗ[B] dualizingModule F := by
  letI : Algebra F.middle G.middle := r.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower A F.middle G.middle := IsScalarTower.of_algebraMap_eq fun a ↦
    (r.commutes a).symm
  letI : IsScalarTower F.middle G.middle B := IsScalarTower.of_algebraMap_eq fun c ↦ (hr c).symm
  letI : Module.Flat F.middle B := finiteOpenFactorization_flat F
  letI : Module.FinitePresentation F.middle G.middle :=
    Module.FinitePresentation.of_equiv
      { r.toLinearEquiv.toAddEquiv with
        map_smul' := fun c x ↦ by
          change r (c * x) = r c * r x
          rw [map_mul] }
  exact dualizingModule_commonChange (isPushout_middleEquiv F G r hr)

/-- `middleEquiv` restricts the functional of a pure tensor along the isomorphism. -/
theorem middleEquiv_tmul (φ : Module.Dual A G.middle) (b : B) :
    middleEquiv F G r hr (dualizingModule.tmul G φ b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
  let : Algebra F.middle G.middle := r.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower A F.middle G.middle := IsScalarTower.of_algebraMap_eq fun a ↦
    (r.commutes a).symm
  let : IsScalarTower F.middle G.middle B := IsScalarTower.of_algebraMap_eq fun c ↦ (hr c).symm
  let : Module.Flat F.middle B := finiteOpenFactorization_flat F
  let : Module.FinitePresentation F.middle G.middle :=
    Module.FinitePresentation.of_equiv
      { r.toLinearEquiv.toAddEquiv with
        map_smul' := fun c x ↦ by
          show r (c * x) = r c * r x
          rw [map_mul] }
  exact dualizingModule_commonChange_tmul (isPushout_middleEquiv F G r hr) φ b

/-- **The canonical element is carried along an isomorphism of intermediate algebras.** -/
theorem middleEquiv_traceCandidate [Module.Flat A B] [Module.FinitePresentation A F.middle]
    [Module.FinitePresentation A G.middle] :
    middleEquiv F G r hr (traceCandidate G) = traceCandidate F := by
  obtain ⟨ι, _, b, l, hl, hτ⟩ := exists_traceCandidate_eq_sum G
  rw [hτ, map_sum]
  simp only [middleEquiv_tmul]
  symm
  refine traceCandidate_eq_sum F b (fun i ↦ (l i).comp r.toLinearMap) fun c ↦ ?_
  simpa [hr] using hl (r c)

end MiddleEquiv

end dualizingModule

end Stacks.Discriminant
