module

public import StacksFrontier.RingTheory.AdicCompletion.SectionsAlgebra
public import StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence
public import StacksFrontier.RingTheory.BeauvilleLaszlo.Surjectivity
import all StacksFrontier.RingTheory.BeauvilleLaszlo.ModuleEquivalence

/-!
# The Beauville--Laszlo theorem for algebras

Let `(R → S, f)` be a Beauville--Laszlo glueing pair, let `A₁` be an `R_f`-algebra, let `A'` be
an `S`-algebra and let `α : A'_f ≅ S ⊗[R] A₁` be an isomorphism of `S`-algebras. Then `A'` and
`A₁` glue: there is an `R`-algebra `A` together with isomorphisms of algebras `A_f ≅ A₁` and
`S ⊗[R] A ≅ A'` that are compatible with `α`.

The glued algebra is the ring-theoretic fibre product `A' ×_{A'_f} A₁`.

## Main results

* `BeauvilleLaszlo.exists_glued_algebra`: the glueing theorem for algebras, as above. The
  compatibility with `α` is recorded as the equality
  `α ((e' (1 ⊗ a))/1) = 1 ⊗ e₁ (a/1)` for every `a : A`, where `e₁` and `e'` are the two
  isomorphisms; the two structure maps `A → A'` and `A → A₁` are exactly
  `a ↦ e' (1 ⊗ a)` and `a ↦ e₁ (a/1)`.

## References

* [Beauville--Laszlo]
* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0BP3](https://stacks.math.columbia.edu/tag/0BP3)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

namespace BeauvilleLaszlo

open scoped TensorProduct

universe u v w

/-- **Beauville--Laszlo glueing for algebras.** Let `(R → S, f)` be a glueing pair, let `A₁` be
an `R_f`-algebra, let `A'` be an `S`-algebra and let `α : A'_f ≅ S ⊗[R] A₁` be an isomorphism of
`S`-algebras. Then there is an `R`-algebra `A` together with isomorphisms of algebras
`A_f ≅ A₁` and `S ⊗[R] A ≅ A'` compatible with `α`, in the sense that the two structure maps
`a ↦ e' (1 ⊗ a)` into `A'` and `a ↦ e₁ (a/1)` into `A₁` are identified by `α`. -/
theorem exists_glued_algebra
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] (f : R)
    (hglue : IsGlueingPair (algebraMap R S) f)
    (A' : Type w) [CommRing A'] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
    (A₁ : Type w) [CommRing A₁] [Algebra R A₁]
    [Algebra (Localization.Away f) A₁] [IsScalarTower R (Localization.Away f) A₁]
    (α : Localization.Away (algebraMap R A' f) ≃ₐ[S] S ⊗[R] A₁) :
    ∃ (A : Type w) (_ : CommRing A) (_ : Algebra R A)
      (e₁ : Localization.Away (algebraMap R A f) ≃ₐ[R] A₁)
      (e' : S ⊗[R] A ≃ₐ[S] A'),
      ∀ a : A,
        α (algebraMap A' (Localization.Away (algebraMap R A' f)) (e' (1 ⊗ₜ[R] a))) =
          1 ⊗ₜ[R] e₁ (algebraMap A (Localization.Away (algebraMap R A f)) a) := by
  have h1 : IsLocalizedModule (Submonoid.powers (algebraMap S A' (algebraMap R S f)))
      (Algebra.linearMap A' (Localization.Away (algebraMap R A' f))) := by
    rw [← IsScalarTower.algebraMap_apply R S A' f]
    exact isLocalizedModule_iff_isLocalization.mpr inferInstance
  have h2 : IsLocalizedModule (Submonoid.powers (algebraMap R S f))
      ((Algebra.linearMap A' (Localization.Away (algebraMap R A' f))).restrictScalars S) :=
    IsLocalizedModule.restrictScalars_powers (algebraMap R S f) _
  let β : LocalizedModule.Away (algebraMap R S f) A' ≃ₗ[S]
      Localization.Away (algebraMap R A' f) :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S f))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S f)) A')
      ((Algebra.linearMap A' (Localization.Away (algebraMap R A' f))).restrictScalars S)
  have hβ : ∀ a : A', β (LocalizedModule.mk a 1) =
      algebraMap A' (Localization.Away (algebraMap R A' f)) a :=
    fun a ↦ IsLocalizedModule.linearEquiv_apply _ _ _ a
  let αm : LocalizedModule.Away (algebraMap R S f) A' ≃ₗ[S] S ⊗[R] A₁ :=
    β.trans α.toLinearEquiv
  let φ : (A' × A₁) →ₐ[R] S ⊗[R] A₁ :=
    ((α.toAlgHom.restrictScalars R).comp
      ((Algebra.ofId A' (Localization.Away (algebraMap R A' f))).restrictScalars R)).comp
      (AlgHom.fst R A' A₁)
  let ψ : (A' × A₁) →ₐ[R] S ⊗[R] A₁ :=
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A₁)).comp (AlgHom.snd R A' A₁)
  let Asub : Subalgebra R (A' × A₁) := AlgHom.equalizer φ ψ
  have hmem : ∀ x : A' × A₁, x ∈ Asub ↔ x ∈ kernel f αm := by
    intro x
    rw [AlgHom.mem_equalizer, LinearMap.mem_ker]
    show α (algebraMap A' (Localization.Away (algebraMap R A' f)) x.1) = 1 ⊗ₜ[R] x.2 ↔ _
    rw [show difference f αm x =
        LocalizedModule.mk x.1 1 - αm.symm (1 ⊗ₜ[R] x.2) from rfl, sub_eq_zero,
      LinearEquiv.eq_symm_apply]
    show _ ↔ α (β (LocalizedModule.mk x.1 1)) = _
    rw [hβ]
  let E : Asub ≃ₗ[R] kernel f αm :=
    { toFun := fun x ↦ ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x ↦ ⟨x.1, (hmem x.1).2 x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let q : S ⊗[R] Asub →ₐ[S] A' :=
    Algebra.TensorProduct.lift (Algebra.ofId S A')
      ((AlgHom.fst R A' A₁).comp Asub.val) fun _ _ ↦ mul_comm _ _
  have hq : Function.Bijective q := by
    have hfun : (q : S ⊗[R] Asub → A') =
        (extendScalars (S := S) (genericProjection f αm)) ∘
          (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) E) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
        show (Algebra.ofId S A') s * (a : A' × A₁).1 = s • (a : A' × A₁).1
        rw [Algebra.smul_def]
        rfl
      | add x y hx hy => simp only [map_add, Function.comp_apply, hx, hy]
    rw [hfun]
    exact (genericProjection_baseChange_bijective f αm hglue.1 hglue.2).comp
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) E).bijective
  let h : Asub →ₐ[R] A₁ := (AlgHom.snd R A' A₁).comp Asub.val
  let l : Asub →ₐ[R] Localization.Away (algebraMap R Asub f) :=
    (Algebra.ofId Asub (Localization.Away (algebraMap R Asub f))).restrictScalars R
  have : IsLocalizedModule (Submonoid.powers f) l.toLinearMap :=
    IsLocalizedModule.restrictScalars_powers f
      (Algebra.linearMap Asub (Localization.Away (algebraMap R Asub f)))
  have := localProjection_isLocalizedModule f αm
  have : IsLocalizedModule (Submonoid.powers f) h.toLinearMap :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f) (localProjection f αm) E
  let eL : Localization.Away (algebraMap R Asub f) ≃ₗ[R] A₁ :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f) l.toLinearMap h.toLinearMap
  have heL : ∀ a : Asub, eL (l a) = h a :=
    fun a ↦ IsLocalizedModule.linearEquiv_apply _ _ _ a
  let e₁ : Localization.Away (algebraMap R Asub f) ≃ₐ[R] A₁ :=
    AlgEquiv.ofLinearEquiv eL (by simpa using heL 1)
      (map_mul_of_isLocalizedModule (Submonoid.powers f) l eL.toLinearMap h heL
        (IsLocalizedModule.map_units h.toLinearMap))
  refine ⟨Asub, inferInstance, inferInstance, e₁, AlgEquiv.ofBijective q hq, fun a ↦ ?_⟩
  show α (algebraMap A' _ ((Algebra.ofId S A') 1 * (a : A' × A₁).1)) = 1 ⊗ₜ[R] e₁ (l a)
  rw [map_one, one_mul, show e₁ (l a) = h a from heL a]
  exact (AlgHom.mem_equalizer φ ψ _).1 a.2

end BeauvilleLaszlo

end
