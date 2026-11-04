module

public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Algebra.Module.InjectiveHull.FieldExtensionBaseChange

/-!
# Injective dimension of a field-extension base change of an injective module

Let `k ⊆ K` be an extension of fields, let `A` be a `k`-algebra of finite type and let `I` be an
injective `A`-module.  This file proves that the base change `A_K ⊗_A I` of `I` along
`A → A_K`, where `A_K = K ⊗_k A`, has *finite* injective dimension over `A_K`.

## Main results

* `Module.exists_hasInjectiveDimensionLE_tensorProduct_fieldExtension` — the base change
  `(K ⊗_k A) ⊗_A I` of an injective module `I` over a finite-type `k`-algebra `A` has finite
  injective dimension over `K ⊗_k A`.

## Implementation notes

Writing `A` as a quotient of a polynomial algebra `P = k[x_1, …, x_n]` turns the field extension
into a *finite* base change situation: `P` is Noetherian, `A` is a finite `P`-module, and
`S = P ⊗_k K` is a flat `P`-algebra isomorphic, as a ring, to `K[x_1, …, x_n]`.  Over the latter
every module has injective dimension at most `n` by
`Module.forall_hasInjectiveDimensionLE_mvPolynomial`, so the abstract flat base change bound
`Module.hasInjectiveDimensionLE_extendScalars_of_injective` applies with `d = n` and produces the
bound for `(S ⊗_P A) ⊗_A I`.

Two transports along ring isomorphisms turn this into the statement about `K ⊗_k A`.  The first,
`forall_hasInjectiveDimensionLE_of_ringEquiv`, moves the polynomial bound from `K[x_1, …, x_n]`
to `S`.  The second uses the chain of algebra isomorphisms
`S ⊗_P A ≃ A ⊗_P (P ⊗_k K) ≃ A ⊗_k K ≃ K ⊗_k A`, which is compatible with the two maps
`Algebra.TensorProduct.includeRight` out of `A`, together with `extendScalarsCongr`, which
promotes such a compatible ring isomorphism to a semilinear isomorphism of the two base changes
of `I`.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Transport of a universal injective-dimension bound along a ring isomorphism: if every module
over `R` has injective dimension at most `n` and `R ≃+* R'`, then every `R'`-module has injective
dimension at most `n`.  The `R'`-module `N` is viewed as an `R`-module through the isomorphism,
and the identity map is a semilinear isomorphism between the two. -/
private theorem forall_hasInjectiveDimensionLE_of_ringEquiv {R R' : Type u} [Ring R] [Ring R']
    (e : R ≃+* R') (n : ℕ) (h : ∀ M : ModuleCat.{u} R, HasInjectiveDimensionLE M n)
    (N : ModuleCat.{u} R') : HasInjectiveDimensionLE N n := by
  let M : ModuleCat.{u} R :=
    let _ := Module.compHom (N : Type u) e.toRingHom
    ModuleCat.of R (N : Type u)
  let eM : M ≃ₛₗ[RingHomClass.toRingHom e] N :=
    { AddEquiv.refl (N : Type u) with map_smul' := fun _ _ => rfl }
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv e eM n).mp (h M)

/-- A ring isomorphism `e : B₁ ≃+* B₂` which is compatible with two ring homomorphisms
`h₁ : A →+* B₁` and `h₂ : A →+* B₂` out of a common ring `A` induces an `e`-semilinear isomorphism
`B₁ ⊗_A M ≃ B₂ ⊗_A M` between the two extensions of scalars of an `A`-module `M`. -/
private noncomputable def extendScalarsCongr {A B₁ B₂ : Type u} [CommRing A] [CommRing B₁]
    [CommRing B₂] (h₁ : A →+* B₁) (h₂ : A →+* B₂) (e : B₁ ≃+* B₂)
    (he : ∀ a : A, e (h₁ a) = h₂ a) (M : ModuleCat.{u} A) :
    ((ModuleCat.extendScalars.{u, u, u} h₁).obj M : Type u) ≃ₛₗ[RingHomClass.toRingHom e]
      ((ModuleCat.extendScalars.{u, u, u} h₂).obj M : Type u) := by
  letI : Module B₁ (TensorProduct A
      ((ModuleCat.restrictScalars.{u, u, u} h₁).obj (ModuleCat.of B₁ B₁) : Type u)
      (M : Type u)) :=
    inferInstanceAs (Module B₁ ((ModuleCat.extendScalars.{u, u, u} h₁).obj M : Type u))
  letI : Module B₂ (TensorProduct A
      ((ModuleCat.restrictScalars.{u, u, u} h₂).obj (ModuleCat.of B₂ B₂) : Type u)
      (M : Type u)) :=
    inferInstanceAs (Module B₂ ((ModuleCat.extendScalars.{u, u, u} h₂).obj M : Type u))
  let eA : ((ModuleCat.restrictScalars.{u, u, u} h₁).obj (ModuleCat.of B₁ B₁) : Type u) ≃ₗ[A]
      ((ModuleCat.restrictScalars.{u, u, u} h₂).obj (ModuleCat.of B₂ B₂) : Type u) :=
    { e.toAddEquiv with
      map_smul' := fun a (b : B₁) => by
        change e (h₁ a * b) = h₂ a * e b
        rw [map_mul, he] }
  let t := TensorProduct.congr eA (LinearEquiv.refl A (M : Type u))
  have key : ∀ (b : B₁) (w : TensorProduct A
      ((ModuleCat.restrictScalars.{u, u, u} h₁).obj (ModuleCat.of B₁ B₁) : Type u) (M : Type u)),
      t (b • w) = e b • t w := by
    intro b w
    induction w using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b' m =>
      exact congrArg
        (fun z : ((ModuleCat.restrictScalars.{u, u, u} h₂).obj (ModuleCat.of B₂ B₂) : Type u) =>
          z ⊗ₜ m) (map_mul e b b')
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { t.toAddEquiv with map_smul' := key }

/-- The ring isomorphism `(P ⊗_k K) ⊗_P A ≃+* K ⊗_k A` used to identify the two base changes of
`A`: commute the outer factors, cancel the base change `P`, and commute again. -/
private noncomputable def baseChangeRingEquiv (k K A P : Type u) [CommRing k] [CommRing K]
    [CommRing A] [CommRing P] [Algebra k K] [Algebra k A] [Algebra k P] [Algebra P A]
    [IsScalarTower k P A] :
    TensorProduct P (TensorProduct k P K) A ≃+* TensorProduct k K A :=
  (Algebra.TensorProduct.comm P (TensorProduct k P K) A).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k P P A K).toRingEquiv.trans
      (Algebra.TensorProduct.comm k A K).toRingEquiv)

/-- The isomorphism `baseChangeRingEquiv` is compatible with the two inclusions of `A` as the right
tensor factor: it sends `1 ⊗ₜ a` to `1 ⊗ₜ a`. -/
private lemma baseChangeRingEquiv_includeRight (k K A P : Type u) [CommRing k] [CommRing K]
    [CommRing A] [CommRing P] [Algebra k K] [Algebra k A] [Algebra k P] [Algebra P A]
    [IsScalarTower k P A] (a : A) :
    baseChangeRingEquiv k K A P
        ((Algebra.TensorProduct.includeRight :
          A →ₐ[P] TensorProduct P (TensorProduct k P K) A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k K A) a := by
  simp [baseChangeRingEquiv, Algebra.TensorProduct.one_def]

/-- **Stacks-style base change of injectives along a field extension.** Let `k ⊆ K` be an
extension of fields and let `A` be a `k`-algebra of finite type.  For every injective `A`-module
`I` the base change `A_K ⊗_A I`, where `A_K = K ⊗_k A`, has finite injective dimension
over `A_K`. -/
public theorem Module.exists_hasInjectiveDimensionLE_tensorProduct_fieldExtension
    {k K A : Type u} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (I : ModuleCat.{u} A) [CategoryTheory.Injective I] :
    ∃ n : ℕ, HasInjectiveDimensionLE
      ((ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k K A).toRingHom).obj I) n := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := A)).mp
    inferInstance
  let P := MvPolynomial (Fin n) k
  let _ : Algebra P A := f.toRingHom.toAlgebra
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hf
  refine ⟨n, ?_⟩
  -- Over `S = P ⊗_k K`, which is a polynomial ring over `K`, every module has dimension `≤ n`.
  have hSdim : ∀ Y : ModuleCat.{u} (TensorProduct k P K), HasInjectiveDimensionLE Y n :=
    forall_hasInjectiveDimensionLE_of_ringEquiv
      (((Algebra.TensorProduct.comm k P K).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv).symm) n
      (Module.forall_hasInjectiveDimensionLE_mvPolynomial K n)
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_semiLinearEquiv _
    (extendScalarsCongr _ _ (baseChangeRingEquiv k K A P)
      (baseChangeRingEquiv_includeRight k K A P) I) n).mp
    (Module.hasInjectiveDimensionLE_extendScalars_of_injective
      (R := P) (S := TensorProduct k P K) (A := A) n hSdim I)

end
