module

public import StacksFrontier.AlgebraicGeometry.Sites.GaloisDescentFppf
public import StacksFrontier.FieldTheory.GaloisTensorProduct
public import StacksFrontier.RingTheory.AdjoinRoot.LocalRing
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# Lifting a finite Galois extension of the residue field of a nilpotent local ring

Let `A` be a local ring with residue field `k` and let `K / k` be a finite separable extension.
Choose a primitive element `α` of `K / k` (`Field.powerBasisOfFiniteOfSeparable`) and a monic lift
`f ∈ A[X]` of its minimal polynomial, of the same degree. The monogenic algebra
`Lift A K = A[X] ⧸ (f)` is the étale lift of `K` to `A`:

* it is local, with maximal ideal `𝔪_A · Lift A K`
  (`AdjoinRoot.isLocalRing_of_irreducible_map_residue`), free and finite over `A`, étale over `A`
  (the reduction of `f` is separable, so `f'` is a unit),
  hence finitely presented, and faithfully flat over `A` (free of positive rank); Artinian when `A`
  is;
* `x ↦ α` identifies its residue field with `K` over `k` (`residueFieldEquiv`).

When the maximal ideal of `A` is nilpotent (for instance `A` Artinian local:
`isArtinianRing_iff_isNilpotent_maximalIdeal`), so is that of `Lift A K`, and formal étaleness
lifts every `A`-algebra endomorphism of the residue field uniquely to `Lift A K`. This gives the
action `galoisAction : Gal(K/k) →* (Lift A K ≃ₐ[A] Lift A K)`, reducing to the Galois action on
`K`. When moreover `K / k` is Galois:

* `Lift A K` is a **Galois covering** of `A` with group `G = Gal(K/k)`: the map
  `b ⊗ b' ↦ (σ ↦ b · σ b')` is an isomorphism `Lift A K ⊗[A] Lift A K ≃ (G → Lift A K)`
  (`galoisTensorEquiv`). It is surjective by Nakayama, since modulo the maximal ideal it is the
  isomorphism `K ⊗[k] K ≃ (G → K)` of `IsGalois.tensorProductEquivPi`, and then injective because
  source and target are free of the same rank `[K : k] = #G` over `Lift A K`;
* there is `c` with `∑ σ, σ c = 1` (`exists_sum_galoisAction_eq_one`): lift an element of trace
  one and divide by the resulting `G`-invariant unit.

These are the ring-theoretic inputs for the Galois-descent step in the proof of Stacks 07XW; none
of them is itself a Stacks tag, so nothing here is registered.

## Main definitions

* `Stacks.ArtinianGaloisLift.Lift`: the étale lift `A[X] ⧸ (f)` of `K`.
* `Stacks.ArtinianGaloisLift.residueFieldEquiv`: its residue field is `K`, over `k`.
* `Stacks.ArtinianGaloisLift.liftResidueAut`: for any formally étale local `A`-algebra `B` with
  nilpotent maximal ideal, the unique lifting `Aut_A(κ(B)) →* Aut_A(B)`.
* `Stacks.ArtinianGaloisLift.galoisAction`: the lifted action of `Gal(K/k)`.
* `Stacks.ArtinianGaloisLift.galoisTensorEquiv`: `Lift A K ⊗[A] Lift A K ≃ (G → Lift A K)`.

## Main results

* `Stacks.ArtinianGaloisLift.finrank_lift`: `Lift A K` is free of rank `[K : k]` over `A`.
* `Stacks.ArtinianGaloisLift.toField_galoisAction` and `Stacks.ArtinianGaloisLift.eq_galoisAction`:
  the lifted action reduces to `σ`, and is the only action doing so.
* `Stacks.ArtinianGaloisLift.bijective_galoisTensorPi`: the Galois condition, in the spelling
  `Function.Bijective (AlgebraicGeometry.galoisTensorPi ρ)` consumed by the fppf Galois descent of
  `StacksFrontier.AlgebraicGeometry.Sites.GaloisDescentFppf`.
* `Stacks.ArtinianGaloisLift.exists_sum_galoisAction_eq_one`: an element of trace one.

## Implementation notes

`Algebra.FinitePresentation A (Lift A K)` and `Module.FaithfullyFlat A (Lift A K)` are not stated
separately: they are found by `inferInstance`, from `Algebra.Etale.finitePresentation` and from
Mathlib's instance for a nontrivial free module.

The construction itself only needs `A` local and `K / k` finite separable; nilpotence of the
maximal ideal enters with the Galois action, and `IsGalois` only in the last section. That section
takes `K` in the universe of `A`, because `IsGalois.bijective_tensorProductPi` puts `k` and `K` in
one universe.
-/

@[expose] public section

noncomputable section

open Polynomial IsLocalRing AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace Stacks.ArtinianGaloisLift

section Construction

variable (A : Type u) [CommRing A] [IsLocalRing A] (K : Type v) [Field K]
  [Algebra (ResidueField A) K] [FiniteDimensional (ResidueField A) K]
  [Algebra.IsSeparable (ResidueField A) K]

/-- The minimal polynomial of the primitive element of `K / k` lifts to a monic polynomial over
`A` of the same degree `[K : k]`. -/
theorem exists_monic_lift_minpoly :
    ∃ f : A[X], f.map (residue A) =
        minpoly (ResidueField A) (Field.powerBasisOfFiniteOfSeparable (ResidueField A) K).gen ∧
      f.natDegree = Module.finrank (ResidueField A) K ∧ f.Monic := by
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) K
  obtain ⟨f, hf, hdeg, hmon⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts _).2 (map_surjective _ residue_surjective _)) (minpoly.monic pb.isIntegral_gen)
  exact ⟨f, hf, by rw [hdeg, pb.natDegree_minpoly, pb.finrank], hmon⟩

/-- A monic lift to `A[X]` of the minimal polynomial over `k` of the primitive element
`(Field.powerBasisOfFiniteOfSeparable k K).gen` of `K`, of degree `[K : k]`. -/
def liftPoly : A[X] := (exists_monic_lift_minpoly A K).choose

/-- `liftPoly A K` reduces to the minimal polynomial of the primitive element. -/
theorem map_liftPoly : (liftPoly A K).map (residue A) =
    minpoly (ResidueField A) (Field.powerBasisOfFiniteOfSeparable (ResidueField A) K).gen :=
  (exists_monic_lift_minpoly A K).choose_spec.1

/-- `liftPoly A K` has degree `[K : k]`. -/
theorem natDegree_liftPoly :
    (liftPoly A K).natDegree = Module.finrank (ResidueField A) K :=
  (exists_monic_lift_minpoly A K).choose_spec.2.1

/-- `liftPoly A K` is monic. -/
theorem monic_liftPoly : (liftPoly A K).Monic :=
  (exists_monic_lift_minpoly A K).choose_spec.2.2

/-- The reduction of `liftPoly A K` is irreducible. -/
theorem irreducible_map_liftPoly : Irreducible ((liftPoly A K).map (residue A)) := by
  rw [map_liftPoly]
  exact minpoly.irreducible (Field.powerBasisOfFiniteOfSeparable _ K).isIntegral_gen

/-- The reduction of `liftPoly A K` is separable. -/
theorem separable_map_liftPoly : ((liftPoly A K).map (residue A)).Separable := by
  rw [map_liftPoly]
  exact Algebra.IsSeparable.isSeparable _ _

/-- **The étale lift of `K` to `A`**: the monogenic `A`-algebra `A[X] ⧸ (f)` for the monic lift
`f = liftPoly A K` of the minimal polynomial of a primitive element of `K / k`. -/
abbrev Lift : Type u := AdjoinRoot (liftPoly A K)

/-- `Lift A K` is local, since the reduction of `f` is irreducible. -/
instance : IsLocalRing (Lift A K) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue (monic_liftPoly A K)
    (irreducible_map_liftPoly A K)

/-- `A → Lift A K` is a local ring map. -/
instance : IsLocalHom (algebraMap A (Lift A K)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic (monic_liftPoly A K)

/-- `Lift A K` is free over `A` (of rank `[K : k]`, see `AdjoinRoot.powerBasis'`). -/
instance : Module.Free A (Lift A K) := (monic_liftPoly A K).free_adjoinRoot

/-- `Lift A K` is finite over `A`. -/
instance : Module.Finite A (Lift A K) := (monic_liftPoly A K).finite_adjoinRoot

/-- `Lift A K` is étale over `A`: the reduction of `f` is separable, so `f'` is a unit in it. -/
instance : Algebra.Etale A (Lift A K) :=
  Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot_of_separable (monic_liftPoly A K)
    (irreducible_map_liftPoly A K) (separable_map_liftPoly A K)

/-- `Lift A K` is free over `A` of rank `[K : k]`. -/
theorem finrank_lift : Module.finrank A (Lift A K) = Module.finrank (ResidueField A) K := by
  rw [(AdjoinRoot.powerBasis' (monic_liftPoly A K)).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_liftPoly]

/-- `Lift A K` is Artinian when `A` is, being finite over it. -/
instance [IsArtinianRing A] : IsArtinianRing (Lift A K) := .of_finite A _

/-- The surjection `Lift A K → K` over `A → k`, sending the root to the primitive element. Its
kernel is the maximal ideal (`ker_toField`), and it induces `residueFieldEquiv`. -/
def toField : Lift A K →+* K :=
  AdjoinRoot.lift ((algebraMap (ResidueField A) K).comp (residue A))
    (Field.powerBasisOfFiniteOfSeparable (ResidueField A) K).gen (by
      rw [← eval₂_map, map_liftPoly, ← aeval_def, minpoly.aeval])

/-- `toField` restricted to `A` is the residue map followed by `k → K`. -/
@[simp]
theorem toField_algebraMap (a : A) :
    toField A K (algebraMap A (Lift A K) a) = algebraMap (ResidueField A) K (residue A a) := by
  rw [AdjoinRoot.algebraMap_eq, toField, AdjoinRoot.lift_of, RingHom.comp_apply]

/-- `toField` sends the root to the primitive element. -/
@[simp]
theorem toField_root :
    toField A K (AdjoinRoot.root (liftPoly A K)) =
      (Field.powerBasisOfFiniteOfSeparable (ResidueField A) K).gen :=
  AdjoinRoot.lift_root _

/-- `toField` is surjective: `K = k[α]`. -/
theorem toField_surjective : Function.Surjective (toField A K) := by
  intro y
  obtain ⟨p, rfl⟩ := (Field.powerBasisOfFiniteOfSeparable (ResidueField A) K).exists_eq_aeval' y
  obtain ⟨q, rfl⟩ := map_surjective _ residue_surjective p
  exact ⟨AdjoinRoot.mk _ q, by rw [toField, AdjoinRoot.lift_mk, aeval_def, eval₂_map]⟩

/-- The kernel of `toField` is the maximal ideal of `Lift A K`. -/
theorem ker_toField : RingHom.ker (toField A K) = maximalIdeal (Lift A K) :=
  (IsLocalRing.isMaximal_iff _).mp (RingHom.ker_isMaximal_of_surjective _ (toField_surjective A K))

/-- **The residue field of `Lift A K` is `K`**, as a `k`-algebra: the isomorphism induced by
`toField`. -/
def residueFieldEquiv : ResidueField (Lift A K) ≃ₐ[ResidueField A] K :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (ker_toField A K).symm).trans
      (RingHom.quotientKerEquivOfSurjective (toField_surjective A K))) (by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue]
    exact toField_algebraMap A K a)

/-- `residueFieldEquiv` on residues is `toField`. -/
@[simp]
theorem residueFieldEquiv_residue (b : Lift A K) :
    residueFieldEquiv A K (residue _ b) = toField A K b :=
  rfl

end Construction

section ResidueLift

/-! ### Lifting residue automorphisms to a formally étale local algebra -/

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [Algebra.FormallyEtale A B] (hB : IsNilpotent (maximalIdeal B))

/-- The unique lift `B →ₐ[A] B` of an `A`-algebra endomorphism `φ` of the residue field of a
formally étale local `A`-algebra `B` with nilpotent maximal ideal: the `A`-algebra map lifting
`φ ∘ residue` along the nilpotent thickening `B → κ(B)`. It exists because `B` is formally smooth,
and it is unique because `B` is formally unramified (`eq_liftResidueEnd`). -/
def liftResidueEnd (φ : ResidueField B →ₐ[A] ResidueField B) : B →ₐ[A] B :=
  Algebra.FormallySmooth.liftOfSurjective (φ.comp (IsScalarTower.toAlgHom A B _))
    (IsScalarTower.toAlgHom A B _) residue_surjective (by rwa [IsScalarTower.coe_toAlgHom,
      ResidueField.algebraMap_eq, ker_residue])

/-- `liftResidueEnd hB φ` reduces to `φ`. -/
theorem residue_liftResidueEnd (φ : ResidueField B →ₐ[A] ResidueField B) (b : B) :
    residue B (liftResidueEnd hB φ b) = φ (residue B b) :=
  Algebra.FormallySmooth.liftOfSurjective_apply (φ.comp (IsScalarTower.toAlgHom A B _))
    (IsScalarTower.toAlgHom A B _) residue_surjective _ b

/-- **Uniqueness of the lift**: an `A`-algebra endomorphism of `B` reducing to `φ` is
`liftResidueEnd hB φ`. -/
theorem eq_liftResidueEnd (φ : ResidueField B →ₐ[A] ResidueField B) (ψ : B →ₐ[A] B)
    (h : ∀ b, residue B (ψ b) = φ (residue B b)) : ψ = liftResidueEnd hB φ :=
  Algebra.FormallyUnramified.ext' (residue B) (by rwa [ker_residue]) _ _
    fun b => by rw [h, residue_liftResidueEnd]

/-- The lift of the identity is the identity. -/
theorem liftResidueEnd_id : liftResidueEnd hB (AlgHom.id A (ResidueField B)) = AlgHom.id A B :=
  (eq_liftResidueEnd hB _ _ fun _ => rfl).symm

/-- Lifting is compatible with composition. -/
theorem liftResidueEnd_comp (φ ψ : ResidueField B →ₐ[A] ResidueField B) :
    liftResidueEnd hB (φ.comp ψ) = (liftResidueEnd hB φ).comp (liftResidueEnd hB ψ) :=
  (eq_liftResidueEnd hB _ _ fun b => by simp [residue_liftResidueEnd]).symm

/-- **The `A`-algebra automorphisms of the residue field lift uniquely**: the group homomorphism
`Aut_A(κ(B)) →* Aut_A(B)` sending `φ` to its unique lift, for `B` a formally étale local
`A`-algebra with nilpotent maximal ideal. -/
def liftResidueAut : (ResidueField B ≃ₐ[A] ResidueField B) →* (B ≃ₐ[A] B) where
  toFun φ := AlgEquiv.ofAlgHom (liftResidueEnd hB φ.toAlgHom) (liftResidueEnd hB φ.symm.toAlgHom)
    (by rw [← liftResidueEnd_comp, AlgEquiv.comp_symm, liftResidueEnd_id])
    (by rw [← liftResidueEnd_comp, AlgEquiv.symm_comp, liftResidueEnd_id])
  map_one' := AlgEquiv.ext fun b => congr($(liftResidueEnd_id hB) b)
  map_mul' φ ψ := AlgEquiv.ext fun b =>
    congr($(liftResidueEnd_comp hB φ.toAlgHom ψ.toAlgHom) b)

/-- `liftResidueAut hB φ` reduces to `φ`. -/
theorem residue_liftResidueAut (φ : ResidueField B ≃ₐ[A] ResidueField B) (b : B) :
    residue B (liftResidueAut hB φ b) = φ (residue B b) :=
  residue_liftResidueEnd hB φ.toAlgHom b

end ResidueLift

section Action

/-! ### The lifted Galois action -/

variable {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsNilpotent (maximalIdeal A))
  (K : Type v) [Field K] [Algebra (ResidueField A) K] [FiniteDimensional (ResidueField A) K]
  [Algebra.IsSeparable (ResidueField A) K]

include hA in
/-- The maximal ideal of `Lift A K` is nilpotent when that of `A` is, being its extension. -/
theorem isNilpotent_maximalIdeal_lift : IsNilpotent (maximalIdeal (Lift A K)) := by
  obtain ⟨n, hn⟩ := hA
  refine ⟨n, ?_⟩
  rw [AdjoinRoot.maximalIdeal_eq_map_maximalIdeal (irreducible_map_liftPoly A K), ← Ideal.map_pow,
    hn]
  exact Ideal.map_bot

/-- **The lifted Galois action.** `σ ∈ Gal(K/k)` acts on `Lift A K` by the unique `A`-algebra
automorphism reducing to `σ` under `residueFieldEquiv` (`toField_galoisAction`). -/
def galoisAction : (K ≃ₐ[ResidueField A] K) →* (Lift A K ≃ₐ[A] Lift A K) :=
  (liftResidueAut (isNilpotent_maximalIdeal_lift hA K)).comp ((AlgEquiv.restrictScalarsHom A).comp
    (AlgEquiv.autCongr (residueFieldEquiv A K).symm).toMonoidHom)

/-- **The lifted action reduces to the Galois action**: `toField ∘ σ̃ = σ ∘ toField`. -/
theorem toField_galoisAction (σ : K ≃ₐ[ResidueField A] K) (b : Lift A K) :
    toField A K (galoisAction hA K σ b) = σ (toField A K b) := by
  rw [← residueFieldEquiv_residue, galoisAction, MonoidHom.comp_apply, residue_liftResidueAut]
  simp

/-- **Uniqueness of the lifted action**: an `A`-algebra endomorphism of `Lift A K` reducing to `σ`
under `toField` is `galoisAction hA K σ`. -/
theorem eq_galoisAction (σ : K ≃ₐ[ResidueField A] K) (ψ : Lift A K →ₐ[A] Lift A K)
    (h : ∀ b, toField A K (ψ b) = σ (toField A K b)) : ψ = (galoisAction hA K σ).toAlgHom :=
  Algebra.FormallyUnramified.ext' (toField A K)
    (by rw [ker_toField]; exact isNilpotent_maximalIdeal_lift hA K) _ _
    fun b => by rw [h, AlgEquiv.coe_toAlgHom, toField_galoisAction]

end Action

section Galois

/-- A vector of `ι → R` whose entries all lie in `I` lies in `I • ⊤`. -/
theorem mem_smul_top_pi_of_forall_mem {R ι : Type*} [CommRing R] [Finite ι] {I : Ideal R}
    (u : ι → R) (hu : ∀ i, u i ∈ I) : u ∈ I • (⊤ : Submodule R (ι → R)) := by
  classical
  have := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single u]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : Pi.single i (u i) = u i • (Pi.single i 1 : ι → R) := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [this]
  exact Submodule.smul_mem_smul (hu i) trivial

variable {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsNilpotent (maximalIdeal A))
  (K : Type u) [Field K] [Algebra (ResidueField A) K] [FiniteDimensional (ResidueField A) K]
  [IsGalois (ResidueField A) K]

/-- `galoisTensorPi (galoisAction hA K)` is surjective: modulo the maximal ideal of `Lift A K` its
image contains the image of `K ⊗[k] K → (G → K)`, which is everything
(`IsGalois.bijective_tensorProductPi`), so Nakayama applies to the finite module `G → Lift A K`. -/
theorem surjective_galoisTensorPi : Function.Surjective (galoisTensorPi (galoisAction hA K)) := by
  classical
  let N : Submodule (Lift A K) ((K ≃ₐ[ResidueField A] K) → Lift A K) :=
    LinearMap.range (galoisTensorPi (galoisAction hA K)).toLinearMap
  have hred : ∀ t : K ⊗[ResidueField A] K, ∃ n ∈ N,
      ∀ σ, toField A K (n σ) = IsGalois.tensorProductPi (ResidueField A) K t σ := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨b, rfl⟩ := toField_surjective A K x
      obtain ⟨b', rfl⟩ := toField_surjective A K y
      exact ⟨_, LinearMap.mem_range_self _ (b ⊗ₜ b'), fun σ => by
        simp [toField_galoisAction]⟩
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨n₁, hn₁, h₁⟩ := h₁
      obtain ⟨n₂, hn₂, h₂⟩ := h₂
      exact ⟨n₁ + n₂, N.add_mem hn₁ hn₂, fun σ => by simp [h₁, h₂]⟩
  have htop : (⊤ : Submodule (Lift A K) ((K ≃ₐ[ResidueField A] K) → Lift A K)) ≤
      N ⊔ maximalIdeal (Lift A K) • ⊤ := by
    intro v _
    obtain ⟨t, ht⟩ := (IsGalois.bijective_tensorProductPi (ResidueField A) K).2
      (fun σ => toField A K (v σ))
    obtain ⟨n, hn, h⟩ := hred t
    rw [show v = n + (v - n) by abel]
    refine Submodule.add_mem_sup hn (mem_smul_top_pi_of_forall_mem _ fun σ => ?_)
    rw [← ker_toField, RingHom.mem_ker, Pi.sub_apply, map_sub, h, ht, sub_self]
  intro v
  exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge htop (Submodule.mem_top (x := v))

/-- `galoisTensorPi (galoisAction hA K)` is injective: it is a surjection between free
`Lift A K`-modules of the same finite rank `[K : k] = #G`. -/
theorem injective_galoisTensorPi : Function.Injective (galoisTensorPi (galoisAction hA K)) := by
  have hcard : Nat.card (K ≃ₐ[ResidueField A] K) =
      (AdjoinRoot.powerBasis' (monic_liftPoly A K)).dim := by
    rw [IsGalois.card_aut_eq_finrank, AdjoinRoot.powerBasis'_dim, natDegree_liftPoly]
  let e : (Lift A K ⊗[A] Lift A K) ≃ₗ[Lift A K] ((K ≃ₐ[ResidueField A] K) → Lift A K) :=
    (Algebra.TensorProduct.basis (Lift A K)
      (AdjoinRoot.powerBasis' (monic_liftPoly A K)).basis).equiv (Pi.basisFun _ _)
      (Finite.equivFinOfCardEq hcard).symm
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap
    (galoisTensorPi (galoisAction hA K)).toLinearMap e.injective (surjective_galoisTensorPi hA K)

/-- **The Galois condition.** `b ⊗ b' ↦ (σ ↦ b · σ̃ b')` is a bijection
`Lift A K ⊗[A] Lift A K → (Gal(K/k) → Lift A K)`. -/
theorem bijective_galoisTensorPi : Function.Bijective (galoisTensorPi (galoisAction hA K)) :=
  ⟨injective_galoisTensorPi hA K, surjective_galoisTensorPi hA K⟩

/-- **`Lift A K` is a Galois covering of `A` with group `Gal(K/k)`**: the isomorphism
`Lift A K ⊗[A] Lift A K ≃ₐ (Gal(K/k) → Lift A K)`, `b ⊗ b' ↦ (σ ↦ b · σ̃ b')`. -/
def galoisTensorEquiv :
    Lift A K ⊗[A] Lift A K ≃ₐ[Lift A K] ((K ≃ₐ[ResidueField A] K) → Lift A K) :=
  AlgEquiv.ofBijective _ (bijective_galoisTensorPi hA K)

/-- **An element of trace one.** There is `c ∈ Lift A K` with `∑ σ, σ̃ c = 1`: lift `y ∈ K` with
`Tr_{K/k} y = 1`, so that `s = ∑ σ, σ̃ (lift y)` reduces to `1` and is a `G`-invariant unit, and
take `c = s⁻¹ · lift y`. -/
theorem exists_sum_galoisAction_eq_one :
    ∃ c : Lift A K, ∑ σ : K ≃ₐ[ResidueField A] K, galoisAction hA K σ c = 1 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ResidueField A) K 1
  have hy' : ∑ σ : K ≃ₐ[ResidueField A] K, σ y = 1 := by
    rw [← trace_eq_sum_automorphisms, hy, map_one]
  obtain ⟨b, rfl⟩ := toField_surjective A K y
  set s := ∑ σ : K ≃ₐ[ResidueField A] K, galoisAction hA K σ b with hs_def
  have hs : toField A K s = 1 := by simp [s, map_sum, toField_galoisAction, hy']
  obtain ⟨u, hu⟩ : IsUnit s := by
    rw [← residue_ne_zero_iff_isUnit, ← (residueFieldEquiv A K).injective.ne_iff, map_zero,
      residueFieldEquiv_residue, hs]
    exact one_ne_zero
  have hinv (τ : K ≃ₐ[ResidueField A] K) : galoisAction hA K τ s = s := by
    rw [hs_def, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by
      rw [Equiv.coe_mulLeft, map_mul, AlgEquiv.mul_apply]
  have hinv' (τ : K ≃ₐ[ResidueField A] K) : galoisAction hA K τ ↑u⁻¹ = ↑u⁻¹ := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    conv_lhs => rw [hu, ← hinv τ, ← hu, ← map_mul, Units.mul_inv, map_one]
  refine ⟨↑u⁻¹ * b, ?_⟩
  simp only [map_mul, hinv', ← Finset.mul_sum, ← hs_def, ← hu, Units.inv_mul]

end Galois

end Stacks.ArtinianGaloisLift
