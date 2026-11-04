module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.UniversalProperty
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Unramified stages from an idempotent diagonal kernel of a completed tensor square

Let `A → B` be a ring map with `B` a linearly topologized topological ring, and let
`μ : B ⊗̂_A B → B` be a continuous ring map restricting to the identity on both factors. If the
kernel of `μ` is idempotent, then every quotient `B ⧸ K` by an open ideal is formally unramified
over `A ⧸ I`, for every ideal `I` of `A` mapping into `K`.

The kernel of the multiplication `S ⊗_{A ⧸ I} S → S`, `S = B ⧸ K`, is the image of the kernel of
`μ` under the ring map `B ⊗̂_A B → S ⊗_{A ⧸ I} S` induced by the two projections `B → S`; the
image of an idempotent ideal under a surjective ring map is idempotent, and the module of
Kähler differentials is the conormal module of that kernel.

## Main results

* `TopologicalRing.formallyUnramified_quotient_of_isIdempotentElem_ker`: the statement above.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TopologicalRing

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace B]
  [IsTopologicalRing B] [IsLinearTopology B B]

omit [Algebra A B] [IsLinearTopology B B] in
/-- A map out of a topological ring into a discrete space which is constant on the cosets of an
open ideal is continuous. -/
theorem continuous_of_add_mem_eq {T : Type*} [TopologicalSpace T] [DiscreteTopology T]
    (f : B → T) (K : Ideal B) (hK : IsOpen (K : Set B))
    (hf : ∀ b k, k ∈ K → f (b + k) = f b) : Continuous f := by
  refine continuous_def.mpr fun V _ => isOpen_iff_forall_mem_open.mpr fun b hb => ?_
  refine ⟨(b + ·) '' (K : Set B), ?_, isOpenMap_add_left b _ hK, ⟨0, K.zero_mem, add_zero b⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  rwa [Set.mem_preimage, hf b k hk]

/-- A ring map onto `S ⊗[R] S` is surjective once both inclusions of `S`, precomposed with a
surjection `q`, factor through it. -/
theorem surjective_of_comp_eq_includeLeft_includeRight {R S B C : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [CommRing B] [Semiring C] (q : B →+* S)
    (hq : Function.Surjective q) (f g : B →+* C) (φ : C →+* S ⊗[R] S)
    (hf : φ.comp f = Algebra.TensorProduct.includeLeftRingHom.comp q)
    (hg : φ.comp g = (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom.comp q) :
    Function.Surjective φ := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero φ⟩
  | tmul x y =>
    obtain ⟨b, rfl⟩ := hq x
    obtain ⟨c, rfl⟩ := hq y
    refine ⟨f b * g c, ?_⟩
    rw [map_mul, ← RingHom.comp_apply φ, hf, ← RingHom.comp_apply φ, hg]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply]
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add φ _ _⟩

/-- Let `μ : C → B` have a section `s`, and let `φ : C → D` be surjective with
`m ∘ φ = q ∘ μ`, where `φ ∘ s` kills the kernel of `q`. Then `ker m` is the image of `ker μ`. -/
theorem ker_eq_map_ker_of_comp_eq {B C D S : Type*} [CommRing B] [CommRing C] [CommRing D]
    [CommRing S] (μ : C →+* B) (s : B →+* C) (hs : μ.comp s = RingHom.id B) (φ : C →+* D)
    (hφ : Function.Surjective φ) (m : D →+* S) (q : B →+* S) (hmφ : m.comp φ = q.comp μ)
    (hq : ∀ b, q b = 0 → φ (s b) = 0) : RingHom.ker m = (RingHom.ker μ).map φ := by
  refine le_antisymm (fun t ht => ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
  · obtain ⟨x, rfl⟩ := hφ t
    have hx : q (μ x) = 0 := by
      rw [← RingHom.comp_apply q, ← hmφ, RingHom.comp_apply]
      exact RingHom.mem_ker.mp ht
    have hmem : x - s (μ x) ∈ RingHom.ker μ := by
      rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply μ, hs, RingHom.id_apply, sub_self]
    simpa only [map_sub, hq _ hx, sub_zero] using Ideal.mem_map_of_mem φ hmem
  · rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply m, hmφ, RingHom.comp_apply,
      RingHom.mem_ker.mp hx, map_zero]

/-- **Unramified quotient stages from an idempotent diagonal kernel.** Let
`μ : B ⊗̂_A B → B` be a continuous ring map which is the identity on both factors and whose
kernel is idempotent. Then for an open ideal `K` of `B` and an ideal `I` of `A` with `I B ⊆ K`,
the quotient `B ⧸ K` is formally unramified over `A ⧸ I`. -/
theorem formallyUnramified_quotient_of_isIdempotentElem_ker
    (μ : CompletedTensorProduct (R := A) (M := B) (N := B) →+* B) (hμ : Continuous μ)
    (hl : μ.comp completedTensorProductInl = RingHom.id B)
    (hr : μ.comp completedTensorProductInr = RingHom.id B)
    (hJ : IsIdempotentElem (RingHom.ker μ)) (I : Ideal A) (K : Ideal B)
    (hK : IsOpen (K : Set B)) (hIK : I ≤ K.comap (algebraMap A B)) :
    letI : Algebra (A ⧸ I) (B ⧸ K) := (Ideal.quotientMap K (algebraMap A B) hIK).toAlgebra
    Algebra.FormallyUnramified (A ⧸ I) (B ⧸ K) := by
  let : Algebra (A ⧸ I) (B ⧸ K) := (Ideal.quotientMap K (algebraMap A B) hIK).toAlgebra
  let T := (B ⧸ K) ⊗[A ⧸ I] (B ⧸ K)
  let : UniformSpace T := ⊥
  have hT : DiscreteTopology T := ⟨rfl⟩
  have hS : DiscreteTopology (B ⧸ K) := QuotientAddGroup.discreteTopology (N := K.toAddSubgroup) hK
  let mk : B →+* B ⧸ K := Ideal.Quotient.mk K
  let α : B →+* T := (Algebra.TensorProduct.includeLeftRingHom).comp mk
  let β : B →+* T := (Algebra.TensorProduct.includeRight : (B ⧸ K) →ₐ[A ⧸ I] T).toRingHom.comp mk
  have hcos : ∀ b k, k ∈ K → mk (b + k) = mk b := fun b k hk => by
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hk, add_zero]
  have hα : Continuous α := continuous_of_add_mem_eq α K hK fun b k hk => by
    simp only [α, RingHom.comp_apply, hcos b k hk]
  have hβ : Continuous β := continuous_of_add_mem_eq β K hK fun b k hk => by
    simp only [β, RingHom.comp_apply, hcos b k hk]
  have hαβ : α.comp (algebraMap A B) = β.comp (algebraMap A B) := by
    ext x
    show mk (algebraMap A B x) ⊗ₜ[A ⧸ I] (1 : B ⧸ K) = (1 : B ⧸ K) ⊗ₜ[A ⧸ I] mk (algebraMap A B x)
    rw [show mk (algebraMap A B x) = algebraMap (A ⧸ I) (B ⧸ K) (Ideal.Quotient.mk I x) from rfl,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let φ := completedTensorProductLift α β hα hβ hαβ
  have hφl : φ.comp completedTensorProductInl = α := completedTensorProductLift_comp_inl _ _ _ _ _
  have hφr : φ.comp completedTensorProductInr = β := completedTensorProductLift_comp_inr _ _ _ _ _
  let m : T →+* B ⧸ K := (Algebra.TensorProduct.lmul' (A ⧸ I) : T →ₐ[A ⧸ I] B ⧸ K).toRingHom
  have hmφ : m.comp φ = mk.comp μ := by
    let : UniformSpace (B ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (B ⧸ K)
    refine completedTensorProduct_ringHom_ext ((continuous_of_discreteTopology (f := m)).comp
      (continuous_completedTensorProductLift α β hα hβ hαβ))
      ((continuous_of_add_mem_eq mk K hK hcos).comp hμ) ?_ ?_
    · rw [RingHom.comp_assoc, hφl, RingHom.comp_assoc, hl]
      ext b
      simp only [m, α, mk, RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply]
      exact (Algebra.TensorProduct.lmul'_apply_tmul (R := A ⧸ I) _ _).trans (mul_one _)
    · rw [RingHom.comp_assoc, hφr, RingHom.comp_assoc, hr]
      ext b
      simp only [m, β, mk, RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      exact (Algebra.TensorProduct.lmul'_apply_tmul (R := A ⧸ I) _ _).trans (one_mul _)
  have hker : RingHom.ker m = (RingHom.ker μ).map φ :=
    ker_eq_map_ker_of_comp_eq μ _ hl φ
      (surjective_of_comp_eq_includeLeft_includeRight mk Ideal.Quotient.mk_surjective _ _ φ hφl hφr)
      m mk hmφ fun b hb => by rw [← RingHom.comp_apply φ, hφl]; simp [α, hb]
  have hidem : IsIdempotentElem (KaehlerDifferential.ideal (A ⧸ I) (B ⧸ K)) := by
    rw [show KaehlerDifferential.ideal (A ⧸ I) (B ⧸ K) = RingHom.ker m from rfl, hker]
    exact (Ideal.map_mul φ _ _).symm.trans (congrArg _ hJ.eq)
  exact ⟨(KaehlerDifferential.ideal (A ⧸ I) (B ⧸ K)).cotangent_subsingleton_iff.mpr hidem⟩

end TopologicalRing
