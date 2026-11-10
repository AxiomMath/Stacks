module

public import Mathlib.RingTheory.Finiteness.Prod
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic

/-!
# Determinants of endomorphisms of short exact sequences of finite projective modules

Let `R` be a commutative ring. For an endomorphism of a short exact sequence
`0 → A → E → B → 0` of finite projective `R`-modules, the determinant of the middle component is
the product of the determinants of the outer components. The proof splits the sequence and writes
the block upper triangular endomorphism of `A × B` as a product of a diagonal endomorphism, a
unipotent one and another diagonal one. Each factor is computed by
`ProjectiveDeterminant.det_one_add_comp_comm` (Stacks 0FJF).

## Main results

* `ProjectiveDeterminant.det_linearMap_id`: the determinant of the identity is `1`, with the
  module in any universe.
* `ProjectiveDeterminant.det_linearEquiv_conj`: the determinant is invariant under conjugation by
  a linear equivalence between modules in any universes.
* `ProjectiveDeterminant.det_prodMap`: the determinant of `f × g` is the product.
* `ProjectiveDeterminant.det_of_exact`: the determinant is multiplicative along an endomorphism of
  a short exact sequence.
-/

@[expose] public section

namespace ProjectiveDeterminant

universe u v w x

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- The determinant of the identity of a finite projective module is `1`. -/
public theorem det_linearMap_id : det (LinearMap.id : M →ₗ[R] M) = 1 :=
  ((Classical.choose_spec (existsUnique_scalar (M := M)
    (map (M := M) (N := M) (fun _ => rfl) (LinearMap.id : M →ₗ[R] M)))).2 1 (by
      rw [map_id]
      simp)).symm

/-- The determinant of `1 + j (f - 1) p` is that of `f`, when `p` is a retraction of `j`. -/
private theorem det_id_add_comp_sub_id_comp (p : M →ₗ[R] N) (j : N →ₗ[R] M)
    (hpj : p.comp j = LinearMap.id) (f : N →ₗ[R] N) :
    det (LinearMap.id + (j.comp (f - LinearMap.id)).comp p) = det f := by
  have h := det_one_add_comp_comm p (j.comp (f - LinearMap.id))
  rw [← LinearMap.comp_assoc, hpj, LinearMap.id_comp, add_sub_cancel] at h
  exact h.symm

/-- The determinant is invariant under conjugation by a linear equivalence. -/
public theorem det_linearEquiv_conj (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) : det (e.conj f) = det f := by
  rw [← det_id_add_comp_sub_id_comp e.symm.toLinearMap e.toLinearMap (by ext; simp) f]
  congr 1
  ext x
  simp [LinearEquiv.conj_apply]

/-- The determinant of `f × id` on `M × N` is the determinant of `f`. -/
public theorem det_prodMap_id (f : M →ₗ[R] M) :
    det (f.prodMap (LinearMap.id : N →ₗ[R] N)) = det f := by
  rw [← det_id_add_comp_sub_id_comp (LinearMap.fst R M N) (LinearMap.inl R M N) (by ext; simp) f]
  congr 1
  ext x <;> simp

/-- The determinant of `id × g` on `M × N` is the determinant of `g`. -/
public theorem det_id_prodMap (g : N →ₗ[R] N) :
    det ((LinearMap.id : M →ₗ[R] M).prodMap g) = det g := by
  rw [← det_id_add_comp_sub_id_comp (LinearMap.snd R M N) (LinearMap.inr R M N) (by ext; simp) g]
  congr 1
  ext x <;> simp

/-- The determinant of the unipotent endomorphism `(x, y) ↦ (x + γ y, y)` of `M × N` is `1`. -/
public theorem det_unipotent (γ : N →ₗ[R] M) :
    det (LinearMap.id + (LinearMap.inl R M N).comp (γ.comp (LinearMap.snd R M N))) = 1 := by
  have h := det_one_add_comp_comm (R := R) (M := M × N) (N := N)
    (LinearMap.snd R M N) ((LinearMap.inl R M N).comp γ)
  have h1 : (LinearMap.snd R M N).comp ((LinearMap.inl R M N).comp γ) = 0 := by
    ext x
    simp
  rw [h1, add_zero, det_linearMap_id] at h
  rw [h, LinearMap.comp_assoc]

/-- The determinant of a block upper triangular endomorphism `(x, y) ↦ (f x + γ y, g y)` of
`M × N` is the product of the determinants of the diagonal blocks. -/
public theorem det_blockTriangular (f : M →ₗ[R] M) (γ : N →ₗ[R] M) (g : N →ₗ[R] N) :
    det ((LinearMap.inl R M N).comp ((f.comp (LinearMap.fst R M N)) +
        γ.comp (LinearMap.snd R M N)) +
      (LinearMap.inr R M N).comp (g.comp (LinearMap.snd R M N))) = det f * det g := by
  have hfac : (LinearMap.inl R M N).comp ((f.comp (LinearMap.fst R M N)) +
        γ.comp (LinearMap.snd R M N)) +
      (LinearMap.inr R M N).comp (g.comp (LinearMap.snd R M N)) =
      ((LinearMap.id.prodMap g).comp
        (LinearMap.id + (LinearMap.inl R M N).comp (γ.comp (LinearMap.snd R M N)))).comp
          (f.prodMap LinearMap.id) := by
    ext x <;> simp
  rw [hfac, det_comp, det_comp, det_prodMap_id, det_id_prodMap, det_unipotent]
  ring

/-- The determinant of `f × g` on `M × N` is the product of the determinants. -/
public theorem det_prodMap (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    det (f.prodMap g) = det f * det g := by
  have h := det_blockTriangular f 0 g
  rw [← h]
  congr 1
  ext x <;> simp

variable {A : Type v} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
variable {E : Type w} [AddCommGroup E] [Module R E] [Module.Finite R E] [Module.Projective R E]
variable {B : Type x} [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]

/-- **Determinants are multiplicative along short exact sequences.** For an endomorphism
`(α, ε, β)` of a short exact sequence `0 → A → E → B → 0` of finite projective modules,
`det ε = det α * det β`. -/
public theorem det_of_exact {i : A →ₗ[R] E} {q : E →ₗ[R] B} (hi : Function.Injective i)
    (hex : Function.Exact i q) (hq : Function.Surjective q)
    (α : A →ₗ[R] A) (ε : E →ₗ[R] E) (β : B →ₗ[R] B)
    (hα : ε.comp i = i.comp α) (hβ : q.comp ε = β.comp q) :
    det ε = det α * det β := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  have hqi : ∀ z, q (i z) = 0 := fun z => (hex (i z)).2 ⟨z, rfl⟩
  have hqs : ∀ z, q (s z) = z := fun z => LinearMap.congr_fun hs z
  -- the splitting `E ≃ A × B`
  let e : (A × B) ≃ₗ[R] E :=
    LinearEquiv.ofBijective (i.coprod s) (by
      constructor
      · intro ⟨a, b⟩ ⟨a', b'⟩ h
        simp only [LinearMap.coprod_apply] at h
        have hb : b = b' := by
          have := congrArg q h
          simp only [map_add] at this
          simpa [hqi, hqs] using this
        subst hb
        have ha : i a = i a' := by simpa using h
        rw [hi ha]
      · intro y
        obtain ⟨a, ha⟩ := (hex (y - s (q y))).1 (by simp [hqs])
        exact ⟨(a, q y), by simp [ha]⟩)
  -- the off-diagonal block of `ε` in the splitting
  have hγ : ∀ b : B, ∃ a : A, i a = ε (s b) - s (β b) := fun b =>
    (hex _).1 (by
      have := LinearMap.congr_fun hβ (s b)
      simp only [LinearMap.comp_apply] at this
      simp [this, hqs])
  choose γf hγf using hγ
  let γ : B →ₗ[R] A :=
    { toFun := γf
      map_add' := fun b b' => hi (by simp [hγf]; abel)
      map_smul' := fun r b => hi (by simp [hγf, smul_sub]) }
  have hconj : e.symm.conj ε = (LinearMap.inl R A B).comp ((α.comp (LinearMap.fst R A B)) +
      γ.comp (LinearMap.snd R A B)) +
    (LinearMap.inr R A B).comp (β.comp (LinearMap.snd R A B)) := by
    apply LinearMap.ext
    intro ⟨a, b⟩
    apply e.injective
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
    have h1 := LinearMap.congr_fun hα a
    simp only [LinearMap.comp_apply] at h1
    have h2 : γ b = γf b := rfl
    simp only [e, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Prod.mk_add_mk, add_zero, zero_add, map_add, h2]
    change ε (i a + s b) = i (α a + γf b) + s (β b)
    rw [map_add, h1, map_add, hγf]
    abel
  rw [← det_linearEquiv_conj e.symm ε, hconj, det_blockTriangular]

end ProjectiveDeterminant
