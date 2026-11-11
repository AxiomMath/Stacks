module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Two-sided sub vector spaces of `K ⊗_k V` for a central skew field `K`

Stacks Lemma 074B: let `V` be a `k`-vector space and `K` a central `k`-algebra which is a skew
field. Then every two-sided `K`-sub vector space `W` of `K ⊗_k V` is generated, as a left
`K`-vector space, by `W ∩ (1 ⊗ V)`.

Here `K` is written `D`. A two-sided `D`-sub vector space of `D ⊗[k] V` is a `D`-submodule for the
left action of `D` on the first factor which is also stable under right multiplication on that
factor, i.e. under `LinearMap.rTensor V (LinearMap.mulRight k c)` for every `c : D`.

## Main results

* `Submodule.eq_span_inter_range_one_tmul`: Stacks 074B.
* `Submodule.eq_zero_of_sum_tmul_mem_of_mulRight_mem`: a two-sided sub vector space meeting
  `1 ⊗ V` trivially contains no nonzero `∑ aᵢ ⊗ bᵢ` with the `bᵢ` linearly independent.
-/

@[expose] public section

open TensorProduct

namespace Submodule

variable {k D V : Type*} [Field k] [DivisionRing D] [Algebra k D] [AddCommGroup V] [Module k V]

/-- Let `D` be a central `k`-algebra which is a skew field and `W ⊆ D ⊗[k] V` a two-sided
`D`-sub vector space with `W ∩ (1 ⊗ V) = 0`. Then any element `∑ i ∈ s, a i ⊗ₜ b i` of `W` with
the `b i` linearly independent has all coefficients `a i` equal to zero. -/
lemma eq_zero_of_sum_tmul_mem_of_mulRight_mem [Algebra.IsCentral k D]
    {W : Submodule D (D ⊗[k] V)}
    (hW : ∀ c : D, ∀ w ∈ W, LinearMap.rTensor V (LinearMap.mulRight k c) w ∈ W)
    (h0 : ∀ v : V, (1 : D) ⊗ₜ[k] v ∈ W → v = 0)
    {ι : Type*} {b : ι → V} (hb : LinearIndependent k b) {s : Finset ι} {a : ι → D}
    (h : ∑ i ∈ s, a i ⊗ₜ[k] b i ∈ W) : ∀ i ∈ s, a i = 0 := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | insert j s hjs ih =>
    rw [Finset.sum_insert hjs] at h
    rcases eq_or_ne (a j) 0 with hj | hj
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact ih (by simpa [hj] using h) i hi
    exfalso
    set a' : ι → D := fun i ↦ (a j)⁻¹ * a i with ha'
    have h1 : (1 : D) ⊗ₜ[k] b j + ∑ i ∈ s, a' i ⊗ₜ[k] b i ∈ W := by
      have := W.smul_mem (a j)⁻¹ h
      simpa only [smul_add, Finset.smul_sum, smul_tmul', smul_eq_mul, inv_mul_cancel₀ hj,
        ha'] using this
    have hcen (x : ι) : ∃ c : k, x ∈ s → a' x = algebraMap k D c := by
      by_cases hx : x ∈ s
      · have hz : ∀ z : D, z * a' x = a' x * z := fun z ↦ by
          refine sub_eq_zero.1 <| ih (a := fun i ↦ z * a' i - a' i * z) ?_ x hx
          have := W.sub_mem (W.smul_mem z h1) (hW z _ h1)
          convert this using 1
          simp [smul_add, Finset.smul_sum, smul_tmul', sub_tmul, Finset.sum_sub_distrib]
        obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff k).1 <|
          Subalgebra.mem_center_iff.2 fun z ↦ hz z
        exact ⟨c, fun _ ↦ hc⟩
      · exact ⟨0, fun h ↦ absurd h hx⟩
    choose c hc using hcen
    have h2 : b j + ∑ x ∈ s, c x • b x = 0 := by
      refine h0 _ ?_
      convert h1 using 1
      rw [tmul_add, tmul_sum]
      congr 1
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [hc x hx, Algebra.algebraMap_eq_smul_one, smul_tmul]
    refine hb.notMem_span_image (show j ∉ (↑s : Set ι) by simpa using hjs) ?_
    rw [eq_neg_of_add_eq_zero_left h2]
    exact Submodule.neg_mem _ <| Submodule.sum_mem _ fun x hx ↦ Submodule.smul_mem _ _ <|
      Submodule.subset_span <| Set.mem_image_of_mem b (by simpa using hx)

/-- Let `D` be a central `k`-algebra which is a skew field. A two-sided `D`-sub vector space of
`D ⊗[k] V` meeting `1 ⊗ V` trivially is zero. -/
lemma eq_bot_of_mulRight_mem [Algebra.IsCentral k D] {W : Submodule D (D ⊗[k] V)}
    (hW : ∀ c : D, ∀ w ∈ W, LinearMap.rTensor V (LinearMap.mulRight k c) w ∈ W)
    (h0 : ∀ v : V, (1 : D) ⊗ₜ[k] v ∈ W → v = 0) : W = ⊥ := by
  obtain ⟨ι, 𝓑⟩ := Module.Free.exists_basis k V
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  obtain ⟨r, rfl⟩ := TensorProduct.eq_repr_basis_right 𝓑 x
  simp only [Finsupp.sum] at hx ⊢
  simp [Finset.eq_empty_of_forall_notMem fun i hi ↦ Finsupp.mem_support_iff.1 hi <|
    eq_zero_of_sum_tmul_mem_of_mulRight_mem hW h0 𝓑.linearIndependent hx i hi]

/-- **Stacks 074B.** Let `V` be a `k`-vector space and let `D` be a central `k`-algebra which is a
skew field. Let `W ⊆ D ⊗[k] V` be a two-sided `D`-sub vector space: a `D`-submodule for the left
action of `D` on the first factor which is also stable under right multiplication by every
`c : D` on that factor. Then `W` is generated as a left `D`-vector space by `W ∩ (1 ⊗ V)`.

Stacks writes the tensor product as `V ⊗_k K`; here the factors are swapped to `D ⊗[k] V`, so
that the left `D`-vector space structure is Mathlib's base-change module structure. -/
@[stacks 074B]
theorem eq_span_inter_range_one_tmul [Algebra.IsCentral k D] (W : Submodule D (D ⊗[k] V))
    (hW : ∀ c : D, ∀ w ∈ W, LinearMap.rTensor V (LinearMap.mulRight k c) w ∈ W) :
    W = Submodule.span D ((W : Set (D ⊗[k] V)) ∩ Set.range fun v : V ↦ (1 : D) ⊗ₜ[k] v) := by
  set S := Submodule.span D ((W : Set (D ⊗[k] V)) ∩ Set.range fun v : V ↦ (1 : D) ⊗ₜ[k] v)
  refine le_antisymm ?_ (Submodule.span_le.2 Set.inter_subset_left)
  -- `V'` is the subspace of `v` with `1 ⊗ v ∈ W`.
  set V' : Submodule k V := (W.restrictScalars k).comap (TensorProduct.mk k D V 1) with hV'
  have hmemV' (v : V) : v ∈ V' ↔ (1 : D) ⊗ₜ[k] v ∈ W := Iff.rfl
  -- `D ⊗ V'` lies in the span.
  have hrange (y : D ⊗[k] V') : LinearMap.lTensor D V'.subtype y ∈ S := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul d v =>
      have : d ⊗ₜ[k] (v : V) = d • ((1 : D) ⊗ₜ[k] (v : V)) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, this]
      exact S.smul_mem _ <| Submodule.subset_span ⟨(hmemV' v).1 v.2, v, rfl⟩
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  have hSW : S ≤ W := Submodule.span_le.2 Set.inter_subset_left
  set φ : D ⊗[k] V →ₗ[D] D ⊗[k] (V ⧸ V') := V'.mkQ.baseChange D with hφ
  have hφapp (x : D ⊗[k] V) : φ x = LinearMap.lTensor D V'.mkQ x := by
    rw [hφ, ← LinearMap.baseChange_eq_ltensor]
  have hker {x : D ⊗[k] V} (hx : φ x = 0) : x ∈ S := by
    rw [hφapp, ← LinearMap.mem_ker, lTensor_mkQ] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hrange y
  -- The image of `W` is a two-sided sub vector space meeting `1 ⊗ (V ⧸ V')` trivially.
  have hW2 : ∀ c : D, ∀ w ∈ W.map φ,
      LinearMap.rTensor (V ⧸ V') (LinearMap.mulRight k c) w ∈ W.map φ := by
    rintro c _ ⟨w, hw, rfl⟩
    refine ⟨_, hW c w hw, ?_⟩
    simp only [hφapp]
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul d v => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have h02 : ∀ v : V ⧸ V', (1 : D) ⊗ₜ[k] v ∈ W.map φ → v = 0 := by
    intro v hv
    obtain ⟨v, rfl⟩ := V'.mkQ_surjective v
    obtain ⟨w, hw, hwv⟩ := hv
    have hdiff : φ (w - (1 : D) ⊗ₜ[k] v) = 0 := by
      rw [map_sub, hwv, hφ, LinearMap.baseChange_tmul, sub_self]
    have h1v : (1 : D) ⊗ₜ[k] v ∈ W := by
      simpa using W.sub_mem hw (hSW (hker hdiff))
    exact (Submodule.Quotient.mk_eq_zero V').2 ((hmemV' v).2 h1v)
  have hbot := eq_bot_of_mulRight_mem hW2 h02
  intro x hx
  exact hker <| (Submodule.mem_bot D).1 <| hbot ▸ Submodule.mem_map_of_mem hx

end Submodule
