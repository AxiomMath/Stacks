module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# First cohomology of a tensor product of complexes over a field, through two faces

Let `k` be a field and let `C⁰ → C¹ → C²` and `D⁰ → D¹ → D²` be complexes of `k`-vector spaces
whose degree-zero cocycles are the multiples of a single element, `c₀` resp. `d₀`. A degree-one
cocycle of the total complex of `C ⊗ D` is a pair `(α, β) ∈ C¹ ⊗ D⁰ × C⁰ ⊗ D¹` with
`(d ⊗ 1) α = 0`, `(1 ⊗ d) β = 0` and `(1 ⊗ d) α = (d ⊗ 1) β`. By the Künneth formula its class
lies in `H¹(C) ⊗ H⁰(D) ⊕ H⁰(C) ⊗ H¹(D)`; the result here, `exists_eq_of_faces`, is the
consequence of that formula which the theorem of the cube uses: the class vanishes as soon as it
vanishes after the two "faces" `1 ⊗ ε : C ⊗ D ⟶ C ⊗ D'` and `η ⊗ 1 : C ⊗ D ⟶ C' ⊗ D`, for maps
of complexes `ε`, `η` which do not kill `d₀`, resp. `c₀`, and whose targets have degree-zero
cocycles inside the line through the image of `c₀`.

The proof is the usual one: exactness of `- ⊗ V` over a field puts the class of `α` in
`H¹(C) ⊗ H⁰(D) = H¹(C) ⊗ k d₀`, the face `ε` kills it, so `α` is a coboundary `(d ⊗ 1) e`; then
`β - (1 ⊗ d) e = c₀ ⊗ g`, and the face `η` shows that `g` is a coboundary.

## Main results

* `StacksDraft.KunnethOne.exists_eq_of_faces`.
-/

@[expose] public section

open TensorProduct LinearMap

universe u

namespace StacksDraft.KunnethOne

variable {k : Type u} [Field k]

/-- An element of `M ⊗ N` lying in the image of `S ⊗ N` for a submodule `S` of the line through
`v` is `v ⊗ n` for some `n`. -/
theorem exists_eq_tmul_of_mem_range {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (v : M) (S : Submodule k M) (hS : S ≤ k ∙ v)
    (x : M ⊗[k] N) (hx : x ∈ range (S.subtype.rTensor N)) : ∃ n : N, x = v ⊗ₜ n := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s n =>
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hS s.2)
    exact ⟨c • n, by simp [← hc, TensorProduct.smul_tmul]⟩
  | add y y' hy hy' =>
    obtain ⟨n, hn⟩ := hy
    obtain ⟨n', hn'⟩ := hy'
    exact ⟨n + n', by rw [map_add, hn, hn', TensorProduct.tmul_add]⟩

/-- Over a field, `v ⊗ n = 0` with `v ≠ 0` forces `n = 0`. -/
theorem eq_zero_of_tmul_eq_zero {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {v : M} (hv : v ≠ 0) {n : N} (h : v ⊗ₜ[k] n = 0) : n = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k M, f v ≠ 0 :=
    not_forall.1 fun hcon => hv ((Module.forall_dual_apply_eq_zero_iff k v).1 hcon)
  have := congrArg (TensorProduct.lift ((LinearMap.lsmul k N) ∘ₗ f)) h
  rw [TensorProduct.lift.tmul, map_zero] at this
  exact (smul_eq_zero.1 this).resolve_left hf

/-- Over a field, `m ⊗ w = 0` with `w ≠ 0` forces `m = 0`. -/
theorem eq_zero_of_tmul_eq_zero' {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {w : N} (hw : w ≠ 0) {m : M} (h : m ⊗ₜ[k] w = 0) : m = 0 :=
  eq_zero_of_tmul_eq_zero hw (by rw [← TensorProduct.comm_tmul k M N, h, map_zero])

/-- An element of `M ⊗ N` killed by `1 ⊗ f`, where the kernel of `f` lies in the line through `v`,
is `m ⊗ v` for some `m`. -/
private theorem exists_eq_tmul_of_lTensor_eq_zero {M N P : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] (f : N →ₗ[k] P) (v : N)
    (hv : ker f ≤ k ∙ v) (x : M ⊗[k] N) (hx : f.lTensor M x = 0) : ∃ m : M, x = m ⊗ₜ v := by
  obtain ⟨γ, hγ⟩ := (Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f) _).1 hx
  have key : ∀ g : M ⊗[k] ker f, (ker f).subtype.rTensor M (TensorProduct.comm k M _ g) =
      TensorProduct.comm k M N ((ker f).subtype.lTensor M g) := fun g => by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hγ' : TensorProduct.comm k M N x ∈ range ((ker f).subtype.rTensor M) :=
    ⟨TensorProduct.comm k M (ker f) γ, by rw [key, hγ]⟩
  obtain ⟨m, hm⟩ := exists_eq_tmul_of_mem_range v (ker f) hv _ hγ'
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.comm k N M) hm
  rw [TensorProduct.comm_tmul] at this
  rw [← this]
  simp

/-- The two tensor-product maps `f ⊗ 1` and `1 ⊗ g` commute. -/
private theorem lTensor_rTensor_comm {R M N P Q : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (x : P ⊗[R] M) :
    f.lTensor Q (g.rTensor M x) = g.rTensor N (f.lTensor P x) := by
  rw [← LinearMap.comp_apply, lTensor_comp_rTensor, ← LinearMap.comp_apply, rTensor_comp_lTensor]

/-- An element of `M ⊗ N` killed by `f ⊗ 1`, where the kernel of `f` lies in the line through `v`,
is `v ⊗ n` for some `n`. -/
private theorem exists_eq_tmul_of_rTensor_eq_zero {M N P : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P] (f : M →ₗ[k] P) (v : M)
    (hv : ker f ≤ k ∙ v) (x : M ⊗[k] N) (hx : f.rTensor N x = 0) : ∃ n : N, x = v ⊗ₜ n :=
  exists_eq_tmul_of_mem_range v (ker f) hv x
    ((Module.Flat.rTensor_exact N (LinearMap.exact_subtype_ker_map f) x).1 hx)

/-- If `π ∘ δ = 0` and `(1 ⊗ φ) x = (δ ⊗ 1) y`, then `(1 ⊗ φ) ((π ⊗ 1) x) = 0`. -/
private theorem lTensor_rTensor_eq_zero_of_comp_eq_zero {R A B H D N : Type*} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B] [AddCommMonoid H] [Module R H]
    [AddCommMonoid D] [Module R D] [AddCommMonoid N] [Module R N]
    {δ : A →ₗ[R] B} {π : B →ₗ[R] H} (hπδ : π ∘ₗ δ = 0) (φ : D →ₗ[R] N)
    {x : B ⊗[R] D} {y : A ⊗[R] N} (h : φ.lTensor B x = δ.rTensor N y) :
    φ.lTensor H (π.rTensor D x) = 0 := by
  rw [lTensor_rTensor_comm, h, ← LinearMap.comp_apply, ← rTensor_comp, hπδ, rTensor_zero,
    LinearMap.zero_apply]

variable {C0 C1 C2 D0 D1 D2 Cp0 Cp1 Dp0 : Type u}
  [AddCommGroup C0] [Module k C0] [AddCommGroup C1] [Module k C1] [AddCommGroup C2] [Module k C2]
  [AddCommGroup D0] [Module k D0] [AddCommGroup D1] [Module k D1] [AddCommGroup D2] [Module k D2]
  [AddCommGroup Cp0] [Module k Cp0] [AddCommGroup Cp1] [Module k Cp1]
  [AddCommGroup Dp0] [Module k Dp0]

/-- A degree-one cocycle `(α, β)` of `C ⊗ D` with `α = (d ⊗ 1) e` which vanishes on the face `η`
is a coboundary. -/
private theorem exists_eq_of_face_of_rTensor_eq (dC0 : C0 →ₗ[k] C1) (dD0 : D0 →ₗ[k] D1)
    (dCp : Cp0 →ₗ[k] Cp1) (η0 : C0 →ₗ[k] Cp0) (η1 : C1 →ₗ[k] Cp1)
    (hη : dCp ∘ₗ η0 = η1 ∘ₗ dC0) (c0 : C0) (hc0 : ker dC0 ≤ k ∙ c0) (hc0d : dC0 c0 = 0)
    (hcp : ker dCp ≤ k ∙ η0 c0) (hηc0 : η0 c0 ≠ 0)
    (α : C1 ⊗[k] D0) (β : C0 ⊗[k] D1) (hαβ : dD0.lTensor C1 α = dC0.rTensor D1 β)
    (hface1 : ∃ e1 : Cp0 ⊗[k] D0, dCp.rTensor D0 e1 = η1.rTensor D0 α ∧
      dD0.lTensor Cp0 e1 = η0.rTensor D1 β) (e : C0 ⊗[k] D0) (he : dC0.rTensor D0 e = α) :
    ∃ e : C0 ⊗[k] D0, dC0.rTensor D0 e = α ∧ dD0.lTensor C0 e = β := by
  set β' := β - dD0.lTensor C0 e
  have h5 : dC0.rTensor D1 β' = 0 := by
    simp only [β', map_sub]
    rw [← hαβ, ← he, lTensor_rTensor_comm, sub_self]
  obtain ⟨g, hg⟩ := exists_eq_tmul_of_rTensor_eq_zero dC0 c0 hc0 β' h5
  obtain ⟨e1, he1, he1'⟩ := hface1
  set e1' := e1 - η0.rTensor D0 e
  have h6 : dCp.rTensor D0 e1' = 0 := by
    simp only [e1', map_sub]
    rw [he1, ← he, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← rTensor_comp,
      ← rTensor_comp, hη, sub_self]
  obtain ⟨h, hh⟩ := exists_eq_tmul_of_rTensor_eq_zero dCp (η0 c0) hcp e1' h6
  have h6' : η0 c0 ⊗ₜ[k] (dD0 h - g) = 0 := by
    have : dD0.lTensor Cp0 e1' = η0.rTensor D1 β' := by
      simp only [e1', β', map_sub]
      rw [he1', lTensor_rTensor_comm]
    rw [hh, hg, lTensor_tmul, rTensor_tmul] at this
    rw [TensorProduct.tmul_sub, this, sub_self]
  have hgh : g = dD0 h := (sub_eq_zero.1 (eq_zero_of_tmul_eq_zero hηc0 h6')).symm
  refine ⟨e + c0 ⊗ₜ h, ?_, ?_⟩
  · rw [map_add, rTensor_tmul, hc0d, TensorProduct.zero_tmul, add_zero, he]
  · rw [map_add, lTensor_tmul, ← hgh, ← hg]
    simp [β']

/-- **A first cohomology class of `C ⊗ D` which vanishes on two faces is zero.** -/
theorem exists_eq_of_faces (dC0 : C0 →ₗ[k] C1) (dC1 : C1 →ₗ[k] C2) (dD0 : D0 →ₗ[k] D1)
    (dCp : Cp0 →ₗ[k] Cp1) (η0 : C0 →ₗ[k] Cp0) (η1 : C1 →ₗ[k] Cp1)
    (hη : dCp ∘ₗ η0 = η1 ∘ₗ dC0) (ε0 : D0 →ₗ[k] Dp0)
    (hdC : dC1 ∘ₗ dC0 = 0) (c0 : C0) (hc0 : ker dC0 ≤ k ∙ c0) (hc0d : dC0 c0 = 0)
    (hcp : ker dCp ≤ k ∙ η0 c0) (hηc0 : η0 c0 ≠ 0)
    (d0 : D0) (hd0 : ker dD0 ≤ k ∙ d0) (hεd0 : ε0 d0 ≠ 0)
    (α : C1 ⊗[k] D0) (β : C0 ⊗[k] D1)
    (hα : dC1.rTensor D0 α = 0) (hαβ : dD0.lTensor C1 α = dC0.rTensor D1 β)
    (hface2 : ∃ e2 : C0 ⊗[k] Dp0, dC0.rTensor Dp0 e2 = ε0.lTensor C1 α)
    (hface1 : ∃ e1 : Cp0 ⊗[k] D0, dCp.rTensor D0 e1 = η1.rTensor D0 α ∧
      dD0.lTensor Cp0 e1 = η0.rTensor D1 β) :
    ∃ e : C0 ⊗[k] D0, dC0.rTensor D0 e = α ∧ dD0.lTensor C0 e = β := by
  classical
  set Z1 := ker dC1
  have hdC' : ∀ x, dC0 x ∈ Z1 := fun x => by
    show dC1 (dC0 x) = 0
    exact congrArg (fun φ : C0 →ₗ[k] C2 => φ x) hdC
  set δ : C0 →ₗ[k] Z1 := dC0.codRestrict Z1 hdC'
  set H := Z1 ⧸ range δ
  set π : Z1 →ₗ[k] H := (range δ).mkQ
  have hπδ : π ∘ₗ δ = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hsub : ∀ (N : Type u) [AddCommGroup N] [Module k N],
      Function.Injective (Z1.subtype.rTensor N) := fun N _ _ =>
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hsubδ : ∀ (N : Type u) [AddCommGroup N] [Module k N],
      Z1.subtype.rTensor N ∘ₗ δ.rTensor N = dC0.rTensor N := fun N _ _ => by
    rw [← rTensor_comp]; rfl
  have hex1 : Function.Exact Z1.subtype dC1 := LinearMap.exact_subtype_ker_map dC1
  obtain ⟨α', rfl⟩ := (Module.Flat.rTensor_exact D0 hex1 α).1 hα
  have hlift : ∀ (N : Type u) [AddCommGroup N] [Module k N] (φ : D0 →ₗ[k] N) (y : C0 ⊗[k] N),
      dC0.rTensor N y = φ.lTensor C1 (Z1.subtype.rTensor D0 α') → φ.lTensor Z1 α' = δ.rTensor N y :=
    fun N _ _ φ y h => by
      apply hsub N
      rw [← LinearMap.comp_apply (Z1.subtype.rTensor N) (δ.rTensor N), hsubδ, h,
        lTensor_rTensor_comm]
  obtain ⟨θ, hθ⟩ := exists_eq_tmul_of_lTensor_eq_zero dD0 d0 hd0 _
    (lTensor_rTensor_eq_zero_of_comp_eq_zero hπδ dD0 (hlift D1 dD0 β hαβ.symm))
  have h3 : θ = 0 := by
    obtain ⟨e2, he2⟩ := hface2
    have h3b := lTensor_rTensor_eq_zero_of_comp_eq_zero hπδ ε0 (hlift Dp0 ε0 e2 he2)
    rw [hθ, lTensor_tmul] at h3b
    exact eq_zero_of_tmul_eq_zero' hεd0 h3b
  rw [h3, TensorProduct.zero_tmul] at hθ
  have hexH : Function.Exact (range δ).subtype π := LinearMap.exact_subtype_mkQ _
  obtain ⟨b, hb⟩ := (rTensor_exact D0 hexH (Submodule.mkQ_surjective _) α').1 hθ
  obtain ⟨e, he⟩ := rTensor_surjective D0 (LinearMap.surjective_rangeRestrict δ) b
  have hαe : Z1.subtype.rTensor D0 α' = dC0.rTensor D0 e := by
    rw [← hb, ← he, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← rTensor_comp,
      ← rTensor_comp]
    rfl
  exact exists_eq_of_face_of_rTensor_eq dC0 dD0 dCp η0 η1 hη c0 hc0 hc0d hcp hηc0 _ β hαβ hface1
    e hαe.symm

end StacksDraft.KunnethOne

end
