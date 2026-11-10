module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The equalizer sequence of two algebra maps, tensored with a module

Let `A` be a ring and let `p₁ p₂ : C → D` be two maps of `A`-algebras. For an `A`-module `N`
consider the sequence

`0 → N ⊗_A A → N ⊗_A C → N ⊗_A D`,

whose first map is induced by the structure map `A → C` and whose second map is induced by
`p₁ - p₂`. This file studies the property that this sequence is exact, that is, that
`N ≅ N ⊗_A A` is the equalizer of the two maps `N ⊗_A C ⇉ N ⊗_A D`. For the algebras
`C = Γ(U, 𝒪)` and `D = Γ(U ×_X U, 𝒪)` of an étale chart `U` of an algebraic space `X` over
`Spec A`, and `N = A'` an `A`-algebra, this is the statement that the global functions of
`X ×_{Spec A} Spec A'` are `A'`.

## Main definitions

* `AlgHom.EqualizerTensorExact p₁ p₂ N`: the sequence above is exact.

## Main results

* `AlgHom.EqualizerTensorExact.of_flat`: the property passes from an `A`-algebra `k` to every
  flat `k`-module, and `AlgHom.EqualizerTensorExact.of_faithfullyFlat` descends it back.
* `AlgHom.EqualizerTensorExact.of_exact`: for `C` and `D` flat over `A`, the property is closed
  under extensions of coefficient modules.
-/

@[expose] public section

open TensorProduct

namespace AlgHom

variable {A C D : Type*} [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
  (p₁ p₂ : C →ₐ[A] D)

/-- The equalizer sequence `0 → N ⊗_A A → N ⊗_A C → N ⊗_A D` of two algebra maps
`p₁ p₂ : C → D`, tensored with the `A`-module `N`, is exact: its first map, induced by the
structure map `A → C`, is injective, and its image is the kernel of the map induced by
`p₁ - p₂`. -/
def EqualizerTensorExact (N : Type*) [AddCommGroup N] [Module A N] : Prop :=
  Function.Injective ((Algebra.linearMap A C).lTensor N) ∧
    Function.Exact ((Algebra.linearMap A C).lTensor N)
      ((p₁.toLinearMap - p₂.toLinearMap).lTensor N)

variable {p₁ p₂}

/-- The difference `p₁ - p₂` kills the image of the structure map. -/
theorem sub_comp_linearMap :
    (p₁.toLinearMap - p₂.toLinearMap) ∘ₗ Algebra.linearMap A C = 0 := by
  ext
  simp

/-- The composite `N ⊗_A A → N ⊗_A C → N ⊗_A D` is zero. -/
theorem lTensor_sub_lTensor_linearMap {N : Type*} [AddCommGroup N] [Module A N]
    (w : N ⊗[A] A) :
    (p₁.toLinearMap - p₂.toLinearMap).lTensor N ((Algebra.linearMap A C).lTensor N w) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, sub_comp_linearMap,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- Maps of coefficient modules commute with maps of the other tensor factor. -/
theorem rTensor_lTensor_apply {N N' X Y : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (φ : N →ₗ[A] N') (f : X →ₗ[A] Y) (x : N ⊗[A] X) :
    φ.rTensor Y (f.lTensor N x) = f.lTensor N' (φ.rTensor X x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

/-! ### The sequence through `n ↦ n ⊗ 1` -/

section TmulOne

variable (A C) in
/-- The map `N → N ⊗_A C`, `n ↦ n ⊗ 1`. -/
noncomputable def tmulOne (N : Type*) [AddCommGroup N] [Module A N] : N →ₗ[A] N ⊗[A] C :=
  (TensorProduct.mk A N C).flip 1

/-- `tmulOne A C N` sends `n` to `n ⊗ₜ 1`. -/
@[simp]
theorem tmulOne_apply {N : Type*} [AddCommGroup N] [Module A N] (n : N) :
    tmulOne A C N n = n ⊗ₜ 1 := rfl

/-- `n ↦ n ⊗ 1` is the first map of the sequence, read through `N ≅ N ⊗_A A`. -/
theorem lTensor_linearMap_rid_symm {N : Type*} [AddCommGroup N] [Module A N] (n : N) :
    (Algebra.linearMap A C).lTensor N ((TensorProduct.rid A N).symm n) = tmulOne A C N n := by
  simp

/-- `n ↦ n ⊗ 1` is natural in `N`. -/
theorem rTensor_tmulOne {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (φ : N →ₗ[A] N') (n : N) :
    φ.rTensor C (tmulOne A C N n) = tmulOne A C N' (φ n) :=
  rfl

/-- The sequence is exact exactly when `n ↦ n ⊗ 1` is injective with image the kernel of
`p₁ - p₂`. -/
theorem equalizerTensorExact_iff_tmulOne {N : Type*} [AddCommGroup N] [Module A N] :
    EqualizerTensorExact p₁ p₂ N ↔ Function.Injective (tmulOne A C N) ∧
      ∀ x : N ⊗[A] C, (p₁.toLinearMap - p₂.toLinearMap).lTensor N x = 0 →
        ∃ n, tmulOne A C N n = x := by
  constructor
  · intro h
    refine ⟨fun n₁ n₂ hn => ?_, fun x hx => ?_⟩
    · rw [← lTensor_linearMap_rid_symm, ← lTensor_linearMap_rid_symm] at hn
      exact (TensorProduct.rid A N).symm.injective (h.1 hn)
    · obtain ⟨w, rfl⟩ := (h.2 x).mp hx
      exact ⟨TensorProduct.rid A N w, by
        rw [← lTensor_linearMap_rid_symm, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨hinj, hex⟩
    refine ⟨fun w₁ w₂ hw => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
    · obtain ⟨n₁, rfl⟩ := (TensorProduct.rid A N).symm.surjective w₁
      obtain ⟨n₂, rfl⟩ := (TensorProduct.rid A N).symm.surjective w₂
      rw [lTensor_linearMap_rid_symm, lTensor_linearMap_rid_symm] at hw
      rw [hinj hw]
    · obtain ⟨n, rfl⟩ := hex x hx
      exact ⟨(TensorProduct.rid A N).symm n, lTensor_linearMap_rid_symm n⟩
    · rintro ⟨w, rfl⟩
      exact lTensor_sub_lTensor_linearMap w

end TmulOne

/-! ### Flat base change -/

section BaseChange

variable (k : Type*) [CommRing k] [Algebra A k]
  {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower A k N]

/-- The identification `N ⊗_k (k ⊗_A X) ≅ N ⊗_A X` for a `k`-module `N` is natural in `X`. -/
theorem cancelBaseChange_naturality {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) :
    f.lTensor N ∘ₗ
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A k k N X).restrictScalars
          A).toLinearMap =
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A k k N Y).restrictScalars
          A).toLinearMap ∘ₗ
        ((f.baseChange k).lTensor N).restrictScalars A := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [map_add, map_add, hz, hw]
  | tmul n x =>
    induction x using TensorProduct.inductionOn with
    | tmul a x => simp
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/-- The sequence for a `k`-module `N` is exact iff the `N ⊗_k`-tensored base-changed sequence is
injective and exact. -/
private theorem equalizerTensorExact_iff_lTensor_baseChange :
    EqualizerTensorExact p₁ p₂ N ↔
      Function.Injective (((Algebra.linearMap A C).baseChange k).lTensor N |>.restrictScalars A) ∧
        Function.Exact (((Algebra.linearMap A C).baseChange k).lTensor N |>.restrictScalars A)
          (((p₁.toLinearMap - p₂.toLinearMap).baseChange k).lTensor N |>.restrictScalars A) := by
  set e₁ := (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k N A).restrictScalars A
  set e₂ := (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k N C).restrictScalars A
  set e₃ := (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k N D).restrictScalars A
  have h₁ := cancelBaseChange_naturality (N := N) k (Algebra.linearMap A C)
  have h₂ := cancelBaseChange_naturality (N := N) k (p₁.toLinearMap - p₂.toLinearMap)
  refine and_congr ?_ (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
    h₁ h₂)
  exact ((Function.Injective.of_comp_iff' _ e₁.bijective).symm.trans
    (Iff.of_eq (congrArg (fun f : _ →ₗ[A] _ => Function.Injective ⇑f) h₁))).trans
    (e₂.injective.of_comp_iff _)

variable {k}

/-- **Flat base change.** If the sequence is exact for an `A`-algebra `k`, it is exact for every
flat `k`-module. -/
theorem EqualizerTensorExact.of_flat [Module.Flat k N] (h : EqualizerTensorExact p₁ p₂ k) :
    EqualizerTensorExact p₁ p₂ N := by
  have hinj : Function.Injective ((Algebra.linearMap A C).baseChange k) := h.1
  have hex : Function.Exact ((Algebra.linearMap A C).baseChange k)
      ((p₁.toLinearMap - p₂.toLinearMap).baseChange k) := h.2
  exact (equalizerTensorExact_iff_lTensor_baseChange k).mpr
    ⟨Module.Flat.lTensor_preserves_injective_linearMap _ hinj, Module.Flat.lTensor_exact N hex⟩

/-- **Faithfully flat descent.** If the sequence is exact for a faithfully flat `k`-module, it is
exact for the `A`-algebra `k`. -/
theorem EqualizerTensorExact.of_faithfullyFlat [Module.FaithfullyFlat k N]
    (h : EqualizerTensorExact p₁ p₂ N) : EqualizerTensorExact p₁ p₂ k := by
  obtain ⟨hinj, hex⟩ := (equalizerTensorExact_iff_lTensor_baseChange k).mp h
  refine ⟨?_, ?_⟩
  · change Function.Injective ((Algebra.linearMap A C).baseChange k)
    rwa [← Module.FaithfullyFlat.lTensor_injective_iff_injective k N]
  · change Function.Exact ((Algebra.linearMap A C).baseChange k)
      ((p₁.toLinearMap - p₂.toLinearMap).baseChange k)
    rwa [← Module.FaithfullyFlat.lTensor_exact_iff_exact k N]

end BaseChange

/-! ### Extensions -/

section Extension

variable [Module.Flat A C] [Module.Flat A D]
  {V L L'' : Type*} [AddCommGroup V] [Module A V] [AddCommGroup L] [Module A L]
  [AddCommGroup L''] [Module A L'']

/-- **Closure under extensions.** Let `0 → V → L → L'' → 0` be a short exact sequence of
`A`-modules. If `C` and `D` are flat over `A` and the sequence is exact for `V` and for `L''`,
it is exact for `L`. -/
theorem EqualizerTensorExact.of_exact {f : V →ₗ[A] L} {g : L →ₗ[A] L''}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hV : EqualizerTensorExact p₁ p₂ V) (hL'' : EqualizerTensorExact p₁ p₂ L'') :
    EqualizerTensorExact p₁ p₂ L := by
  have hfC : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  have hfD : Function.Injective (f.rTensor D) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  refine ⟨(injective_iff_map_eq_zero _).mpr fun w hw => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : g.rTensor A w = 0 :=
      hL''.1 (by rw [map_zero, ← rTensor_lTensor_apply, hw, map_zero])
    obtain ⟨v, hv⟩ := (rTensor_exact A hfg hg w).mp h1
    have h2 : (Algebra.linearMap A C).lTensor V v = 0 :=
      hfC (by rw [map_zero, rTensor_lTensor_apply, hv, hw])
    rw [← hv, hV.1 (h2.trans (map_zero _).symm), map_zero]
  · have h1 : (p₁.toLinearMap - p₂.toLinearMap).lTensor L'' (g.rTensor C x) = 0 := by
      rw [← rTensor_lTensor_apply, hx, map_zero]
    obtain ⟨w'', hw''⟩ := (hL''.2 _).mp h1
    obtain ⟨w, rfl⟩ := LinearMap.rTensor_surjective A hg w''
    have h2 : g.rTensor C (x - (Algebra.linearMap A C).lTensor L w) = 0 := by
      rw [map_sub, rTensor_lTensor_apply, hw'', sub_self]
    obtain ⟨y, hy⟩ := (rTensor_exact C hfg hg _).mp h2
    have h3 : (p₁.toLinearMap - p₂.toLinearMap).lTensor V y = 0 :=
      hfD (by rw [rTensor_lTensor_apply, hy, map_zero, map_sub, hx, lTensor_sub_lTensor_linearMap,
        sub_self])
    obtain ⟨v, hv⟩ := (hV.2 _).mp h3
    exact ⟨w + f.rTensor A v, by rw [map_add, ← rTensor_lTensor_apply, hv, hy, add_sub_cancel]⟩
  · rintro ⟨w, rfl⟩
    exact lTensor_sub_lTensor_linearMap w

end Extension

end AlgHom
