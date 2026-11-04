module

public import Mathlib.RingTheory.Flat.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Base change of submodules

Lemmas about `Submodule.baseChange` along an algebra `A → B`: monotonicity, compatibility with
`Submodule.map`, `LinearMap.range` and suprema, base change of `I • ⊤` for an ideal `I`, base
change of multiplication by a scalar, and the fact that flat base change commutes with
intersections of submodules.
-/

open scoped TensorProduct

namespace ArtinReesBaseChange

/-- Base change of submodules along `A → B` is monotone. -/
theorem baseChange_mono {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {p q : Submodule A M} (h : p ≤ q) :
    Submodule.baseChange B p ≤ Submodule.baseChange B q := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span]
  exact Submodule.span_mono (SetLike.coe_mono (Submodule.map_mono h))

/-- The image of `p.baseChange B` under `f.baseChange B` is the base change of `p.map f`. -/
theorem map_baseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] (f : M →ₗ[A] N)
    (p : Submodule A M) :
    Submodule.map (LinearMap.baseChange B f) (Submodule.baseChange B p)
      = Submodule.baseChange B (Submodule.map f p) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span,
    Submodule.map_span]
  congr 1
  rw [Submodule.map_coe, Submodule.map_coe, Submodule.map_coe,
    Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp [TensorProduct.mk_apply, LinearMap.baseChange_tmul]

/-- The range of `f.baseChange B` is the base change of the range of `f`. -/
theorem range_baseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N] (f : M →ₗ[A] N) :
    LinearMap.range (LinearMap.baseChange B f) = Submodule.baseChange B (LinearMap.range f) := by
  rw [LinearMap.range_eq_map, LinearMap.range_eq_map, ← Submodule.baseChange_top (R := A) (A := B),
    map_baseChange]

/-- For `a ∈ J`, the multiple `a • z` of any `z : B ⊗[A] N` lies in the base change of `J • ⊤`. -/
theorem smul_mem_baseChange {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (J : Ideal A) (a : A) (ha : a ∈ J) (z : B ⊗[A] N) :
    a • z ∈ Submodule.baseChange B (J • (⊤ : Submodule A N)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
      rw [← TensorProduct.tmul_smul]
      exact Submodule.tmul_mem_baseChange_of_mem b (Submodule.smul_mem_smul ha Submodule.mem_top)
  | add x y hx hy =>
      rw [smul_add]
      exact (Submodule.baseChange B _).add_mem hx hy

/-- For the extension `J.map (algebraMap A B)` of `J`, its action on `⊤ : Submodule B (B ⊗[A] N)`
equals the base change of `J • ⊤`. -/
theorem ideal_smul_top {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (J : Ideal A) :
    (Ideal.map (algebraMap A B) J) • (⊤ : Submodule B (B ⊗[A] N))
      = Submodule.baseChange B (J • (⊤ : Submodule A N)) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro b' hb' z _
    have hspan : Ideal.map (algebraMap A B) J = Ideal.span ((algebraMap A B) '' J) := rfl
    rw [hspan] at hb'
    induction hb' using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        rw [algebraMap_smul]
        exact smul_mem_baseChange J a ha z
    | zero => simp
    | add x y _ _ ihx ihy =>
        rw [add_smul]
        exact (Submodule.baseChange B _).add_mem ihx ihy
    | smul b x _ ih =>
        rw [smul_assoc]
        exact (Submodule.baseChange B _).smul_mem b ih
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    intro w hw
    simp only [Submodule.map_coe, Set.mem_image, SetLike.mem_coe] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      show (TensorProduct.mk A B N 1) (r • n) ∈ _
      rw [map_smul, ← algebraMap_smul B r ((TensorProduct.mk A B N 1) n)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · intro x y hx hy
      rw [map_add]
      exact (Ideal.map (algebraMap A B) J • (⊤ : Submodule B (B ⊗[A] N))).add_mem hx hy

/-- The range of `p.subtype.baseChange B` is `p.baseChange B`. -/
theorem range_subtype_baseChange {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (p : Submodule A N) :
    LinearMap.range (LinearMap.baseChange B p.subtype) = Submodule.baseChange B p := by
  rfl

/-- Base change of submodules commutes with arbitrary suprema. No flatness is needed: both sides
are the span over `B` of the same set of pure tensors. -/
theorem baseChange_iSup {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {ι : Sort*} (p : ι → Submodule A M) :
    Submodule.baseChange B (⨆ i, p i) = ⨆ i, Submodule.baseChange B (p i) := by
  rw [Submodule.iSup_eq_span, Submodule.baseChange_span, Set.image_iUnion,
    Submodule.span_iUnion]
  refine iSup_congr fun i => ?_
  rw [← Submodule.baseChange_span, Submodule.span_eq]

/-- The base change of multiplication by a scalar `a : A` is multiplication by its image in `B`. -/
theorem baseChange_smul_id {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] (a : A) :
    LinearMap.baseChange B (a • (LinearMap.id : M →ₗ[A] M)) =
      (algebraMap A B a) • (LinearMap.id : B ⊗[A] M →ₗ[B] B ⊗[A] M) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y =>
      simp only [LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def]
      rw [TensorProduct.smul_tmul]
  | add x y hx hy => simp

/-- Base change along a flat `A`-algebra `B` preserves exactness. -/
private theorem baseChange_exact {A B M N P : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module A M]
    [Module A N] [Module A P] {f : M →ₗ[A] N} {g : N →ₗ[A] P} (h : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange B f) (LinearMap.baseChange B g) := by
  simpa only [LinearMap.baseChange_eq_ltensor] using Module.Flat.lTensor_exact B h

/-- For a flat `A`-algebra `B`, base change commutes with intersections of submodules. -/
@[ega "0 6.1.3" "special case"]
theorem baseChange_inf {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [AddCommGroup N] [Module A N] (p q : Submodule A N) :
    Submodule.baseChange B (p ⊓ q)
      = Submodule.baseChange B p ⊓ Submodule.baseChange B q := by
  refine le_antisymm (le_inf (baseChange_mono inf_le_left) (baseChange_mono inf_le_right)) ?_
  rintro x ⟨hxp, hxq⟩
  rw [← range_subtype_baseChange] at hxp
  obtain ⟨y, hy⟩ := hxp
  set g : p →ₗ[A] (N ⧸ q) := q.mkQ ∘ₗ p.subtype with hg
  have hker : LinearMap.baseChange B g y = 0 := by
    rw [hg, LinearMap.baseChange_comp, LinearMap.comp_apply, hy]
    obtain ⟨z, hz⟩ : x ∈ LinearMap.range (LinearMap.baseChange B q.subtype) := by
      rwa [range_subtype_baseChange]
    rw [← hz]
    exact (baseChange_exact (LinearMap.exact_subtype_mkQ q)).apply_apply_eq_zero z
  obtain ⟨z, hz⟩ := (baseChange_exact (LinearMap.exact_subtype_ker_map g) y).mp hker
  set h : g.ker →ₗ[A] N := p.subtype ∘ₗ g.ker.subtype with hh
  have hxh : x = LinearMap.baseChange B h z := by
    rw [hh, LinearMap.baseChange_comp, LinearMap.comp_apply, hz, hy]
  have hrange : LinearMap.range h ≤ p ⊓ q := by
    rintro w ⟨t, rfl⟩
    have hwq : h t ∈ q := by
      rw [← Submodule.Quotient.mk_eq_zero q]
      exact t.2
    exact ⟨(g.ker.subtype t).2, hwq⟩
  refine baseChange_mono hrange ?_
  rw [← range_baseChange, hxh]
  exact ⟨z, rfl⟩

end ArtinReesBaseChange
