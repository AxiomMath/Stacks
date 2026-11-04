module

public import Mathlib.RingTheory.Length
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The index of a linear map and its additivity under composition

Let `A` be a commutative ring and `g : M →ₗ[A] N` a linear map whose kernel and cokernel both
have finite length over `A`. Its *index* is the integer

`(length A (N ⧸ range g)).toNat - (length A (ker g)).toNat`.

This file proves that the index is additive under composition: for `f : M →ₗ[A] N` and
`g : N →ₗ[A] P` the index of `g ∘ f` is the sum of the indices of `f` and of `g`. The
finiteness needed to say this is proved alongside: the kernel and cokernel of a composite have
finite length as soon as those of the two factors do.

The underlying mechanism is a six-term exact sequence

`0 → ker f → ker (g ∘ f) → ker g → N ⧸ range f → P ⧸ range (g ∘ f) → P ⧸ range g → 0`

whose alternating sum of lengths vanishes. That alternating sum is isolated as
`Module.length_alternating_exact_six`, which is stated for an arbitrary six-term exact sequence
and is the only place where additivity of `Module.length` is used.

## Main results

* `Module.lengthToNat_eq_ker_add_range`: the length of a finite-length module is the length of
  the kernel plus the length of the range of any linear map out of it.
* `Module.length_alternating_exact_six`: the alternating sum of the lengths along a six-term
  exact sequence of finite-length modules vanishes.
* `Module.finiteLength_middle_of_exact`: a module caught between two finite-length modules in
  an exact sequence has finite length.
* `Module.finiteLength_kernel_cokernel_comp`: the kernel and the cokernel of a composite have
  finite length when those of both factors do.
* `Module.lengthIndex_comp`: the index of a composite is the sum of the indices.

## Implementation notes

Lengths are compared in `ℕ∞` through `Module.length_eq_add_of_exact` and then transferred to
`ℕ` by `ENat.toNat`, which is only additive away from `⊤`; that is why every term of the
six-term sequence except the last carries a finite-length hypothesis, and why the arithmetic is
finished by `omega` rather than by `abel`. The length of the last term is finite as a
consequence, but asserting it is not needed.

The six exact sequence connecting the kernels and cokernels of `f`, `g` and `g ∘ f` is built
from `Submodule.inclusion`, `LinearMap.restrict`, `Submodule.mkQ`, `Submodule.mapQ` and
`Submodule.factor`; each of its exactness assertions is an equality of a kernel with a range
of submodules, so `LinearMap.exact_iff` reduces it to a `simp` about those five constructions.
-/

@[expose] public section

universe u

namespace Module

variable {A : Type*} [CommRing A]

/-- The length of a module is the length of the kernel plus the length of the range of any linear
map out of it. -/
private theorem length_eq_ker_add_range {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) :
    Module.length A M = Module.length A (LinearMap.ker g) + Module.length A (LinearMap.range g) :=
  Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by simp))

/-- In an exact sequence `0 → M₁ → M₂ → M₃ → 0` of finite-length modules, the lengths add up in
`ℕ`. -/
private theorem lengthToNat_add_of_exact {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (h₁ : IsFiniteLength A M₁) (h₃ : IsFiniteLength A M₃) :
    (Module.length A M₂).toNat = (Module.length A M₁).toNat + (Module.length A M₃).toNat := by
  rw [Module.length_eq_add_of_exact f g hf hg hfg,
    ENat.toNat_add (Module.length_ne_top_iff.mpr h₁) (Module.length_ne_top_iff.mpr h₃)]

/-- A module of finite length splits the length of any linear map out of it: its length is the
length of the kernel plus the length of the range. -/
public theorem lengthToNat_eq_ker_add_range {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) (hM : IsFiniteLength A M) :
    (Module.length A M).toNat = (Module.length A (LinearMap.ker g)).toNat +
      (Module.length A (LinearMap.range g)).toNat :=
  lengthToNat_add_of_exact _ g.rangeRestrict (Submodule.subtype_injective _)
    g.surjective_rangeRestrict (LinearMap.exact_iff.mpr (by simp))
    (IsFiniteLength.of_injective (f := (LinearMap.ker g).subtype) hM
      (Submodule.subtype_injective _))
    (IsFiniteLength.of_surjective (f := g.rangeRestrict) hM g.surjective_rangeRestrict)

/-- Along an exact sequence `0 → M₀ → M₁ → M₂ → M₃ → M₄ → M₅ → 0` whose first five terms have
finite length, the lengths alternate: the sum of the lengths in even position equals the sum of
the lengths in odd position. -/
@[ega "0 11.10.2" "special case"]
public theorem length_alternating_exact_six
    {M₀ M₁ M₂ M₃ M₄ M₅ : Type*}
    [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    [AddCommGroup M₄] [Module A M₄] [AddCommGroup M₅] [Module A M₅]
    (f₀ : M₀ →ₗ[A] M₁) (f₁ : M₁ →ₗ[A] M₂) (f₂ : M₂ →ₗ[A] M₃)
    (f₃ : M₃ →ₗ[A] M₄) (f₄ : M₄ →ₗ[A] M₅)
    (h₀ : Function.Injective f₀) (h₄ : Function.Surjective f₄)
    (e₀ : Function.Exact f₀ f₁) (e₁ : Function.Exact f₁ f₂)
    (e₂ : Function.Exact f₂ f₃) (e₃ : Function.Exact f₃ f₄)
    (hM₀ : IsFiniteLength A M₀) (hM₁ : IsFiniteLength A M₁)
    (hM₂ : IsFiniteLength A M₂) (hM₃ : IsFiniteLength A M₃)
    (hM₄ : IsFiniteLength A M₄) :
    (Module.length A M₀).toNat + (Module.length A M₂).toNat +
        (Module.length A M₄).toNat =
      (Module.length A M₁).toNat + (Module.length A M₃).toNat +
        (Module.length A M₅).toNat := by
  have hlen₀ := lengthToNat_eq_ker_add_range f₀ hM₀
  have hlen₁ := lengthToNat_eq_ker_add_range f₁ hM₁
  have hlen₂ := lengthToNat_eq_ker_add_range f₂ hM₂
  have hlen₃ := lengthToNat_eq_ker_add_range f₃ hM₃
  have hlen₄ := lengthToNat_eq_ker_add_range f₄ hM₄
  have hker₀ : (Module.length A (LinearMap.ker f₀)).toNat = 0 := by
    rw [LinearMap.ker_eq_bot.mpr h₀]
    simp
  rw [hker₀] at hlen₀
  rw [← (LinearMap.exact_iff.mp e₀).symm] at hlen₁
  rw [← (LinearMap.exact_iff.mp e₁).symm] at hlen₂
  rw [← (LinearMap.exact_iff.mp e₂).symm] at hlen₃
  rw [← (LinearMap.exact_iff.mp e₃).symm, LinearMap.range_eq_top.mpr h₄] at hlen₄
  have hlen₄' : (Module.length A M₄).toNat =
      (Module.length A (LinearMap.range f₃)).toNat + (Module.length A M₅).toNat := by
    simpa using hlen₄
  omega

/-- A module squeezed between two finite-length modules in an exact sequence has finite
length. -/
public theorem finiteLength_middle_of_exact {M N L : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup L] [Module A L]
    (a : M →ₗ[A] N) (b : N →ₗ[A] L) (hab : Function.Exact a b)
    (hM : IsFiniteLength A M) (hL : IsFiniteLength A L) : IsFiniteLength A N := by
  have hk : IsFiniteLength A (LinearMap.ker b) := by
    rw [LinearMap.exact_iff.mp hab]
    exact IsFiniteLength.of_surjective hM a.surjective_rangeRestrict
  have hr : IsFiniteLength A (LinearMap.range b) :=
    IsFiniteLength.of_injective hL (Submodule.subtype_injective _)
  rw [← Module.length_ne_top_iff, length_eq_ker_add_range b]
  exact WithTop.add_ne_top.mpr
    ⟨Module.length_ne_top_iff.mpr hk, Module.length_ne_top_iff.mpr hr⟩

section Comparison

variable {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P)

/-- The range of `f` is carried by `g` into the range of `g ∘ f`, so `g` descends to the
cokernels. -/
private theorem range_le_comap_range_comp :
    LinearMap.range f ≤ Submodule.comap g (LinearMap.range (g.comp f)) := by
  rw [← Submodule.map_le_iff_le_comap, LinearMap.range_comp]

/-- The second map of the six-term sequence comparing `f`, `g` and `g ∘ f`: the inclusion of
the kernel of `f` into the kernel of the composite. -/
private def kerInclusionComp : LinearMap.ker f →ₗ[A] LinearMap.ker (g.comp f) :=
  Submodule.inclusion (LinearMap.ker_le_ker_comp f g)

/-- The third map of the six-term sequence: `f` restricted to the kernel of the composite
lands in the kernel of `g`. -/
private def kerCompToKer : LinearMap.ker (g.comp f) →ₗ[A] LinearMap.ker g :=
  f.restrict (by simp)

/-- The fourth map of the six-term sequence: the kernel of `g` mapped into the cokernel
of `f`. -/
private def kerToCokerComp : LinearMap.ker g →ₗ[A] N ⧸ LinearMap.range f :=
  (LinearMap.range f).mkQ.comp (LinearMap.ker g).subtype

/-- The fifth map of the six-term sequence: `g` descended to the cokernels of `f` and of the
composite. -/
private def cokerMapComp : N ⧸ LinearMap.range f →ₗ[A] P ⧸ LinearMap.range (g.comp f) :=
  (LinearMap.range f).mapQ (LinearMap.range (g.comp f)) g (range_le_comap_range_comp f g)

/-- The sixth map of the six-term sequence: the projection of the cokernel of the composite
onto the cokernel of `g`. -/
private def cokerCompToCoker : P ⧸ LinearMap.range (g.comp f) →ₗ[A] P ⧸ LinearMap.range g :=
  Submodule.factor (LinearMap.range_comp_le_range f g)

private theorem kerInclusionComp_injective : Function.Injective (kerInclusionComp f g) :=
  Submodule.inclusion_injective (LinearMap.ker_le_ker_comp f g)

private theorem cokerCompToCoker_surjective : Function.Surjective (cokerCompToCoker f g) :=
  Submodule.factor_surjective (LinearMap.range_comp_le_range f g)

private theorem exact_kerInclusionComp_kerCompToKer :
    Function.Exact (kerInclusionComp f g) (kerCompToKer f g) := by
  rw [LinearMap.exact_iff]
  simp [kerInclusionComp, kerCompToKer, LinearMap.ker_restrict, Submodule.range_inclusion]

private theorem exact_kerCompToKer_kerToCokerComp :
    Function.Exact (kerCompToKer f g) (kerToCokerComp f g) := by
  rw [LinearMap.exact_iff]
  have hker : LinearMap.ker (kerToCokerComp f g) =
      Submodule.comap (LinearMap.ker g).subtype (LinearMap.range f) := by
    simp [kerToCokerComp, LinearMap.ker_comp]
  rw [hker]
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, hx⟩ : (y : N) ∈ LinearMap.range f := hy
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, hx] using y.2
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨(x : M), rfl⟩

private theorem exact_kerToCokerComp_cokerMapComp :
    Function.Exact (kerToCokerComp f g) (cokerMapComp f g) := by
  rw [LinearMap.exact_iff]
  simp [kerToCokerComp, cokerMapComp, LinearMap.range_comp, Submodule.ker_mapQ,
    Submodule.comap_map_eq]

private theorem exact_cokerMapComp_cokerCompToCoker :
    Function.Exact (cokerMapComp f g) (cokerCompToCoker f g) := by
  rw [LinearMap.exact_iff]
  simp [cokerMapComp, cokerCompToCoker, Submodule.factor, Submodule.ker_mapQ,
    Submodule.range_mapQ]

/-- The kernel and the cokernel of a composite have finite length as soon as the kernels and
cokernels of both factors do. -/
public theorem finiteLength_kernel_cokernel_comp
    (hkf : IsFiniteLength A (LinearMap.ker f))
    (hcf : IsFiniteLength A (N ⧸ LinearMap.range f))
    (hkg : IsFiniteLength A (LinearMap.ker g))
    (hcg : IsFiniteLength A (P ⧸ LinearMap.range g)) :
    IsFiniteLength A (LinearMap.ker (g.comp f)) ∧
      IsFiniteLength A (P ⧸ LinearMap.range (g.comp f)) :=
  ⟨finiteLength_middle_of_exact _ _ (exact_kerInclusionComp_kerCompToKer f g) hkf hkg,
    finiteLength_middle_of_exact _ _ (exact_cokerMapComp_cokerCompToCoker f g) hcf hcg⟩

/-- **The index of a composite is the sum of the indices.** For linear maps `f` and `g` whose
kernels and cokernels have finite length, the cokernel length minus the kernel length is
additive along `g ∘ f`. -/
public theorem lengthIndex_comp
    (hkf : IsFiniteLength A (LinearMap.ker f))
    (hcf : IsFiniteLength A (N ⧸ LinearMap.range f))
    (hkg : IsFiniteLength A (LinearMap.ker g))
    (hkcomp : IsFiniteLength A (LinearMap.ker (g.comp f)))
    (hccomp : IsFiniteLength A (P ⧸ LinearMap.range (g.comp f))) :
    ((Module.length A (P ⧸ LinearMap.range (g.comp f))).toNat : ℤ) -
        ((Module.length A (LinearMap.ker (g.comp f))).toNat : ℤ) =
      (((Module.length A (N ⧸ LinearMap.range f)).toNat : ℤ) -
          ((Module.length A (LinearMap.ker f)).toNat : ℤ)) +
        (((Module.length A (P ⧸ LinearMap.range g)).toNat : ℤ) -
          ((Module.length A (LinearMap.ker g)).toNat : ℤ)) := by
  have hlen := length_alternating_exact_six (kerInclusionComp f g) (kerCompToKer f g)
    (kerToCokerComp f g) (cokerMapComp f g) (cokerCompToCoker f g)
    (kerInclusionComp_injective f g) (cokerCompToCoker_surjective f g)
    (exact_kerInclusionComp_kerCompToKer f g) (exact_kerCompToKer_kerToCokerComp f g)
    (exact_kerToCokerComp_cokerMapComp f g) (exact_cokerMapComp_cokerCompToCoker f g)
    hkf hkcomp hkg hcf hccomp
  omega

end Comparison

section Ladder

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]
  [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
  [AddCommGroup N₃] [Module A N₃]

/-- **The index of a linear map is additive along a ladder of short exact sequences.** Given a
commutative ladder whose rows `0 → M₁ → M₂ → M₃ → 0` and `0 → N₁ → N₂ → N₃ → 0` are exact and
whose outer verticals `a` and `c` have finite-length kernel and cokernel, the middle vertical
`b` has finite-length kernel and cokernel and its index is the sum of the two outer indices. -/
public theorem lengthIndex_add_of_ladder
    (u : M₁ →ₗ[A] M₂) (v : M₂ →ₗ[A] M₃) (s : N₁ →ₗ[A] N₂) (t : N₂ →ₗ[A] N₃)
    (a : M₁ →ₗ[A] N₁) (b : M₂ →ₗ[A] N₂) (c : M₃ →ₗ[A] N₃)
    (hu : Function.Injective u) (hv : Function.Surjective v) (huv : Function.Exact u v)
    (hs : Function.Injective s) (ht : Function.Surjective t) (hst : Function.Exact s t)
    (hleft : s.comp a = b.comp u) (hright : t.comp b = c.comp v)
    (hka : IsFiniteLength A (LinearMap.ker a))
    (hca : IsFiniteLength A (N₁ ⧸ LinearMap.range a))
    (hkc : IsFiniteLength A (LinearMap.ker c))
    (hcc : IsFiniteLength A (N₃ ⧸ LinearMap.range c)) :
    IsFiniteLength A (LinearMap.ker b) ∧
      IsFiniteLength A (N₂ ⧸ LinearMap.range b) ∧
      ((Module.length A (N₂ ⧸ LinearMap.range b)).toNat : ℤ) -
          ((Module.length A (LinearMap.ker b)).toNat : ℤ) =
        (((Module.length A (N₁ ⧸ LinearMap.range a)).toNat : ℤ) -
            ((Module.length A (LinearMap.ker a)).toNat : ℤ)) +
          (((Module.length A (N₃ ⧸ LinearMap.range c)).toNat : ℤ) -
            ((Module.length A (LinearMap.ker c)).toNat : ℤ)) := by
  have hrw : ∀ x : M₂, t (b x) = c (v x) := LinearMap.congr_fun hright
  have hlw : ∀ y : M₁, s (a y) = b (u y) := LinearMap.congr_fun hleft
  set W : Submodule A M₂ := Submodule.comap v (LinearMap.ker c) with hWdef
  have hmemW : ∀ x : M₂, x ∈ W ↔ c (v x) = 0 := fun x => Iff.rfl
  have huW : ∀ y : M₁, u y ∈ W := fun y => by
    rw [hmemW, huv.apply_apply_eq_zero y, map_zero]
  set ι : M₁ →ₗ[A] W := LinearMap.codRestrict W u huW with hιdef
  have hιval : ∀ y : M₁, (ι y : M₂) = u y := fun _ => rfl
  have hιinj : Function.Injective ι := fun y y' h => hu (by
    simpa only [hιval] using congrArg (Subtype.val (p := fun x => x ∈ W)) h)
  have hbW : ∀ x : M₂, x ∈ W → b x ∈ LinearMap.range s := fun x hx => by
    rw [← LinearMap.exact_iff.mp hst, LinearMap.mem_ker, hrw x]
    exact (hmemW x).mp hx
  obtain ⟨β, hβ⟩ : ∃ β : W →ₗ[A] N₁, ∀ x : W, s (β x) = b (x : M₂) :=
    ⟨(LinearEquiv.ofInjective s hs).symm.toLinearMap.comp (b.restrict hbW), fun x => by
      have h := (LinearEquiv.ofInjective s hs).apply_symm_apply (b.restrict hbW x)
      have h2 := congrArg (Subtype.val (p := fun n => n ∈ LinearMap.range s)) h
      simpa only [LinearEquiv.ofInjective_apply, LinearMap.coe_restrict_apply,
        LinearMap.comp_apply, LinearMap.coe_coe, LinearEquiv.coe_coe] using h2⟩
  have hvW : ∀ x : M₂, x ∈ W → v x ∈ LinearMap.ker c := fun _ hx => hx
  set w : W →ₗ[A] LinearMap.ker c := v.restrict hvW with hwdef
  have hwval : ∀ x : W, (w x : M₃) = v (x : M₂) := fun _ => rfl
  have hwsurj : Function.Surjective w := fun y => by
    obtain ⟨x, hx⟩ := hv (y : M₃)
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · rw [hmemW, hx]; exact y.2
    · rw [hwval]; exact hx
  have hwker : LinearMap.ker w = LinearMap.range ι := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · have hzero : v (x : M₂) = 0 := by
        simpa only [hwval, ZeroMemClass.coe_zero] using
          congrArg (Subtype.val (p := fun y => y ∈ LinearMap.ker c))
            (LinearMap.mem_ker.mp hx)
      obtain ⟨y, hy⟩ := (LinearMap.exact_iff.mp huv ▸ hzero : (x : M₂) ∈ LinearMap.range u)
      exact ⟨y, Subtype.ext (by rw [hιval]; exact hy)⟩
    · obtain ⟨y, rfl⟩ := hx
      refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
      rw [hwval, hιval, huv.apply_apply_eq_zero y, ZeroMemClass.coe_zero]
  have hβι : β.comp ι = a := by
    ext y
    exact hs (by rw [LinearMap.comp_apply, hβ (ι y), hιval, ← hlw y])
  have hkerble : LinearMap.ker b ≤ W := fun x hx => by
    rw [hmemW, ← hrw x, (LinearMap.mem_ker.mp hx), map_zero]
  have hkermap : Submodule.map W.subtype (LinearMap.ker β) = LinearMap.ker b := by
    refine le_antisymm ?_ (fun x hx => ?_)
    · rintro x ⟨x₀, hx₀, rfl⟩
      have hz : β x₀ = 0 := hx₀
      refine LinearMap.mem_ker.mpr ?_
      show b (x₀ : M₂) = 0
      rw [← hβ x₀, hz, map_zero]
    · refine ⟨⟨x, hkerble hx⟩, ?_, rfl⟩
      show β ⟨x, hkerble hx⟩ = 0
      exact hs (by rw [hβ ⟨x, hkerble hx⟩, map_zero]; exact LinearMap.mem_ker.mp hx)
  have eKer : (LinearMap.ker β) ≃ₗ[A] (LinearMap.ker b) :=
    (Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W)
      (LinearMap.ker β)).trans (LinearEquiv.ofEq _ _ hkermap)
  have eQuot : (W ⧸ LinearMap.range ι) ≃ₗ[A] (LinearMap.ker c) :=
    (Submodule.quotEquivOfEq _ _ hwker.symm).trans
      (LinearMap.quotKerEquivOfSurjective w hwsurj)
  have hk₁mem : ∀ y : M₁, y ∈ LinearMap.ker a → ι y ∈ LinearMap.ker β := fun y hy =>
    LinearMap.mem_ker.mpr (by
      rw [← LinearMap.comp_apply, hβι]; exact LinearMap.mem_ker.mp hy)
  have hkβ : IsFiniteLength A (LinearMap.ker β) := by
    refine finiteLength_middle_of_exact (ι.restrict hk₁mem)
      (w.comp (LinearMap.ker β).subtype) ?_ hka hkc
    rw [LinearMap.exact_iff]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · have hxw : ((x : W)) ∈ LinearMap.ker w :=
        LinearMap.mem_ker.mpr (by
          have h := LinearMap.mem_ker.mp hx
          rwa [LinearMap.comp_apply] at h)
      obtain ⟨y, hy⟩ := hwker ▸ hxw
      have hya : y ∈ LinearMap.ker a := LinearMap.mem_ker.mpr (by
        rw [← hβι, LinearMap.comp_apply, hy]
        exact x.2)
      exact ⟨⟨y, hya⟩, Subtype.ext hy⟩
    · obtain ⟨y, rfl⟩ := hx
      refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
      show (w ((ι.restrict hk₁mem) y : W) : M₃) = ((0 : LinearMap.ker c) : M₃)
      rw [hwval, ZeroMemClass.coe_zero]
      show v (ι (y : M₁) : M₂) = 0
      rw [hιval, huv.apply_apply_eq_zero]
  have hkb : IsFiniteLength A (LinearMap.ker b) := eKer.isFiniteLength hkβ
  have hrange : LinearMap.range a ≤ LinearMap.range β := by
    rintro n ⟨y, rfl⟩
    exact ⟨ι y, by rw [← LinearMap.comp_apply, hβι]⟩
  have hcβ : IsFiniteLength A (N₁ ⧸ LinearMap.range β) :=
    IsFiniteLength.of_surjective hca (Submodule.factor_surjective hrange)
  have hsbarle : LinearMap.range β ≤ Submodule.comap s (LinearMap.range b) := by
    rintro n ⟨x, rfl⟩
    exact ⟨(x : M₂), (hβ x).symm⟩
  have htbarle : LinearMap.range b ≤ Submodule.comap t (LinearMap.range c) := by
    rintro n ⟨x, rfl⟩
    exact ⟨v x, (hrw x).symm⟩
  set sbar : (N₁ ⧸ LinearMap.range β) →ₗ[A] (N₂ ⧸ LinearMap.range b) :=
    Submodule.mapQ _ _ s hsbarle with hsbardef
  set tbar : (N₂ ⧸ LinearMap.range b) →ₗ[A] (N₃ ⧸ LinearMap.range c) :=
    Submodule.mapQ _ _ t htbarle with htbardef
  have hsbarinj : Function.Injective sbar := by
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun z hz => ?_) bot_le
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range β) z
    have hmem : s n ∈ LinearMap.range b := by
      have h := LinearMap.mem_ker.mp hz
      rw [hsbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at h
      exact h
    obtain ⟨x, hx⟩ := hmem
    have hxW : x ∈ W := by
      rw [hmemW, ← hrw x, hx]
      exact hst.apply_apply_eq_zero n
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨⟨x, hxW⟩, hs (by rw [hβ ⟨x, hxW⟩]; exact hx)⟩
  have htbarsurj : Function.Surjective tbar := fun z => by
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range c) z
    obtain ⟨n₂, rfl⟩ := ht n
    exact ⟨Submodule.mkQ _ n₂, by
      rw [htbardef, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]⟩
  have hexact : Function.Exact sbar tbar := by
    rw [LinearMap.exact_iff]
    refine le_antisymm (fun z hz => ?_) (LinearMap.range_le_ker_iff.mpr ?_)
    · obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range b) z
      have hmem : t n ∈ LinearMap.range c := by
        have h := LinearMap.mem_ker.mp hz
        rw [htbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
          Submodule.Quotient.mk_eq_zero] at h
        exact h
      obtain ⟨y, hy⟩ := hmem
      obtain ⟨x, hx⟩ := hv y
      have hdiff : n - b x ∈ LinearMap.range s := by
        rw [← LinearMap.exact_iff.mp hst, LinearMap.mem_ker, map_sub, hrw x, hx, hy, sub_self]
      obtain ⟨n₁, hn₁⟩ := hdiff
      refine ⟨Submodule.mkQ (LinearMap.range β) n₁, ?_⟩
      rw [hsbardef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
      refine (Submodule.Quotient.eq _).mpr ⟨-x, ?_⟩
      rw [map_neg, hn₁]
      abel
    · apply LinearMap.ext
      intro z
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range β) z
      rw [LinearMap.comp_apply, hsbardef, htbardef, Submodule.mkQ_apply,
        Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨0, by rw [map_zero, hst.apply_apply_eq_zero n]⟩
  have hcb : IsFiniteLength A (N₂ ⧸ LinearMap.range b) :=
    finiteLength_middle_of_exact sbar tbar hexact hcβ hcc
  have hlenC := lengthToNat_add_of_exact sbar tbar hsbarinj htbarsurj hexact hcβ hcc
  have hkι : IsFiniteLength A (LinearMap.ker ι) := by
    rw [LinearMap.ker_eq_bot.mpr hιinj]
    exact IsFiniteLength.of_subsingleton
  have hcι : IsFiniteLength A (W ⧸ LinearMap.range ι) := eQuot.symm.isFiniteLength hkc
  have hindex := lengthIndex_comp ι β hkι hcι hkβ (by rw [hβι]; exact hka)
    (by rw [hβι]; exact hca)
  rw [hβι] at hindex
  have hkιzero : (Module.length A (LinearMap.ker ι)).toNat = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hιinj, Module.length_bot]
    rfl
  have hcιlen : (Module.length A (W ⧸ LinearMap.range ι)).toNat =
      (Module.length A (LinearMap.ker c)).toNat := by rw [eQuot.length_eq]
  have hkblen : (Module.length A (LinearMap.ker β)).toNat =
      (Module.length A (LinearMap.ker b)).toNat := by rw [eKer.length_eq]
  rw [hkιzero, hcιlen, hkblen] at hindex
  exact ⟨hkb, hcb, by rw [hlenC]; omega⟩

end Ladder

end Module

end
