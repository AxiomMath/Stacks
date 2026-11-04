module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeTwoCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.LocallyConstantGModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locally constant coinduced module is acyclic in low degrees, and lifting along it

Let `G` be a profinite group and `B` an abelian group. The locally constant functions `G → B`
(`Stacks.GroupCohomology.lcFun`), on which `G` acts by right translation, `(g • f)(x) = f(x g)`,
have no cochain-level cohomology in degrees one and two, by explicit contracting formulas:

* a locally constant `1`-cocycle `c` is `dZero z` for `z(x) = c(x)(1)`;
* a locally constant `2`-cocycle `f` is `dOne b` for `b(g)(x) = f(x, g)(1)`.

A discrete `G`-module `M` embeds equivariantly into the locally constant functions `G → M` by
`m ↦ (x ↦ x • m)` (`Stacks.GroupCohomology.orbitMap`). Together with three lifting statements along
a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `G`-modules, all at the level of cochains, this is
the cochain half of the comparison between derived-functor cohomology and cochain cohomology in
degree two.

## Main results

* `Stacks.GroupCohomology.vanishesOne_lcFun`, `Stacks.GroupCohomology.vanishesTwo_lcFun`:
  the locally constant coinduced module is acyclic in degrees one and two, at the cochain level.
* `Stacks.GroupCohomology.exists_invariant_lift_of_vanishesOne`: invariants lift along
  `M₂ → M₃` when `M₁` has no `1`-cocycles but coboundaries.
* `Stacks.GroupCohomology.vanishesOne_of_exists_invariant_lift`: `M₁` has no `1`-cocycles but
  coboundaries when `M₂` has none and invariants lift along `M₂ → M₃`.
* `Stacks.GroupCohomology.vanishesTwo_of_vanishesOne_quotient`: `M₁` has no `2`-cocycles but
  coboundaries when `M₂` has none and `M₃` has no `1`-cocycles but coboundaries.
-/

@[expose] public noncomputable section

open groupCohomology

universe t u v w

namespace Stacks.GroupCohomology

/-! ### The locally constant coinduced module -/

section Coinduced

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {B : Type v} [AddCommGroup B]

/-- **The locally constant functions have no `1`-cocycles but coboundaries**: a locally
constant `1`-cocycle `c` with values in `lcFun G B` is `dZero z` for `z(x) = c(x)(1)`. -/
@[sga "3 I 5.2.2" "special case"]
theorem vanishesOne_lcFun : VanishesOne G (lcFun G B) := by
  intro c hc hcoc
  refine ⟨⟨fun x ↦ ((c x : lcFun G B) : G → B) 1,
    hc.comp fun f : lcFun G B ↦ (f : G → B) 1⟩, funext fun g ↦ Subtype.ext ?_⟩
  funext x
  have h := congrArg (fun f : lcFun G B ↦ (f : G → B) 1) (hcoc x g)
  simp only [AddSubgroup.coe_add, Pi.add_apply, lcFun_smul_coe, one_mul] at h
  simp only [dZero_apply, AddSubgroup.coe_sub, Pi.sub_apply, lcFun_smul_coe]
  rw [h]
  abel

/-- A function on `G` invariant under right translation by an open subgroup is locally
constant. -/
theorem isLocallyConstant_of_forall_mul_right_eq {α : Type*} (N : OpenSubgroup G) {φ : G → α}
    (hφ : ∀ x n : G, n ∈ N → φ (x * n) = φ x) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y : G ↦ x⁻¹ * y) ⁻¹' (N : Set G), N.isOpen.preimage (by fun_prop),
    by simp [N.one_mem], fun y hy ↦ ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe] at hy
  rw [← hφ x _ hy, mul_inv_cancel_left]

/-- **The locally constant functions have no `2`-cocycles but coboundaries**: a locally
constant `2`-cocycle `f` with values in `lcFun G B` is `dOne b` for `b(g)(x) = f(x, g)(1)`. The
cochain `b` is locally constant because on a profinite group `f` is right invariant under an
open subgroup. -/
@[sga "3 I 5.2.2" "special case"]
theorem vanishesTwo_lcFun [CompactSpace G] [TotallyDisconnectedSpace G] :
    VanishesTwo G (lcFun G B) := by
  intro f hf hcoc
  obtain ⟨N, hN⟩ := exists_openSubgroup_forall_mul_right_eq₂ hf
  let b : G → lcFun G B := fun g ↦
    ⟨fun x ↦ ((f (x, g) : lcFun G B) : G → B) 1,
      (hf.comp_continuous (by fun_prop : Continuous fun x : G ↦ (x, g))).comp
        fun f : lcFun G B ↦ (f : G → B) 1⟩
  refine ⟨b, isLocallyConstant_of_forall_mul_right_eq N fun g n hn ↦ ?_, funext fun p ↦ ?_⟩
  · refine Subtype.ext (funext fun x ↦ ?_)
    show ((f (x, g * n) : lcFun G B) : G → B) 1 = ((f (x, g) : lcFun G B) : G → B) 1
    have := hN x g 1 n N.one_mem hn
    rw [mul_one] at this
    rw [this]
  · obtain ⟨g, h⟩ := p
    refine Subtype.ext (funext fun x ↦ ?_)
    have hc := congrArg (fun f : lcFun G B ↦ (f : G → B) 1) (hcoc x g h)
    simp only [AddSubgroup.coe_add, Pi.add_apply, lcFun_smul_coe, one_mul] at hc
    simp only [dOne_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub, Pi.add_apply, Pi.sub_apply,
      lcFun_smul_coe, b]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hc
    rw [← hc]
    abel

end Coinduced

/-! ### Lifting along a short exact sequence, at the level of cochains -/

section Lifting

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M₁ : Type v} {M₂ : Type w} {M₃ : Type t} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [DistribMulAction G M₁] [DistribMulAction G M₂] [DistribMulAction G M₃]
  (i : M₁ →+ M₂) (p : M₂ →+ M₃)
  (hi_smul : ∀ (g : G) (m : M₁), i (g • m) = g • i m)
  (hp_smul : ∀ (g : G) (m : M₂), p (g • m) = g • p m)
  (hi : Function.Injective i) (hp : Function.Surjective p)
  (hpi : ∀ m, p (i m) = 0) (hex : ∀ m, p m = 0 → ∃ m₁, i m₁ = m)

include hi_smul hp_smul hi hp hpi hex

/-- **Invariants lift along `M₂ → M₃` when `H ¹(G, M₁) = 0` at the cochain level.** A lift `x` of
an invariant `y` defines the locally constant `1`-cocycle `g ↦ g • x - x` of `M₁`; subtracting
a trivializing element of `M₁` from `x` makes it invariant. -/
theorem exists_invariant_lift_of_vanishesOne (hM₂ : HasOpenStabilizers G M₂)
    (h₁ : VanishesOne G M₁) (y : M₃) (hy : ∀ g : G, g • y = y) :
    ∃ x : M₂, (∀ g : G, g • x = x) ∧ p x = y := by
  obtain ⟨x, rfl⟩ := hp y
  have hker : ∀ g : G, ∃ m : M₁, i m = g • x - x := fun g ↦
    hex _ (by rw [map_sub, hp_smul, hy, sub_self])
  choose c hc using hker
  have hcoc : IsCocycle₁ c := by
    intro g h
    refine hi ?_
    rw [map_add, hi_smul, hc, hc, hc, smul_sub, mul_smul]
    abel
  have hcl : IsLocallyConstant c := by
    exact isLocallyConstant_of_comp_injective hi
      (by simp only [hc]; exact isLocallyConstant_dZero hM₂ x)
  obtain ⟨m, hm⟩ := h₁ c hcl hcoc
  refine ⟨x - i m, fun g ↦ ?_, by rw [map_sub, hpi, sub_zero]⟩
  have hmg : g • m = c g + m := by
    have := congrFun hm g
    rw [dZero_apply] at this
    rw [← this]
    abel
  rw [smul_sub, ← hi_smul, hmg, map_add, hc]
  abel

/-- **`H ¹(G, M₁) = 0` at the cochain level from `H ¹(G, M₂) = 0` and lifting of invariants.**
A locally constant `1`-cocycle `c` of `M₁` is `dZero z` in `M₂`; the image of `z` in `M₃` is
invariant, so lifts to an invariant `w`, and `z - w` comes from a trivializing element of `M₁`. -/
theorem vanishesOne_of_exists_invariant_lift (h₂ : VanishesOne G M₂)
    (hlift : ∀ y : M₃, (∀ g : G, g • y = y) → ∃ x : M₂, (∀ g : G, g • x = x) ∧ p x = y) :
    VanishesOne G M₁ := by
  intro c hcl hcoc
  obtain ⟨z, hz⟩ := h₂ (i ∘ c) (hcl.comp i) (isCocycle₁_comp i hi_smul hcoc)
  have hzg : ∀ g : G, g • z - z = i (c g) := fun g ↦ congrFun hz g
  obtain ⟨w, hw, hwz⟩ := hlift (p z) fun g ↦ by
    rw [← hp_smul, ← sub_eq_zero, ← map_sub, hzg, hpi]
  obtain ⟨m, hm⟩ := hex (z - w) (by rw [map_sub, hwz, sub_self])
  refine ⟨m, funext fun g ↦ hi ?_⟩
  rw [dZero_apply, map_sub, hi_smul, hm, smul_sub, hw, ← hzg]
  abel

/-- **`H ²(G, M₁) = 0` at the cochain level from `H ²(G, M₂) = 0` and `H ¹(G, M₃) = 0`.** A
locally constant `2`-cocycle `f` of `M₁` is `dOne b` in `M₂`; the image of `b` in `M₃` is a
`1`-cocycle, hence `dZero y`; lifting `y` to `x` and subtracting `dZero x` from `b` leaves a
cochain with values in `M₁` whose coboundary is `f`. -/
theorem vanishesTwo_of_vanishesOne_quotient (hM₂ : HasOpenStabilizers G M₂)
    (h₂ : VanishesTwo G M₂) (h₃ : VanishesOne G M₃) : VanishesTwo G M₁ := by
  intro f hfl hfcoc
  obtain ⟨b, hbl, hb⟩ := h₂ (i ∘ f) (hfl.comp i) (isCocycle₂_comp i hi_smul hfcoc)
  have hpb : IsCocycle₁ (p ∘ b) := by
    intro g h
    have := congrArg p (congrFun hb (g, h))
    simp only [dOne_apply, Function.comp_apply, map_add, map_sub, hp_smul, hpi] at this
    simp only [Function.comp_apply]
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  obtain ⟨y, hy⟩ := h₃ (p ∘ b) (hbl.comp p) hpb
  obtain ⟨x, rfl⟩ := hp y
  have hker : ∀ g : G, ∃ m : M₁, i m = b g - dZero x g := fun g ↦ hex _ (by
    rw [map_sub, ← Function.comp_apply (f := p) (g := b), ← hy, dZero_apply, dZero_apply,
      map_sub, hp_smul, sub_self])
  choose a ha using hker
  have hal : IsLocallyConstant a := by
    refine isLocallyConstant_of_comp_injective hi ?_
    simp only [ha]
    exact hbl.comp₂ (isLocallyConstant_dZero hM₂ x) (· - ·)
  refine ⟨a, hal, funext fun q ↦ hi ?_⟩
  obtain ⟨g, h⟩ := q
  have := congrFun hb (g, h)
  simp only [dOne_apply, Function.comp_apply] at this
  simp only [dOne_apply, map_add, map_sub, hi_smul, ha, dZero_apply, smul_sub, mul_smul]
  rw [← this]
  abel

end Lifting

end Stacks.GroupCohomology

end
