module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.ExtVanishingRange

/-!
# `Ext` along the reduction maps between the quotients by the powers of a regular element

Let `A` be a commutative ring, `f ∈ A` an element acting regularly on an `A`-module `M`, and `K`
an object of the derived category of `A`-modules. The quotients `M/f^nM` form a tower under the
reduction maps, and `Ext` into `K` turns it into a tower the other way,

  `Ext^i_A(M/fM, K) ⟶ Ext^i_A(M/f^{n+1}M, K)`.

This file identifies that map on the part of `Ext^i_A(M/fM, K)` coming from the connecting map of
the long exact sequence of `0 → M → M → M/fM → 0`: the square

  `0 → M --f^{n+1}--> M --> M/f^{n+1}M → 0`
  `      ↓f^n          ↓1       ↓`
  `0 → M --f--------> M --> M/fM → 0`

is a morphism of short exact sequences, so the connecting maps are compatible with multiplication
by `f^n`. Two consequences follow. First, if `Ext^{i+1}_A(M, K)` has no `f`-torsion then the whole
of `Ext^{i+1}_A(M/fM, K)` comes from the connecting map; and second, the connecting map for
`f^{n+1}` kills `f^{n+1}Ext^i_A(M, K)`. Together they give the vanishing of the reduction map on
`Ext` as soon as multiplication by `f^n` from `Ext^i_A(M, K)/f` to `Ext^i_A(M, K)/f^{n+1}` is zero.

That is the last step of the proof of [Stacks, Tag 0DXU]: there `M = A_𝔮`, `K` is a normalized
dualizing complex of `A_𝔮`, and the two hypotheses are supplied by the depth of `A_𝔮` and by the
nilpotence of `f` on the dual `Ext` modules, which is
`Stacks.RingTheory.PrincipalDivisorDepth.exists_mulPowQuotSMulTop_eq_zero_of_depthDimOffDivisor`.

## Main definitions

* `Dualizing.quotPowToQuot` — the reduction `M/f^{n+1}M ⟶ M/fM`.
* `Dualizing.smulPowShortComplexMap` — the morphism of short exact sequences displayed above.
* `Dualizing.extQuotPow` — the induced map `Ext^i(M/fM, K) ⟶ Ext^i(M/f^{n+1}M, K)`.

## Main results

* `Dualizing.extQuotPow_extConnecting` — compatibility of `extQuotPow` with the connecting maps:
  it carries the connecting image of `z` to the connecting image of `f^n z`.
* `Dualizing.extQuotPow_eq_zero` — the vanishing of `extQuotPow`.
* `Dualizing.subsingleton_moduleExtInto_self_of_lt_depth` — `H^{-i}(ω) = 0` below the depth.
* `Dualizing.extQuotPow_eq_zero_of_le_depth_of_pow_smul_eq_zero` — the two cases of
  [Stacks, Tag 0DXU] that need the long exact sequence, `dim(A/𝔮) = 2` and `dim(A/𝔮) = 1`,
  uniformly: the two hypotheses of `Dualizing.extQuotPow_eq_zero` are supplied from
  `k ≤ depth(B)` and the nilpotence of `f` on `H^{-k}(ω)`.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated DerivedCategory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

variable {A : Type u} [CommRing A]

/-! ### The morphism of short exact sequences -/

/-- The reduction `M ⧸ f^{n+1}M → M ⧸ fM`, induced by the identity of `M`. -/
def quotPowToQuot (f : A) (M : Type v) [AddCommGroup M] [Module A M] (n : ℕ) :
    QuotSMulTop (f ^ (n + 1)) M →ₗ[A] QuotSMulTop f M :=
  Submodule.mapQ _ _ LinearMap.id (by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (f ^ (n + 1)) ⊤).mp hx
    refine Submodule.mem_comap.mpr ((Submodule.mem_smul_pointwise_iff_exists _ f ⊤).mpr
      ⟨f ^ n • y, Submodule.mem_top, ?_⟩)
    rw [LinearMap.id_apply, smul_smul]
    congr 1
    ring)

/-- The reduction `M ⧸ f^{n+1}M → M ⧸ fM` sends the class of `x` to the class of `x`. -/
@[simp]
theorem quotPowToQuot_mk (f : A) {M : Type v} [AddCommGroup M] [Module A M] (n : ℕ) (x : M) :
    quotPowToQuot f M n (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : QuotSMulTop f M) := rfl

/-- The morphism of short exact sequences from `0 → M → M → M/f^{n+1}M → 0` to
`0 → M → M → M/fM → 0`, with multiplication by `f^n` on the left, the identity in the middle and
the reduction on the right. -/
def smulPowShortComplexMap (f : A) (M : ModuleCat.{v} A) (n : ℕ) :
    ModuleCat.smulShortComplex M (f ^ (n + 1)) ⟶ ModuleCat.smulShortComplex M f where
  τ₁ := f ^ n • 𝟙 M
  τ₂ := 𝟙 M
  τ₃ := ModuleCat.ofHom (quotPowToQuot f M n)
  comm₁₂ := by
    ext x
    change f • (f ^ n • x) = f ^ (n + 1) • x
    rw [smul_smul]
    congr 1
    ring
  comm₂₃ := by
    ext x
    rfl

/-! ### The induced map on `Ext` -/

/-- Precomposition with the reduction `M/f^{n+1}M → M/fM`: the transition map of the tower
`n ↦ Ext^i_A(M/f^{n+1}M, K)`. -/
noncomputable def extQuotPow (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (n : ℕ) (i : ℤ) :
    moduleExtInto (QuotSMulTop f M) K i →ₗ[A]
      moduleExtInto (QuotSMulTop (f ^ (n + 1)) M) K i where
  toFun x := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
    (ModuleCat.ofHom (quotPowToQuot f M n)) ≫ x
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- **Compatibility of the reduction map on `Ext` with the connecting maps.** The reduction
`Ext^{i+1}(M/fM, K) → Ext^{i+1}(M/f^{n+1}M, K)` carries the connecting image of `z` to the
connecting image of `f^n z`.

This is the third commuting square of the morphism of distinguished triangles induced by
`Dualizing.smulPowShortComplexMap`. -/
theorem extQuotPow_extConnecting (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (n : ℕ)
    (hregn : IsSMulRegular M (f ^ (n + 1))) (i : ℤ) (z : moduleExtInto M K i) :
    extQuotPow M K f n (i + 1) (extConnecting M K f hreg i z) =
      extConnecting M K (f ^ (n + 1)) hregn i (f ^ n • z) := by
  have hcomm := (ShortComplex.ShortExact.singleTriangle.map
    (hregn.smulShortComplex_shortExact (M := ModuleCat.of A M))
    (hreg.smulShortComplex_shortExact (M := ModuleCat.of A M))
    (smulPowShortComplexMap f (ModuleCat.of A M) n)).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃, smulPowShortComplexMap] at hcomm
  have hlast : (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (f ^ n • 𝟙 (ModuleCat.of A M))) ≫
      ((shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (1 : ℤ)).map z ≫
        (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A)) i 1 (i + 1) rfl).inv.app K) =
      (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (1 : ℤ)).map (f ^ n • z) ≫
        (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A)) i 1 (i + 1) rfl).inv.app K := by
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
      Category.id_comp]
  refine (Category.assoc ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
    (ModuleCat.ofHom (quotPowToQuot f M n))) _ _).symm.trans ?_
  refine (congrArg (fun u => u ≫ ((shiftFunctor (DerivedCategory (ModuleCat.{v} A))
      (1 : ℤ)).map z ≫ (shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A))
        i 1 (i + 1) rfl).inv.app K)) hcomm.symm).trans ?_
  exact (Category.assoc
    (hregn.smulShortComplex_shortExact (M := ModuleCat.of A M)).singleδ _ _).trans
      (congrArg (fun w =>
        (hregn.smulShortComplex_shortExact (M := ModuleCat.of A M)).singleδ ≫ w) hlast)

/-! ### The vanishing -/

/-- **The vanishing of the reduction map on `Ext`, the last step of the proof of
[Stacks, Tag 0DXU].** Let `f` act regularly on `M`. If `Ext^{i+1}_A(M, K)` has no `f`-torsion and
multiplication by `f^n` from `Ext^i_A(M, K)/f` to `Ext^i_A(M, K)/f^{n+1}` is zero, then the
reduction map `Ext^{i+1}_A(M/fM, K) → Ext^{i+1}_A(M/f^{n+1}M, K)` is zero.

Absence of `f`-torsion in `Ext^{i+1}_A(M, K)` makes the map `Ext^{i+1}(M/fM, K) → Ext^{i+1}(M, K)`
of the long exact sequence vanish, so every class of `Ext^{i+1}(M/fM, K)` is a connecting image;
`Dualizing.extQuotPow_extConnecting` turns the connecting image of `z` into the connecting image
of `f^n z`, which the second hypothesis places in `f^{n+1}Ext^i_A(M, K)`; and the connecting map
for `f^{n+1}` factors through `Ext^i_A(M, K)/f^{n+1}` by
`Dualizing.quotientExtEmbedding`. -/
theorem extQuotPow_eq_zero (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (n : ℕ)
    (i : ℤ)
    (htors : ∀ x : moduleExtInto M K (i + 1), f • x = 0 → x = 0)
    (hvan : ∀ z : moduleExtInto M K i,
      f ^ n • z ∈ (f ^ (n + 1)) • (⊤ : Submodule A (moduleExtInto M K i))) :
    extQuotPow M K f n (i + 1) = 0 := by
  have hregn : IsSMulRegular M (f ^ (n + 1)) := hreg.pow (n + 1)
  refine LinearMap.ext fun x => ?_
  have h1 : extFromQuotient M K f (i + 1) x = 0 :=
    htors _ ((exact_extFromQuotient_lsmul M K f hreg (i + 1)).apply_apply_eq_zero x)
  obtain ⟨z, hz⟩ := (exact_extConnecting_extFromQuotient M K f hreg i x).mp h1
  obtain ⟨ι, -, hspec⟩ := quotientExtEmbedding M K (f ^ (n + 1)) hregn i
  obtain ⟨w, -, hw⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ (f ^ (n + 1)) ⊤).mp (hvan z)
  have hzero : ((f ^ (n + 1)) • (⊤ : Submodule A (moduleExtInto M K i))).mkQ
      (f ^ (n + 1) • w) = 0 :=
    (Submodule.mkQ_apply _ _).trans ((Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top))
  rw [LinearMap.zero_apply, ← hz, extQuotPow_extConnecting M K f hreg n hregn i z, ← hw,
    ← hspec, hzero, map_zero]

/-! ### The three cases of the proof of [Stacks, Tag 0DXU] -/

section Dualizing

variable {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- **The vanishing of `Ext^{-i}_B(B, ω)` below the depth.**  For a Noetherian local ring `B`
with normalized dualizing complex `ω`, the module `Ext^{-i}_B(B, ω) = H^{-i}(ω)` vanishes for
every `i` strictly below `depth(B)`.

This is [Stacks, Tag 0DWZ] part (3), which says that the depth is the least `i` with
`Ext^{-i}_B(B, ω) ≠ 0`.  It is the step by which the proof of [Stacks, Tag 0DXU] kills
`H^0(ω^•_{A_𝔮})` from `depth(A_𝔮) ≥ 1`, and `H^0(ω^•_{A_𝔮})` together with
`H^{-1}(ω^•_{A_𝔮})` from `depth(A_𝔮) ≥ 2`. -/
theorem subsingleton_moduleExtInto_self_of_lt_depth
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (i : ℕ) (hi : (i : ℕ∞) < Module.depth B (IsLocalRing.maximalIdeal B) B) :
    Subsingleton (moduleExtInto B K (-(i : ℤ))) := by
  by_contra hcon
  have hnt : Nontrivial (moduleExtInto B K (-(i : ℤ))) :=
    not_subsingleton_iff_nontrivial.mp hcon
  refine absurd hi (not_lt.mpr ?_)
  rw [depth_eq_iInf_nontrivial_moduleExtInto (A := B) (M := B) K hK]
  exact (iInf_le _ i).trans (iInf_le (fun _ : Nontrivial
    (moduleExtInto B K (-(i : ℤ))) => (i : ℕ∞)) hnt)

/-- **The last step of the proof of [Stacks, Tag 0DXU], in the two cases that need the long exact
sequence.**  Let `B` be a Noetherian local ring with normalized dualizing complex `ω`, let
`f ∈ B` act regularly on `B`, let `1 ≤ k ≤ depth(B)`, and let `f^c` annihilate
`Ext^{-k}_B(B, ω) = H^{-k}(ω)`.  Then for every `n ≥ c` the reduction map

  `Ext^{-k+1}_B(B/fB, ω) ⟶ Ext^{-k+1}_B(B/f^{n+1}B, ω)`

is zero.

In the proof of [Stacks, Tag 0DXU] this is applied over `B = A_𝔮` for a prime `𝔮 ∈ V(f)` other
than `𝔪`, with `ω` a normalized dualizing complex of `A_𝔮`, at the degree `-2 + dim(A/𝔮)`:

* `dim(A/𝔮) = 2`, so `k = 1`.  The depth bound is
  `Stacks.RingTheory.PrincipalDivisorDepth.one_le_depth_localization`, `f` being a
  nonzerodivisor, and `H^{-1}(ω)` is where hypothesis (6) makes `f` nilpotent.
* `dim(A/𝔮) = 1`, so `k = 2`.  The depth bound is
  `Stacks.RingTheory.PrincipalDivisorDepth.two_le_depth_localization_of_depthDimOnDivisor`, from
  hypothesis (5), and `H^{-2}(ω)` is where hypothesis (6) makes `f` nilpotent.

The remaining case `dim(A/𝔮) ≥ 3` needs no long exact sequence: the degree is then positive and
`Dualizing.subsingleton_moduleExtInto_of_pos` of `ExtVanishingRange.lean` kills the target
outright.

Both hypotheses of `Dualizing.extQuotPow_eq_zero` are supplied here.  Absence of `f`-torsion in
`Ext^{-k+1}_B(B, ω)` is the vanishing of that module, which holds because `k - 1 < depth(B)`
(`Dualizing.subsingleton_moduleExtInto_self_of_lt_depth`); and `f^n` carries
`Ext^{-k}_B(B, ω)` into `f^{n+1}Ext^{-k}_B(B, ω)` because it kills it outright, `n` being at
least `c`. -/
theorem extQuotPow_eq_zero_of_le_depth_of_pow_smul_eq_zero
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (f : B) (hreg : IsSMulRegular B f) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k : ℕ∞) ≤ Module.depth B (IsLocalRing.maximalIdeal B) B) (c : ℕ)
    (hc : ∀ x : moduleExtInto B K (-(k : ℤ)), f ^ c • x = 0) (n : ℕ) (hn : c ≤ n) :
    extQuotPow B K f n (-(k : ℤ) + 1) = 0 := by
  refine extQuotPow_eq_zero B K f hreg n (-(k : ℤ)) (fun x _ => ?_) (fun z => ?_)
  · have : Subsingleton (moduleExtInto B K (-(k : ℤ) + 1)) := by
      have hlt : ((k - 1 : ℕ) : ℕ∞) < Module.depth B (IsLocalRing.maximalIdeal B) B :=
        lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt (by omega) Nat.one_pos) hk
      have heq : -((k - 1 : ℕ) : ℤ) = -(k : ℤ) + 1 := by
        have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
        omega
      exact heq ▸ subsingleton_moduleExtInto_self_of_lt_depth K hK (k - 1) hlt
    exact Subsingleton.elim x 0
  · have hz : f ^ n • z = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, mul_comm (f ^ c) (f ^ d), mul_smul, hc, smul_zero]
    rw [hz]
    exact Submodule.zero_mem _

end Dualizing

end Dualizing

end
