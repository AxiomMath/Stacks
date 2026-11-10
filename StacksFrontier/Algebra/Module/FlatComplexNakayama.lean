module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Nakayama step for the cohomology of a base change of a flat complex

Let `A` be a commutative ring and `E₀ ⟶ E₁ ⟶ E₂` a complex of `A`-modules with `E₂` flat. For an
`A`-algebra `S` write `H(S)` for the cohomology in the middle of `S ⊗_A E₀ ⟶ S ⊗_A E₁ ⟶ S ⊗_A E₂`.
If `S` is local, `t ∈ 𝔪_S` is a nonzerodivisor of `S`, `H(S)` is a finite `S`-module and
`H(S/tS) = 0`, then `H(S) = 0`.

The mapping cone of a map from `C₀ ⟶ C₁ ⟶ C₂` to a two-term complex `D₀ ⟶ D₁` has vanishing
middle cohomology after base change to `S` exactly when the map is onto on `H⁰` and one-to-one on
`H¹` in the sense relevant for a two-term target.

## Main definitions

* `Stacks.FlatComplexNakayama.homology`: the middle cohomology of the base change to `S`.
* `Stacks.FlatComplexNakayama.IsExactAt`: its vanishing, as "every cycle is a boundary".
* `Stacks.FlatComplexNakayama.coneD₀`, `coneD₁`: the mapping cone of a map to a two-term complex.
* `Stacks.FlatComplexNakayama.SurjZero`, `InjOne`: surjectivity on `H⁰` and injectivity on `H¹`
  after base change.

## Main results

* `Stacks.FlatComplexNakayama.isExactAt_of_quotient`: the Nakayama step.
* `Stacks.FlatComplexNakayama.ker_eq_bot_of_quotient`: the same step for the kernel of a single
  map, i.e. for `H⁰`.
* `Stacks.FlatComplexNakayama.isExactAt_cone_iff`: the cone criterion.
* `Stacks.FlatComplexNakayama.finite_homology_cone`: finiteness of the cohomology of the cone.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Stacks.FlatComplexNakayama

variable {A : Type u} [CommRing A]

section Homology

variable {E₀ E₁ E₂ : Type v} [AddCommGroup E₀] [AddCommGroup E₁] [AddCommGroup E₂]
  [Module A E₀] [Module A E₁] [Module A E₂] (d₀ : E₀ →ₗ[A] E₁) (d₁ : E₁ →ₗ[A] E₂)
  (S : Type w) [CommRing S] [Algebra A S]

/-- The cycles in the middle of the base change of `E₀ ⟶ E₁ ⟶ E₂` to `S`. -/
abbrev cycles : Submodule S (S ⊗[A] E₁) := LinearMap.ker (d₁.baseChange S)

/-- The boundaries in the middle of the base change of `E₀ ⟶ E₁ ⟶ E₂` to `S`, as a submodule of
the cycles. -/
abbrev boundaries : Submodule S (cycles d₁ S) :=
  (LinearMap.range (d₀.baseChange S)).comap (cycles d₁ S).subtype

/-- The cohomology in the middle of the base change of `E₀ ⟶ E₁ ⟶ E₂` to `S`. -/
abbrev homology : Type _ := cycles d₁ S ⧸ boundaries d₀ d₁ S

/-- Exactness in the middle of the base change to `S`: every cycle is a boundary. -/
def IsExactAt : Prop :=
  ∀ x : S ⊗[A] E₁, d₁.baseChange S x = 0 → ∃ y, d₀.baseChange S y = x

/-- The middle cohomology of the base change to `S` vanishes if and only if the base change is
exact in the middle. -/
theorem subsingleton_homology_iff : Subsingleton (homology d₀ d₁ S) ↔ IsExactAt d₀ d₁ S := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  exact ⟨fun h x hx => h (Submodule.mem_top (x := (⟨x, hx⟩ : cycles d₁ S))),
    fun h ⟨x, hx⟩ _ => h x hx⟩

variable {S}

/-- Base change of a linear map commutes with reduction along an algebra map. -/
theorem rTensor_baseChange_apply {E F : Type v} [AddCommGroup E] [AddCommGroup F] [Module A E]
    [Module A F] (f : E →ₗ[A] F) {S' : Type w} [CommRing S'] [Algebra A S'] (π : S →ₐ[A] S')
    (x : S ⊗[A] E) :
    π.toLinearMap.rTensor F (f.baseChange S x) = f.baseChange S' (π.toLinearMap.rTensor E x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s e => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Multiplication by `t` on the left factor of `S ⊗ E` is the scalar action of `t`. -/
theorem rTensor_mulLeft_apply {E : Type v} [AddCommGroup E] [Module A E] (t : S)
    (x : S ⊗[A] E) : (LinearMap.mulLeft A t).rTensor E x = t • x := by
  induction x using TensorProduct.inductionOn with
  | tmul s e => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- `S ⟶ S ⟶ S/tS`, multiplication by `t` followed by the quotient map, is exact. -/
theorem exact_mulLeft_mk (t : S) :
    Function.Exact (LinearMap.mulLeft A t)
      (Ideal.Quotient.mkₐ A (Ideal.span {t})).toLinearMap := by
  intro x
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton', Set.mem_range, LinearMap.mulLeft_apply]
  exact exists_congr fun a => by rw [mul_comm]

/-- Base change of a composite which is zero is zero. -/
theorem baseChange_baseChange_eq_zero (hd : d₁ ∘ₗ d₀ = 0) (y : S ⊗[A] E₀) :
    d₁.baseChange S (d₀.baseChange S y) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hd, LinearMap.baseChange_zero,
    LinearMap.zero_apply]

/-- Nakayama's lemma: a finite module over a local ring in which every element is divisible by
some `t ∈ 𝔪` is zero. -/
private theorem subsingleton_of_forall_eq_smul {M : Type*} [AddCommGroup M] [Module S M]
    [IsLocalRing S] [Module.Finite S M] {t : S} (ht : t ∈ IsLocalRing.maximalIdeal S)
    (h : ∀ m : M, ∃ m', m = t • m') : Subsingleton M := by
  have htop : (⊤ : Submodule S M) ≤ IsLocalRing.maximalIdeal S • (⊤ : Submodule S M) := by
    intro q _
    obtain ⟨q', rfl⟩ := h q
    exact Submodule.smul_mem_smul ht Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) ⊤
    (Module.finite_def.mp ‹_›) htop (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact subsingleton_of_forall_eq 0 fun q => (Submodule.mem_bot S).mp (hbot.le Submodule.mem_top)

/-- If `x ∈ S ⊗ E` is killed by `f` and by reduction mod `t`, with `f : E ⟶ F` and `F` flat, then
`x = t • z` for some `z` killed by `f`. -/
private theorem exists_eq_smul_of_rTensor_mk_eq_zero {E F : Type v} [AddCommGroup E]
    [AddCommGroup F] [Module A E] [Module A F] [Module.Flat A F] (f : E →ₗ[A] F) {t : S}
    (hreg : IsSMulRegular S t) {x : S ⊗[A] E} (hx : f.baseChange S x = 0)
    (hπ : (Ideal.Quotient.mkₐ A (Ideal.span {t})).toLinearMap.rTensor E x = 0) :
    ∃ z, f.baseChange S z = 0 ∧ x = t • z := by
  obtain ⟨z, hz⟩ := (rTensor_exact E (exact_mulLeft_mk (A := A) t)
    (Ideal.Quotient.mkₐ_surjective A _) _).mp hπ
  rw [rTensor_mulLeft_apply] at hz
  refine ⟨z, ?_, hz.symm⟩
  apply Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.mulLeft A t)
    (fun a b hab => hreg hab)
  rw [map_zero, rTensor_mulLeft_apply, ← map_smul, hz, hx]

/-- **The Nakayama step.** Let `S` be a local `A`-algebra, `t ∈ 𝔪_S` a nonzerodivisor of `S` and
`E₀ ⟶ E₁ ⟶ E₂` a complex of `A`-modules with `E₂` flat. If the middle cohomology of the base
change to `S` is a finite `S`-module and the base change to `S/tS` is exact in the middle, then so
is the base change to `S`. -/
theorem isExactAt_of_quotient [IsLocalRing S] [Module.Flat A E₂] (hd : d₁ ∘ₗ d₀ = 0) (t : S)
    (ht : t ∈ IsLocalRing.maximalIdeal S) (hreg : IsSMulRegular S t)
    (hfin : Module.Finite S (homology d₀ d₁ S))
    (h : IsExactAt d₀ d₁ (S ⧸ Ideal.span {t})) : IsExactAt d₀ d₁ S := by
  rw [← subsingleton_homology_iff]
  set π := Ideal.Quotient.mkₐ A (Ideal.span {t})
  have hπ : Function.Surjective π.toLinearMap := Ideal.Quotient.mkₐ_surjective A _
  have hdiv : ∀ q : homology d₀ d₁ S, ∃ q', q = t • q' := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx' : d₁.baseChange _ (π.toLinearMap.rTensor E₁ x) = 0 := by
      rw [← rTensor_baseChange_apply, LinearMap.mem_ker.mp hx, map_zero]
    obtain ⟨ybar, hybar⟩ := h _ hx'
    obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective E₀ hπ ybar
    obtain ⟨z, hzc, hz⟩ := exists_eq_smul_of_rTensor_mk_eq_zero d₁ hreg
      (x := x - d₀.baseChange S y)
      (by rw [map_sub, baseChange_baseChange_eq_zero d₀ d₁ hd, LinearMap.mem_ker.mp hx, sub_zero])
      (by rw [map_sub, rTensor_baseChange_apply, hybar, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨z, hzc⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨y, ?_⟩
    change d₀.baseChange S y = x - t • z
    rw [← hz, sub_sub_cancel]
  exact subsingleton_of_forall_eq_smul ht hdiv

/-- **The Nakayama step for the kernel of a single map.** With `S` and `t` as in
`Stacks.FlatComplexNakayama.isExactAt_of_quotient` and `E₁` flat: if the kernel of the base
change to `S` of `d : E₀ ⟶ E₁` is a finite `S`-module and the base change to `S/tS` is injective,
then so is the base change to `S`. -/
@[sga "3 VIIA 7.4.3" "special case"]
theorem ker_eq_bot_of_quotient [IsLocalRing S] [Module.Flat A E₁] (t : S)
    (ht : t ∈ IsLocalRing.maximalIdeal S) (hreg : IsSMulRegular S t)
    (hfin : Module.Finite S (LinearMap.ker (d₀.baseChange S)))
    (h : LinearMap.ker (d₀.baseChange (S ⧸ Ideal.span {t})) = ⊥) :
    LinearMap.ker (d₀.baseChange S) = ⊥ := by
  set π := Ideal.Quotient.mkₐ A (Ideal.span {t})
  set K := LinearMap.ker (d₀.baseChange S)
  have hdiv : ∀ k : K, ∃ k', k = t • k' := by
    rintro ⟨x, hx⟩
    have hx' : d₀.baseChange _ (π.toLinearMap.rTensor E₀ x) = 0 := by
      rw [← rTensor_baseChange_apply, LinearMap.mem_ker.mp hx, map_zero]
    obtain ⟨z, hzk, hz⟩ := exists_eq_smul_of_rTensor_mk_eq_zero d₀ hreg
      (LinearMap.mem_ker.mp hx) (LinearMap.ker_eq_bot'.mp h _ hx')
    exact ⟨⟨z, hzk⟩, Subtype.ext hz⟩
  have := subsingleton_of_forall_eq_smul ht hdiv
  exact Submodule.eq_bot_of_subsingleton

end Homology

section Cone

variable {C₀ C₁ C₂ D₀ D₁ : Type v} [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [Module A C₀] [Module A C₁] [Module A C₂] [Module A D₀]
  [Module A D₁] (d₀ : C₀ →ₗ[A] C₁) (d₁ : C₁ →ₗ[A] C₂) (δ₀ : D₀ →ₗ[A] D₁) (φ₀ : C₀ →ₗ[A] D₀)
  (φ₁ : C₁ →ₗ[A] D₁)

/-- The first differential of the mapping cone of `(φ₀, φ₁)` from `C₀ ⟶ C₁ ⟶ C₂` to `D₀ ⟶ D₁`. -/
def coneD₀ : C₀ →ₗ[A] C₁ × D₀ := d₀.prod φ₀

/-- The second differential of the mapping cone of `(φ₀, φ₁)`. -/
def coneD₁ : C₁ × D₀ →ₗ[A] C₂ × D₁ :=
  (d₁ ∘ₗ LinearMap.fst A C₁ D₀).prod (φ₁ ∘ₗ LinearMap.fst A C₁ D₀ - δ₀ ∘ₗ LinearMap.snd A C₁ D₀)

/-- The mapping cone is a complex: `coneD₁ ∘ coneD₀ = 0` when `d₁ ∘ d₀ = 0` and
`φ₁ ∘ d₀ = δ₀ ∘ φ₀`. -/
theorem coneD₁_comp_coneD₀ (hd : d₁ ∘ₗ d₀ = 0) (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀) :
    coneD₁ d₁ δ₀ φ₁ ∘ₗ coneD₀ d₀ φ₀ = 0 := by
  ext c
  · simpa [coneD₀, coneD₁] using LinearMap.congr_fun hd c
  · simpa [coneD₀, coneD₁, sub_eq_zero] using LinearMap.congr_fun hφ c

variable (S : Type w) [CommRing S] [Algebra A S]

/-- Surjectivity on `H⁰` after base change to `S`: every element of the kernel of `δ₀ ⊗ S` comes
from an element of the kernel of `d₀ ⊗ S`. -/
def SurjZero : Prop :=
  ∀ y : S ⊗[A] D₀, δ₀.baseChange S y = 0 →
    ∃ c : S ⊗[A] C₀, d₀.baseChange S c = 0 ∧ φ₀.baseChange S c = y

/-- Injectivity on `H¹` after base change to `S`, relative to the two-term target: a cycle of
`C ⊗ S` whose image in `D₁ ⊗ S` is a coboundary of `D ⊗ S` is a coboundary of `C ⊗ S`. -/
def InjOne : Prop :=
  ∀ x : S ⊗[A] C₁, d₁.baseChange S x = 0 → (∃ y, φ₁.baseChange S x = δ₀.baseChange S y) →
    ∃ c, d₀.baseChange S c = x

/-- Under `S ⊗ (C₁ × D₀) ≃ (S ⊗ C₁) × (S ⊗ D₀)`, the base change of `coneD₀` sends `c` to
`(d₀ c, φ₀ c)`. -/
theorem prodRight_coneD₀ (c : S ⊗[A] C₀) :
    TensorProduct.prodRight A S S C₁ D₀ ((coneD₀ d₀ φ₀).baseChange S c) =
      (d₀.baseChange S c, φ₀.baseChange S c) := by
  induction c using TensorProduct.inductionOn with
  | tmul s x => simp [coneD₀]
  | add x y hx hy => simp only [map_add, hx, hy, Prod.mk_add_mk]

/-- Under `S ⊗ (C₂ × D₁) ≃ (S ⊗ C₂) × (S ⊗ D₁)`, the base change of `coneD₁` sends `(x, y)` to
`(d₁ x, φ₁ x - δ₀ y)`. -/
theorem prodRight_coneD₁ (w : S ⊗[A] (C₁ × D₀)) :
    TensorProduct.prodRight A S S C₂ D₁ ((coneD₁ d₁ δ₀ φ₁).baseChange S w) =
      (d₁.baseChange S (TensorProduct.prodRight A S S C₁ D₀ w).1,
        φ₁.baseChange S (TensorProduct.prodRight A S S C₁ D₀ w).1 -
          δ₀.baseChange S (TensorProduct.prodRight A S S C₁ D₀ w).2) := by
  induction w using TensorProduct.inductionOn with
  | tmul s x => simp [coneD₁, TensorProduct.tmul_sub]
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    congr 1
    abel

/-- If the base change to `S` of the mapping cone is exact in the middle, every pair `(x, y)` with
`d₁ x = 0` and `φ₁ x = δ₀ y` is `(d₀ c, φ₀ c)` for some `c`. -/
private theorem exists_of_isExactAt_cone (h : IsExactAt (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S)
    (x : S ⊗[A] C₁) (y : S ⊗[A] D₀) (hx : d₁.baseChange S x = 0)
    (hxy : φ₁.baseChange S x = δ₀.baseChange S y) :
    ∃ c, d₀.baseChange S c = x ∧ φ₀.baseChange S c = y := by
  set e₁ := TensorProduct.prodRight A S S C₁ D₀
  obtain ⟨c, hc⟩ := h (e₁.symm (x, y)) (by
    apply (TensorProduct.prodRight A S S C₂ D₁).injective
    rw [prodRight_coneD₁]
    simp [e₁, hx, hxy])
  have := congrArg e₁ hc
  rw [prodRight_coneD₀, LinearEquiv.apply_symm_apply, Prod.mk.injEq] at this
  exact ⟨c, this⟩

/-- If the base change to `S` of the mapping cone is exact in the middle, the map is onto on
`H⁰`. -/
private theorem surjZero_of_isExactAt_cone (h : IsExactAt (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S) :
    SurjZero d₀ δ₀ φ₀ S := fun y hy => by
  obtain ⟨c, hc⟩ := exists_of_isExactAt_cone d₀ d₁ δ₀ φ₀ φ₁ S h 0 y (map_zero _)
    (by rw [map_zero, hy])
  exact ⟨c, hc⟩

/-- If the base change to `S` of the mapping cone is exact in the middle, the map is one-to-one
on `H¹`. -/
private theorem injOne_of_isExactAt_cone (h : IsExactAt (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S) :
    InjOne d₀ d₁ δ₀ φ₁ S := fun x hx ⟨y, hxy⟩ =>
  (exists_of_isExactAt_cone d₀ d₁ δ₀ φ₀ φ₁ S h x y hx hxy).imp fun _ hc => hc.1

/-- If `(x, y)` is a cycle of the base change of the cone and `d₀ c = x`, then `y - φ₀ c` lies in
the kernel of `δ₀ ⊗ S`. -/
private theorem baseChange_snd_sub_eq_zero (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀) {w : S ⊗[A] (C₁ × D₀)}
    (hw : (coneD₁ d₁ δ₀ φ₁).baseChange S w = 0) {c : S ⊗[A] C₀}
    (hc : d₀.baseChange S c = (TensorProduct.prodRight A S S C₁ D₀ w).1) :
    δ₀.baseChange S ((TensorProduct.prodRight A S S C₁ D₀ w).2 - φ₀.baseChange S c) = 0 := by
  have hw' := congrArg (TensorProduct.prodRight A S S C₂ D₁) hw
  rw [prodRight_coneD₁, map_zero, Prod.mk_eq_zero, sub_eq_zero] at hw'
  have hcomm : δ₀.baseChange S (φ₀.baseChange S c) = φ₁.baseChange S (d₀.baseChange S c) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, hφ]
  rw [map_sub, ← hw'.2, hcomm, hc, sub_self]

/-- If the map is onto on `H⁰` and one-to-one on `H¹` after base change to `S`, the base change
of the mapping cone is exact in the middle. -/
private theorem isExactAt_cone_of_surjZero_of_injOne (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hs : SurjZero d₀ δ₀ φ₀ S) (hi : InjOne d₀ d₁ δ₀ φ₁ S) :
    IsExactAt (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S := by
  set e₁ := TensorProduct.prodRight A S S C₁ D₀
  intro w hw
  have hw' := congrArg (TensorProduct.prodRight A S S C₂ D₁) hw
  rw [prodRight_coneD₁, map_zero, Prod.mk_eq_zero, sub_eq_zero] at hw'
  obtain ⟨c, hc⟩ := hi (e₁ w).1 hw'.1 ⟨(e₁ w).2, hw'.2⟩
  obtain ⟨c', hc'0, hc'⟩ := hs _ (baseChange_snd_sub_eq_zero d₀ d₁ δ₀ φ₀ φ₁ S hφ hw hc)
  refine ⟨c + c', e₁.injective ?_⟩
  rw [prodRight_coneD₀, map_add, map_add, hc, hc'0, add_zero, hc', add_sub_cancel]

/-- **The cone criterion.** The base change to `S` of the mapping cone is exact in the middle if
and only if the map is onto on `H⁰` and one-to-one on `H¹`. -/
theorem isExactAt_cone_iff (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀) :
    IsExactAt (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S ↔
      SurjZero d₀ δ₀ φ₀ S ∧ InjOne d₀ d₁ δ₀ φ₁ S :=
  ⟨fun h => ⟨surjZero_of_isExactAt_cone d₀ d₁ δ₀ φ₀ φ₁ S h,
      injOne_of_isExactAt_cone d₀ d₁ δ₀ φ₀ φ₁ S h⟩,
    fun ⟨hs, hi⟩ => isExactAt_cone_of_surjZero_of_injOne d₀ d₁ δ₀ φ₀ φ₁ S hφ hs hi⟩

/-- The map from the middle cohomology of the cone to the middle cohomology of the source,
`[(x, y)] ↦ [x]`. -/
def homologyConeToHomology :
    homology (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S →ₗ[S] homology d₀ d₁ S :=
  Submodule.mapQ _ _
    (LinearMap.codRestrict (cycles d₁ S)
      (LinearMap.fst S (S ⊗[A] C₁) (S ⊗[A] D₀) ∘ₗ
        (TensorProduct.prodRight A S S C₁ D₀).toLinearMap ∘ₗ
          (cycles (coneD₁ d₁ δ₀ φ₁) S).subtype)
      (fun w => by
        have h := congrArg Prod.fst (congrArg (TensorProduct.prodRight A S S C₂ D₁)
          (LinearMap.mem_ker.mp w.2))
        rwa [prodRight_coneD₁, map_zero] at h))
    (by
      rintro ⟨w, hw⟩ ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hc' : (coneD₀ d₀ φ₀).baseChange S c = w := hc
      change d₀.baseChange S c = (TensorProduct.prodRight A S S C₁ D₀ w).1
      rw [← hc', prodRight_coneD₀])

/-- **Finiteness of the cohomology of the cone.** Over a Noetherian `S`, if the kernel of
`δ₀ ⊗ S` and the middle cohomology of `C ⊗ S` are finite, so is the middle cohomology of the
cone. -/
theorem finite_homology_cone [IsNoetherianRing S] (hφ : φ₁ ∘ₗ d₀ = δ₀ ∘ₗ φ₀)
    (hD : Module.Finite S (LinearMap.ker (δ₀.baseChange S)))
    (hC : Module.Finite S (homology d₀ d₁ S)) :
    Module.Finite S (homology (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S) := by
  set e₁ := TensorProduct.prodRight A S S C₁ D₀
  set e₂ := TensorProduct.prodRight A S S C₂ D₁
  set Ψ := homologyConeToHomology d₀ d₁ δ₀ φ₀ φ₁ S
  let Φ : LinearMap.ker (δ₀.baseChange S) →ₗ[S] homology (coneD₀ d₀ φ₀) (coneD₁ d₁ δ₀ φ₁) S :=
    (Submodule.mkQ _).comp
      (LinearMap.codRestrict (cycles (coneD₁ d₁ δ₀ φ₁) S)
        (e₁.symm.toLinearMap ∘ₗ LinearMap.inr S (S ⊗[A] C₁) (S ⊗[A] D₀) ∘ₗ
          (LinearMap.ker (δ₀.baseChange S)).subtype)
        (fun y => by
          rw [LinearMap.mem_ker]
          apply e₂.injective
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
            LinearMap.inr_apply, Submodule.coe_subtype]
          rw [prodRight_coneD₁]
          simp [e₁, LinearMap.mem_ker.mp y.2]))
  have hker : LinearMap.ker Ψ ≤ LinearMap.range Φ := by
    intro q hq
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨c, hc⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    have hc' : d₀.baseChange S c = (e₁ w).1 := hc
    have hy : (e₁ w).2 - φ₀.baseChange S c ∈ LinearMap.ker (δ₀.baseChange S) :=
      baseChange_snd_sub_eq_zero d₀ d₁ δ₀ φ₀ φ₁ S hφ hw hc'
    refine ⟨⟨_, hy⟩, ?_⟩
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨-c, e₁.injective ?_⟩
    rw [prodRight_coneD₀]
    simp only [map_neg, Submodule.subtype_apply, LinearMap.codRestrict_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearMap.inr_apply, map_sub,
      LinearEquiv.apply_symm_apply, hc']
    ext <;> simp
  have hfgker : (⊤ ⊓ LinearMap.ker Ψ).FG :=
    Submodule.FG.of_le (Submodule.FG.map Φ (Module.finite_def.mp hD))
      (by rwa [top_inf_eq, ← LinearMap.range_eq_map])
  have hfgmap : (Submodule.map Ψ ⊤).FG := IsNoetherian.noetherian _
  exact ⟨Submodule.fg_of_fg_map_of_fg_inf_ker Ψ hfgmap hfgker⟩

end Cone

end Stacks.FlatComplexNakayama

end
