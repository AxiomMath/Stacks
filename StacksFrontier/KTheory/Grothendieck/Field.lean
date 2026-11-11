module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.KTheory.Grothendieck.PID
import StacksCore.Tactic.EgaSgaAttribute
@[expose] public section


open CategoryTheory

universe u

/-- Over a field `k`, the (finite) dimension function is additive on short
exact sequences of `k`-vector spaces in `ModuleCat.{u} k`: if
`0 → X₁ → X₂ → X₃ → 0` is short exact and `X₂` is finite-dimensional, then
`finrank k X₂ = finrank k X₁ + finrank k X₃`.

This additivity is what makes `finrank` descend to a homomorphism from the
Grothendieck group of finite `k`-modules to `ℤ`; the full statement of Stacks
Example 00JE (`K₀(k) = K'₀(k) ≅ ℤ` via dimension, which equals length) is
`K0toK0'_field_bijective_and_isoZ`. -/
@[sga "6 I 6.0" "(ii), special case"]
theorem finrank_additive_of_shortExact {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{u} k))
    (hfin : Module.Finite k S.X₂)
    (hS : S.ShortExact) :
    Module.finrank k S.X₂ = Module.finrank k S.X₁ + Module.finrank k S.X₃ := by
  have hf_inj : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hg_surj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hker_eq : LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
    hS.exact.moduleCat_range_eq_ker
  have h_rn : Module.finrank k (LinearMap.range S.g.hom)
      + Module.finrank k (LinearMap.ker S.g.hom) = Module.finrank k S.X₂ :=
    LinearMap.finrank_range_add_finrank_ker (S.g.hom)
  have h_range_g : Module.finrank k (LinearMap.range S.g.hom) =
      Module.finrank k S.X₃ := by
    rw [LinearMap.range_eq_top.mpr hg_surj, finrank_top]
  have h_ker : Module.finrank k (LinearMap.ker S.g.hom) =
      Module.finrank k (LinearMap.range S.f.hom) := by
    rw [hker_eq]
  have h_range_f : Module.finrank k (LinearMap.range S.f.hom) =
      Module.finrank k S.X₁ :=
    LinearMap.finrank_range_of_inj hf_inj
  linarith [h_rn, h_range_g, h_ker, h_range_f]

/-- **Stacks Example 00JE.** Let `k` be a field. Then `K₀(k) = K'₀(k) ≅ ℤ`, the
isomorphism being given by the dimension function, which is also the length function.
Precisely:
* the canonical map `K0toK0' k : K₀(k) → K'₀(k)` is bijective;
* there is an isomorphism `K'₀(k) ≃+ ℤ` sending the class `[M]` of every finite
  `k`-module `M` to `dim_k M`;
* there is an isomorphism `K₀(k) ≃+ ℤ` sending the class `[M]` of every finite
  (projective) `k`-module `M` to `dim_k M`;
* for every finite `k`-module `M`, `length_k M = dim_k M`.

Here `K'₀(k) = K0PrimeOfFinPres k` and `K₀(k) = K0OfProjGen k` are the Grothendieck
groups of finite, resp. finite projective, `k`-modules modulo short exact sequences,
built as in Stacks Section 00JC. -/
@[stacks 00JE "K0(k) → K'0(k) bijective, K'0(k) ≅ ℤ and K0(k) ≅ ℤ via dimension, \
dimension equals length"]
theorem K0toK0'_field_bijective_and_isoZ (k : Type u) [Field k] :
    Function.Bijective (K0toK0' k) ∧
    (∃ e : K0PrimeOfFinPres k ≃+ ℤ, ∀ (M : Type u) [AddCommGroup M] [Module k M]
        [Module.Finite k M], e (K0PrimeOfFinPres.mkM k M) = Module.finrank k M) ∧
    (∃ e : K0OfProjGen k ≃+ ℤ, ∀ (M : Type u) [AddCommGroup M] [Module k M]
        [Module.Finite k M], e (K0OfProjGen.mkM k M) = Module.finrank k M) ∧
    ∀ (M : Type u) [AddCommGroup M] [Module k M] [Module.Finite k M],
      Module.length k M = Module.finrank k M := by
  refine ⟨⟨fun _ _ h => (rankHomK0_bijective k).injective (congrArg (rankHom k) h),
    fun w => ?_⟩, ⟨K0PrimeOfFinPres.rankEquiv, fun M _ _ _ => ?_⟩,
    ⟨K0OfProjGen.rankEquiv k, fun M _ _ _ => ?_⟩,
    fun M _ _ _ => Module.length_eq_finrank k M⟩
  · obtain ⟨y, hy⟩ := (rankHomK0_bijective k).surjective (rankHom k w)
    exact ⟨y, (rankHom_bijective (R := k)).injective hy⟩
  · obtain ⟨p, ⟨ep⟩⟩ := exists_generator_iso (R := k) M
    rw [K0PrimeOfFinPres.mkM_eq_mk_of_iso M ep, K0PrimeOfFinPres.rankEquiv,
      AddEquiv.ofBijective_apply, rankHom_mk, K0'Gen.rankZ, ← ep.finrank_eq]
    rfl
  · obtain ⟨p, ⟨ep⟩⟩ := K0OfProjGen.exists_gen_of_iso (R := k) M
    rw [K0OfProjGen.mkM_eq_mk_of_iso M ep, K0OfProjGen.rankEquiv,
      AddEquiv.ofBijective_apply, rankHomK0, AddMonoidHom.comp_apply]
    change rankHom k (K0PrimeOfFinPres.mk k p.1) = _
    rw [rankHom_mk, K0'Gen.rankZ, ← ep.finrank_eq]
    rfl
