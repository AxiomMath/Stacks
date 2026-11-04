module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.CokernelMultiplicity
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareVanishing
public import StacksFrontier.RingTheory.Koszul.TorResidueField
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksFrontier.RingTheory.Length.IndexAdditivity
public import StacksFrontier.RingTheory.FiniteLength
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived exterior square of the residue field of a regular local ring

Let `(R, 𝔪, κ)` be a regular local ring of Krull dimension `c`. The derived exterior squares
`LᵢΛ²_R(κ)` of Dold and Puppe (`Stacks.DerivedSquare.homology`) have finite length
(`Stacks.DerivedSquare.isFiniteLength_homology`) and vanish for `i > 2c`
(`Stacks.DerivedSquare.isZero_homology_of_isRegularLocalRing`). This file computes their Euler
characteristic

  `a_c = ∑_{i ≤ 2c} (-1)ⁱ length_R LᵢΛ²_R(κ) = -2^(c-1)` if `c ≥ 1`, and `a_0 = 0`.

**The recursion.** For `c = 0` the ring is a field, `L₀Λ²(κ) = ⋀²κ = 0` since `κ` is cyclic, and
there is nothing else to sum. For `c ≥ 1` write `𝔪 = (y₁, …, y_{c-1}, f)` with a regular system of
parameters, put `N = R ⧸ (y₁, …, y_{c-1})`, so that `f` is `N`-regular, `N ⧸ fN ≅ κ`, and `R ⧸ (f)`
is regular local of dimension `c - 1`. For an endomorphism `g` of a module with kernel and cokernel
of finite length write `ind g = length (coker g) - length (ker g)`; it is additive under
composition (`Module.lengthIndex_comp`), so `ind (f²) = 2 ind f` on each `LᵢΛ²(N)`.

* The reduction long exact sequence
  `⋯ → LᵢΛ²_R(N) →(f) LᵢΛ²_R(N) → LᵢΛ²_{R ⧸ (f)}(N ⧸ fN) → Lᵢ₋₁Λ²_R(N) → ⋯` gives
  `∑ (-1)ⁱ ind (f on LᵢΛ²(N)) = ∑ (-1)ⁱ length LᵢΛ²_{R ⧸ (f)}(κ) = a_{c-1}`.
* The cross-effect sequences of a simplicial horseshoe over `0 → N →(f) N → κ → 0` give, with
  `Q = Λ²P₂ ⧸ Λ²P₁`, `∑ (-1)ⁱ length Hᵢ(Q) = ∑ (-1)ⁱ ind (f² on LᵢΛ²(N))` and
  `∑ (-1)ⁱ length Hᵢ(Q) = ∑ (-1)ⁱ length Torᵢ(N, κ) + a_c`.
* `length Torᵢ(N, κ) = (c - 1 choose i)`, so `∑ (-1)ⁱ length Torᵢ(N, κ) = (1 - 1)^(c-1)`.

Hence `a_c = 2 a_{c-1} - [c = 1]`, which gives the formula. Combined with
`∑ (-1)ⁱ length Torᵢ(κ, κ) = [c = 0]` this says that `[κ]·[κ] - 2 a_c = 2^c`, which is the value
`ψ²[κ] = 2^c [κ]` of the second Adams operation on the class of the residue field.

## Main results

* `Module.sum_range_neg_one_pow_mul_length_eq_sum_index`: for a long exact sequence
  `⋯ → Vᵢ →aᵢ V'ᵢ → Zᵢ → Vᵢ₋₁ → ⋯ → V'₀ → Z₀ → 0` with `Zᵢ` of finite length and `Zₙ = 0`, the
  alternating sum of the lengths of the `Zᵢ` below `n` is the alternating sum of the indices of
  the `aᵢ`.
* `Module.lengthIndex_smul_pow_two`: the index of multiplication by `c²` is twice that of
  multiplication by `c`.
* `IsRegularLocalRing.exists_isKoszulRegular_isSMulRegular_of_ringKrullDim_eq_succ`: a regular
  system of parameters of a regular local ring of dimension `c + 1`, split as `(y, f)` with the
  properties above.
* `Stacks.DerivedSquare.sum_range_neg_one_pow_mul_length_reduction`,
  `Stacks.DerivedSquare.sum_range_neg_one_pow_mul_length_quotientHomology` and
  `Stacks.DerivedSquare.sum_range_neg_one_pow_mul_length_homology_P₃`: the three Euler
  characteristic identities above.
* `Stacks.DerivedSquare.sum_range_neg_one_pow_mul_length_homology_of_isSimpleModule`: the value of
  `a_c`, computed for any simple module, and
  `Stacks.DerivedSquare.sum_range_neg_one_pow_mul_length_homology_residueField` its case `κ`.
* `Stacks.DerivedSquare.sum_tor_sub_two_mul_sum_length_homology_residueField`:
  `∑ (-1)ⁱ length Torᵢ(κ, κ) - 2 a_c = 2^c`.

## Implementation notes

Lengths are `Module.length`, valued in `ℕ∞`, and the Euler characteristics are integers formed
from `ENat.toNat` of the lengths, summed over `Finset.range`, as in
`StacksFrontier.RingTheory.Koszul.TorResidueField`. The statement for `κ` is proved for an arbitrary
simple `R`-module, which is isomorphic to `κ`; this is the form in which the induction runs, since
the module `N ⧸ fN` arising in the recursion is the residue field of `R ⧸ (f)` only up to
isomorphism. Lengths over `R ⧸ (f)` of `R ⧸ (f)`-modules agree with their lengths over `R`
(`length_restrictScalars_eq_of_surjective`).

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v

/-! ### Euler characteristics of long exact sequences -/

namespace Module

variable {A : Type*} [CommRing A]

section Spot

variable {V V' Z V₀ V₀' : Type*} [AddCommGroup V] [Module A V] [AddCommGroup V'] [Module A V']
  [AddCommGroup Z] [Module A Z] [AddCommGroup V₀] [Module A V₀] [AddCommGroup V₀'] [Module A V₀']
  {a : V →ₗ[A] V'} {b : V' →ₗ[A] Z} {d : Z →ₗ[A] V₀} {a₀ : V₀ →ₗ[A] V₀'}

/-- In an exact sequence `V →a V' →b Z →d V₀ →a₀ V₀'`, the length of `Z` is the length of the
cokernel of `a` plus the length of the kernel of `a₀`. -/
theorem length_eq_length_quotient_range_add_length_ker (hab : Function.Exact a b)
    (hbd : Function.Exact b d) (hda : Function.Exact d a₀) :
    length A Z = length A (V' ⧸ LinearMap.range a) + length A (LinearMap.ker a₀) := by
  rw [length_eq_add_of_exact (LinearMap.ker d).subtype d.rangeRestrict
    (Submodule.subtype_injective _) d.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by simp)), LinearMap.exact_iff.mp hbd,
    ← LinearMap.exact_iff.mp hda, ← b.quotKerEquivRange.length_eq, LinearMap.exact_iff.mp hab]

/-- In an exact sequence `V →a V' →b Z` with `Z` of finite length, the cokernel of `a` has finite
length. -/
theorem isFiniteLength_quotient_range_of_exact (hab : Function.Exact a b)
    (hZ : IsFiniteLength A Z) : IsFiniteLength A (V' ⧸ LinearMap.range a) := by
  rw [← LinearMap.exact_iff.mp hab]
  exact IsFiniteLength.of_injective (f := (LinearMap.range b).subtype ∘ₗ
    b.quotKerEquivRange.toLinearMap) hZ
    ((Submodule.subtype_injective _).comp b.quotKerEquivRange.injective)

/-- In an exact sequence `Z →d V₀ →a₀ V₀'` with `Z` of finite length, the kernel of `a₀` has
finite length. -/
theorem isFiniteLength_ker_of_exact (hda : Function.Exact d a₀) (hZ : IsFiniteLength A Z) :
    IsFiniteLength A (LinearMap.ker a₀) := by
  rw [LinearMap.exact_iff.mp hda]
  exact IsFiniteLength.of_surjective hZ d.surjective_rangeRestrict

end Spot

/-- For a linear map `g : M → N` between modules of finite length, the length of the cokernel
minus the length of the kernel is `length N - length M`. -/
theorem toNat_length_quotient_range_sub_toNat_length_ker {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) (hM : IsFiniteLength A M)
    (hN : IsFiniteLength A N) :
    ((length A (N ⧸ LinearMap.range g)).toNat : ℤ) - ((length A (LinearMap.ker g)).toNat : ℤ) =
      ((length A N).toNat : ℤ) - ((length A M).toNat : ℤ) := by
  have h₁ := lengthToNat_eq_ker_add_range g hM
  have h₂ : length A N = length A (LinearMap.range g) + length A (N ⧸ LinearMap.range g) :=
    length_eq_add_of_exact (LinearMap.range g).subtype (LinearMap.range g).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hN' := length_ne_top_iff.2 hN
  rw [h₂] at hN'
  rw [h₂, ENat.toNat_add (ne_top_of_le_ne_top hN' le_self_add)
    (ne_top_of_le_ne_top hN' le_add_self)]
  push_cast
  omega

/-- A telescoping identity: if `z₀ = c₀` and `zᵢ₊₁ = cᵢ₊₁ + kᵢ`, then the alternating sum of the
`zᵢ` for `i ≤ m` is that of the `cᵢ - kᵢ` plus the boundary term `(-1)ᵐ kₘ`. -/
private theorem sum_range_succ_neg_one_pow_mul_telescope (z c k : ℕ → ℤ) (h0 : z 0 = c 0)
    (hs : ∀ i, z (i + 1) = c (i + 1) + k i) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * z i =
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i * (c i - k i) + (-1) ^ m * k m := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (m + 1), hs, pow_succ]
    ring

/-- **The Euler characteristic of a long exact sequence, by indices.** Let
`⋯ → Vᵢ₊₁ →aᵢ₊₁ V'ᵢ₊₁ →bᵢ₊₁ Zᵢ₊₁ →dᵢ Vᵢ →aᵢ V'ᵢ →bᵢ Zᵢ → ⋯ → V'₀ →b₀ Z₀ → 0` be exact, with every
`Zᵢ` of finite length and `Zₙ = 0`. Then

`∑_{i < n} (-1)ⁱ length Zᵢ = ∑_{i < n} (-1)ⁱ (length (coker aᵢ) - length (ker aᵢ))`.

No finiteness is assumed on the `Vᵢ` and `V'ᵢ`: the kernels and cokernels of the `aᵢ` have finite
length because they are a quotient and a submodule of the `Zᵢ`. -/
theorem sum_range_neg_one_pow_mul_length_eq_sum_index {V V' Z : ℕ → ModuleCat.{v} A}
    (a : ∀ i, V i ⟶ V' i) (b : ∀ i, V' i ⟶ Z i) (d : ∀ i, Z (i + 1) ⟶ V i)
    (hab : ∀ i, Function.Exact (a i).hom (b i).hom)
    (hbd : ∀ i, Function.Exact (b (i + 1)).hom (d i).hom)
    (hda : ∀ i, Function.Exact (d i).hom (a i).hom) (hb : Function.Surjective (b 0).hom)
    (hZ : ∀ i, IsFiniteLength A (Z i)) {n : ℕ} (hn : Subsingleton (Z n)) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ((length A (Z i)).toNat : ℤ) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (((length A (V' i ⧸ LinearMap.range (a i).hom)).toNat : ℤ) -
          ((length A (LinearMap.ker (a i).hom)).toNat : ℤ)) := by
  have hsucc : ∀ i, length A (Z (i + 1)) =
      length A (V' (i + 1) ⧸ LinearMap.range (a (i + 1)).hom) +
        length A (LinearMap.ker (a i).hom) := fun i =>
    length_eq_length_quotient_range_add_length_ker (hab (i + 1)) (hbd i) (hda i)
  have hfin : ∀ i, length A (Z (i + 1)) ≠ ⊤ := fun i => length_ne_top_iff.2 (hZ (i + 1))
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ_neg_one_pow_mul_telescope (fun i => ((length A (Z i)).toNat : ℤ))
      (fun i => ((length A (V' i ⧸ LinearMap.range (a i).hom)).toNat : ℤ))
      (fun i => ((length A (LinearMap.ker (a i).hom)).toNat : ℤ))
      (by rw [Module.length_eq_length_quotient_range_of_surjective _ _ hb
        (LinearMap.exact_iff.mp (hab 0)).symm])
      (fun i => by
        have h := hfin i
        rw [hsucc] at h ⊢
        rw [ENat.toNat_add (ne_top_of_le_ne_top h le_self_add)
          (ne_top_of_le_ne_top h le_add_self), Nat.cast_add]) m]
    have hk : length A (LinearMap.ker (a m).hom) = 0 := by
      have h := hsucc m
      rw [length_eq_zero_iff.2 hn] at h
      exact (add_eq_zero.1 h.symm).2
    simp [hk]

/-- **The index of multiplication by a square.** On a module where multiplication by `c` has
kernel and cokernel of finite length, multiplication by `c²` has index twice that of
multiplication by `c`. -/
theorem lengthIndex_smul_pow_two {M : Type*} [AddCommGroup M] [Module A M] (c : A)
    (hk : IsFiniteLength A (LinearMap.ker (c • LinearMap.id : M →ₗ[A] M)))
    (hq : IsFiniteLength A (M ⧸ LinearMap.range (c • LinearMap.id : M →ₗ[A] M))) :
    ((length A (M ⧸ LinearMap.range (c ^ 2 • LinearMap.id : M →ₗ[A] M))).toNat : ℤ) -
        ((length A (LinearMap.ker (c ^ 2 • LinearMap.id : M →ₗ[A] M))).toNat : ℤ) =
      2 * (((length A (M ⧸ LinearMap.range (c • LinearMap.id : M →ₗ[A] M))).toNat : ℤ) -
        ((length A (LinearMap.ker (c • LinearMap.id : M →ₗ[A] M))).toNat : ℤ)) := by
  have hcomp : (c • LinearMap.id : M →ₗ[A] M) ∘ₗ (c • LinearMap.id : M →ₗ[A] M) =
      c ^ 2 • LinearMap.id := by
    ext x
    simp [pow_two, mul_smul]
  obtain ⟨hk₂, hq₂⟩ := finiteLength_kernel_cokernel_comp (c • LinearMap.id : M →ₗ[A] M)
    (c • LinearMap.id) hk hq hk hq
  have h := lengthIndex_comp (c • LinearMap.id : M →ₗ[A] M) (c • LinearMap.id) hk hq hk hk₂ hq₂
  rw [hcomp] at h
  rw [h]
  ring

end Module

/-! ### Modules over a local ring -/

/-- Two simple modules over a local ring are isomorphic: both are isomorphic to the residue
field. -/
@[sga "3 VIIB 0.2.1" "special case"]
theorem IsLocalRing.nonempty_linearEquiv_of_isSimpleModule {R : Type*} [CommRing R]
    [IsLocalRing R] (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSimpleModule R M] [IsSimpleModule R N] : Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›
  obtain ⟨J, hJ, ⟨e'⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R N›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  rw [IsLocalRing.eq_maximalIdeal hJ] at e'
  exact ⟨e.trans e'.symm⟩

/-- **`(R ⧸ J) ⧸ f(R ⧸ J)` is the residue field.** If `J` is an ideal and `f` an element of a local
ring `R` with `J + (f) = 𝔪`, then `(R ⧸ J) ⧸ f(R ⧸ J)` is a simple `R`-module. -/
theorem IsLocalRing.isSimpleModule_quotient_smul_top {R : Type*} [CommRing R] [IsLocalRing R]
    {J : Ideal R} {f : R} (h : J ⊔ Ideal.span {f} = maximalIdeal R) :
    IsSimpleModule R ((R ⧸ J) ⧸ Ideal.span {f} • (⊤ : Submodule R (R ⧸ J))) := by
  let π : R →ₗ[R] (R ⧸ J) ⧸ Ideal.span {f} • (⊤ : Submodule R (R ⧸ J)) :=
    (Ideal.span {f} • (⊤ : Submodule R (R ⧸ J))).mkQ ∘ₗ J.mkQ
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = maximalIdeal R := by
    rw [← h]
    ext r
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · have hr' : J.mkQ r ∈ Ideal.span {f} • (⊤ : Submodule R (R ⧸ J)) :=
        (Submodule.Quotient.mk_eq_zero _).1 hr
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hr'
      obtain ⟨b, -, hb⟩ := hr'
      obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective J b
      have hJ : r - f * s ∈ J := by
        rw [← Submodule.Quotient.eq]
        exact hb.symm.trans (Submodule.Quotient.mk_smul J f s).symm
      exact Submodule.mem_sup.2 ⟨r - f * s, hJ, f * s,
        Ideal.mem_span_singleton'.2 ⟨s, mul_comm _ _⟩, sub_add_cancel _ _⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
      refine ⟨Submodule.Quotient.mk t, Submodule.mem_top, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).2 ha,
        zero_add, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm]
  exact isSimpleModule_iff_quot_maximal.2 ⟨maximalIdeal R, maximalIdeal.isMaximal R,
    ⟨(π.quotKerEquivOfSurjective hπ).symm.trans (Submodule.quotEquivOfEq _ _ hker)⟩⟩

/-- An `S`-module which is simple as an `R`-module, for a surjective ring map `R → S`, is a simple
`S`-module: the two lengths agree. -/
theorem ModuleCat.isSimpleModule_of_isSimpleModule_restrictScalars {R S : Type*} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat S)
    [h : IsSimpleModule R ((ModuleCat.restrictScalars φ).obj M)] : IsSimpleModule S M := by
  rw [← Module.length_eq_one_iff, ← length_restrictScalars_eq_of_surjective R S φ hφ M]
  exact (Module.length_eq_one_iff (M := (ModuleCat.restrictScalars φ).obj M)).2 h

/-! ### A regular system of parameters, split off its last element -/

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Splitting off a parameter.** The maximal ideal of a regular local ring `R` of dimension
`c + 1` is `(y₁, …, y_c) + (f)` for a Koszul-regular sequence `y₁, …, y_c` and a nonzerodivisor
`f` which is regular on `R ⧸ (y₁, …, y_c)` and such that `R ⧸ (f)` is regular local of dimension
`c`. Take a minimal set of generators of the maximal ideal: it is a regular sequence in any
order, and each of its quotients by an initial segment is regular local ([Stacks, Tag 00NQ]). -/
theorem exists_isKoszulRegular_isSMulRegular_of_ringKrullDim_eq_succ {c : ℕ}
    (hc : ringKrullDim R = (c + 1 : ℕ)) :
    ∃ (y : Fin c → R) (f : R), Koszul.IsKoszulRegular y ∧
      Ideal.span (Set.range y) ⊔ Ideal.span {f} = maximalIdeal R ∧ f ∈ nonZeroDivisors R ∧
      IsSMulRegular (R ⧸ Ideal.span (Set.range y)) f ∧
      IsRegularLocalRing (R ⧸ Ideal.span {f}) ∧ ringKrullDim (R ⧸ Ideal.span {f}) = c := by
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hgen : Ideal.ofList s.toList = maximalIdeal R := by
    rw [← hspan]
    simp [Ideal.ofList]
  have hlen : s.toList.length = (maximalIdeal R).spanFinrank := by simp [hcard]
  have hc' : s.toList.length = c + 1 := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hc
    rw [hlen]
    exact_mod_cast h
  have hne : s.toList ≠ [] := fun h => by simp [h] at hc'
  obtain ⟨l, f, hxs⟩ : ∃ (l : List R) (f : R), s.toList = l ++ [f] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  have hl : l.length = c := by
    have h := congrArg List.length hxs
    simp only [List.length_append, List.length_singleton] at h
    omega
  have hofList : Ideal.ofList l = Ideal.span (Set.range l.get) := by
    rw [show Set.range l.get = {r | r ∈ l} from by
      ext r
      exact List.mem_iff_get.symm]
  have hgen' : Ideal.ofList (f :: l) = maximalIdeal R := by
    rw [← hgen, hxs, Ideal.ofList_cons, Ideal.ofList_append, Ideal.ofList_singleton, sup_comm]
  have hlen' : (f :: l).length = (maximalIdeal R).spanFinrank := by
    rw [← hlen, hxs]
    simp
  have H := (isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
  obtain ⟨hreg, -⟩ := H _ hgen hlen
  obtain ⟨hreg', hquot'⟩ := H _ hgen' hlen'
  obtain ⟨hloc, hdim⟩ := hquot' 1 (by simp)
  rw [show (f :: l).take 1 = [f] from rfl, Ideal.ofList_singleton] at hloc hdim
  have hfR : IsSMulRegular R f :=
    ((RingTheory.Sequence.isWeaklyRegular_cons_iff R f l).1 hreg'.toIsWeaklyRegular).1
  rw [hxs] at hreg
  obtain ⟨hlw, hfl⟩ :=
    (RingTheory.Sequence.isWeaklyRegular_append_iff R l [f]).1 hreg.toIsWeaklyRegular
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hfl
  have hsmul : Ideal.ofList l • (⊤ : Submodule R R) = Ideal.span (Set.range l.get) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hofList]
  rw [hsmul] at hfl
  have hmax : Ideal.span (Set.range l.get) ⊔ Ideal.span {f} = maximalIdeal R := by
    rw [← hofList, ← Ideal.ofList_singleton, ← Ideal.ofList_append, ← hxs, hgen]
  subst hl
  refine ⟨l.get, f, ?_, hmax, ?_, hfl, hloc, ?_⟩
  · refine (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := R)).2.2 ?_
    rw [List.ofFn_get]
    refine ⟨hlw, fun h => ?_⟩
    rw [hsmul] at h
    have hle : Ideal.span (Set.range l.get) ≤ maximalIdeal R := hmax ▸ le_sup_left
    rw [← h] at hle
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 hle)
  · have := IsRegularLocalRing.isDomain R
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    have h1 : f • (1 : R) = f • (0 : R) := by simp [h0]
    exact one_ne_zero (hfR h1)
  · have hdim' : ringKrullDim (R ⧸ Ideal.span {f}) + ((1 : ℕ) : WithBot ℕ∞) =
        ((l.length + 1 : ℕ) : WithBot ℕ∞) := hdim.trans hc
    generalize ringKrullDim (R ⧸ Ideal.span {f}) = x at hdim' ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hdim' (by rw [WithBot.bot_add]; exact (WithBot.coe_ne_bot).symm)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => norm_cast at hdim'
      | coe e =>
        norm_cast at hdim' ⊢
        omega

end IsRegularLocalRing

/-! ### The three Euler characteristic identities -/

namespace Stacks.DerivedSquare

open SimplicialProjectiveResolution AlgebraicTopology Opposite Simplicial

section General

variable {A : Type u} [CommRing A]

/-- The derived exterior squares of isomorphic modules have the same length. -/
theorem length_homology_eq_of_iso {M M' : ModuleCat.{u} A} (e : M ≅ M')
    (P : SimplicialProjectiveResolution M) (P' : SimplicialProjectiveResolution M') (i : ℕ) :
    Module.length A (homology P i) = Module.length A (homology P' i) :=
  ((simplicialLeftDerivedObjIso (exteriorSquare A) P i).symm ≪≫
    (simplicialLeftDerived (exteriorSquare A) i).mapIso e ≪≫
      simplicialLeftDerivedObjIso (exteriorSquare A) P' i).toLinearEquiv.length_eq

/-- On complexes indexed by `ℕ`, a chain map which is surjective in degree `0` is surjective on
`H₀`. -/
private theorem surjective_homologyMap_zero {K L : ChainComplex (ModuleCat.{u} A) ℕ} (φ : K ⟶ L)
    [Epi (φ.f 0)] : Function.Surjective (HomologicalComplex.homologyMap φ 0).hom :=
  (ModuleCat.epi_iff_surjective _).1
    (HomologicalComplex.epi_homologyMap_of_epi_of_not_rel φ 0 fun j => by simp)

/-- **`L₀Λ²` of a simple module vanishes**: `L₀Λ²(M) = ⋀²M`, and `M` is cyclic. -/
theorem length_homology_zero_of_isSimpleModule {M : ModuleCat.{u} A} [IsSimpleModule A M]
    (P : SimplicialProjectiveResolution M) : Module.length A (homology P 0) = 0 := by
  have := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : Subsingleton (⋀[A]^2 M) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt (fun _ : Fin 1 => m)
      (by simpa [Set.range_const] using IsSimpleModule.span_singleton_eq_top A hm) 2 (by simp)
  rw [(homologyZeroIso P).toLinearEquiv.length_eq]
  exact Module.length_eq_zero_iff.2 this

variable {r : A} {M : ModuleCat.{u} A}

/-- The reduction map `L₀Λ²_A(M) → L₀Λ²_{A ⧸ (r)}(M ⧸ rM)` is surjective. -/
theorem surjective_reductionMap_zero (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) :
    Function.Surjective (reductionMap P hr hM 0).hom := by
  have : Epi (((reductionShortComplex P hr hM).map (alternatingFaceMapComplex _)).g.f 0) :=
    (shortExact_smul_exteriorPowerReduction_app r 2 (P.obj _⦋0⦌)
      (isSMulRegular_exteriorPower hr (P.obj _⦋0⦌) 2)).epi_g
  exact (reductionHomologyIso P hr hM 0).toLinearEquiv.surjective.comp
    (surjective_homologyMap_zero _)

/-- **The Euler characteristic of the reduction modulo a regular element.** For `r` regular on `A`
and on `M`, the alternating sum of the lengths of `LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)` for `i < n` is the
alternating sum of the indices of multiplication by `r` on `LᵢΛ²_A(M)`, provided these lengths are
finite and `LₙΛ²_{A ⧸ (r)}(M ⧸ rM) = 0`. -/
theorem sum_range_neg_one_pow_mul_length_reduction (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r)
    (hfin : ∀ i, IsFiniteLength A ((ModuleCat.restrictScalars
      (Ideal.Quotient.mk (Ideal.span {r}))).obj (homology (P.reduce r hr hM) i)))
    {n : ℕ} (hn : Subsingleton (homology (P.reduce r hr hM) n)) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ((Module.length A ((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (Ideal.span {r}))).obj (homology (P.reduce r hr hM) i))).toNat : ℤ) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (((Module.length A (homology P i ⧸
          LinearMap.range (r • LinearMap.id : homology P i →ₗ[A] homology P i))).toNat : ℤ) -
        ((Module.length A
          (LinearMap.ker (r • LinearMap.id : homology P i →ₗ[A] homology P i))).toNat : ℤ)) :=
  Module.sum_range_neg_one_pow_mul_length_eq_sum_index (fun i => r • 𝟙 (homology P i))
    (fun i => reductionMap P hr hM i) (fun i => reductionδ P hr hM i)
    (fun i => exact_smul_reductionMap P hr hM i) (fun i => exact_reductionMap_reductionδ P hr hM i)
    (fun i => exact_reductionδ_smul P hr hM i) (surjective_reductionMap_zero P hr hM) hfin hn

/-- Multiplication by `r` on `LᵢΛ²_A(M)` has a cokernel of finite length when
`LᵢΛ²_{A ⧸ (r)}(M ⧸ rM)` has finite length. -/
theorem isFiniteLength_quotient_range_smul (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ)
    (hfin : IsFiniteLength A ((ModuleCat.restrictScalars
      (Ideal.Quotient.mk (Ideal.span {r}))).obj (homology (P.reduce r hr hM) i))) :
    IsFiniteLength A
      (homology P i ⧸ LinearMap.range (r • LinearMap.id : homology P i →ₗ[A] homology P i)) :=
  Module.isFiniteLength_quotient_range_of_exact (exact_smul_reductionMap P hr hM i) hfin

/-- Multiplication by `r` on `LᵢΛ²_A(M)` has a kernel of finite length when
`Lᵢ₊₁Λ²_{A ⧸ (r)}(M ⧸ rM)` has finite length. -/
theorem isFiniteLength_ker_smul (P : SimplicialProjectiveResolution M)
    (hr : r ∈ nonZeroDivisors A) (hM : IsSMulRegular M r) (i : ℕ)
    (hfin : IsFiniteLength A ((ModuleCat.restrictScalars
      (Ideal.Quotient.mk (Ideal.span {r}))).obj (homology (P.reduce r hr hM) (i + 1)))) :
    IsFiniteLength A
      (LinearMap.ker (r • LinearMap.id : homology P i →ₗ[A] homology P i)) :=
  Module.isFiniteLength_ker_of_exact (exact_reductionδ_smul P hr hM i) hfin

section Smul

variable {N : ModuleCat.{u} A} {c : A} {g : M ⟶ N} {w : (c • 𝟙 M) ≫ g = 0}
  (H : SimplicialHorseshoe (ShortComplex.mk (c • 𝟙 M) g w))

/-- The map `L₀Λ²(M) → H₀(Λ²P₂ ⧸ Λ²P₁)` is surjective. -/
theorem surjective_toQuotientHomology_zero : Function.Surjective (toQuotientHomology H 0).hom := by
  have : Epi (((alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (cokernel.π (wedgeι H ≫ filtrationι H))).f 0) := by
    rw [alternatingFaceMapComplex_map_f]
    infer_instance
  exact (surjective_homologyMap_zero _).comp
    (derivedIso (exteriorSquare A) H.P₁ H.P₂ 0).toLinearEquiv.surjective

/-- **The Euler characteristic of the cone of `c²`.** In a simplicial horseshoe over
`0 → M →c M → N → 0`, the alternating sum of the lengths of `Hᵢ(Λ²P₂ ⧸ Λ²P₁)` for `i < n` is the
alternating sum of the indices of multiplication by `c²` on `LᵢΛ²(M)`, provided these lengths are
finite and `Hₙ(Λ²P₂ ⧸ Λ²P₁) = 0`. -/
theorem sum_range_neg_one_pow_mul_length_quotientHomology
    (hfin : ∀ i, IsFiniteLength A ((quotientComplex H).homology i)) {n : ℕ}
    (hn : Subsingleton ((quotientComplex H).homology n)) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        ((Module.length A ((quotientComplex H).homology i)).toNat : ℤ) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (((Module.length A (homology H.P₁ i ⧸ LinearMap.range
          (c ^ 2 • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i))).toNat : ℤ) -
        ((Module.length A (LinearMap.ker
          (c ^ 2 • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i))).toNat : ℤ)) :=
  Module.sum_range_neg_one_pow_mul_length_eq_sum_index (fun i => c ^ 2 • 𝟙 (homology H.P₁ i))
    (fun i => toQuotientHomology H i) (fun i => quotientδ H i)
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_quotient_smul_middle H i))
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_quotient_smul_right H i))
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_quotient_smul_left H i))
    (surjective_toQuotientHomology_zero H) hfin hn

end Smul

section Cross

variable {S : ShortComplex (ModuleCat.{u} A)} (H : SimplicialHorseshoe S)

/-- The map `H₀(Λ²P₂ ⧸ Λ²P₁) → L₀Λ²(P₃)` is surjective. -/
theorem surjective_homologyMap_quotientToExteriorSquare_zero :
    Function.Surjective (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (quotientToExteriorSquare H)) 0).hom := by
  have : Epi (quotientToExteriorSquare H) := (crossSequence_shortExact H).epi_g
  have : Epi (((alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (quotientToExteriorSquare H)).f 0) := by
    rw [alternatingFaceMapComplex_map_f]
    infer_instance
  exact surjective_homologyMap_zero _

/-- In a simplicial horseshoe, `Hᵢ(Λ²P₂ ⧸ Λ²P₁)` has finite length when `Hᵢ(P₁ ⊗ P₃)` and
`LᵢΛ²(P₃)` have. -/
theorem isFiniteLength_quotientHomology (i : ℕ)
    (hT : IsFiniteLength A ((crossComplex H).homology i))
    (hL : IsFiniteLength A (homology H.P₃ i)) :
    IsFiniteLength A ((quotientComplex H).homology i) :=
  Module.finiteLength_middle_of_exact _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (exact_cross_middle H i))
    hT hL

/-- **The Euler characteristic of the cross-effect sequence.** In a simplicial horseshoe over
`0 → M' → M → M'' → 0`, if `Hᵢ(P₁ ⊗ P₃) = Torᵢ(M', M'')` and `LᵢΛ²(M'')` have finite length and
`LₙΛ²(M'') = 0`, then

`∑_{i < n} (-1)ⁱ length LᵢΛ²(M'') =
  ∑_{i < n} (-1)ⁱ (length Hᵢ(Λ²P₂ ⧸ Λ²P₁) - length Hᵢ(P₁ ⊗ P₃))`. -/
theorem sum_range_neg_one_pow_mul_length_homology_P₃
    (hT : ∀ i, IsFiniteLength A ((crossComplex H).homology i))
    (hL : ∀ i, IsFiniteLength A (homology H.P₃ i)) {n : ℕ}
    (hn : Subsingleton (homology H.P₃ n)) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ((Module.length A (homology H.P₃ i)).toNat : ℤ) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (((Module.length A ((quotientComplex H).homology i)).toNat : ℤ) -
          ((Module.length A ((crossComplex H).homology i)).toNat : ℤ)) := by
  rw [Module.sum_range_neg_one_pow_mul_length_eq_sum_index
    (fun i => HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (crossToQuotient H)) i)
    (fun i => HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (quotientToExteriorSquare H)) i)
    (fun i => crossδ H i)
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_cross_middle H i))
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_cross_right H i))
    (fun i => (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (exact_cross_left H i))
    (surjective_homologyMap_quotientToExteriorSquare_zero H) hL hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.toNat_length_quotient_range_sub_toNat_length_ker _ (hT i)
    (isFiniteLength_quotientHomology H i (hT i) (hL i))]

end Cross

section SmulCross

variable {N : ModuleCat.{u} A} {c : A} {g : M ⟶ N} {w : (c • 𝟙 M) ≫ g = 0}
  (H : SimplicialHorseshoe (ShortComplex.mk (c • 𝟙 M) g w))

/-- **The Euler characteristic of `LΛ²(N)` for `0 → M →c M → N → 0`.** It is twice the
alternating sum of the indices of multiplication by `c` on `LᵢΛ²(M)`, minus the alternating sum
of the lengths of `Hᵢ(P₁ ⊗ P₃)`, provided these are finite and vanish in degree `n`. -/
private theorem sum_range_neg_one_pow_mul_length_homology_P₃_eq_two_mul_sub
    (hT : ∀ i, IsFiniteLength A ((crossComplex H).homology i))
    (hL : ∀ i, IsFiniteLength A (homology H.P₃ i))
    (hk : ∀ i, IsFiniteLength A
      (LinearMap.ker (c • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i)))
    (hq : ∀ i, IsFiniteLength A (homology H.P₁ i ⧸
      LinearMap.range (c • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i)))
    {n : ℕ} (hTn : Subsingleton ((crossComplex H).homology n))
    (hLn : Subsingleton (homology H.P₃ n)) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * ((Module.length A (homology H.P₃ i)).toNat : ℤ) =
      2 * ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (((Module.length A (homology H.P₁ i ⧸ LinearMap.range
          (c • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i))).toNat : ℤ) -
        ((Module.length A (LinearMap.ker
          (c • LinearMap.id : homology H.P₁ i →ₗ[A] homology H.P₁ i))).toNat : ℤ)) -
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        ((Module.length A ((crossComplex H).homology i)).toNat : ℤ) := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (exact_cross_middle H n)
  have key : ∀ z : (quotientComplex H).homology n, z = 0 := fun z => by
    obtain ⟨t, ht⟩ := (hex z).1 (Subsingleton.elim _ _)
    rw [← ht, Subsingleton.elim t 0, map_zero]
  have hquot := sum_range_neg_one_pow_mul_length_quotientHomology H
    (fun i => isFiniteLength_quotientHomology H i (hT i) (hL i))
    ⟨fun x x' => (key x).trans (key x').symm⟩
  have hind := fun i => Module.lengthIndex_smul_pow_two c (hk i) (hq i)
  simp only [hind, mul_left_comm _ (2 : ℤ), ← Finset.mul_sum] at hquot
  rw [sum_range_neg_one_pow_mul_length_homology_P₃ H hT hL hLn, ← hquot,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => mul_sub _ _ _

end SmulCross

/-- The alternating sum of the lengths of `LᵢΛ²(M)` stabilizes once these vanish. -/
private theorem sum_range_neg_one_pow_mul_length_homology_eq_of_le
    (P : SimplicialProjectiveResolution M) {k m : ℕ} (hkm : k ≤ m)
    (h : ∀ i, k ≤ i → Subsingleton (homology P i)) :
    ∑ i ∈ Finset.range m, (-1 : ℤ) ^ i * ((Module.length A (homology P i)).toNat : ℤ) =
      ∑ i ∈ Finset.range k, (-1 : ℤ) ^ i * ((Module.length A (homology P i)).toNat : ℤ) :=
  Finset.eventually_constant_sum (fun i hi => by
    rw [Module.length_eq_zero_iff.2 (h i hi)]
    simp) hkm

end General

/-- If `y` is Koszul-regular in a local ring and `X` is a simple module, then
`length Torᵢ(R ⧸ (y), X) = (c choose i)`. -/
private theorem _root_.IsLocalRing.length_tor_quotient_of_isSimpleModule {R : Type u} [CommRing R]
    [IsLocalRing R] {c : ℕ} (y : Fin c → R) (hy : Koszul.IsKoszulRegular y)
    (hle : Ideal.span (Set.range y) ≤ maximalIdeal R) (X : Type u) [AddCommGroup X] [Module R X]
    [IsSimpleModule R X] (i : ℕ) :
    Module.length R (((Tor' (ModuleCat.{u} R) i).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range y)))).obj (ModuleCat.of R X)) = c.choose i := by
  refine (Koszul.length_tor_of_le_annihilator y hy X ?_ i).trans ?_
  · rwa [IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := X))]
  · rw [Module.length_eq_one R X, mul_one]

/-- An alternating sum of binomial coefficients `c.choose i` over `i < n`, for `c < n`. -/
private theorem _root_.Int.alternating_sum_range_choose_of_lt {c n : ℕ} (h : c < n) :
    ∑ i ∈ Finset.range n, ((-1) ^ i * c.choose i : ℤ) = if c = 0 then 1 else 0 := by
  rw [Finset.eventually_constant_sum (N := c + 1) (fun i hi => by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp) (by omega)]
  exact Int.alternating_sum_range_choose

/-! ### The residue field of a regular local ring -/

/-- The inductive step of `sum_range_neg_one_pow_mul_length_homology_of_isSimpleModule`:
`a_{c+1} = 2 a_c - [c = 0]`, with `a_c = 0` for `c = 0` and `a_c = -2^(c-1)` otherwise. -/
private theorem sum_range_neg_one_pow_mul_length_homology_succ {c : ℕ}
    (ih : ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R], ringKrullDim R = c →
      ∀ {M : ModuleCat.{u} R} [IsSimpleModule R M] (P : SimplicialProjectiveResolution M),
        ∑ i ∈ Finset.range (2 * c + 1),
            (-1 : ℤ) ^ i * ((Module.length R (homology P i)).toNat : ℤ) =
          if c = 0 then 0 else -2 ^ (c - 1))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (hc : ringKrullDim R = (c + 1 : ℕ))
    {M : ModuleCat.{u} R} [IsSimpleModule R M] (P : SimplicialProjectiveResolution M) :
    ∑ i ∈ Finset.range (2 * (c + 1) + 1),
        (-1 : ℤ) ^ i * ((Module.length R (homology P i)).toNat : ℤ) = -2 ^ c := by
  obtain ⟨y, f, hy, hspan, hf, hfN, hloc, hdim⟩ :=
    IsRegularLocalRing.exists_isKoszulRegular_isSMulRegular_of_ringKrullDim_eq_succ hc
  let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ Ideal.span (Set.range y))
  let φ := Ideal.Quotient.mk (Ideal.span {f})
  let X : ModuleCat.{u} R :=
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj N)
  let H := SimplicialHorseshoe.ofResolutions
    (Classical.arbitrary (SimplicialProjectiveResolution N))
    (Classical.arbitrary (SimplicialProjectiveResolution X)) (shortExact_smul_unit_app f N hfN)
  let Q := H.P₁.reduce f hf hfN
  have hXsimple : IsSimpleModule R X := by
    have := IsLocalRing.isSimpleModule_quotient_smul_top hspan
    exact IsSimpleModule.congr (TensorProduct.quotTensorEquivQuotSMul N (Ideal.span {f}) :
      X ≃ₗ[R] N ⧸ Ideal.span {f} • (⊤ : Submodule R N))
  have hXsimple' : IsSimpleModule (R ⧸ Ideal.span {f}) ((ModuleCat.extendScalars φ).obj N) :=
    ModuleCat.isSimpleModule_of_isSimpleModule_restrictScalars φ Ideal.Quotient.mk_surjective _
  have hW : ∀ i, Module.length R ((ModuleCat.restrictScalars φ).obj (homology Q i)) =
      Module.length (R ⧸ Ideal.span {f}) (homology Q i) := fun i =>
    length_restrictScalars_eq_of_surjective R _ φ Ideal.Quotient.mk_surjective _
  have hWfin : ∀ i, IsFiniteLength R ((ModuleCat.restrictScalars φ).obj (homology Q i)) :=
    fun i => by
      rw [← Module.length_ne_top_iff, hW]
      exact Module.length_ne_top_iff.2
        (isFiniteLength_homology (IsSimpleModule.isFiniteLength _ _) Q i)
  have hQzero : ∀ i, 2 * c < i → Subsingleton (homology Q i) := fun i hi =>
    ModuleCat.isZero_iff_subsingleton.1 (isZero_homology_of_isRegularLocalRing hdim.le Q hi)
  have hT : ∀ i, Module.length R ((crossComplex H).homology i) = c.choose i := fun i => by
    rw [(crossHomologyIsoTor H i).toLinearEquiv.length_eq]
    exact IsLocalRing.length_tor_quotient_of_isSimpleModule y hy (le_sup_left.trans hspan.le) X i
  have hTn : Subsingleton ((crossComplex H).homology (2 * (c + 1) + 1)) :=
    Module.length_eq_zero_iff.1 (by rw [hT, Nat.choose_eq_zero_of_lt (by omega)]; rfl)
  have hLzero : Subsingleton (homology H.P₃ (2 * (c + 1) + 1)) :=
    ModuleCat.isZero_iff_subsingleton.1
      (isZero_homology_of_isRegularLocalRing hc.le H.P₃ (by omega))
  obtain ⟨e⟩ := IsLocalRing.nonempty_linearEquiv_of_isSimpleModule (R := R) M X
  simp only [fun i => length_homology_eq_of_iso e.toModuleIso P H.P₃ i]
  rw [sum_range_neg_one_pow_mul_length_homology_P₃_eq_two_mul_sub H
      (fun i => Module.length_ne_top_iff.1 (by rw [hT]; exact ENat.natCast_ne_top _))
      (fun i => isFiniteLength_homology (IsSimpleModule.isFiniteLength R X) H.P₃ i)
      (fun i => isFiniteLength_ker_smul H.P₁ hf hfN i (hWfin (i + 1)))
      (fun i => isFiniteLength_quotient_range_smul H.P₁ hf hfN i (hWfin i)) hTn hLzero,
    ← sum_range_neg_one_pow_mul_length_reduction H.P₁ hf hfN hWfin (hQzero _ (by omega))]
  simp only [φ, Q] at hW
  simp only [hW, hT, ENat.toNat_natCast]
  rw [sum_range_neg_one_pow_mul_length_homology_eq_of_le Q (k := 2 * c + 1)
    (m := 2 * (c + 1) + 1) (by omega) hQzero, ih hdim Q,
    Int.alternating_sum_range_choose_of_lt (by omega)]
  rcases c with _ | c <;> simp
  ring

/-- **The Euler characteristic of the derived exterior square of the residue field.** Let `R` be a
regular local ring of dimension `c` and `M` a simple `R`-module, for instance the residue field
`κ`. For any simplicial projective resolution `P` of `M`,

`∑_{i ≤ 2c} (-1)ⁱ length_R LᵢΛ²_R(M) = -2^(c-1)` if `c ≥ 1`, and `= 0` if `c = 0`.

The modules `LᵢΛ²_R(M)` have finite length (`isFiniteLength_homology` with
`IsSimpleModule.isFiniteLength`) and vanish for `i > 2c` (`isZero_homology_of_isRegularLocalRing`),
so this is the whole Euler characteristic. The proof is the recursion `a_c = 2 a_{c-1} - [c = 1]`
through `R ⧸ (f)` for a regular parameter `f`, described in the module docstring. -/
theorem sum_range_neg_one_pow_mul_length_homology_of_isSimpleModule (c : ℕ) {R : Type u}
    [CommRing R] [IsRegularLocalRing R] (hc : ringKrullDim R = c) {M : ModuleCat.{u} R}
    [IsSimpleModule R M] (P : SimplicialProjectiveResolution M) :
    ∑ i ∈ Finset.range (2 * c + 1),
        (-1 : ℤ) ^ i * ((Module.length R (homology P i)).toNat : ℤ) =
      if c = 0 then 0 else -2 ^ (c - 1) := by
  induction c generalizing R with
  | zero => simp [length_homology_zero_of_isSimpleModule P]
  | succ c ih =>
    rw [ite_eq_right (Nat.add_one_ne_zero c), Nat.add_sub_cancel]
    exact sum_range_neg_one_pow_mul_length_homology_succ (@fun _ _ _ hc' _ _ P' => ih hc' P') hc P

/-- **The Euler characteristic of `LΛ²_R(κ)`.** For a regular local ring `R` of dimension `c` with
residue field `κ`, `∑_{i ≤ 2c} (-1)ⁱ length_R LᵢΛ²_R(κ)` is `-2^(c-1)` if `c ≥ 1` and `0` if
`c = 0`. -/
theorem sum_range_neg_one_pow_mul_length_homology_residueField {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {c : ℕ} (hc : ringKrullDim R = c)
    (P : SimplicialProjectiveResolution (ModuleCat.of R (ResidueField R))) :
    ∑ i ∈ Finset.range (2 * c + 1),
        (-1 : ℤ) ^ i * ((Module.length R (homology P i)).toNat : ℤ) =
      if c = 0 then 0 else -2 ^ (c - 1) :=
  have : IsSimpleModule R (ResidueField R) :=
    Module.length_eq_one_iff.1 Stacks.OrderOfVanishing.length_residueField
  sum_range_neg_one_pow_mul_length_homology_of_isSimpleModule c hc P

/-- **`ψ²(κ) = 2^c`.** For a regular local ring `R` of dimension `c` with residue field `κ`, the
supported square `[κ]·[κ] = ∑_{n ≤ c} (-1)ⁿ length_R Torₙ^R(κ, κ)` minus twice the Euler
characteristic `∑_{i ≤ 2c} (-1)ⁱ length_R LᵢΛ²_R(κ)` of the derived exterior square is `2^c`. -/
theorem sum_tor_sub_two_mul_sum_length_homology_residueField {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {c : ℕ} (hc : ringKrullDim R = c)
    (P : SimplicialProjectiveResolution (ModuleCat.of R (ResidueField R))) :
    ∑ n ∈ Finset.range (c + 1), (-1 : ℤ) ^ n * ((Module.length R (((Tor' (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R (ResidueField R)))).toNat : ℤ) -
      2 * ∑ i ∈ Finset.range (2 * c + 1),
        (-1 : ℤ) ^ i * ((Module.length R (homology P i)).toNat : ℤ) = 2 ^ c := by
  rw [IsRegularLocalRing.sum_range_neg_one_pow_mul_length_tor_residueField_residueField hc,
    sum_range_neg_one_pow_mul_length_homology_residueField hc P]
  rcases c with _ | c
  · simp
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    ring

end Stacks.DerivedSquare

end
