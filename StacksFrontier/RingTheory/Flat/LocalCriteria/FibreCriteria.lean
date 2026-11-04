module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
public import StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor
import all StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion

/-!
# Criteria for flatness over a Noetherian local base: 00ME to 00MI

The Noetherian step and statement of Stacks 00ME, and its consequences: lifting a
nonzerodivisor (00MF) and a regular sequence (00MG) from the fibre, freeness from a free fibre
(00MH) and exactness of a complex from exactness of its fibre (00MI).
-/

section

universe u v w

@[expose] public section

section

open Function TensorProduct IsLocalRing

namespace Stacks.Flatness.LocalCriterion

/-- The fibre of a quotient is the quotient of the fibre: the class of `x` lies in `J(M/p)` exactly
when `x` lies in `JM + p`. -/
private lemma mk_mem_smul_top_iff {A B : Type*} [CommRing A] [AddCommGroup B] [Module A B]
    (J : Ideal A) (p : Submodule A B) (x : B) :
    (Submodule.Quotient.mk x : B ⧸ p) ∈ J • (⊤ : Submodule A (B ⧸ p)) ↔
      x ∈ J • (⊤ : Submodule A B) ⊔ p := by
  have hmap : J • (⊤ : Submodule A (B ⧸ p)) = Submodule.map p.mkQ (J • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [hmap, ← Submodule.mkQ_apply, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]

section Noetherian

variable {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Krull's intersection theorem for the finite `S`-module `N/IN`, whose `𝔪S`-adic filtration is
the image of the filtration by `𝔪ⁿ + I`, turns
`Stacks.Flatness.LocalCriterion.comap_smul_top_pow_add_le` into `u⁻¹(IM) ⊆ IN`. -/
private lemma comap_smul_top_le [Module.Flat R M] [Module.Finite S N] (u : N →ₗ[R] M)
    (hu : Injective (u.lTensor (R ⧸ maximalIdeal R))) (I : Ideal R) :
    ((I • (⊤ : Submodule R M)).comap u) ≤ I • (⊤ : Submodule R N) := by
  have hmax := IsLocalRing.maximalIdeal.isMaximal R
  set 𝔪 := maximalIdeal R
  intro y hy
  rw [Submodule.mem_comap] at hy
  -- `IN` is an `S`-submodule of `N`, so Krull's intersection theorem applies to `N/IN`.
  set K : Submodule S N := (I.map (algebraMap R S)) • ⊤ with hK
  rw [← Module.Flat.mem_map_smul_top_iff (S := S) I y, ← hK]
  have : Module.Finite S (N ⧸ K) := Module.Finite.of_surjective K.mkQ (Submodule.mkQ_surjective K)
  have hmk : K.mkQ y = 0 := by
    have hmem : K.mkQ y ∈
        ⨅ n : ℕ, (𝔪.map (algebraMap R S)) ^ n • (⊤ : Submodule S (N ⧸ K)) := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 : y ∈ (𝔪 ^ n + I) • (⊤ : Submodule R N) :=
        comap_smul_top_pow_add_le u hu I n (Submodule.smul_mono_left le_sup_right hy)
      rw [Ideal.add_eq_sup, Submodule.sup_smul, Submodule.mem_sup] at h1
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := h1
      rw [Submodule.mkQ_apply, mk_mem_smul_top_iff]
      refine Submodule.add_mem_sup ?_ ((Module.Flat.mem_map_smul_top_iff (S := S) I y₂).2 hy₂)
      rw [← Ideal.map_pow]
      exact (Module.Flat.mem_map_smul_top_iff (S := S) (𝔪 ^ n) y₁).2 hy₁
    rwa [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N ⧸ K) _
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne] at hmem
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk

end Noetherian

section Fibre

variable {R N M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The fibre `ū : N/IN → M/IM` of `u` is injective exactly when `R/I ⊗ u` is; this is the
direction the source's hypothesis is used in. -/
private lemma injective_lTensor_of_injective_mapQ {I : Ideal R} (u : N →ₗ[R] M)
    (hu : Injective (Submodule.mapQ (I • (⊤ : Submodule R N)) (I • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top I u))) :
    Injective (u.lTensor (R ⧸ I)) := by
  have hmkN : Surjective (TensorProduct.mk R (R ⧸ I) N 1) := by
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ]
    exact (TensorProduct.quotTensorEquivQuotSMul N I).symm.surjective.comp
      (Submodule.mkQ_surjective _)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := hmkN z
  rw [show (u.lTensor (R ⧸ I)) (TensorProduct.mk R (R ⧸ I) N 1 y)
      = TensorProduct.mk R (R ⧸ I) M 1 (u y) from by simp,
    ← LinearMap.mem_ker, LinearMap.ker_tensorProductMk] at hz
  have h3 : (I • (⊤ : Submodule R N)).mkQ y = 0 := by
    refine hu ?_
    rw [map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
  rw [← LinearMap.mem_ker, LinearMap.ker_tensorProductMk]
  exact h3

end Fibre

open IsLocalRing in
/-- **Stacks 00ME.** -/
private theorem solution
    {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    (u : N →ₗ[R] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u))) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) := by
  have hkey := comap_smul_top_le (S := S) u (injective_lTensor_of_injective_mapQ u hu)
  refine ⟨?_, flat_quotient_range_of_comap_smul_top_le u hkey⟩
  have h := hkey ⊥
  rw [Submodule.bot_smul, Submodule.bot_smul, le_bot_iff] at h
  exact LinearMap.ker_eq_bot.1 h

end Stacks.Flatness.LocalCriterion

end

section

open IsLocalRing in
/-- **Stacks 00ME.** Let `R → S` be a local homomorphism of local rings with `S` Noetherian, let
`𝔪` be the maximal ideal of `R`, let `M` be a flat `R`-module, let `N` be a finite `S`-module and
let `u : N → M` be a map of `R`-modules. If the induced map `ū : N/𝔪N → M/𝔪M` is injective, then
`u` is injective and `M/u(N)` is flat over `R`.

Here `N/𝔪N` is `N ⧸ 𝔪 • ⊤` and `ū` is the canonical `Submodule.mapQ`, which sends the class of `x`
to the class of `u x`; see the module docstring. -/
@[stacks 00ME "`N/𝔪N` is `N ⧸ 𝔪 • (⊤ : Submodule R N)` and `ū` the canonical `Submodule.mapQ` of
`u`. The cokernel `M/u(N)` is `M ⧸ LinearMap.range u`, and the two conclusions are conjoined; see
the module docstring. The non-Noetherian generalization is 046Y.", ega "III 4.6.7.1"]
theorem
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
    {R S N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    (u : N →ₗ[R] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal R • (⊤ : Submodule R N))
      (maximalIdeal R • (⊤ : Submodule R M)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u))) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) :=
      Stacks.Flatness.LocalCriterion.solution (S := S) u hu

end

/-! ### Stacks 00MF -/

section


namespace Stacks.Flatness.FibreNonZeroDivisor

/-- The map induced by `g` on the quotients `M ⧸ p → N ⧸ q` is injective exactly when `g` reflects
membership, that is when `q.comap g ≤ p`. -/
public lemma mapQ_injective_iff {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {p : Submodule R M} {q : Submodule R N} {g : M →ₗ[R] N}
    (h : p ≤ q.comap g) :
    Function.Injective (Submodule.mapQ p q g h) ↔ q.comap g ≤ p := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, eq_bot_iff, Submodule.map_le_iff_le_comap,
    Submodule.comap_bot, Submodule.ker_mkQ]

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If the class of `f` is a nonzerodivisor in the fibre ring `S ⧸ IS`, then multiplication by `f`
induces an injective map on the fibres `S/IS` of `S` over `R ⧸ I`.

This is the hypothesis of Stacks 00ME for `u = f · : S → S`. Its content is that `f * x ∈ IS`
forces `x ∈ IS`, which is what it means for the class of `f` to kill nothing in `S ⧸ IS`. -/
private lemma injective_mapQ_mul_of_mem_nonZeroDivisors (I : Ideal R) {f : S}
    (hf : Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) f ∈
      nonZeroDivisors (S ⧸ Ideal.map (algebraMap R S) I)) :
    Function.Injective (Submodule.mapQ (I • (⊤ : Submodule R S)) (I • (⊤ : Submodule R S))
      ((LinearMap.mul S S f).restrictScalars R)
      (Submodule.smul_top_le_comap_smul_top I _)) := by
  refine (mapQ_injective_iff _).2 fun x hx => ?_
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, LinearMap.mul_apply',
    Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← Ideal.Quotient.eq_zero_iff_mem,
    map_mul] at hx ⊢
  exact (mem_nonZeroDivisors_iff.1 hf).1 _ hx

/-- The cokernel of multiplication by `f` on an `R`-algebra `S`: the range of `f · : S → S`, viewed
as an `R`-submodule of `S`, is the ideal `fS` with its scalars restricted to `R`. -/
private lemma range_restrictScalars_mul (f : S) :
    LinearMap.range ((LinearMap.mul S S f).restrictScalars R)
      = Submodule.restrictScalars R (Ideal.span {f}) := by
  rw [LinearMap.range_restrictScalars, Ideal.range_mul']

end

private theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {f : S}
    (hf : Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) f ∈
      nonZeroDivisors (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))) :
    f ∈ nonZeroDivisors S ∧ Module.Flat R (S ⧸ Ideal.span {f}) := by
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) ((LinearMap.mul S S f).restrictScalars R)
      (injective_mapQ_mul_of_mem_nonZeroDivisors _ hf)
  exact ⟨isRegular_iff_mem_nonZeroDivisors.1 (isLeftRegular_iff_isRegular.1 hinj),
    Module.Flat.of_linearEquiv
      ((Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {f})).symm.trans
        (Submodule.quotEquivOfEq _ _ (range_restrictScalars_mul f).symm))⟩

end Stacks.Flatness.FibreNonZeroDivisor

end

section

namespace Module.Flat

/-- The map of `R`-fibres `N/IN → M/IM` induced by an `S`-linear map `u : N → M` over an
`R`-algebra `S` is injective as soon as `u a ∈ (IS) • ⊤` forces `a ∈ (IS) • ⊤`, a condition on the
`S`-side: the `R`- and `S`-side fibres are quotients by submodules with the same elements. -/
public lemma injective_mapQ_restrictScalars_of_forall_mem {R S M N : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (I : Ideal R) (u : N →ₗ[S] M)
    (h : ∀ a : N, u a ∈ Ideal.map (algebraMap R S) I • (⊤ : Submodule S M) →
      a ∈ Ideal.map (algebraMap R S) I • (⊤ : Submodule S N)) :
    Function.Injective (Submodule.mapQ (I • (⊤ : Submodule R N)) (I • (⊤ : Submodule R M))
      (u.restrictScalars R) (Submodule.smul_top_le_comap_smul_top _ _)) := by
  refine (Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff _).2 fun a ha => ?_
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    ← mem_map_smul_top_iff (S := S)] at ha
  exact (mem_map_smul_top_iff (S := S) I a).1 (h a ha)

end Module.Flat

end

section

namespace Module.Flat

/-- **Stacks 00MF.** Let `R → S` be a flat and local ring homomorphism of Noetherian local rings,
let `𝔪` be the maximal ideal of `R`, and let `f ∈ S` be a nonzerodivisor in `S/𝔪S`. Then `f` is a
nonzerodivisor in `S` and `S/fS` is flat over `R`.

Here `S/𝔪S` is the ring quotient `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)`,
the image of `f` in it is pinned as `Ideal.Quotient.mk`, and `S/fS` is `S ⧸ Ideal.span {f}` with
its canonical `R`-algebra structure; see the module docstring. -/
@[stacks 00MF "\"Nonzerodivisor\" is `nonZeroDivisors` at the level of rings, as in the source:
`𝔪S` is `Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and `S/fS` is
`S ⧸ Ideal.span {f}`. The two conclusions are conjoined, in the order of the sibling lemmas 00ME
and 046Z rather than the source's. `IsNoetherianRing R` is redundant (faithful flatness descends
the ascending chain condition) but is part of the tag's hypotheses; see the module docstring.",
  sga "3 V 7.2"]
theorem
    mem_nonZeroDivisors_and_flat_quotient_span_singleton_of_mem_nonZeroDivisors_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {f : S}
    (hf : Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) f ∈
      nonZeroDivisors (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))) :
    f ∈ nonZeroDivisors S ∧ Module.Flat R (S ⧸ Ideal.span {f}) :=
      Stacks.Flatness.FibreNonZeroDivisor.solution hf

end Module.Flat

end

/-! ### Stacks 00MG -/

section

namespace Module.Flat

/-- Flatness over a base `R` passes to a quotient by a submodule that vanishes. -/
public lemma quotient_of_eq_bot {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Flat R M]
    {p : Submodule S M} (hp : p = ⊥) : Module.Flat R (M ⧸ p) :=
  .of_linearEquiv ((Submodule.quotEquivOfEqBot p hp).restrictScalars R)

end Module.Flat

end


section


namespace Stacks.Flatness.RegularSequenceQuotient

open RingTheory.Sequence
open scoped Pointwise


/-- Regularity of a sequence in a commutative ring is invariant under ring isomorphism. -/
public lemma isRegular_ringEquiv_congr {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (as : List A) : IsRegular A as ↔ IsRegular B (as.map e) :=
  AddEquiv.isRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => by simp))

/-- A sequence `a :: as` in a commutative ring `A` is regular if and only if `a` is a
nonzerodivisor and the image of `as` is a regular sequence in `A ⧸ (a)`. This is the ring-level
reading of `RingTheory.Sequence.isRegular_cons_iff'`, whose two halves are phrased for the module
`A` and its quotient by the submodule `a • ⊤`. -/
private lemma isRegular_cons_iff_mem_nonZeroDivisors {A : Type*} [CommRing A] (a : A)
    (as : List A) :
    IsRegular A (a :: as) ↔ a ∈ nonZeroDivisors A ∧
      IsRegular (A ⧸ Ideal.span {a}) (as.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
  rw [isRegular_cons_iff']
  refine and_congr ?_ ?_
  · rw [← isLeftRegular_iff, isLeftRegular_iff_isRegular, isRegular_iff_mem_nonZeroDivisors]
  · have h : (a • (⊤ : Submodule A A)) = (Ideal.span {a} : Ideal A) := by
      rw [← Submodule.ideal_span_singleton_smul]; simp
    exact AddEquiv.isRegular_congr (e := (Submodule.quotEquivOfEq _ _ h).toAddEquiv)
      (List.forall₂_same.mpr (by
        intro r _ x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        induction x using Quotient.ind
        rfl))

/-- A commutative ring carrying a regular sequence in one of its quotients is nonzero: `IsRegular`
demands that the last quotient of the sequence be nonzero. -/
private lemma nontrivial_of_isRegular_quotient {A : Type*} [CommRing A] {I : Ideal A}
    {as : List (A ⧸ I)} (h : IsRegular (A ⧸ I) as) : Nontrivial A :=
  have := h.nontrivial
  (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I)).nontrivial

/-- A local homomorphism into a local ring `S` stays local after composing with a quotient map of
`S` onto a nonzero ring, that quotient being local as well. -/
private lemma isLocalHom_algebraMap_quotient {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] (J : Ideal S) [Nontrivial (S ⧸ J)] :
    IsLocalHom (algebraMap R (S ⧸ J)) := by
  have : IsLocalHom (Ideal.Quotient.mk J) := .of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  infer_instance

/-- The two ways of forming the fibre over `𝔪` of `R → S ⧸ (f)`: quotient the fibre of `R → S` by
the image of `f`, or quotient `S ⧸ (f)` by the image of `𝔪`. -/
private noncomputable def fibreQuotEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔪 : Ideal R) (f : S) :
    ((S ⧸ Ideal.map (algebraMap R S) 𝔪) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.map (algebraMap R S) 𝔪) f}) ≃+*
      ((S ⧸ Ideal.span {f}) ⧸ Ideal.map (algebraMap R (S ⧸ Ideal.span {f})) 𝔪) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
    ((DoubleQuot.quotQuotEquivComm (Ideal.map (algebraMap R S) 𝔪) (Ideal.span {f})).trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_map, Ideal.Quotient.mk_comp_algebraMap])))

/-- `fibreQuotEquiv` carries the class of `x : S` to the class of `x`. -/
private lemma fibreQuotEquiv_mk_mk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝔪 : Ideal R) (f x : S) :
    fibreQuotEquiv 𝔪 f (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {f}) x) := rfl

/-- The inductive step of Stacks 00MG on the side of the fibre: a sequence in the fibre of `R → S`
is regular modulo the image of `f` if and only if its image in the fibre of `R → S ⧸ (f)` is
regular. This is the identification of the two fibres, `fibreQuotEquiv`, read on sequences. -/
private lemma isRegular_fibre_quotient_span_singleton_iff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (𝔪 : Ideal R) (f : S) (l : List S) :
    IsRegular ((S ⧸ Ideal.map (algebraMap R S) 𝔪) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.map (algebraMap R S) 𝔪) f})
      ((l.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) 𝔪))).map (Ideal.Quotient.mk
        (Ideal.span {Ideal.Quotient.mk (Ideal.map (algebraMap R S) 𝔪) f}))) ↔
      IsRegular ((S ⧸ Ideal.span {f}) ⧸ Ideal.map (algebraMap R (S ⧸ Ideal.span {f})) 𝔪)
        ((l.map (Ideal.Quotient.mk (Ideal.span {f}))).map (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (S ⧸ Ideal.span {f})) 𝔪))) := by
  rw [isRegular_ringEquiv_congr (fibreQuotEquiv 𝔪 f)]
  simp only [List.map_map, Function.comp_def, fibreQuotEquiv_mk_mk]

/-- The flatness half of the inductive step of Stacks 00MG: the partial quotients of `S` along
`f :: l` are flat over `R` as soon as `S` is and the partial quotients of `S ⧸ (f)` along the image
of `l` are, since `S ⧸ (f, l₁, …, l_i)` is `(S ⧸ (f)) ⧸ (l̄₁, …, l̄_i)`. -/
private lemma flat_quotient_ofList_take_cons {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (f : S) (l : List S)
    (h : ∀ i, Module.Flat R ((S ⧸ Ideal.span {f}) ⧸
      Ideal.ofList ((l.map (Ideal.Quotient.mk (Ideal.span {f}))).take i))) :
    ∀ i, Module.Flat R (S ⧸ Ideal.ofList ((f :: l).take i))
  | 0 => Module.Flat.quotient_of_eq_bot (by simp)
  | i + 1 => by
    have hi : Module.Flat R ((S ⧸ Ideal.span {f}) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) (Ideal.ofList (l.take i))) := by
      have := h i; rwa [← List.map_take, ← Ideal.map_ofList] at this
    have e : (S ⧸ (Ideal.span {f} ⊔ Ideal.ofList (l.take i))) ≃ₗ[R]
        ((S ⧸ Ideal.span {f}) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) (Ideal.ofList (l.take i))) :=
      (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {f})
        (Ideal.ofList (l.take i))).symm.toLinearEquiv
    rw [List.take_succ_cons, Ideal.ofList_cons]
    exact .of_linearEquiv e

open Module.Flat in
/-- The induction behind Stacks 00MG, on the length `n` of the sequence: the base ring `R` is
fixed, the ring `S` is replaced by `S ⧸ (f₁)` at each step, and the inductive step is 00MF. -/
private theorem key (n : ℕ) :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
      [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
      [Module.Flat R S] (fs : List S), fs.length = n →
      IsRegular (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
        (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))) →
      IsRegular S fs ∧ ∀ i, Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) := by
  induction n with
  | zero =>
    intro R S _ _ _ _ _ _ _ _ _ fs hlen _
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact ⟨.nil S S, fun _ => Module.Flat.quotient_of_eq_bot (by simp)⟩
  | succ n ih =>
    intro R S _ _ _ _ _ _ _ _ _ fs hlen hfs
    obtain ⟨f, l, rfl⟩ := List.exists_of_length_succ fs hlen
    rw [List.map_cons, isRegular_cons_iff_mem_nonZeroDivisors] at hfs
    -- Stacks 00MF: `f` is a nonzerodivisor in `S` and `S ⧸ (f)` is flat over `R`.
    obtain ⟨hfnzd, hflat⟩ :=
      mem_nonZeroDivisors_and_flat_quotient_span_singleton_of_mem_nonZeroDivisors_maximalIdeal
        (S := S) hfs.1
    -- The fibre of `R → S ⧸ (f)` is the fibre of `R → S` modulo the image of `f`.
    have hfib := (isRegular_fibre_quotient_span_singleton_iff
      (IsLocalRing.maximalIdeal R) f l).mp hfs.2
    -- so `S ⧸ (f)` is again a Noetherian local ring, flat and local over `R`.
    have : Nontrivial (S ⧸ Ideal.span {f}) := nontrivial_of_isRegular_quotient hfib
    have : IsLocalRing (S ⧸ Ideal.span {f}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap R (S ⧸ Ideal.span {f})) := isLocalHom_algebraMap_quotient _
    obtain ⟨hreg, hflats⟩ :=
      ih (l.map (Ideal.Quotient.mk (Ideal.span {f}))) (by simpa using hlen) hfib
    exact ⟨(isRegular_cons_iff_mem_nonZeroDivisors f l).mpr ⟨hfnzd, hreg⟩,
      flat_quotient_ofList_take_cons f l hflats⟩

private theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {fs : List S}
    (hfs : RingTheory.Sequence.IsRegular
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))))) :
    RingTheory.Sequence.IsRegular S fs ∧
      ∀ i, Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) :=
  key fs.length fs rfl hfs

end Stacks.Flatness.RegularSequenceQuotient

end

section


/-- **Stacks 00MG.** Let `R → S` be a flat and local ring homomorphism of Noetherian local rings,
let `𝔪` be the maximal ideal of `R`, and let `f₁, …, f_c` be elements of `S` whose images form a
regular sequence in `S/𝔪S`. Then `f₁, …, f_c` is a regular sequence in `S` and each of the
quotients `S/(f₁, …, f_i)` is flat over `R`.

Here `S/𝔪S` is the ring quotient `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)`, the
images are pinned as `Ideal.Quotient.mk`, and `S/(f₁, …, f_i)` is `S ⧸ Ideal.ofList (fs.take i)`
with its canonical `R`-algebra structure; see the module docstring. -/
@[stacks 00MG "\"Regular sequence\" is `RingTheory.Sequence.IsRegular`, which is Definition 00LF
verbatim, nonvanishing clause included, and the sequence is a `List S`. The fibre is
`S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and `S/(f₁, …, f_i)` is
`S ⧸ Ideal.ofList (fs.take i)`, quantified over all `i : ℕ` since `List.take` saturates.
`IsNoetherianRing R` and `IsLocalHom (algebraMap R S)` are both redundant here but are part of the
tag's hypotheses; see the module docstring.",
  ega "0 15.1.16" "c) => a), M = B",
  ega "IV 11.3.8" "(c) ⇒ (a), special case"]
theorem Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    {fs : List S}
    (hfs : RingTheory.Sequence.IsRegular
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (fs.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))))) :
    RingTheory.Sequence.IsRegular S fs ∧
      ∀ i, Module.Flat R (S ⧸ Ideal.ofList (fs.take i)) :=
        Stacks.Flatness.RegularSequenceQuotient.solution hfs

end

/-! ### Stacks 00MH -/

section


namespace Stacks.Flatness.FreeFromFreeFibre

open IsLocalRing Module.Flat

/-- A tuple over a finite index type all of whose entries lie in `I` lies in `I • ⊤`. -/
private theorem mem_smul_top_of_forall_mem {S ι : Type*} [CommRing S] [Finite ι] {I : Ideal S}
    {a : ι → S} (ha : ∀ i, a i ∈ I) : a ∈ I • (⊤ : Submodule S (ι → S)) := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single a]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h : Pi.single i (a i) = a i • (Pi.single i 1 : ι → S) := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [h]
  exact Submodule.smul_mem_smul (ha i) Submodule.mem_top

section Fibre

variable {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] [Fintype ι]

/-- Reducing modulo `I` the map `S^ι → M` defined by a family `x` gives the map `(S/I)^ι → M/IM`
defined by the reductions of the `x i`. -/
private theorem mkQ_linearCombination (I : Ideal S) (x : ι → M) (a : ι → S) :
    (I • (⊤ : Submodule S M)).mkQ (Fintype.linearCombination S x a)
      = Fintype.linearCombination (S ⧸ I) (fun i => (I • (⊤ : Submodule S M)).mkQ (x i))
          (fun i => Ideal.Quotient.mk I (a i)) := by
  simp [Fintype.linearCombination_apply]

/-- The map `S^ι → M` defined by a basis of `M` is surjective. -/
private theorem surjective_linearCombination_basis (b : Module.Basis ι S M) :
    Function.Surjective (Fintype.linearCombination S b) :=
  fun y => ⟨b.repr y, by rw [Fintype.linearCombination_apply]; exact b.sum_repr y⟩

/-- **Nakayama's lemma 00DV (6)** for a family: a finite family `x` generates a finite `S`-module
`M` as soon as its reductions generate the fibre `M/IM` over `S/I`, for `I` inside the Jacobson
radical of `S`. -/
private theorem surjective_linearCombination_of_surjective_linearCombination_mkQ
    [Module.Finite S M] {I : Ideal S} (hI : I ≤ Ideal.jacobson ⊥) (x : ι → M)
    (hx : Function.Surjective (Fintype.linearCombination (S ⧸ I)
      fun i => (I • (⊤ : Submodule S M)).mkQ (x i))) :
    Function.Surjective (Fintype.linearCombination S x) := by
  refine LinearMap.surjective_of_surjective_comp_mkQ _ I hI fun z => ?_
  obtain ⟨c, hc⟩ := hx z
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := I) (c i)
  exact ⟨a, by rw [LinearMap.comp_apply, mkQ_linearCombination]; simpa [ha] using hc⟩

/-- If the reductions of a family `x` are linearly independent over `S/I`, then a combination
`∑ aᵢ xᵢ` lying in `IM` has all its coefficients in `I`. -/
private theorem mem_of_linearCombination_mem_smul_top {I : Ideal S} {x : ι → M}
    (hx : LinearIndependent (S ⧸ I) fun i => (I • (⊤ : Submodule S M)).mkQ (x i)) {a : ι → S}
    (ha : Fintype.linearCombination S x a ∈ I • (⊤ : Submodule S M)) (i : ι) : a i ∈ I := by
  rw [Fintype.linearIndependent_iff] at hx
  refine Ideal.Quotient.eq_zero_iff_mem.mp (hx (fun i => Ideal.Quotient.mk I (a i)) ?_ i)
  rw [← Fintype.linearCombination_apply, ← mkQ_linearCombination]
  simpa using ha

end Fibre

/-- **The heart of 00MH**, by the local criterion 00ME: for `M` flat over `R` and `S` a Noetherian
local ring over the local ring `R`, the map `S^ι → M` defined by a finite family `x` is injective
as soon as the reductions of the `x i` are linearly independent over the residue algebra `S/𝔪S`.

The relation `∑ aᵢ xᵢ ∈ 𝔪S • ⊤` puts every `aᵢ` in `𝔪S` by that independence, hence the tuple `a`
in `𝔪S • ⊤`, which is exactly injectivity of the fibre map that 00ME asks for. -/
private theorem injective_linearCombination_of_linearIndependent_mkQ {R S M ι : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat R M] [Fintype ι] {x : ι → M}
    (hx : LinearIndependent (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      fun i => (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M)).mkQ (x i)) :
    Function.Injective (Fintype.linearCombination S x) :=
  (injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
    (S := S) (N := ι → S) ((Fintype.linearCombination S x).restrictScalars R)
    (injective_mapQ_restrictScalars_of_forall_mem _ _ fun _ ha =>
      mem_smul_top_of_forall_mem fun i => mem_of_linearCombination_mem_smul_top hx ha i)).1

/-- A nonzero module over an `R`-algebra `S` that is `S`-linearly isomorphic to a product of copies
of `S` has `S` as a direct summand, so flatness over `R` descends from it to `S`. The product is
over a nonempty index type precisely because the module is nonzero. -/
private theorem flat_of_linearEquiv_pi {R S M ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Nontrivial M]
    [Module.Flat R M] (e : (ι → S) ≃ₗ[S] M) : Module.Flat R S := by
  classical
  have : Module.Flat R (ι → S) := Module.Flat.of_linearEquiv (e.restrictScalars R)
  rcases isEmpty_or_nonempty ι with h | h
  · exact absurd e.toEquiv.symm.subsingleton (not_subsingleton M)
  · obtain ⟨i⟩ := h
    exact Module.Flat.of_retract (LinearMap.single R (fun _ : ι => S) i) (LinearMap.proj i)
      (by ext s; simp)

@[nolint unusedArguments]
private theorem solution
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    [Nontrivial M] [Module.Flat R M]
    (hM : Module.Free (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (M ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S M))) :
    Module.Free S M ∧ Module.Flat R S := by
  classical
  set J : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  -- a basis of the fibre `M/𝔪M` over `S/𝔪S`, and a lift `x` of it to `M`
  set ι := Module.Free.ChooseBasisIndex (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M))
  have : Fintype ι := Module.Free.ChooseBasisIndex.fintype _ _
  set b := Module.Free.chooseBasis (S ⧸ J) (M ⧸ J • (⊤ : Submodule S M))
  choose x hx using fun i : ι => Submodule.Quotient.mk_surjective (J • (⊤ : Submodule S M)) (b i)
  have hxb : (fun i => (J • (⊤ : Submodule S M)).mkQ (x i)) = b := funext hx
  -- the map `S^ι → M` it defines is injective by 00ME and surjective by 00DV
  have hbij : Function.Bijective (Fintype.linearCombination S x) :=
    ⟨injective_linearCombination_of_linearIndependent_mkQ (by rw [hxb]; exact b.linearIndependent),
      surjective_linearCombination_of_surjective_linearCombination_mkQ
        ((map_maximalIdeal_le (algebraMap R S)).trans
          (jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top).ge) x
        (by rw [hxb]; exact surjective_linearCombination_basis b)⟩
  have e : (ι → S) ≃ₗ[S] M := LinearEquiv.ofBijective _ hbij
  exact ⟨Module.Free.of_equiv e, flat_of_linearEquiv_pi e⟩

end Stacks.Flatness.FreeFromFreeFibre

end

section

namespace Module.Flat

/-- **Stacks 00MH.** Let `R → S` be a local homomorphism of Noetherian local rings, let `𝔪` be the
maximal ideal of `R`, and let `M` be a nonzero finite `S`-module. If `M/𝔪M` is a free
`S/𝔪S`-module and `M` is flat over `R`, then `M` is free over `S` and `S` is flat over `R`.

Here `S/𝔪S` is the ring quotient `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and
`M/𝔪M` is the quotient `M ⧸ 𝔪S • (⊤ : Submodule S M)` with its canonical `S/𝔪S`-module structure;
see the module docstring. -/
@[stacks 00MH "\"Nonzero\" is `Nontrivial M`. The fibre ring is
`S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and `M/𝔪M` is
`M ⧸ 𝔪S • (⊤ : Submodule S M)`, whose `S/𝔪S`-module structure is
`Module.instQuotientIdealSubmoduleHSMulTop`. The two conclusions are conjoined, in the source's
order: `M` is free over `S`, `S` is flat over `R`. `IsNoetherianRing R` is unused but is part of
the tag's hypotheses; see the module docstring.", ega "0 10.1.3" "special case"]
theorem free_and_flat_of_free_maximalIdeal
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    [Nontrivial M] [Module.Flat R M]
    (hM : Module.Free (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (M ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S M))) :
    Module.Free S M ∧ Module.Flat R S :=
      Stacks.Flatness.FreeFromFreeFibre.solution hM

end Module.Flat

end

/-! ### Stacks 00MI -/

section


namespace Stacks.Flatness.LocalExactnessCriterion

open CategoryTheory Limits IsLocalRing TensorProduct

/-! ### Reduction modulo an ideal -/

section Fibre

variable {S : Type*} [CommRing S] (J : Ideal S) {M : Type*} [AddCommGroup M] [Module S M]

end Fibre

/-- Exactness at `i + 1` of a chain complex of modules is the equality of the kernel of the
outgoing differential with the range of the incoming one. -/
private lemma exactAt_succ_iff {S : Type*} [CommRing S] (C : ChainComplex (ModuleCat S) ℕ)
    (i : ℕ) : C.ExactAt (i + 1) ↔
      LinearMap.ker (C.d (i + 1) i).hom = LinearMap.range (C.d (i + 2) (i + 1)).hom := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact eq_comm

/-! ### The local criterion at one index of a complex -/

/-- **The local criterion 00ME at one index of a complex.** Let `R → S` be a local homomorphism of
local rings with `S` Noetherian, let `𝔪` be the maximal ideal of `R`, let `P →[g] N →[f] M` be a
complex of `S`-modules with `N` finite over `S` and `M` flat over `R`, and assume that
`f x ∈ 𝔪M` forces `x ∈ 𝔪N + g(P)`. Then `Ker f = Im g` and `M/f(N)` is flat over `R`.

This is 00ME applied to the map `u : N/g(P) → M` induced by `f`, whose reduction modulo `𝔪` is
injective by the hypothesis; `LinearMap.ker_eq_bot_range_liftQ_iff` turns the injectivity of `u`
into `Ker f = Im g`, and `Submodule.range_liftQ` identifies the two cokernels. -/
@[ega "0 10.2.4" "b ⇒ a", ega "IV 11.3.7" "(b) ⇒ (a), special case"]
theorem _root_.Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top
    {R S P N M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup P] [Module S P]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Flat R M]
    (g : P →ₗ[S] N) (f : N →ₗ[S] M) (hfg : f ∘ₗ g = 0)
    (hex : ∀ x : N, f x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M) →
      x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N) ⊔ LinearMap.range g) :
    LinearMap.ker f = LinearMap.range g ∧ Module.Flat R (M ⧸ LinearMap.range f) := by
  have hle : LinearMap.range g ≤ LinearMap.ker f := LinearMap.range_le_ker_iff.mpr hfg
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) ((Submodule.liftQ _ f hle).restrictScalars R)
      (Module.Flat.injective_mapQ_restrictScalars_of_forall_mem (S := S) _ _ fun q hq => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Stacks.Flatness.LocalCriterion.mk_mem_smul_top_iff _ _ x).mpr (hex x hq))
  have hinj' : Function.Injective (Submodule.liftQ (LinearMap.range g) f hle) := hinj
  rw [LinearMap.range_restrictScalars, Submodule.range_liftQ] at hflat
  exact ⟨(LinearMap.ker_eq_bot_range_liftQ_iff hle).mp (LinearMap.ker_eq_bot.mpr hinj'), hflat⟩

/-! ### Exactness of the reduced complex, read on elements -/

/-- Exactness at `i + 1` of the complex obtained from `C` by base change along `S → S/J`, read
elementwise: if `d_{i+1}x` lies in `J F_i` then `x` lies in `J F_{i+1} + d_{i+2}(F_{i+2})`. -/
private lemma mem_sup_range_of_exactAt {S : Type*} [CommRing S] (J : Ideal S)
    (C : ChainComplex (ModuleCat S) ℕ) (i : ℕ)
    (h : (((ModuleCat.extendScalars (Ideal.Quotient.mk J)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj C).ExactAt (i + 1))
    (x : C.X (i + 1)) (hx : (C.d (i + 1) i).hom x ∈ J • (⊤ : Submodule S (C.X i))) :
    x ∈ J • (⊤ : Submodule S (C.X (i + 1))) ⊔ LinearMap.range (C.d (i + 2) (i + 1)).hom := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at h
  obtain ⟨t, ht⟩ :=
    h ((1 : S ⧸ J) ⊗ₜ[S] x) ((TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J _).mpr hx)
  obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul J t
  have ht' : (1 : S ⧸ J) ⊗ₜ[S] ((C.d (i + 2) (i + 1)).hom y) = (1 : S ⧸ J) ⊗ₜ[S] x := ht
  refine Submodule.mem_sup.mpr
    ⟨_, ?_, _, LinearMap.mem_range_self (C.d (i + 2) (i + 1)).hom y, sub_add_cancel x _⟩
  rw [← TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J, TensorProduct.tmul_sub, ht', sub_self]

/-! ### Stacks 00MI -/


/-- **Stacks 00MI.** Let `R → S` be a local homomorphism of Noetherian local rings, let `𝔪` be the
maximal ideal of `R`, and let `0 → F_e → F_{e-1} → ⋯ → F_0` be a finite complex of finite
`S`-modules, presented as a chain complex `C` of `S`-modules with `C.X i = 0` for `i > e`. Assume
that every `F_i` is flat over `R` and that the reduced complex `0 → F_e/𝔪F_e → ⋯ → F_0/𝔪F_0` is
exact. Then `0 → F_e → ⋯ → F_0` is exact, and `Coker(F_1 → F_0)` is flat over `R`. -/
@[nolint unusedArguments]
private theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    (C : ChainComplex (ModuleCat.{max w v} S) ℕ) [∀ i, Module.Finite S (C.X i)] (e : ℕ)
    (_hC : ∀ i, e < i → IsZero (C.X i))
    (hflat : ∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (C.X i)))
    (hexact : ∀ i, 0 < i →
      (((ModuleCat.extendScalars
          (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).ExactAt i) :
    (∀ i, 0 < i → C.ExactAt i) ∧
      Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (cokernel (C.d 1 0))) := by
  let _ : ∀ i, Module R (C.X i) := fun i => Module.compHom _ (algebraMap R S)
  have : ∀ i, IsScalarTower R S (C.X i) := fun _ =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : ∀ i, Module.Flat R (C.X i) := hflat
  -- the criterion at index `i + 1`
  have key : ∀ i : ℕ, LinearMap.ker (C.d (i + 1) i).hom
      = LinearMap.range (C.d (i + 2) (i + 1)).hom ∧
      Module.Flat R (C.X i ⧸ LinearMap.range (C.d (i + 1) i).hom) := fun i =>
    Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top _ _
      (by rw [← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero])
      (mem_sup_range_of_exactAt _ C i (hexact (i + 1) i.succ_pos))
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact (exactAt_succ_iff C j).mpr (key j).1
  · have h0 : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S (C.X 0 ⧸ LinearMap.range (C.d 1 0).hom))) := (key 0).2
    exact Module.Flat.of_linearEquiv
      (((ModuleCat.restrictScalars (algebraMap R S)).mapIso
        (ModuleCat.cokernelIsoRangeQuotient (C.d 1 0))).toLinearEquiv)

end Stacks.Flatness.LocalExactnessCriterion

end

section


open CategoryTheory Limits IsLocalRing in
/-- **Stacks 00MI.** Let `R → S` be a local homomorphism of Noetherian local rings, let `𝔪` be the
maximal ideal of `R`, and let `0 → F_e → F_{e-1} → ⋯ → F_0` be a finite complex of finite
`S`-modules, presented as a chain complex `C` of `S`-modules with `C.X i = 0` for `i > e`. Assume
that every `F_i` is flat over `R` and that the reduced complex `0 → F_e/𝔪F_e → ⋯ → F_0/𝔪F_0` is
exact. Then `0 → F_e → ⋯ → F_0` is exact, and `Coker(F_1 → F_0)` is flat over `R`.

Reduction modulo `𝔪` is base change along `S → S/𝔪S`, `Coker(F_1 → F_0)` is the categorical
cokernel, and flatness over `R` is flatness after restricting scalars along `algebraMap R S`; see
the module docstring. -/
@[stacks 00MI "The complex is a `ChainComplex (ModuleCat S) ℕ` vanishing above `e`, as in 00N0, so
that `ExactAt e` is the leading `0 →`; exactness is assumed and concluded at every positive index,
which above `e` is automatic. `F_i/𝔪F_i` is the base change
`(S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) ⊗[S] F_i` of `ModuleCat.extendScalars`, applied
to `C` as a complex, and `Coker(F_1 → F_0)` is `cokernel (C.d 1 0)`. `IsNoetherianRing R` is
unused but is part of the tag's hypotheses; see the module docstring."]
theorem Module.Flat.exactAt_and_flat_cokernel_of_exactAt_maximalIdeal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R] [IsNoetherianRing S]
    (C : ChainComplex (ModuleCat.{max w v} S) ℕ) [∀ i, Module.Finite S (C.X i)] (e : ℕ)
    (hC : ∀ i, e < i → IsZero (C.X i))
    (hflat : ∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (C.X i)))
    (hexact : ∀ i, 0 < i →
      (((ModuleCat.extendScalars
          (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).ExactAt i) :
    (∀ i, 0 < i → C.ExactAt i) ∧
      Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (cokernel (C.d 1 0))) :=
        Stacks.Flatness.LocalExactnessCriterion.solution C e hC hflat hexact

end

end

end
