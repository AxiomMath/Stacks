module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Flat.LocalCriteria
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# A variant of the local criterion for flatness

Let `R → S` be a local homomorphism of Noetherian local rings, let `I ⊊ R` be an ideal of `R`
and let `M` be a finite `S`-module, viewed as an `R`-module by restriction of scalars. This file
proves Stacks 00ML: if `Tor₁^R(M, R/I) = 0` and `M/IM` is flat over `R/I`, then `M` is flat
over `R`. By Remark 00M6 the first hypothesis says exactly that `I ⊗_R M → R ⊗_R M` is
injective, and that is the form in which it is stated here.

## Main results

* `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient`: Stacks 00ML.

## Implementation notes

The proof is the source's, with the deduction of `Tor₁^R(κ, M) = 0` and the appeal to the local
criterion 00MK replaced by a single Artin–Rees argument, so that neither 00MK nor the
faithful flatness of the `𝔪S`-adic completion is needed.

Write `K = ker(M ⊗_R J → M)` for an ideal `J ⊆ R`. There are two halves.

* *The two hypotheses control every ideal containing a power of `I`.* Stacks 051C says that they
  force `Tor₁^R(Q, M) = 0` for every `R`-module `Q` annihilated by a power of `I`; the
  `Tor`-vanishing is used here in the second slot and in the concrete shape that the canonical
  free presentation `(M →₀ R) ↠ M` of `M` stays left exact after tensoring with `Q`.
  `Stacks.Flatness.LocalCriterionVariant.tor2_of_smul_eq_bot` is the case where `I` itself
  annihilates `Q`: it is the snake-lemma reduction `lemmaC_reduction_tor` of Tag 051I applied to
  that presentation, whose input is the first-slot statement `tor_vanishing_Jkilled_first_slot`.
  `Stacks.Flatness.LocalCriterionVariant.tor2_of_submodule` is the two-out-of-three property
  coming from the right exactness of `Q ↦ X ⊗_R Q` together with the flatness of the free module
  `M →₀ R`, and `Stacks.Flatness.LocalCriterionVariant.tor2_of_annihilated` is the resulting
  induction on the exponent.
  `Stacks.Flatness.LocalCriterionVariant.lTensor_subtype_injective_of_quotient_annihilated` turns
  the conclusion back into injectivity of `M ⊗_R P → M ⊗_R Fr` for a submodule `P ≤ Fr` with
  `Fr/P` annihilated by a power of `I`, again by `lemmaC_reduction_tor`.
* *Artin–Rees.* Fix `n` and let `L = I^{n+c}`, where `c` is the Artin–Rees constant of `I` and
  `J` from `Ideal.exists_pow_inf_eq_pow_smul`. The map `J → R/L` has image a submodule `P` of
  `R/L`, and `R/L` — hence `(R/L)/P` — is annihilated by `L`, so `M ⊗_R P → M ⊗_R (R/L)` is
  injective by the previous half. An element of `K` therefore dies already in `M ⊗_R P`, hence
  comes from `M ⊗_R (J ∩ L)` by right exactness, hence lies in `Iⁿ(M ⊗_R J)` because
  `J ∩ L ⊆ Iⁿ J` by Artin–Rees. As `M ⊗_R J` is a finite `S`-module, `I ⊆ 𝔪_R` and `R → S` is
  local, Krull's intersection theorem over `S`
  (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) gives `K = 0`.

Tensor products are written with `M` on the left, `M ⊗_R J`, so that the `S`-action coming from
`M` is the one `TensorProduct.leftModule` provides and Krull's theorem can be applied over `S`;
`LinearMap.lTensor_inj_iff_rTensor_inj` converts to the `rTensor` form in which the statement and
`Module.Flat.iff_rTensor_injective'` are phrased.

## References

* [StacksProject 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [StacksProject 051C](https://stacks.math.columbia.edu/tag/051C)
* [StacksProject 00M6](https://stacks.math.columbia.edu/tag/00M6)
-/

universe u v w x
open TensorProduct

namespace Ideal

/-- **Injectivity of `I ⊗_R N → N` passes to the ideal `IA` of an `R`-algebra `A`**, for `N` an
`A`-module.

No hypothesis on `A` beyond being an `R`-algebra is needed. The comparison
`σ : ↥I ⊗[R] N → ↥(IA) ⊗[A] N`, `i ⊗ n ↦ (algebraMap i) ⊗ n`, is surjective, because `IA` is
generated over `A` by the image of `I` and `(a • x) ⊗ n = x ⊗ (a • n)` over `A`; and the
multiplication `↥(IA) ⊗[A] N → N` composed with `σ` is the multiplication `↥I ⊗[R] N → N`. A
surjection followed by a map whose composite is injective has the second map injective.

`σ` is built with `TensorProduct.liftAddHom` rather than `TensorProduct.lift`, since `↥(IA) ⊗[A] N`
carries no `R`-module structure. -/
public theorem rTensor_subtype_map_injective {R : Type*} [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] (I : Ideal R)
    (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (h : Function.Injective (LinearMap.rTensor N I.subtype)) :
    Function.Injective (LinearMap.rTensor N (I.map (algebraMap R A)).subtype) := by
  have hb : ∀ (r : R) (i : ↥I) (n : N),
      (Algebra.idealMap A I (r • i)) ⊗ₜ[A] n = (Algebra.idealMap A I i) ⊗ₜ[A] (r • n) := by
    intro r i n
    rw [map_smul, ← IsScalarTower.algebraMap_smul A r (Algebra.idealMap A I i),
      TensorProduct.smul_tmul, IsScalarTower.algebraMap_smul]
  set σ : ↥I ⊗[R] N →+ ↥(I.map (algebraMap R A)) ⊗[A] N :=
    TensorProduct.liftAddHom
      { toFun := fun i => (TensorProduct.mk A _ N (Algebra.idealMap A I i)).toAddMonoidHom
        map_zero' := by ext n; simp
        map_add' := fun i j => by ext n; simp }
      hb with hσ
  have hσt : ∀ (i : ↥I) (n : N), σ (i ⊗ₜ[R] n) = (Algebra.idealMap A I i) ⊗ₜ[A] n := fun i n => rfl
  have hgen : ∀ (a : A) (ha : a ∈ I.map (algebraMap R A)) (n : N),
      ∃ w, σ w = (⟨a, ha⟩ : ↥(I.map (algebraMap R A))) ⊗ₜ[A] n := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact fun n => ⟨(⟨r, hr⟩ : ↥I) ⊗ₜ[R] n, by rw [hσt]; rfl⟩
    | zero => exact fun n => ⟨0, by rw [map_zero]; exact (TensorProduct.zero_tmul _ n).symm⟩
    | add x y hx hy ihx ihy =>
        intro n
        obtain ⟨w₁, h₁⟩ := ihx n
        obtain ⟨w₂, h₂⟩ := ihy n
        exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, ← TensorProduct.add_tmul]; rfl⟩
    | smul c x hx ih =>
        intro n
        obtain ⟨w, hw⟩ := ih (c • n)
        exact ⟨w, by rw [hw]; exact (TensorProduct.smul_tmul _ _ _).symm⟩
  have hsurj : Function.Surjective σ := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x n => exact hgen x.1 x.2 n
    | add u v hu hv =>
        obtain ⟨w₁, h₁⟩ := hu
        obtain ⟨w₂, h₂⟩ := hv
        exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂]⟩
  have hcomp : ∀ w : ↥I ⊗[R] N,
      (TensorProduct.lid A N) (LinearMap.rTensor N (I.map (algebraMap R A)).subtype (σ w))
        = (TensorProduct.lid R N) (LinearMap.rTensor N I.subtype w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul i n =>
        rw [hσt]
        simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        exact algebraMap_smul A (i : R) n
    | add u v hu hv => simp only [map_add, hu, hv]
  have hφ : Function.Injective
      (fun z : ↥I ⊗[R] N => (TensorProduct.lid R N) (LinearMap.rTensor N I.subtype z)) :=
    (TensorProduct.lid R N).injective.comp h
  intro u v huv
  obtain ⟨u', rfl⟩ := hsurj u
  obtain ⟨v', rfl⟩ := hsurj v
  refine congrArg σ (hφ ?_)
  change (TensorProduct.lid R N) (LinearMap.rTensor N I.subtype u')
    = (TensorProduct.lid R N) (LinearMap.rTensor N I.subtype v')
  rw [← hcomp, ← hcomp, huv]

end Ideal

namespace Stacks.Flatness.LocalCriterionVariant

variable {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- The injectivity of `I ⊗_R M → R ⊗_R M` in the equivalent form `I ⊗_R M → M`. -/
private theorem lift_lsmul_injective_of_rTensor_injective (I : Ideal R)
    (htor : Function.Injective (LinearMap.rTensor M I.subtype)) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) := by
  have heq :
    (TensorProduct.lid R M).toLinearMap.comp (LinearMap.rTensor M I.subtype) =
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype) := by
    apply TensorProduct.ext'; intro j n; simp
  rw [← heq, LinearMap.coe_comp]
  exact (TensorProduct.lid R M).injective.comp htor

/-- `Tor₁^R(M, Q) = 0` for an `R`-module `Q` annihilated by `I`, in the concrete form that the
canonical free presentation of `M` stays left exact after tensoring with `Q`. -/
private theorem tor2_of_smul_eq_bot (I : Ideal R)
    (hquot : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor : Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)))
    {Q : Type x} [AddCommGroup Q] [Module R Q] (hQ : I • (⊤ : Submodule R Q) = ⊥) :
    Function.Injective
      (LinearMap.rTensor Q
        (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype) := by
  have hfirst :
    Function.Injective
      (LinearMap.rTensor M (LinearMap.ker (Finsupp.linearCombination R (id : Q → Q))).subtype) :=
    tor_vanishing_Jkilled_first_slot I hquot htor hQ
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact
    lemmaC_reduction_tor (Finsupp.linearCombination R (id : M → M))
      (Finsupp.linearCombination_id_surjective R M) _ (Submodule.subtype_injective _)
      (LinearMap.exact_subtype_ker_map (Finsupp.linearCombination R (id : M → M))) Q hfirst

/-- Two out of three for the vanishing of `Tor₁^R(M, -)`: if it vanishes on a submodule `P` of
`Q` and on `Q/P`, it vanishes on `Q`. -/
private theorem tor2_of_submodule {Q : Type x} [AddCommGroup Q] [Module R Q] (P : Submodule R Q)
    (hP :
      Function.Injective
        (LinearMap.rTensor ↥P (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype))
    (hQP :
      Function.Injective
        (LinearMap.rTensor (Q ⧸ P)
          (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype)) :
    Function.Injective
      (LinearMap.rTensor Q
        (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype) := by
  set K : Submodule R (M →₀ R) := LinearMap.ker (Finsupp.linearCombination R (id : M → M)) with hK
  have hsqQ :
    (LinearMap.lTensor (M →₀ R) P.mkQ) ∘ₗ (LinearMap.rTensor Q K.subtype) =
      (LinearMap.rTensor (Q ⧸ P) K.subtype) ∘ₗ (LinearMap.lTensor ↥K P.mkQ) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hsqP :
    (LinearMap.lTensor (M →₀ R) P.subtype) ∘ₗ (LinearMap.rTensor ↥P K.subtype) =
      (LinearMap.rTensor Q K.subtype) ∘ₗ (LinearMap.lTensor ↥K P.subtype) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hFinj : Function.Injective (LinearMap.lTensor (M →₀ R) P.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap P.subtype P.subtype_injective
  have hex : Function.Exact (LinearMap.lTensor ↥K P.subtype) (LinearMap.lTensor ↥K P.mkQ) :=
    lTensor_exact ↥K (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective
  have main : ∀ z : ↥K ⊗[R] Q, LinearMap.rTensor Q K.subtype z = 0 → z = 0 := by
    intro z hz
    have h1 : LinearMap.lTensor ↥K P.mkQ z = 0 := by
      apply hQP
      rw [map_zero, ← LinearMap.comp_apply, ← hsqQ, LinearMap.comp_apply, hz, map_zero]
    obtain ⟨y, hy⟩ := (hex z).mp h1
    have h3 : LinearMap.rTensor ↥P K.subtype y = 0 := by
      apply hFinj
      rw [map_zero, ← LinearMap.comp_apply, hsqP, LinearMap.comp_apply, hy, hz]
    have h4 : y = 0 := hP (by rw [h3, map_zero])
    rw [← hy, h4, map_zero]
  intro a b hab
  exact sub_eq_zero.mp (main (a - b) (by rw [map_sub, hab, sub_self]))

/-- **Stacks 051C (2).** `Tor₁^R(M, Q) = 0` for every `R`-module `Q` annihilated by a power
of `I`. -/
private theorem tor2_of_annihilated (I : Ideal R)
    (hquot : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor : Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)))
    (Q : Type x) [AddCommGroup Q] [Module R Q] (m : ℕ) (hQ : (I ^ m) • (⊤ : Submodule R Q) = ⊥) :
    Function.Injective
      (LinearMap.rTensor Q
        (LinearMap.ker (Finsupp.linearCombination R (id : M → M))).subtype) := by
  induction m generalizing Q with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hQ
    have hz : ∀ y : Q, y = 0 := by
      intro y
      have hy : y ∈ (⊤ : Submodule R Q) := Submodule.mem_top
      rw [hQ, Submodule.mem_bot] at hy
      exact hy
    have hall :
      ∀ t : ↥(LinearMap.ker (Finsupp.linearCombination R (id : M → M))) ⊗[R] Q, t = 0 := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a q => rw [hz q, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    intro a b _
    rw [hall a, hall b]
  | succ k ih =>
    set P : Submodule R Q := I • (⊤ : Submodule R Q) with hPdef
    have hkP : I ^ k • P = ⊥ := by
      rw [hPdef, smul_smul, ← pow_succ]
      exact hQ
    have hPtop : (I ^ k) • (⊤ : Submodule R ↥P) = ⊥ := by
      have hmap : Submodule.map P.subtype ((I ^ k) • (⊤ : Submodule R ↥P)) = I ^ k • P := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      have hinj : Function.Injective (Submodule.map P.subtype) :=
        Submodule.map_injective_of_injective Subtype.coe_injective
      apply hinj
      rw [Submodule.map_bot, hmap, hkP]
    have hQkill : I • (⊤ : Submodule R (Q ⧸ P)) = ⊥ := by
      have hmap :
        I • (⊤ : Submodule R (Q ⧸ P)) = Submodule.map P.mkQ (I • (⊤ : Submodule R Q)) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      rw [hmap, ← hPdef, Submodule.mkQ_map_self]
    exact tor2_of_submodule P (ih ↥P hPtop) (tor2_of_smul_eq_bot I hquot htor hQkill)

/-- If the quotient `Fr/P` is annihilated by a power of `I`, then `M ⊗_R P → M ⊗_R Fr` is
injective. -/
private theorem lTensor_subtype_injective_of_quotient_annihilated (I : Ideal R)
    (hquot : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (htor : Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)))
    {Fr : Type x} [AddCommGroup Fr] [Module R Fr] (P : Submodule R Fr) (m : ℕ)
    (h : (I ^ m) • (⊤ : Submodule R (Fr ⧸ P)) = ⊥) :
    Function.Injective (LinearMap.lTensor M P.subtype) :=
  lemmaC_reduction_tor P.mkQ P.mkQ_surjective P.subtype P.subtype_injective
    (LinearMap.exact_subtype_mkQ P) M (tor2_of_annihilated I hquot htor (Fr ⧸ P) m h)

/-- An ideal annihilates the quotient of the ring by it. -/
private theorem smul_top_quotient_self (A : Ideal R) : A • (⊤ : Submodule R (R ⧸ A)) = ⊥ := by
  calc
    A • (⊤ : Submodule R (R ⧸ A)) = A • Submodule.map A.mkQ (⊤ : Submodule R R) := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    _ = Submodule.map A.mkQ (A • (⊤ : Submodule R R)) := by rw [Submodule.map_smul'']
    _ = Submodule.map A.mkQ A := by simp
    _ = ⊥ := A.mkQ_map_self

/-- What annihilates a module annihilates each of its quotients. -/
private theorem smul_top_quotient_of_smul_top {A : Ideal R} {X : Type x} [AddCommGroup X]
    [Module R X] (hX : A • (⊤ : Submodule R X) = ⊥) (P : Submodule R X) :
    A • (⊤ : Submodule R (X ⧸ P)) = ⊥ := by
  calc
    A • (⊤ : Submodule R (X ⧸ P)) = A • Submodule.map P.mkQ (⊤ : Submodule R X) := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    _ = Submodule.map P.mkQ (A • (⊤ : Submodule R X)) := by rw [Submodule.map_smul'']
    _ = ⊥ := by rw [hX, Submodule.map_bot]

/-- The image of `M ⊗_R N → M ⊗_R J` lies in `K · (M ⊗_R J)` for a submodule `N` of `J` whose
elements lie in `KJ`: such an element is a sum of products `r • b` with `r ∈ K` and `b ∈ J`,
and `m ⊗ (r • b) = r • (m ⊗ b)`. -/
private theorem lTensor_range_subtype_le_smul_top {J : Ideal R} (K : Ideal R) (N : Submodule R ↥J)
    (hN : N ≤ Submodule.comap J.subtype (K • (J : Submodule R R))) :
    LinearMap.range (LinearMap.lTensor M N.subtype) ≤ K • (⊤ : Submodule R (M ⊗[R] ↥J)) := by
  have hP : Submodule.map J.subtype (K • (⊤ : Submodule R ↥J)) = K • (J : Submodule R R) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hsub : Submodule.comap J.subtype (K • (J : Submodule R R)) ≤ K • (⊤ : Submodule R ↥J) := by
    rw [← hP, Submodule.comap_map_eq_of_injective Subtype.val_injective]
  have key :
    ∀ (m : M) (y : ↥J),
      y ∈ K • (⊤ : Submodule R ↥J) → m ⊗ₜ[R] y ∈ K • (⊤ : Submodule R (M ⊗[R] ↥J)) := by
    intro m y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z _
      rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro y z hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul m y => simpa using key m _ (hsub (hN y.2))
  | add u v hu hv =>
    rw [map_add]; exact Submodule.add_mem _ hu hv

end Stacks.Flatness.LocalCriterionVariant
