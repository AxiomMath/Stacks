module

public import StacksFrontier.RingTheory.Flat.EtaleLocalizationProjectiveBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleBaseChange
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleReductionInput
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibreAtPrime
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveClosedFibre
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveLocalBaseClause
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.UnramifiedIncomparable

/-!
# The étale-local reduction of 05IG

This file isolates the situation that the proof of [Stacks, Tag 05IG] reduces to, and proves the
tag's equivalence from it.

`Stacks.WeaklyAssociatedPrimes.Reduction` records the data the source's reduction produces out of
`R → S`, `N` and `𝔮`: a *local* ring `R₁`, an `R₁`-algebra `S₁` receiving `S`, a prime `𝔮₁` of
`S₁` over the maximal ideal of `R₁`, and an `S₁`-module `N₁` which is the base change of `N` and
which is **projective** over `R₁`, together with

* the two transport equivalences, saying that weak association of `𝔮₁` to `N₁ ⊗_R X` over `S₁` is
  weak association of its contraction to `N ⊗_R X` over `S`, and that weak association of the
  maximal ideal to `R₁ ⊗_R X` is weak association of `𝔭` to `X`;
* the *key observation* `Reduction.below`: a prime of `S₁` whose contraction is weakly associated
  to the fibre module contracts into `𝔮`.  This is what the choice of the element inverted before
  the structure theorem is for;
* `Reduction.incomparable`: two primes of `S₁` with the same contraction to `S` are incomparable,
  because `S₁` is unramified over a localization of `S`.

Granted such data the tag follows.  Writing `C` for the statement that `𝔮₁` is associated, in the
strict sense of [Stacks, Tag 00LA], to the closed fibre `N₁ / 𝔪₁ N₁` — a condition that does not
mention `X` — the file proves

* `Reduction.isAssociatedPrimeStacks_closedFibre`: `𝔮 ∈ WeakAss_S(N ⊗_R X)` implies `C`;
* `Reduction.isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks_closedFibre`: `𝔭 ∈ WeakAss_R(X)`
  and `C` imply `𝔮 ∈ WeakAss_S(N ⊗_R X)`;
* `Reduction.isWeaklyAssociatedPrime_base`: `𝔮 ∈ WeakAss_S(N ⊗_R X)` implies `𝔭 ∈ WeakAss_R(X)`.

Since `𝔭` is always weakly associated to `κ(𝔭)`, taking `X = κ(𝔭)` in the second statement turns
`C` into the fibre condition of the tag, and `Reduction.isWeaklyAssociatedPrime_tensorProduct_iff`
is the tag itself.

The two middle statements are the local-projective cases already proved:  the first is the fibre
clause `isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct`, the second is
`isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre`, whose maximality
hypothesis is supplied here by `below` together with `incomparable`.  The base clause is the
source's own argument:  a witness `z` with `𝔮` minimal over `Ann_S(z)` has nonzero image `z₁` in
`N₁ ⊗_R X` because `S → S₁` is flat, each `𝔭`-generator kills a power of `z₁` because the
elements of `S ∖ 𝔮` act regularly on the closed fibre — this is `below` again, through
[Stacks, Tag 05FR] — so the annihilator of `z₁` over `R₁` has radical `𝔪₁ = 𝔭 R₁`, and
projectivity of `N₁` splits off the tensor factor.

## Main definitions

* `Stacks.WeaklyAssociatedPrimes.Reduction`: the reduced situation.

## Main results

* `Stacks.WeaklyAssociatedPrimes.Reduction.isWeaklyAssociatedPrime_tensorProduct_iff`: the
  equivalence of [Stacks, Tag 05IG], granted a reduction.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 05FR](https://stacks.math.columbia.edu/tag/05FR)
* [Stacks Project, Tag 0CU6](https://stacks.math.columbia.edu/tag/0CU6)
* [Stacks Project, Tag 0CU7](https://stacks.math.columbia.edu/tag/0CU7)
-/

@[expose] public section

open TensorProduct

open IsLocalRing

universe u

namespace Stacks.WeaklyAssociatedPrimes

/-- **The situation the proof of [Stacks, Tag 05IG] reduces to.**

The rings `R₁` and `S₁` and the module `N₁` are the result of inverting an element of `S` outside
`𝔮`, performing the elementary étale localization of [Stacks, Tag 05ID], and localizing the base
at the chosen prime;  `ι` exhibits `N₁` as the base change of `N`, `q₁` is the resulting prime,
and the remaining fields are the properties of that situation which the proof of the tag uses. -/
structure Reduction (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] where
  /-- The local base. -/
  R₁ : Type u
  /-- The ring above the local base. -/
  S₁ : Type u
  /-- The module, projective over the local base. -/
  N₁ : Type u
  [commRingR₁ : CommRing R₁]
  [commRingS₁ : CommRing S₁]
  [addCommGroupN₁ : AddCommGroup N₁]
  [isLocalRingR₁ : IsLocalRing R₁]
  [algebraRR₁ : Algebra R R₁]
  [algebraR₁S₁ : Algebra R₁ S₁]
  [algebraSS₁ : Algebra S S₁]
  [algebraRS₁ : Algebra R S₁]
  [towerRR₁S₁ : IsScalarTower R R₁ S₁]
  [towerRSS₁ : IsScalarTower R S S₁]
  [moduleS₁N₁ : Module S₁ N₁]
  [moduleR₁N₁ : Module R₁ N₁]
  [moduleSN₁ : Module S N₁]
  [moduleRN₁ : Module R N₁]
  [towerR₁S₁N₁ : IsScalarTower R₁ S₁ N₁]
  [towerSS₁N₁ : IsScalarTower S S₁ N₁]
  [towerRS₁N₁ : IsScalarTower R S₁ N₁]
  [towerRR₁N₁ : IsScalarTower R R₁ N₁]
  [towerRSN₁ : IsScalarTower R S N₁]
  [projectiveN₁ : Module.Projective R₁ N₁]
  [finitePresentationN₁ : Module.FinitePresentation S₁ N₁]
  [flatS₁ : Module.Flat S S₁]
  [flatRN₁ : Module.Flat R N₁]
  [noetherianFibre :
    IsNoetherianRing (S₁ ⧸ Ideal.map (algebraMap R₁ S₁) (maximalIdeal R₁))]
  /-- `N₁` is the base change of `N` along `S → S₁`. -/
  ι : N →ₗ[S] N₁
  /-- `ι` exhibits `N₁` as a base change. -/
  isBaseChange_ι : IsBaseChange S₁ ι
  /-- The prime of `S₁`. -/
  q₁ : Ideal S₁
  [q₁_isPrime : q₁.IsPrime]
  /-- The maximal ideal of `R₁` is `𝔭 R₁`:  the lower horizontal map is unramified. -/
  map_eq_maximalIdeal : Ideal.map (algebraMap R R₁) p = maximalIdeal R₁
  /-- `q₁` contains the closed fibre ideal. -/
  map_maximalIdeal_le : Ideal.map (algebraMap R₁ S₁) (maximalIdeal R₁) ≤ q₁
  /-- `q₁` contracts to `q`. -/
  comap_q₁ : q₁.comap (algebraMap S S₁) = q
  /-- `R₁ → S₁` is essentially of finite presentation. -/
  essFP : (algebraMap R₁ S₁).EssentiallyOfFinitePresentation
  /-- Weak association of a prime of `S₁` to `N₁ ⊗_R X` is weak association of its contraction
  to `N ⊗_R X`:  [Stacks, Tag 05FP] and [Stacks, Tag 05C9]. -/
  transΦ : ∀ (s : Ideal S₁), s.IsPrime → ∀ (X : Type u) [AddCommGroup X] [Module R X],
    (IsWeaklyAssociatedPrime S₁ (N₁ ⊗[R] X) s ↔
      IsWeaklyAssociatedPrime S (N ⊗[R] X) (s.comap (algebraMap S S₁)))
  /-- Weak association of the maximal ideal of `R₁` to `R₁ ⊗_R X` is weak association of `𝔭`
  to `X`. -/
  transΨ : ∀ (X : Type u) [AddCommGroup X] [Module R X],
    (IsWeaklyAssociatedPrime R₁ (R₁ ⊗[R] X) (maximalIdeal R₁) ↔
      IsWeaklyAssociatedPrime R X p)
  /-- Two primes of `S₁` with the same contraction to `S` are incomparable. -/
  incomparable : ∀ s : Ideal S₁, s.IsPrime → q₁ ≤ s →
    s.comap (algebraMap S S₁) = q → s = q₁
  /-- **The key observation.**  A prime of `S₁` whose contraction to `S` is weakly associated to
  the fibre module contracts into `𝔮`. -/
  below : ∀ s : Ideal S₁, s.IsPrime →
    IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) (s.comap (algebraMap S S₁)) →
    s.comap (algebraMap S S₁) ≤ q

namespace Reduction

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {N : Type u} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]

attribute [instance] commRingR₁ commRingS₁ addCommGroupN₁ isLocalRingR₁ algebraRR₁ algebraR₁S₁
  algebraSS₁ algebraRS₁ towerRR₁S₁ towerRSS₁ moduleS₁N₁ moduleR₁N₁ moduleSN₁ moduleRN₁
  towerR₁S₁N₁ towerSS₁N₁ towerRS₁N₁ towerRR₁N₁ towerRSN₁ projectiveN₁ finitePresentationN₁ flatS₁
  flatRN₁ noetherianFibre q₁_isPrime

/-- The closed fibre ideal `𝔪₁ S₁`. -/
abbrev fibreIdeal' (D : Reduction R S N p q) : Ideal D.S₁ :=
  Ideal.map (algebraMap D.R₁ D.S₁) (maximalIdeal D.R₁)

/-- The closed fibre module `N₁ / 𝔪₁ N₁`. -/
abbrev closedFibre (D : Reduction R S N p q) : Type u :=
  D.N₁ ⧸ (D.fibreIdeal' • (⊤ : Submodule D.S₁ D.N₁))

/-- The module `N₁` is finite over `S₁`. -/
instance (D : Reduction R S N p q) : Module.Finite D.S₁ D.N₁ := inferInstance

/-- The module `N₁` is flat over `R₁`. -/
instance (D : Reduction R S N p q) : Module.Flat D.R₁ D.N₁ := Module.Flat.of_projective

/-- The closed fibre `N₁ / 𝔪₁ N₁` is finite over `S₁ / 𝔪₁ S₁`. -/
instance (D : Reduction R S N p q) :
    Module.Finite (D.S₁ ⧸ D.fibreIdeal') D.closedFibre :=
  Submodule.instFiniteQuotientIdealHSMulTop D.N₁ D.fibreIdeal'

/-- A scalar tower on the left factor passes to a tensor product. -/
theorem isScalarTower_tensorProduct_left
    {A B M X : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module R M] [SMulCommClass R A M] [SMulCommClass R B M]
    [AddCommGroup X] [Module R X] :
    IsScalarTower A B (M ⊗[R] X) := by
  refine IsScalarTower.of_algebraMap_smul fun a x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul m y =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul]
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

omit [q.IsPrime] [q.LiesOver p] in
/-- The closed fibre ideal is `𝔭 S₁`. -/
theorem fibreIdeal'_eq (D : Reduction R S N p q) :
    D.fibreIdeal' = Ideal.map (algebraMap R D.S₁) p := by
  rw [fibreIdeal', ← D.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R D.R₁ D.S₁]

/-- Cancelling the base change: `N₁ ⊗_{R₁} (R₁ ⊗_R X)` is `N₁ ⊗_R X`. -/
noncomputable def cancel (D : Reduction R S N p q) (X : Type u) [AddCommGroup X]
    [Module R X] :
    (D.N₁ ⊗[D.R₁] (D.R₁ ⊗[R] X)) ≃ₗ[D.S₁] (D.N₁ ⊗[R] X) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R D.R₁ D.S₁ D.N₁ X

/-- A prime associated to a module in the strict sense of [Stacks, Tag 00LA] is weakly associated
to it. -/
theorem isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks {A X : Type*} [CommRing A]
    [AddCommGroup X] [Module A X] {J : Ideal A} (h : IsAssociatedPrimeStacks A X J) :
    IsWeaklyAssociatedPrime A X J := by
  obtain ⟨hJ, w, hw⟩ := h
  refine ⟨w, ?_⟩
  have hann : (A ∙ w).annihilator = J := by
    rw [← hw, Submodule.bot_colon]
  rw [hann]
  exact ⟨⟨hJ, le_rfl⟩, fun _ h _ => h.2⟩

omit [q.IsPrime] [q.LiesOver p] in
/-- **The fibre clause.**  If `𝔮` is weakly associated to `N ⊗_R X` then `𝔮₁` is associated, in
the strict sense of [Stacks, Tag 00LA], to the closed fibre `N₁ / 𝔪₁ N₁`. -/
theorem isAssociatedPrimeStacks_closedFibre (D : Reduction R S N p q)
    (X : Type u) [AddCommGroup X] [Module R X]
    (h : IsWeaklyAssociatedPrime S (N ⊗[R] X) q) :
    IsAssociatedPrimeStacks D.S₁ D.closedFibre D.q₁ := by
  have h1 : IsWeaklyAssociatedPrime D.S₁ (D.N₁ ⊗[R] X) D.q₁ :=
    (D.transΦ D.q₁ inferInstance X).mpr (by rw [D.comap_q₁]; exact h)
  have h2 : IsWeaklyAssociatedPrime D.S₁ (D.N₁ ⊗[D.R₁] (D.R₁ ⊗[R] X)) D.q₁ :=
    isWeaklyAssociatedPrime_of_linearEquiv' (D.cancel X).symm h1
  exact isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct D.essFP
    D.map_maximalIdeal_le h2

omit [q.IsPrime] [q.LiesOver p] in
/-- A prime of `S₁` weakly associated to the closed fibre contracts into `𝔮`. -/
theorem comap_le_of_isWeaklyAssociatedPrime_closedFibre (D : Reduction R S N p q)
    (s : Ideal D.S₁) (hs : s.IsPrime)
    (h : IsWeaklyAssociatedPrime D.S₁ D.closedFibre s) :
    s.comap (algebraMap S D.S₁) ≤ q := by
  -- the closed fibre is `N₁ ⊗_R R/𝔭`, which embeds in `N₁ ⊗_R κ(𝔭)` because `N₁` is flat
  have he : D.closedFibre ≃ₗ[D.S₁] D.N₁ ⊗[R] (R ⧸ p) :=
    (Submodule.quotEquivOfEq _ _ (congrArg
        (fun I : Ideal D.S₁ => I • (⊤ : Submodule D.S₁ D.N₁)) D.fibreIdeal'_eq)) ≪≫ₗ
      _root_.Stacks.AssociatedPrimes.FlatBaseChange.quotSMulEquivTensorQuot p
  have hker : LinearMap.ker (Algebra.linearMap R p.ResidueField) = p :=
    Ideal.ext fun _ => Ideal.algebraMap_residueField_eq_zero
  have hinj := _root_.Stacks.AssociatedPrimes.FlatBaseChange.injective_map_id
    (S := D.S₁) (N := D.N₁)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot p _ hker.ge hker.le))
  have h2 : IsWeaklyAssociatedPrime D.S₁ (D.N₁ ⊗[R] p.ResidueField) s :=
    Module.weaklyAssociatedPrimes_subset_of_injective hinj
      (isWeaklyAssociatedPrime_of_linearEquiv' he h)
  exact D.below s hs ((D.transΦ s hs p.ResidueField).mp h2)

omit [q.IsPrime] [q.LiesOver p] in
/-- **Regularity of the scalars outside `𝔮` on the closed fibre.**  This is the key observation
`below` read through [Stacks, Tag 00LD]. -/
theorem isSMulRegular_closedFibre (D : Reduction R S N p q) (σ : S) (hσ : σ ∉ q) :
    IsSMulRegular D.closedFibre (algebraMap S D.S₁ σ) := by
  have hreg : IsSMulRegular D.closedFibre
      (Ideal.Quotient.mk D.fibreIdeal' (algebraMap S D.S₁ σ)) := by
    refine isSMulRegular_of_notMem_associatedPrimes _ fun r hr hmem => ?_
    have hrp : r.IsPrime := hr.1
    obtain ⟨-, w, hw⟩ := hr
    rw [← Submodule.colon_span, Submodule.bot_colon] at hw
    -- `r` is minimal over the annihilator of `w`, hence weakly associated
    have hwa : IsWeaklyAssociatedPrime (D.S₁ ⧸ D.fibreIdeal') D.closedFibre r := by
      refine ⟨w, ⟨⟨hrp, hw ▸ Ideal.le_radical⟩, fun J hJ _ => ?_⟩⟩
      intro x hx
      rw [hw] at hx
      obtain ⟨n, hn⟩ := hx
      exact hJ.1.mem_of_pow_mem n (hJ.2 hn)
    -- descend along the surjection `S₁ → S₁ / 𝔪₁ S₁`
    have hsurj : Function.Surjective (algebraMap D.S₁ (D.S₁ ⧸ D.fibreIdeal')) :=
      Ideal.Quotient.mk_surjective
    have h2 : IsWeaklyAssociatedPrime D.S₁ D.closedFibre
        (r.comap (algebraMap D.S₁ (D.S₁ ⧸ D.fibreIdeal'))) :=
      (isWeaklyAssociatedPrime_comap_iff_of_surjective hsurj r).mp hwa
    have hrcp : (r.comap (algebraMap D.S₁ (D.S₁ ⧸ D.fibreIdeal'))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle := D.comap_le_of_isWeaklyAssociatedPrime_closedFibre _ hrcp h2
    exact hσ (hle hmem)
  simpa only [IsSMulRegular, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using hreg

omit [q.IsPrime] [q.LiesOver p] in
/-- Multiplication by the image of a scalar outside `𝔮` is injective on `N₁ ⊗_R X`:
[Stacks, Tag 05FR]. -/
theorem smul_injective (D : Reduction R S N p q)
    (X : Type u) [AddCommGroup X] [Module R X] (σ : S) (hσ : σ ∉ q) :
    Function.Injective (fun z : D.N₁ ⊗[R] X => algebraMap S D.S₁ σ • z) := by
  have h := smul_injective_of_isSMulRegular_closedFibre (R := D.R₁) (S := D.S₁)
    (N := D.N₁) (M := D.R₁ ⊗[R] X) (algebraMap S D.S₁ σ) (D.isSMulRegular_closedFibre σ hσ)
  intro a b hab
  have hab' : algebraMap S D.S₁ σ • a = algebraMap S D.S₁ σ • b := hab
  have ha : (D.cancel X).symm a = (D.cancel X).symm b := by
    refine h ?_
    change algebraMap S D.S₁ σ • (D.cancel X).symm a = algebraMap S D.S₁ σ • (D.cancel X).symm b
    rw [← map_smul, ← map_smul, hab']
  simpa using congrArg (D.cancel X) ha

omit [q.IsPrime] [q.LiesOver p] in
/-- **The implication `⟸` of [Stacks, Tag 05IG], after the reduction.** -/
theorem isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks_closedFibre
    (D : Reduction R S N p q) (X : Type u) [AddCommGroup X] [Module R X]
    (hX : IsWeaklyAssociatedPrime R X p)
    (hC : IsAssociatedPrimeStacks D.S₁ D.closedFibre D.q₁) :
    IsWeaklyAssociatedPrime S (N ⊗[R] X) q := by
  have hM : IsWeaklyAssociatedPrime D.R₁ (D.R₁ ⊗[R] X) (maximalIdeal D.R₁) :=
    (D.transΨ X).mpr hX
  have hmax : ∀ s : Ideal D.S₁, IsAssociatedPrimeStacks D.S₁ D.closedFibre s →
      D.q₁ ≤ s → D.q₁ = s := by
    intro s hs hle
    have hsp : s.IsPrime := hs.1
    have hsq : s.comap (algebraMap S D.S₁) ≤ q :=
      D.comap_le_of_isWeaklyAssociatedPrime_closedFibre s hsp
        (isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks hs)
    have hqs : q ≤ s.comap (algebraMap S D.S₁) :=
      le_of_eq_of_le D.comap_q₁.symm (Ideal.comap_mono hle)
    exact (D.incomparable s hsp hle (le_antisymm hsq hqs)).symm
  have h1 : IsWeaklyAssociatedPrime D.S₁ (D.N₁ ⊗[D.R₁] (D.R₁ ⊗[R] X)) D.q₁ :=
    isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre D.essFP hM hC hmax
  have h2 : IsWeaklyAssociatedPrime D.S₁ (D.N₁ ⊗[R] X) D.q₁ :=
    isWeaklyAssociatedPrime_of_linearEquiv' (D.cancel X) h1
  have := (D.transΦ D.q₁ inferInstance X).mp h2
  rwa [D.comap_q₁] at this

omit [q.IsPrime] in
/-- **The base clause of [Stacks, Tag 05IG], after the reduction.**  No finiteness hypothesis on
`𝔭` is used. -/
theorem isWeaklyAssociatedPrime_base (D : Reduction R S N p q)
    (X : Type u) [AddCommGroup X] [Module R X]
    (h : IsWeaklyAssociatedPrime S (N ⊗[R] X) q) :
    IsWeaklyAssociatedPrime R X p := by
  obtain ⟨z, hz⟩ := h
  -- the base change of the witness
  let φ : (N ⊗[R] X) →ₗ[S] (D.N₁ ⊗[R] X) :=
    TensorProduct.AlgebraTensorModule.map D.ι (LinearMap.id : X →ₗ[R] X)
  have hφ : IsBaseChange D.S₁ φ :=
    isBaseChange_tensorProduct_map (R := R) (P := X) _ D.isBaseChange_ι
  have hzne : φ z ≠ 0 :=
    ne_zero_of_isBaseChange_of_annihilator_le φ hφ
      (Ideal.IsPrime.ne_top D.q₁_isPrime) (by rw [D.comap_q₁]; exact hz.1.2)
  -- the maximal ideal of `R₁` is in the radical of the annihilator of the image
  have htowRR₁ : IsScalarTower R D.R₁ (D.N₁ ⊗[R] X) :=
    isScalarTower_tensorProduct_left (A := R) (B := D.R₁) (M := D.N₁) (X := X)
  have htowRS : IsScalarTower R S (D.N₁ ⊗[R] X) :=
    isScalarTower_tensorProduct_left (A := R) (B := S) (M := D.N₁) (X := X)
  have htowSS₁ : IsScalarTower S D.S₁ (D.N₁ ⊗[R] X) :=
    isScalarTower_tensorProduct_left (A := S) (B := D.S₁) (M := D.N₁) (X := X)
  have hrad : ∀ ρ ∈ p, ∃ n : ℕ, (algebraMap R D.R₁ ρ) ^ n • φ z = 0 := by
    intro ρ hρ
    have h1 : q.comap (algebraMap R S) = p := (q.over_def p).symm
    have hρq : algebraMap R S ρ ∈ q := Ideal.mem_comap.mp (h1.ge hρ)
    obtain ⟨σ, hσ, n, hσn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hz hρq
    rw [Submodule.mem_annihilator_span_singleton] at hσn
    refine ⟨n, ?_⟩
    refine D.smul_injective X σ hσ ?_
    change algebraMap S D.S₁ σ • ((algebraMap R D.R₁ ρ) ^ n • φ z)
      = algebraMap S D.S₁ σ • (0 : D.N₁ ⊗[R] X)
    rw [smul_zero]
    have hA : ∀ y : D.N₁ ⊗[R] X, algebraMap S D.S₁ σ • y = σ • y := fun y =>
      IsScalarTower.algebraMap_smul D.S₁ σ y
    have hB : ∀ y : D.N₁ ⊗[R] X,
        (algebraMap R D.R₁ ρ) ^ n • y = (algebraMap R S ρ) ^ n • y := by
      intro y
      rw [← map_pow, ← map_pow, IsScalarTower.algebraMap_smul D.R₁,
        IsScalarTower.algebraMap_smul S]
    rw [hA, hB, ← mul_smul, ← map_smul φ, hσn, map_zero]
  have hann : (D.R₁ ∙ φ z).annihilator ≤ maximalIdeal D.R₁ := by
    refine le_maximalIdeal fun htop => hzne ?_
    have h1 : (1 : D.R₁) ∈ (D.R₁ ∙ φ z).annihilator := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact h1
  have hmem : IsWeaklyAssociatedPrime D.R₁ (D.N₁ ⊗[R] X) (maximalIdeal D.R₁) := by
    refine ⟨φ z, minimalPrimes_of_radical_condition _ _ inferInstance hann ?_⟩
    intro a ha
    rw [← D.map_eq_maximalIdeal] at ha
    have hsub : Ideal.map (algebraMap R D.R₁) p
        ≤ ((D.R₁ ∙ φ z).annihilator).radical := by
      rw [Ideal.map_le_iff_le_comap]
      intro ρ hρ
      obtain ⟨n, hn⟩ := hrad ρ hρ
      exact ⟨n, by simpa [Submodule.mem_annihilator_span_singleton] using hn⟩
    obtain ⟨n, hn⟩ := hsub ha
    refine ⟨1, ?_, n, by simpa using hn⟩
    intro h1
    exact (maximalIdeal.isMaximal D.R₁).ne_top
      ((maximalIdeal D.R₁).eq_top_iff_one.mpr h1)
  have hmem' : IsWeaklyAssociatedPrime D.R₁ (D.N₁ ⊗[D.R₁] (D.R₁ ⊗[R] X))
      (maximalIdeal D.R₁) :=
    isWeaklyAssociatedPrime_of_linearEquiv' ((D.cancel X).symm.restrictScalars D.R₁) hmem
  exact (D.transΨ X).mp (isWeaklyAssociatedPrime_of_tensorProduct_projective hmem')

omit [q.IsPrime] in
/-- **[Stacks, Tag 05IG], granted a reduction.**  A prime `𝔮` of `S` lying over `𝔭` is weakly
associated to `N ⊗_R X` exactly when `𝔭` is weakly associated to `X` and `𝔮` is weakly associated
to the fibre module `N ⊗_R κ(𝔭)`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff (D : Reduction R S N p q)
    (X : Type u) [AddCommGroup X] [Module R X] :
    IsWeaklyAssociatedPrime S (N ⊗[R] X) q ↔
      IsWeaklyAssociatedPrime R X p ∧
        IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) q := by
  have hκ : IsWeaklyAssociatedPrime R p.ResidueField p := by
    refine isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks ⟨inferInstance, 1, ?_⟩
    ext a
    rw [Submodule.bot_colon, Submodule.mem_annihilator_span_singleton, Algebra.smul_def, mul_one]
    exact Ideal.algebraMap_residueField_eq_zero
  refine ⟨fun h => ⟨D.isWeaklyAssociatedPrime_base X h, ?_⟩, fun h => ?_⟩
  · exact D.isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks_closedFibre p.ResidueField hκ
      (D.isAssociatedPrimeStacks_closedFibre X h)
  · exact D.isWeaklyAssociatedPrime_of_isAssociatedPrimeStacks_closedFibre X h.1
      (D.isAssociatedPrimeStacks_closedFibre p.ResidueField h.2)

end Reduction

end Stacks.WeaklyAssociatedPrimes

end
