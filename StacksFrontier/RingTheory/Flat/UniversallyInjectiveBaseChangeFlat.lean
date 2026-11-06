module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Fibres.AssociatedPrimesCover
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveBaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveLocalize

/-!
# Universal injectivity of a flat base change over an arbitrary base

Let `R → S` be of finite presentation, let `N` be a finitely presented `S`-module which is flat
over `R`, and let `S → S'` be flat. If the image of `Spec(S') → Spec(S)` contains every
associated prime of every fibre `N ⊗[R] κ(p)` of `N`, then the canonical map `N → N ⊗[S] S'` is
universally injective over `R`. This is Stacks 05DH, the globalisation of the local statement
Stacks 05DG.

## Main results

* `Stacks.UniversalInjectivity.universallyInjective_baseChange_of_flat`: Stacks 05DH.

## Implementation notes

The proof is the stalkwise criterion of Stacks 05CL
(`Stacks.UniversalInjectivity.LocalizationCriteria.universallyInjective_of_localizedMapRp`): it
  suffices to prove universal
injectivity of the localized map `N_q → (N ⊗[S] S')_q` over `R_p`, with `p = q.under R`, for
every prime `q` of `S`. Over the local base `R_p` this is Stacks 05DG
(`universallyInjectivePoly_tensorUnit_of_flat`), applied to `R_p → S_q`, the module `N_q` and
the flat `S_q`-algebra `S'_q = Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)`. Its
hypotheses over `R_p` are supplied by
`StacksFrontier/RingTheory/Flat/UniversallyInjectiveLocalize.lean`, except for the essential finite
presentation of `R_p → S_q`, which is obtained by exhibiting `S_q` as a localization of
`R_p ⊗[R] S`.

What has to be done by hand is the translation of the hypothesis. Stacks 05DG asks for primes of
`S_q` over the maximal ideal of `R_p` which are associated to the closed fibre
`N_q / 𝔪_{R_p} N_q`, whereas Stacks 05DH speaks of primes of `S` associated to the full fibre
`N ⊗[R] κ(p)`. The passage between the two factors through the fibre ring `A = κ(p) ⊗[R] S` of
`Ideal.Fiber`: the closed fibre ring `S_q ⧸ 𝔪_{R_p} S_q` is identified `S`-algebra-isomorphically
with the local ring `A_{q'}` of `A` at the prime `q'` corresponding to `q` under
`PrimeSpectrum.primesOverOrderIsoFiber`, and the closed-fibre module with the localization of
`A ⊗[S] N ≃ N ⊗[R] κ(p)` at `q'`. An associated prime of that localization contracts to an
associated prime of `A ⊗[S] N` by Stacks 0310 (2), which applies because `A` is of finite type
over the field `κ(p)`, hence Noetherian.

That descent step is stated for Mathlib's `associatedPrimes`, whose defining condition on the
annihilator of an element is only required up to radical, while 05DH and 05DG are stated with
`IsAssociatedPrimeStacks`, which requires the annihilator itself to equal the prime. The two
private comparison lemmas below bridge this: one direction is unconditional, and the converse
holds over a Noetherian ring, which is exactly where it is used.

## References

* [Stacks Project, Tag 05DH](https://stacks.math.columbia.edu/tag/05DH)
* [Stacks Project, Tag 05DG](https://stacks.math.columbia.edu/tag/05DG)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Stacks.UniversalInjectivity

/-! ### Comparison with Mathlib's associated primes -/

/-- Over a Noetherian ring an associated prime in the sense of Mathlib's `associatedPrimes` is a
strict associated prime in the sense of Stacks 00LA: Noetherianity makes the annihilator of the
witnessing element equal to the prime, not merely cofinal with it. -/
private lemma isAssociatedPrimeStacks_of_mem_associatedPrimes {A M : Type*} [CommRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] {p : Ideal A}
    (h : p ∈ associatedPrimes A M) : IsAssociatedPrimeStacks A M p := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨hp, x, hx⟩ := h
  exact ⟨hp, x, by simpa only [Submodule.colon_span] using hx.symm⟩

/-- A linear equivalence matches up the annihilators of corresponding elements. -/
private lemma colon_span_singleton_congr {A M M' : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') (x : M) :
    (⊥ : Submodule A M').colon (Submodule.span A {e x}) =
      (⊥ : Submodule A M).colon (Submodule.span A {x}) := by
  ext a
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  rw [← map_smul, map_eq_zero_iff _ e.injective]

/-- Being a strict associated prime is invariant under a linear equivalence of modules. -/
private lemma isAssociatedPrimeStacks_congr {A M M' : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M') {p : Ideal A} :
    IsAssociatedPrimeStacks A M p ↔ IsAssociatedPrimeStacks A M' p := by
  constructor
  · rintro ⟨hp, x, hx⟩
    exact ⟨hp, e x, (colon_span_singleton_congr e x).trans hx⟩
  · rintro ⟨hp, x, hx⟩
    exact ⟨hp, e.symm x, (colon_span_singleton_congr e.symm x).trans hx⟩

/-- A strict associated prime pulls back along a ring map `f : A →+* B` whenever the `A`-action on
`M` is the restriction along `f` of the `B`-action. -/
private lemma isAssociatedPrimeStacks_comap {A B M : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] [Module B M] (f : A →+* B)
    (hf : ∀ (a : A) (x : M), a • x = f a • x)
    {p : Ideal B} (h : IsAssociatedPrimeStacks B M p) :
    IsAssociatedPrimeStacks A M (p.comap f) := by
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp.comap f, x, ?_⟩
  ext a
  rw [Ideal.mem_comap, ← hx, Submodule.mem_colon_span_singleton, Submodule.mem_bot,
    Submodule.mem_colon_span_singleton, Submodule.mem_bot, hf]

/-! ### The data of Stacks 05DG over the local ring at a prime -/

/-- The canonical map `R_p → S_q` attached to a prime `q` of `S` with `p = q.under R` is
essentially of finite presentation as soon as `R → S` is of finite presentation: `S_q` is a
localization of the finitely presented `R_p`-algebra `R_p ⊗[R] S`. -/
@[ega "IV 1.3.10" "partial"]
private lemma essentiallyOfFinitePresentation_atPrime {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] :
    (algebraMap (Localization.AtPrime (q.under R))
      (Localization.AtPrime q)).EssentiallyOfFinitePresentation := by
  classical
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let C := Rp ⊗[R] S
  let : Algebra.FinitePresentation Rp C := Algebra.FinitePresentation.baseChange Rp
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) C :=
    IsLocalization.tensorRight Rp p.primeCompl
  let φ : C →ₐ[Rp] Sq :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp Sq) (IsScalarTower.toAlgHom R S Sq)
      fun _ _ ↦ Commute.all _ _
  let : Algebra C Sq := φ.toRingHom.toAlgebra
  let : IsScalarTower S C Sq := IsScalarTower.of_algebraMap_eq fun s ↦ by
    show _ = φ (1 ⊗ₜ s)
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  let : IsScalarTower Rp C Sq := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact fun hx ↦ hr (Ideal.mem_comap.mp hx)
  let : IsLocalization (Submonoid.map (algebraMap S C) q.primeCompl) Sq :=
    IsLocalization.isLocalization_of_submonoid_le (S := C) (T := Sq)
      (M := Algebra.algebraMapSubmonoid S p.primeCompl) (N := q.primeCompl) hle
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := C)
    (Submonoid.map (algebraMap S C) q.primeCompl)

/-- Associated primes of `N ⊗[R] κ(P)` depend only on the prime `P`, not on how it is written. -/
private lemma isAssociatedPrimeStacks_residueField_congr
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (P₁ P₂ : Ideal R) [P₁.IsPrime] [P₂.IsPrime] (q : Ideal S) (h : P₁ = P₂) :
    IsAssociatedPrimeStacks S (N ⊗[R] P₁.ResidueField) q ↔
      IsAssociatedPrimeStacks S (N ⊗[R] P₂.ResidueField) q := by
  subst h
  rfl

set_option maxHeartbeats 400000 in
open Module.associatedPrimes in
/-- The hypothesis of Stacks 05DG over the local base `R_p`, in the presence of an `S`-algebra
`A` playing the role of the fibre `κ(p) ⊗[R] S`.

Let `q` be a prime of `S`, let `p = q.under R`, and suppose given a Noetherian `S`-algebra `A`
with a prime `qA` over `q` such that `A ⊗[S] N` is the fibre `N ⊗[R] κ(p)` and the local ring
`A_{qA}` is the closed fibre `S_q ⧸ 𝔪_{R_p} S_q`. A prime `r` of `S_q` over the maximal ideal of
`R_p` which is associated to the closed-fibre module transports to an associated prime of the
localization of `A ⊗[S] N` at `qA`, which contracts to an associated prime of `A ⊗[S] N` by
Stacks 0310 (2) and hence to a prime `q₀ ⊆ q` of `S` associated to the fibre `N ⊗[R] κ(p)`. The
hypothesis supplies a prime of `S'` over `q₀`, and its extension to `S'_q` contracts to `r`. -/
private lemma exists_isPrime_comap_eq_of_algEquiv_closedFibre
    {R : Type u} {S : Type v} {S' N : Type w} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup N] [Module S N] [Algebra R S] [Algebra S S'] [Module R N]
    [IsScalarTower R S N]
    (himage : ∀ (q : Ideal S) [q.IsPrime],
      IsAssociatedPrimeStacks S (N ⊗[R] (q.under R).ResidueField) q →
        ∃ q' : Ideal S', q'.IsPrime ∧ q'.under S = q)
    (q : Ideal S) [q.IsPrime] {A : Type*} [CommRing A] [Algebra S A] [IsNoetherianRing A]
    (qA : Ideal A) [qA.IsPrime] (hqA : qA.under S = q)
    (eFibre : A ⊗[S] N ≃ₗ[S] N ⊗[R] (q.under R).ResidueField)
    (eClosed : Localization.AtPrime qA ≃ₐ[S] (Localization.AtPrime q ⧸
      Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
        (maximalIdeal (Localization.AtPrime (q.under R)))))
    (r : Ideal (Localization.AtPrime q))
    (hr : Ideal.comap (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) r =
      maximalIdeal (Localization.AtPrime (q.under R)))
    (hassoc : IsAssociatedPrimeStacks (Localization.AtPrime q)
      (LocalizedModule q.primeCompl N ⧸
        (Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
            (maximalIdeal (Localization.AtPrime (q.under R))) •
          (⊤ : Submodule (Localization.AtPrime q) (LocalizedModule q.primeCompl N)))) r) :
    ∃ r' : Ideal (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)), r'.IsPrime ∧
      Ideal.comap (algebraMap (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) r' = r := by
  classical
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let S'q := Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)
  let Nq := LocalizedModule q.primeCompl N
  let IS : Ideal Sq := Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)
  let : r.IsPrime := hassoc.1
  let Aq := Localization.AtPrime qA
  let BS := Sq ⧸ IS
  let : Algebra A Aq := inferInstance
  let : IsScalarTower S A Aq := inferInstance
  -- The fibre module and its localization at `qA`.
  let M := A ⊗[S] N
  let locM := LocalizedModule qA.primeCompl M
  let : IsScalarTower S A locM := inferInstance
  let : IsScalarTower A Aq locM := inferInstance
  let : IsScalarTower S Aq locM := IsScalarTower.to₁₃₄ S A Aq locM
  let eLocM : Aq ⊗[A] M ≃ₗ[Aq] locM :=
    (IsLocalizedModule.isBaseChange qA.primeCompl Aq
      (LocalizedModule.mkLinearMap qA.primeCompl M)).equiv
  let eCancel : Aq ⊗[A] M ≃ₗ[Aq] Aq ⊗[S] N := by
    let : IsScalarTower S Aq Aq := IsScalarTower.of_algebraMap_smul
      (R := S) (A := Aq) (M := Aq) fun s x ↦ by simp [Algebra.smul_def]
    let : IsScalarTower A Aq Aq := IsScalarTower.of_algebraMap_smul
      (R := A) (A := Aq) (M := Aq) fun a x ↦ (Algebra.smul_def a x).symm
    exact TensorProduct.AlgebraTensorModule.cancelBaseChange
      (R := S) (A := A) (B := Aq) (M := Aq) (N := N)
  -- Transport the associated prime `r` from the closed fibre of `N_q` to `locM`.
  let eQuot : (BS ⊗[Sq] Nq) ≃ₗ[Sq] (Nq ⧸ (IS • (⊤ : Submodule Sq Nq))) :=
    TensorProduct.quotTensorEquivQuotSMul Nq IS
  have hT : IsAssociatedPrimeStacks Sq (BS ⊗[Sq] Nq) r :=
    (isAssociatedPrimeStacks_congr eQuot).mpr hassoc
  have hISle : IS ≤ r := by
    show Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp) ≤ r
    rw [Ideal.map_le_iff_le_comap, hr]
  let rBS : Ideal BS := Ideal.map (Ideal.Quotient.mk IS) r
  have hrBS : rBS.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hISle
  have hrBSunder : rBS.comap (Ideal.Quotient.mk IS) = r := Ideal.comap_map_mk hISle
  let : Module BS (BS ⊗[Sq] Nq) := TensorProduct.leftModule
  have hBS : IsAssociatedPrimeStacks BS (BS ⊗[Sq] Nq) rBS := by
    obtain ⟨-, y, hy⟩ := hT
    refine ⟨hrBS, y, ?_⟩
    ext b
    rw [Submodule.colon_span, Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hy' : s ∈ r ↔ s • y = 0 :=
      Iff.of_eq (by simpa only [Submodule.mem_colon_span_singleton, Submodule.mem_bot] using
        (congrArg (fun I : Ideal Sq ↦ s ∈ I) hy).symm)
    rw [← Ideal.mem_comap, hrBSunder]
    show (algebraMap Sq BS s) • y = 0 ↔ s ∈ r
    rw [IsScalarTower.algebraMap_smul]
    exact hy'.symm
  let : Module BS locM := Module.compHom locM (eClosed.symm : BS →+* Aq)
  let : IsScalarTower S BS locM := IsScalarTower.of_algebraMap_smul
    (R := S) (A := BS) (M := locM) fun s x ↦ by
      rw [MulAction.compHom_smul_def]
      have h1 : eClosed.symm (algebraMap S BS s) = algebraMap S Aq s := by
        rw [← eClosed.commutes s, eClosed.symm_apply_apply]
      exact (congrArg (fun a : Aq ↦ a • x) h1).trans
        (IsScalarTower.algebraMap_smul (R := S) (A := Aq) (M := locM) s x)
  let eQ₁ : (BS ⊗[Sq] Nq) ≃ₗ[Sq] BS ⊗[Sq] (Sq ⊗[S] N) :=
    TensorProduct.congr (LinearEquiv.refl Sq BS)
      ((IsLocalizedModule.isBaseChange q.primeCompl Sq
        (LocalizedModule.mkLinearMap q.primeCompl N)).equiv.symm)
  let eQ₂ : (BS ⊗[Sq] (Sq ⊗[S] N)) ≃ₗ[BS] BS ⊗[S] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq BS BS N
  let eQ₃ : (BS ⊗[S] N) ≃ₗ[S] Aq ⊗[S] N :=
    TensorProduct.congr eClosed.symm.toLinearEquiv (LinearEquiv.refl S N)
  let eQ : (BS ⊗[Sq] Nq) ≃ₗ[S] locM :=
    (eQ₁.restrictScalars S).trans ((eQ₂.restrictScalars S).trans
      (eQ₃.trans ((eCancel.symm.restrictScalars S).trans (eLocM.restrictScalars S))))
  have hQ₁ (b : BS) (x : BS ⊗[Sq] Nq) : eQ₁ (b • x) = b • eQ₁ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul c n => simp [eQ₁, TensorProduct.smul_tmul']
  have hQ₃ (b : BS) (x : BS ⊗[S] N) : eQ₃ (b • x) = eClosed.symm b • eQ₃ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul c n => simp [eQ₃, TensorProduct.smul_tmul']
  have heQ (b : BS) (x : BS ⊗[Sq] Nq) : eQ (b • x) = eClosed.symm b • eQ x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul b' n =>
      show eLocM (eCancel.symm (eQ₃ (eQ₂ (eQ₁ (b • (b' ⊗ₜ[Sq] n)))))) =
        eClosed.symm b • eLocM (eCancel.symm (eQ₃ (eQ₂ (eQ₁ (b' ⊗ₜ[Sq] n)))))
      rw [hQ₁ b, eQ₂.map_smul, hQ₃ b, ← eLocM.map_smul, ← eCancel.symm.map_smul]
  have hLocBS : IsAssociatedPrimeStacks BS locM rBS := by
    obtain ⟨hp', x, hx⟩ := hBS
    refine ⟨hp', eQ x, ?_⟩
    rw [← hx]
    ext b
    rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot,
      Submodule.mem_colon_span_singleton, Submodule.mem_bot,
      show (b • eQ x = 0) = (eQ (b • x) = 0) from congrArg (· = 0) (heQ b x).symm,
      eQ.map_eq_zero_iff]
  let pA : Ideal Aq := Ideal.comap (eClosed : Aq →+* BS) rBS
  have hLocAq : IsAssociatedPrimeStacks Aq locM pA :=
    isAssociatedPrimeStacks_comap (eClosed : Aq →+* BS) (fun a x ↦ by
      change a • x = eClosed.symm (eClosed a) • x
      rw [eClosed.symm_apply_apply]) hLocBS
  -- Stacks 0310 (2): descend the associated prime along the localization at `qA`.
  let p0 : Ideal A := Ideal.comap (algebraMap A Aq) pA
  have hA0 : IsAssociatedPrimeStacks A M p0 :=
    isAssociatedPrimeStacks_of_mem_associatedPrimes
      (comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
        (R := A) (R' := Aq) (M := M) (M' := locM) qA.primeCompl
        (LocalizedModule.mkLinearMap qA.primeCompl M) pA
        (Stacks.Divisors.mem_associatedPrimes_of_isAssociatedPrimeStacks hLocAq)
        ((isNoetherianRing_iff_ideal_fg A).mp ‹IsNoetherianRing A› _))
  let q0 : Ideal S := Ideal.comap (algebraMap S A) p0
  have hq0 : IsAssociatedPrimeStacks S M q0 :=
    isAssociatedPrimeStacks_comap (algebraMap S A)
      (fun s x ↦ (IsScalarTower.algebraMap_smul A s x).symm) hA0
  have hq0N : IsAssociatedPrimeStacks S (N ⊗[R] (q.under R).ResidueField) q0 :=
    (isAssociatedPrimeStacks_congr eFibre).mp hq0
  have hq0le : q0 ≤ q := by
    dsimp only [q0, p0, pA]
    calc Ideal.comap (algebraMap S A) (Ideal.comap (algebraMap A Aq)
          (Ideal.comap (eClosed : Aq →+* BS) rBS))
        ≤ Ideal.comap (algebraMap S A) (Ideal.comap (algebraMap A Aq) (maximalIdeal Aq)) :=
          Ideal.comap_mono (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hLocAq.1.ne_top))
      _ = q := by
          rw [show Ideal.comap (algebraMap A Aq) (maximalIdeal Aq) = qA from
            Localization.AtPrime.under_maximalIdeal (I := qA)]
          exact hqA
  have hq0r : q0 = r.under S := by
    have : IsScalarTower S Sq BS := inferInstance
    rw [Ideal.under_def]
    dsimp only [q0, p0, pA, rBS]
    ext s
    show eClosed (algebraMap A Aq (algebraMap S A s)) ∈ Ideal.map (Ideal.Quotient.mk IS) r ↔
      (algebraMap S Sq) s ∈ r
    have hscalar : eClosed (algebraMap A Aq (algebraMap S A s)) =
        (Ideal.Quotient.mk IS) ((algebraMap S Sq) s) :=
      (congrArg eClosed (IsScalarTower.algebraMap_apply S A Aq s)).trans (eClosed.commutes s)
    rw [hscalar, ← Ideal.mem_comap, hrBSunder]
  have hq0underR : q0.under R = p := by
    rw [hq0r]
    show Ideal.comap (algebraMap R S) (Ideal.comap (algebraMap S Sq) r) = p
    rw [Ideal.comap_comap,
      show (algebraMap S Sq).comp (algebraMap R S) = algebraMap R Sq from
        IsScalarTower.algebraMap_eq R S Sq]
    calc Ideal.comap (algebraMap R Sq) r
        = Ideal.comap (algebraMap R Rp) (Ideal.comap (algebraMap Rp Sq) r) := by
          rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq R Rp Sq]
      _ = Ideal.comap (algebraMap R Rp) (maximalIdeal Rp) := by rw [hr]
      _ = p := Localization.AtPrime.under_maximalIdeal (I := p)
  have hq0Fibre : IsAssociatedPrimeStacks S (N ⊗[R] (q0.under R).ResidueField) q0 := by
    exact (isAssociatedPrimeStacks_residueField_congr (S := S) (N := N) _ _ q0
      hq0underR.symm).mp hq0N
  let : q0.IsPrime := hq0.1
  -- Lift `q0` to `S'` and push the lift into `S'_q`.
  obtain ⟨q0', hq0', hq0eq⟩ := himage q0 hq0Fibre
  have hdisjoint : Disjoint (Algebra.algebraMapSubmonoid S' q.primeCompl : Set S')
      (q0' : Set S') := by
    rw [Set.disjoint_left]
    rintro x ⟨s, hs, rfl⟩ hx
    exact hs (hq0le (hq0eq ▸ Ideal.mem_comap.mpr hx))
  refine ⟨Ideal.map (algebraMap S' S'q) q0',
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S' q.primeCompl) S'q q0' hq0' hdisjoint, ?_⟩
  apply (IsLocalization.orderEmbedding q.primeCompl Sq).injective
  show Ideal.comap (algebraMap S Sq)
    (Ideal.comap (algebraMap Sq S'q) (Ideal.map (algebraMap S' S'q) q0')) =
    Ideal.comap (algebraMap S Sq) r
  rw [Ideal.comap_comap,
    show (algebraMap Sq S'q).comp (algebraMap S Sq) = algebraMap S S'q from
      (IsScalarTower.algebraMap_eq S Sq S'q).symm,
    ← show (algebraMap S' S'q).comp (algebraMap S S') = algebraMap S S'q from
      IsScalarTower.algebraMap_eq S S' S'q,
    ← Ideal.comap_comap,
    show Ideal.comap (algebraMap S' S'q) (Ideal.map (algebraMap S' S'q) q0') = q0' from
      IsLocalization.under_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid S' q.primeCompl) S'q hq0' hdisjoint]
  exact hq0eq.trans hq0r

/-- The hypothesis of Stacks 05DG over the local base `R_p`, deduced from the hypothesis of
Stacks 05DH over `R`.

The `S`-algebra that `exists_isPrime_comap_eq_of_algEquiv_closedFibre` asks for is the fibre
ring `A = κ(p) ⊗[R] S` of `Ideal.Fiber`, which is Noetherian because it is of finite type over
the field `κ(p)`. The prime of `A` over `q` is the one `PrimeSpectrum.primesOverOrderIsoFiber`
attaches to `q`, and the identification of `A_{qA}` with the closed fibre `S_q ⧸ 𝔪_{R_p} S_q`
runs through `Ideal.Fiber.algEquivAux₁`: both are localizations of `S ⧸ pS`, the first at the
image of that prime and the second at the image of `q`, and the two images agree. -/
private lemma exists_isPrime_comap_eq_of_isAssociatedPrimeStacks_closedFibre
    {R : Type u} {S : Type v} {S' N : Type w} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup N] [Module S N] [Algebra R S] [Algebra S S'] [Module R N]
    [IsScalarTower R S N] [Algebra.FinitePresentation R S]
    (himage : ∀ (q : Ideal S) [q.IsPrime],
      IsAssociatedPrimeStacks S (N ⊗[R] (q.under R).ResidueField) q →
        ∃ q' : Ideal S', q'.IsPrime ∧ q'.under S = q)
    (q : Ideal S) [hq : q.IsPrime]
    (r : Ideal (Localization.AtPrime q))
    (hr : Ideal.comap (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) r =
      maximalIdeal (Localization.AtPrime (q.under R)))
    (hassoc : IsAssociatedPrimeStacks (Localization.AtPrime q)
      (LocalizedModule q.primeCompl N ⧸
        (Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
            (maximalIdeal (Localization.AtPrime (q.under R))) •
          (⊤ : Submodule (Localization.AtPrime q) (LocalizedModule q.primeCompl N)))) r) :
    ∃ r' : Ideal (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)), r'.IsPrime ∧
      Ideal.comap (algebraMap (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) r' = r := by
  classical
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let IS : Ideal Sq := Ideal.map (algebraMap Rp Sq) (maximalIdeal Rp)
  -- The prime of the fibre ring `A = κ(p) ⊗[R] S` corresponding to `q`.
  have hqOver : q ∈ p.primesOver S := ⟨hq, ⟨rfl⟩⟩
  let qF : PrimeSpectrum (p.Fiber S) :=
    PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, hqOver⟩
  have hqF : qF.asIdeal.comap Algebra.TensorProduct.includeRight = q := by
    have h' := RelIso.symm_apply_apply
      (PrimeSpectrum.primesOverOrderIsoFiber R S p) (⟨q, hqOver⟩ : p.primesOver S)
    change (PrimeSpectrum.primesOverOrderIsoFiber R S p).symm qF = _ at h'
    simpa only [PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply] using
      congrArg Subtype.val h'
  let Aq := Localization.AtPrime qF.asIdeal
  let sFiber := qF.asIdeal.comap Algebra.TensorProduct.includeRight
  let : sFiber.LiesOver p := ⟨by
    show p = (qF.asIdeal.comap Algebra.TensorProduct.includeRight).under R
    rw [hqF]⟩
  -- `S_q` is also the localization of `S` at `sFiber`, which `hqF` identifies with `q`.
  let Tq := Localization.AtPrime sFiber
  let : Algebra Rp Tq := Localization.AtPrime.algebraOfLiesOver p sFiber
  let : Localization.AtPrime.IsLiesOverAlgebra p sFiber := inferInstance
  have hcompl : Submonoid.map (RingEquiv.refl S) q.primeCompl = sFiber.primeCompl := by
    ext x
    simp [sFiber, hqF]
  let : IsLocalization q.primeCompl Tq :=
    IsLocalization.of_ringEquiv_left (RingEquiv.refl S) hcompl fun _ ↦ rfl
  let eTqSq : Tq ≃ₐ[S] Sq := IsLocalization.algEquiv q.primeCompl Tq Sq
  -- The two closed-fibre rings `T_q ⧸ p T_q` and `S_q ⧸ 𝔪_{R_p} S_q` agree.
  let IT : Ideal Tq := (p.map (algebraMap R S)).map (algebraMap S Tq)
  have hK : IS = (p.map (algebraMap R S)).map (algebraMap S Sq) := by
    dsimp only [IS]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hIS : p.map (algebraMap R Sq) = (p.map (algebraMap R S)).map (algebraMap S Sq) := by
    rw [Ideal.map_map]
    congr 1
  have hprime : p.map (algebraMap R Sq) = IT.map (eTqSq : Tq →+* Sq) := by
    show p.map (algebraMap R Sq) =
      ((p.map (algebraMap R S)).map (algebraMap S Tq)).map (eTqSq : Tq →+* Sq)
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    simp [IsScalarTower.algebraMap_apply R S Sq]
  have hIJ : IS = IT.map (eTqSq : Tq →+* Sq) := hK.trans (hIS.symm.trans hprime)
  let BT := Tq ⧸ IT
  let BS := Sq ⧸ IS
  let eB : BT ≃ₐ[S] BS := Ideal.quotientEquivAlg IT IS eTqSq hIJ
  -- The fibre ring and its localization at `qF`.
  let K := p.ResidueField
  let A := p.Fiber S
  let : Algebra K A := Algebra.TensorProduct.leftAlgebra
  let : Algebra S A := Algebra.TensorProduct.rightAlgebra
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pS := p.map (algebraMap R S)
  let SpS := S ⧸ pS
  let e₁ : A ≃ₐ[S] Sp ⧸ pS.map (algebraMap S Sp) := by
    simpa [pS] using Ideal.Fiber.algEquivAux₁ (R := R) (S := S) p
  let q' : Ideal (Sp ⧸ pS.map (algebraMap S Sp)) := qF.asIdeal.comap e₁.symm
  have hunder : qF.asIdeal.under S = sFiber := rfl
  have : (q'.under SpS).LiesOver (qF.asIdeal.under S) :=
    Ideal.under_liesOver_of_liesOver SpS q' (qF.asIdeal.under S)
  have hpc : Algebra.algebraMapSubmonoid SpS sFiber.primeCompl = (q'.under SpS).primeCompl := by
    simpa [hunder] using Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (q'.under SpS) (qF.asIdeal.under S) Ideal.Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid SpS sFiber.primeCompl)
      (Localization.AtPrime q') := by
    rw [hpc]
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid SpS (Algebra.algebraMapSubmonoid S p.primeCompl))
      (Localization.AtPrime q') q'
  have := IsScalarTower.to₁₃₄ R S SpS (Localization.AtPrime q')
  have := IsScalarTower.to₁₃₄ R S SpS BT
  let eLocq' : Localization.AtPrime q' ≃ₐ[S] Aq :=
    Localization.localAlgEquiv q' qF.asIdeal e₁.symm rfl
  let eQuotq' : Localization.AtPrime q' ≃ₐ[SpS] BT :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid SpS sFiber.primeCompl) _ _
  let eClosed : Aq ≃ₐ[S] BS :=
    (eLocq'.symm.trans (eQuotq'.restrictScalars S)).trans eB
  let : Algebra.FinitePresentation K A := Algebra.FinitePresentation.baseChange K
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_finitePresentation
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  -- `A ⊗[S] N` is the fibre `N ⊗[R] κ(p)`.
  let eFibre : A ⊗[S] N ≃ₗ[S] N ⊗[R] K :=
    ((TensorProduct.comm S A N).trans (TensorProduct.congr (LinearEquiv.refl S N)
      (Algebra.TensorProduct.commRight R S K).symm.toLinearEquiv)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K)
  exact exists_isPrime_comap_eq_of_algEquiv_closedFibre himage q qF.asIdeal
    (by rw [Ideal.under_def]; exact hqF) eFibre eClosed r hr hassoc

/-- The stalkwise criterion of Stacks 05CL is fed by Stacks 05DG through the canonical
identification of `(N ⊗[S] S')_q` with `N_q ⊗[S_q] S'_q`, which matches the localization at `q`
of the base-change map `N → N ⊗[S] S'` with the base-change map of `N_q` along `S_q → S'_q`. -/
private lemma universallyInjective_localizedMapRp_of_tensorUnit
    {R : Type u} {S : Type v} {S' N : Type w} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup N] [Module S N] [Algebra R S] [Algebra S S'] (q : Ideal S) [q.IsPrime]
    (hloc : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
      (((TensorProduct.mk (Localization.AtPrime q) (LocalizedModule q.primeCompl N)
          (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))).flip
        1).restrictScalars (Localization.AtPrime (q.under R)))) :
    Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
      (Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapRp (R := R) ((TensorProduct.mk S
        N S').flip 1) q) := by
  classical
  let f : N →ₗ[S] N ⊗[S] S' := (TensorProduct.mk S N S').flip 1
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let S'q := Localization (Algebra.algebraMapSubmonoid S' q.primeCompl)
  let Nq := LocalizedModule q.primeCompl N
  -- Identify `(N ⊗[S] S')_q` with `N_q ⊗[S_q] S'_q` compatibly with the maps out of `N_q`.
  let eN : (Sq ⊗[S] N) ≃ₗ[Sq] Nq :=
    (IsLocalizedModule.isBaseChange q.primeCompl Sq
      (LocalizedModule.mkLinearMap q.primeCompl N)).equiv
  let eSq : (Sq ⊗[S] S') ≃ₐ[Sq] S'q := Localization.tensorRightAlgEquiv q.primeCompl S'
  let eT : (Sq ⊗[S] (N ⊗[S] S')) ≃ₗ[Sq] LocalizedModule q.primeCompl (N ⊗[S] S') :=
    (IsLocalizedModule.isBaseChange q.primeCompl Sq
      (LocalizedModule.mkLinearMap q.primeCompl (N ⊗[S] S'))).equiv
  let eDist : Sq ⊗[S] (N ⊗[S] S') ≃ₗ[Sq] (Sq ⊗[S] N) ⊗[Sq] (Sq ⊗[S] S') :=
    TensorProduct.AlgebraTensorModule.distribBaseChange S Sq N S'
  let eTarget : LocalizedModule q.primeCompl (N ⊗[S] S') ≃ₗ[Sq] (Nq ⊗[Sq] S'q) :=
    eT.symm.trans (eDist.trans (TensorProduct.congr eN eSq.toLinearEquiv))
  let fLoc : Nq →ₗ[Sq] LocalizedModule q.primeCompl (N ⊗[S] S') :=
    LocalizedModule.map q.primeCompl f
  let fLocal : Nq →ₗ[Sq] Nq ⊗[Sq] S'q := (TensorProduct.mk Sq Nq S'q).flip 1
  have hbridge : eTarget.toLinearMap ∘ₗ fLoc = fLocal := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h n s =>
      have hsL : LocalizedModule.mk (n ⊗ₜ[S] (1 : S')) s =
          Localization.mk (1 : S) s • LocalizedModule.mk (n ⊗ₜ[S] (1 : S')) 1 := by
        simpa using (LocalizedModule.mk_smul_mk (r := (1 : S))
          (m := n ⊗ₜ[S] (1 : S')) (s := s) (t := (1 : q.primeCompl))).symm
      have hsR : LocalizedModule.mk n s =
          Localization.mk (1 : S) s • LocalizedModule.mk n 1 := by
        simpa using (LocalizedModule.mk_smul_mk (r := (1 : S))
          (m := n) (s := s) (t := (1 : q.primeCompl))).symm
      show eTarget (LocalizedModule.map q.primeCompl f (LocalizedModule.mk n s)) =
        fLocal (LocalizedModule.mk n s)
      rw [LocalizedModule.map_mk]
      show eTarget (LocalizedModule.mk (n ⊗ₜ[S] (1 : S')) s) =
        (LocalizedModule.mk n s) ⊗ₜ[Sq] (1 : S'q)
      rw [hsL, hsR]
      simp only [map_smul]
      have hbase : eTarget (LocalizedModule.mk (n ⊗ₜ[S] (1 : S')) 1) =
          (LocalizedModule.mk n 1) ⊗ₜ[Sq] (1 : S'q) := by
        have heT : eT.symm (LocalizedModule.mk (n ⊗ₜ[S] (1 : S')) 1) =
            (Localization.mk (1 : S) (1 : q.primeCompl) : Sq) ⊗ₜ[S] (n ⊗ₜ[S] (1 : S')) :=
          LocalizedModule.equivTensorProduct_apply_mk (S := q.primeCompl) (M := N ⊗[S] S')
            (x := n ⊗ₜ[S] (1 : S')) (s := (1 : q.primeCompl))
        have heSqone : eSq ((1 : Sq) ⊗ₜ[S] (1 : S')) = (1 : S'q) := map_one eSq
        simp [eTarget, eDist, eN, heT, heSqone, Localization.mk_one]
      rw [hbase]
      exact TensorProduct.smul_tmul' (Localization.mk (1 : S) s)
        (LocalizedModule.mk n (1 : q.primeCompl)) (1 : S'q)
  show Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective
    (Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapRp f q)
  intro Q _ _
  have hnat : ((eTarget.restrictScalars Rp).rTensor Q).toLinearMap ∘ₗ
      ((fLoc.restrictScalars Rp).rTensor Q) = (fLocal.restrictScalars Rp).rTensor Q := by
    ext x y
    show (eTarget.toLinearMap ∘ₗ fLoc) x ⊗ₜ[Rp] y = fLocal x ⊗ₜ[Rp] y
    rw [hbridge]
  have hcoe : Function.Injective
      (((eTarget.restrictScalars Rp).rTensor Q).toLinearMap ∘ₗ
        ((fLoc.restrictScalars Rp).rTensor Q)) := by
    rw [hnat]
    exact hloc Q
  simp only [LinearMap.coe_comp] at hcoe
  exact hcoe.of_comp

/-! ### Stacks 05DH -/

/-- **Stacks 05DH.** Under the stated finite-presentation and flatness hypotheses, if every
associated prime of each fibre of `N` lifts to `S'`, then the canonical base-change map
`N → N ⊗[S] S'` is universally injective over `R`. -/
@[stacks 05DH]
theorem universallyInjective_baseChange_of_flat
    {R : Type u} {S : Type v} {S' N : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup N] [Module S N] [Algebra R S] [Algebra S S']
    [Module R N] [IsScalarTower R S N] [Algebra R S'] [IsScalarTower R S S']
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N]
    [Module.Flat R N] [Module.Flat S S']
    (himage : ∀ (q : Ideal S) [q.IsPrime],
      IsAssociatedPrimeStacks S (N ⊗[R] (q.under R).ResidueField) q →
        ∃ q' : Ideal S', q'.IsPrime ∧ q'.under S = q) :
    UniversallyInjective
      (((TensorProduct.mk S N S').flip 1).restrictScalars R) := by
  apply Stacks.UniversalInjectivity.LocalizationCriteria.universallyInjective_of_localizedMapRp (R
    := R) (S := S)
    ((TensorProduct.mk S N S').flip 1)
  intro q _
  refine universallyInjective_localizedMapRp_of_tensorUnit q ?_
  have : Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N) :=
    flat_localizedModule_atPrime q
  exact universallyInjectivePoly_tensorUnit_of_flat (essentiallyOfFinitePresentation_atPrime q)
    (exists_isPrime_comap_eq_of_isAssociatedPrimeStacks_closedFibre himage q)

end Stacks.UniversalInjectivity

end
