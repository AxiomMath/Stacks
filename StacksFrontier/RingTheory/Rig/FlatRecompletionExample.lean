module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.NonreducedLocalizedCompletion
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Flat

/-!
# Naive rig-flatness need not survive recompletion

There is a two-dimensional Noetherian local domain `A`, complete with respect to a principal
ideal `I = (a)`, and an element `f` of its maximal ideal outside `I`, whose completed principal
localization `C = (A_f)^∧` is nonreduced even after inverting `a`.  Writing `B = C / nil(C)` for
the reduction, the structure map `φ : A → B` is adic, topologically of finite type and naively
rig-flat — indeed `B` is a quotient of the restricted power series ring `A{x}` by the map sending
`x` to the image of `1/f`, and every prime of `B` avoiding `a` contracts to `(0)` in the domain
`A`, so `B` localized away from such a prime is a module over the fraction field of `A`.

Yet the induced map `ψ` of completed principal localizations of `φ` at `f` is *not* naively
rig-flat: its target recompletes to `B` itself, so `ψ` is the reduction map `C → B`, and that map
becomes flat after inverting `a` only if `C[1/a]` is already reduced, which it is not.

This is the counterexample showing that naive rig-flatness is strictly weaker than rig-flatness.

## Main results

* `Rig.exists_isNaivelyRigFlat_not_isNaivelyRigFlat_completedAwayMap` — the example.

## Implementation notes

The target is the reduction of the completed localization itself, not an arbitrary quotient.  The
restricted power series presentation is recorded with its action on constants and on the variable.
Each ring carries the adic topology induced by the specified principal ideal.  The final negation
is evaluated on the canonical map of completed principal localizations at the same element `f`,
and the identification of its target with `B` is part of the existential statement so that the
failure of flatness is pinned to a concrete map.

## References

* [Stacks Project, Tag 0GGN](https://stacks.math.columbia.edu/tag/0GGN)
-/

@[expose] public noncomputable section

universe u

namespace Rig

/-! ### Presenting a principal localization by one restricted variable -/

private theorem surjective_aeval_away {A : Type*} [CommRing A] (f : A) :
    Function.Surjective
      ((MvPolynomial.aeval (fun _ : Fin 1 => IsLocalization.Away.invSelf f) :
        MvPolynomial (Fin 1) A →ₐ[A] Localization.Away f).toRingHom) := by
  intro z
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (S := Localization.Away f) f z
  refine ⟨MvPolynomial.C r * MvPolynomial.X 0 ^ n, ?_⟩
  change (MvPolynomial.aeval (fun _ : Fin 1 => IsLocalization.Away.invSelf f)
    (MvPolynomial.C r * MvPolynomial.X 0 ^ n)) = z
  simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [← hr, mul_assoc, ← mul_pow]
  simp [IsLocalization.Away.mul_invSelf]

private theorem exists_pos_pow_mem_of_isTopologicallyNilpotent
    {A : Type*} [CommRing A] (I : Ideal A) (g : A)
    (hg : @IsTopologicallyNilpotent A _ I.adicTopology g) :
    ∃ n : ℕ, 0 < n ∧ g ^ n ∈ I := by
  let : TopologicalSpace A := I.adicTopology
  have hI : (I : Set A) ∈ nhds (0 : A) := by
    rw [I.hasBasis_nhds_zero_adic.mem_iff]
    exact ⟨1, trivial, by simp⟩
  obtain ⟨n, hn⟩ := hg.exists_pow_mem_of_mem_nhds hI
  cases n with
  | zero =>
    have h1 : (1 : A) ∈ I := by simpa using hn
    refine ⟨1, by decide, ?_⟩
    rw [(Ideal.eq_top_iff_one I).mpr h1]
    simp
  | succ n => exact ⟨n + 1, Nat.succ_pos _, hn⟩

/-- The completion of a principal localization in one variable is a quotient of the completion of
the polynomial ring in one variable. -/
private theorem exists_surjective_polynomialCompletion_away
    {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (f : A) :
    ∃ Φ : AdicCompletion (Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A) I)
        (MvPolynomial (Fin 1) A) →+*
        AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f),
      Function.Surjective Φ ∧
        Φ.comp (algebraMap (MvPolynomial (Fin 1) A)
          (AdicCompletion (Ideal.map (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A) I)
            (MvPolynomial (Fin 1) A))) =
          (algebraMap (Localization.Away f)
            (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
              (Localization.Away f))).comp
            (MvPolynomial.aeval (fun _ : Fin 1 =>
              IsLocalization.Away.invSelf (S := Localization.Away f) f)).toRingHom := by
  classical
  let P := MvPolynomial (Fin 1) A
  let Af := Localization.Away f
  let Ip : Ideal P := Ideal.map (MvPolynomial.C : A →+* P) I
  let If : Ideal Af := I.map (algebraMap A Af)
  let ev : P →+* Af :=
    (MvPolynomial.aeval (fun _ : Fin 1 => IsLocalization.Away.invSelf (S := Af) f)).toRingHom
  let : Algebra P Af := ev.toAlgebra
  have hevC : ev.comp (MvPolynomial.C : A →+* P) = algebraMap A Af := by
    ext x
    exact MvPolynomial.aeval_C _ _
  have hmap : Ip.map ev = If := by
    dsimp only [Ip, If]
    rw [Ideal.map_map, hevC]
  have hle : Ip.map ev ≤ If := hmap.le
  let Φ : AdicCompletion Ip P →+* AdicCompletion If Af :=
    Stacks.Nagata.PthRootDescent.mapAdicCompletion Ip If hle
  have hΦ : Φ.comp (algebraMap P (AdicCompletion Ip P)) =
      (algebraMap Af (AdicCompletion If Af)).comp ev :=
    RingHom.ext fun p => Stacks.Nagata.PthRootDescent.mapAdicCompletion_of hle p
  let K : Ideal (AdicCompletion Ip P) := Ip.map (algebraMap P (AdicCompletion Ip P))
  have hK : K.map Φ = If.map (algebraMap Af (AdicCompletion If Af)) := by
    dsimp only [K]
    rw [Ideal.map_map, hΦ, ← Ideal.map_map, hmap]
  have : IsPrecomplete K (AdicCompletion Ip P) := by
    dsimp only [K]
    exact (AdicCompletion.isAdicComplete_self Ip (I.fg_of_isNoetherianRing.map _)).toIsPrecomplete
  have : IsHausdorff (K.map Φ) (AdicCompletion If Af) := by
    rw [hK]
    exact (AdicCompletion.isAdicComplete_self If If.fg_of_isNoetherianRing).toIsHausdorff
  have hmod : Function.Surjective ((Ideal.Quotient.mk (K.map Φ)).comp Φ) := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ If c)
    obtain ⟨p, hp⟩ := surjective_aeval_away f x
    refine ⟨algebraMap P (AdicCompletion Ip P) p, ?_⟩
    apply Ideal.Quotient.eq.mpr
    have hdiff : c - algebraMap Af (AdicCompletion If Af) x ∈ K.map Φ := by
      rw [hK, ← AdicCompletion.ker_evalOneₐ_eq_map If If.fg_of_isNoetherianRing, RingHom.mem_ker]
      change AdicCompletion.evalOneₐ If (c - algebraMap Af (AdicCompletion If Af) x) = 0
      have hEval (y : Af) : AdicCompletion.evalOneₐ If
          (algebraMap Af (AdicCompletion If Af) y) = Ideal.Quotient.mk If y :=
        congrArg (fun g : Af →+* Af ⧸ If => g y)
          (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk If)
      rw [map_sub, hEval, hx]
      simp
    change Φ (algebraMap P (AdicCompletion Ip P) p) - c ∈ K.map Φ
    rw [Stacks.Nagata.PthRootDescent.mapAdicCompletion_of hle]
    change algebraMap Af (AdicCompletion If Af) (ev p) - c ∈ K.map Φ
    rw [show ev p = x from hp]
    simpa [sub_eq_add_neg, add_comm] using neg_mem hdiff
  exact ⟨Φ, surjective_of_mk_map_comp_surjective Φ hmod, hΦ⟩

/-! ### Flatness from contracting primes to zero -/

/-- If every prime of `B` avoiding the image of `a` contracts to `(0)` in the domain `A`, then
`B` localized away from the image of any `g` with a power in `(a)` is flat over `A`: it is a
module over the fraction field of `A`. -/
private theorem flat_away_of_comap_eq_bot
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] (φ : A →+* B) (a : A)
    (hprime : ∀ q : Ideal B, q.IsPrime → φ a ∉ q → q.comap φ = ⊥)
    (g : A) (hpow : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ Ideal.span {a}) :
    RingHom.Flat ((algebraMap B (Localization.Away (φ g))).comp φ) := by
  classical
  let T := Localization.Away (φ g)
  let ψ : A →+* T := (algebraMap B T).comp φ
  have hunit (r : A) (hr : r ≠ 0) : IsUnit (ψ r) := by
    by_contra hnot
    have hproper : Ideal.span {ψ r} ≠ ⊤ := fun htop =>
      hnot (Ideal.span_singleton_eq_top.mp htop)
    obtain ⟨m, hmmax, hm⟩ := Ideal.exists_le_maximal (Ideal.span {ψ r}) hproper
    let q : Ideal B := m.comap (algebraMap B T)
    have : m.IsPrime := hmmax.isPrime
    have hq : q.IsPrime := Ideal.IsPrime.comap (algebraMap B T)
    have hgq : φ g ∉ q := fun h =>
      (Ideal.notMem_of_isUnit m (IsLocalization.Away.algebraMap_isUnit (φ g))) h
    have hqa : φ a ∉ q := by
      intro ha
      obtain ⟨n, hnpos, hn⟩ := hpow
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hn
      have hpowq : φ g ^ n ∈ q := by
        rw [← map_pow]
        change ψ (g ^ n) ∈ m
        rw [hx, map_mul]
        exact Ideal.mul_mem_right (ψ x) m ha
      exact hgq ((hq.pow_mem_iff_mem n hnpos).mp hpowq)
    have hrbot : r ∈ (⊥ : Ideal A) := by
      rw [← hprime q hq hqa]
      exact hm (Ideal.subset_span rfl)
    exact hr (Ideal.mem_bot.mp hrbot)
  let e : FractionRing A →+* T := IsLocalization.lift
    (M := nonZeroDivisors A) (S := FractionRing A) (P := T) (g := ψ)
    (fun s => hunit s.1 (nonZeroDivisors.coe_ne_zero s))
  have hAflat : RingHom.Flat (algebraMap A (FractionRing A)) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat (p := nonZeroDivisors A) (S := FractionRing A)
  have heq : e.comp (algebraMap A (FractionRing A)) = ψ := by
    ext r
    exact IsLocalization.lift_eq _ r
  change RingHom.Flat ψ
  rw [← heq]
  exact RingHom.Flat.comp hAflat
    (RingHom.Flat.of_isField (Field.toIsField (FractionRing A)) e)

/-! ### Ring homomorphisms out of an adic completion -/

private theorem exists_approximation_adicCompletion {R : Type*} [CommRing R]
    (I : Ideal R) (hI : I.FG) (c : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, algebraMap R (AdicCompletion I R) r - c ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n c)
  refine ⟨r, ?_⟩
  rw [← AdicCompletion.ker_evalₐ I hI n, RingHom.mem_ker, map_sub]
  change AdicCompletion.evalₐ I n (AdicCompletion.of I R r) - _ = 0
  rw [AdicCompletion.evalₐ_of, hr]
  exact sub_self _

/-- Two ring homomorphisms out of an adic completion into a Hausdorff adic target agree as soon as
they agree on the image of the ring, provided both carry the extended ideal into the target's
ideal. -/
private theorem ringHom_ext_adicCompletion {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (hI : I.FG) (J : Ideal S) [IsHausdorff J S]
    (F G : AdicCompletion I R →+* S)
    (hF : (I.map (algebraMap R (AdicCompletion I R))).map F ≤ J)
    (hG : (I.map (algebraMap R (AdicCompletion I R))).map G ≤ J)
    (h : ∀ r, F (algebraMap R (AdicCompletion I R) r) =
      G (algebraMap R (AdicCompletion I R) r)) : F = G := by
  refine RingHom.ext (congrFun (IsHausdorff.funext' J (f := F) (g := G) fun n c => ?_))
  obtain ⟨r, hr⟩ := exists_approximation_adicCompletion I hI c n
  have hh (H : AdicCompletion I R →+* S)
      (hH : (I.map (algebraMap R (AdicCompletion I R))).map H ≤ J) :
      Ideal.Quotient.mk (J ^ n) (H (algebraMap R (AdicCompletion I R) r)) =
        Ideal.Quotient.mk (J ^ n) (H c) := by
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub]
    exact Ideal.pow_right_mono hH n (by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem H hr)
  rw [← hh F hF, ← hh G hG, h]

private theorem denseRange_of_adic_approximation {R S : Type*}
    [CommRing R] [CommRing S] (J : Ideal S) (F : R →+* S)
    (h : ∀ s n, ∃ r, F r - s ∈ J ^ n) :
    letI : TopologicalSpace S := J.adicTopology
    DenseRange F := by
  let : TopologicalSpace S := J.adicTopology
  intro s
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨n, _, hn⟩ := (J.hasBasis_nhds_adic s).mem_iff.mp hU
  obtain ⟨r, hr⟩ := h s n
  exact ⟨F r, hn ⟨F r - s, hr, by simp⟩, ⟨r, rfl⟩⟩

private theorem denseRange_quotient_adicCompletion {P R S : Type*}
    [CommRing P] [CommRing R] [CommRing S]
    (I : Ideal R) (hI : I.FG) (π : AdicCompletion I R →+* S)
    (hπ : Function.Surjective π) (F : P →+* R) (hF : Function.Surjective F) :
    let J := (I.map (algebraMap R (AdicCompletion I R))).map π
    letI : TopologicalSpace S := J.adicTopology
    DenseRange ((π.comp (algebraMap R (AdicCompletion I R))).comp F) := by
  apply denseRange_of_adic_approximation
  intro s n
  obtain ⟨c, rfl⟩ := hπ s
  obtain ⟨r, hr⟩ := exists_approximation_adicCompletion I hI c n
  obtain ⟨p, rfl⟩ := hF r
  refine ⟨p, ?_⟩
  change π (algebraMap R (AdicCompletion I R) (F p)) - π c ∈ _
  rw [← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem π hr

/-- Completing a complete ring along a principal localization at a unit changes nothing. -/
private theorem exists_adicCompletion_away_equiv {B : Type*} [CommRing B]
    (J : Ideal B) [IsAdicComplete J B] (g : B) (hg : IsUnit g) :
    ∃ e : AdicCompletion (J.map (algebraMap B (Localization.Away g)))
        (Localization.Away g) ≃+* B,
      ∀ b, e (algebraMap (Localization.Away g) _ (algebraMap B _ b)) = b := by
  let e₀ : B ≃ₐ[B] Localization.Away g := IsLocalization.atUnits B (Submonoid.powers g)
    (by rintro _ ⟨n, rfl⟩; exact hg.pow n)
  have he₀ (b : B) : e₀ b = algebraMap B (Localization.Away g) b := e₀.commutes b
  have : IsAdicComplete (J.map (algebraMap B (Localization.Away g))) (Localization.Away g) := by
    have heq : e₀.toRingEquiv.toRingHom = algebraMap B (Localization.Away g) := RingHom.ext he₀
    have h := (IsAdicComplete.congr_ringEquiv J e₀.toRingEquiv).mpr inferInstance
    change IsAdicComplete (J.map e₀.toRingEquiv.toRingHom) _ at h
    rwa [heq] at h
  refine ⟨(AdicCompletion.ofAlgEquiv
      (J.map (algebraMap B (Localization.Away g)))).symm.toRingEquiv.trans
    e₀.symm.toRingEquiv, fun b => ?_⟩
  change e₀.symm ((AdicCompletion.ofAlgEquiv _).symm
    (AdicCompletion.of _ _ (algebraMap B (Localization.Away g) b))) = b
  rw [AdicCompletion.ofAlgEquiv_symm_of, ← he₀, e₀.symm_apply_apply]

private theorem completedAwayMap_of {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (f : A) (x : Localization.Away f) :
    RingHom.completedAwayMap φ I f (algebraMap (Localization.Away f) _ x) =
      algebraMap (Localization.Away (φ f)) _
        (IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f x) := by
  let : Algebra (Localization.Away f) (Localization.Away (φ f)) :=
    (IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f).toAlgebra
  unfold RingHom.completedAwayMap
  exact Stacks.Nagata.PthRootDescent.mapAdicCompletion_of _ x

/-! ### Flatness of a surjection with nilpotent kernel -/

private theorem injective_of_flat_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (F : R →+* S)
    (hF : Function.Surjective F) (hker : RingHom.ker F ≤ nilradical R)
    (hflat : RingHom.Flat F) : Function.Injective F := by
  let : Algebra R S := F.toAlgebra
  have : Module.Flat R S := hflat
  have : Module.FaithfullyFlat R S := ⟨fun m hm htop => by
    have := hm
    have hmap : m.map F = ⊤ := by
      have hh : m.map (algebraMap R S) = ⊤ := by
        simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] using htop
      exact hh
    have h : (m.map F).comap F = m ⊔ RingHom.ker F := Ideal.comap_map_of_surjective F hF m
    have hk : RingHom.ker F ≤ m := hker.trans (nilradical_le_prime m)
    rw [hmap, Ideal.comap_top, sup_eq_left.mpr hk] at h
    exact hm.ne_top h.symm⟩
  exact FaithfulSMul.algebraMap_injective R S

private theorem ker_awayMap_le_nilradical {R S : Type*} [CommRing R] [CommRing S]
    (F : R →+* S) (hker : RingHom.ker F ≤ nilradical R) (a : R) :
    RingHom.ker (IsLocalization.Away.map (Localization.Away a)
      (Localization.Away (F a)) F a) ≤ nilradical (Localization.Away a) := by
  let Ra := Localization.Away a
  let Sa := Localization.Away (F a)
  let G := IsLocalization.Away.map Ra Sa F a
  intro z hz
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj a z
  have hFr : algebraMap S Sa (F r) = 0 := by
    have hmap : G (algebraMap R Ra r) = algebraMap S Sa (F r) := IsLocalization.map_eq _ r
    rw [← hmap, ← hr]
    change G (z * algebraMap R Ra a ^ n) = 0
    rw [map_mul, show G z = 0 from hz, zero_mul]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (F a)) Sa (F r)).mp hFr
  have hnil : IsNilpotent (a ^ m * r) := mem_nilradical.mp (hker (by
    rwa [RingHom.mem_ker, map_mul, map_pow]))
  have hnil' := hnil.map (algebraMap R Ra)
  rw [map_mul, map_pow, ← hr] at hnil'
  rw [show algebraMap R Ra a ^ m * (z * algebraMap R Ra a ^ n) =
      z * (algebraMap R Ra a ^ (m + n)) by ring] at hnil'
  exact mem_nilradical.mpr (((IsLocalization.Away.algebraMap_isUnit (S := Ra) a).pow
    (m + n)).isNilpotent_mul_unit_of_commute_iff (Commute.all _ _) |>.mp hnil')

/-- A surjection with nilpotent kernel onto a reduced ring cannot stay flat after inverting an
element at which the source is nonreduced. -/
private theorem not_flat_awayMap_of_not_isReduced {R S : Type*}
    [CommRing R] [CommRing S] [IsReduced S] (F : R →+* S)
    (hF : Function.Surjective F) (hker : RingHom.ker F ≤ nilradical R)
    (a : R) (hnr : ¬ IsReduced (Localization.Away a)) :
    ¬ RingHom.Flat (IsLocalization.Away.map (Localization.Away a)
      (Localization.Away (F a)) F a) := by
  intro hflat
  apply hnr
  apply isReduced_of_injective (IsLocalization.Away.map (Localization.Away a)
    (Localization.Away (F a)) F a)
  apply injective_of_flat_of_surjective_of_ker_le_nilradical _ ?_
    (ker_awayMap_le_nilradical F hker a) hflat
  rw [IsLocalization.Away.map_surjective_iff]
  intro b
  obtain ⟨r, rfl⟩ := hF b
  exact ⟨r, 0, by simp⟩

private theorem flat_awayMap_of_flat_comp {R S : Type*} [CommRing R] [CommRing S]
    (F : R →+* S) (a : R)
    (hflat : RingHom.Flat ((algebraMap S (Localization.Away (F a))).comp F)) :
    RingHom.Flat (IsLocalization.Away.map (Localization.Away a)
      (Localization.Away (F a)) F a) := by
  let Ra := Localization.Away a
  let Sa := Localization.Away (F a)
  let G := IsLocalization.Away.map Ra Sa F a
  let : Algebra R Sa := ((algebraMap S Sa).comp F).toAlgebra
  let : Algebra Ra Sa := G.toAlgebra
  have : IsScalarTower R Ra Sa := IsScalarTower.of_algebraMap_eq' (by
    ext r
    have hmap : G (algebraMap R Ra r) = algebraMap S Sa (F r) := IsLocalization.map_eq _ r
    exact hmap.symm)
  have : Module.Flat R Sa := hflat
  exact (Module.flat_iff_of_isLocalization Ra (Submonoid.powers a) Sa).mpr inferInstance

/-! ### Primes of a two-dimensional local domain -/

/-- In a two-dimensional local domain, a prime of a ring in which the image of `f` is a unit and
the image of `a` lies in the Jacobson radical, avoiding the image of `a`, contracts to `(0)`. -/
private theorem comap_eq_bot_of_ringKrullDim_eq_two
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B]
    (φ : A →+* B) (a f : A) (hdim : ringKrullDim A = 2)
    (hf : f ∈ IsLocalRing.maximalIdeal A) (hfu : IsUnit (φ f))
    (ha : φ a ∈ (⊥ : Ideal B).jacobson)
    (q : Ideal B) (hq : q.IsPrime) (haq : φ a ∉ q) : q.comap φ = ⊥ := by
  have := hq
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hq.ne_top
  have := hm
  have ham : φ a ∈ m := by
    simpa only [Ideal.jacobson_eq_self_of_isMaximal] using
      (Ideal.jacobson_mono (show (⊥ : Ideal B) ≤ m from bot_le) ha)
  let p := q.comap φ
  let p' := m.comap φ
  have : p.IsPrime := Ideal.IsPrime.comap φ
  have : p'.IsPrime := Ideal.IsPrime.comap φ
  have hpp : p < p' :=
    lt_of_le_of_ne (Ideal.comap_mono hqm) fun h => haq (show a ∈ p by rwa [h])
  have hp'm : p' < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      fun h => Ideal.notMem_of_isUnit m hfu (show f ∈ p' by rwa [h])
  by_contra hp
  have h1 : 1 ≤ p.height := Order.one_le_iff_ne_zero.mpr
    (fun h => hp (Ideal.height_eq_zero_iff_eq_bot.mp h))
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hpp
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hp'm
  have h : (3 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height := calc
    3 = (1 : ℕ∞) + 1 + 1 := by norm_num
    _ ≤ p.height + 1 + 1 := by gcongr
    _ ≤ p'.height + 1 := by gcongr
    _ ≤ _ := h3
  have hh : (3 : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    simpa only [WithBot.coe_ofNat] using (WithBot.coe_le_coe.mpr h)
  rw [hdim] at hh
  norm_num at hh

/-! ### The three clauses of the example -/

/-- The reduction of the completed principal localization is a quotient of the restricted power
series ring in one variable, by the map sending the variable to the image of `1 / f`. -/
private theorem exists_restrictedPowerSeries_presentation
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (f : A) :
    let Af := Localization.Away f
    let C := AdicCompletion (I.map (algebraMap A Af)) Af
    let π : C →+* C ⧸ nilradical C := Ideal.Quotient.mk (nilradical C)
    ∃ θ : RestrictedPowerSeries I (Fin 1) →+* C ⧸ nilradical C,
      Function.Surjective θ ∧
        (∀ x : A, θ (RestrictedPowerSeries.polynomialRingHom I (Fin 1) (MvPolynomial.C x)) =
          π (algebraMap A C x)) ∧
        θ (RestrictedPowerSeries.polynomialRingHom I (Fin 1) (MvPolynomial.X 0)) =
          π (algebraMap Af C (IsLocalization.Away.invSelf (S := Af) f)) := by
  intro Af C π
  obtain ⟨Φ, hΦ, hΦof⟩ := exists_surjective_polynomialCompletion_away (A := A) I f
  let eP : RestrictedPowerSeries I (Fin 1) ≃+*
      AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A))
        (MvPolynomial (Fin 1) A) :=
    RestrictedPowerSeries.adicCompletionEquiv I (Fin 1)
  have hθ : ∀ p : MvPolynomial (Fin 1) A,
      (π.comp (Φ.comp eP.toRingHom))
          (RestrictedPowerSeries.polynomialRingHom I (Fin 1) p) =
        π (algebraMap Af C (MvPolynomial.aeval
          (fun _ : Fin 1 => IsLocalization.Away.invSelf (S := Af) f) p)) := by
    intro p
    change π (Φ (eP _)) = _
    rw [RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom]
    exact congrArg π (congrArg (fun H : MvPolynomial (Fin 1) A →+* C => H p) hΦof)
  refine ⟨π.comp (Φ.comp eP.toRingHom),
    Ideal.Quotient.mk_surjective.comp (hΦ.comp eP.surjective), fun x => ?_, ?_⟩
  · rw [hθ, MvPolynomial.aeval_C]
    rfl
  · rw [hθ, MvPolynomial.aeval_X]

/-- The reduction map of the example is adic, topologically of finite type and naively
rig-flat. -/
private theorem isNaivelyRigFlat_reduction
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a f : A) :
    let I : Ideal A := Ideal.span {a}
    let Af := Localization.Away f
    let C := AdicCompletion (I.map (algebraMap A Af)) Af
    let B := C ⧸ nilradical C
    let φ : A →+* B := (Ideal.Quotient.mk (nilradical C)).comp (algebraMap A C)
    letI : TopologicalSpace A := I.adicTopology
    letI : TopologicalSpace B := (I.map φ).adicTopology
    (∀ q : Ideal B, q.IsPrime → φ a ∉ q → q.comap φ = ⊥) → RingHom.IsNaivelyRigFlat φ := by
  intro I Af C B φ hprime
  let If : Ideal Af := I.map (algebraMap A Af)
  let π : C →+* B := Ideal.Quotient.mk (nilradical C)
  let K : Ideal C := If.map (algebraMap Af C)
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing If
  have hK : K = I.map (algebraMap A C) := Ideal.map_map _ _
  have hKJ : K.map π = I.map φ := by rw [hK, Ideal.map_map]
  refine ⟨⟨I, rfl, rfl⟩, ?_, fun g hg => ?_⟩
  · let F : MvPolynomial (Fin 1) A →+* Af :=
      (MvPolynomial.aeval (fun _ : Fin 1 => IsLocalization.Away.invSelf (S := Af) f)).toRingHom
    refine ⟨1, (π.comp (algebraMap Af C)).comp F, ?_, ?_⟩
    · ext x
      change π (algebraMap Af C (MvPolynomial.aeval _ (MvPolynomial.C x))) = φ x
      rw [MvPolynomial.aeval_C]
      rfl
    · rw [← hKJ]
      exact denseRange_quotient_adicCompletion If If.fg_of_isNoetherianRing π
        Ideal.Quotient.mk_surjective F (surjective_aeval_away f)
  · exact flat_away_of_comap_eq_bot φ a hprime g
      (exists_pos_pow_mem_of_isTopologicallyNilpotent I g hg)

/-- The target of the induced map of completed principal localizations recompletes to the
reduction itself, so that map is the reduction map; it is therefore not flat after inverting the
image of `a`, and in particular not naively rig-flat. -/
private theorem not_isNaivelyRigFlat_completedAwayMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] (a f : A) :
    let I : Ideal A := Ideal.span {a}
    let Af := Localization.Away f
    let If : Ideal Af := I.map (algebraMap A Af)
    let C := AdicCompletion If Af
    let B := C ⧸ nilradical C
    let φ : A →+* B := (Ideal.Quotient.mk (nilradical C)).comp (algebraMap A C)
    IsUnit (φ f) → ¬ IsReduced (Localization.Away (algebraMap A C a)) →
      (let B_f := Localization.Away (φ f)
       let J_f := (I.map φ).map (algebraMap B B_f)
       let I_hat := If.map (algebraMap Af C)
       let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
       letI : TopologicalSpace C := I_hat.adicTopology
       letI : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
       let ψ := RingHom.completedAwayMap φ I f
       (∃ e : AdicCompletion J_f B_f ≃+* B,
         (∀ b : B, e ((algebraMap B_f (AdicCompletion J_f B_f)) (algebraMap B B_f b)) = b) ∧
         (∀ c : C, e (ψ c) = Ideal.Quotient.mk (nilradical C) c)) ∧
       let a_hat : C := algebraMap Af C (algebraMap A Af a)
       (¬ _root_.RingHom.Flat (IsLocalization.Away.map (Localization.Away a_hat)
         (Localization.Away (ψ a_hat)) ψ a_hat)) ∧ (¬ RingHom.IsNaivelyRigFlat ψ)) := by
  intro I Af If C B φ hunit hClocnr
  let π : C →+* B := Ideal.Quotient.mk (nilradical C)
  let K : Ideal C := If.map (algebraMap Af C)
  let J : Ideal B := I.map φ
  have hK : K = I.map (algebraMap A C) := Ideal.map_map _ _
  have hKJ : K.map π = J := by rw [hK, Ideal.map_map]
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing If
  have : IsAdicComplete K C := AdicCompletion.isAdicComplete_self If If.fg_of_isNoetherianRing
  have : IsAdicComplete J B := hKJ ▸ isAdicComplete_quotient K (nilradical C)
  let Bf := Localization.Away (φ f)
  let Jf : Ideal Bf := J.map (algebraMap B Bf)
  let D := AdicCompletion Jf Bf
  let L : Ideal D := Jf.map (algebraMap Bf D)
  let β : B →+* D := (algebraMap Bf D).comp (algebraMap B Bf)
  let ψ : C →+* D := RingHom.completedAwayMap φ I f
  let : TopologicalSpace C := K.adicTopology
  let : TopologicalSpace D := L.adicTopology
  obtain ⟨e, he⟩ := exists_adicCompletion_away_equiv J (φ f) hunit
  have hcomp : ψ.comp (algebraMap Af C) = (β.comp π).comp (algebraMap Af C) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro x
    change ψ (algebraMap Af C (algebraMap A Af x)) =
      β (π (algebraMap Af C (algebraMap A Af x)))
    have hmap : IsLocalization.Away.map Af Bf φ f (algebraMap A Af x) =
        algebraMap B Bf (φ x) := IsLocalization.map_eq _ x
    rw [completedAwayMap_of, hmap]
    rfl
  have hGL : K.map (β.comp π) = L := by
    rw [← Ideal.map_map, hKJ]
    change J.map ((algebraMap Bf D).comp (algebraMap B Bf)) =
      (J.map (algebraMap B Bf)).map (algebraMap Bf D)
    exact (Ideal.map_map (algebraMap B Bf) (algebraMap Bf D)).symm
  have hψL : K.map ψ = L := by
    change (If.map (algebraMap Af C)).map ψ = L
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
    exact hGL
  have : IsHausdorff L D :=
    (AdicCompletion.isAdicComplete_self Jf Jf.fg_of_isNoetherianRing).toIsHausdorff
  have hψ : ψ = β.comp π := ringHom_ext_adicCompletion If If.fg_of_isNoetherianRing
    L ψ (β.comp π) hψL.le hGL.le (fun x => congrArg (fun h : Af →+* D => h x) hcomp)
  have heψ (c : C) : e (ψ c) = π c := by
    rw [hψ]
    exact he (π c)
  have hψsurj : Function.Surjective ψ := by
    intro d
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e d)
    exact ⟨c, e.injective (by rwa [heψ])⟩
  have hψker : RingHom.ker ψ ≤ nilradical C := by
    intro c hc
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π c = 0
    rw [← heψ, show ψ c = 0 from hc, map_zero]
  have : IsReduced B := (Ideal.isRadical_iff_quotient_reduced (nilradical C)).mp
    (Ideal.radical_isRadical (⊥ : Ideal C))
  have : IsReduced D := isReduced_of_injective e e.injective
  let ah : C := algebraMap Af C (algebraMap A Af a)
  have hnot := not_flat_awayMap_of_not_isReduced ψ hψsurj hψker ah hClocnr
  refine ⟨⟨e, he, heψ⟩, hnot, fun hrig => hnot ?_⟩
  have hnil : IsTopologicallyNilpotent ah := by
    let : WithIdeal C := ⟨K⟩
    exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem (algebraMap Af C)
      (Ideal.mem_map_of_mem (algebraMap A Af) (Ideal.subset_span rfl)))
  exact flat_awayMap_of_flat_comp ψ ah (hrig.2.2 ah hnil)

/-! ### The example -/

/-- **Stacks 0GGN.** Naive rig-flatness is not preserved by passing to completed principal
localizations: there is a two-dimensional Noetherian local domain `A`, complete for a principal
ideal `(a)`, and `f ∈ 𝔪 ∖ (a)`, such that the reduction `B` of the completed localization
`C = (A_f)^∧` receives a naively rig-flat adic map `φ : A → B` of topological finite type —
presented by the restricted power series ring `A{x}` with `x ↦ 1/f` — while the induced map `ψ`
of completed principal localizations of `φ` at `f` is not naively rig-flat. -/
@[stacks 0GGN]
public theorem exists_isNaivelyRigFlat_not_isNaivelyRigFlat_completedAwayMap :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (_ : IsNoetherianRing A) (a f : A),
      ringKrullDim A = 2 ∧
        IsAdicComplete (Ideal.span {a}) A ∧
        f ∈ IsLocalRing.maximalIdeal A ∧
        f ∉ Ideal.span {a} ∧
        (let I : Ideal A := Ideal.span {a}
         let Af := Localization.Away f
         let If : Ideal Af := I.map (algebraMap A Af)
         let C := AdicCompletion If Af
         let B := C ⧸ nilradical C
         let φ : A →+* B := (Ideal.Quotient.mk (nilradical C)).comp (algebraMap A C)
         letI : TopologicalSpace A := I.adicTopology
         letI : TopologicalSpace B := (I.map φ).adicTopology
         (¬ IsReduced (Localization.Away (algebraMap A C a))) ∧
           (∃ θ : RestrictedPowerSeries I (Fin 1) →+* B,
             Function.Surjective θ ∧
               (∀ x : A,
                 θ (RestrictedPowerSeries.polynomialRingHom I (Fin 1) (MvPolynomial.C x)) =
                   φ x) ∧
               θ (RestrictedPowerSeries.polynomialRingHom I (Fin 1) (MvPolynomial.X 0)) =
                 Ideal.Quotient.mk (nilradical C)
                   (algebraMap Af C (IsLocalization.Away.invSelf (S := Af) f))) ∧
           (∀ q : Ideal B, q.IsPrime → φ a ∉ q → q.comap φ = ⊥) ∧
           RingHom.IsNaivelyRigFlat φ ∧
             (let B_f := Localization.Away (φ f)
              let J_f := (I.map φ).map (algebraMap B B_f)
              let I_hat := If.map (algebraMap Af C)
              let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
              letI : TopologicalSpace C := I_hat.adicTopology
              letI : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
              let ψ := RingHom.completedAwayMap φ I f
              (∃ e : AdicCompletion J_f B_f ≃+* B,
                (∀ b : B, e ((algebraMap B_f (AdicCompletion J_f B_f))
                  (algebraMap B B_f b)) = b) ∧
                (∀ c : C, e (ψ c) = Ideal.Quotient.mk (nilradical C) c)) ∧
              let a_hat : C := algebraMap Af C (algebraMap A Af a)
              (¬ _root_.RingHom.Flat (IsLocalization.Away.map (Localization.Away a_hat)
                (Localization.Away (ψ a_hat)) ψ a_hat)) ∧
                (¬ RingHom.IsNaivelyRigFlat ψ))) := by
  classical
  obtain ⟨A, hAcomm, hAdom, hAlocal, hAnoeth, a, f, hdim, hcomplete, hfm, hfa, -, hClocnr⟩ :=
    exists_nonreduced_adicCompletion_localization_away.{u}
  refine ⟨A, hAcomm, hAdom, hAlocal, hAnoeth, a, f, hdim, hcomplete, hfm, hfa, ?_⟩
  let I : Ideal A := Ideal.span {a}
  let Af := Localization.Away f
  let If : Ideal Af := I.map (algebraMap A Af)
  let C := AdicCompletion If Af
  let B := C ⧸ nilradical C
  let π : C →+* B := Ideal.Quotient.mk (nilradical C)
  let φ : A →+* B := π.comp (algebraMap A C)
  have : IsNoetherianRing C := AdicCompletion.isNoetherianRing If
  have : IsAdicComplete (If.map (algebraMap Af C)) C :=
    AdicCompletion.isAdicComplete_self If If.fg_of_isNoetherianRing
  have hKJ : (If.map (algebraMap Af C)).map π = I.map φ := by
    rw [show If.map (algebraMap Af C) = I.map (algebraMap A C) from Ideal.map_map _ _,
      Ideal.map_map]
  have : IsAdicComplete (I.map φ) B :=
    hKJ ▸ isAdicComplete_quotient (If.map (algebraMap Af C)) (nilradical C)
  have hunit : IsUnit (φ f) :=
    ((IsLocalization.Away.algebraMap_isUnit (S := Af) f).map (algebraMap Af C)).map π
  have hprime : ∀ q : Ideal B, q.IsPrime → φ a ∉ q → q.comap φ = ⊥ :=
    comap_eq_bot_of_ringKrullDim_eq_two φ a f hdim hfm hunit
      ((IsAdicComplete.le_jacobson_bot (I.map φ))
        (Ideal.mem_map_of_mem φ (Ideal.subset_span rfl)))
  exact ⟨hClocnr, exists_restrictedPowerSeries_presentation I f, hprime,
    isNaivelyRigFlat_reduction a f hprime,
    not_isNaivelyRigFlat_completedAwayMap a f hunit hClocnr⟩

end Rig

end
