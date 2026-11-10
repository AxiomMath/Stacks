module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The completion at a finite intersection of comaximal ideals

For a finite family `I i` of pairwise comaximal ideals of a ring `R` with intersection `J`, the
quotients `R / Jⁿ` decompose as `∏ R / (I i)ⁿ` by the Chinese remainder theorem, so the `J`-adic
completion of `R` is the product of the `I i`-adic completions. When the `I i` are maximal
ideals, each `I i`-adic completion of `R` is moreover the completion of the local ring `R_{I i}`,
because `R / (I i)ⁿ` is already local.

Together these identify `R^∧_J` with `∏ (R_{I i})^∧`, which is the decomposition the proof of
**Stacks 0DZF** uses when it says that `P^∧` is `∏ P^∧_{𝔪 i}`.

## Main results

* `Stacks.AdicCompletion.bijective_adicCompletion_iInf_to_pi`: the `⨅ I i`-adic completion of
  `R` is the product of the `I i`-adic completions of `R`.
* `Stacks.AdicCompletion.bijective_adicCompletionMap_localization_atPrime`: for a maximal ideal
  `𝔪`, the `𝔪`-adic completion of `R` is the `𝔪 R_𝔪`-adic completion of the local ring `R_𝔪`.

## Implementation notes

`Stacks.AdicCompletion.bijective_adicCompletionMap_localization_atPrime` is
`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective` applied to the
isomorphisms `R / 𝔪ⁿ ≅ R_𝔪 / 𝔪ⁿ R_𝔪`, which hold because every element outside `𝔪` is already a
unit in `R / 𝔪ⁿ`: its image lies outside the unique maximal ideal `𝔪 / 𝔪ⁿ` of that ring. So the
localization inverts only units and `IsLocalization.atUnits` applies.

The product decomposition is built level by level and lifted: `Stacks.AdicCompletion` has no
general statement that a compatible family of isomorphisms of the levels induces one of the
completions for a *family* of ideals, only for a single ring map, so the inverse is assembled by
hand out of `AdicCompletion.liftRingHom`.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
-/

@[expose] public section

universe u

namespace Stacks.AdicCompletion

/-- For a maximal ideal `𝔪` of `R`, the map `R / 𝔪ⁿ → R_𝔪 / 𝔪ⁿ R_𝔪` is bijective: the
localization inverts elements that are already units. -/
public theorem bijective_quotientMap_pow_localization_atPrime
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S m] (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap ((m ^ n).map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map) := by
  refine (IsLocalization.atUnits (R ⧸ m ^ n)
    (Algebra.algebraMapSubmonoid (R ⧸ m ^ n) m.primeCompl)
    (S := S ⧸ (m ^ n).map (algebraMap R S)) ?_).bijective
  rintro _ ⟨x, hx, rfl⟩
  exact Ideal.Quotient.isUnit_mk_pow_of_notMem m hx

/-- **For a maximal ideal `𝔪`, the `𝔪`-adic completion of `R` is the completion of `R_𝔪`.** -/
public theorem bijective_adicCompletionMap_localization_atPrime
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S m] :
    Function.Bijective
      (adicCompletionMap (algebraMap R S) m (m.map (algebraMap R S)) le_rfl) :=
  adicCompletionMap_bijective_of_quotientMap_bijective (algebraMap R S) m
    (bijective_quotientMap_pow_localization_atPrime m S)

/-- Powers of a finite intersection of pairwise comaximal ideals: `(⨅ I i)ⁿ = ⨅ (I i)ⁿ`. -/
public theorem iInf_pow_eq_of_pairwise_isCoprime
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (n : ℕ) :
    (⨅ i, I i) ^ n = ⨅ i, I i ^ n := by
  classical
  let := Fintype.ofFinite ι
  have hprod : ∏ i, I i = ⨅ i, I i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (fun i _ j _ hij => hI hij)
  have hprod' : ∏ i, I i ^ n = ⨅ i, I i ^ n := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (fun i _ j _ hij => (hI hij).pow)
  rw [← hprod, ← hprod', Finset.prod_pow]

/-- The Chinese remainder isomorphism at the `n`-th level:
`R / (⨅ I i)ⁿ ≅ ∏ R / (I i)ⁿ`. -/
@[sga "3 XXII 5.9.10" "partial", sga "3 XXIV 3.9.1" "partial"]
public noncomputable def quotientPowIInfEquivPi
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (n : ℕ) :
    R ⧸ (⨅ i, I i) ^ n ≃+* ∀ i, R ⧸ I i ^ n :=
  (Ideal.quotEquivOfEq (iInf_pow_eq_of_pairwise_isCoprime I hI n)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => I i ^ n)
      (fun _ _ hij => (hI hij).pow))

/-- A level of a completion is recovered from a higher level by the quotient map. -/
public theorem evalₐ_factorPow {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | h x =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa [Ideal.smul_top_eq_map, neg_sub] using
      Submodule.neg_mem _ (SModEq.sub_mem.mp (x.property hmn))

/-- **The completion at a finite intersection of pairwise comaximal ideals is the product of the
completions.** The map is the product of the canonical maps `R^∧_{⨅ I j} → R^∧_{I i}`. -/
public theorem bijective_adicCompletion_iInf_to_pi
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) :
    Function.Bijective (RingHom.pi fun i =>
      adicCompletionMap (RingHom.id R) (⨅ j, I j) (I i) (by simpa using iInf_le I i)) := by
  let J := ⨅ i, I i
  let e := quotientPowIInfEquivPi I hI
  let F := RingHom.pi fun i =>
    adicCompletionMap (RingHom.id R) J (I i) (by simpa [J] using iInf_le I i)
  have he (n : ℕ) (x : R ⧸ J ^ n) (i : ι) :
      e n x i = Ideal.quotientMap (I i ^ n) (RingHom.id R)
        (by simpa using pow_le_pow_left' (iInf_le I i) n) x := by
    induction x using Quotient.inductionOn with
    | _ x => rfl
  have henat {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ J ^ n) (i : ι) :
      e m (Ideal.Quotient.factorPow J hmn x) i =
        Ideal.Quotient.factorPow (I i) hmn (e n x i) := by
    induction x using Quotient.inductionOn with
    | _ x => rfl
  have hlevel (n : ℕ) (x : AdicCompletion J R) (i : ι) :
      AdicCompletion.evalₐ (I i) n (F x i) = e n (AdicCompletion.evalₐ J n x) i := by
    change AdicCompletion.evalₐ (I i) n
      (adicCompletionMap (RingHom.id R) J (I i) (by simpa [J] using iInf_le I i) x) = _
    unfold adicCompletionMap
    rw [AdicCompletion.evalₐ_liftRingHom, he]
    rfl
  let g (n : ℕ) : (∀ i, AdicCompletion (I i) R) →+* R ⧸ J ^ n :=
    (e n).symm.toRingHom.comp (RingHom.pi fun i =>
      (AdicCompletion.evalₐ (I i) n).toRingHom.comp
        (Pi.evalRingHom (fun j => AdicCompletion (I j) R) i))
  have hg {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow J hmn).comp (g n) = g m := by
    ext x
    apply (e m).injective
    funext i
    change e m (Ideal.Quotient.factorPow J hmn ((e n).symm _)) i = e m ((e m).symm _) i
    rw [henat]
    simp only [RingEquiv.apply_symm_apply]
    exact evalₐ_factorPow (I i) hmn (x i)
  let G := AdicCompletion.liftRingHom J g hg
  have hFG (x : ∀ i, AdicCompletion (I i) R) : F (G x) = x := by
    funext i
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [hlevel]
    change e n (AdicCompletion.evalₐ J n (AdicCompletion.liftRingHom J g hg x)) i = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    change e n ((e n).symm _) i = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨fun x y hxy => AdicCompletion.ext_evalₐ fun n => (e n).injective (funext fun i => ?_),
    fun y => ⟨G y, hFG y⟩⟩
  rw [← hlevel, ← hlevel, hxy]

/-- A level of the map induced on completions by a ring map. -/
public theorem adicCompletionMap_evalₐ_apply
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hf : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicCompletionMap f I J hf x) =
      Ideal.quotientMap (J ^ n) f
        (by rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
            exact pow_le_pow_left' hf n) (AdicCompletion.evalₐ I n x) := by
  unfold adicCompletionMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- Bijectivity of the induced map on completions is insensitive to replacing `I.map f` by an
ideal equal to it. -/
public theorem adicCompletionMap_bijective_of_map_eq
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (hIJ : I.map f = J)
    (h : Function.Bijective (adicCompletionMap f I (I.map f) le_rfl)) :
    Function.Bijective (adicCompletionMap f I J hIJ.le) := by
  subst J
  exact h

end Stacks.AdicCompletion
