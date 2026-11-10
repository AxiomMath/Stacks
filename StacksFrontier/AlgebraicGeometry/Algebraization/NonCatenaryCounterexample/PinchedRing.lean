module

public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.BaseRing
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceZigzagTwo
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.RingTheory.Pinch

/-!
# The non-catenary local ring of the counterexample to Stacks 0EJA, and its distance function

Let `B` be the semilocal ring of
`StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.BaseRing`, with maximal
ideals `𝔪₁B` (height six) and `𝔫B` (height three), and suppose given a ring isomorphism
`K ≅ K(y₁, y₂, y₃)`. Pinching `𝔪₁B` and `𝔫B` together along the induced isomorphism of residue
fields gives a Noetherian local domain `A` (`Stacks.Pinch.pinch`). Let `𝔟 = (Q₀ ∩ W) ∩ A`,
`A'' = A/𝔟` and `I = (x₁) ⊆ A''`; this is the algebraization situation of the counterexample, with
`𝔞` the maximal ideal of `A''`.

In `Y = Spec(A''/I)`, whose points are the primes of `A` containing `W ∩ A`, the chain
`W ⊂ V ⊂ J` (with `J` the maximal ideal of `A`) is saturated of length two, while
`W ⊂ C ⊂ P` is a chain of length two below the point `P`. The zigzag of
`Stacks.Algebraization.distanceFunction_le_two_of_zigzag` therefore gives `δ^Y_Z(P) ≤ 2`, although
`dim({P}‾) = 3`: Stacks 0EIY (5) fails for the non-catenary ring `A''/I`.

## Main definitions

* `Stacks.NonCatenaryExample.RingA`: the non-catenary Noetherian local domain `A`.
* `Stacks.NonCatenaryExample.situation`: the algebraization situation `(A'', I, 𝔞)`.

## Main results

* `Stacks.NonCatenaryExample.distanceToZ_ptP_le_two`: `δ^Y_Z(P) ≤ 2`.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Pinch

universe u

namespace Stacks.NonCatenaryExample

variable (K : Type u) [Field K] (e : K ≃+* FractionRing (MvPolynomial (Fin 3) K))

/-- The pinched subring `A ⊆ B`. -/
abbrev pinchA : Subring (RingB K) := pinch (ext K (idealM K)) (ext K (idealN K)) (residueEquiv K e)

/-- The non-catenary Noetherian local domain `A`. -/
abbrev RingA : Type u := pinchA K e

/-- The ring `A` is local. -/
instance : IsLocalRing (RingA K e) := isLocalRing_pinch (residueEquiv K e) (maximal_eq_or_eq K)

/-- The ring `A` is Noetherian. -/
instance : IsNoetherianRing (RingA K e) :=
  isNoetherianRing_pinch (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K)

/-- The contraction `𝔭B ∩ A` of a prime of `R`. -/
abbrev primeA (𝔭 : Ideal (R6 K)) : Ideal (RingA K e) := (ext K 𝔭).comap (pinchA K e).subtype

/-- The variable `x₂` lies in `idealM K`. -/
theorem X1_mem_idealM : (MvPolynomial.X 1 : R6 K) ∈ idealM K := Ideal.subset_span ⟨1, rfl⟩
/-- The variable `x₂` lies in `idealN K`. -/
theorem X1_mem_idealN : (MvPolynomial.X 1 : R6 K) ∈ idealN K := Ideal.subset_span (by simp)
/-- The variable `x₁` lies in `idealM K`. -/
theorem X0_mem_idealM : (MvPolynomial.X 0 : R6 K) ∈ idealM K := Ideal.subset_span ⟨0, rfl⟩
/-- The variable `x₁` lies in `idealN K`. -/
theorem X0_mem_idealN : (MvPolynomial.X 0 : R6 K) ∈ idealN K := Ideal.subset_span (by simp)

/-- A prime of `B` extended from a prime of `R` not containing `x₂` is not maximal. -/
theorem not_isMaximal_ext {𝔭 : Ideal (R6 K)} [𝔭.IsPrime] (h : 𝔭 ≤ idealM K ∨ 𝔭 ≤ idealN K)
    (hx : (MvPolynomial.X 1 : R6 K) ∉ 𝔭) : ¬ (ext K 𝔭).IsMaximal := by
  intro hmax
  refine hx ((algebraMap_mem_ext_iff K h _).mp ?_)
  rcases maximal_eq_or_eq K _ hmax with hM | hN
  · exact hM ▸ Ideal.mem_map_of_mem _ (X1_mem_idealM K)
  · exact hN ▸ Ideal.mem_map_of_mem _ (X1_mem_idealN K)

/-- The prime `idealW K` is contained in `idealM K` or in `idealN K`. -/
theorem hW : idealW K ≤ idealM K ∨ idealW K ≤ idealN K := Or.inl (idealW_le_idealM K)
/-- The prime `idealV K` is contained in `idealM K` or in `idealN K`. -/
theorem hV : idealV K ≤ idealM K ∨ idealV K ≤ idealN K := Or.inr (idealV_le_idealN K)
/-- The prime `idealC K` is contained in `idealM K` or in `idealN K`. -/
theorem hC : idealC K ≤ idealM K ∨ idealC K ≤ idealN K :=
  Or.inl ((idealC_le_idealP K).trans (idealP_le_idealM K))
/-- The prime `idealP K` is contained in `idealM K` or in `idealN K`. -/
theorem hP : idealP K ≤ idealM K ∨ idealP K ≤ idealN K := Or.inl (idealP_le_idealM K)
/-- The prime `idealQ0 K` is contained in `idealM K` or in `idealN K`. -/
theorem hQ0 : idealQ0 K ≤ idealM K ∨ idealQ0 K ≤ idealN K := Or.inl (idealQ0_le_idealM K)

/-- The extension of `idealW K` to `B` is not a maximal ideal. -/
theorem notMax_W : ¬ (ext K (idealW K)).IsMaximal :=
  not_isMaximal_ext K (hW K) (by rw [mem_idealW_iff]; simp [mapW])
/-- The extension of `idealV K` to `B` is not a maximal ideal. -/
theorem notMax_V : ¬ (ext K (idealV K)).IsMaximal :=
  not_isMaximal_ext K (hV K) (by rw [mem_idealV_iff]; simp [mapV])
/-- The extension of `idealC K` to `B` is not a maximal ideal. -/
theorem notMax_C : ¬ (ext K (idealC K)).IsMaximal :=
  not_isMaximal_ext K (hC K) (by rw [mem_idealC_iff]; simp [mapC])
/-- The extension of `idealP K` to `B` is not a maximal ideal. -/
theorem notMax_P : ¬ (ext K (idealP K)).IsMaximal :=
  not_isMaximal_ext K (hP K) (by rw [mem_idealP_iff]; simp [mapP])

/-- Nothing lies strictly between `V ∩ A` and the maximal ideal of `A`. -/
theorem primeA_V_cover (q : Ideal (RingA K e)) [q.IsPrime] (h : primeA K e (idealV K) ≤ q) :
    q = primeA K e (idealV K) ∨ q = maximalIdeal (RingA K e) := by
  by_cases hq : q = maximalIdeal (RingA K e)
  · exact Or.inr hq
  obtain ⟨Q, hQp, hQm, rfl⟩ :=
    exists_comap_eq (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) q hq
  have hVQ : ext K (idealV K) ≤ Q := (comap_le_comap_iff _ Q hQm).mp h
  left
  rcases le_extM_or_le_extN K Q with hM | hN
  · exfalso
    apply X2_sub_one_notMem_idealM K
    rw [← algebraMap_mem_ext_iff K (Or.inl le_rfl)]
    exact hM (hVQ (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))))
  · have hlt : Q < ext K (idealN K) := lt_of_le_of_ne hN fun h' => hQm (h' ▸ isMaximal_extN K)
    rw [eq_of_le_of_lt_extN K Q hVQ hlt]

/-- Nothing lies strictly between `W ∩ A` and `V ∩ A`. -/
theorem primeA_W_cover (q : Ideal (RingA K e)) [q.IsPrime] (h₁ : primeA K e (idealW K) ≤ q)
    (h₂ : q ≤ primeA K e (idealV K)) :
    q = primeA K e (idealW K) ∨ q = primeA K e (idealV K) := by
  have hq : q ≠ maximalIdeal (RingA K e) := fun hq =>
    comap_isPrime_ne_maximalIdeal (φ := residueEquiv K e) (maximal_eq_or_eq K)
      (ext K (idealV K)) (notMax_V K)
      (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) (hq ▸ h₂))
  obtain ⟨Q, hQp, hQm, rfl⟩ :=
    exists_comap_eq (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) q hq
  have hWQ : ext K (idealW K) ≤ Q := (comap_le_comap_iff _ Q hQm).mp h₁
  have hQV : Q ≤ ext K (idealV K) := (comap_le_comap_iff Q _ (notMax_V K)).mp h₂
  rcases eq_or_lt_of_le hQV with heq | hlt
  · exact Or.inr (by rw [heq])
  · exact Or.inl (by rw [eq_of_le_of_lt_extV K Q hWQ hlt])

/-- Let `𝔭 ≤ 𝔮` be primes of `R`, with `𝔭` contained in `idealM K` or in `idealN K`. If some
`a ∈ 𝔮` does not lie in `𝔭`, then `𝔭B < 𝔮B`. -/
theorem ext_lt_ext {𝔭 𝔮 : Ideal (R6 K)} [𝔭.IsPrime] [𝔮.IsPrime]
    (h𝔭 : 𝔭 ≤ idealM K ∨ 𝔭 ≤ idealN K) (hle : 𝔭 ≤ 𝔮)
    {a : R6 K} (ha𝔮 : a ∈ 𝔮) (ha𝔭 : a ∉ 𝔭) : ext K 𝔭 < ext K 𝔮 := by
  refine lt_of_le_of_ne (Ideal.map_mono hle) fun h => ha𝔭 ?_
  rw [← algebraMap_mem_ext_iff K h𝔭, h]
  exact Ideal.mem_map_of_mem _ ha𝔮

/-- `W ∩ A` is strictly contained in `C ∩ A`. -/
theorem primeA_W_lt_C : primeA K e (idealW K) < primeA K e (idealC K) :=
  comap_lt_comap (residueEquiv K e) (ext_lt_ext K (hW K) (idealW_le_idealC K)
    (a := MvPolynomial.X 3) (Ideal.subset_span (by simp)) (by rw [mem_idealW_iff]; simp [mapW]))

/-- `C ∩ A` is strictly contained in `P ∩ A`. -/
theorem primeA_C_lt_P : primeA K e (idealC K) < primeA K e (idealP K) :=
  comap_lt_comap (residueEquiv K e) (ext_lt_ext K (hC K) (idealC_le_idealP K)
    (a := MvPolynomial.X 4) (Ideal.subset_span (by simp)) (by rw [mem_idealC_iff]; simp [mapC]))

/-- `W ∩ A` is contained in `V ∩ A`. -/
theorem primeA_W_le_V : primeA K e (idealW K) ≤ primeA K e (idealV K) :=
  Ideal.comap_mono (Ideal.map_mono (idealW_le_idealV K))

/-! ### The algebraization situation -/

/-- The element `x₁ ∈ J ⊆ A`. -/
def elemF : RingA K e :=
  ⟨algebraMap (R6 K) (RingB K) (MvPolynomial.X 0),
    mem_pinch_of_mem_inf _ _ _ (Ideal.mem_inf.mpr
      ⟨Ideal.mem_map_of_mem (algebraMap (R6 K) (RingB K)) (X0_mem_idealM K),
        Ideal.mem_map_of_mem (algebraMap (R6 K) (RingB K)) (X0_mem_idealN K)⟩)⟩

/-- If `x₁ ∈ 𝔭`, then `x₁ ∈ 𝔭B ∩ A`. -/
theorem elemF_mem_primeA {𝔭 : Ideal (R6 K)} (h : (MvPolynomial.X 0 : R6 K) ∈ 𝔭) :
    elemF K e ∈ primeA K e 𝔭 :=
  Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap (R6 K) (RingB K)) h)

/-- `x₁ ∈ W ∩ A`. -/
theorem elemF_mem_primeA_W : elemF K e ∈ primeA K e (idealW K) :=
  elemF_mem_primeA K e (Ideal.subset_span (Set.mem_singleton _))

/-- The ideal `𝔟 = (Q₀B ∩ WB) ∩ A`. -/
def idealB : Ideal (RingA K e) :=
  (ext K (idealQ0 K) ⊓ ext K (idealW K)).comap (pinchA K e).subtype

/-- `𝔟 ⊆ W ∩ A`. -/
theorem idealB_le_primeA_W : idealB K e ≤ primeA K e (idealW K) :=
  Ideal.comap_mono inf_le_right

/-- The local ring `A'' = A/𝔟` of the counterexample. -/
abbrev RingA2 : Type u := RingA K e ⧸ idealB K e

/-- The ring `A''` is nontrivial. -/
instance : Nontrivial (RingA2 K e) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h =>
    (Ideal.IsPrime.ne_top (inferInstance : (primeA K e (idealW K)).IsPrime))
      (top_le_iff.mp (h ▸ idealB_le_primeA_W K e))

/-- The ring `A''` is local. -/
instance : IsLocalRing (RingA2 K e) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The ideal `I = (x₁)` of `A''`. -/
abbrev idealI : Ideal (RingA2 K e) := Ideal.span {Ideal.Quotient.mk (idealB K e) (elemF K e)}

/-- The ideal `I` is contained in the maximal ideal of `A''`. -/
theorem idealI_le_maximalIdeal : idealI K e ≤ maximalIdeal (RingA2 K e) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine (mem_maximalIdeal _).mpr fun hu => ?_
  have hprime : ((primeA K e (idealW K)).map (Ideal.Quotient.mk (idealB K e))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by simpa using idealB_le_primeA_W K e)
  exact hprime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (elemF_mem_primeA_W K e)) hu)

/-- The ring `A''/I` is nontrivial. -/
instance : Nontrivial (RingA2 K e ⧸ idealI K e) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h =>
    (Ideal.IsPrime.ne_top (inferInstance : (maximalIdeal (RingA2 K e)).IsPrime))
      (top_le_iff.mp (h ▸ idealI_le_maximalIdeal K e))

/-- The ring `A''/I` is local. -/
instance : IsLocalRing (RingA2 K e ⧸ idealI K e) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The algebraization situation of the counterexample: `A''`, `I = (x₁)`, `𝔞 = 𝔪_{A''}`. -/
abbrev situation : Stacks.Algebraization.AlgebraizationSituation.{u} where
  A := RingA2 K e
  I := idealI K e
  a := maximalIdeal (RingA2 K e)
  I_le_a := idealI_le_maximalIdeal K e

/-- The surjection `A → A''/I`. -/
def toY : RingA K e →+* RingA2 K e ⧸ idealI K e :=
  (Ideal.Quotient.mk (idealI K e)).comp (Ideal.Quotient.mk (idealB K e))

/-- The map `A → A''/I` is surjective. -/
theorem toY_surjective : Function.Surjective (toY K e) :=
  Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective

/-- The kernel of `A → A''/I` is contained in every ideal of `A` containing `𝔟` and `x₁`. -/
theorem ker_toY_le {q : Ideal (RingA K e)} (hb : idealB K e ≤ q) (hf : elemF K e ∈ q) :
    RingHom.ker (toY K e) ≤ q := by
  intro a ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  have h2 : c' * elemF K e - a ∈ idealB K e := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
    exact sub_eq_zero.mpr hc
  simpa using q.sub_mem (q.mul_mem_left c' hf) (hb h2)

/-- `x₁` lies in the kernel of `A → A''/I`. -/
theorem elemF_mem_ker_toY : elemF K e ∈ RingHom.ker (toY K e) := by
  rw [RingHom.mem_ker, toY, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- `𝔟` is contained in the kernel of `A → A''/I`. -/
theorem idealB_le_ker_toY : idealB K e ≤ RingHom.ker (toY K e) := by
  intro a ha
  rw [RingHom.mem_ker, toY, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The point of `Y` given by a prime of `A` containing `W ∩ A`. -/
def pointY (q : Ideal (RingA K e)) [q.IsPrime] (hq : primeA K e (idealW K) ≤ q) :
    PrimeSpectrum (RingA2 K e ⧸ idealI K e) :=
  ⟨q.map (toY K e), Ideal.map_isPrime_of_surjective (toY_surjective K e)
    (ker_toY_le K e ((idealB_le_primeA_W K e).trans hq) (hq (elemF_mem_primeA_W K e)))⟩

/-- The preimage in `A` of the point `pointY K e q hq` is `q`. -/
theorem comap_pointY (q : Ideal (RingA K e)) [q.IsPrime] (hq : primeA K e (idealW K) ≤ q) :
    (pointY K e q hq).asIdeal.comap (toY K e) = q := by
  change (q.map (toY K e)).comap (toY K e) = q
  rw [Ideal.comap_map_of_surjective _ (toY_surjective K e), sup_eq_left,
    ← RingHom.ker_eq_comap_bot]
  exact ker_toY_le K e ((idealB_le_primeA_W K e).trans hq) (hq (elemF_mem_primeA_W K e))

/-- Every prime of `A` containing `𝔟` and `x₁` contains `W ∩ A`. -/
theorem primeA_W_le (q : Ideal (RingA K e)) [q.IsPrime] (hb : idealB K e ≤ q)
    (hf : elemF K e ∈ q) : primeA K e (idealW K) ≤ q := by
  have hprod : primeA K e (idealQ0 K) * primeA K e (idealW K) ≤ q := by
    refine le_trans ?_ hb
    intro x hx
    refine Ideal.mul_le.mpr (fun a ha b hb' => ?_) hx
    exact Ideal.mem_comap.mpr ⟨by simpa using Ideal.mul_mem_right _ _ ha,
      by simpa using Ideal.mul_mem_left _ _ hb'⟩
  rcases (Ideal.IsPrime.mul_le (inferInstance : q.IsPrime)).mp hprod with hQ | hW
  · by_cases hm : q = maximalIdeal (RingA K e)
    · exact hm ▸ le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    obtain ⟨Q, hQp, hQm, rfl⟩ :=
      exists_comap_eq (residueEquiv K e) (extM_ne_extN K) (maximal_eq_or_eq K) q hm
    have hQ0 : ext K (idealQ0 K) ≤ Q := (comap_le_comap_iff _ Q hQm).mp hQ
    refine (comap_le_comap_iff _ Q hQm).mpr ?_
    rw [Ideal.map_le_iff_le_comap, idealW, Ideal.span_le, Set.singleton_subset_iff]
    exact hf
  · exact hW

/-- Every point `x` of `Y` is the point `pointY` of its preimage in `A`. -/
theorem eq_pointY (x : PrimeSpectrum (RingA2 K e ⧸ idealI K e)) :
    ∃ hq : primeA K e (idealW K) ≤ x.asIdeal.comap (toY K e),
      x = pointY K e (x.asIdeal.comap (toY K e)) hq := by
  refine ⟨primeA_W_le K e _ ((idealB_le_ker_toY K e).trans (Ideal.comap_mono bot_le))
    (Ideal.comap_mono bot_le (elemF_mem_ker_toY K e)), ?_⟩
  ext1
  change x.asIdeal = (x.asIdeal.comap (toY K e)).map (toY K e)
  rw [Ideal.map_comap_of_surjective _ (toY_surjective K e)]

/-- `pointY K e q hq ≤ pointY K e q' hq'` if and only if `q ≤ q'`. -/
theorem pointY_le_iff {q q' : Ideal (RingA K e)} [q.IsPrime] [q'.IsPrime]
    (hq : primeA K e (idealW K) ≤ q) (hq' : primeA K e (idealW K) ≤ q') :
    pointY K e q hq ≤ pointY K e q' hq' ↔ q ≤ q' := by
  refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
  rw [← comap_pointY K e q hq, ← comap_pointY K e q' hq']
  exact Ideal.comap_mono h

/-- `pointY K e q hq = pointY K e q' hq'` implies `q = q'`. -/
theorem pointY_injective {q q' : Ideal (RingA K e)} [q.IsPrime] [q'.IsPrime]
    (hq : primeA K e (idealW K) ≤ q) (hq' : primeA K e (idealW K) ≤ q')
    (h : pointY K e q hq = pointY K e q' hq') : q = q' := by
  rw [← comap_pointY K e q hq, ← comap_pointY K e q' hq', h]

/-- Equal primes `q = q'` give equal points `pointY K e q hq = pointY K e q' hq'`. -/
theorem pointY_congr {q q' : Ideal (RingA K e)} [q.IsPrime] [q'.IsPrime]
    {hq : primeA K e (idealW K) ≤ q} {hq' : primeA K e (idealW K) ≤ q'} (h : q = q') :
    pointY K e q hq = pointY K e q' hq' := by
  subst h
  rfl

/-- The point `w` of `Y` given by `W ∩ A`. -/
abbrev ptW := pointY K e (primeA K e (idealW K)) le_rfl
/-- The point `v` of `Y` given by `V ∩ A`. -/
abbrev ptV := pointY K e (primeA K e (idealV K)) (primeA_W_le_V K e)
/-- The point `c` of `Y` given by `C ∩ A`. -/
abbrev ptC := pointY K e (primeA K e (idealC K)) (primeA_W_lt_C K e).le
/-- The point `y` of `Y` given by `P ∩ A`. -/
abbrev ptP := pointY K e (primeA K e (idealP K)) ((primeA_W_lt_C K e).trans (primeA_C_lt_P K e)).le

/-- The closed point of `Y` is a maximal ideal of `A''/I`. -/
instance : (closedPoint (RingA2 K e ⧸ idealI K e)).asIdeal.IsMaximal :=
  inferInstanceAs (maximalIdeal (RingA2 K e ⧸ idealI K e)).IsMaximal

/-- The preimage in `A` of the closed point of `Y` is the maximal ideal of `A`. -/
theorem comap_closedPoint :
    (closedPoint (RingA2 K e ⧸ idealI K e)).asIdeal.comap (toY K e) = maximalIdeal (RingA K e) :=
  IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ (toY_surjective K e))

/-- The distance function of the algebraization situation satisfies `δ^Y_Z(P) ≤ 2` at the point
`P` of `Y`. -/
theorem distanceToZ_ptP_le_two : (situation K e).distanceToZ (ptP K e) ≤ 2 := by
  classical
  let Y := (situation K e).Y
  let z0 : Y := closedPoint (RingA2 K e ⧸ idealI K e)
  have spec_iff : ∀ a b : PrimeSpectrum (RingA2 K e ⧸ idealI K e),
      ((a : Y) ⤳ (b : Y)) ↔ a ≤ b := fun a b => (PrimeSpectrum.le_iff_specializes a b).symm
  have hz0 : z0 ∈ ((situation K e).closedSubsetZ : Set Y) := by
    change (maximalIdeal (RingA2 K e)).map (Ideal.Quotient.mk (idealI K e)) ≤
      (closedPoint (RingA2 K e ⧸ idealI K e)).asIdeal
    exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)).symm)
  have hle_closed : ∀ a : PrimeSpectrum (RingA2 K e ⧸ idealI K e), a ≤ closedPoint _ :=
    fun a => le_maximalIdeal (Ideal.IsPrime.ne_top a.isPrime)
  refine Stacks.Algebraization.distanceFunction_le_two_of_zigzag (situation K e).Y
    (Z := (situation K e).closedSubsetZ)
    (z := z0) (v := ptV K e) (w := ptW K e) (c := ptC K e) (y := ptP K e) hz0
    ((spec_iff _ _).mpr (hle_closed _)) ?_ ((spec_iff _ _).mpr ((pointY_le_iff K e _ _).mpr
      (primeA_W_le_V K e))) ?_ ((spec_iff _ _).mpr ((pointY_le_iff K e _ _).mpr
      (primeA_W_lt_C K e).le)) ((spec_iff _ _).mpr ((pointY_le_iff K e _ _).mpr
      (primeA_C_lt_P K e).le)) ?_ ?_
  · intro x hvx hxz
    have : (x : PrimeSpectrum (RingA2 K e ⧸ idealI K e)).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime x
    have : (Ideal.comap (toY K e) x.asIdeal).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨hq, hx⟩ := eq_pointY K e x
    have h1 : primeA K e (idealV K) ≤ x.asIdeal.comap (toY K e) :=
      (pointY_le_iff K e _ hq).mp ((spec_iff _ _).mp (hx ▸ hvx))
    rcases primeA_V_cover K e _ h1 with h | h
    · exact Or.inl (hx.trans (pointY_congr K e h))
    · right
      apply PrimeSpectrum.ext
      rw [← Ideal.map_comap_of_surjective _ (toY_surjective K e) x.asIdeal, h,
        ← comap_closedPoint K e, Ideal.map_comap_of_surjective _ (toY_surjective K e)]
  · intro x hwx hxv
    have : (x : PrimeSpectrum (RingA2 K e ⧸ idealI K e)).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime x
    have : (Ideal.comap (toY K e) x.asIdeal).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨hq, hx⟩ := eq_pointY K e x
    have h1 := (pointY_le_iff K e _ hq).mp ((spec_iff _ _).mp (hx ▸ hwx))
    have h2 := (pointY_le_iff K e hq _).mp ((spec_iff _ _).mp (hx ▸ hxv))
    rcases primeA_W_cover K e _ h1 h2 with h | h
    · exact Or.inl (hx.trans (pointY_congr K e h))
    · exact Or.inr (hx.trans (pointY_congr K e h))
  · intro h
    exact (primeA_W_lt_C K e).ne (pointY_injective K e _ _ h)
  · intro h
    exact (primeA_C_lt_P K e).ne (pointY_injective K e _ _ h)

end Stacks.NonCatenaryExample

end
