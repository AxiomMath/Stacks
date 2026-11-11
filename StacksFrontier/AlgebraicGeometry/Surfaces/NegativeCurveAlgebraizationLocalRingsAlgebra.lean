module

public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Local rings with a common tower of quotients have isomorphic completions

Let `R` and `S` be local rings and let `(Tₙ)` be a tower of rings, with transition maps
`Tₙ₊₁ ⟶ Tₙ`, together with compatible surjections `R ⟶ Tₙ` and `S ⟶ Tₙ` whose kernels lie in
`𝔪_R ^ (n + 1)` and `𝔪_S ^ (n + 1)` respectively. Then `R ⧸ 𝔪_R ^ n ≅ Tₙ ⧸ 𝔪_{Tₙ} ^ n ≅
S ⧸ 𝔪_S ^ n` compatibly in `n`, so the completions of `R` and `S` at their maximal ideals are
isomorphic. For Noetherian `R` and `S` it follows that they have the same Krull dimension
(Stacks 07NV) and that `R` is regular if and only if `S` is (Stacks 07NY).

This is the algebra behind the comparison, in the construction of Stacks 0D5E, of the local
rings of the algebraization `Y ⟶ Spec A` of the formal neighbourhood of a curve `C` in a surface
`X` with those of `X` along `C`: both surject onto the local rings of the members
`Xₙ = Y ×_{Spec A} Spec (A ⧸ 𝔪ⁿ⁺¹)` of the adic tower.

## Main definitions

* `IsLocalRing.quotientMaximalIdealPowEquiv`: for a surjection `f : R ⟶ T` of local rings with
  kernel in `𝔪_R ^ k`, the isomorphism `R ⧸ 𝔪_R ^ k ≅ T ⧸ 𝔪_T ^ k`.
* `IsLocalRing.adicCompletionRingEquivOfTower`: the isomorphism of completions.

## Main results

* `IsLocalRing.ringKrullDim_eq_of_tower`: `R` and `S` have the same Krull dimension.
* `IsLocalRing.isRegularLocalRing_iff_of_tower`: `R` is regular if and only if `S` is.

## References

* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

section QuotientEquiv

variable {R T : Type*} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]

/-- For a surjection `f : R ⟶ T` of local rings, `𝔪_R ^ k` lies in the inverse image of
`𝔪_T ^ k`. -/
theorem maximalIdeal_pow_le_comap (f : R →+* T) (hf : Function.Surjective f) (k : ℕ) :
    maximalIdeal R ^ k ≤ (maximalIdeal T ^ k).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_maximalIdeal_of_surjective f hf]

/-- For a surjection `f : R ⟶ T` of local rings whose kernel lies in `𝔪_R ^ k`, the induced map
`R ⧸ 𝔪_R ^ k ⟶ T ⧸ 𝔪_T ^ k` is bijective. -/
theorem bijective_quotientMap_maximalIdeal_pow (f : R →+* T) (hf : Function.Surjective f)
    (k : ℕ) (hk : RingHom.ker f ≤ maximalIdeal R ^ k) :
    Function.Bijective
      (Ideal.quotientMap (maximalIdeal T ^ k) f (maximalIdeal_pow_le_comap f hf k)) := by
  refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective hf⟩
  rw [← map_maximalIdeal_of_surjective f hf, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective' f hf]
  exact sup_le le_rfl hk

/-- For a surjection `f : R ⟶ T` of local rings whose kernel lies in `𝔪_R ^ k`, the isomorphism
`R ⧸ 𝔪_R ^ k ≅ T ⧸ 𝔪_T ^ k`. -/
def quotientMaximalIdealPowEquiv (f : R →+* T) (hf : Function.Surjective f) (k : ℕ)
    (hk : RingHom.ker f ≤ maximalIdeal R ^ k) :
    R ⧸ maximalIdeal R ^ k ≃+* T ⧸ maximalIdeal T ^ k :=
  RingEquiv.ofBijective _ (bijective_quotientMap_maximalIdeal_pow f hf k hk)

/-- `quotientMaximalIdealPowEquiv` sends the class of `r` to the class of `f r`. -/
@[simp]
theorem quotientMaximalIdealPowEquiv_mk (f : R →+* T) (hf : Function.Surjective f) (k : ℕ)
    (hk : RingHom.ker f ≤ maximalIdeal R ^ k) (r : R) :
    quotientMaximalIdealPowEquiv f hf k hk (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (f r) :=
  rfl

end QuotientEquiv

section Tower

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  {T : ℕ → Type*} [∀ n, CommRing (T n)] [∀ n, IsLocalRing (T n)]
  (π : ∀ n, T (n + 1) →+* T n) (φ : ∀ n, R →+* T n) (ψ : ∀ n, S →+* T n)
  (hφ : ∀ n, (π n).comp (φ (n + 1)) = φ n) (hψ : ∀ n, (π n).comp (ψ (n + 1)) = ψ n)
  (hφs : ∀ n, Function.Surjective (φ n)) (hψs : ∀ n, Function.Surjective (ψ n))
  (hφk : ∀ n, RingHom.ker (φ n) ≤ maximalIdeal R ^ (n + 1))
  (hψk : ∀ n, RingHom.ker (ψ n) ≤ maximalIdeal S ^ (n + 1))

/-- The isomorphism `R ⧸ 𝔪_R ^ n ≅ S ⧸ 𝔪_S ^ n` through `Tₙ ⧸ 𝔪_{Tₙ} ^ n`. -/
def quotientPowEquivOfTower (n : ℕ) : R ⧸ maximalIdeal R ^ n ≃+* S ⧸ maximalIdeal S ^ n :=
  (quotientMaximalIdealPowEquiv (φ n) (hφs n) n
      ((hφk n).trans (Ideal.pow_le_pow_right n.le_succ))).trans
    (quotientMaximalIdealPowEquiv (ψ n) (hψs n) n
      ((hψk n).trans (Ideal.pow_le_pow_right n.le_succ))).symm

/-- `quotientPowEquivOfTower` sends the class of `r` to the class of `s` exactly when `r` and `s`
have the same image in `Tₙ ⧸ 𝔪_{Tₙ} ^ n`. -/
theorem quotientPowEquivOfTower_mk_eq_mk_iff (n : ℕ) (r : R) (s : S) :
    quotientPowEquivOfTower φ ψ hφs hψs hφk hψk n (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ s ↔ φ n r - ψ n s ∈ maximalIdeal (T n) ^ n := by
  rw [quotientPowEquivOfTower, RingEquiv.trans_apply, RingEquiv.symm_apply_eq,
    quotientMaximalIdealPowEquiv_mk, quotientMaximalIdealPowEquiv_mk, Ideal.Quotient.eq]

include hφ hψ in
/-- The isomorphisms `quotientPowEquivOfTower` are compatible with the transition maps. -/
theorem factorPow_quotientPowEquivOfTower (n : ℕ) (x : R ⧸ maximalIdeal R ^ (n + 1)) :
    Ideal.Quotient.factorPow (maximalIdeal S) n.le_succ
        (quotientPowEquivOfTower φ ψ hφs hψs hφk hψk (n + 1) x) =
      quotientPowEquivOfTower φ ψ hφs hψs hφk hψk n
        (Ideal.Quotient.factorPow (maximalIdeal R) n.le_succ x) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    (quotientPowEquivOfTower φ ψ hφs hψs hφk hψk (n + 1) (Ideal.Quotient.mk _ r))
  have h := (quotientPowEquivOfTower_mk_eq_mk_iff φ ψ hφs hψs hφk hψk (n + 1) r s).mp hs.symm
  rw [← hs, Ideal.Quotient.factorPow, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.Quotient.factor_mk, eq_comm,
    quotientPowEquivOfTower_mk_eq_mk_iff φ ψ hφs hψs hφk hψk n r s]
  have hπ : (maximalIdeal (T (n + 1))).map (π n) = maximalIdeal (T n) := by
    rw [← map_maximalIdeal_of_surjective (φ (n + 1)) (hφs (n + 1)), Ideal.map_map, hφ n,
      map_maximalIdeal_of_surjective (φ n) (hφs n)]
  have hmem := Ideal.mem_map_of_mem (π n) h
  rw [Ideal.map_pow, hπ, map_sub, ← RingHom.comp_apply, ← RingHom.comp_apply, hφ n,
    hψ n] at hmem
  exact Ideal.pow_le_pow_right n.le_succ hmem

/-- Compatibility of a family of maps into the quotients `S ⧸ I ^ n` along all the transition
maps, from compatibility along consecutive ones. -/
theorem factorPow_comp_eq_of_succ {A B : Type*} [CommRing A] [CommRing B] (I : Ideal B)
    (f : ∀ n, A →+* B ⧸ I ^ n)
    (hf : ∀ n, (Ideal.Quotient.factorPow I n.le_succ).comp (f (n + 1)) = f n)
    {m n : ℕ} (hmn : m ≤ n) : (Ideal.Quotient.factorPow I hmn).comp (f n) = f m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    ext a
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f m a)
    rw [RingHom.comp_apply, ← hb, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  | succ n hmn ih =>
    rw [← ih, ← hf n, ← RingHom.comp_assoc]
    ext a
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (f (n + 1) a)
    simp only [RingHom.comp_apply, ← hc, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]

/-- The map `R^ ⟶ S ⧸ 𝔪_S ^ n` from the completion of `R`, through `R ⧸ 𝔪_R ^ n`. -/
def adicCompletionToQuotientPow (n : ℕ) :
    AdicCompletion (maximalIdeal R) R →+* S ⧸ maximalIdeal S ^ n :=
  (quotientPowEquivOfTower φ ψ hφs hψs hφk hψk n).toRingHom.comp
    (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom

include hφ hψ in
/-- The maps `adicCompletionToQuotientPow` are compatible. -/
theorem factorPow_comp_adicCompletionToQuotientPow {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal S) hmn).comp
        (adicCompletionToQuotientPow φ ψ hφs hψs hφk hψk n) =
      adicCompletionToQuotientPow φ ψ hφs hψs hφk hψk m := by
  refine factorPow_comp_eq_of_succ _ _ (fun n => ?_) hmn
  ext x
  simp only [adicCompletionToQuotientPow, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgHom.coe_toRingHom]
  rw [factorPow_quotientPowEquivOfTower π φ ψ hφ hψ hφs hψs hφk hψk n]
  congr 1
  obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  exact (AdicCompletion.Ideal.mk_eq_mk (maximalIdeal R) n.le_succ y)

include hφ hψ in
/-- The ring map `R^ ⟶ S^` of completions induced by the tower. -/
def adicCompletionHomOfTower :
    AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal S) S :=
  AdicCompletion.liftRingHom (maximalIdeal S) (adicCompletionToQuotientPow φ ψ hφs hψs hφk hψk)
    (factorPow_comp_adicCompletionToQuotientPow π φ ψ hφ hψ hφs hψs hφk hψk)

/-- The ring map of completions commutes with the projections to `R ⧸ 𝔪_R ^ n` and
`S ⧸ 𝔪_S ^ n`. -/
theorem evalₐ_adicCompletionHomOfTower (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) :
    AdicCompletion.evalₐ (maximalIdeal S) n
        (adicCompletionHomOfTower π φ ψ hφ hψ hφs hψs hφk hψk x) =
      quotientPowEquivOfTower φ ψ hφs hψs hφk hψk n
        (AdicCompletion.evalₐ (maximalIdeal R) n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ n x

/-- **Local rings with a common tower of quotients have isomorphic completions.** Let `R`, `S`
be local rings and `(Tₙ)` a tower of local rings with compatible surjections `R ⟶ Tₙ`,
`S ⟶ Tₙ` whose kernels lie in `𝔪_R ^ (n + 1)` and `𝔪_S ^ (n + 1)`. Then the completions of
`R` and `S` at their maximal ideals are isomorphic. -/
def adicCompletionRingEquivOfTower :
    AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S where
  toFun := adicCompletionHomOfTower π φ ψ hφ hψ hφs hψs hφk hψk
  invFun := adicCompletionHomOfTower π ψ φ hψ hφ hψs hφs hψk hφk
  left_inv x := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_adicCompletionHomOfTower, evalₐ_adicCompletionHomOfTower]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n x)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      (quotientPowEquivOfTower φ ψ hφs hψs hφk hψk n (Ideal.Quotient.mk _ r))
    rw [← hr, ← hs]
    have h := (quotientPowEquivOfTower_mk_eq_mk_iff φ ψ hφs hψs hφk hψk n r s).mp hs.symm
    refine (quotientPowEquivOfTower_mk_eq_mk_iff ψ φ hψs hφs hψk hφk n s r).mpr ?_
    rw [← neg_sub]
    exact neg_mem h
  right_inv x := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_adicCompletionHomOfTower, evalₐ_adicCompletionHomOfTower]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal S) n x)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (quotientPowEquivOfTower ψ φ hψs hφs hψk hφk n (Ideal.Quotient.mk _ s))
    rw [← hs, ← hr]
    have h := (quotientPowEquivOfTower_mk_eq_mk_iff ψ φ hψs hφs hψk hφk n s r).mp hr.symm
    refine (quotientPowEquivOfTower_mk_eq_mk_iff φ ψ hφs hψs hφk hψk n r s).mpr ?_
    rw [← neg_sub]
    exact neg_mem h
  map_mul' := map_mul _
  map_add' := map_add _

variable [IsNoetherianRing R] [IsNoetherianRing S]

include hφ hψ hφs hψs hφk hψk in
/-- **Local rings with a common tower of quotients have the same dimension**: the completions
are isomorphic, and completion does not change the dimension (Stacks 07NV). -/
theorem ringKrullDim_eq_of_tower : ringKrullDim R = ringKrullDim S := by
  rw [ringKrullDim_adicCompletion_maximalIdeal (A := R),
    ringKrullDim_adicCompletion_maximalIdeal (A := S)]
  exact ringKrullDim_eq_of_ringEquiv
    (adicCompletionRingEquivOfTower π φ ψ hφ hψ hφs hψs hφk hψk)

include hφ hψ hφs hψs hφk hψk in
/-- **Local rings with a common tower of quotients are regular together**: the completions are
isomorphic, and a Noetherian local ring is regular exactly when its completion is
(Stacks 07NY). -/
theorem isRegularLocalRing_iff_of_tower : IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  rw [isRegularLocalRing_iff_adicCompletion_maximalIdeal (A := R),
    isRegularLocalRing_iff_adicCompletion_maximalIdeal (A := S)]
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv
      (adicCompletionRingEquivOfTower π φ ψ hφ hψ hφs hψs hφk hψk),
    fun _ => IsRegularLocalRing.of_ringEquiv
      (adicCompletionRingEquivOfTower π φ ψ hφ hψ hφs hψs hφk hψk).symm⟩

end Tower

end IsLocalRing

end
