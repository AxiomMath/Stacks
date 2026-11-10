module

public import StacksFrontier.RingTheory.Invariant.InertiaFixedField
public import StacksFrontier.RingTheory.Invariant.DecompositionFixedField
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A strict henselization inside a separable closure, and the Frobenius on it

Let `A` be a normal local domain with fraction field `K`, `L` a separable closure of `K`, `B` the
integral closure of `A` in `L`, `q` a prime of `B` over the maximal ideal of `A` with inertia
group `I`, and `H` a strict henselization of `A` (a henselian local ind-étale `A`-algebra whose
residue field is a separable closure of that of `A`). By the uniqueness of strict henselizations
(Stacks 08HT) and `(B_q)^I = A^{sh}` (`IsIntegralClosure.isHenselization_inertiaInvariants`),
`H` is `A`-isomorphic to `(B_q)^I`, so a fraction field of `H` embeds into `L` with image the
inertia field `L^I`.

If moreover `θ` is a local `A`-endomorphism of `H` whose residue map is an inverse of the
`Q`-th power map, and `Fr ∈ Gal(L/K)` stabilizes `q` and raises to the `Q`-th power modulo `q`
(an arithmetic Frobenius at `q`), then `Fr ∘ Φ ∘ θ = Φ` for every `A`-algebra map
`Φ : H → B_q` into the strictly henselian ring `B_q` (Stacks 04GU, uniqueness). This is how the
Frobenius of a strict henselization at a point of a curve over a finite field is read inside
`Gal(L/K)` (Weil II 1.8).

## Main results

* `IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale` — `H ≃ₐ[A] (B_q)^I`.
* `IsIntegralClosure.exists_ringHom_fractionRing_range_eq_inertiaFixedField` — a fraction field
  of `H` embeds into `L` with image `L^I`, extending `H ≃ (B_q)^I`.
* `IsIntegralClosure.residue_localizedSubringEquivOfStabilizes` — an arithmetic Frobenius raises
  to the `Q`-th power on the residue field of `B_q`.
* `IsIntegralClosure.galAction_comp_comp_eq_of_residue_pow` — `Fr ∘ Φ ∘ θ = Φ`.

## References

* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped Pointwise

universe u

namespace IsIntegralClosure

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

attribute [local instance] galAction galSMulCommClass

/-! ### The strict henselization as the inertia invariants -/

section Embedding

variable [IsSepClosed L] (q : Ideal (integralClosure A L)) [q.IsPrime]
  [q.LiesOver (maximalIdeal A)]
  (H : Type u) [CommRing H] [IsLocalRing H] [Algebra A H] [IsLocalHom (algebraMap A H)]

/-- **A strict henselization of `A` is `A`-isomorphic to `(B_q)^I`** (Stacks 08HT): both are
henselian local ind-étale `A`-algebras whose residue fields are separable closures of the residue
field of `A`. -/
@[ega "IV 18.8.8.1" "special case"]
theorem nonempty_algEquiv_inertiaInvariants_of_indEtale [HenselianLocalRing H]
    (hH : StacksDraft.IndEtale A H) [IsSepClosure (ResidueField A) (ResidueField H)] :
    Nonempty (H ≃ₐ[A] inertiaInvariants A K L q) := by
  obtain ⟨hR, _⟩ := isHenselization_inertiaInvariants A K L q
  have : HenselianLocalRing (inertiaInvariants A K L q) := hR.henselian
  let e : ResidueField H ≃ₐ[ResidueField A] ResidueField (inertiaInvariants A K L q) :=
    IsSepClosure.equiv (ResidueField A) (ResidueField H) (ResidueField (inertiaInvariants A K L q))
  obtain ⟨Φ, -⟩ := IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv
    (R := A) (A := H) (B := inertiaInvariants A K L q) (K := ResidueField H) hH hR.ind_etale
    (RingEquiv.refl _) e.toRingEquiv (fun r => by
      change residue H (algebraMap A H r) = e.symm (residue _ (algebraMap A _ r))
      rw [← ResidueField.algebraMap_residue, ← ResidueField.algebraMap_residue, ← e.commutes,
        AlgEquiv.symm_apply_apply])
  exact ⟨Φ⟩

omit [IsIntegrallyClosed A] [IsLocalRing A] [IsSepClosed L] [q.LiesOver (maximalIdeal A)]
  [IsLocalRing H] [IsLocalHom (algebraMap A H)] in
/-- **A fraction field of a strict henselization of `A` embeds into `L` with image the inertia
field `L^I`**, extending a given `A`-isomorphism `H ≃ (B_q)^I`. -/
theorem exists_ringHom_fractionRing_range_eq_inertiaFixedField
    (Φ : H ≃ₐ[A] inertiaInvariants A K L q) (Ksh : Type u) [Field Ksh] [Algebra H Ksh]
    [IsFractionRing H Ksh] :
    ∃ ι : Ksh →+* L, (∀ h : H, ι (algebraMap H Ksh h) = ((Φ h : localizedSubring q) : L)) ∧
      Set.range ι = (inertiaFixedField A K L q : Set L) := by
  have := isFractionRing_inertiaFixedField A K L q
  let e : Ksh ≃+* inertiaFixedField A K L q :=
    IsFractionRing.ringEquivOfRingEquiv (A := H) (B := inertiaInvariants A K L q) Φ.toRingEquiv
  refine ⟨(inertiaFixedField A K L q).val.toRingHom.comp e.toRingHom, fun h => ?_, ?_⟩
  · change ((e (algebraMap H Ksh h) : inertiaFixedField A K L q) : L) = _
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact coe_algebraMap_inertiaFixedField A K L q _
  · ext z
    refine ⟨?_, fun hz => ⟨e.symm ⟨z, hz⟩, by simp⟩⟩
    rintro ⟨w, rfl⟩
    exact (e w).2

end Embedding

/-! ### The Frobenius on the localization `B_q` -/

section Frobenius

variable (q : Ideal (integralClosure A L)) [q.IsPrime]

omit [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] in
/-- **An arithmetic Frobenius at `q` raises to the `Q`-th power on the residue field of `B_q`.**
If `σ` stabilizes `q` and `σ b - b ^ Q ∈ q` for every `b ∈ B`, then for `x = b / s` in `B_q`,
`(σ x - x ^ Q) · σ s · s ^ Q = (σ b - b ^ Q) s ^ Q + b ^ Q (s ^ Q - σ s)` has numerator in `q`
and denominator outside `q`. -/
theorem residue_localizedSubringEquivOfStabilizes (σ : Gal(L/K)) (hσ : σ • q = q) (Q : ℕ)
    (hFr : ∀ b : integralClosure A L, σ • b - b ^ Q ∈ q) (x : localizedSubring q) :
    residue (localizedSubring q) (localizedSubringEquivOfStabilizes A K L q hσ x) =
      residue (localizedSubring q) x ^ Q := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  obtain ⟨b, s, hs, hbs⟩ := x.2
  have hs' : s ^ Q - σ • s ∈ q := by simpa using q.neg_mem (hFr s)
  have hσbs : σ (x : L) * σ (s : L) = σ (b : L) := by rw [← map_mul, hbs]
  refine mem_maximalIdeal_localizedSubring q
    (n := (σ • b - b ^ Q) * s ^ Q + b ^ Q * (s ^ Q - σ • s))
    (d := (σ • s) * s ^ Q)
    (q.add_mem (q.mul_mem_right _ (hFr b)) (q.mul_mem_left _ hs'))
    (q.primeCompl.mul_mem (notMem_smul_of_notMem A K L hσ hs) (q.primeCompl.pow_mem hs Q)) ?_
  push_cast [coe_localizedSubringEquivOfStabilizes, coe_smul A K L]
  have hbsQ : (x : L) ^ Q * (s : L) ^ Q = (b : L) ^ Q := by rw [← mul_pow, hbs]
  linear_combination ((s : L) ^ Q) * hσbs - (σ (s : L)) * hbsQ

omit [IsIntegrallyClosed A] [IsLocalRing A] in
/-- **The Frobenius on a strict henselization, read in `B_q`** (Stacks 04GU, uniqueness). Let
`Φ : H → B_q` be an `A`-algebra map from a henselian local ind-étale `A`-algebra, local, and `θ`
a local `A`-endomorphism of `H` whose residue map is inverse to the `Q`-th power map. For an
arithmetic Frobenius `σ` at `q`, the two local maps `σ ∘ Φ ∘ θ` and `Φ` induce the same map on
residue fields, hence are equal. -/
theorem galAction_comp_comp_eq_of_residue_pow [IsSepClosed L] (H : Type u) [CommRing H]
    [IsLocalRing H] [Algebra A H] (hH : StacksDraft.IndEtale A H)
    (Φ : H →ₐ[A] localizedSubring q) [IsLocalHom Φ]
    (θ : H →ₐ[A] H) [IsLocalHom θ] (σ : Gal(L/K)) (hσ : σ • q = q) (Q : ℕ)
    (hFr : ∀ b : integralClosure A L, σ • b - b ^ Q ∈ q)
    (hθ : ∀ h : H, residue H (θ h) ^ Q = residue H h) (h : H) :
    σ ((Φ (θ h) : localizedSubring q) : L) = ((Φ h : localizedSubring q) : L) := by
  let := (henselianLocalRing_and_isSepClosed_localizedSubring A K L q).1
  let f₁ : H →ₐ[A] localizedSubring q :=
    (localizedSubringEquivOfStabilizes A K L q hσ).toAlgHom.comp (Φ.comp θ)
  have : IsLocalHom f₁ := ⟨fun z hz => isUnit_of_map_unit θ z (isUnit_of_map_unit Φ _
    ((isUnit_map_iff (localizedSubringEquivOfStabilizes A K L q hσ) _).mp hz))⟩
  let φ : ResidueField H →+* ResidueField (localizedSubring q) :=
    ResidueField.map (Φ : H →+* localizedSubring q)
  have hres₂ : (residue (localizedSubring q)).comp (Φ : H →+* localizedSubring q) =
      φ.comp (residue H) := by
    ext z
    exact (ResidueField.map_residue _ z).symm
  have hres₁ : (residue (localizedSubring q)).comp (f₁ : H →+* localizedSubring q) =
      φ.comp (residue H) := by
    ext z
    change residue _ (localizedSubringEquivOfStabilizes A K L q hσ (Φ (θ z))) = φ (residue H z)
    rw [residue_localizedSubringEquivOfStabilizes A K L q σ hσ Q hFr]
    change residue _ ((Φ : H →+* localizedSubring q) (θ z)) ^ Q = _
    rw [← ResidueField.map_residue, ← map_pow, hθ]
  have hφ : φ.comp ((residue H).comp (algebraMap A H)) =
      (residue (localizedSubring q)).comp (algebraMap A (localizedSubring q)) := by
    rw [← RingHom.comp_assoc, ← hres₂, RingHom.comp_assoc, AlgHom.comp_algebraMap]
  exact congrArg (fun z : localizedSubring q => (z : L)) (AlgHom.congr_fun
    ((HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH φ hφ f₁ inferInstance hres₁).trans
      (HenselianLocalRing.indEtaleAlgHomOfResidue_unique hH φ hφ Φ inferInstance hres₂).symm) h)

/-- The inclusion `(B_q)^I ⊆ B_q`, as an `A`-algebra map. -/
def inertiaInvariantsToLocalizedSubring :
    inertiaInvariants A K L q →ₐ[A] localizedSubring q where
  toRingHom := (inertiaInvariants A K L q).subtype
  commutes' a := Subtype.ext ((coe_algebraMap_inertiaInvariants A K L q a).trans
    (coe_algebraMap_localizedSubringBase q a).symm)

/-- The inclusion `(B_q)^I ⊆ B_q` is local: the inverse in `B_q` of an invariant unit is
invariant. -/
instance isLocalHom_inertiaInvariantsToLocalizedSubring :
    IsLocalHom (inertiaInvariantsToLocalizedSubring A K L q) := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨v, hv : (v : localizedSubring q) = z⟩ := hz
  have h1 : ((v : localizedSubring q) : L) * ((↑(v⁻¹) : localizedSubring q) : L) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]
    rfl
  have hfix : ∀ σ ∈ q.inertia Gal(L/K), σ ((↑(v⁻¹) : localizedSubring q) : L) =
      ((↑(v⁻¹) : localizedSubring q) : L) := fun σ hσ => by
    rw [eq_inv_of_mul_eq_one_right h1, map_inv₀, hv,
      (mem_inertiaInvariants_iff A K L q _).mp z.2 σ hσ]
  let w : inertiaInvariants A K L q :=
    ⟨(↑(v⁻¹) : localizedSubring q), (mem_inertiaInvariants_iff A K L q _).mpr hfix⟩
  refine ⟨⟨z, w, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · change (z : localizedSubring q) * (↑(v⁻¹) : localizedSubring q) = 1
    rw [← hv, Units.mul_inv]
  · change (↑(v⁻¹) : localizedSubring q) * (z : localizedSubring q) = 1
    rw [← hv, Units.inv_mul]

omit [IsIntegrallyClosed A] [IsLocalRing A] in
/-- **The Frobenius on a strict henselization, read in `(B_q)^I`.** For an `A`-isomorphism
`Φ : H ≃ (B_q)^I`, a local `A`-endomorphism `θ` of `H` with residue map inverse to the `Q`-th
power map, and an arithmetic Frobenius `σ` at `q`, `σ ∘ Φ ∘ θ = Φ` inside `L`. -/
theorem galAction_algEquiv_comp_eq_of_residue_pow [IsSepClosed L] (H : Type u) [CommRing H]
    [IsLocalRing H] [Algebra A H] (hH : StacksDraft.IndEtale A H)
    (Φ : H ≃ₐ[A] inertiaInvariants A K L q) (θ : H →ₐ[A] H) [IsLocalHom θ] (σ : Gal(L/K))
    (hσ : σ • q = q) (Q : ℕ) (hFr : ∀ b : integralClosure A L, σ • b - b ^ Q ∈ q)
    (hθ : ∀ h : H, residue H (θ h) ^ Q = residue H h) (h : H) :
    σ (((Φ (θ h) : localizedSubring q)) : L) = ((Φ h : localizedSubring q) : L) := by
  let Φ' : H →ₐ[A] localizedSubring q :=
    (inertiaInvariantsToLocalizedSubring A K L q).comp Φ.toAlgHom
  have : IsLocalHom Φ' := ⟨fun z hz => (isUnit_map_iff Φ z).mp
    (isUnit_of_map_unit (inertiaInvariantsToLocalizedSubring A K L q) _ hz)⟩
  exact galAction_comp_comp_eq_of_residue_pow A K L q H hH Φ' θ σ hσ Q hFr hθ h

end Frobenius

end IsIntegralClosure

end
