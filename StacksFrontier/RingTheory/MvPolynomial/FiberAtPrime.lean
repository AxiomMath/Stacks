module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The closed fibre of a localized polynomial ring

Let `R₀` be a ring, let `Q` be a prime of `R₀[x_i]` and let `p₀ = Q ∩ R₀`. The fibre of the
local ring `R₀[x_i]_Q` over `(R₀)_{p₀}` is the quotient `F = R₀[x_i]_Q / p₀ R₀[x_i]_Q`. This file
shows that `F` is the localization of the polynomial ring `κ(p₀)[x_i]` over the residue field at
a prime, namely at the preimage of the maximal ideal of `F`.

## Main definitions

* `MvPolynomial.FiberAtPrime Q`: the ring `R₀[x_i]_Q / p₀ R₀[x_i]_Q`.
* `MvPolynomial.FiberAtPrime.mk Q`: the canonical map `R₀[x_i] → F`.
* `MvPolynomial.FiberAtPrime.ofResidueField Q`: the map `κ(p₀)[x_i] → F`.
* `MvPolynomial.FiberAtPrime.basePrime Q`: the prime of `κ(p₀)[x_i]` below the maximal ideal of
  `F`.

## Main results

* `MvPolynomial.FiberAtPrime.isLocalization`: `F` is the localization of `κ(p₀)[x_i]` at
  `basePrime Q`.
-/

@[expose] public section

open MvPolynomial

namespace MvPolynomial

variable {R₀ : Type*} [CommRing R₀] {ι : Type*} (Q : Ideal (MvPolynomial ι R₀)) [Q.IsPrime]

/-- The fibre `F = R₀[x_i]_Q / p₀ R₀[x_i]_Q` of the local ring `R₀[x_i]_Q` over `(R₀)_{p₀}`, where
`p₀ = Q ∩ R₀`. -/
noncomputable abbrev FiberAtPrime : Type _ :=
  Localization.AtPrime Q ⧸ Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q)

namespace FiberAtPrime

/-- The canonical map `R₀[x_i] → F`. -/
noncomputable def mk : MvPolynomial ι R₀ →+* FiberAtPrime Q :=
  (Ideal.Quotient.mk _).comp (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))

/-- `mk` is the quotient map after the localization map, on elements. -/
@[simp]
theorem mk_apply (g : MvPolynomial ι R₀) :
    mk Q g = Ideal.Quotient.mk (Ideal.map (algebraMap R₀ (Localization.AtPrime Q))
      (Ideal.under R₀ Q)) (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q) g) :=
  rfl

/-- Polynomials outside `Q` become units in the fibre. -/
private theorem isUnit_mk_of_notMem {g : MvPolynomial ι R₀} (hg : g ∉ Q) : IsUnit (mk Q g) :=
  (IsLocalization.map_units (M := Q.primeCompl) (Localization.AtPrime Q) ⟨g, hg⟩).map
    (Ideal.Quotient.mk _)

/-- The reduction `θ : R₀[x_i] → κ(p₀)[x_i]` of the coefficients to the residue field. -/
noncomputable abbrev residueMap :
    MvPolynomial ι R₀ →+* MvPolynomial ι (Ideal.under R₀ Q).ResidueField :=
  MvPolynomial.map (algebraMap R₀ (Ideal.under R₀ Q).ResidueField)

/-- The ideal `p₀ R₀[x_i]_Q` lies in the maximal ideal. -/
theorem map_le_maximalIdeal :
    Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal,
    IsScalarTower.algebraMap_eq R₀ (MvPolynomial ι R₀) (Localization.AtPrime Q), ← Ideal.map_map]
  exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)

/-- The ideal `p₀ R₀[x_i]_Q` is proper. -/
theorem map_ne_top :
    Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q) ≠ ⊤ := fun h ↦
  (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top
    (top_le_iff.1 (h ▸ map_le_maximalIdeal Q))

/-- The fibre is a nonzero ring. -/
instance : Nontrivial (FiberAtPrime Q) :=
  Ideal.Quotient.nontrivial_iff.2 (map_ne_top Q)

/-- The fibre is a local ring, as a nonzero quotient of a local ring. -/
instance : IsLocalRing (FiberAtPrime Q) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- `p₀` maps to zero in the fibre. -/
theorem under_le_ker :
    Ideal.under R₀ Q ≤ RingHom.ker ((mk Q).comp (algebraMap R₀ (MvPolynomial ι R₀))) := by
  intro r hr
  rw [RingHom.mem_ker, RingHom.comp_apply, mk, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hr

/-- The elements of `R₀` outside `p₀` become units in the fibre. -/
theorem primeCompl_le_comap_isUnit :
    (Ideal.under R₀ Q).primeCompl ≤
      (IsUnit.submonoid (FiberAtPrime Q)).comap
        ((mk Q).comp (algebraMap R₀ (MvPolynomial ι R₀))) := by
  intro r hr
  exact isUnit_mk_of_notMem Q hr

/-- The map `κ(p₀) → F` induced by `R₀ → F`. -/
noncomputable def residueFieldHom : (Ideal.under R₀ Q).ResidueField →+* FiberAtPrime Q :=
  Ideal.ResidueField.lift _ _ (under_le_ker Q) (primeCompl_le_comap_isUnit Q)

/-- The map `ψ : κ(p₀)[x_i] → F`, extending `κ(p₀) → F` by `x_i ↦ x_i`. -/
noncomputable def ofResidueField :
    MvPolynomial ι (Ideal.under R₀ Q).ResidueField →+* FiberAtPrime Q :=
  eval₂Hom (residueFieldHom Q) fun j ↦ mk Q (X j)

/-- `ψ ∘ θ` is the canonical map `R₀[x_i] → F`. -/
theorem ofResidueField_residueMap (g : MvPolynomial ι R₀) :
    ofResidueField Q (residueMap Q g) = mk Q g := by
  have h : (ofResidueField Q).comp (residueMap Q) = mk Q := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.comp_apply, residueMap, MvPolynomial.map_C, ofResidueField,
        MvPolynomial.eval₂Hom_C, residueFieldHom, Ideal.ResidueField.lift_algebraMap,
        RingHom.comp_apply]
      rw [← MvPolynomial.algebraMap_eq]
    · rw [RingHom.comp_apply, residueMap, MvPolynomial.map_X, ofResidueField,
        MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun h g

/-- The prime `q̄` of `κ(p₀)[x_i]` below the maximal ideal of `F`, at which `F` is the
localization of `κ(p₀)[x_i]`. -/
noncomputable def basePrime : Ideal (MvPolynomial ι (Ideal.under R₀ Q).ResidueField) :=
  Ideal.comap (ofResidueField Q) (IsLocalRing.maximalIdeal (FiberAtPrime Q))

/-- `q̄` is prime. -/
instance : (basePrime Q).IsPrime :=
  Ideal.comap_isPrime (ofResidueField Q) (IsLocalRing.maximalIdeal (FiberAtPrime Q))

/-- An element of `Q` maps into the maximal ideal of `F`. -/
theorem mk_mem_maximalIdeal {g : MvPolynomial ι R₀} (hg : g ∈ Q) :
    mk Q g ∈ IsLocalRing.maximalIdeal (FiberAtPrime Q) := by
  have hx :
    algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q) g ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hg
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 :
    algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q) g * c - 1 ∈
      Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, sub_eq_zero]
    exact hb
  have h3 :=
    Submodule.sub_mem (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (Ideal.mul_mem_right c _ hx) (map_le_maximalIdeal Q h1)
  rw [sub_sub_cancel] at h3
  exact IsLocalRing.notMem_maximalIdeal.2 isUnit_one h3

/-- An element of `R₀[x_i]` maps into the maximal ideal of `F` exactly when it lies in `Q`. -/
theorem mk_mem_maximalIdeal_iff {g : MvPolynomial ι R₀} :
    mk Q g ∈ IsLocalRing.maximalIdeal (FiberAtPrime Q) ↔ g ∈ Q := by
  refine ⟨fun h ↦ ?_, mk_mem_maximalIdeal Q⟩
  by_contra hg
  exact (IsLocalRing.mem_maximalIdeal _).1 h (isUnit_mk_of_notMem Q hg)

/-- The reduction of an element of `Q` lies in `q̄`. -/
theorem residueMap_mem_basePrime {g : MvPolynomial ι R₀} (hg : g ∈ Q) :
    residueMap Q g ∈ basePrime Q := by
  rw [basePrime, Ideal.mem_comap, ofResidueField_residueMap]
  exact mk_mem_maximalIdeal Q hg

/-- The `κ(p₀)[x_i]`-algebra structure on `F` given by `ψ`. -/
@[instance_reducible]
noncomputable def algebra :
    Algebra (MvPolynomial ι (Ideal.under R₀ Q).ResidueField) (FiberAtPrime Q) :=
  (ofResidueField Q).toAlgebra

/-- The kernel of `θ` is `p₀ R₀[x_i]`. -/
theorem ker_residueMap :
    RingHom.ker (residueMap Q) =
      Ideal.map (algebraMap R₀ (MvPolynomial ι R₀)) (Ideal.under R₀ Q) := by
  rw [residueMap, MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField,
    MvPolynomial.algebraMap_eq]

/-- **Clearing denominators over the residue field.** Every polynomial over `κ(p₀)` becomes the
reduction of a polynomial over `R₀` after multiplication by a nonzero constant `d ∉ p₀`. -/
theorem exists_C_mul_eq_residueMap (w : MvPolynomial ι (Ideal.under R₀ Q).ResidueField) :
    ∃ d ∉ Ideal.under R₀ Q,
      ∃ a : MvPolynomial ι R₀,
        MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d) * w = residueMap Q a := by
  induction w using MvPolynomial.induction_on with
  | C t =>
    obtain ⟨n, ⟨m, hm⟩, ht⟩ :=
      IsLocalization.exists_mk'_eq (nonZeroDivisors (R₀ ⧸ Ideal.under R₀ Q)) (S :=
        (Ideal.under R₀ Q).ResidueField) t
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective n
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective m
    have hdp : d ∉ Ideal.under R₀ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact mem_nonZeroDivisors_iff_ne_zero.1 hm
    refine ⟨d, hdp, MvPolynomial.C n, ?_⟩
    rw [residueMap, MvPolynomial.map_C, ← MvPolynomial.C_mul, ← ht]
    congr 1
    exact
      IsLocalization.mk'_spec' (Ideal.under R₀ Q).ResidueField
        (Ideal.Quotient.mk (Ideal.under R₀ Q) n)
        (⟨Ideal.Quotient.mk (Ideal.under R₀ Q) d, hm⟩ : nonZeroDivisors (R₀ ⧸ Ideal.under R₀ Q))
  | add p q hp hq =>
    obtain ⟨d₁, hd₁, a₁, ha₁⟩ := hp
    obtain ⟨d₂, hd₂, a₂, ha₂⟩ := hq
    refine
      ⟨d₁ * d₂, fun h ↦ ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hd₁ hd₂),
        MvPolynomial.C d₂ * a₁ + MvPolynomial.C d₁ * a₂, ?_⟩
    have e1 :
      residueMap Q (MvPolynomial.C d₂ * a₁ + MvPolynomial.C d₁ * a₂) =
        MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d₂) * residueMap Q a₁ +
          MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d₁) * residueMap Q a₂ := by
      rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C]
    have e2 :
      (MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField (d₁ * d₂)) :
          MvPolynomial ι (Ideal.under R₀ Q).ResidueField) =
        MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d₁) *
          MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d₂) := by
      rw [map_mul, MvPolynomial.C_mul]
    rw [e1, e2, ← ha₁, ← ha₂]
    ring
  | mul_X p j hp =>
    obtain ⟨d, hd, a, ha⟩ := hp
    exact
      ⟨d, hd, a * MvPolynomial.X j, by
        rw [map_mul, MvPolynomial.map_X, ← ha]; ring⟩

/-- `ψ : κ(p₀)[x_i] → F` is injective. -/
theorem ofResidueField_injective : Function.Injective (ofResidueField Q) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨d, hd, a, ha⟩ := exists_C_mul_eq_residueMap Q w
  have h1 :
    algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q) a ∈
      Ideal.map (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))
        (Ideal.map (algebraMap R₀ (MvPolynomial ι R₀)) (Ideal.under R₀ Q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← Ideal.Quotient.eq_zero_iff_mem]
    have : mk Q a = 0 := by rw [← ofResidueField_residueMap, ← ha, map_mul, hw, mul_zero]
    rwa [mk, RingHom.comp_apply] at this
  obtain ⟨⟨⟨b, hb⟩, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp h1
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)] at e
  obtain ⟨c, hc⟩ := e
  have hJ :
    (c : MvPolynomial ι R₀) * b ∈
      Ideal.map (algebraMap R₀ (MvPolynomial ι R₀)) (Ideal.under R₀ Q) :=
    Ideal.mul_mem_left _ _ hb
  have hprod :
    residueMap Q ((c : MvPolynomial ι R₀) * (s : MvPolynomial ι R₀)) * residueMap Q a = 0 := by
    rw [← map_mul]
    have :
      ((c : MvPolynomial ι R₀) * (s : MvPolynomial ι R₀)) * a = (c : MvPolynomial ι R₀) * b := by
      rw [← hc]; ring
    rw [this, ← RingHom.mem_ker, ker_residueMap]
    exact hJ
  have hs0 : residueMap Q ((c : MvPolynomial ι R₀) * (s : MvPolynomial ι R₀)) ≠ 0 := by
    intro h
    rw [← RingHom.mem_ker, ker_residueMap] at h
    exact (Q.primeCompl.mul_mem c.2 s.2) (Ideal.map_le_iff_le_comap.2 le_rfl h)
  have hta : residueMap Q a = 0 := (mul_eq_zero.1 hprod).resolve_left hs0
  have hdne :
    MvPolynomial.C (algebraMap R₀ (Ideal.under R₀ Q).ResidueField d) ≠
      (0 : MvPolynomial ι (Ideal.under R₀ Q).ResidueField) := by
    simpa [MvPolynomial.C_eq_zero] using hd
  rw [hta] at ha
  exact (mul_eq_zero.1 ha).resolve_left hdne

/-- **`F` is the localization of `κ(p₀)[x_i]` at `q̄`.** -/
theorem isLocalization :
    letI := algebra Q
    IsLocalization.AtPrime (FiberAtPrime Q) (basePrime Q) := by
  let := algebra Q
  have hmap : algebraMap (MvPolynomial ι (Ideal.under R₀ Q).ResidueField) (FiberAtPrime Q) =
      ofResidueField Q :=
    RingHom.algebraMap_toAlgebra _
  refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · rw [hmap]
    exact IsLocalRing.notMem_maximalIdeal.1 y.2
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    refine ⟨⟨residueMap Q a, ⟨residueMap Q (s : MvPolynomial ι R₀), ?_⟩⟩, ?_⟩
    · rw [Ideal.mem_primeCompl_iff, basePrime, Ideal.mem_comap, ofResidueField_residueMap]
      exact IsLocalRing.notMem_maximalIdeal.2 (isUnit_mk_of_notMem Q s.2)
    · have key :
        Ideal.Quotient.mk (Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q))
              (IsLocalization.mk' (Localization.AtPrime Q) a s) *
            ofResidueField Q (residueMap Q (s : MvPolynomial ι R₀)) =
          ofResidueField Q (residueMap Q a) := by
        rw [ofResidueField_residueMap, ofResidueField_residueMap, mk, RingHom.comp_apply,
          RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
      exact key
  · rw [hmap] at h
    exact ⟨1, by rw [ofResidueField_injective Q h]⟩

end FiberAtPrime

end MvPolynomial
