module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Algebra
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs

/-!
# Quasi-regularity of a sequence as an elementary relation condition

Let `R` be a commutative ring and `f : Fin c → R` a finite sequence, generating the ideal
`J = (f₀, …, f_{c-1})`.  Quasi-regularity of `f` is bijectivity of the canonical map
`Φ : (R/J)[T₀, …, T_{c-1}] → ⨁_d J^d/J^{d+1}`.  Since `Φ` is always surjective, quasi-regularity
is an *elementary relation condition*: a polynomial `p` over `R` whose every homogeneous
evaluation `∑_{|e| = d} f^e · p_e` lies in `J^{d+1}` must have all its coefficients in `J`.  That
form is `IsQuasiRegularRel`; it transports along ring isomorphisms and satisfies a local-global
principle over the maximal ideals of `R`.

## Main definitions

* `IsQuasiRegularRel f`: the elementary relation condition described above.

## Main results

* `isQuasiRegular_ofFn_iff`: `RingTheory.Sequence.IsQuasiRegular R (List.ofFn f)` is bijectivity
  of the polynomial-source map `associatedGradedMap f`.
* `isQuasiRegularRel_iff_bijective`: the elementary condition is that bijectivity.
* `isQuasiRegularRel_ringEquiv`: transport along a ring isomorphism.
* `IsQuasiRegularRel.localization`: the condition passes to any localization of `R`.
* `mem_of_forall_maximal` and `exists_mul_coeff_mem_of_localization`: the two halves of the
  converse, a local-global principle over the maximal ideals of `R`.

## Implementation notes

The source `(R/J)[T] ⊗_{R/J} (R/JR)` of `quasiRegularCanonicalMap` is identified with the
polynomial algebra `(R/J)[T]` by `tmulQuotOne`, inserting the class of `1`; this is an
isomorphism because `R/JR` and `R/J` are the same quotient of `R`.
-/

@[expose] public section

open Stacks.RingTheory.QuasiRegular

namespace Stacks.RingTheory.RegularIdealSheaf

variable {R : Type*} [CommRing R] {c : ℕ}

section Bridge

/-- The scalar actions of `R` and of `R/J` on `R/JR` are compatible. -/
instance isScalarTower_qrMbar (f : Fin c → R) : IsScalarTower R (qrRbar f) (qrMbar R f) := by
  constructor
  intro a b m
  induction b using Submodule.Quotient.induction_on with
  | _ y =>
    induction m using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      change a * y * x = a * (y * x)
      ring

/-- `R/JR → R/J`, the identification of the two quotients of `R` by `J`. -/
noncomputable def mbarToRbar (f : Fin c → R) : qrMbar R f →ₗ[qrRbar f] qrRbar f :=
  LinearMap.extendScalarsOfSurjective
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
    (Submodule.quotEquivOfEq (Jid f • (⊤ : Submodule R R)) (Jid f : Submodule R R)
      (by simp)).toLinearMap

/-- `R/J → R/JR`, the identification of the two quotients of `R` by `J`. -/
noncomputable def rbarToMbar (f : Fin c → R) : qrRbar f →ₗ[qrRbar f] qrMbar R f :=
  LinearMap.extendScalarsOfSurjective
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
    (Submodule.quotEquivOfEq (Jid f : Submodule R R) (Jid f • (⊤ : Submodule R R))
      (by simp)).toLinearMap

/-- `R/J ≃ R/JR` as `R/J`-modules: the submodule `J • R` of `R` is the ideal `J`. -/
noncomputable def rbarEquivMbar (f : Fin c → R) : qrRbar f ≃ₗ[qrRbar f] qrMbar R f :=
  LinearEquiv.ofLinearMap (rbarToMbar f) (mbarToRbar f)
    (LinearMap.ext fun x => by
      induction x using Submodule.Quotient.induction_on with
      | _ a => rfl)
    (LinearMap.ext fun x => by
      induction x using Submodule.Quotient.induction_on with
      | _ a => rfl)

/-- Tensoring with the class of `1` identifies the polynomial algebra `(R/J)[T]` with the source
`(R/J)[T] ⊗_{R/J} (R/JR)` of `quasiRegularCanonicalMap`. -/
noncomputable def tmulQuotOne (f : Fin c → R) :
    MvPolynomial (Fin c) (qrRbar f) ≃ₗ[qrRbar f] Source R f :=
  (TensorProduct.rid (qrRbar f) (MvPolynomial (Fin c) (qrRbar f))).symm.trans
    (TensorProduct.congr (LinearEquiv.refl _ _) (rbarEquivMbar f))

/-- `tmulQuotOne f` sends `q` to `q ⊗ 1`. -/
theorem tmulQuotOne_apply (f : Fin c → R) (q : MvPolynomial (Fin c) (qrRbar f)) :
    tmulQuotOne f q = q ⊗ₜ[qrRbar f] quotOne f := rfl

/-- The polynomial-source map is bijective if and only if the canonical map is. -/
theorem bijective_associatedGradedMap_iff (f : Fin c → R) :
    Function.Bijective (associatedGradedMap f) ↔
      Function.Bijective (quasiRegularCanonicalMap (M := R) f) := by
  have hcomp : (associatedGradedMap f : MvPolynomial (Fin c) (qrRbar f) → Target R f)
      = (quasiRegularCanonicalMap (M := R) f) ∘ (tmulQuotOne f) :=
    funext fun q => associatedGradedMap_apply f q
  rw [hcomp]
  exact Function.Bijective.of_comp_iff _ (tmulQuotOne f).bijective

/-- Bijectivity of the canonical map depends only on the sequence, not on the indexing type. -/
theorem bijective_canonical_cast {c c' : ℕ} (h : c' = c) (g : Fin c' → R) (f : Fin c → R)
    (hgf : ∀ i, g i = f (Fin.cast h i)) :
    Function.Bijective (quasiRegularCanonicalMap (M := R) g) ↔
      Function.Bijective (quasiRegularCanonicalMap (M := R) f) := by
  subst h
  obtain rfl : g = f := funext hgf
  rfl

/-- The sequence `f₀, …, f_{c-1}` is
quasi-regular exactly when `(R/J)[T] → ⨁_d J^d/J^{d+1}` is bijective. -/
theorem isQuasiRegular_ofFn_iff (f : Fin c → R) :
    RingTheory.Sequence.IsQuasiRegular R (List.ofFn f) ↔
      Function.Bijective (associatedGradedMap f) :=
  (bijective_canonical_cast List.length_ofFn _ f fun _ => List.getElem_ofFn _).trans
    (bijective_associatedGradedMap_iff f).symm

end Bridge

section Rel

/-- The elementary relation form of quasi-regularity: every polynomial `p` over `R` all of
whose homogeneous evaluations `∑_{|e| = d} f^e · (coeff e p)` lie in `J^{d+1}` has all its
coefficients in `J`. -/
def IsQuasiRegularRel (f : Fin c → R) : Prop :=
  ∀ (p : MvPolynomial (Fin c) R) (T : Finset (Fin c →₀ ℕ)), p.support ⊆ T →
    (∀ d : ℕ, gradedPartOn f p T d ∈ (Jid f ^ (d + 1) : Ideal R)) →
      ∀ e : Fin c →₀ ℕ, p.coeff e ∈ Jid f

/-- The elementary relation condition is bijectivity of the quasi-regularity map. -/
theorem isQuasiRegularRel_iff_bijective (f : Fin c → R) :
    IsQuasiRegularRel f ↔ Function.Bijective (associatedGradedMap f) := by
  constructor
  · intro h
    refine ⟨fun a b hab => sub_eq_zero.mp ?_, associatedGradedMap_surjective f⟩
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk (Jid f))
      Ideal.Quotient.mk_surjective (a - b)
    have hd := (associatedGradedMap_map_eq_zero_iff f p p.support subset_rfl).mp
      (by rw [hp, map_sub, hab, sub_self])
    rw [← hp]
    refine MvPolynomial.ext _ _ fun e => ?_
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h p p.support subset_rfl hd e
  · intro hbij p T hT hd e
    have h0 : associatedGradedMap f (MvPolynomial.map (Ideal.Quotient.mk (Jid f)) p) = 0 :=
      (associatedGradedMap_map_eq_zero_iff f p T hT).mpr hd
    have hz : MvPolynomial.map (Ideal.Quotient.mk (Jid f)) p = 0 :=
      hbij.1 (by rw [h0, map_zero])
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.coeff_map, hz,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The ideal generated by the image sequence is the image of the generated ideal. -/
theorem Jid_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin c → R) :
    Jid (fun i => φ (f i)) = Ideal.map φ (Jid f) := by
  rw [Jid, Jid, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The homogeneous evaluations of a polynomial commute with a ring homomorphism. -/
theorem gradedPartOn_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin c → R)
    (p : MvPolynomial (Fin c) R) (T : Finset (Fin c →₀ ℕ)) (d : ℕ) :
    gradedPartOn (fun i => φ (f i)) (MvPolynomial.map φ p) T d = φ (gradedPartOn f p T d) := by
  rw [gradedPartOn_eq_sum, gradedPartOn_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, MvPolynomial.coeff_map]
  congr 1
  rw [fpow, fpow, map_prod]
  exact Finset.prod_congr rfl fun i _ => (map_pow φ (f i) (e i)).symm

/-- The elementary relation condition only depends on the sequence. -/
theorem isQuasiRegularRel_congr {f g : Fin c → R} (h : f = g) (hf : IsQuasiRegularRel f) :
    IsQuasiRegularRel g := h ▸ hf

/-- The elementary relation condition transports along an invertible ring homomorphism. -/
theorem isQuasiRegularRel_of_bijective {S : Type*} [CommRing S] (φ : R →+* S) (ψ : S →+* R)
    (hψφ : ∀ x, ψ (φ x) = x) (hφψ : ∀ y, φ (ψ y) = y) (f : Fin c → R)
    (h : IsQuasiRegularRel f) : IsQuasiRegularRel (fun i => φ (f i)) := by
  intro p T hT hd e
  have hJ : Jid (fun i => φ (f i)) = Ideal.map φ (Jid f) := Jid_map φ f
  have hmap : MvPolynomial.map φ (MvPolynomial.map ψ p) = p := by
    rw [MvPolynomial.map_map, show φ.comp ψ = RingHom.id S from RingHom.ext hφψ,
      MvPolynomial.map_id]
  have hsupp : (MvPolynomial.map ψ p).support ⊆ T :=
    (MvPolynomial.support_map_subset _ _).trans hT
  have hd₀ : ∀ d : ℕ, gradedPartOn f (MvPolynomial.map ψ p) T d ∈ (Jid f ^ (d + 1) : Ideal R) := by
    intro d
    have hdd := hd d
    rw [hJ, ← Ideal.map_pow, ← hmap, gradedPartOn_map] at hdd
    obtain ⟨x, hx, hxe⟩ :=
      (Ideal.mem_map_iff_of_surjective φ fun y => ⟨ψ y, hφψ y⟩).mp hdd
    rwa [← hψφ x, hxe, hψφ] at hx
  have hco : φ ((MvPolynomial.map ψ p).coeff e) ∈ Ideal.map φ (Jid f) :=
    Ideal.mem_map_of_mem _ (h _ T hsupp hd₀ e)
  rwa [MvPolynomial.coeff_map, hφψ, ← hJ] at hco

/-- The elementary relation condition transports along a ring isomorphism. -/
theorem isQuasiRegularRel_ringEquiv {S : Type*} [CommRing S] (ε : R ≃+* S) (f : Fin c → R)
    (h : IsQuasiRegularRel f) : IsQuasiRegularRel (fun i => ε (f i)) :=
  isQuasiRegularRel_of_bijective (ε : R →+* S) (ε.symm : S →+* R)
    (fun x => ε.symm_apply_apply x) (fun y => ε.apply_symm_apply y) f h

end Rel

section Localization

/-- The elementary relation condition passes to any localization of `R`. -/
theorem IsQuasiRegularRel.localization (f : Fin c → R) (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S] (h : IsQuasiRegularRel f) :
    IsQuasiRegularRel (fun i => algebraMap R S (f i)) := by
  rw [isQuasiRegularRel_iff_bijective] at h
  rw [isQuasiRegularRel_iff_bijective, ← isQuasiRegular_ofFn_iff]
  have _ : Module.Flat R S := IsLocalization.flat S T
  have hbc : IsBaseChange S (Algebra.linearMap R S) :=
    IsLocalizedModule.isBaseChange T S (Algebra.linearMap R S)
  have hqr := RingTheory.Sequence.IsQuasiRegular.of_flat_of_isBaseChange (N := S) hbc
    (rs := List.ofFn f) ((isQuasiRegular_ofFn_iff f).mpr h)
  rwa [List.map_ofFn] at hqr

/-- Clearing denominators: if the image of `a` lies in the ideal generated by the image of `I`,
then some element of the localizing submonoid multiplies `a` into `I`. -/
theorem exists_mul_mem_of_algebraMap_mem (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization T S] (I : Ideal R) (a : R)
    (h : algebraMap R S a ∈ Ideal.map (algebraMap R S) I) : ∃ t ∈ T, t * a ∈ I := by
  obtain ⟨⟨i, t⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff T S).mp h
  rw [← map_mul] at hx
  obtain ⟨t', hx'⟩ := (IsLocalization.eq_iff_exists T S).mp hx
  refine ⟨(t' : R) * (t : R), mul_mem t'.2 t.2, ?_⟩
  have hre : (t' : R) * (t : R) * a = (t' : R) * (a * (t : R)) := by ring
  rw [hre, hx']
  exact Ideal.mul_mem_left _ _ i.2

/-- Ideal membership is local: an element lies in `I` as soon as, at every maximal ideal, some
element outside that maximal ideal multiplies it into `I`. -/
theorem mem_of_forall_maximal (I : Ideal R) (a : R)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ t : R, t ∉ m ∧ t * a ∈ I) : a ∈ I := by
  by_contra hna
  let K : Ideal R :=
    { carrier := {t : R | t * a ∈ I}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by simpa [add_mul] using I.add_mem hx hy
      smul_mem' := fun r x hx => by simpa [smul_eq_mul, mul_assoc] using I.mul_mem_left r hx }
  have hmemK : ∀ t : R, t ∈ K ↔ t * a ∈ I := fun _ => Iff.rfl
  have hKne : K ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, hmemK, one_mul]
    exact hna
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal K hKne
  obtain ⟨t, htm, hta⟩ := h m hm
  exact htm (hKm ((hmemK t).mpr hta))

/-- From the elementary relation condition at one localization of `R`,
a relation over `R` whose homogeneous evaluations lie in `J^{d+1}` has each of its coefficients
multiplied into `J` by some element of the localizing submonoid. -/
theorem exists_mul_coeff_mem_of_localization (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S] (f : Fin c → R)
    (hS : IsQuasiRegularRel (fun i => algebraMap R S (f i)))
    (p : MvPolynomial (Fin c) R) (T' : Finset (Fin c →₀ ℕ)) (hT : p.support ⊆ T')
    (hd : ∀ d : ℕ, gradedPartOn f p T' d ∈ (Jid f ^ (d + 1) : Ideal R)) (e : Fin c →₀ ℕ) :
    ∃ t ∈ T, t * p.coeff e ∈ Jid f := by
  have hsupp : (MvPolynomial.map (algebraMap R S) p).support ⊆ T' :=
    (MvPolynomial.support_map_subset _ _).trans hT
  have hd' : ∀ d : ℕ,
      gradedPartOn (fun i => algebraMap R S (f i)) (MvPolynomial.map (algebraMap R S) p) T' d
        ∈ (Jid (fun i => algebraMap R S (f i)) ^ (d + 1)) := by
    intro d
    rw [gradedPartOn_map, Jid_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hd d)
  have hco := hS _ T' hsupp hd' e
  rw [MvPolynomial.coeff_map, Jid_map] at hco
  exact exists_mul_mem_of_algebraMap_mem T S (Jid f) _ hco

end Localization

end Stacks.RingTheory.RegularIdealSheaf
