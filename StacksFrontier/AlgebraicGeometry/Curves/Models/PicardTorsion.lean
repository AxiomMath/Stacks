module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardTorsionGeneral

/-!
# Picard groups of models: torsion is detected on the reduced special fibre

Let `R` be a discrete valuation ring with uniformizer `π` and residue field `k`, let `X` be a
regular proper model of a smooth projective curve over the fraction field of `R`, and let `h` be
an integer prime to the characteristic of `k`. The restriction map
`Pic(X)[h] ⟶ Pic((X_k)_red)[h]` is then injective.

The source's proof factors the restriction through the truncations
`X_n = X ×_{Spec R} Spec(R/π^{n+1})`. Each `(X_k)_red ⟶ X_n` is a thickening, so restriction is
bijective on `h`-torsion there; an `h`-torsion class trivial on `(X_k)_red` is therefore trivial
on every `X_n`, and the theorem on formal functions together with properness of `X ⟶ Spec(R)`
upgrades that to triviality on `X`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.truncation` — the truncation
  `X_n = X ×_{Spec R} Spec(R/π^{n+1})` of the model, with its projection `truncationι` to `X`.
* `Stacks.Models.RegularProperModelSituation.specialFiberRed` — the reduced special fibre
  `(X_k)_red`, with its morphism `specialFiberRedι` to `X`.
* `Stacks.Models.RegularProperModelSituation.specialFiberRedToTruncation` — the factorisation
  `(X_k)_red ⟶ X_n` of `specialFiberRedι` through the `n`th truncation.

## Main results

* `Stacks.Models.RegularProperModelSituation.isThickening_specialFiberToTruncation` — the
  special fibre is a thickening of every truncation, obtained by base change from
  `Spec(k) ⟶ Spec(R/π^{n+1})`.
* `Stacks.Models.RegularProperModelSituation.isThickening_specialFiberRedToTruncation` — hence
  so is the reduced special fibre.
* `Stacks.Models.injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion_of_truncation` — the
  deduction of [Stacks, Tag 0CAE] from its two inputs discussed below.

## Implementation notes

This file holds the geometry shared by the proof of [Stacks, Tag 0CAE]; the tag itself is stated
and proved in `StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective`. What is
proved here is the chain of thickenings `(X_k)_red ⟶ X_k ⟶ X_n` (the first factor by
`AlgebraicGeometry.Scheme.isThickening_reductionι`, the second by base change from
`Spec(k) ⟶ Spec(R/π^{n+1})`, whose kernel consists of nilpotents because `π` generates the
maximal ideal of `R`), and the deduction of injectivity on `h`-torsion from two inputs: that
global units lift along each thickening `(X_k)_red ⟶ X_n`, and that an `h`-torsion class trivial
on every truncation is trivial. The second input is the theorem on formal functions together with
the properness of `X ⟶ Spec(R)`; both inputs are proved in `PicardTorsionInjective`, the first in
the weaker form `Stacks.Thickenings.GlobalUnitsPowerLift`, which is what the bijection on torsion
of [Stacks, Tag 0C6S] needs. The hypothesis "`h` is prime to the characteristic of `k`" is
spelled as `IsUnit ((h : ℤ) : k)`.

The ideal of the `n`th truncation is written `(π) ^ (n + 1)`, which is the ideal `(π^{n+1})`,
so that the ideal sheaf of `X_n ⊆ X` is literally the `(n + 1)`st power of `(π) · 𝒪_X`.

## References

* [Stacks Project, Tag 0CAE](https://stacks.math.columbia.edu/tag/0CAE)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClassHom zsmulTorsion
  schemePullbackClass_comp mapsTo_zsmulTorsion)

universe u

namespace Stacks.Models

/-- A surjection of commutative rings whose kernel consists of nilpotent elements induces a
thickening of spectra: it is a closed immersion because the map is surjective, and surjective on
points because the kernel lies in every prime. -/
private theorem isThickening_specMap_of_ker_le_nilradical {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    Thickenings.IsThickening (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom f) hf, ?_⟩
  show Function.Surjective (PrimeSpectrum.comap f)
  intro p
  have hp : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker f : Set A) := fun x hx =>
    nilradical_le_prime p.asIdeal (hker hx)
  rw [← _root_.range_comap_of_surjective _ f hf] at hp
  exact hp

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The residue field as a quotient of the truncated base ring -/

/-- The uniformizer generates the maximal ideal of the discrete valuation ring. -/
theorem maximalIdeal_eq_span_pi : IsLocalRing.maximalIdeal S.R = Ideal.span {S.π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer S.π).mp S.uniformizer

/-- The chosen structure map `R ⟶ k` onto the residue field is the canonical residue map
followed by the chosen identification of residue fields. -/
theorem algebraMap_eq_residueEquiv_residue (r : S.R) :
    algebraMap S.R S.k r = S.residueEquiv (IsLocalRing.residue S.R r) := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq]
  exact (S.residueEquiv.commutes r).symm

/-- An element of `R` dies in `k` exactly when it lies in the maximal ideal. -/
theorem algebraMap_eq_zero_iff (r : S.R) :
    algebraMap S.R S.k r = 0 ↔ r ∈ IsLocalRing.maximalIdeal S.R := by
  rw [S.algebraMap_eq_residueEquiv_residue r,
    map_eq_zero_iff _ S.residueEquiv.injective, IsLocalRing.residue_eq_zero_iff]

/-- The chosen structure map `R ⟶ k` is surjective. -/
theorem surjective_algebraMap : Function.Surjective (algebraMap S.R S.k) := by
  intro a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (S.residueEquiv.symm a)
  refine ⟨r, ?_⟩
  rw [S.algebraMap_eq_residueEquiv_residue r,
    show IsLocalRing.residue S.R r = S.residueEquiv.symm a from hr, AlgEquiv.apply_symm_apply]

/-- The ideal `(π)^{n+1} = (π^{n+1})` of `R`, cutting out the `n`th truncation of the base. It is
written as a power of the ideal `(π)`, which is the form in which the ideal sheaf `(π) · 𝒪_X`
and its powers enter the theorem on formal functions. -/
abbrev truncationIdeal (n : ℕ) : Ideal S.R := Ideal.span {S.π} ^ (n + 1)

/-- The truncated base ring `R/π^{n+1}`. -/
abbrev truncationRing (n : ℕ) : Type u := S.R ⧸ S.truncationIdeal n

/-- The surjection `R/π^{n+1} ⟶ k` onto the residue field. -/
def truncationResidue (n : ℕ) : S.truncationRing n →+* S.k :=
  Ideal.Quotient.lift _ (algebraMap S.R S.k) fun a ha => by
    rw [truncationIdeal, Ideal.span_singleton_pow] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    have hpi : algebraMap S.R S.k S.π = 0 :=
      (S.algebraMap_eq_zero_iff S.π).mpr
        (S.maximalIdeal_eq_span_pi ▸ Ideal.mem_span_singleton_self S.π)
    rw [map_mul, map_pow, hpi, zero_pow (Nat.succ_ne_zero n), zero_mul]

/-- The map `R/π^{n+1} ⟶ k` sends the class of `r` to the image of `r` in `k`. -/
@[simp]
theorem truncationResidue_mk (n : ℕ) (r : S.R) :
    S.truncationResidue n (Ideal.Quotient.mk (S.truncationIdeal n) r) = algebraMap S.R S.k r :=
  rfl

/-- The map `R/π^{n+1} ⟶ k` is surjective. -/
theorem surjective_truncationResidue (n : ℕ) : Function.Surjective (S.truncationResidue n) := by
  intro a
  obtain ⟨r, hr⟩ := S.surjective_algebraMap a
  exact ⟨Ideal.Quotient.mk (S.truncationIdeal n) r, by rw [S.truncationResidue_mk]; exact hr⟩

/-- The kernel of `R/π^{n+1} ⟶ k` consists of nilpotent elements: it is generated by the class
of `π`, whose `(n+1)`st power vanishes. -/
theorem ker_truncationResidue_le_nilradical (n : ℕ) :
    RingHom.ker (S.truncationResidue n) ≤ nilradical (S.truncationRing n) := by
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, S.truncationResidue_mk] at hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp
    (S.maximalIdeal_eq_span_pi ▸ (S.algebraMap_eq_zero_iff r).mp hx)
  refine mem_nilradical.mpr ⟨n + 1, ?_⟩
  rw [← map_pow, mul_pow]
  refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ ?_)
  rw [truncationIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-! ### The truncations of the model and the reduced special fibre -/

/-- The base `Spec(R/π^{n+1}) ⟶ Spec(R)` of the `n`th truncation. -/
def truncationBase (n : ℕ) :
    Spec (.of (S.truncationRing n)) ⟶ Spec (.of S.R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (S.truncationIdeal n)))

/-- The morphism `Spec(k) ⟶ Spec(R/π^{n+1})` cutting the special fibre out of the `n`th
truncated base. -/
def specialFiberToTruncationBase (n : ℕ) :
    Spec (.of S.k) ⟶ Spec (.of (S.truncationRing n)) :=
  Spec.map (CommRingCat.ofHom (S.truncationResidue n))

/-- The composite `Spec(k) ⟶ Spec(R/π^{n+1}) ⟶ Spec(R)` is the morphism induced by `R ⟶ k`. -/
theorem specialFiberToTruncationBase_comp_truncationBase (n : ℕ) :
    S.specialFiberToTruncationBase n ≫ S.truncationBase n
      = Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) := by
  rw [specialFiberToTruncationBase, truncationBase, ← Spec.map_comp]
  congr 1

/-- `Spec(k) ⟶ Spec(R/π^{n+1})` is a thickening. -/
theorem isThickening_specialFiberToTruncationBase (n : ℕ) :
    Thickenings.IsThickening (S.specialFiberToTruncationBase n) :=
  isThickening_specMap_of_ker_le_nilradical _ (S.surjective_truncationResidue n)
    (S.ker_truncationResidue_le_nilradical n)

/-- The **`n`th truncation** `X_n = X ×_{Spec R} Spec(R/π^{n+1})` of the model. -/
abbrev truncation (n : ℕ) : Scheme.{u} := pullback S.X_to_R (S.truncationBase n)

/-- The projection `X_n ⟶ X` of the `n`th truncation onto the model. -/
abbrev truncationι (n : ℕ) : S.truncation n ⟶ S.X := pullback.fst _ _

/-- The morphism `X_k ⟶ X_n` from the special fibre into the `n`th truncation. -/
def specialFiberToTruncation (n : ℕ) : S.specialFiber ⟶ S.truncation n :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
      ≫ S.specialFiberToTruncationBase n)
    (by rw [Category.assoc, S.specialFiberToTruncationBase_comp_truncationBase n,
      pullback.condition])

/-- The composite `X_k ⟶ X_n ⟶ X` is the projection of the special fibre onto the model. -/
@[simp]
theorem specialFiberToTruncation_comp_truncationι (n : ℕ) :
    S.specialFiberToTruncation n ≫ S.truncationι n
      = pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
  pullback.lift_fst _ _ _

/-- The composite `X_k ⟶ X_n ⟶ Spec(R/π^{n+1})` is the structure morphism `X_k ⟶ Spec(k)`
followed by `Spec(k) ⟶ Spec(R/π^{n+1})`. -/
@[simp]
theorem specialFiberToTruncation_comp_snd (n : ℕ) :
    S.specialFiberToTruncation n ≫ pullback.snd S.X_to_R (S.truncationBase n)
      = pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
        ≫ S.specialFiberToTruncationBase n :=
  pullback.lift_snd _ _ _

/-- The square cutting the special fibre out of the `n`th truncation is a pullback square: it is
the left half of the horizontal pasting whose right half defines `X_n`. -/
theorem isPullback_specialFiberToTruncation (n : ℕ) :
    IsPullback (S.specialFiberToTruncation n)
      (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
      (pullback.snd S.X_to_R (S.truncationBase n)) (S.specialFiberToTruncationBase n) := by
  have hbig : IsPullback
      (pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
      (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
      S.X_to_R (S.specialFiberToTruncationBase n ≫ S.truncationBase n) := by
    rw [S.specialFiberToTruncationBase_comp_truncationBase n]
    exact IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (S.specialFiberToTruncation_comp_snd n)
    (IsPullback.of_hasPullback _ _)
  rwa [S.specialFiberToTruncation_comp_truncationι n]

/-- **The special fibre is a thickening of every truncation of the model.** This is the
base change along `X_n ⟶ Spec(R/π^{n+1})` of the thickening `Spec(k) ⟶ Spec(R/π^{n+1})`. -/
theorem isThickening_specialFiberToTruncation (n : ℕ) :
    Thickenings.IsThickening (S.specialFiberToTruncation n) :=
  Thickenings.isThickening_of_isPullback (S.isPullback_specialFiberToTruncation n)
    (S.isThickening_specialFiberToTruncationBase n)

/-- The **reduced special fibre** `(X_k)_red` of the model. -/
abbrev specialFiberRed : Scheme.{u} := S.specialFiber.reduction

/-- The canonical morphism `(X_k)_red ⟶ X` from the reduced special fibre to the model. -/
def specialFiberRedι : S.specialFiberRed ⟶ S.X :=
  S.specialFiber.reductionι ≫ pullback.fst _ _

/-- The factorisation `(X_k)_red ⟶ X_n` of `specialFiberRedι` through the `n`th truncation. -/
def specialFiberRedToTruncation (n : ℕ) : S.specialFiberRed ⟶ S.truncation n :=
  S.specialFiber.reductionι ≫ S.specialFiberToTruncation n

/-- The composite `(X_k)_red ⟶ X_n ⟶ X` is `specialFiberRedι`. -/
theorem specialFiberRedToTruncation_comp_truncationι (n : ℕ) :
    S.specialFiberRedToTruncation n ≫ S.truncationι n = S.specialFiberRedι := by
  rw [specialFiberRedToTruncation, specialFiberRedι, Category.assoc,
    S.specialFiberToTruncation_comp_truncationι n]

/-- **The reduced special fibre is a thickening of every truncation of the model**: it is a
thickening of the special fibre, which is a thickening of the truncation. -/
theorem isThickening_specialFiberRedToTruncation (n : ℕ) :
    Thickenings.IsThickening (S.specialFiberRedToTruncation n) :=
  ⟨@IsClosedImmersion.comp _ _ _ _ _ S.specialFiber.isThickening_reductionι.1
      (S.isThickening_specialFiberToTruncation n).1,
    (S.isThickening_specialFiberToTruncation n).2.comp
      S.specialFiber.isThickening_reductionι.2⟩

/-- The structure morphism `(X_k)_red ⟶ Spec(k)` of the reduced special fibre. -/
def specialFiberRedToBase : S.specialFiberRed ⟶ Spec (.of S.k) :=
  S.specialFiber.reductionι ≫ pullback.snd _ _

/-- An integer invertible in the residue field is invertible in the global functions of the
reduced special fibre, which is a scheme over that field. -/
theorem isUnit_intCast_specialFiberRed {h : ℤ} (hh : IsUnit ((h : ℤ) : S.k)) :
    IsUnit ((h : ℤ) : Γ(S.specialFiberRed, ⊤)) := by
  have hmap := hh.map
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberRedToBase.appTop).hom
  rwa [map_intCast] at hmap

end RegularProperModelSituation

/-- **The reduction of [Stacks, Tag 0CAE] to its two inputs.** In the situation of Tag 0C61, let
`h` be an integer invertible in the residue field `k`. If global units lift along every
thickening `(X_k)_red ⟶ X_n`, and an `h`-torsion class trivial on every truncation `X_n` is
trivial, then restriction `Pic(X)[h] ⟶ Pic((X_k)_red)[h]` is injective.

Both inputs are discharged for a regular proper model in
`StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsionInjective`, where the tag itself is
stated as `Stacks.Models.injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion`; the units
input is used there in the weaker form `Stacks.Thickenings.GlobalUnitsPowerLift`. -/
theorem injOn_schemePullbackClass_specialFiberRedι_zsmulTorsion_of_truncation
    (S : RegularProperModelSituation.{u}) {h : ℤ} (hh : IsUnit ((h : ℤ) : S.k))
    (hunits : ∀ n : ℕ, Function.Surjective (Units.map
      (CommRingCat.Hom.hom ((S.specialFiberRedToTruncation n).app ⊤)).toMonoidHom))
    (hformal : ∀ x ∈ zsmulTorsion (ofScheme S.X) h, ∀ y ∈ zsmulTorsion (ofScheme S.X) h,
      (∀ n : ℕ, schemePullbackClass (S.truncationι n) x
        = schemePullbackClass (S.truncationι n) y) → x = y) :
    Set.InjOn (schemePullbackClass S.specialFiberRedι) (zsmulTorsion (ofScheme S.X) h) := by
  intro x hx y hy hxy
  refine hformal x hx y hy fun n => ?_
  have hbij := Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_isThickening
    (S.specialFiberRedToTruncation n) (S.isThickening_specialFiberRedToTruncation n)
    (S.isUnit_intCast_specialFiberRed hh) (hunits n)
  have hm : ∀ z ∈ zsmulTorsion (ofScheme S.X) h,
      schemePullbackClass (S.truncationι n) z ∈ zsmulTorsion (ofScheme (S.truncation n)) h :=
    fun z hz => mapsTo_zsmulTorsion (A := ofScheme S.X) (B := ofScheme (S.truncation n))
      (schemePullbackClassHom (S.truncationι n)) h hz
  refine hbij.injOn (hm x hx) (hm y hy) ?_
  rw [schemePullbackClass_comp, schemePullbackClass_comp,
    S.specialFiberRedToTruncation_comp_truncationι n]
  exact hxy

end Stacks.Models

end
