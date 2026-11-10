module

public import Mathlib
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.TameRamification
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma for extensions of discrete valuation rings

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`. This file
follows the passage from formal smoothness of `A → B` to Abhyankar's lemma and its consequences
for tame ramification.

First, if `A → B` is formally smooth for the maximal-ideal-adic topology, then after a finite
extension `K₁ / K` the integral closure `B₁` of `B` in the reduced compositum is the reduced
tensor product `(B ⊗_A A₁)_red`, and every extension of discrete valuation rings obtained by
localizing at a maximal ideal of `B₁` is again formally smooth. Second, Abhyankar's lemma: if the
residue characteristic of `A` is zero, or if it is prime to the ramification index `e` of `A → B`
and the residue-field extension `κ_B / κ_A` is separable, then those local factors are formally
smooth as soon as `e` divides the ramification index downstairs. Third, tame ramification of a
finite separable extension `L / K` is characterized by the existence of a Kummer extension
`K[π^(1/e)]` of exponent prime to the residue characteristic over which `L` embeds into an
unramified extension. Finally, tame and unramified extensions go up along `A → B`, and every
tamely ramified extension is contained in a tamely ramified finite Galois extension while any two
are contained in a common tamely ramified one.

## Main definitions

* `IsDiscreteValuationRing.HasUnramifiedKummerOverfield`: for a fixed exponent `n`, the property
  that `L` embeds into an unramified extension of the Kummer extension `K[π^(1/n)]`.

## Main results

* `IsDiscreteValuationRing.formallySmooth_localizations_after_finite_fraction_field_extension`:
  after a finite fraction-field extension the integral closure is the reduced tensor product and
  all the induced local extensions are formally smooth.
* `IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd`: Abhyankar's
  lemma for extensions of discrete valuation rings.
* `IsDiscreteValuationRing.isTamelyRamifiedWithRespectTo_tfae_hasUnramifiedKummerOverfield`:
  three equivalent characterizations of tame ramification.
* `IsDiscreteValuationRing.exists_algEquiv_pi_field_and_ramification_goes_up`: a finite separable
  extension stays a finite product of fields after scalar extension, and unramifiedness and tame
  ramification pass to every factor.
* `IsDiscreteValuationRing.exists_isGalois_and_common_extension_isTamelyRamifiedWithRespectTo`:
  the two permanence properties of tame ramification under finite overextensions.

## Implementation notes

The equalities of the sources are represented by algebra equivalences together with the
compatibility equations that pin down both canonical maps, so that applications do not have to
rebuild the comparison data separately. The extensions at maximal ideals are represented by their
canonical maps on localizations. Formal smoothness is tested in the maximum of the source and
target ring universes.

The first result is a corrected form of the source statement for Tag 09EQ: the printed equalities
`L₁ = L ⊗_K K₁` and `B₁ = B ⊗_A A₁` fail for an inseparable `K₁ / K` over a non-excellent base
(the completion example of Tag 00PB), where `L ⊗_K K₁` is not reduced. They are recovered here
under the additional hypothesis that `L ⊗_K K₁` is reduced.

The rings `A[π^(1/n)]` and fields `K[π^(1/n)]` are the canonical Kummer models of Tag 09EV.
Containment of field extensions is represented by compatible algebra structures and scalar
towers; the common overextension is not required to be a specified compositum, in accordance with
the source.

## References

* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
* [The Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
* [The Stacks Project, Tag 0EXW](https://stacks.math.columbia.edu/tag/0EXW)
* [The Stacks Project, Tag 0EXY](https://stacks.math.columbia.edu/tag/0EXY)
* [The Stacks Project, Tag 0EXX](https://stacks.math.columbia.edu/tag/0EXX)
-/

/-!
## This part

This first file collects the auxiliary facts on residue fields used throughout: surjectivity of
maps from localizations onto residue fields, the comparison map out of a tensor product of
residue fields and its separability consequences, finiteness of residue fields of integral
closures, and a criterion for a localization to be a discrete valuation ring.
-/

@[expose] public section

set_option maxRecDepth 4096

namespace IsDiscreteValuationRing

section

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

open scoped TensorProduct


noncomputable section

private theorem surjective_of_artinian_range_of_localization
    {R S T F : Type*} [CommRing R] [CommRing S] [CommRing T] [Field F]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] [IsArtinianRing T]
    (f : S →+* F) (hf : Function.Surjective f) (g : T →+* F)
    (h : ∀ r : R, f (algebraMap R S r) ∈ g.range) : Function.Surjective g := by
  let : Field g.range := (IsArtinianRing.isField_of_isDomain g.range).toField
  intro x
  obtain ⟨s, rfl⟩ := hf x
  obtain ⟨⟨a, b⟩, hs⟩ := IsLocalization.mk'_surjective M s
  have hb : f (algebraMap R S b) ≠ 0 :=
    ((IsLocalization.map_units S b).map f).ne_zero
  let av : g.range := ⟨f (algebraMap R S a), h a⟩
  let bv : g.range := ⟨f (algebraMap R S b), h b⟩
  have hz : (av / bv : g.range).val = f s := by
    apply (mul_left_inj' hb).mp
    calc
      (av / bv : g.range).val * f (algebraMap R S b) = f (algebraMap R S a) := by
        change ((av / bv) * bv : g.range).val = av.val
        rw [div_mul_cancel₀ _ fun h0 => hb (congrArg Subtype.val h0)]
      _ = f s * f (algebraMap R S b) := by
        rw [← map_mul, ← hs, IsLocalization.mk'_spec]
  exact hz ▸ (av / bv).property

open IsLocalRing in
def residueTensorMap
    (A B D C : Type*) [CommRing A] [CommRing B] [CommRing D] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D] [IsLocalRing C]
    [Algebra A B] [Algebra A D] [Algebra A C] [Algebra B C] [Algebra D C]
    [IsScalarTower A B C] [IsScalarTower A D C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap D C)] :
    (ResidueField D ⊗[ResidueField A] ResidueField B) →ₐ[ResidueField D]
      ResidueField C :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (ResidueField D) (ResidueField C))
    (IsScalarTower.toAlgHom (ResidueField A) (ResidueField B) (ResidueField C))
    (fun _ _ => Commute.all _ _)

open IsLocalRing in
private theorem residueTensorMap_tmul
    (A B D C : Type*) [CommRing A] [CommRing B] [CommRing D] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D] [IsLocalRing C]
    [Algebra A B] [Algebra A D] [Algebra A C] [Algebra B C] [Algebra D C]
    [IsScalarTower A B C] [IsScalarTower A D C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap D C)] (d : D) (b : B) :
    residueTensorMap A B D C (residue D d ⊗ₜ[ResidueField A] residue B b) =
      residue C (algebraMap D C d * algebraMap B C b) := by
  simp [residueTensorMap]

open IsLocalRing in
theorem residueTensorMap_surjective
    (A B A₁ B₁ D C : Type*)
    [CommRing A] [CommRing B] [CommRing A₁] [CommRing B₁] [CommRing D] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing D] [IsLocalRing C]
    [Algebra A B] [Algebra A A₁] [Algebra A D] [Algebra A C]
    [Algebra B B₁] [Algebra A₁ B₁] [Algebra A₁ D] [Algebra A₁ C]
    [Algebra B C] [Algebra B₁ C] [Algebra D C]
    [IsScalarTower A B C] [IsScalarTower A D C]
    [IsScalarTower A₁ D C] [IsScalarTower A₁ B₁ C] [IsScalarTower B B₁ C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A D)]
    [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap B C)]
    [IsLocalHom (algebraMap D C)]
    [Module.Finite (ResidueField A) (ResidueField D)]
    (M : Submonoid B₁) [IsLocalization M C]
    (g : (B ⊗[A] A₁) →+* B₁) (hg : Function.Surjective g)
    (hleft : ∀ b : B, g ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b) =
      algebraMap B B₁ b)
    (hright : ∀ a : A₁, g ((Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a) =
      algebraMap A₁ B₁ a) : Function.Surjective (residueTensorMap A B D C) := by
  have : IsArtinianRing (ResidueField B ⊗[ResidueField A] ResidueField D) :=
    IsArtinianRing.of_finite (ResidueField B) _
  have : IsArtinianRing (ResidueField D ⊗[ResidueField A] ResidueField B) :=
    (Algebra.TensorProduct.comm (ResidueField A) (ResidueField B)
      (ResidueField D)).toRingEquiv.isArtinianRing
  apply surjective_of_artinian_range_of_localization M (residue C)
    residue_surjective (residueTensorMap A B D C).toRingHom
  intro b₁
  obtain ⟨s, rfl⟩ := hg b₁
  induction s using TensorProduct.inductionOn with
  | tmul b a =>
    refine ⟨residue D (algebraMap A₁ D a) ⊗ₜ[ResidueField A] residue B b, ?_⟩
    change residueTensorMap A B D C _ = _
    rw [residueTensorMap_tmul]
    have hmul : b ⊗ₜ[A] a =
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A₁) b *
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[A] B ⊗[A] A₁) a := by simp
    rw [hmul, g.map_mul, hleft, hright, (algebraMap B₁ C).map_mul,
      ← IsScalarTower.algebraMap_apply A₁ D C,
      ← IsScalarTower.algebraMap_apply A₁ B₁ C,
      ← IsScalarTower.algebraMap_apply B B₁ C, mul_comm]
  | add x y hx hy =>
    simpa only [map_add] using
      (residueTensorMap A B D C).toRingHom.range.add_mem hx hy

private theorem geometricallyReduced_tensor_baseChange
    (k F E : Type*) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra.IsSeparableExtension k F] : Algebra.IsGeometricallyReduced E (E ⊗[k] F) := by
  have : Algebra.IsGeometricallyReduced k F :=
    ((Algebra.isSeparableExtension_tfae k F (ringExpChar k)).out 1 4).mp
      (show Algebra.IsSeparableExtension k F from inferInstance)
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange k E (AlgebraicClosure E) (AlgebraicClosure E) F)
    (Algebra.TensorProduct.cancelBaseChange k E (AlgebraicClosure E)
      (AlgebraicClosure E) F).injective

theorem separable_of_surjective_from_tensor
    (k F E G : Type*) [Field k] [Field F] [Field E] [Field G]
    [Algebra k F] [Algebra k E] [Algebra E G]
    [Algebra.IsSeparableExtension k F] [Module.Finite k E]
    (f : (E ⊗[k] F) →ₐ[E] G) (hf : Function.Surjective f) :
    Algebra.IsSeparableExtension E G := by
  let U := E ⊗[k] F
  let q : Ideal U := RingHom.ker f
  have : q.IsPrime := RingHom.ker_isPrime f
  let V := Localization.AtPrime q
  have : Algebra.IsGeometricallyReduced E U := geometricallyReduced_tensor_baseChange k F E
  have : IsReduced U := Algebra.isReduced_of_isGeometricallyReduced E
  have : IsArtinianRing (F ⊗[k] E) := IsArtinianRing.of_finite F _
  have : IsArtinianRing U := (Algebra.TensorProduct.comm k F E).toRingEquiv.isArtinianRing
  let : Field V := (IsArtinianRing.isField_of_isReduced_of_isLocalRing V).toField
  have : Algebra.IsGeometricallyReduced E V := by
    rw [Algebra.isGeometricallyReduced_field_iff]
    exact isReduced_tensor_localization E U q.primeCompl V (AlgebraicClosure E)
  have hunits : ∀ y : q.primeCompl, IsUnit (f y) := fun y => isUnit_iff_ne_zero.mpr y.property
  let l : V →ₐ[E] G := IsLocalization.liftAlgHom (S := V) hunits
  have hl : Function.Surjective l := by
    intro x
    obtain ⟨u, rfl⟩ := hf x
    exact ⟨algebraMap U V u, IsLocalization.lift_eq hunits u⟩
  let e : V ≃ₐ[E] G := AlgEquiv.ofBijective l ⟨l.toRingHom.injective, hl⟩
  have : Algebra.IsGeometricallyReduced E G :=
    Algebra.IsGeometricallyReduced.of_injective e.symm.toAlgHom e.symm.injective
  exact ((Algebra.isSeparableExtension_tfae E G (ringExpChar E)).out 4 1).mp this

open IsLocalRing in
theorem isLocalHom_of_integral_localization
    (A R D : Type*) [CommRing A] [IsLocalRing A] [CommRing R] [CommRing D]
    [IsLocalRing D] [Algebra A R] [Algebra R D] [Algebra A D]
    [IsScalarTower A R D] [Algebra.IsIntegral A R]
    (q : Ideal R) [q.IsMaximal] [IsLocalization.AtPrime D q] :
    IsLocalHom (algebraMap A D) := by
  apply ((local_hom_TFAE (algebraMap A D)).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A R D, ← Ideal.comap_comap]
  change ((IsLocalRing.maximalIdeal D).under R).comap (algebraMap A R) = IsLocalRing.maximalIdeal A
  rw [IsLocalization.AtPrime.under_maximalIdeal D q]
  exact eq_maximalIdeal (inferInstance : (q.under A).IsMaximal)

open IsLocalRing in
private theorem finite_residueField_of_quasiFinite
    (A D : Type*) [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
    [Algebra A D] [IsLocalHom (algebraMap A D)] [Algebra.QuasiFinite A D] :
    Module.Finite (ResidueField A) (ResidueField D) := by
  have : Algebra.QuasiFinite A (ResidueField D) :=
    Algebra.QuasiFinite.of_surjective_algHom (Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal D))
      Ideal.Quotient.mk_surjective
  have : Algebra.QuasiFinite (ResidueField A) (ResidueField D) :=
    Algebra.QuasiFinite.of_restrictScalars A (ResidueField A) (ResidueField D)
  exact Module.Finite.of_quasiFinite

open IsLocalRing in
private theorem quasiFinite_equivalent_integralClosure
    (A K L R : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.DimensionLEOne A] [Field K] [Field L] [CommRing R]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Module.Finite K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra A R]
    (e : R ≃ₐ[A] integralClosure A L) : Algebra.QuasiFinite A R := by
  have : Algebra.QuasiFinite A (integralClosure A L) :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
      A K L (integralClosure A L)).2.2
  exact (Algebra.QuasiFinite.iff_of_algEquiv e).mpr this

open IsLocalRing in
theorem finite_residueField_localized_integralClosure
    (A K L R : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.DimensionLEOne A] [IsLocalRing A] [Field K] [Field L] [CommRing R]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Module.Finite K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra A R]
    (e : R ≃ₐ[A] integralClosure A L) (q : Ideal R) [q.IsMaximal] :
    ∃ h : IsLocalHom (algebraMap A (Localization.AtPrime q)),
      letI := h
      Module.Finite (ResidueField A) (ResidueField (Localization.AtPrime q)) := by
  let : Algebra.IsIntegral A R := e.isIntegral_iff.mpr inferInstance
  let := isLocalHom_of_integral_localization A R (Localization.AtPrime q) q
  refine ⟨inferInstance, ?_⟩
  let : Algebra.QuasiFinite A R := quasiFinite_equivalent_integralClosure A K L R e
  let : Algebra.QuasiFinite A (Localization.AtPrime q) :=
    Algebra.QuasiFinite.of_isLocalization q.primeCompl
  exact finite_residueField_of_quasiFinite A (Localization.AtPrime q)

open IsLocalRing in
theorem dvr_of_regular_principal_and_field_away
    (R : Type*) [CommRing R] [IsLocalRing R] (π : R)
    (hreg : π ∈ nonZeroDivisors R) (hmax : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (hfield : IsField (Localization.Away π)) :
    ∃ (_ : IsDomain R), IsDiscreteValuationRing R := by
  let : Field (Localization.Away π) := hfield.toField
  have hf : Function.Injective (algebraMap R (Localization.Away π)) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr hreg)
  let : IsDomain R := Function.Injective.isDomain (algebraMap R (Localization.Away π)) hf
  refine ⟨inferInstance, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ?_⟩
  have hπ : Prime π := (Ideal.span_singleton_prime (mem_nonZeroDivisors_iff_ne_zero.mp hreg)).mp
    (hmax ▸ (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime))
  refine ⟨π, hπ.irreducible, fun {x} hx => ?_⟩
  have hxunit : IsUnit (algebraMap R (Localization.Away π) x) :=
    isUnit_iff_ne_zero.mpr (fun h => hx (hf (h.trans (map_zero _).symm)))
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff π).mp hxunit
  obtain ⟨m, _, hm⟩ := (dvd_prime_pow hπ n).mp hn
  exact ⟨m, hm.symm⟩

end

end

end IsDiscreteValuationRing
