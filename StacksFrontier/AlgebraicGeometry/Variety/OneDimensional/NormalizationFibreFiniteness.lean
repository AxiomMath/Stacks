module

public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationDimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the fibres of the normalization in dimension one

Let `X` be a locally Noetherian scheme of dimension at most one and `ν : X^ν → X` its
normalization. The stalk `(ν_* 𝒪_{X^ν})_x` is the integral closure of `A = 𝒪_{X, x}` in the
product of the residue fields of the minimal primes of `A`, which splits as the product over
those primes of the integral closures of the one-dimensional Noetherian domains `A ⧸ p` in their
fraction fields. Krull–Akizuki makes each factor quasi-finite over `A ⧸ p`, hence over `A`, so
the stalk is quasi-finite over `A`. The fibre of `ν` over `x` is the maximal spectrum of that
stalk, so it is finite, and the residue field extensions it induces are finite.

## Main results

* `AlgebraicGeometry.quasiFinite_normalizationPushforwardStalk`: the stalk of the pushforward is
  quasi-finite over the local ring.
* `AlgebraicGeometry.finite_fibre_normalization`: the fibres of the normalization are finite.
* `AlgebraicGeometry.finite_residueFieldMap_normalization`: the residue field extensions induced
  by the normalization are finite.

## Implementation notes

The fibre is read off the maximal spectrum of the pushforward stalk through
`AlgebraicGeometry.normalizationFiberEquivMaximalSpectrum`, which also supplies the comparison
of the residue field at a point of the fibre with the quotient of the stalk by the matching
maximal ideal, as an extension of `κ(x)`. Finiteness of that extension is deduced from the
quasi-finiteness of the stalk: the fibre `κ(x) ⊗_A C` of a quasi-finite algebra is a
finite-dimensional `κ(x)`-vector space, and the quotient `C ⧸ 𝔪` is a quotient of it.

## References

* [Stacks Project, Tag 0C45](https://stacks.math.columbia.edu/tag/0C45)
* [Stacks Project, Tag 09IG](https://stacks.math.columbia.edu/tag/09IG)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.NormalizationStalkAmbient
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The product decomposition of the integral closure of `A` in the product of the residue
fields of its minimal primes, as an isomorphism of `A`-algebras. -/
@[ega "II 6.3.6" "special case"]
private def integralClosureMinimalPrimesAlgEquivPi (A : Type u) [CommRing A]
    [Finite (minimalPrimes A)] :
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    letI (p : minimalPrimes A) :
        Algebra A (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) :=
      ((algebraMap (A ⧸ p.1)
        (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1))).comp
          (Ideal.Quotient.mk p.1)).toAlgebra
    integralClosure A (minimalPrimeResidueFieldProduct A) ≃ₐ[A]
      ∀ p : minimalPrimes A,
        integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1) := by
  letI (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  letI (p : minimalPrimes A) :
      Algebra A (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) :=
    ((algebraMap (A ⧸ p.1)
      (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1))).comp
        (Ideal.Quotient.mk p.1)).toAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := integralClosure_minimalPrimeResidueFieldProduct_ringEquiv_pi A) fun a => ?_
  funext p
  exact Subtype.ext (IsScalarTower.algebraMap_apply A (A ⧸ p.1) p.1.ResidueField a).symm

/-- **The integral closure of a Noetherian ring of dimension at most one in the product of the
residue fields of its minimal primes is quasi-finite over it.** It is the product over those
primes of the integral closures of the quotients `A ⧸ 𝔭`, and Krull–Akizuki makes each factor
quasi-finite. -/
theorem quasiFinite_integralClosure_minimalPrimeResidueFieldProduct (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hdim : Ring.KrullDimLE 1 A) :
    letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
      (minimalPrimeResidueFieldProductHom A).toAlgebra
    Algebra.QuasiFinite A (integralClosure A (minimalPrimeResidueFieldProduct A)) := by
  let : Finite (minimalPrimes A) := minimalPrimes.finite_of_isNoetherianRing _
  let (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  let : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  let (p : minimalPrimes A) :
      Algebra A (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) :=
    ((algebraMap (A ⧸ p.1)
      (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1))).comp
        (Ideal.Quotient.mk p.1)).toAlgebra
  have (p : minimalPrimes A) :
      Algebra.QuasiFinite A (integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) :=
    Stacks.quasiFinite_integralClosure_residueField_quotient A hdim p.1
  have : Algebra.QuasiFinite A
      (∀ p : minimalPrimes A,
        integralClosure (A ⧸ p.1) (@Ideal.ResidueField A _ p.1 p.2.1.1)) :=
    Algebra.QuasiFinite.pi _
  exact (Algebra.QuasiFinite.iff_of_algEquiv
    (integralClosureMinimalPrimesAlgEquivPi A)).mpr inferInstance

/-- **The stalk of the pushforward of the structure sheaf of the normalization is quasi-finite
over the local ring**, on a locally Noetherian scheme of dimension at most one. -/
theorem quasiFinite_normalizationPushforwardStalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (x : X) :
    letI := normalizationPushforwardStalkAlgebra X hfin x
    Algebra.QuasiFinite (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) := by
  let := normalizationPushforwardStalkAlgebra X hfin x
  have hKD : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    Ring.krullDimLE_iff.mpr
      ((Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
        X x).trans hdim)
  let : Algebra (X.presheaf.stalk x)
      (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  have : Algebra.QuasiFinite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x))) :=
    quasiFinite_integralClosure_minimalPrimeResidueFieldProduct (X.presheaf.stalk x) hKD
  exact (Algebra.QuasiFinite.iff_of_algEquiv
    (normalizationStalkAlgEquivIntegralClosureMinimalPrimes X hfin x)).mpr inferInstance


/-- The stalk of the pushforward of the structure sheaf of the normalization is integral over
the local ring: it is an integral closure of it. -/
theorem isIntegral_normalizationPushforwardStalk {X : Scheme.{u}}
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (x : X) :
    letI := normalizationPushforwardStalkAlgebra X hfin x
    Algebra.IsIntegral (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) := by
  let := normalizationPushforwardStalkAlgebra X hfin x
  let : Algebra (X.presheaf.stalk x)
      (minimalPrimeResidueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimeResidueFieldProductHom (X.presheaf.stalk x)).toAlgebra
  have : Algebra.IsIntegral (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimeResidueFieldProduct (X.presheaf.stalk x))) :=
    ⟨integralClosure.isIntegral⟩
  exact (AlgEquiv.isIntegral_iff
    (normalizationStalkAlgEquivIntegralClosureMinimalPrimes X hfin x)).mpr inferInstance

/-- Every maximal ideal of the pushforward stalk lies over the maximal ideal of the local
ring, the extension being integral and the base local. -/
private theorem liesOver_maximalIdeal_of_isMaximal {X : Scheme.{u}}
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (x : X)
    (M : MaximalSpectrum (normalizationPushforwardStalk X hfin x)) :
    letI := normalizationPushforwardStalkAlgebra X hfin x
    M.asIdeal.LiesOver (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  let := normalizationPushforwardStalkAlgebra X hfin x
  have := isIntegral_normalizationPushforwardStalk hfin x
  have : M.asIdeal.IsMaximal := M.isMaximal
  exact ⟨(IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := X.presheaf.stalk x) M.asIdeal)).symm⟩

/-- **The fibres of the normalization of a one-dimensional locally Noetherian scheme are
finite.** The fibre over `x` is the maximal spectrum of the pushforward stalk, whose maximal
ideals all lie over the maximal ideal of `𝒪_{X,x}` because the stalk is integral over it, and
quasi-finiteness bounds the primes lying over a given one. -/
theorem finite_fibre_normalization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (x : X) :
    ((Scheme.normalization X hfin).base ⁻¹' {x}).Finite := by
  let := normalizationPushforwardStalkAlgebra X hfin x
  have := quasiFinite_normalizationPushforwardStalk hdim hfin x
  have : Finite ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).primesOver
      (normalizationPushforwardStalk X hfin x)) :=
    Algebra.QuasiFinite.finite_primesOver (S := normalizationPushforwardStalk X hfin x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have : Finite (MaximalSpectrum (normalizationPushforwardStalk X hfin x)) :=
    Finite.of_injective
      (fun M : MaximalSpectrum (normalizationPushforwardStalk X hfin x) =>
        (⟨M.asIdeal, M.isMaximal.isPrime, liesOver_maximalIdeal_of_isMaximal hfin x M⟩ :
          ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).primesOver
            (normalizationPushforwardStalk X hfin x))))
      fun M N h => MaximalSpectrum.ext (congrArg Subtype.val h)
  obtain ⟨eq, -⟩ := normalizationFiberEquivMaximalSpectrum X hfin x
  have : Finite {y : Scheme.normalizationScheme X hfin //
      Scheme.normalization X hfin y = x} := Finite.of_equiv _ eq.symm
  rw [← Set.finite_coe_iff]
  exact Finite.of_equiv _
    (Equiv.subtypeEquivRight (p := fun y : Scheme.normalizationScheme X hfin =>
      Scheme.normalization X hfin y = x) fun y => by simp)


/-- The residue field extension at a point of the fibre of the normalization over `x` is
finite: that residue field is the quotient of the pushforward stalk `C` by the maximal ideal
matching the point, and quasi-finiteness makes the fibre `κ(𝔪) ⊗_A C`, of which the quotient is
a quotient, a finite `κ(x)`-module. -/
@[ega "0 23.2.6" "special case"]
private theorem finite_residueFieldMap_fibre {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (x : X)
    (y : {y : Scheme.normalizationScheme X hfin // Scheme.normalization X hfin y = x}) :
    (((Scheme.normalization X hfin).residueFieldMap y.1).hom.comp
      (X.residueFieldCongr y.2.symm).hom.hom).Finite := by
  classical
  let := normalizationPushforwardStalkAlgebra X hfin x
  have := quasiFinite_normalizationPushforwardStalk hdim hfin x
  obtain ⟨fe, hcomp⟩ := normalizationFiberEquivMaximalSpectrum X hfin x
  obtain ⟨e, -, hsq⟩ := hcomp y
  have : (fe y).asIdeal.IsMaximal := (fe y).isMaximal
  let f := ((Scheme.normalization X hfin).residueFieldMap y.1).hom.comp
    (X.residueFieldCongr y.2.symm).hom.hom
  let : Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (normalizationPushforwardStalk X hfin x ⧸ (fe y).asIdeal) := (e.toRingHom.comp f).toAlgebra
  have : IsScalarTower (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (normalizationPushforwardStalk X hfin x ⧸ (fe y).asIdeal) :=
    IsScalarTower.of_algebraMap_eq' hsq.symm
  have hg : (e.toRingHom.comp f).Finite :=
    Stacks.finite_residueField_of_quasiFinite
      (Ideal.Quotient.mkₐ (X.presheaf.stalk x) (fe y).asIdeal)
      (Ideal.Quotient.mkₐ_surjective _ _)
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  change f.Finite
  rw [this]
  exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hg

/-- **The residue field extensions induced by the normalization of a one-dimensional locally
Noetherian scheme are finite.** -/
@[ega "0 23.2.6" "special case"]
theorem finite_residueFieldMap_normalization {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (y : Scheme.normalizationScheme X hfin) :
    ((Scheme.normalization X hfin).residueFieldMap y).hom.Finite := by
  have h := finite_residueFieldMap_fibre hdim hfin (Scheme.normalization X hfin y) ⟨y, rfl⟩
  have hid : (X.residueFieldCongr
      (rfl : Scheme.normalization X hfin y = Scheme.normalization X hfin y)).hom.hom =
      RingHom.id (X.residueField (Scheme.normalization X hfin y)) := by
    rw [show X.residueFieldCongr
        (rfl : Scheme.normalization X hfin y = Scheme.normalization X hfin y) =
        Iso.refl (X.residueField (Scheme.normalization X hfin y)) from by
      simp [Scheme.residueFieldCongr]]
    rfl
  rwa [hid, RingHom.comp_id] at h

end AlgebraicGeometry

end
