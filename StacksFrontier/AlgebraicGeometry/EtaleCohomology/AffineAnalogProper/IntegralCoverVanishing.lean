module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.AlgebraicGeometry.Etale.ClosedSubschemeOfNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# An integral surjective cover with no higher constant cohomology on closed subschemes

Let `X = Spec A` be an affine scheme. Write `A` as a quotient of the polynomial ring
`P = ℤ[x_a : a ∈ A]`, let `L` be an algebraic closure of the fraction field of `P` and `R` the
integral closure of `P` in `L`. Then `X' = Spec R ×_{Spec P} X` is integral and surjective over
`X`, and every closed subscheme `Z'` of `X'` is a closed subscheme of the normal integral affine
scheme `Spec R`, whose function field `L` is algebraically closed. By [Stacks, Tag 09ZC]
`H^q_ét(Z', M) = 0` for every finite abelian group `M` and every `q ≥ 1`. This is part (1) of
[Stacks, Tag 09ZD].

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_constantSheaf_of_isNormal` — Stacks 09ZC read on
  Mathlib's small étale site.
* `Stacks.EtaleCohomology.exists_isIntegralHom_surjective_forall_subsingleton_H` — Stacks 09ZD,
  part (1).

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H` on Mathlib's small étale site
`AlgebraicGeometry.Scheme.smallEtaleTopology`, with coefficients in `AddCommGrpCat.{u + 1}`, the
universe in which that site has sheafification and `Ext`-groups without further hypotheses. The
statement of Stacks 09ZC is proved on the size-bounded small étale site of a big étale site; it
is moved to Mathlib's by `Stacks.EtaleCohomology.ConstantTransport`, after choosing a big étale
site containing the scheme.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
* [Stacks Project, Tag 09ZC](https://stacks.math.columbia.edu/tag/09ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks 09ZC on Mathlib's small étale site.** Let `X` be a normal integral affine scheme
with separably closed function field and `Z ⟶ X` a closed immersion. For every finite abelian
group `M` and `q ≥ 1`, `H^q_ét(Z, M) = 0`. -/
theorem subsingleton_H_constantSheaf_of_isNormal
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNormal X]
    [IsSepClosed X.functionField]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) := by
  obtain ⟨B, hZ⟩ := BigEtaleSite.exists_contains Z
  have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B Z hZ) AddCommGrpCat.{u + 1}) :=
    smallEtaleSheaf_hasExt B Z hZ
  exact ConstantTransport.subsingleton_H_smallEtale_of_boundedSmallEtale B Z hZ M q
    (AlgebraicGeometry.subsingleton_smallEtaleH_constantSheaf' B X Z i hZ M q hq)

/-- The function field of the spectrum of a domain whose fraction field is algebraically closed
is algebraically closed. -/
theorem isAlgClosed_functionField_spec (R : CommRingCat.{u}) [IsDomain R] (L : Type u) [Field L]
    [Algebra R L] [IsFractionRing R L] [IsAlgClosed L] : IsAlgClosed (Spec R).functionField :=
  IsAlgClosed.of_ringEquiv L _
    (IsLocalization.algEquiv (nonZeroDivisors R) L (Spec R).functionField).toRingEquiv

/-- The spectrum of a ring morphism which is injective and integral is surjective: every prime
of the source lies under a prime of the target (going up). -/
theorem surjective_specMap_of_injective_of_isIntegral {P R : CommRingCat.{u}} (f : P ⟶ R)
    (hinj : Function.Injective f.hom) (hint : f.hom.IsIntegral) : Surjective (Spec.map f) := by
  let := f.hom.toAlgebra
  have : Algebra.IsIntegral P R := ⟨hint⟩
  refine ⟨fun (p : PrimeSpectrum P) => ?_⟩
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R)
    (Ideal.comap_bot_le_of_injective (algebraMap P R) hinj)
  exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum R), PrimeSpectrum.ext hQp⟩

/-- **Stacks Project, Tag 09ZD, part (1).** Let `X` be an affine scheme. There is an integral
surjective morphism `X' ⟶ X` such that for every closed subscheme `Z'` of `X'`, every finite
abelian group `M` and every `q ≥ 1`, `H^q_ét(Z', M) = 0`.

Write `Γ(X, ⊤)` as a quotient of `P = ℤ[x_a : a ∈ Γ(X, ⊤)]`, let `R` be the integral closure of
`P` in an algebraic closure `L` of its fraction field and put `X' = Spec R ×_{Spec P} X`. Then
`X' ⟶ X` is a base change of the integral surjective `Spec R ⟶ Spec P`, and `X' ⟶ Spec R` is a
closed immersion, so every closed subscheme of `X'` is one of `Spec R`. The ring `R` is a normal
domain with fraction field `L`, which is algebraically closed, so Stacks 09ZC applies. -/
theorem exists_isIntegralHom_surjective_forall_subsingleton_H (X : Scheme.{u}) [IsAffine X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), IsIntegralHom π ∧ Surjective π ∧
      ∀ (Z' : Scheme.{u}) (i : Z' ⟶ X') [IsClosedImmersion i]
        (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ), 0 < q →
        Subsingleton (Sheaf.H.{u + 1}
          ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) := by
  classical
  let A := Γ(X, ⊤)
  let P := MvPolynomial A ℤ
  let φ : P →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hφ : Function.Surjective φ := fun a => ⟨MvPolynomial.X a, MvPolynomial.eval₂_X _ _ a⟩
  let K := FractionRing P
  let L := AlgebraicClosure K
  let R := integralClosure P L
  have hPL : Function.Injective (algebraMap P L) := by
    rw [IsScalarTower.algebraMap_eq P K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective P K)
  have : Algebra.IsAlgebraic P L := IsFractionRing.comap_isAlgebraic_iff (K := K).mpr inferInstance
  have hfrac : IsFractionRing R L :=
    integralClosure.isFractionRing_of_algebraic (fun x hx => hPL (hx.trans (map_zero _).symm))
  have : IsIntegrallyClosed R := (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mpr inferInstance
  let Y := Spec (.of R)
  have : IsNormal Y := isNormal_spec_iff.mpr (IsNormalRing.of_isIntegrallyClosed R)
  have : IsAlgClosed Y.functionField := isAlgClosed_functionField_spec (.of R) L
  let s : X ⟶ Spec (.of P) := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  have : IsClosedImmersion s := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  let ρ : Y ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom (algebraMap P R))
  have hint : (algebraMap P R).IsIntegral := (Algebra.IsIntegral.isIntegral (R := P) (A := R) ·)
  have hρint : IsIntegralHom ρ := IsIntegralHom.SpecMap_iff.mpr hint
  have hρsurj : Surjective ρ := surjective_specMap_of_injective_of_isIntegral _
    (fun x y h => hPL (by simpa using congrArg (fun r : R => (r : L)) h)) hint
  exact ⟨pullback ρ s, pullback.snd ρ s, inferInstance, inferInstance, fun Z' i _ M _ q hq =>
    subsingleton_H_constantSheaf_of_isNormal Y Z' (i ≫ pullback.fst ρ s) M q hq⟩

end Stacks.EtaleCohomology
