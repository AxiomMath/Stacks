module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkIntegralClosureLocalization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# The local rings of the normalization

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components, let `ν`
be its normalization and let `y` be a point of the normalization lying over `x`.  The local ring
`𝒪_{Y,y}` is a localization at a prime ideal of the integral closure of `𝒪_{X,x}` in the product
of the residue fields of the minimal primes of `𝒪_{X,x}`.

Indeed `Y ×_X Spec 𝒪_{X,x}` is the spectrum of that integral closure, by Tag 0C3B, and its first
projection is a flat preimmersion, so it has a point over `y` carrying the same local ring.

## Main results

* `AlgebraicGeometry.Scheme.exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime`:
  `𝒪_{Y,y}` is a localization at a prime of the integral closure of `𝒪_{X,x}` in the product of
  the residue fields of the minimal primes of `𝒪_{X,x}`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- **The local rings of the normalization are localizations of an integral closure.** Let `X` be
a scheme whose quasi-compact opens have finitely many irreducible components, let `x` be a point
of `X` and let `y` be a point of the normalization of `X` lying over `x`.  Then the local ring of
the normalization at `y` is the localization at a prime ideal of the integral closure of
`𝒪_{X,x}` in the product of the residue fields of the minimal primes of `𝒪_{X,x}`. -/
theorem exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (y : X.normalizationScheme hX)
    (hy : (normalization X hX).base y = x) :
    ∃ p : PrimeSpectrum ↥(integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))),
      Nonempty ((X.normalizationScheme hX).presheaf.stalk y ≃+*
        Localization.AtPrime p.asIdeal) := by
  have hinst : (minimalPrimes.residueFieldProductHom (X.presheaf.stalk x)).toAlgebra =
      (inferInstance :
        Algebra (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  obtain ⟨w, hw, hiso⟩ :=
    exists_point_pullback_fromSpecStalk_isIso_stalkMap (normalization X hX) x y hy
  obtain ⟨e, -⟩ := exists_iso_pullback_normalization_fromSpecStalk X hX x
  rw [hinst] at e
  subst hw
  refine ⟨e.hom.base w, ⟨((asIso ((pullback.fst (normalization X hX)
    (X.fromSpecStalk x)).stalkMap w)).trans
      ((asIso (e.hom.stalkMap w)).symm.trans
        (Spec.stalkIso _ (e.hom.base w)))).commRingCatIsoToRingEquiv⟩⟩

/-- **The local rings of the normalization, described downstairs of a localization.** Suppose in
addition that `𝒪_{X,x}` is the localization at a submonoid `M` of a ring `R` whose reduction has
an artinian total ring of fractions.  Then the local ring of the normalization of `X` at a point
`y` over `x` is the localization at a prime ideal of the integral closure of `R` in the total
ring of fractions of the reduction of `R`.

In the reduced fibre theorem `R` is a tensor product `𝒪_{X,x} ⊗_A B` and this is the
identification of `𝒪_{Y,y}` with a local ring of an integral closure which Stacks 09IL asserts
without proof. -/
theorem exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_of_isLocalization
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (R : Type u) [CommRing R] [Algebra R (X.presheaf.stalk x)] (M : Submonoid R)
    [IsLocalization M (X.presheaf.stalk x)]
    [IsArtinianRing (FractionRing (R ⧸ _root_.nilradical R))]
    (y : X.normalizationScheme hX) (hy : (normalization X hX).base y = x) :
    ∃ p : PrimeSpectrum ↥(integralClosure R (FractionRing (R ⧸ _root_.nilradical R))),
      Nonempty ((X.normalizationScheme hX).presheaf.stalk y ≃+*
        Localization.AtPrime p.asIdeal) := by
  let T := ↥(integralClosure R (FractionRing (R ⧸ _root_.nilradical R)))
  let W := Localization (Algebra.algebraMapSubmonoid T M)
  let : Algebra (X.presheaf.stalk x) W := localizationAlgebra M T
  obtain ⟨q, ⟨eStalk⟩⟩ :=
    exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime X hX x y hy
  obtain ⟨eLoc⟩ := nonempty_algEquiv_integralClosure_fractionRing_reduction R
    (X.presheaf.stalk x) M
  let f : ↥(integralClosure (X.presheaf.stalk x)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) ≃+* W :=
    ((minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct (X.presheaf.stalk x)
      (finite_minimalPrimes_stalk X hX x)).mapIntegralClosure.symm.trans eLoc).toRingEquiv
  let p : Ideal W := q.asIdeal.comap f.symm
  have : p.IsPrime := Ideal.IsPrime.comap _
  have hmap : q.asIdeal.primeCompl.map f.toMonoidHom = p.primeCompl := by
    ext w
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, p, Ideal.mem_comap]
    refine ⟨?_, fun hw ↦ ⟨f.symm w, hw, f.apply_symm_apply w⟩⟩
    rintro ⟨a, ha, rfl⟩
    simpa using ha
  refine ⟨⟨p.comap (algebraMap T W), Ideal.IsPrime.comap _⟩, ⟨eStalk.trans
      ((IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime p) f hmap).trans
      (IsLocalization.algEquiv (p.comap (algebraMap T W)).primeCompl
        (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap T W)))
        ).toRingEquiv)⟩⟩

end AlgebraicGeometry.Scheme

end
