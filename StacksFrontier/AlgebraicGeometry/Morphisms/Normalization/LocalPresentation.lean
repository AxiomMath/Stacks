module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.RingTheory.MinimalPrimes.Localization

/-!
# Local presentation of the normalization

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components and
let `x` be a point of `X`. The normalization of `X`, pulled back to the spectrum of the local
ring `A = 𝒪_{X,x}`, is the spectrum of the integral closure of `A` in the product of the
residue fields of the minimal primes of `A`.

## Main results

* `AlgebraicGeometry.exists_iso_pullback_normalization_fromSpecStalk` is the isomorphism over
  `Spec 𝒪_{X,x}`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section ResidueField

/-- The residue field of a local ring presenting the localization of `R` at a prime `P` is the
residue field of `R` at `P`. -/
noncomputable def residueFieldEquivOfIsLocalizationAtPrime {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalization.AtPrime B P] :
    IsLocalRing.ResidueField B ≃+* Ideal.ResidueField P :=
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv P.primeCompl B (Localization.AtPrime P)).toRingEquiv

/-- The residue field isomorphism `residueFieldEquivOfIsLocalizationAtPrime` sends the residue of
the image of `r : R` to the image of `r` in the residue field of `R` at `P`. -/
lemma residueFieldEquivOfIsLocalizationAtPrime_residue {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (B : Type u) [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalization.AtPrime B P] (r : R) :
    residueFieldEquivOfIsLocalizationAtPrime P B
        (IsLocalRing.residue B (algebraMap R B r)) =
      algebraMap R (Ideal.ResidueField P) r := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (Ideal.ResidueField P),
    IsLocalRing.ResidueField.algebraMap_eq]
  exact congrArg (IsLocalRing.residue _)
    ((IsLocalization.algEquiv P.primeCompl B (Localization.AtPrime P)).commutes r)

end ResidueField

section GenericPoints

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- The minimal prime of the ring of sections attached to a generic point of `X` lying in an
affine open. -/
abbrev genericMinimalPrime (η : {η : genericPoints X // η.1 ∈ U}) : Ideal Γ(X, U) :=
  ((genericPointsInOpenEquivMinimalPrimes hU η : minimalPrimes Γ(X, U)) : Ideal Γ(X, U))

/-- The minimal prime attached to a generic point `η` is the prime ideal of `η` in the affine
open. -/
lemma genericMinimalPrime_eq (η : {η : genericPoints X // η.1 ∈ U}) :
    genericMinimalPrime hU η = (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal :=
  genericPointsInOpenEquivMinimalPrimes_asIdeal hU η

/-- The ideal attached to a generic point is a minimal prime of the ring of sections. -/
lemma genericMinimalPrime_mem (η : {η : genericPoints X // η.1 ∈ U}) :
    genericMinimalPrime hU η ∈ minimalPrimes Γ(X, U) :=
  (genericPointsInOpenEquivMinimalPrimes hU η).2

/-- Distinct generic points in an affine open have distinct minimal primes. -/
lemma genericMinimalPrime_injective :
    Function.Injective (genericMinimalPrime hU) := fun _ _ h =>
  (genericPointsInOpenEquivMinimalPrimes hU).injective (Subtype.ext h)

/-- Every minimal prime of the ring of sections of an affine open is attached to a generic point
lying in it. -/
lemma genericMinimalPrime_surjective (p' : Ideal Γ(X, U))
    (hp' : p' ∈ minimalPrimes Γ(X, U)) :
    ∃ η : {η : genericPoints X // η.1 ∈ U}, genericMinimalPrime hU η = p' :=
  ⟨(genericPointsInOpenEquivMinimalPrimes hU).symm ⟨p', hp'⟩,
    congrArg (fun z : minimalPrimes Γ(X, U) => (z : Ideal Γ(X, U)))
      ((genericPointsInOpenEquivMinimalPrimes hU).apply_symm_apply ⟨p', hp'⟩)⟩

/-- The prime of the ring of sections corresponding to a generic point of `X` in an affine
open presents the stalk at that point. -/
lemma isLocalization_stalk_genericPoint (η : {η : genericPoints X // η.1 ∈ U}) :
    letI : Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    IsLocalization (genericMinimalPrime hU η).primeCompl (X.presheaf.stalk η.1.1) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  convert hU.isLocalization_stalk ⟨η.1.1, η.2⟩ using 2
  exact genericMinimalPrime_eq hU η

/-- At a generic point of `X` lying in an affine open, the residue field of `X` is the residue
field of the ring of sections at the corresponding minimal prime. -/
noncomputable def genericResidueFieldEquiv (η : {η : genericPoints X // η.1 ∈ U}) :
    X.residueField η.1.1 ≃+* Ideal.ResidueField (genericMinimalPrime hU η) :=
  let : Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  let := isLocalization_stalk_genericPoint hU η
  residueFieldEquivOfIsLocalizationAtPrime _ (X.presheaf.stalk η.1.1)

/-- The residue field isomorphism `genericResidueFieldEquiv` sends the value of a section `r` at
the generic point `η` to the image of `r` in the residue field at the minimal prime of `η`. -/
lemma genericResidueFieldEquiv_evaluation (η : {η : genericPoints X // η.1 ∈ U})
    (r : Γ(X, U)) :
    genericResidueFieldEquiv hU η ((X.evaluation U η.1.1 η.2) r) =
      algebraMap Γ(X, U) (Ideal.ResidueField (genericMinimalPrime hU η)) r :=
  let : Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  let := isLocalization_stalk_genericPoint hU η
  residueFieldEquivOfIsLocalizationAtPrime_residue _ (X.presheaf.stalk η.1.1) r

/-- The sections of the generic-point residue spectrum over the preimage of an affine open
form the product of the residue fields at the minimal primes of its ring of sections, indexed
by the generic points of `X` lying in that open. -/
noncomputable def genericPreimageSectionsRingEquivResidueFieldProduct
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    Γ(Scheme.genericPointResidueSpectrum X,
        Scheme.fromGenericPointResidueFields X ⁻¹ᵁ U) ≃+*
      minimalPrimes.enumResidueFieldProduct (genericMinimalPrime hU) :=
  (genericPreimageSectionsRingEquiv X U).trans
    (RingEquiv.piCongrRight fun η => genericResidueFieldEquiv hU η)

/-- The isomorphism `genericPreimageSectionsRingEquivResidueFieldProduct` sends the pullback of a
section `r` over the affine open to the image of `r` in the product of the residue fields. -/
lemma genericPreimageSectionsRingEquivResidueFieldProduct_app
    [Finite {η : genericPoints X // η.1 ∈ U}] (r : Γ(X, U)) :
    genericPreimageSectionsRingEquivResidueFieldProduct hU
        ((Scheme.fromGenericPointResidueFields X).app U r) =
      algebraMap Γ(X, U)
        (minimalPrimes.enumResidueFieldProduct (genericMinimalPrime hU)) r := by
  funext η
  exact (congrArg (genericResidueFieldEquiv hU η)
    congr($(genericPreimageSectionsRingEquiv_comp_app X U η).hom r)).trans
    (genericResidueFieldEquiv_evaluation hU η r)

end GenericPoints

section Main

variable (X : Scheme.{u})
  (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)

/-- The normalization of a scheme whose quasi-compact opens have finitely many irreducible
components, pulled back to the spectrum of the local ring at a point, is the spectrum of the
integral closure of that local ring in the product of the residue fields of its minimal primes,
as a scheme over that spectrum. -/
theorem exists_iso_pullback_normalization_fromSpecStalk (x : X) :
    ∃ e : pullback (Scheme.normalization X hX) (X.fromSpecStalk x) ≅
        Spec (.of (integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
          (integralClosure (X.presheaf.stalk x)
            (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))))) =
        pullback.snd (Scheme.normalization X hX) (X.fromSpecStalk x) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let f := Scheme.fromGenericPointResidueFields X
  let : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have : Finite (genericPoints (U : Set X)) :=
    (genericPoints.finite (hX U hU.isCompact)).to_subtype
  have : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X U)
      (Scheme.genericPointsInOpenEquiv X U).injective
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization P.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let σ := genericMinimalPrime hU
  have hsurj := genericMinimalPrime_surjective hU
  obtain ⟨u, hu⟩ : ∃ u : minimalPrimes (X.presheaf.stalk x) → {η : genericPoints X // η.1 ∈ U},
      ∀ q, σ (u q) = Ideal.under Γ(X, U) (q : Ideal (X.presheaf.stalk x)) :=
    ⟨fun q => (minimalPrimes.exists_eq_under P (X.presheaf.stalk x) hsurj q).choose,
      fun q => (minimalPrimes.exists_eq_under P (X.presheaf.stalk x) hsurj q).choose_spec⟩
  let : Algebra (minimalPrimes.enumResidueFieldProduct σ)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) :=
    (minimalPrimes.localizationResidueFieldProductHom σ u hu).toAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (minimalPrimes.enumResidueFieldProduct σ) P.primeCompl)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) :=
    minimalPrimes.isLocalization_residueFieldProduct P (X.presheaf.stalk x)
      (genericMinimalPrime_mem hU) (genericMinimalPrime_injective hU) inferInstance u hu
  let : IsScalarTower Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) := by
    refine IsScalarTower.of_algebraMap_eq fun r => funext fun q => ?_
    change algebraMap Γ(X, U) (Ideal.ResidueField (q : Ideal (X.presheaf.stalk x))) r = _
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x)
      (Ideal.ResidueField (q : Ideal (X.presheaf.stalk x)))]
    exact (Ideal.ResidueField.map_algebraMap (σ (u q)) (q : Ideal (X.presheaf.stalk x))
      (algebraMap Γ(X, U) (X.presheaf.stalk x)) (hu q) r).symm
  let : Algebra (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) :=
    RingHom.toAlgebra
      { toFun := fun y => ⟨algebraMap (minimalPrimes.enumResidueFieldProduct σ)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) y.1,
          (y.2.map (IsScalarTower.toAlgHom Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)
            (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))).tower_top⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  let : IsScalarTower (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))
      (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) := .of_algebraMap_eq' rfl
  let : IsScalarTower Γ(X, U)
      (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) :=
    IsScalarTower.of_algebraMap_eq fun y => Subtype.ext
      (IsScalarTower.algebraMap_apply Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) y)
  let : IsLocalization
      (Submonoid.map
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)))
        P.primeCompl)
      (integralClosure (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x))) :=
    IsLocalization.integralClosure P.primeCompl
  let : Algebra Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  let eSA : Γ(Scheme.genericPointResidueSpectrum X, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      minimalPrimes.enumResidueFieldProduct σ :=
    AlgEquiv.ofRingEquiv (f := genericPreimageSectionsRingEquivResidueFieldProduct hU)
      (genericPreimageSectionsRingEquivResidueFieldProduct_app hU)
  let eIC := eSA.mapIntegralClosure
  let iso1 : (f.fromNormalization ⁻¹ᵁ U).toScheme ≅
      Spec (.of (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))) :=
    relativeNormalizationPreimageIso f U hU ≪≫
      Scheme.Spec.mapIso eIC.toRingEquiv.toCommRingCatIso.symm.op
  have he : CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))) ≫
      eIC.toRingEquiv.toCommRingCatIso.symm.hom =
      CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) Γ(Scheme.genericPointResidueSpectrum X, f ⁻¹ᵁ U))) := by
    ext a
    exact congrArg Subtype.val (eIC.symm.commutes a)
  have hiso1 : iso1.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)))) =
      (f.fromNormalization ∣_ U) ≫ hU.isoSpec.hom := by
    change ((relativeNormalizationPreimageIso f U hU).hom ≫
        Spec.map eIC.toRingEquiv.toCommRingCatIso.symm.hom) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U)
            (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)))) = _
    rw [Category.assoc, ← Spec.map_comp, he]
    exact relativeNormalizationPreimageIso_comp f U hU
  have htop : IsPullback (iso1.inv ≫ (f.fromNormalization ⁻¹ᵁ U).ι)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)))))
      f.fromNormalization hU.fromSpec :=
    ((isPullback_morphismRestrict f.fromNormalization U).flip).of_iso
      iso1 (Iso.refl _) hU.isoSpec (Iso.refl _)
      (by simp) hiso1.symm (by simp) (by simp [IsAffineOpen.fromSpec])
  have hH : (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))).comp
        (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      (algebraMap (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))
        (integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))).comp
        (algebraMap Γ(X, U)
          (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ))) :=
    RingHom.ext fun r => Subtype.ext <|
      (IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x)
        (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) r).trans
        (IsScalarTower.algebraMap_apply Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)) r)
  have hbot := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) (minimalPrimes.enumResidueFieldProduct σ)))
      (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x)
          (minimalPrimes.residueFieldProduct (X.presheaf.stalk x)))) hH P.primeCompl)
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (X.presheaf.stalk x))) ≫
      hU.fromSpec = X.fromSpecStalk x := hU.fromSpecStalk_eq_fromSpecStalk hxU
  have hfinal := hbot.paste_horiz htop
  rw [hbase] at hfinal
  exact ⟨hfinal.isoPullback.symm,
    (Iso.inv_comp_eq _).mpr hfinal.isoPullback_hom_snd.symm⟩

end Main

end AlgebraicGeometry
