module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Localization.Algebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksFrontier.RingTheory.IntegralClosure.Defs
public import StacksFrontier.RingTheory.MinimalPrimes.Localization
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents

/-!
# Stalk of the normalization

Let `X` be a scheme such that every quasi-compact open has finitely many irreducible
components, and let `Xⁿ ⟶ X` be its normalization. At a point `x`, the stalk of the
pushforward of `𝒪_{Xⁿ}` is canonically the integral closure of `𝒪_{X,x}` both in the total
ring of fractions of its reduction and in the product of the residue fields of its minimal
primes. The set of those minimal primes is finite.

## Main definitions

* `Stacks.NormalizationStalkAmbient.reductionFractionRingHom` and
  `minimalPrimes.residueFieldProductHom` are the canonical maps from a ring into the two ambient
  algebras: the total ring of fractions of its reduction, and the product of the residue fields
  of its minimal primes.
* `AlgebraicGeometry.Scheme.normalizationPushforwardStalk` is the stalk at `x` of the
  pushforward of the structure sheaf of the normalization.

## Main results

* `isFractionRing_localization_of_artinian`: a localization of a ring has for its total ring of
  fractions the localization of the ring's own total ring of fractions, provided the latter is
  Artinian.

The remaining results live in the `AlgebraicGeometry.Scheme` namespace.

* `normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing` identifies the
  normalization stalk with the integral closure in the total ring of fractions of the reduction.
* `normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields` identifies it with
  the integral closure in the product of the residue fields of the minimal primes.
* `finite_minimalPrimes_stalk`: those minimal primes form a finite set.
* `pushforwardStalk_isLocalization`: for an affine open `U` containing `x` and a quasi-compact
  quasi-separated `f : Y ⟶ X`, the stalk at `x` of `f _* 𝒪_Y` is the localization of
  `Γ(Y, f ⁻¹ᵁ U)` at the image of the prime of `x`.

## Implementation notes

The reduction of a ring `A` is represented by `A ⧸ nilradical A`, and the residue field at a
prime `p` by `Ideal.ResidueField p`. The algebra structure on the pushforward stalk is induced
by the stalk of the structure-sheaf map of the normalization morphism. Thus both displayed
equivalences are equivalences over `𝒪_{X,x}` and in particular record the canonical
compatibility with the local-ring maps. The subalgebra form of the integral closure is
Mathlib's `integralClosure`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace minimalPrimes

/-- The canonical map from a ring to the product of the residue fields of its minimal
primes. -/
public noncomputable def residueFieldProductHom (A : Type*) [CommRing A] :
    A →+* residueFieldProduct A :=
  RingHom.pi fun p : minimalPrimes A ↦
    letI : p.1.IsPrime := p.2.1.1
    algebraMap A p.1.ResidueField

private noncomputable def reductionEquiv (A : Type*) [CommRing A] :
    minimalPrimes (A ⧸ nilradical A) ≃ minimalPrimes A := by
  classical
  let f := Ideal.Quotient.mk (nilradical A)
  have hset : minimalPrimes A = Ideal.comap f '' minimalPrimes (A ⧸ nilradical A) := by
    rw [← Ideal.minimalPrimes_eq_comap]
    simp [nilradical, Ideal.radical_minimalPrimes, minimalPrimes]
  let g : minimalPrimes (A ⧸ nilradical A) → minimalPrimes A := fun q =>
    ⟨Ideal.comap f q.1, by
      rw [hset]
      exact ⟨q, q.2, rfl⟩⟩
  have hinj : Function.Injective g := by
    intro q q' h
    exact Subtype.ext ((Ideal.comap_injective_of_surjective f Ideal.Quotient.mk_surjective)
      (congrArg Subtype.val h))
  have hsurj : Function.Surjective g := by
    intro p
    obtain ⟨q, hq, hp⟩ : (p : Ideal A) ∈ Ideal.comap f '' minimalPrimes (A ⧸ nilradical A) :=
      hset ▸ p.2
    exact ⟨⟨q, hq⟩, Subtype.ext hp⟩
  exact Equiv.ofBijective g ⟨hinj, hsurj⟩

/-- The total fraction ring of a ring's reduction, written as the product of the residue
fields at the ring's minimal primes. -/
@[no_expose] public noncomputable def reductionFractionRingAlgEquivResidueFieldProduct
    (A : Type*) [CommRing A] (hA : (minimalPrimes A).Finite) :
    letI (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
    FractionRing (A ⧸ nilradical A) ≃ₐ[A] residueFieldProduct A := by
  classical
  let R := A ⧸ nilradical A
  let f : A →+* R := Ideal.Quotient.mk (nilradical A)
  let : Algebra A R := f.toAlgebra
  let : IsScalarTower A R (FractionRing R) := .of_algebraMap_eq' rfl
  let : IsReduced R :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  have hR : (minimalPrimes R).Finite :=
    finite_minimalPrimes_quotient_nilradical A hA
  let : Finite (minimalPrimes R) := hR
  let (q : minimalPrimes R) : q.1.IsPrime := q.2.1.1
  let (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  let (q : minimalPrimes R) : Algebra R (FractionRing (R ⧸ (q : Ideal R))) :=
    ((algebraMap (R ⧸ (q : Ideal R)) (FractionRing (R ⧸ (q : Ideal R)))).comp
      (Ideal.Quotient.mk (q : Ideal R))).toAlgebra
  let eIndex : minimalPrimes R ≃ minimalPrimes A := reductionEquiv A
  let eTotal := Classical.choice <|
    minimalPrimes.totalFractionRing_algEquiv_pi_fractionRing_quotient
      (A := A ⧸ nilradical A) hR
  let eFracFields : (∀ q : minimalPrimes R, FractionRing (R ⧸ (q : Ideal R))) ≃ₐ[R]
      (∀ q : minimalPrimes R, q.1.ResidueField) :=
    AlgEquiv.piCongrRight fun q => by
      let : IsFractionRing (R ⧸ (q : Ideal R)) q.1.ResidueField := inferInstance
      let er : FractionRing (R ⧸ (q : Ideal R)) ≃+* q.1.ResidueField :=
        IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl (R ⧸ (q : Ideal R)))
      exact AlgEquiv.ofRingEquiv (f := er) fun r => by
        change er (algebraMap (R ⧸ (q : Ideal R)) (FractionRing (R ⧸ (q : Ideal R)))
          (Ideal.Quotient.mk (q : Ideal R) r)) =
          algebraMap (R ⧸ (q : Ideal R)) q.1.ResidueField (Ideal.Quotient.mk (q : Ideal R) r)
        rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
        rfl
  let eResidue : (q : minimalPrimes R) →
      q.1.ResidueField ≃+* (eIndex q).1.ResidueField := by
    intro q
    let p := eIndex q
    let : p.1.IsPrime := p.2.1.1
    let : q.1.IsPrime := q.2.1.1
    have hp : p.1 = q.1.comap f := rfl
    let hmap := Ideal.ResidueField.map p.1 q.1 f hp
    have hmapBij : Function.Bijective hmap :=
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
        |>.residueFieldMap_bijective p.1 q.1 hp
    exact (RingEquiv.ofBijective hmap hmapBij).symm
  let : Algebra A (∀ q : minimalPrimes R, q.1.ResidueField) :=
    ((algebraMap R (∀ q : minimalPrimes R, q.1.ResidueField)).comp f).toAlgebra
  let eComponents : (∀ q : minimalPrimes R, q.1.ResidueField) ≃ₐ[A]
      (∀ q : minimalPrimes R, (eIndex q).1.ResidueField) := by
    let er : (∀ q : minimalPrimes R, q.1.ResidueField) ≃+*
        (∀ q : minimalPrimes R, (eIndex q).1.ResidueField) :=
      RingEquiv.piCongrRight eResidue
    exact AlgEquiv.ofRingEquiv (f := er) fun a => by
      funext q
      let p := eIndex q
      let : p.1.IsPrime := p.2.1.1
      let : q.1.IsPrime := q.2.1.1
      let : Algebra A q.1.ResidueField :=
        ((algebraMap R q.1.ResidueField).comp f).toAlgebra
      let : Algebra A p.1.ResidueField := (algebraMap A p.1.ResidueField).toAlgebra
      have hp : p.1 = q.1.comap f := rfl
      let hmap := Ideal.ResidueField.map p.1 q.1 f hp
      have hmapBij : Function.Bijective hmap :=
        (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
          |>.residueFieldMap_bijective p.1 q.1 hp
      let erq : p.1.ResidueField ≃+* q.1.ResidueField :=
        RingEquiv.ofBijective hmap hmapBij
      change erq.symm (algebraMap R q.1.ResidueField (f a)) =
        algebraMap A p.1.ResidueField a
      rw [← Ideal.ResidueField.map_algebraMap p.1 q.1 f hp a]
      change erq.symm (erq (algebraMap A p.1.ResidueField a)) = _
      exact erq.symm_apply_apply _
  let eReindex : (∀ q : minimalPrimes R, (eIndex q).1.ResidueField) ≃ₐ[A]
      residueFieldProduct A :=
    AlgEquiv.piCongrLeft (R := A) (A₁ := fun p : minimalPrimes A => p.1.ResidueField) eIndex
  let : Algebra A (∀ q : minimalPrimes R, FractionRing (R ⧸ (q : Ideal R))) :=
    ((algebraMap R (∀ q : minimalPrimes R, FractionRing (R ⧸ (q : Ideal R)))).comp f).toAlgebra
  let eTotalA : FractionRing R ≃ₐ[A]
      (∀ q : minimalPrimes R, FractionRing (R ⧸ (q : Ideal R))) :=
    AlgEquiv.ofRingEquiv (f := eTotal.toRingEquiv) fun a =>
      funext fun q => congrFun (eTotal.commutes (f a)) q
  let eFracFieldsA : (∀ q : minimalPrimes R, FractionRing (R ⧸ (q : Ideal R))) ≃ₐ[A]
      (∀ q : minimalPrimes R, q.1.ResidueField) :=
    AlgEquiv.ofRingEquiv (f := eFracFields.toRingEquiv) fun a =>
      funext fun q => congrFun (eFracFields.commutes (f a)) q
  exact eTotalA.trans (eFracFieldsA.trans (eComponents.trans eReindex))

end minimalPrimes

/-- A localization of a ring at a submonoid has for its total ring of fractions the
localization at the image of that submonoid of the total ring of fractions of the ring,
provided the latter is Artinian. -/
public theorem isFractionRing_localization_of_artinian
    {R Q A B : Type*} [CommRing R] [CommRing Q] [CommRing A] [CommRing B]
    [Algebra R Q] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra Q B]
    [IsScalarTower R A B] [IsScalarTower R Q B]
    (M : Submonoid R) [IsLocalization M A] [IsFractionRing R Q]
    [IsLocalization (Algebra.algebraMapSubmonoid Q M) B] [IsArtinianRing Q] :
    IsFractionRing A B := by
  have := IsLocalization.commutes A Q B M (nonZeroDivisors R)
  have : IsArtinianRing B := IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid Q M) B
  exact IsLocalization.of_le (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
    (nonZeroDivisors A) (IsLocalization.map_nonZeroDivisors_le M A) fun _ ha =>
      IsArtinianRing.isUnit_of_mem_nonZeroDivisors
        (IsLocalization.nonZeroDivisors_le_comap
          (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) B ha)

namespace AlgebraicGeometry.Scheme

/-- The stalk at `x` of the pushforward of the structure sheaf of the normalization of `X`. -/
public abbrev normalizationPushforwardStalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : CommRingCat.{u} :=
  let ν := normalization X hX
  (TopCat.Presheaf.stalkFunctor CommRingCat x).obj
    ((TopCat.Sheaf.pushforward CommRingCat ν.base).obj
      (normalizationScheme X hX).sheaf).presheaf

/-- The canonical `𝒪_{X,x}`-algebra structure on the stalk of the pushforward of the
structure sheaf of the normalization. -/
@[instance_reducible]
public noncomputable def normalizationPushforwardStalkAlgebra (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
  let ν := normalization X hX
  ((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.toAlgebra

private lemma residueFieldCongr_evaluation_eq {X : Scheme.{u}} (U : X.Opens)
    {x y : X} (h : x = y) (hx : x ∈ U) (hy : y ∈ U)
    (a : Γ(X, U)) :
    (X.residueFieldCongr h).symm.hom (X.evaluation U y hy a) =
      X.evaluation U x hx a := by
  cases h
  rfl

private def residueFieldEquivOfEq {R : Type*} [CommRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (h : p = q) :
    p.ResidueField ≃+* q.ResidueField := by
  subst q
  exact RingEquiv.refl _

private lemma residueFieldEquivOfEq_algebraMap {R : Type*} [CommRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (h : p = q) (r : R) :
    residueFieldEquivOfEq p q h (algebraMap R p.ResidueField r) =
      algebraMap R q.ResidueField r := by
  subst q
  rfl

/-- The affine chart sends a generic point of `U` to itself. -/
private lemma fromSpec_isoSpec_hom_generic {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    hU.fromSpec (hU.isoSpec.hom ⟨η.1.1, η.2⟩) = η.1.1 := by
  change (hU.isoSpec.hom ≫ hU.fromSpec) ⟨η.1.1, η.2⟩ = η.1.1
  rw [hU.isoSpec_hom_fromSpec]
  rfl

/-- The minimal prime attached to a generic point is the prime of its image in `Spec`. -/
private lemma genericPointsInOpenEquivMinimalPrimes_eq_isoSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (η : {η : genericPoints X // η.1 ∈ U}) :
    (genericPointsInOpenEquivMinimalPrimes hU η : Ideal Γ(X, U)) =
      (hU.isoSpec.hom ⟨η.1.1, η.2⟩).asIdeal := by
  simpa [IsAffineOpen.primeIdealOf] using genericPointsInOpenEquivMinimalPrimes_asIdeal hU η

private noncomputable def genericPointResidueFieldEquivMinimalPrime
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (η : {η : genericPoints X // η.1 ∈ U}) :
    X.residueField η.1.1 ≃+*
      @Ideal.ResidueField (Γ(X, U)) _
        (genericPointsInOpenEquivMinimalPrimes hU η).1
        (genericPointsInOpenEquivMinimalPrimes hU η).2.1.1 := by
  let A := Γ(X, U)
  let eIndex := genericPointsInOpenEquivMinimalPrimes hU
  let : (eIndex η).1.IsPrime := (eIndex η).2.1.1
  let xU : U.toScheme := ⟨η.1.1, η.2⟩
  let xSpec : Spec (.of A) := hU.isoSpec.hom xU
  let : xSpec.asIdeal.IsPrime := xSpec.2
  let eSpec : Spec (.of A) ≅ U.toScheme := hU.isoSpec.symm
  let j : Spec (.of A) ⟶ X := eSpec.hom ≫ U.ι
  have hj : j xSpec = η.1.1 := fromSpec_isoSpec_hom_generic hU η
  have hq : (eIndex η : Ideal A) = xSpec.asIdeal :=
    genericPointsInOpenEquivMinimalPrimes_eq_isoSpec hU η
  let eCast : (eIndex η).1.ResidueField ≃+* xSpec.asIdeal.ResidueField :=
    residueFieldEquivOfEq (eIndex η).1 xSpec.asIdeal hq
  let eRes : X.residueField η.1.1 ≃+* xSpec.asIdeal.ResidueField :=
    (X.residueFieldCongr hj).symm.commRingCatIsoToRingEquiv.trans
      ((asIso (j.residueFieldMap xSpec)).commRingCatIsoToRingEquiv.trans
        ((Scheme.Spec.residueFieldIso (.of A) xSpec).commRingCatIsoToRingEquiv))
  exact eRes.trans eCast.symm

private lemma genericPointResidueFieldEquivMinimalPrime_evaluation
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (η' : {η : genericPoints X // η.1 ∈ U}) (a : Γ(X, U)) :
    let q := genericPointsInOpenEquivMinimalPrimes hU η'
    let : q.1.IsPrime := q.2.1.1
    genericPointResidueFieldEquivMinimalPrime X U hU η'
      (X.evaluation U η'.1.1 η'.2 a) = algebraMap Γ(X, U) q.1.ResidueField a := by
  let A := Γ(X, U)
  let eIndex := genericPointsInOpenEquivMinimalPrimes hU
  let ePoint := genericPointResidueFieldEquivMinimalPrime X U hU
  let z := η'.1.1
  have hηU : z ∈ U := η'.2
  let xU : U.toScheme := ⟨z, hηU⟩
  let xSpec : (Spec (.of A)) := hU.isoSpec.hom xU
  let : xSpec.asIdeal.IsPrime := xSpec.2
  let q := eIndex η'
  let : q.1.IsPrime := q.2.1.1
  let j : Spec (.of A) ⟶ X := hU.fromSpec
  have hj : j xSpec = z := fromSpec_isoSpec_hom_generic hU η'
  have hq : (q : Ideal A) = xSpec.asIdeal :=
    genericPointsInOpenEquivMinimalPrimes_eq_isoSpec hU η'
  let eSpecRes : (Spec (.of A)).residueField xSpec ≃+* xSpec.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso (.of A) xSpec).commRingCatIsoToRingEquiv
  let eJRes : X.residueField z ≃+* (Spec (.of A)).residueField xSpec :=
    (X.residueFieldCongr hj).symm.commRingCatIsoToRingEquiv.trans
      ((asIso (j.residueFieldMap xSpec)).commRingCatIsoToRingEquiv)
  let eCast : q.1.ResidueField ≃+* xSpec.asIdeal.ResidueField :=
    residueFieldEquivOfEq q.1 xSpec.asIdeal hq
  show ePoint η' (X.evaluation U z hηU a) = _
  unfold ePoint
  show eCast.symm (eSpecRes (eJRes (X.evaluation U z hηU a))) = _
  have hxj : j xSpec ∈ U := by rwa [hj]
  have hxpre : xSpec ∈ j ⁻¹ᵁ U := hxj
  have hcongr : (X.residueFieldCongr hj).symm.hom
      (X.evaluation U z hηU a) = X.evaluation U (j xSpec) hxj a :=
    residueFieldCongr_evaluation_eq U hj hxj hηU a
  have hnat := Scheme.evaluation_naturality_apply j xSpec hxj a
  unfold eJRes
  show eCast.symm (eSpecRes (j.residueFieldMap xSpec
    ((X.residueFieldCongr hj).symm.hom (X.evaluation U z hηU a)))) = _
  have hspec : eSpecRes
      ((Spec (.of A)).evaluation (j ⁻¹ᵁ U) xSpec hxpre (j.app U a)) =
        algebraMap A xSpec.asIdeal.ResidueField a := by
    rw [← eSpecRes.apply_symm_apply (algebraMap A xSpec.asIdeal.ResidueField a)]
    apply congrArg eSpecRes
    have heval : (Spec (.of (Γ(X, U)))).evaluation
        (j ⁻¹ᵁ U) xSpec hxpre (j.app U a) =
        (Spec (.of (Γ(X, U)))).evaluation ⊤ xSpec (by simp)
          ((Scheme.ΓSpecIso (Γ(X, U))).inv a) := by
      show (((Spec (.of (Γ(X, U)))).presheaf.germ
          (j ⁻¹ᵁ U) xSpec hxpre) ≫ (Spec (.of (Γ(X, U)))).residue xSpec)
          (hU.fromSpec.app U a) =
        (((Spec (.of (Γ(X, U)))).presheaf.germ ⊤ xSpec (by simp)) ≫
          (Spec (.of (Γ(X, U)))).residue xSpec)
          ((Scheme.ΓSpecIso (Γ(X, U))).inv a)
      have hi : (eqToHom hU.fromSpec_preimage_self) =
          (homOfLE (show j ⁻¹ᵁ U ≤ ⊤ from le_top)) := Subsingleton.elim _ _
      rw [hU.fromSpec_app_self, CommRingCat.comp_apply, hi, CommRingCat.comp_apply]
      have hgerm := (Spec (CommRingCat.of (↑Γ(X, U)))).presheaf.germ_res_apply
        (homOfLE (show j ⁻¹ᵁ U ≤ ⊤ from le_top)) xSpec hxpre
        ((Scheme.ΓSpecIso Γ(X, U)).inv a)
      exact congrArg
        (fun t : (Spec (CommRingCat.of (Γ(X, U)))).presheaf.stalk xSpec =>
          ((Spec (CommRingCat.of (Γ(X, U)))).residue xSpec) t) hgerm
    rw [heval]
    have hmap := congrArg (fun φ => φ a)
      (Scheme.Spec.algebraMap_residueFieldIso_inv (.of A) xSpec)
    show (((Spec (.of A)).presheaf.germ ⊤ xSpec (by simp)) ≫
        (Spec (.of A)).residue xSpec) ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.Spec.residueFieldIso (.of A) xSpec).inv
        (algebraMap A xSpec.asIdeal.ResidueField a)
    exact hmap.symm
  have hcast : eCast (algebraMap A q.1.ResidueField a) =
      algebraMap A xSpec.asIdeal.ResidueField a :=
    residueFieldEquivOfEq_algebraMap q.1 xSpec.asIdeal hq a
  rw [hcongr, hnat, hspec, ← hcast, RingEquiv.symm_apply_apply]

/-- The generic-point sections over an affine open form the total fraction ring of its
reduction. -/
private noncomputable def genericPreimageSectionsAlgEquivReductionFractionRing
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (hMin : (minimalPrimes Γ(X, U)).Finite)
    [Finite {η : genericPoints X // η.1 ∈ U}] :
    let A := Γ(X, U)
    let f := fromGenericPointResidueFields X
    let S := Γ(genericPointResidueSpectrum X, f ⁻¹ᵁ U)
    letI : Algebra A S := (f.app U).hom.toAlgebra
    S ≃ₐ[A] FractionRing (A ⧸ _root_.nilradical A) := by
  classical
  let A := Γ(X, U)
  let f := fromGenericPointResidueFields X
  let S := Γ(genericPointResidueSpectrum X, f ⁻¹ᵁ U)
  let I := {η : genericPoints X // η.1 ∈ U}
  let : Algebra A S := (f.app U).hom.toAlgebra
  let (η : I) : Algebra A (X.residueField η.1.1) :=
    (X.evaluation U η.1.1 η.2).hom.toAlgebra
  let eG : S ≃ₐ[A] (∀ η : I, X.residueField η.1.1) :=
    AlgEquiv.ofRingEquiv
      (f := genericPreimageSectionsRingEquiv X U)
      (fun a => funext fun η => congrArg (fun g => g.hom a)
        (genericPreimageSectionsRingEquiv_comp_app X U η))
  let eIndex := genericPointsInOpenEquivMinimalPrimes hU
  let (q : minimalPrimes A) : q.1.IsPrime := q.2.1.1
  let eFields : (∀ η : I, X.residueField η.1.1) ≃ₐ[A]
      (∀ η : I, (eIndex η).1.ResidueField) :=
    AlgEquiv.piCongrRight fun η => AlgEquiv.ofRingEquiv
      (f := genericPointResidueFieldEquivMinimalPrime X U hU η)
      (genericPointResidueFieldEquivMinimalPrime_evaluation X U hU η)
  let eReindex : (∀ η : I, (eIndex η).1.ResidueField) ≃ₐ[A]
      minimalPrimes.residueFieldProduct A :=
    AlgEquiv.piCongrLeft (R := A) (A₁ := fun q : minimalPrimes A => q.1.ResidueField) eIndex
  exact eG.trans (eFields.trans (eReindex.trans
    (minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct A hMin).symm))

/-- The local ring of `X` at `x` has only finitely many minimal primes. -/
public theorem finite_minimalPrimes_stalk (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) : (minimalPrimes (X.presheaf.stalk x)).Finite := by
  classical
  obtain ⟨U, hU, hxU, hUtop⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let xU : U := ⟨x, hxU⟩
  let R := X.presheaf.obj (.op U)
  have hR : (minimalPrimes R).Finite :=
    finite_minimalPrimes_of_affine_open hX U hU.isoSpec.symm
  have hcomp : (irreducibleComponents (PrimeSpectrum R)).Finite :=
    have := hR.to_subtype
    Set.finite_coe_iff.mp (.of_equiv _ (minimalPrimes.equivIrreducibleComponents R).toEquiv)
  let p := hU.primeIdealOf xU
  have hthrough : (PrimeSpectrum.irreducibleComponentsThrough R p.asIdeal).Finite :=
    hcomp.subset fun _ hC => hC.1
  have : Finite (minimalPrimes (Localization.AtPrime p.asIdeal)) := by
    let e := PrimeSpectrum.irreducibleComponentsThroughEquiv R p.asIdeal
      (Localization.AtPrime p.asIdeal)
    have : Finite ↑(PrimeSpectrum.irreducibleComponentsThrough R p.asIdeal) := hthrough.to_subtype
    exact Finite.of_equiv _ e
  let : Algebra (X.presheaf.obj (.op U)) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xU
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk xU
  let eLoc : Localization.AtPrime p.asIdeal ≃ₐ[R] X.presheaf.stalk x :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (X.presheaf.stalk x)
  let g : X.presheaf.stalk x →+* Localization.AtPrime p.asIdeal :=
    eLoc.toRingEquiv.symm.toRingHom
  show ((⊥ : Ideal (X.presheaf.stalk x)).minimalPrimes).Finite
  have hEq : (⊥ : Ideal (Localization.AtPrime p.asIdeal)).comap g = ⊥ := by
    ext a
    simp [g]
  have hSurj : Function.Surjective g := eLoc.toRingEquiv.symm.surjective
  rw [← hEq, Ideal.comap_minimalPrimes_eq_of_surjective hSurj (⊥ : Ideal _)]
  exact (Set.toFinite _).image (Ideal.comap g)

/-- The stalk at `x` of the pushforward `f _* 𝒪_Y` along a quasi-compact quasi-separated
morphism is the localization of `Γ(Y, f ⁻¹ᵁ U)`, for an affine open `U` containing `x`, at the
image of the complement of the prime corresponding to `x`. -/
public lemma pushforwardStalk_isLocalization {Y X : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    let F := f.base _* Y.presheaf
    letI : Algebra Γ(Y, f ⁻¹ᵁ U) (F.stalk x) := (F.germ U x hx).hom.toAlgebra
    IsLocalization (((hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl).map (f.app U).hom)
      (F.stalk x) := by
  let F := f.base _* Y.presheaf
  let S := Γ(Y, f ⁻¹ᵁ U)
  let p := hU.primeIdealOf ⟨x, hx⟩
  let : Algebra S (F.stalk x) := (F.germ U x hx).hom.toAlgebra
  have hloc (r : Γ(X, U)) :
      let : Algebra S Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
        (F.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
      IsLocalization.Away (f.app U r) Γ(Y, f ⁻¹ᵁ X.basicOpen r) := by
    dsimp +instances [F, S]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hU.isCompact)
      (f.isQuasiSeparated_preimage hU.isQuasiSeparated) (f.app U r)
  have hpr (r : Γ(X, U)) (hr : x ∈ X.basicOpen r) : r ∈ p.asIdeal.primeCompl := by
    show p ∈ PrimeSpectrum.basicOpen r
    rw [← hU.fromSpec_preimage_basicOpen r]
    show hU.fromSpec p ∈ X.basicOpen r
    rwa [hU.fromSpec_primeIdealOf]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    show IsUnit ((F.germ U x hx) (f.app U r))
    show IsUnit ((f.c.app (op U) ≫ F.germ U x hx) r)
    rw [← TopCat.Presheaf.stalkFunctor_map_germ]
    let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact (IsLocalization.map_units (X.presheaf.stalk x) ⟨r, hr⟩).map
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f.c).hom
  · intro z
    obtain ⟨V, hxV, s, hs⟩ := F.exists_germ_eq z
    obtain ⟨r, hrV, hr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    let s' : Γ(Y, f ⁻¹ᵁ X.basicOpen r) := F.map (homOfLE hrV).op s
    have hs' : F.germ (X.basicOpen r) x hr s' = z :=
      (F.germ_res_apply (homOfLE hrV) x hr s).trans hs
    let : Algebra S Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
      (F.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    have := hloc r
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (.powers (f.app U r)) s'
    refine ⟨⟨a, ⟨f.app U r ^ n, ⟨r ^ n, p.asIdeal.primeCompl.pow_mem (hpr r hr) n,
      map_pow _ _ _⟩⟩⟩, ?_⟩
    show z * F.germ U x hx (f.app U r ^ n) = F.germ U x hx a
    rw [← hs', ← F.germ_res_apply (homOfLE (X.basicOpen_le r)) x hr,
      ← F.germ_res_apply (homOfLE (X.basicOpen_le r)) x hr, ← map_mul]
    exact congrArg (F.germ (X.basicOpen r) x hr) ha
  · intro a b hab
    change F.germ U x hx a = F.germ U x hx b at hab
    obtain ⟨V, hxV, i, j, hij⟩ := F.germ_eq x hx hx a b hab
    obtain ⟨r, hrV, hr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    let : Algebra S Γ(Y, f ⁻¹ᵁ X.basicOpen r) :=
      (F.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    have := hloc r
    have hab' : algebraMap S Γ(Y, f ⁻¹ᵁ X.basicOpen r) a =
        algebraMap S Γ(Y, f ⁻¹ᵁ X.basicOpen r) b := by
      have := congrArg (F.map (homOfLE hrV).op) hij
      show F.map (homOfLE (X.basicOpen_le r)).op a =
        F.map (homOfLE (X.basicOpen_le r)).op b
      simpa only [← CommRingCat.comp_apply, ← Functor.map_comp,
        show i.op ≫ (homOfLE hrV).op = (homOfLE (X.basicOpen_le r)).op from
          Subsingleton.elim _ _,
        show j.op ≫ (homOfLE hrV).op = (homOfLE (X.basicOpen_le r)).op from
          Subsingleton.elim _ _] using this
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := .powers (f.app U r)) hab'
    exact ⟨⟨f.app U r ^ n, ⟨r ^ n, p.asIdeal.primeCompl.pow_mem (hpr r hr) n,
      map_pow _ _ _⟩⟩, hn⟩

/-- The total ring of fractions of the reduction of a localization of `R` at `M`, written as
the localization at the image of `M` of the total ring of fractions of the reduction of `R`. -/
@[no_expose] public noncomputable def fractionRingReductionLocalizationEquiv
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A]
    [IsArtinianRing (FractionRing (R ⧸ _root_.nilradical R))] :
    let S := FractionRing (R ⧸ _root_.nilradical R)
    let L := Localization (Algebra.algebraMapSubmonoid S M)
    letI : Algebra A L := localizationAlgebra M S
    L ≃ₐ[A] FractionRing (A ⧸ _root_.nilradical A) := by
  let R₀ := R ⧸ _root_.nilradical R
  let A₀ := A ⧸ _root_.nilradical A
  let S := FractionRing R₀
  let L := Localization (Algebra.algebraMapSubmonoid S M)
  let M₀ := Algebra.algebraMapSubmonoid R₀ M
  have hn : (_root_.nilradical R).map (algebraMap R A) = _root_.nilradical A := by
    simpa only [_root_.nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      IsLocalization.map_radical M A (⊥ : Ideal R)
  let : Algebra R₀ A₀ := Ideal.Quotient.algebraQuotientOfLEComap
    (show _root_.nilradical R ≤ (_root_.nilradical A).comap (algebraMap R A) from
      Ideal.map_le_iff_le_comap.mp hn.le)
  have : IsLocalization M₀ A₀ :=
    IsLocalization.of_surjective M A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker]
        exact hn.ge)
  have : IsLocalization (Algebra.algebraMapSubmonoid S M₀) L := by
    change IsLocalization ((M.map (algebraMap R R₀)).map (algebraMap R₀ S)) L
    convert (Localization.isLocalization (M := Algebra.algebraMapSubmonoid S M)) using 1
    ext s
    simp only [Submonoid.mem_map]
    constructor
    · rintro ⟨r₀, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap R R₀ r, ⟨r, hr, rfl⟩, rfl⟩
  let : Algebra A₀ L := localizationAlgebra M₀ S
  let : Algebra A L := localizationAlgebra M S
  have : IsScalarTower R A L := isScalarTower_localizationAlgebra M S
  have : IsScalarTower R₀ A₀ L := isScalarTower_localizationAlgebra M₀ S
  have : IsFractionRing A₀ L := isFractionRing_localization_of_artinian (Q := S) M₀
  let e := IsLocalization.algEquiv (nonZeroDivisors A₀) L (FractionRing A₀)
  have ht : (algebraMap A₀ L).comp (algebraMap A A₀) = algebraMap A L := by
    apply IsLocalization.ringHom_ext M
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R A L]
    change algebraMap A₀ L (algebraMap R₀ A₀ (Ideal.Quotient.mk _ r)) = _
    rw [← IsScalarTower.algebraMap_apply R₀ A₀ L]
    rfl
  exact AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun a => by
    change e (algebraMap A L a) = _
    rw [← DFunLike.congr_fun ht a, RingHom.comp_apply, e.commutes]
    rfl

/-- Taking the integral closure commutes with localization: if `C` is the localization at `M`
of a ring `T` identified with the integral closure of `R` in `S`, and `A` and `L` are the
localizations at `M` of `R` and of `S`, then `C` is the integral closure of `A` in `L`. -/
@[no_expose] public noncomputable def integralClosureLocalizationEquiv
    {R A S T C L : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [CommRing C] [CommRing L]
    [Algebra R A] [Algebra R S] [Algebra R T] [Algebra R C] [Algebra R L]
    [Algebra T C] [Algebra A C] [Algebra A L] [Algebra S L]
    [IsScalarTower R T C] [IsScalarTower R A C]
    [IsScalarTower R A L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M A]
    [IsLocalization (Algebra.algebraMapSubmonoid T M) C]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) L]
    (e : T ≃ₐ[R] integralClosure R S) : C ≃ₐ[A] integralClosure A L := by
  let φ : integralClosure R S →+* integralClosure A L :=
    { toFun := fun s => ⟨algebraMap S L s, (s.2.map (IsScalarTower.toAlgHom R S L)).tower_top⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  let : Algebra (integralClosure R S) (integralClosure A L) := φ.toAlgebra
  have : IsScalarTower (integralClosure R S) (integralClosure A L) L :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower R (integralClosure R S) (integralClosure A L) :=
    .of_algebraMap_eq' (by ext r; exact IsScalarTower.algebraMap_apply R S L r)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R S) M)
      (integralClosure A L) := IsLocalization.integralClosure M
  let e' : C ≃ₐ[R] integralClosure A L :=
    IsLocalization.algEquivOfAlgEquiv C (integralClosure A L) e
      (Algebra.algebraMapSubmonoid_map_eq M e.toAlgHom)
  apply AlgEquiv.ofRingEquiv (f := e'.toRingEquiv)
  have h : e'.toRingHom.comp (algebraMap A C) = algebraMap A (integralClosure A L) := by
    apply IsLocalization.ringHom_ext M
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R A C,
      ← IsScalarTower.algebraMap_apply R A (integralClosure A L)]
    exact congrArg Subtype.val (e'.commutes r)
  exact DFunLike.congr_fun h

/-- The stalk of the pushforward of the structure sheaf of the normalization is canonically
isomorphic, as an `𝒪_{X,x}`-algebra, to the integral closure of `𝒪_{X,x}` in the total ring of
fractions of its reduction. -/
@[stacks 0C3B "the total ring of fractions of the reduction"]
public noncomputable def
    normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    let A := X.presheaf.stalk x
    letI : Algebra A (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra A (FractionRing (A ⧸ _root_.nilradical A)) :=
      (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[A]
      integralClosure A (FractionRing (A ⧸ _root_.nilradical A)) := Classical.choice (by
  classical
  let := quasiCompactFromGenericPointResidueFields X hX
  let := quasiSeparatedFromGenericPointResidueFields X
  let f := fromGenericPointResidueFields X
  let ν := normalization X hX
  let C := normalizationPushforwardStalk X hX x
  let F := ν.base _* (normalizationScheme X hX).presheaf
  let A := X.presheaf.stalk x
  let : Algebra A C := normalizationPushforwardStalkAlgebra X hX x
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let R := Γ(X, U)
  let S := FractionRing (R ⧸ _root_.nilradical R)
  let T := Γ(normalizationScheme X hX, ν ⁻¹ᵁ U)
  let M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let L := Localization (Algebra.algebraMapSubmonoid S M)
  let : Algebra R A := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization M A := hU.isLocalization_stalk ⟨x, hx⟩
  let : Algebra R T := (ν.app U).hom.toAlgebra
  let : Algebra T C := (F.germ U x hx).hom.toAlgebra
  let : Algebra R C := ((F.germ U x hx).hom.comp (ν.app U).hom).toAlgebra
  have : IsScalarTower R T C := .of_algebraMap_eq' rfl
  have : IsScalarTower R A C := .of_algebraMap_eq' (by
    change ((F.germ U x hx).hom.comp (ν.app U).hom) =
      (((TopCat.Presheaf.stalkFunctor CommRingCat x).map ν.c).hom.comp
        (X.presheaf.germ U x hx).hom)
    exact congrArg CommRingCat.Hom.hom
      (TopCat.Presheaf.stalkFunctor_map_germ U x hx ν.c).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid T M) C :=
    pushforwardStalk_isLocalization ν U hU x hx
  let : Algebra R Γ(genericPointResidueSpectrum X, f ⁻¹ᵁ U) :=
    (f.app U).hom.toAlgebra
  have hmin : (minimalPrimes R).Finite :=
    finite_minimalPrimes_of_affine_open hX U hU.isoSpec.symm
  let : Finite (minimalPrimes R) := hmin
  let : Finite {η : genericPoints X // η.1 ∈ U} :=
    Finite.of_equiv (minimalPrimes R)
      (genericPointsInOpenEquivMinimalPrimes hU).symm
  let eS := genericPreimageSectionsAlgEquivReductionFractionRing X U hU hmin
  let eT : T ≃ₐ[R] integralClosure R S :=
    (AlgEquiv.ofRingEquiv
      (f := (f.normalizationObjIso hU).commRingCatIsoToRingEquiv) (fun r => by
        change (f.normalizationObjIso hU).hom (ν.app U r) = _
        have he := congrArg (fun g => g r) (f.fromNormalization_app hU)
        rw [he]
        exact (f.normalizationObjIso hU).inv_hom_id_apply _)).trans eS.mapIntegralClosure
  let : Algebra A L := localizationAlgebra M S
  have : IsScalarTower R A L := isScalarTower_localizationAlgebra M S
  let eC : C ≃ₐ[A] integralClosure A L := integralClosureLocalizationEquiv M eT
  let (p : minimalPrimes R) : p.1.IsPrime := p.2.1.1
  have : IsArtinianRing S :=
    (minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct R
      hmin).toRingEquiv.symm.isArtinianRing
  let eL := fractionRingReductionLocalizationEquiv R A M
  let eLRing : L ≃+* FractionRing (A ⧸ _root_.nilradical A) := eL.toRingEquiv
  have heL (a : A) :
      eLRing (algebraMap A L a) = Stacks.NormalizationStalkAmbient.reductionFractionRingHom A a :=
    eL.commutes a
  let : Algebra A (FractionRing (A ⧸ _root_.nilradical A)) :=
    (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A).toAlgebra
  let eL' : L ≃ₐ[A] FractionRing (A ⧸ _root_.nilradical A) :=
    AlgEquiv.ofRingEquiv (f := eLRing) heL
  exact ⟨eC.trans eL'.mapIntegralClosure⟩)

/-- The stalk of the pushforward of the structure sheaf of the normalization is canonically
isomorphic, as an `𝒪_{X,x}`-algebra, to the integral closure of `𝒪_{X,x}` in the product of the
residue fields of its minimal primes. -/
@[stacks 0C3B "the product of the minimal-prime residue fields"]
public noncomputable def
    normalizationPushforwardStalkEquivIntegralClosureMinimalPrimeResidueFields
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    let A := X.presheaf.stalk x
    letI (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
    letI : Algebra A (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    letI : Algebra A (minimalPrimes.residueFieldProduct A) :=
      (minimalPrimes.residueFieldProductHom A).toAlgebra
    normalizationPushforwardStalk X hX x ≃ₐ[A]
      integralClosure A (minimalPrimes.residueFieldProduct A) := Classical.choice (by
  let A := X.presheaf.stalk x
  let (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  let : Algebra A (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let e₀ := minimalPrimes.reductionFractionRingAlgEquivResidueFieldProduct A
    (finite_minimalPrimes_stalk X hX x)
  let e₀Ring : FractionRing (A ⧸ _root_.nilradical A) ≃+* minimalPrimes.residueFieldProduct A :=
    e₀.toRingEquiv
  have he₀ (a : A) : e₀Ring (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A a) =
      minimalPrimes.residueFieldProductHom A a := e₀.commutes a
  let : Algebra A (FractionRing (A ⧸ _root_.nilradical A)) :=
    (Stacks.NormalizationStalkAmbient.reductionFractionRingHom A).toAlgebra
  let : Algebra A (minimalPrimes.residueFieldProduct A) :=
    (minimalPrimes.residueFieldProductHom A).toAlgebra
  let e : FractionRing (A ⧸ _root_.nilradical A) ≃ₐ[A] minimalPrimes.residueFieldProduct A :=
    AlgEquiv.ofRingEquiv (f := e₀Ring) he₀
  exact
    ⟨(normalizationPushforwardStalkEquivIntegralClosureReductionFractionRing X hX x).trans
      e.mapIntegralClosure⟩)

end AlgebraicGeometry.Scheme
