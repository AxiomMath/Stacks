module

public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.MaximalSpectrum
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Nagata.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Branches and the residue quotient of the normalization

For a strictly henselian reduced Nagata local ring, the geometric branches are counted by the
maximal ideals of its normalization.  For any reduced Nagata local ring, the simultaneous residue
map on the normalization also induces a surjection after quotienting its source by the original
ring and its target by the diagonal copy of the residue field.

## Main definitions

* `Ring.normalizationResidueProductMap`: the simultaneous map to the residue fields at all
  maximal ideals of the normalization.
* `Ring.normalizationResidueQuotientMap`: its induced map modulo the images of the original
  ring.

## Main results

* `Ring.numberOfGeometricBranches_eq_encard_maximalSpectrum_integralClosure`: the geometric
  branches are counted by the maximal ideals of the normalization.
* `Ring.normalizationResidueQuotientMap_surjective`: the residue-quotient map is surjective.

## References

* [Stacks Project, Lemma 33.41.2](https://stacks.math.columbia.edu/tag/0C42)
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Ring

/-- The normalization of a reduced Nagata local ring has finitely many maximal ideals. -/
private theorem finite_maximalSpectrum_integralClosure
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) :
    Finite (MaximalSpectrum (integralClosure A (FractionRing A))) := by
  let B := integralClosure A (FractionRing A)
  let : Module.Finite A B := module_finite_integralClosure_fractionRing hA
  let := (Algebra.QuasiFinite.finite_primesOver (S := B) (IsLocalRing.maximalIdeal A)).fintype
  let f : MaximalSpectrum B → (IsLocalRing.maximalIdeal A).primesOver B := fun q =>
    ⟨q.asIdeal, q.isMaximal.isPrime,
      ⟨(IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q.asIdeal)).symm⟩⟩
  exact Finite.of_injective f fun x y h => MaximalSpectrum.ext (congrArg Subtype.val h)

/-- An algebraic extension of a separably closed field has separable degree one. -/
@[ega "IV 11.4.11"]
private theorem sepDegree_eq_one_of_isSepClosed
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsSepClosed k] :
    Field.sepDegree k K = 1 := by
  rw [Field.sepDegree,
    IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure k K),
    IntermediateField.rank_bot]

/-- The simultaneous residue map from the normalization to the product of its residue fields. -/
public noncomputable def normalizationResidueProductMap (A : Type u) [CommRing A] :
    ↥(integralClosure A (FractionRing A)) →ₗ[A]
      ((m : MaximalSpectrum ↥(integralClosure A (FractionRing A))) →
        ↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) where
  toFun := fun b m => Ideal.Quotient.mk m.asIdeal b
  map_add' := by intros; funext m; exact map_add (Ideal.Quotient.mk m.asIdeal) _ _
  map_smul' := by intros; ext m; simp [Algebra.smul_def]

/-- The simultaneous residue map, modulo the image of the original ring in its normalization
and modulo its diagonal image in the product of residue fields. -/
public noncomputable def normalizationResidueQuotientMap (A : Type u) [CommRing A] :
    (↥(integralClosure A (FractionRing A)) ⧸
        LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) →ₗ[A]
      (((m : MaximalSpectrum ↥(integralClosure A (FractionRing A))) →
          ↥(integralClosure A (FractionRing A)) ⧸ m.asIdeal) ⧸
        LinearMap.range ((normalizationResidueProductMap A).comp
          (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))))  :=
  Submodule.mapQ _ _ (normalizationResidueProductMap A) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩)

/-- For a strictly henselian reduced Nagata local ring, the number of geometric
branches is the number of maximal ideals of its normalization. -/
public theorem numberOfGeometricBranches_eq_encard_maximalSpectrum_integralClosure
    (A : Type u) (ksep : Type v) (Ash : Type u)
    [CommRing A] [IsReduced A] [StrictlyHenselianLocalRing A]
    [Field ksep] [Algebra (ResidueField A) ksep] [IsSepClosure (ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A ksep Ash]
    (hA : IsNagataRing A) :
    numberOfGeometricBranches A ksep Ash =
      Set.encard
        (Set.univ : Set (MaximalSpectrum ↑(integralClosure A (FractionRing A)))) := by
  let : IsNoetherianRing A := hA.1
  have hfinite : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  let : IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) A :=
    IsLocalRing.IsHenselization.of_ind_etale
      (R := A) (L := IsLocalRing.ResidueField A) inferInstance
      ((CommAlgCat.etale A).le_ind _ (show Algebra.Etale A A from inferInstance))
      ⟨RingEquiv.refl _, fun _ => rfl⟩
  have hchar := numberOfBranches_characterizations A A Ash ksep
  obtain ⟨hcontract, hgeom⟩ := (hchar.2.2.2 hfinite).2
  classical
  let Ared := A ⧸ nilradical A
  let A' := integralClosure A (FractionRing Ared)
  have hnil : nilradical A = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
  let eBase₁ : (A ⧸ nilradical A) ≃ₐ[A] A ⧸ (⊥ : Ideal A) :=
    Ideal.quotientEquivAlgOfEq A hnil
  have hker : RingHom.ker (AlgHom.id A A) = (⊥ : Ideal A) := by
    ext x
    simp
  let eBase₂ : (A ⧸ (⊥ : Ideal A)) ≃ₐ[A] A :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := AlgHom.id A A)
        (fun x => ⟨x, by simp⟩))
  let eBase := eBase₁.trans eBase₂
  let eFrac : FractionRing Ared ≃ₐ[A] FractionRing A :=
    IsFractionRing.algEquivOfAlgEquiv eBase
  let eClosure : A' ≃ₐ[A] integralClosure A (FractionRing A) :=
    eFrac.mapIntegralClosure
  let : Finite (MaximalSpectrum (integralClosure A (FractionRing A))) :=
    finite_maximalSpectrum_integralClosure A hA
  let : Finite (MaximalSpectrum A') :=
    Finite.of_equiv _ (_root_.MaximalSpectrum.congr eClosure.toRingEquiv).symm
  let : Fintype (MaximalSpectrum A') := Fintype.ofFinite _
  let (m' : MaximalSpectrum A') : Field (A' ⧸ m'.asIdeal) := Ideal.Quotient.field m'.asIdeal
  let (m' : MaximalSpectrum A') : Algebra (ResidueField A) (A' ⧸ m'.asIdeal) :=
    (Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq (hcontract m'))).toAlgebra
  have hsep (m' : MaximalSpectrum A') :
      Field.sepDegree (ResidueField A) (A' ⧸ m'.asIdeal) = 1 :=
    sepDegree_eq_one_of_isSepClosed (ResidueField A) (A' ⧸ m'.asIdeal)
  have hcard : ENat.card (Σ m' : MaximalSpectrum A',
      (Field.sepDegree (ResidueField A) (A' ⧸ m'.asIdeal)).ord.ToType) =
      Set.encard (Set.univ : Set (MaximalSpectrum A')) := by
    have equivFib (m' : MaximalSpectrum A') :
        (Field.sepDegree (ResidueField A) (A' ⧸ m'.asIdeal)).ord.ToType ≃ ULift.{u} Unit :=
      Classical.choice (Cardinal.eq.mp (by simp [hsep m']))
    calc
      _ = ENat.card (Σ _m' : MaximalSpectrum A', ULift.{u} Unit) :=
        ENat.card_congr (Equiv.sigmaCongrRight equivFib)
      _ = Set.encard (Set.univ : Set (MaximalSpectrum A')) := by
        let : ∀ _m' : MaximalSpectrum A', Unique (ULift.{u} Unit) := fun _ => inferInstance
        rw [ENat.card_congr (Equiv.sigmaUnique (MaximalSpectrum A')
          (fun _ => ULift.{u} Unit))]
        simp
  have hmaxcard : Set.encard (Set.univ : Set (MaximalSpectrum A')) =
      Set.encard (Set.univ : Set (MaximalSpectrum
        (integralClosure A (FractionRing A)))) := by
    rw [Set.encard_univ, Set.encard_univ]
    exact ENat.card_congr (_root_.MaximalSpectrum.congr eClosure.toRingEquiv)
  exact hgeom.trans (hcard.trans hmaxcard)

/-- The simultaneous residue map of the normalization induces a surjection after quotienting by
the original ring and its diagonal residue-field image. -/
public theorem normalizationResidueQuotientMap_surjective
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) :
    Function.Surjective (normalizationResidueQuotientMap A) := by
  classical
  let B := integralClosure A (FractionRing A)
  let f := normalizationResidueProductMap A
  let : Module.Finite A B := module_finite_integralClosure_fractionRing hA
  let : Finite (MaximalSpectrum B) := finite_maximalSpectrum_integralClosure A hA
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hcop : Pairwise (fun i j : MaximalSpectrum B => IsCoprime i.asIdeal j.asIdeal) := by
    intro i j hij
    let := i.isMaximal
    let := j.isMaximal
    exact Ideal.isCoprime_of_isMaximal fun heq => hij (MaximalSpectrum.ext heq)
  have hsurj : Function.Surjective f := fun x =>
    (Ideal.pi_quotient_surjective hcop x).imp fun _ hb => funext hb
  intro y
  refine Quotient.inductionOn' y fun x => ?_
  obtain ⟨b, hb⟩ := hsurj x
  refine ⟨(LinearMap.range (Algebra.linearMap A B)).mkQ b, ?_⟩
  show (LinearMap.range (f.comp (Algebra.linearMap A B))).mkQ (f b) = _
  rw [hb]
  rfl

end Ring
