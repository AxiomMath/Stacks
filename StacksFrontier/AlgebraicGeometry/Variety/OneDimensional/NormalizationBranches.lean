module

public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Stalk
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationFiber
public import StacksFrontier.RingTheory.Branches.Henselization

/-!
# Branches of a scheme and the fibres of its normalization

Let `X` be a scheme every quasi-compact open of which has finitely many irreducible components,
and let `ν : X^ν → X` be its normalization. The number of branches of `X` at a point `x` is the
number of points of `X^ν` above `x`, and the number of geometric branches is the sum over those
points of the separable degrees of the residue-field extensions `κ(x^ν)/κ(x)`.

## Main results

* `AlgebraicGeometry.numberOfBranches_eq_encard_normalizationFiber` counts branches by the fibre
  of the normalization.
* `AlgebraicGeometry.numberOfGeometricBranches_eq_card_sigma_sepDegree_normalization` counts
  geometric branches by the separable degrees over that fibre.

## Implementation notes

The fibre is expressed as a set of points of the normalization scheme, and its cardinality is
measured in `ℕ∞`, as is the number of branches. The weighted count of geometric branches is read
as the extended cardinality of a sigma type whose fibre over a point of the normalization is a
type of the cardinality of the separable degree.

## References

* [Stacks Project, Tag 0C1S](https://stacks.math.columbia.edu/tag/0C1S)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.NormalizationStalkAmbient Stacks.StalkMinimalPrimes.Basic
open IsLocalRing

universe u

/-- A ring equivalence between a residue-field extension and a quotient, compatible with the maps
from a local ring, transports along an algebra equivalence to an equality of separable degrees. -/
private theorem Field.sepDegree_residueField_eq_of_comp_residue {A S : Type*} {K T : Type u}
    [CommRing A] [IsLocalRing A] [Field K] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    (φ : IsLocalRing.ResidueField A →+* K) {m : Ideal S} (e : K ≃+* S ⧸ m) (σ : S ≃ₐ[A] T)
    (h : (e.toRingHom.comp φ).comp (IsLocalRing.residue A) =
      (Ideal.Quotient.mk m).comp (algebraMap A S))
    [hm : (m.map (σ.toRingEquiv : S →+* T)).IsMaximal]
    (hle : IsLocalRing.maximalIdeal A ≤
      (m.map (σ.toRingEquiv : S →+* T)).comap (algebraMap A T)) :
    letI := φ.toAlgebra
    letI : Field (T ⧸ m.map (σ.toRingEquiv : S →+* T)) := Ideal.Quotient.field _
    letI : Algebra (IsLocalRing.ResidueField A) (T ⧸ m.map (σ.toRingEquiv : S →+* T)) :=
      (Ideal.quotientMap _ (algebraMap A T) hle).toAlgebra
    Field.sepDegree (IsLocalRing.ResidueField A) K =
      Field.sepDegree (IsLocalRing.ResidueField A) (T ⧸ m.map (σ.toRingEquiv : S →+* T)) := by
  let := φ.toAlgebra
  let : Field (T ⧸ m.map (σ.toRingEquiv : S →+* T)) := Ideal.Quotient.field _
  let : Algebra (IsLocalRing.ResidueField A) (T ⧸ m.map (σ.toRingEquiv : S →+* T)) :=
    (Ideal.quotientMap _ (algebraMap A T) hle).toAlgebra
  refine Field.sepDegree_eq_of_equiv _ _ _
    { e.trans (Ideal.quotientEquiv m _ σ.toRingEquiv rfl) with
      commutes' := fun c => ?_ }
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  change Ideal.quotientEquiv m _ σ.toRingEquiv rfl (e (φ (IsLocalRing.residue A a))) =
    Ideal.quotientMap _ (algebraMap A T) hle (Ideal.Quotient.mk _ a)
  rw [show e (φ (IsLocalRing.residue A a)) = Ideal.Quotient.mk m (algebraMap A S a) from
    DFunLike.congr_fun h a, Ideal.quotientEquiv_mk, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (σ.commutes a)

namespace AlgebraicGeometry

/-- The number of branches at a point equals the number of points of the normalization above it. -/
@[stacks 0C1S "branches"]
public theorem numberOfBranches_eq_encard_normalizationFiber
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    AlgebraicGeometry.numberOfBranches X x =
      Set.encard {y : Scheme.normalizationScheme X hX |
        Scheme.normalization X hX y = x} := by
  let A := X.presheaf.stalk x
  let Ah := henselizationData A
  let Ash := strictHenselizationData A
  let ksep := SeparableClosure (ResidueField A)
  obtain ⟨hbranches, _⟩ := (numberOfBranches_characterizations A Ah.carrier Ash.carrier
    ksep).2.2.2 (finite_minimalPrimes_stalk X hX x)
  let S := normalizationPushforwardStalk X hX x
  let : Algebra A S := normalizationPushforwardStalkAlgebra X hX x
  let : Algebra A (FractionRing (A ⧸ nilradical A)) :=
    (reductionFractionRingHom A).toAlgebra
  let eNorm := normalizationStalkAlgEquivIntegralClosureFractionRing X hX x
  let B := integralClosure A (FractionRing (A ⧸ nilradical A))
  obtain ⟨fiberEquiv, _⟩ := normalizationFiberEquivMaximalSpectrum X hX x
  let eMax : MaximalSpectrum B ≃ {m : Ideal B // m.IsMaximal} :=
    ⟨fun m => ⟨m.asIdeal, m.isMaximal⟩, fun m => ⟨m.1, m.2⟩, fun _ => rfl, fun _ => rfl⟩
  calc
    AlgebraicGeometry.numberOfBranches X x = _root_.numberOfBranches A Ah.carrier := by
      rw [AlgebraicGeometry.numberOfBranches_eq_numberOfBranchesOfLocalRing]
      rfl
    _ = ENat.card {m : Ideal B // m.IsMaximal} := hbranches
    _ = ENat.card (MaximalSpectrum S) :=
      (ENat.card_congr ((_root_.MaximalSpectrum.congr eNorm.toRingEquiv).trans eMax)).symm
    _ = _ := (ENat.card_congr fiberEquiv).symm

/-- The number of geometric branches at a point is the sum, over the points of the normalization
above it, of the separable degrees of the corresponding residue-field extensions, interpreted
as the extended cardinality of the sigma type of these multiplicities. -/
@[stacks 0C1S "geometric_branches"]
public theorem numberOfGeometricBranches_eq_card_sigma_sepDegree_normalization
    (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    AlgebraicGeometry.numberOfGeometricBranches X x =
      ENat.card (Σ y : {y : Scheme.normalizationScheme X hX //
          Scheme.normalization X hX y = x},
        letI := (((X.residueFieldCongr y.property).inv ≫
          (Scheme.normalization X hX).residueFieldMap y).hom).toAlgebra
        (Field.sepDegree (X.residueField x)
          ((Scheme.normalizationScheme X hX).residueField y)).ord.ToType) := by
  classical
  let A := (X.presheaf.stalk x : Type _)
  obtain ⟨_, hcontract, hgeom⟩ := (numberOfBranches_characterizations A
    (henselizationData A).carrier (strictHenselizationData A).carrier
    (SeparableClosure (IsLocalRing.ResidueField A))).2.2.2 (finite_minimalPrimes_stalk X hX x)
  let : Algebra A (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  let : Algebra A (FractionRing (A ⧸ nilradical A)) :=
    (reductionFractionRingHom A).toAlgebra
  let C := integralClosure A (FractionRing (A ⧸ nilradical A))
  let eNorm := normalizationStalkAlgEquivIntegralClosureFractionRing X hX x
  obtain ⟨fiberEquiv, fiberResidue⟩ := normalizationFiberEquivMaximalSpectrum X hX x
  choose eRes _ hRes using fiberResidue
  let eIndex := fiberEquiv.trans (_root_.MaximalSpectrum.congr eNorm.toRingEquiv)
  let β : MaximalSpectrum C → Type _ := fun m =>
    let : m.asIdeal.IsMaximal := m.isMaximal
    let : Field (C ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let f := Ideal.quotientMap m.asIdeal (algebraMap A C)
      (le_of_eq (hcontract m))
    let : Algebra (IsLocalRing.ResidueField A) (C ⧸ m.asIdeal) := f.toAlgebra
    (Field.sepDegree (IsLocalRing.ResidueField A) (C ⧸ m.asIdeal)).ord.ToType
  change numberOfGeometricBranchesOfLocalRing A = _
  rw [numberOfGeometricBranchesOfLocalRing_eq_encard_minimalPrimes]
  exact hgeom.trans (ENat.card_congr <| (Equiv.sigmaCongrRight fun y =>
    Equiv.cast (congrArg (fun d : Cardinal => d.ord.ToType)
      (Field.sepDegree_residueField_eq_of_comp_residue _ (eRes y) eNorm (hRes y)
        (hm := (eIndex y).isMaximal) (le_of_eq (hcontract (eIndex y)))))).trans
    (Equiv.sigmaCongrLeft (β := β) eIndex)).symm

end AlgebraicGeometry

end
