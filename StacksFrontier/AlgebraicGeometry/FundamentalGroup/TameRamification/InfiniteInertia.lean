module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import StacksCore.FieldTheory.KrullTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia

/-!
# Structure of the decomposition group in an infinite Galois extension

For a discrete valuation ring and a possibly infinite Galois extension of its fraction field,
the decomposition group acts on the residue field with inertia as kernel.  The inertia group
has a canonical wild subgroup and a tame quotient described by compatible roots of unity.

## Main results

* `Ideal.Quotient.ker_stabilizerHom` and `Ideal.Quotient.stabilizerHom_surjective_of_profinite`
  give the first exact sequence.
* `Stacks.FundamentalGroup.exists_tameInertiaCharacter` gives the wild-tame exact sequence, its
  pro-primary wild kernel, and the canonical equivariant character into compatible roots of
  unity, characterized at every finite Galois subextension.

## Implementation notes

The inverse limit of the groups of roots of unity is expressed as compatible families in their
product, and surjectivity is stated directly for every compatible family.  The character at
every finite Galois subextension is the image of its canonical finite inertia character, and
its kernel consists precisely of the elements restricting to finite wild inertia at every
level.  The tame group is the quotient by this kernel; its identification with the inverse
limit follows from the first isomorphism theorem.

The decomposition exact sequence is registered directly from the general results on stabilizers
acting on quotient rings, rather than restated for this discrete valuation setting.

## References

* [Stacks Project, Tag 0BUA](https://stacks.math.columbia.edu/tag/0BUA)
-/

@[expose] public noncomputable section

open scoped Pointwise

universe u v w

namespace Stacks.FundamentalGroup

add_to_stacks 0BUA "the kernel of the decomposition-group residue action"
  Ideal.Quotient.ker_stabilizerHom

add_to_stacks 0BUA "surjectivity of the decomposition-group residue action"
  Ideal.Quotient.stabilizerHom_surjective_of_profinite
add_to_sga "1 V 1.1" "closed points" Ideal.Quotient.stabilizerHom_surjective_of_profinite
add_to_sga "1 V 1.3" "special case" Ideal.Quotient.stabilizerHom_surjective_of_profinite

/-- The contraction of a maximal ideal of the integral closure in a larger field is maximal in the
integral closure in the smaller one. -/
private lemma isMaximal_comap_mapIntegralClosure
    {A K L : Type*} [CommRing A] [CommRing K] [CommRing L]
    [Algebra A K] [Algebra A L] (f : K →ₐ[A] L)
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    (P.comap f.mapIntegralClosure.toRingHom).IsMaximal := by
  let : Algebra (integralClosure A K) (integralClosure A L) :=
    f.mapIntegralClosure.toRingHom.toAlgebra
  let : IsScalarTower A (integralClosure A K) (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.mapIntegralClosure.commutes x).symm
  let : Algebra.IsIntegral (integralClosure A K) (integralClosure A L) :=
    Algebra.IsIntegral.tower_top A
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P

/-- The inertia group at a maximal ideal is closed in the Krull topology. -/
private lemma inertia_isClosed
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    IsClosed (P.inertia Gal(L/K) : Set Gal(L/K)) := by
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  have hσ' : σ ∉ P.inertia Gal(L/K) := hσ
  rw [Ideal.mem_inertia] at hσ'
  push Not at hσ'
  obtain ⟨b, hb⟩ := hσ'
  refine ⟨{τ : Gal(L/K) | τ (b : L) = σ (b : L)}, ?_, ?_, ?_⟩
  · intro τ hτ hτI
    have hsmul : τ • b = σ • b := by
      apply Subtype.ext
      show ((galRestrict A K L (integralClosure A L) τ) b : L) =
        ((galRestrict A K L (integralClosure A L) σ) b : L)
      exact (algebraMap_galRestrict_apply (A := A) (K := K) (L := L)
        (B := integralClosure A L) τ b).trans
        (hτ.trans (algebraMap_galRestrict_apply (A := A) (K := K) (L := L)
          (B := integralClosure A L) σ b).symm)
    exact hb (by simpa only [hsmul] using (Ideal.mem_inertia.mp hτI) b)
  · exact isOpen_krullTopology_apply_eq' K (b : L) (σ (b : L))
  · rfl

/-- The inertia group at a maximal ideal is compact. -/
private lemma inertia_compactSpace
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    CompactSpace (P.inertia Gal(L/K)) := by
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  exact isCompact_iff_compactSpace.mp ((inertia_isClosed A K L P).isCompact)

/-- The decomposition group normalizes the inertia group: a conjugate of an inertia element by a
stabilizer element is again in inertia. -/
private lemma inertia_conjugate
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∀ (τ : MulAction.stabilizer Gal(L/K) P) (σ : P.inertia Gal(L/K)),
      ∃ ρ : P.inertia Gal(L/K),
        (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
          (τ : Gal(L/K))⁻¹ := by
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro τ σ
  refine ⟨⟨(τ : Gal(L/K)) * (σ : Gal(L/K)) * (τ : Gal(L/K))⁻¹, ?_⟩, rfl⟩
  rw [Ideal.mem_inertia]
  intro x
  have hσ := (Ideal.mem_inertia.mp σ.property) ((τ : Gal(L/K))⁻¹ • x)
  have hτ := Ideal.smul_mem_pointwise_smul (τ : Gal(L/K)) _ P hσ
  rw [τ.property] at hτ
  simpa only [mul_smul, smul_sub, smul_inv_smul] using hτ

/-- At a finite Galois subextension the tame ramification index is positive, is prime to the
residue characteristic when that is positive, and is the order of a primitive root of unity in the
residue field. -/
private lemma finite_tame_properties
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let n := IsDiscreteValuationRing.tameRamificationIndex A L P
    let p := ringChar (IsLocalRing.ResidueField A)
    0 < n ∧ (p ≠ 0 → n.Coprime p) ∧
      ∃ z : integralClosure A L ⧸ P, IsPrimitiveRoot z n := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let n := IsDiscreteValuationRing.tameRamificationIndex A L P
  obtain ⟨_, _, _, _, hcard, θcan, _⟩ :=
    IsDiscreteValuationRing.canonicalInertiaCharacter_spec.{_, _, _, 0} A K L P
  have hn : 0 < n := by
    show 0 < IsDiscreteValuationRing.tameRamificationIndex A L P
    rw [← hcard]
    exact Nat.card_pos
  refine ⟨hn, ?_, ?_⟩
  · intro hp
    have he : P.ramificationIdx A ≠ 0 := fun he ↦
      hn.ne' (by simp [n, IsDiscreteValuationRing.tameRamificationIndex, he])
    exact (Nat.coprime_ordCompl
      ((CharP.char_is_prime_or_zero (IsLocalRing.ResidueField A) _).resolve_right hp) he).symm
  · let : NeZero n := ⟨hn.ne'⟩
    exact card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
      ((Nat.card_congr θcan.toEquiv).symm.trans hcard)

/-- The tame ramification index at a finite Galois subextension divides the one at any larger
finite Galois subextension. -/
private lemma finite_tame_dvd_of_le
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F G : FiniteGaloisIntermediateField K L) (h : F ≤ G) :
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : IsScalarTower A G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let qF := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
    let qG := P.comap (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom
    IsDiscreteValuationRing.tameRamificationIndex A F qF ∣
      IsDiscreteValuationRing.tameRamificationIndex A G qG := by
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra F G := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let qG := P.comap (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom
  let : qG.IsMaximal :=
    isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A G L) P
  obtain ⟨_, _, _, _, _, _, _, _, _, hdiv, _⟩ :=
    IsDiscreteValuationRing.surjective_restrictions_commute_with_residue_and_inertiaCharacter
      A K F G qG
  exact Nat.ordCompl_dvd_ordCompl_of_dvd hdiv _

/-- Restriction of automorphisms maps the decomposition group, and the inertia group, at `P` onto
those at the contracted ideal of a finite Galois subextension. -/
private lemma image_restrictNormalHom_stabilizer_and_inertia
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let q := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
    (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)) ''
        (MulAction.stabilizer Gal(L/K) P : Set Gal(L/K)) =
      (MulAction.stabilizer Gal(F/K) q : Set Gal(F/K)) ∧
    (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)) '' (P.inertia Gal(L/K) : Set Gal(L/K)) =
      (q.inertia Gal(F/K) : Set Gal(F/K)) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let C := integralClosure A F
  let B := integralClosure A L
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction Gal(F/K) C :=
    IsIntegralClosure.MulSemiringAction A K F C
  let f : C →ₐ[A] B := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let : Algebra C B := f.toRingHom.toAlgebra
  let : IsScalarTower A C B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let : IsScalarTower C B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower C F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsFractionRing C F :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K F C
  let : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_algebraic A B fun _ hx ↦
      IsFractionRing.to_map_eq_zero_iff.mp
        ((map_eq_zero (algebraMap K L)).mp <|
          (IsScalarTower.algebraMap_apply A K L _).symm.trans hx)
  let q := P.comap f.toRingHom
  simpa only [q, Ideal.under, f, RingHom.algebraMap_toAlgebra] using
    IsIntegralClosure.image_stabilizer_and_inertia_restrictNormalHom A K F L C B P


/-- Restriction of automorphisms maps the inertia group at `P` onto the inertia group at the
contracted ideal of a finite Galois subextension. -/
private lemma inertia_restriction_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let q := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
    ∃ resI : P.inertia Gal(L/K) →* q.inertia Gal(F/K),
      Function.Surjective resI ∧
      ∀ σ, ((resI σ : q.inertia Gal(F/K)) : Gal(F/K)) =
        AlgEquiv.restrictNormal (σ : Gal(L/K)) (F : IntermediateField K L) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let q := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
  let res : Gal(L/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hImage := (image_restrictNormalHom_stabilizer_and_inertia A K L P F).2
  let resI : P.inertia Gal(L/K) →* q.inertia Gal(F/K) :=
    (res.comp (P.inertia Gal(L/K)).subtype).codRestrict _ (by
      intro σ
      show res (σ : Gal(L/K)) ∈ (q.inertia Gal(F/K) : Set Gal(F/K))
      rw [← hImage]
      exact ⟨σ, σ.property, rfl⟩)
  refine ⟨resI, ?_, ?_⟩
  · intro σ
    have hσ : (σ : Gal(F/K)) ∈ (q.inertia Gal(F/K) : Set Gal(F/K)) := σ.property
    rw [← hImage] at hσ
    obtain ⟨τ, hτ, hres⟩ := hσ
    exact ⟨⟨τ, hτ⟩, Subtype.ext hres⟩
  · intro σ
    rfl

/-- Restriction of automorphisms maps the decomposition group at `P` into the decomposition group
at the contracted ideal of a finite Galois subextension. -/
private lemma stabilizer_restriction
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let q := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
    ∀ τ : MulAction.stabilizer Gal(L/K) P,
      ∃ τF : MulAction.stabilizer Gal(F/K) q,
        (τF : Gal(F/K)) =
          AlgEquiv.restrictNormal (τ : Gal(L/K)) (F : IntermediateField K L) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let q := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
  let res : Gal(L/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hImage := (image_restrictNormalHom_stabilizer_and_inertia A K L P F).1
  dsimp only
  intro τ
  have hτ : res (τ : Gal(L/K)) ∈ MulAction.stabilizer Gal(F/K) q := by
    show res (τ : Gal(L/K)) ∈
      (MulAction.stabilizer Gal(F/K) q : Set Gal(F/K))
    rw [← hImage]
    exact ⟨τ, τ.property, rfl⟩
  exact ⟨⟨res τ, hτ⟩, rfl⟩

/-- The action of an automorphism on the integral closure of a finite Galois subextension agrees
with its restriction acting there. -/
private lemma mapIntegralClosure_restrict_smul
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (g : Gal(L/K)) (x : integralClosure A F),
      (IsScalarTower.toAlgHom A F L).mapIntegralClosure
          ((AlgEquiv.restrictNormal g (F : IntermediateField K L)) • x) =
        g • (IsScalarTower.toAlgHom A F L).mapIntegralClosure x := by
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  intro g x
  apply Subtype.ext
  show algebraMap F L (algebraMap (integralClosure A F) F
      (galRestrict A K F (integralClosure A F)
        (AlgEquiv.restrictNormal g (F : IntermediateField K L)) x)) =
    algebraMap (integralClosure A L) L
      (galRestrict A K L (integralClosure A L) g
        ((IsScalarTower.toAlgHom A F L).mapIntegralClosure x))
  rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
  exact AlgEquiv.restrictNormal_commutes g (F : IntermediateField K L) _

/-- The residue-field map induced by a finite Galois subextension is equivariant for the residue
action of the decomposition group. -/
private lemma quotientMap_quotientEquiv
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L))
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let q := P.comap f.toRingHom
    ∀ (τ : MulAction.stabilizer Gal(L/K) P)
      (τF : MulAction.stabilizer Gal(F/K) q),
      (τF : Gal(F/K)) =
        AlgEquiv.restrictNormal (τ : Gal(L/K)) (F : IntermediateField K L) →
      ∀ z : integralClosure A F ⧸ q,
        (Ideal.quotientEquiv P P
          ((MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L))
            (τ : Gal(L/K))) τ.property.symm)
            ((Ideal.quotientMap P f.toRingHom le_rfl) z) =
          (Ideal.quotientMap P f.toRingHom le_rfl)
            ((Ideal.quotientEquiv q q
              ((MulSemiringAction.toRingEquiv Gal(F/K) (integralClosure A F))
                (τF : Gal(F/K))) τF.property.symm) z) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  dsimp only
  intro τ τF hτF z
  induction z using Quotient.inductionOn with
  | _ x =>
      show Ideal.Quotient.mk P ((τ : Gal(L/K)) • f x) =
        Ideal.Quotient.mk P (f ((τF : Gal(F/K)) • x))
      apply congrArg (Ideal.Quotient.mk P)
      symm
      rw [hτF]
      exact mapIntegralClosure_restrict_smul A K L F (τ : Gal(L/K)) x

/-- The canonical tame inertia character at a finite Galois subextension, transported to the
residue field at `P`. -/
@[sga "7 XV 2.2.5"]
private noncomputable def finite_tame_character
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    P.inertia Gal(L/K) →* (integralClosure A L ⧸ P)ˣ := by
  classical
  letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  letI : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  letI : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  letI : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  exact (Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom).comp
    (((rootsOfUnity (IsDiscreteValuationRing.tameRamificationIndex A F q)
      (integralClosure A F ⧸ q)).subtype).comp
      ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q).comp
        (inertia_restriction_surjective A K L P F).choose))

/-- The value of the transported tame character is the image of the finite-level inertia character.
-/
private lemma finite_tame_character_apply
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ σ : P.inertia Gal(L/K),
    let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let q := P.comap f.toRingHom
    letI : q.IsMaximal := isMaximal_comap_mapIntegralClosure
      (IsScalarTower.toAlgHom A F L) P
    ((finite_tame_character A K L P F σ : (integralClosure A L ⧸ P)ˣ) :
      integralClosure A L ⧸ P) =
      (Ideal.quotientMap P f.toRingHom le_rfl)
        ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q
          ((inertia_restriction_surjective A K L P F).choose σ)).1.1) := by
  intro σ
  rfl

/-- The transported tame character has order dividing the tame ramification index. -/
private lemma finite_tame_character_pow
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ σ : P.inertia Gal(L/K),
      (finite_tame_character A K L P F σ) ^
        IsDiscreteValuationRing.tameRamificationIndex A F
          (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) = 1 := by
  intro σ
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let ζ := IsDiscreteValuationRing.canonicalInertiaCharacter A K F q
    ((inertia_restriction_surjective A K L P F).choose σ)
  show (Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom
    (ζ : (integralClosure A F ⧸ q)ˣ)) ^
      IsDiscreteValuationRing.tameRamificationIndex A F q = 1
  rw [← map_pow]
  have hζ : (ζ : (integralClosure A F ⧸ q)ˣ) ^
      IsDiscreteValuationRing.tameRamificationIndex A F q = 1 := ζ.property
  rw [hζ, map_one]

/-- The transported tame characters at two nested finite Galois subextensions are related by the
quotient of their tame ramification indices. -/
private lemma finite_tame_character_le
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F G : FiniteGaloisIntermediateField K L) (h : F ≤ G) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : IsScalarTower A G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ σ : P.inertia Gal(L/K),
      finite_tame_character A K L P F σ =
        finite_tame_character A K L P G σ ^
          (IsDiscreteValuationRing.tameRamificationIndex A G
            (P.comap (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom) /
           IsDiscreteValuationRing.tameRamificationIndex A F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom)) := by
  classical
  intro σ
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra F G := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K F G := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower F G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let fFG := (IsScalarTower.toAlgHom A F G).mapIntegralClosure
  let algFG : Algebra (integralClosure A F) (integralClosure A G) :=
    fFG.toRingHom.toAlgebra
  let : SMul (integralClosure A F) (integralClosure A G) := algFG.toSMul
  let : IsScalarTower A (integralClosure A F) (integralClosure A G) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (fFG.commutes x).symm
  let qF := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
  let : qF.IsMaximal :=
    isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
  let qG := P.comap (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom
  let : qG.IsMaximal :=
    isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A G L) P
  obtain ⟨_, _, _, _, _, _, _, _, hTower⟩ :=
    IsDiscreteValuationRing.canonicalInertiaCharacter_spec A K F qF
  obtain ⟨resI, rootRestriction, hresI, hdiv, hroot, hchar⟩ := hTower G qG
  have hq : qG.under (integralClosure A F) = qF := by
    rfl
  let : qG.LiesOver qF := ⟨hq⟩
  let : Algebra (integralClosure A F ⧸ qF) (integralClosure A G ⧸ qG) :=
    Ideal.Quotient.algebraOfLiesOver qG qF
  let fFL := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let fGL := (IsScalarTower.toAlgHom A G L).mapIntegralClosure
  have hcomp : (Ideal.quotientMap P fFL.toRingHom le_rfl) =
      (Ideal.quotientMap P fGL.toRingHom le_rfl).comp
        (algebraMap (integralClosure A F ⧸ qF) (integralClosure A G ⧸ qG)) := by
    ext x
    rfl
  let σG := (inertia_restriction_surjective A K L P G).choose σ
  let σF := (inertia_restriction_surjective A K L P F).choose σ
  have hσ : resI σG = σF := by
    apply Subtype.ext
    have hσG := (inertia_restriction_surjective A K L P G).choose_spec.2 σ
    have hσF := (inertia_restriction_surjective A K L P F).choose_spec.2 σ
    show (resI σG : Gal(F/K)) = (σF : Gal(F/K))
    rw [hresI σG, hσG, hσF]
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F G
      (σ : Gal(L/K))).symm
  have hlevel :
      (algebraMap (integralClosure A F ⧸ qF) (integralClosure A G ⧸ qG))
        ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F qF σF).1.1) =
      ((IsDiscreteValuationRing.canonicalInertiaCharacter A K G qG σG).1.1) ^
        (IsDiscreteValuationRing.tameRamificationIndex A G qG /
          IsDiscreteValuationRing.tameRamificationIndex A F qF) := by
    have he := hroot (IsDiscreteValuationRing.canonicalInertiaCharacter A K G qG σG)
    rw [hchar σG, hσ] at he
    convert he using 1 <;> rfl
  apply Units.ext
  show ((finite_tame_character A K L P F σ : (integralClosure A L ⧸ P)ˣ) :
      integralClosure A L ⧸ P) =
    ((finite_tame_character A K L P G σ : (integralClosure A L ⧸ P)ˣ) :
      integralClosure A L ⧸ P) ^
      (IsDiscreteValuationRing.tameRamificationIndex A G qG /
        IsDiscreteValuationRing.tameRamificationIndex A F qF)
  rw [finite_tame_character_apply A K L P F σ]
  simp only [finite_tame_character_apply A K L P G σ]
  calc
    (Ideal.quotientMap P fFL.toRingHom le_rfl)
        ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F qF σF).1.1) =
      (Ideal.quotientMap P fGL.toRingHom le_rfl)
        ((algebraMap (integralClosure A F ⧸ qF) (integralClosure A G ⧸ qG))
          ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F qF σF).1.1)) := by
            rw [hcomp]
            rfl
    _ = (Ideal.quotientMap P fGL.toRingHom le_rfl)
        (((IsDiscreteValuationRing.canonicalInertiaCharacter A K G qG σG).1.1) ^
          (IsDiscreteValuationRing.tameRamificationIndex A G qG /
            IsDiscreteValuationRing.tameRamificationIndex A F qF)) :=
              congrArg _ hlevel
    _ = _ :=
      map_pow (Ideal.quotientMap P fGL.toRingHom le_rfl)
        ((IsDiscreteValuationRing.canonicalInertiaCharacter A K G qG σG).1.1)
        (IsDiscreteValuationRing.tameRamificationIndex A G qG /
          IsDiscreteValuationRing.tameRamificationIndex A F qF)

/-- For a chain of divisibilities the quotients multiply. -/
private lemma div_chain {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) :
    c / a = (c / b) * (b / a) := by
  calc
    c / a = (c / b * b) / a := by rw [Nat.div_mul_cancel hbc]
    _ = (c / b) * (b / a) := Nat.mul_div_assoc _ hab

/-- Every root of unity of order the tame ramification index at a finite Galois subextension is a
value of the transported tame character. -/
private lemma finite_tame_character_surjective
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ ζ : (integralClosure A L ⧸ P)ˣ,
      ζ ^ IsDiscreteValuationRing.tameRamificationIndex A F
        (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) = 1 →
      ∃ σ : P.inertia Gal(L/K), finite_tame_character A K L P F σ = ζ := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let n := IsDiscreteValuationRing.tameRamificationIndex A F q
  let φ := Ideal.quotientMap P f.toRingHom le_rfl
  obtain ⟨hn, _, z, hz⟩ := finite_tame_properties A K F q
  let : NeZero n := ⟨hn.ne'⟩
  have hzφ : IsPrimitiveRoot (φ z) n :=
    hz.map_of_injective (f := φ) Ideal.quotientMap_injective
  obtain ⟨_, _, _, _, _, θcan, hθ, _⟩ :=
    IsDiscreteValuationRing.canonicalInertiaCharacter_spec.{_, _, _, 0} A K F q
  let ξ : rootsOfUnity n (integralClosure A F ⧸ q) := hz.toRootsOfUnity
  intro ζ hζ
  have hζval : (ζ : integralClosure A L ⧸ P) ^ n = 1 := by
    have h := congrArg (fun x : (integralClosure A L ⧸ P)ˣ =>
      (x : integralClosure A L ⧸ P)) hζ
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  obtain ⟨i, _, hzi⟩ := hzφ.eq_pow_of_pow_eq_one hζval
  obtain ⟨t, ht⟩ := θcan.surjective (ξ ^ i)
  obtain ⟨σF, hσF⟩ :=
    (QuotientGroup.mk'_surjective
      (IsDiscreteValuationRing.wildInertiaGroup A K F q)) t
  obtain ⟨σ, hσ⟩ :=
    (inertia_restriction_surjective A K L P F).choose_spec.1 σF
  have hcan : IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF = ξ ^ i := by
    rw [← hθ σF]
    show θcan ((QuotientGroup.mk'
      (IsDiscreteValuationRing.wildInertiaGroup A K F q)) σF) = ξ ^ i
    rw [hσF, ht]
  refine ⟨σ, ?_⟩
  apply Units.ext
  rw [finite_tame_character_apply A K L P F σ]
  show φ ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q
    ((inertia_restriction_surjective A K L P F).choose σ)).1.1) = ζ.val
  rw [hσ, hcan]
  show φ (z ^ i) = ζ.val
  rw [map_pow]
  exact hzi

/-- The transported tame character is trivial on an inertia element exactly when its restriction
lies in the finite wild inertia group. -/
private lemma finite_tame_character_eq_one_iff
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
      isMaximal_comap_mapIntegralClosure
      (IsScalarTower.toAlgHom A F L) P
    ∀ σ : P.inertia Gal(L/K),
      finite_tame_character A K L P F σ = 1 ↔
        (inertia_restriction_surjective A K L P F).choose σ ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  obtain ⟨_, _, _, _, _, e, he, _⟩ :=
    IsDiscreteValuationRing.canonicalInertiaCharacter_spec.{_, _, _, 0} A K F q
  intro σ
  let σF := (inertia_restriction_surjective A K L P F).choose σ
  have hmap : Function.Injective
      (Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom) :=
    Units.map_injective Ideal.quotientMap_injective
  show (Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom
    (((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q) σF :
      rootsOfUnity (IsDiscreteValuationRing.tameRamificationIndex A F q)
        (integralClosure A F ⧸ q)) : (integralClosure A F ⧸ q)ˣ)) = 1 ↔ _
  rw [← map_one (Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom)]
  constructor
  · intro h
    have h := hmap h
    have hc : IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF = 1 :=
      Subtype.ext h
    have hq : IsDiscreteValuationRing.tameInertiaMap A K F q σF = 1 :=
      e.injective (by rw [he σF, hc, map_one])
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro hw
    have hq : IsDiscreteValuationRing.tameInertiaMap A K F q σF = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hw
    have hc : IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF = 1 := by
      rw [← he σF, hq, map_one]
    exact congrArg _ (congrArg Subtype.val hc)

/-- Each fibre of the transported tame character is closed in the Krull topology. -/
private lemma finite_tame_character_fiber_isClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L)
    (ζ : (integralClosure A L ⧸ P)ˣ) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    IsClosed {σ : P.inertia Gal(L/K) | finite_tame_character A K L P F σ = ζ} := by
  classical
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  let r := (inertia_restriction_surjective A K L P F).choose
  have hr : Continuous (fun σ : P.inertia Gal(L/K) => (r σ : Gal(F/K))) := by
    have hbase := (InfiniteGalois.restrictNormalHom_continuous
      (F : IntermediateField K L)).comp
        (continuous_subtype_val : Continuous
          (fun σ : P.inertia Gal(L/K) => (σ : Gal(L/K))))
    convert hbase using 1
    funext σ
    exact (inertia_restriction_surjective A K L P F).choose_spec.2 σ
  have hr' : Continuous r := hr.subtype_mk (fun σ => (r σ).property)
  let k : q.inertia Gal(F/K) → (integralClosure A L ⧸ P)ˣ := fun σ =>
    Units.map (Ideal.quotientMap P f.toRingHom le_rfl).toMonoidHom
      ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σ :
        rootsOfUnity (IsDiscreteValuationRing.tameRamificationIndex A F q)
          (integralClosure A F ⧸ q)) : (integralClosure A F ⧸ q)ˣ)
  have hset : {σ : P.inertia Gal(L/K) | finite_tame_character A K L P F σ = ζ} =
      r ⁻¹' {σ | k σ = ζ} := by
    ext σ
    rfl
  rw [hset]
  exact (isClosed_discrete _).preimage hr'

/-- The transported tame character is equivariant for conjugation by the decomposition group and
the induced residue-field automorphism. -/
private lemma finite_tame_character_conj
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∀ (τ : MulAction.stabilizer Gal(L/K) P)
      (σ ρ : P.inertia Gal(L/K)),
      (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
        (τ : Gal(L/K))⁻¹ →
      finite_tame_character A K L P F ρ =
        (Ideal.quotientEquiv P P
          ((MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L))
            (τ : Gal(L/K))) τ.property.symm).toMulEquiv
          (finite_tame_character A K L P F σ) := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap f.toRingHom
  let : q.IsMaximal := isMaximal_comap_mapIntegralClosure
    (IsScalarTower.toAlgHom A F L) P
  intro τ σ ρ hρ
  obtain ⟨τF, hτF⟩ := stabilizer_restriction A K L P F τ
  let res : Gal(L/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  let σF := (inertia_restriction_surjective A K L P F).choose σ
  let ρF := (inertia_restriction_surjective A K L P F).choose ρ
  have hσF : res (σ : Gal(L/K)) = (σF : Gal(F/K)) :=
    ((inertia_restriction_surjective A K L P F).choose_spec.2 σ).symm
  have hρF : (ρF : Gal(F/K)) =
      (τF : Gal(F/K)) * (σF : Gal(F/K)) * (τF : Gal(F/K))⁻¹ := by
    calc
      (ρF : Gal(F/K)) = res (ρ : Gal(L/K)) :=
        (inertia_restriction_surjective A K L P F).choose_spec.2 ρ
      _ = res (τ : Gal(L/K)) * res (σ : Gal(L/K)) *
          (res (τ : Gal(L/K)))⁻¹ := by rw [hρ, map_mul, map_mul, map_inv]
      _ = (τF : Gal(F/K)) * (σF : Gal(F/K)) *
          (τF : Gal(F/K))⁻¹ := by
            rw [show res (τ : Gal(L/K)) = (τF : Gal(F/K)) from hτF.symm, hσF]
  obtain ⟨_, _, _, _, _, _, _, hconj, _⟩ :=
    IsDiscreteValuationRing.canonicalInertiaCharacter_spec.{_, _, _, 0} A K F q
  have hcan : IsDiscreteValuationRing.canonicalInertiaCharacter A K F q ρF =
      (Ideal.quotientEquiv q q
        ((MulSemiringAction.toRingEquiv Gal(F/K) (integralClosure A F))
          (τF : Gal(F/K))) τF.property.symm).toMulEquiv.restrictRootsOfUnity
          (IsDiscreteValuationRing.tameRamificationIndex A F q)
        (IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF) := by
    rw [← hconj τF σF]
    congr 1
    exact Subtype.ext hρF
  let φ := Ideal.quotientMap P f.toRingHom le_rfl
  let QL := Ideal.quotientEquiv P P
    ((MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L))
      (τ : Gal(L/K))) τ.property.symm
  let QF := Ideal.quotientEquiv q q
    ((MulSemiringAction.toRingEquiv Gal(F/K) (integralClosure A F))
      (τF : Gal(F/K))) τF.property.symm
  show φ ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q ρF).1.1) =
    QL (φ ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1))
  rw [hcan]
  show φ (QF ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1)) =
    QL (φ ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1))
  exact (quotientMap_quotientEquiv A K L P F τ τF hτF _).symm

/-- The wild inertia group at a finite Galois subextension is a normal subgroup of the
decomposition group, trivial in residue characteristic zero and a `p`-group in positive residue
characteristic `p`. -/
private lemma finite_wild_spec
    (A K F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    [Algebra A F] [IsScalarTower A K F]
    (q : Ideal (integralClosure A F)) [q.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    let p := ringChar (IsLocalRing.ResidueField A)
    ((IsDiscreteValuationRing.wildInertiaGroup A K F q).map
      ((q.inertia Gal(F/K)).subtype.codRestrict (MulAction.stabilizer Gal(F/K) q)
        fun σ ↦ Ideal.inertia_le_stabilizer (M := Gal(F/K)) q σ.property)).Normal ∧
    (p = 0 → IsDiscreteValuationRing.wildInertiaGroup A K F q = ⊥) ∧
    (0 < p → IsPGroup p (IsDiscreteValuationRing.wildInertiaGroup A K F q)) := by
  classical
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  obtain ⟨W, _, hWD, _, _, hWp, hW0, _, θ, _, hexact, _, _, _, hchar, _⟩ :=
    IsDiscreteValuationRing.exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity
      A K F q
  have hW : IsDiscreteValuationRing.wildInertiaGroup A K F q = W := by
    rw [IsDiscreteValuationRing.wildInertiaGroup_eq_ker_inertiaCharacter,
      ← IsDiscreteValuationRing.inertiaCharacter_eq A K F q θ hchar, ← W.range_subtype,
      hexact.monoidHom_ker_eq]
  rw [hW]
  exact ⟨hWD, hW0, hWp⟩

/-- The wild inertia group at a finite Galois subextension is trivial when the residue field has
characteristic zero. -/
@[sga "1 XIII 2.0" "special case"]
private lemma finite_wild_eq_bot_of_char_zero
    (A K F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    [Algebra A F] [IsScalarTower A K F]
    (q : Ideal (integralClosure A F)) [q.IsMaximal]
    (hp : ringChar (IsLocalRing.ResidueField A) = 0) :
    IsDiscreteValuationRing.wildInertiaGroup A K F q = ⊥ := by
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  exact (finite_wild_spec A K F q).2.1 hp

/-- The wild inertia group at a finite Galois subextension is a `p`-group for the positive residue
characteristic `p`. -/
@[sga "1 XIII 2.0" "special case"]
private lemma finite_wild_isPGroup
    (A K F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    [Algebra A F] [IsScalarTower A K F]
    (q : Ideal (integralClosure A F)) [q.IsMaximal]
    (hp : 0 < ringChar (IsLocalRing.ResidueField A)) :
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    IsPGroup (ringChar (IsLocalRing.ResidueField A))
      (IsDiscreteValuationRing.wildInertiaGroup A K F q) := by
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  exact (finite_wild_spec A K F q).2.2 hp

/-- The wild inertia group at a finite Galois subextension is stable under conjugation by the
decomposition group. -/
private lemma finite_wild_conjugate
    (A K F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    [Algebra A F] [IsScalarTower A K F]
    (q : Ideal (integralClosure A F)) [q.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    ∀ (τ : MulAction.stabilizer Gal(F/K) q)
      (σ ρ : q.inertia Gal(F/K)),
      (ρ : Gal(F/K)) = (τ : Gal(F/K)) * (σ : Gal(F/K)) *
        (τ : Gal(F/K))⁻¹ →
      σ ∈ IsDiscreteValuationRing.wildInertiaGroup A K F q →
      ρ ∈ IsDiscreteValuationRing.wildInertiaGroup A K F q := by
  classical
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let I := q.inertia Gal(F/K)
  let D := MulAction.stabilizer Gal(F/K) q
  let incl : I →* D := I.subtype.codRestrict D
    (fun σ ↦ Ideal.inertia_le_stabilizer (M := Gal(F/K)) q σ.property)
  obtain ⟨hWD, -⟩ := finite_wild_spec A K F q
  let W := IsDiscreteValuationRing.wildInertiaGroup A K F q
  intro τ σ ρ hρ hσ
  have hσD : incl σ ∈ W.map incl := Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
  have hρD : incl ρ ∈ W.map incl := by
    rw [show incl ρ = τ * incl σ * τ⁻¹ from Subtype.ext hρ]
    exact hWD.conj_mem _ hσD τ
  obtain ⟨ρ', hρ', heq⟩ := Subgroup.mem_map.mp hρD
  have hinj : Function.Injective incl := fun x y h ↦
    Subtype.val_injective (congrArg (fun z : D => (z : Gal(F/K))) h)
  exact hinj heq ▸ hρ'

/-- An automorphism whose restriction to a normal subextension is trivial fixes that subextension.
-/
private lemma apply_eq_self_of_restrictNormal_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (F : IntermediateField K L) [Normal K F] (σ : Gal(L/K))
    (h : AlgEquiv.restrictNormal σ F = 1) {x : L} (hx : x ∈ F) : σ x = x := by
  have := AlgEquiv.restrictNormal_commutes σ F ⟨x, hx⟩
  rw [h] at this
  exact this.symm

/-- An element of the inertia group which restricts into the wild inertia group at every finite
Galois subextension is trivial, when the residue field of the base has characteristic zero. -/
private lemma inertia_eq_one_of_wild_of_char_zero
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (hp : ringChar (IsLocalRing.ResidueField A) = 0) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∀ σ : P.inertia Gal(L/K),
      (∀ F : FiniteGaloisIntermediateField K L,
        letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
        letI : (P.comap
            (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
          isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
        (inertia_restriction_surjective A K L P F).choose σ ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom)) →
      σ = 1 := by
  classical
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro σ hwild
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  let F := FiniteGaloisIntermediateField.adjoin K {x}
  have hx : x ∈ (F : IntermediateField K L) :=
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : (P.comap
      (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
    isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
  have hW := hwild F
  rw [finite_wild_eq_bot_of_char_zero A K F
    (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) hp] at hW
  have hres : (AlgEquiv.restrictNormal (σ : Gal(L/K))
      (F : IntermediateField K L) : Gal(F/K)) = 1 := by
    rw [← (inertia_restriction_surjective A K L P F).choose_spec.2 σ]
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hW)
  exact apply_eq_self_of_restrictNormal_eq_one (F : IntermediateField K L) σ hres hx

/-- A subgroup of the inertia group whose elements restrict into the wild inertia group at every
finite Galois subextension is pro-`p` for the residue characteristic `p`: every finite group it
surjects onto with open kernel is a `p`-group. -/
private lemma inertia_subgroup_isPGroup_of_wild
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (hp : 0 < ringChar (IsLocalRing.ResidueField A)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∀ W : Subgroup (P.inertia Gal(L/K)),
      (∀ σ : W, ∀ F : FiniteGaloisIntermediateField K L,
        letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
        letI : (P.comap
            (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
          isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
        (inertia_restriction_surjective A K L P F).choose (σ : P.inertia Gal(L/K)) ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom)) →
      ∀ (H : Type*) [Group H] [Finite H] (f : W →* H),
        IsOpen (f.ker : Set W) → Function.Surjective f →
        IsPGroup (ringChar (IsLocalRing.ResidueField A)) H := by
  classical
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro W hwild H _ _ f hopen hsurj
  obtain ⟨u, hu, hu_eq⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨v, hv, hv_eq⟩ := isOpen_induced_iff.mp hu
  have hv1 : (1 : Gal(L/K)) ∈ v := by
    have h1 : (1 : W) ∈ (f.ker : Set W) :=
      MonoidHom.mem_ker.mpr (map_one f)
    rw [← hu_eq, ← hv_eq] at h1
    exact h1
  obtain ⟨E, hEfin, hEnorm, hEv⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L v).mp (hv.mem_nhds hv1)
  let : FiniteDimensional K E := hEfin
  let : IsGalois K E := (isGalois_iff).mpr ⟨inferInstance, hEnorm⟩
  let F : FiniteGaloisIntermediateField K L := ⟨E⟩
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : (P.comap
      (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
    isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
  let qF := P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
  let Wild := IsDiscreteValuationRing.wildInertiaGroup A K F qF
  let r := (inertia_restriction_surjective A K L P F).choose
  have hrker : ∀ σ : W, r (σ : P.inertia Gal(L/K)) = 1 → f σ = 1 := by
    intro σ hσ
    have hfix : ((σ : P.inertia Gal(L/K)) : Gal(L/K)) ∈
        (E.fixingSubgroup : Set Gal(L/K)) := by
      show ((σ : P.inertia Gal(L/K)) : Gal(L/K)) ∈ E.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hres := (inertia_restriction_surjective A K L P F).choose_spec.2
        (σ : P.inertia Gal(L/K))
      rw [hσ] at hres
      exact apply_eq_self_of_restrictNormal_eq_one (F : IntermediateField K L) _
        (by simpa using hres.symm) hx
    have hvσ : ((σ : P.inertia Gal(L/K)) : Gal(L/K)) ∈ v := hEv hfix
    have huσ : (σ : P.inertia Gal(L/K)) ∈ u := by
      rw [← hv_eq]
      exact hvσ
    have hfσ : σ ∈ (f.ker : Set W) := by
      rw [← hu_eq]
      exact huσ
    exact MonoidHom.mem_ker.mp hfσ
  apply (isPGroup_iff_pow_pow_eq_one).mpr
  intro h
  obtain ⟨σ, rfl⟩ := hsurj h
  have hσW : r (σ : P.inertia Gal(L/K)) ∈ Wild := hwild σ F
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp
    (finite_wild_isPGroup A K F qF hp)) ⟨r (σ : P.inertia Gal(L/K)), hσW⟩
  have hrpow : r ((σ : P.inertia Gal(L/K)) ^
      ringChar (IsLocalRing.ResidueField A) ^ k) = 1 := by
    simpa only [map_pow, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val hk
  have hfker := hrker (σ ^ ringChar (IsLocalRing.ResidueField A) ^ k) hrpow
  exact ⟨k, by simpa only [map_pow] using hfker⟩

/-- Restricting into the wild inertia group at every finite Galois subextension is the same as
exhibiting, at every such subextension, a wild automorphism which the given one restricts to. -/
private lemma wild_restriction_iff_exists_wild
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∀ σ : P.inertia Gal(L/K),
      (∀ F : FiniteGaloisIntermediateField K L,
        letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
        letI : (P.comap
            (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
          isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
        (inertia_restriction_surjective A K L P F).choose σ ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom)) ↔
      (∀ F : FiniteGaloisIntermediateField K L,
        let C := integralClosure A F
        letI : IsScalarTower A F L :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI : MulSemiringAction Gal(F/K) C :=
          IsIntegralClosure.MulSemiringAction A K F C
        let f : C →ₐ[A] integralClosure A L :=
          (IsScalarTower.toAlgHom A F L).mapIntegralClosure
        let q := P.comap f.toRingHom
        ∀ [q.IsMaximal],
          ∃ σF : q.inertia Gal(F/K),
            (σF : Gal(F/K)) =
              AlgEquiv.restrictNormal (σ : Gal(L/K))
                (F : IntermediateField K L) ∧
            σF ∈ IsDiscreteValuationRing.wildInertiaGroup A K F q) := by
  classical
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro σ
  constructor
  · intro h F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
      IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    dsimp only
    intro _
    exact ⟨(inertia_restriction_surjective A K L P F).choose σ,
      (inertia_restriction_surjective A K L P F).choose_spec.2 σ, h F⟩
  · intro h F
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
      IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    let : (P.comap
        (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
      isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
    obtain ⟨σF, hσF, hW⟩ := h F
    have heq : σF = (inertia_restriction_surjective A K L P F).choose σ :=
      Subtype.ext (hσF.trans ((inertia_restriction_surjective A K L P F).choose_spec.2 σ).symm)
    simpa only [heq] using hW

/-- A family of tame characters at the finite Galois subextensions which is compatible with the
quotients of tame ramification indices is realized by a single element of the inertia group. -/
private lemma exists_inertia_of_compatible_family
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (c : FiniteGaloisIntermediateField K L → (integralClosure A L ⧸ P)ˣ)
    (hpow : ∀ F : FiniteGaloisIntermediateField K L,
      letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      letI : (P.comap
          (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
        isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
      c F ^ IsDiscreteValuationRing.tameRamificationIndex A F
        (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) = 1)
    (hcompat : ∀ F G : FiniteGaloisIntermediateField K L, F ≤ G →
      letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      letI : IsScalarTower A G L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      letI : (P.comap
          (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
        isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
      letI : (P.comap
          (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom).IsMaximal :=
        isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A G L) P
      c G ^ (IsDiscreteValuationRing.tameRamificationIndex A G
          (P.comap (IsScalarTower.toAlgHom A G L).mapIntegralClosure.toRingHom) /
        IsDiscreteValuationRing.tameRamificationIndex A F
          (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom)) = c F) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ σ : P.inertia Gal(L/K),
      ∀ F : FiniteGaloisIntermediateField K L,
        finite_tame_character A K L P F σ = c F := by
  classical
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : CompactSpace (P.inertia Gal(L/K)) := inertia_compactSpace A K L P
  let t (F : FiniteGaloisIntermediateField K L) : Set (P.inertia Gal(L/K)) :=
    {σ | finite_tame_character A K L P F σ = c F}
  have hmono (F G : FiniteGaloisIntermediateField K L) (h : F ≤ G) : t G ⊆ t F := by
    intro σ hσ
    show finite_tame_character A K L P F σ = c F
    rw [finite_tame_character_le A K L P F G h σ]
    rw [show finite_tame_character A K L P G σ = c G from hσ]
    exact hcompat F G h
  have hdir : Directed (· ⊇ ·) t := by
    intro F G
    exact ⟨F ⊔ G, hmono F (F ⊔ G) le_sup_left, hmono G (F ⊔ G) le_sup_right⟩
  have hnonempty (F : FiniteGaloisIntermediateField K L) : (t F).Nonempty := by
    obtain ⟨σ, hσ⟩ := finite_tame_character_surjective A K L P F (c F) (hpow F)
    exact ⟨σ, hσ⟩
  have hclosed (F : FiniteGaloisIntermediateField K L) : IsClosed (t F) :=
    finite_tame_character_fiber_isClosed A K L P F (c F)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hnonempty (fun F => (hclosed F).isCompact) hclosed
  exact ⟨σ, fun F => Set.mem_iInter.mp hσ F⟩

/-- Conjugation by the decomposition group preserves the inertia elements whose restriction to
a finite Galois subextension lies in the wild inertia group there. -/
private lemma wild_restriction_conjugate
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (F : FiniteGaloisIntermediateField K L) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).IsMaximal :=
      isMaximal_comap_mapIntegralClosure
      (IsScalarTower.toAlgHom A F L) P
    ∀ (τ : MulAction.stabilizer Gal(L/K) P) (σ ρ : P.inertia Gal(L/K)),
      (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) * (τ : Gal(L/K))⁻¹ →
      (inertia_restriction_surjective A K L P F).choose σ ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) →
        (inertia_restriction_surjective A K L P F).choose ρ ∈
          IsDiscreteValuationRing.wildInertiaGroup A K F
            (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
    IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
  let := isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
  intro τ σ ρ hρ hσ
  obtain ⟨τF, hτF⟩ := stabilizer_restriction A K L P F τ
  let res : Gal(L/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hres (σ : P.inertia Gal(L/K)) :
      ((inertia_restriction_surjective A K L P F).choose σ : Gal(F/K)) = res σ :=
    (inertia_restriction_surjective A K L P F).choose_spec.2 σ
  refine finite_wild_conjugate A K F _ τF _ _ ?_ hσ
  rw [hres, hres, hρ, map_mul, map_mul, map_inv,
    show res (τ : Gal(L/K)) = (τF : Gal(F/K)) from hτF.symm]

/-- The canonical tame character has a pro-primary kernel and maps onto all compatible
families of prime-to-residue-characteristic roots of unity. -/
@[stacks 0BUA "the wild–tame exact sequence and canonical character",
  sga "1 XIII 2.0" "inertia structure", sga "7 I 0.3" "I/P ≅ Ẑ(1), P pro-p"]
public theorem exists_tameInertiaCharacter
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsGalois K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let I := P.inertia Gal(L/K)
    let D := MulAction.stabilizer Gal(L/K) P
    let p := ringChar (IsLocalRing.ResidueField A)
    ∃ S : Set ℕ,
      1 ∈ S ∧
      (∀ n ∈ S, 0 < n) ∧
      (p ≠ 0 → ∀ n ∈ S, Nat.Coprime n p) ∧
      (∀ n ∈ S, ∃ z : B ⧸ P, IsPrimitiveRoot z n) ∧
      (∀ n ∈ S, ∀ m ∈ S, ∃ k ∈ S, n ∣ k ∧ m ∣ k) ∧
      (∀ n ∈ S, ∃ (F : FiniteGaloisIntermediateField K L),
        let C := integralClosure A F
        letI : IsScalarTower A F L :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        let f : C →ₐ[A] B :=
          (IsScalarTower.toAlgHom A F L).mapIntegralClosure
        let q := P.comap f.toRingHom
        ∃ hq : q.IsMaximal,
          letI : q.IsMaximal := hq
          n ∣ IsDiscreteValuationRing.tameRamificationIndex A F q) ∧
      ∃ θ : I →* (∀ _ : S, (B ⧸ P)ˣ),
        (∀ σ : I, ∀ n : S, (θ σ n) ^ n.1 = 1) ∧
        (∀ σ : I, ∀ n m : S, n.1 ∣ m.1 →
          (θ σ m) ^ (m.1 / n.1) = θ σ n) ∧
        (∀ f : ∀ _ : S, (B ⧸ P)ˣ,
          (∀ n : S, (f n) ^ n.1 = 1) →
          (∀ n m : S, n.1 ∣ m.1 → (f m) ^ (m.1 / n.1) = f n) →
          ∃ σ : I, θ σ = f) ∧
        (∀ τ : D, ∀ σ : I,
          ∃ ρ : I,
            (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
              (τ : Gal(L/K))⁻¹ ∧
            ∀ n : S, θ ρ n =
              (Ideal.quotientEquiv P P
                ((MulSemiringAction.toRingEquiv Gal(L/K) B) (τ : Gal(L/K)))
                τ.property.symm).toMulEquiv (θ σ n)) ∧
        (∀ τ : D, ∀ σ : I, σ ∈ θ.ker →
          ∃ ρ : I,
            (ρ : Gal(L/K)) = (τ : Gal(L/K)) * (σ : Gal(L/K)) *
              (τ : Gal(L/K))⁻¹ ∧ ρ ∈ θ.ker) ∧
        (∀ (F : FiniteGaloisIntermediateField K L),
          let C := integralClosure A F
          letI : IsScalarTower A F L :=
            IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
          letI : MulSemiringAction Gal(F/K) C :=
            IsIntegralClosure.MulSemiringAction A K F C
          let f : C →ₐ[A] B :=
            (IsScalarTower.toAlgHom A F L).mapIntegralClosure
          let q := P.comap f.toRingHom
          ∀ [q.IsMaximal],
            ∃ hF : IsDiscreteValuationRing.tameRamificationIndex A F q ∈ S,
              ∀ σ : I,
                ∃ σF : q.inertia Gal(F/K),
                  (σF : Gal(F/K)) =
                    AlgEquiv.restrictNormal (σ : Gal(L/K))
                      (F : IntermediateField K L) ∧
                  ((θ σ ⟨IsDiscreteValuationRing.tameRamificationIndex A F q, hF⟩ :
                    (B ⧸ P)ˣ) : B ⧸ P) =
                    (Ideal.quotientMap P f.toRingHom le_rfl)
                      ((IsDiscreteValuationRing.canonicalInertiaCharacter A K F q σF).1.1)) ∧
        (∀ σ : I, σ ∈ θ.ker ↔
          ∀ (F : FiniteGaloisIntermediateField K L),
            let C := integralClosure A F
            letI : IsScalarTower A F L :=
              IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
            letI : MulSemiringAction Gal(F/K) C :=
              IsIntegralClosure.MulSemiringAction A K F C
            let f : C →ₐ[A] B :=
              (IsScalarTower.toAlgHom A F L).mapIntegralClosure
            let q := P.comap f.toRingHom
            ∀ [q.IsMaximal],
              ∃ σF : q.inertia Gal(F/K),
                (σF : Gal(F/K)) =
                  AlgEquiv.restrictNormal (σ : Gal(L/K))
                    (F : IntermediateField K L) ∧
                σF ∈ IsDiscreteValuationRing.wildInertiaGroup A K F q) ∧
        (p = 0 → θ.ker = ⊥) ∧
        (0 < p →
          ∀ (H : Type*) [Group H] [Finite H] (f : θ.ker →* H),
            IsOpen (f.ker : Set θ.ker) → Function.Surjective f → IsPGroup p H) := by
  classical
  let B := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L B
  let q (F : FiniteGaloisIntermediateField K L) : Ideal (integralClosure A F) :=
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom
  let (F : FiniteGaloisIntermediateField K L) : (q F).IsMaximal := by
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact isMaximal_comap_mapIntegralClosure (IsScalarTower.toAlgHom A F L) P
  let n (F : FiniteGaloisIntermediateField K L) :=
    IsDiscreteValuationRing.tameRamificationIndex A F (q F)
  let S : Set ℕ := {m | 0 < m ∧ ∃ F, m ∣ n F}
  refine ⟨S, ⟨Nat.zero_lt_one, ⊥, one_dvd _⟩, (fun m hm ↦ hm.1), ?_, ?_, ?_,
    (by
      intro m hm
      obtain ⟨F, hF⟩ := hm.2
      exact ⟨F, inferInstanceAs ((q F).IsMaximal), hF⟩), ?_⟩
  · intro hp m hm
    obtain ⟨F, hF⟩ := hm.2
    exact ((finite_tame_properties A K F (q F)).2.1 hp).of_dvd_left hF
  · intro m hm
    obtain ⟨F, hF⟩ := hm.2
    obtain ⟨z, hz⟩ := (finite_tame_properties A K F (q F)).2.2
    let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let f := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
    let φ := Ideal.quotientMap P f.toRingHom le_rfl
    have hz' := hz.map_of_injective (f := φ) Ideal.quotientMap_injective
    exact ⟨φ z ^ (n F / m), hz'.pow (finite_tame_properties A K F (q F)).1
      (Nat.div_mul_cancel hF).symm⟩
  · intro m hm k hk
    obtain ⟨F, hF⟩ := hm.2
    obtain ⟨G, hG⟩ := hk.2
    let E := F ⊔ G
    refine ⟨n E, ⟨(finite_tame_properties A K E (q E)).1,
      E, dvd_rfl⟩, ?_, ?_⟩
    · exact hF.trans (finite_tame_dvd_of_le A K L P F (F ⊔ G) le_sup_left)
    · exact hG.trans (finite_tame_dvd_of_le A K L P G (F ⊔ G) le_sup_right)
  · let stage (m : S) : FiniteGaloisIntermediateField K L :=
      Classical.choose m.2.2
    have hstage (m : S) : m.1 ∣ n (stage m) :=
      Classical.choose_spec m.2.2
    let θ : P.inertia Gal(L/K) →* (∀ m : S, (B ⧸ P)ˣ) := {
      toFun := fun σ m ↦
        finite_tame_character A K L P (stage m) σ ^ (n (stage m) / m.1)
      map_one' := by
        funext m
        simp
      map_mul' := by
        intro σ τ
        funext m
        show finite_tame_character A K L P (stage m) (σ * τ) ^
          (n (stage m) / m.1) =
          finite_tame_character A K L P (stage m) σ ^ (n (stage m) / m.1) *
          finite_tame_character A K L P (stage m) τ ^ (n (stage m) / m.1)
        rw [map_mul]
        exact mul_pow
          (finite_tame_character A K L P (stage m) σ)
          (finite_tame_character A K L P (stage m) τ)
          (n (stage m) / m.1)
    }
    have hθ_stage (σ : P.inertia Gal(L/K)) (m : S)
        (F : FiniteGaloisIntermediateField K L) (hm : m.1 ∣ n F) :
        θ σ m = finite_tame_character A K L P F σ ^ (n F / m.1) := by
      let E := stage m ⊔ F
      have hstageE : n (stage m) ∣ n E :=
        finite_tame_dvd_of_le A K L P (stage m) E le_sup_left
      have hFE : n F ∣ n E :=
        finite_tame_dvd_of_le A K L P F E le_sup_right
      calc
        θ σ m = finite_tame_character A K L P (stage m) σ ^
            (n (stage m) / m.1) := rfl
        _ = (finite_tame_character A K L P E σ ^
            (n E / n (stage m))) ^ (n (stage m) / m.1) := by
              rw [finite_tame_character_le A K L P (stage m) E le_sup_left σ]
        _ = finite_tame_character A K L P E σ ^ (n E / m.1) := by
              rw [← pow_mul, ← div_chain (hstage m) hstageE]
        _ = (finite_tame_character A K L P E σ ^ (n E / n F)) ^
            (n F / m.1) := by
              rw [← pow_mul, ← div_chain hm hFE]
        _ = finite_tame_character A K L P F σ ^ (n F / m.1) := by
              rw [finite_tame_character_le A K L P F E le_sup_right σ]
    have hθ_ker_all (σ : P.inertia Gal(L/K)) :
        σ ∈ θ.ker ↔
          ∀ F : FiniteGaloisIntermediateField K L,
            (inertia_restriction_surjective A K L P F).choose σ ∈
              IsDiscreteValuationRing.wildInertiaGroup A K F (q F) := by
      constructor
      · intro hσ F
        have hnF : n F ∈ S := ⟨(finite_tame_properties A K F (q F)).1, F, dvd_rfl⟩
        have hchar : finite_tame_character A K L P F σ = 1 := by
          have hcoord := congrFun (MonoidHom.mem_ker.mp hσ) ⟨n F, hnF⟩
          rw [hθ_stage σ ⟨n F, hnF⟩ F dvd_rfl] at hcoord
          simpa [n, Nat.div_self (finite_tame_properties A K F (q F)).1]
            using hcoord
        exact (finite_tame_character_eq_one_iff A K L P F σ).mp hchar
      · intro hσ
        apply MonoidHom.mem_ker.mpr
        funext m
        rw [hθ_stage σ m (stage m) (hstage m)]
        have hc := (finite_tame_character_eq_one_iff A K L P (stage m) σ).mpr
          (hσ (stage m))
        simp [hc]
    refine ⟨θ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro σ m
      show (finite_tame_character A K L P (stage m) σ ^
        (n (stage m) / m.1)) ^ m.1 = 1
      rw [← pow_mul, Nat.div_mul_cancel (hstage m)]
      exact finite_tame_character_pow A K L P (stage m) σ
    · intro σ m k hmk
      have hmstage : m.1 ∣ n (stage k) := hmk.trans (hstage k)
      rw [hθ_stage σ m (stage k) hmstage]
      show (finite_tame_character A K L P (stage k) σ ^
        (n (stage k) / k.1)) ^ (k.1 / m.1) =
          finite_tame_character A K L P (stage k) σ ^ (n (stage k) / m.1)
      rw [← pow_mul, ← div_chain hmk (hstage k)]
    · intro f hf_pow hf_compat
      let hnF (F : FiniteGaloisIntermediateField K L) : n F ∈ S :=
        ⟨(finite_tame_properties A K F (q F)).1, F, dvd_rfl⟩
      obtain ⟨σ, hσ⟩ := exists_inertia_of_compatible_family A K L P
        (fun F => f ⟨n F, hnF F⟩) (fun F => hf_pow ⟨n F, hnF F⟩)
        (fun F G h => hf_compat ⟨n F, hnF F⟩ ⟨n G, hnF G⟩
          (finite_tame_dvd_of_le A K L P F G h))
      refine ⟨σ, ?_⟩
      funext m
      rw [hθ_stage σ m (stage m) (hstage m), hσ (stage m)]
      exact hf_compat m ⟨n (stage m), hnF (stage m)⟩ (hstage m)
    · intro τ σ
      obtain ⟨ρ, hρ⟩ := inertia_conjugate A K L P τ σ
      refine ⟨ρ, hρ, ?_⟩
      intro m
      rw [hθ_stage ρ m (stage m) (hstage m),
        hθ_stage σ m (stage m) (hstage m)]
      simp only [Units.val_pow_eq_pow_val]
      rw [finite_tame_character_conj A K L P (stage m) τ σ ρ hρ, map_pow]
    · intro τ σ hσ
      obtain ⟨ρ, hρ⟩ := inertia_conjugate A K L P τ σ
      exact ⟨ρ, hρ, (hθ_ker_all ρ).mpr fun F ↦
        wild_restriction_conjugate A K L P F τ σ ρ hρ ((hθ_ker_all σ).mp hσ F)⟩
    · intro F
      let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
      let : MulSemiringAction Gal(F/K) (integralClosure A F) :=
        IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
      dsimp only
      intro _
      let hF : n F ∈ S := ⟨(finite_tame_properties A K F (q F)).1, F, dvd_rfl⟩
      refine ⟨hF, fun σ ↦ ?_⟩
      let σF := (inertia_restriction_surjective A K L P F).choose σ
      refine ⟨σF, (inertia_restriction_surjective A K L P F).choose_spec.2 σ, ?_⟩
      rw [hθ_stage σ ⟨n F, hF⟩ F dvd_rfl]
      simpa only [n, Nat.div_self (finite_tame_properties A K F (q F)).1,
        pow_one] using finite_tame_character_apply A K L P F σ
    · intro σ
      exact (hθ_ker_all σ).trans (wild_restriction_iff_exists_wild A K L P σ)
    · intro hp
      exact (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦
        inertia_eq_one_of_wild_of_char_zero A K L P hp σ ((hθ_ker_all σ).mp hσ)
    · intro hp H _ _ f hopen hsurj
      exact inertia_subgroup_isPGroup_of_wild A K L P hp θ.ker
        (fun σ F ↦ (hθ_ker_all (σ : P.inertia Gal(L/K))).mp σ.property F) H f hopen hsurj

end Stacks.FundamentalGroup
