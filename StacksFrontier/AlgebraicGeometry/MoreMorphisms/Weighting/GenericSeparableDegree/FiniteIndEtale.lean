module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.GenericPointCount
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.StrictHenselization
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree.GenericPointCount

/-!
# Generic separable degree over finite ind-étale algebras

This file counts geometric points of finite products of local algebras, computes the generic
separable degree when the strict henselization is a factor of a finite ind-étale algebra, and
expresses the weighted fibre sum over an affine strict henselization through generic separable
degrees.
-/

public section

open AlgebraicGeometry
open IsLocalRing
open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private theorem algHom_card_eq_residueField_of_finite
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra F B] [Module.Finite F B] :
    Nat.card (B →ₐ[F] K) = Nat.card ((maximalIdeal B).ResidueField →ₐ[F] K) := by
  classical
  let residueHom := IsScalarTower.toAlgHom F B (maximalIdeal B).ResidueField
  have hsurjective : Function.Surjective (fun hom :
      (maximalIdeal B).ResidueField →ₐ[F] K => hom.comp residueHom) := by
    intro hom
    let : (RingHom.ker hom.toRingHom).IsPrime := RingHom.ker_isPrime _
    let : (RingHom.ker hom.toRingHom).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under
        (R := F) (RingHom.ker hom.toRingHom) (by
          have hbot : (RingHom.ker hom.toRingHom).comap (algebraMap F B) = ⊥ := by
            ext element
            show hom (algebraMap F B element) = 0 ↔ element = 0
            rw [hom.commutes]
            exact map_eq_zero (algebraMap F K)
          rw [Ideal.under_def, hbot]
          infer_instance)
    have hker : RingHom.ker hom.toRingHom = maximalIdeal B :=
      eq_maximalIdeal inferInstance
    refine ⟨Ideal.ResidueField.liftₐ (maximalIdeal B) hom
      (by rw [← hker]; exact le_rfl) ?_, ?_⟩
    · intro element helement
      exact isUnit_iff_ne_zero.mpr fun hzero =>
        helement (hker ▸ hzero : element ∈ maximalIdeal B)
    · exact Ideal.ResidueField.liftₐ_comp_toAlgHom _ _ _ _
  have hinjective : Function.Injective (fun hom :
      (maximalIdeal B).ResidueField →ₐ[F] K => hom.comp residueHom) := by
    intro hom₁ hom₂ heq
    exact Ideal.ResidueField.algHom_ext heq
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinjective, hsurjective⟩)).symm

private theorem algHom_card_eq_finSepDegree_of_finite_local
    (F K : Type*) [Field F] [Field K] [IsAlgClosed K] [Algebra F K]
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra F B] [Module.Finite F B] :
    Nat.card (B →ₐ[F] K) = Field.finSepDegree F (ResidueField B) := by
  let equiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField B) (maximalIdeal B).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal B))
  let : IsScalarTower F (ResidueField B) (maximalIdeal B).ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro element
    rfl
  rw [algHom_card_eq_residueField_of_finite F K B,
    ← algHom_card_eq_of_algEquiv F (ResidueField B) _ K (equiv.restrictScalars F)]
  exact (Field.finSepDegree_eq_of_isAlgClosed F (ResidueField B) K).symm

private theorem algHom_card_eq_one_of_finite_local
    (F K : Type*) [Field F] [IsSepClosed F] [Field K] [IsAlgClosed K] [Algebra F K]
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra F B] [Module.Finite F B] :
    Nat.card (B →ₐ[F] K) = 1 := by
  rw [algHom_card_eq_finSepDegree_of_finite_local F K B]
  exact IsPurelyInseparable.finSepDegree_eq_one F (ResidueField B)

private theorem algHom_card_pi_eq_card_of_finite_local
    (F K : Type*) [Field F] [IsSepClosed F] [Field K] [IsAlgClosed K] [Algebra F K]
    {index : Type*} [Fintype index] (factors : index → Type*)
    [∀ element, CommRing (factors element)] [∀ element, IsLocalRing (factors element)]
    [∀ element, Algebra F (factors element)] [∀ element, Module.Finite F (factors element)] :
    Nat.card ((∀ element, factors element) →ₐ[F] K) = Fintype.card index := by
  rw [algHom_card_pi]
  simp_rw [algHom_card_eq_one_of_finite_local F K]
  simp

private theorem algHom_card_tensorProduct_pi
    (R F K : Type*) [CommRing R] [Field F] [Field K]
    [Algebra R F] [Algebra F K]
    {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Finite R (A i)] :
    Nat.card ((F ⊗[R] (∀ i, A i)) →ₐ[F] K) =
      ∑ i, Nat.card ((F ⊗[R] A i) →ₐ[F] K) := by
  classical
  rw [algHom_card_eq_of_algEquiv F _ _ K (Algebra.TensorProduct.piRight R F F A)]
  exact algHom_card_pi F K _

private theorem isLocalizationAtPrime_of_piAlgEquiv
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {index : Type u} (factors : index → Type u)
    [∀ element, CommRing (factors element)] [∀ element, Algebra R (factors element)]
    [∀ element, IsLocalRing (factors element)]
    (equiv : B ≃ₐ[R] ∀ element, factors element) (element : index) :
    let projection := (Pi.evalAlgHom R factors element).comp equiv.toAlgHom
    let : Algebra B (factors element) := projection.toRingHom.toAlgebra
    IsLocalization.AtPrime (factors element)
      ((maximalIdeal (factors element)).comap projection.toRingHom) := by
  classical
  let projection := (Pi.evalAlgHom R factors element).comp equiv.toAlgHom
  let : Algebra B (factors element) := projection.toRingHom.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro denominator
    exact notMem_maximalIdeal.mp denominator.2
  · intro value
    refine ⟨(equiv.symm (Pi.single element value), 1), ?_⟩
    show value * projection 1 = projection (equiv.symm (Pi.single element value))
    simp [projection]
  · intro numerator₁ numerator₂ heq
    change equiv numerator₁ element = equiv numerator₂ element at heq
    refine ⟨⟨equiv.symm (Pi.single element 1), ?_⟩, ?_⟩
    · simp [Ideal.mem_comap]
    · apply equiv.injective
      ext coordinate
      by_cases hcoordinate : coordinate = element
      · subst coordinate
        simpa using heq
      · simp [hcoordinate]

private theorem exists_henselianLocalFactors_indEtale
    {R : Type u} [CommRing R]
    (Rsh : Type u) [CommRing Rsh] [HenselianLocalRing Rsh]
    [Algebra R Rsh] [IsSepClosed (ResidueField Rsh)]
    (hind : StacksDraft.IndEtale R Rsh)
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] :
    ∃ (index : Type u) (_ : Fintype index) (factors : index → Type u)
      (_ : ∀ element, CommRing (factors element))
      (_ : ∀ element, Algebra Rsh (factors element))
      (_ : ∀ element, HenselianLocalRing (factors element)),
      (∀ element, Module.Finite Rsh (factors element)) ∧
      ∃ equiv : (Rsh ⊗[R] B) ≃ₐ[Rsh] ∀ element, factors element,
        ∀ element,
          let projection := (Pi.evalAlgHom Rsh factors element).comp equiv.toAlgHom
          let : Algebra (Rsh ⊗[R] B) (factors element) := projection.toRingHom.toAlgebra
          let : Algebra B (factors element) :=
            (projection.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
          StacksDraft.IndEtale B (factors element) := by
  classical
  let tensor := Rsh ⊗[R] B
  obtain ⟨index, _, factors, _, _, _, hfinite, ⟨equiv⟩⟩ :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u}
      Rsh).1
      tensor inferInstance
  let : Fintype index := Fintype.ofFinite index
  refine ⟨index, inferInstance, factors, inferInstance, inferInstance, inferInstance,
    hfinite, equiv, ?_⟩
  intro element
  let projection := (Pi.evalAlgHom Rsh factors element).comp equiv.toAlgHom
  let : Algebra tensor (factors element) := projection.toRingHom.toAlgebra
  let : Algebra B tensor := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (factors element) :=
    (projection.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
  let : IsScalarTower B tensor (factors element) := .of_algebraMap_eq' rfl
  let prime : Ideal tensor :=
    (maximalIdeal (factors element)).comap projection.toRingHom
  let : prime.IsPrime := Ideal.comap_isPrime _ _
  let : IsLocalization.AtPrime (factors element) prime :=
    isLocalizationAtPrime_of_piAlgEquiv factors equiv element
  have htensor : StacksDraft.IndEtale B tensor :=
    StacksDraft.indEtale_of_equiv (RingEquiv.refl B)
      (Algebra.TensorProduct.comm R B Rsh).toRingEquiv
      (fun _ => rfl) (StacksDraft.indEtale_tensorProduct B hind)
  exact StacksDraft.indEtale_comp htensor (StacksDraft.indEtale_atPrime prime)

private theorem exists_strictHenselization_of_finite_indEtale_of_isLocalization
    {Rsh B T S : Type u} [CommRing Rsh] [CommRing B] [CommRing T] [CommRing S]
    [HenselianLocalRing Rsh] [HenselianLocalRing T] [IsLocalRing S]
    [Algebra Rsh T] [Module.Finite Rsh T]
    [IsSepClosed (ResidueField Rsh)] [Algebra B T] [Algebra B S]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime S q]
    (hq : q = (maximalIdeal T).comap (algebraMap B T))
    (hind : StacksDraft.IndEtale B T) :
    ∃ algebra : Algebra S T,
      ∃ _tower : @IsScalarTower B S T _ algebra.toSMul _,
        ∃ closureAlgebra : Algebra (maximalIdeal S).ResidueField
            (maximalIdeal T).ResidueField,
          ∃ closure : @IsSepClosure (maximalIdeal S).ResidueField _
              (maximalIdeal T).ResidueField _ closureAlgebra,
            Nonempty (@Stacks.StrictHenselization.IsStrictHenselization S _ _
              (maximalIdeal T).ResidueField _ closureAlgebra closure T _ _ algebra) := by
  have hunits : ∀ denominator : q.primeCompl, IsUnit (algebraMap B T denominator) := by
    intro denominator
    exact notMem_maximalIdeal.mp fun hmem => denominator.2 (hq ▸ hmem)
  let lift : S →+* T := IsLocalization.lift hunits
  let : Algebra S T := lift.toAlgebra
  let : IsScalarTower B S T := .of_algebraMap_eq fun element =>
    (IsLocalization.lift_eq hunits element).symm
  let : IsLocalHom (algebraMap S T) := by
    have hle : maximalIdeal S ≤ (maximalIdeal T).comap (algebraMap S T) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q S,
        Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hq.le
    exact ⟨fun element hunit => notMem_maximalIdeal.mp fun helement =>
      notMem_maximalIdeal.mpr hunit (hle helement)⟩
  let : IsLocalHom (algebraMap Rsh T) :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u}
      Rsh).2.1 T inferInstance |>.2
  let : Algebra.IsIntegral (ResidueField Rsh) (ResidueField T) :=
    Algebra.IsIntegral.residueField
  let : IsSepClosed (ResidueField T) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField Rsh)
  have hlocal : StacksDraft.IndEtale S T :=
    StacksDraft.indEtale_of_comp (StacksDraft.indEtale_atPrime q) hind
  let : IsSepClosure (ResidueField S) (ResidueField T) :=
    isSepClosure_residueField_of_indEtale hlocal
  obtain ⟨closureAlgebra, closure, hstrict⟩ := exists_isStrictHenselization_of_indEtale hlocal
  exact ⟨inferInstance, inferInstance, closureAlgebra, closure, hstrict⟩

private theorem exists_strictHenselization_of_finite_indEtale
    {Rsh B T : Type u} [CommRing Rsh] [CommRing B] [CommRing T]
    [HenselianLocalRing Rsh] [HenselianLocalRing T]
    [Algebra Rsh T] [Module.Finite Rsh T]
    [IsSepClosed (ResidueField Rsh)] [Algebra B T]
    (hind : StacksDraft.IndEtale B T) :
    let prime := (maximalIdeal T).comap (algebraMap B T)
    let : prime.IsPrime := Ideal.comap_isPrime _ _
    let localRing := Localization.AtPrime prime
    ∃ algebra : Algebra localRing T,
      ∃ _tower : @IsScalarTower B localRing T _ algebra.toSMul _,
        ∃ closureAlgebra : Algebra (maximalIdeal localRing).ResidueField
            (maximalIdeal T).ResidueField,
          ∃ closure : @IsSepClosure (maximalIdeal localRing).ResidueField _
              (maximalIdeal T).ResidueField _ closureAlgebra,
            Nonempty (@Stacks.StrictHenselization.IsStrictHenselization localRing _ _
              (maximalIdeal T).ResidueField _ closureAlgebra closure T _ _ algebra) := by
  intro prime _ localRing
  exact exists_strictHenselization_of_finite_indEtale_of_isLocalization
    (Rsh := Rsh) (S := localRing) prime rfl hind

private theorem exists_henselianLocalFactors_genericPointCount
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (F K : Type u) [Field F] [Field K] [Algebra R F] [Algebra F K] :
    ∃ (ι : Type u) (_ : Fintype ι) (A : ι → Type u)
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i))
      (_ : ∀ i, HenselianLocalRing (A i)),
      (∀ i, Module.Finite R (A i)) ∧
      ∃ _e : B ≃ₐ[R] ∀ i, A i,
        Nat.card ((F ⊗[R] B) →ₐ[F] K) =
          ∑ i, Nat.card ((F ⊗[R] A i) →ₐ[F] K) := by
  obtain ⟨ι, hι, A, hring, halg, hhens, hfin, ⟨e⟩⟩ :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u} R).1
      B inferInstance
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : ∀ i, Module.Finite R (A i) := hfin
  refine ⟨ι, inferInstance, A, hring, halg, hhens, hfin, e, ?_⟩
  rw [algHom_card_eq_of_algEquiv F _ _ K
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e)]
  exact algHom_card_tensorProduct_pi R F K A

private theorem genericPointCount_eq_of_finite_indEtale
    {R B Rsh T : Type u} [CommRing R] [CommRing B] [CommRing Rsh] [CommRing T]
    [IsLocalRing R] [HenselianLocalRing Rsh] [HenselianLocalRing T]
    [Algebra R B] [Module.Finite R B] [Algebra R Rsh]
    [Algebra Rsh T] [Module.Finite Rsh T] [Algebra B T] [Algebra R T]
    [IsScalarTower R B T] [IsScalarTower R Rsh T]
    (κR : Type u) [Field κR] [Algebra (maximalIdeal R).ResidueField κR]
    [IsSepClosure (maximalIdeal R).ResidueField κR]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization R κR Rsh)
    (hunibranch : _root_.IsGeometricallyUnibranch R)
    (hind : StacksDraft.IndEtale B T)
    (q : Ideal B) [q.IsPrime] (hq : q = (maximalIdeal T).comap (algebraMap B T))
    [IsLocalHom (algebraMap R (Localization.AtPrime q))]
    (prime : Ideal Rsh) [prime.IsPrime] (hprime : prime ∈ minimalPrimes Rsh)
    (K : Type u) [Field K] [Algebra prime.ResidueField K]
    [IsAlgClosure prime.ResidueField K] :
    genericPointCount (S := Localization.AtPrime q) hunibranch =
      Nat.card ((prime.ResidueField ⊗[Rsh] T) →ₐ[prime.ResidueField] K) := by
  subst q
  let := hRsh.isLocalHom
  let := isSepClosure_residueField_of_strictHenselization R κR Rsh hRsh
  let : IsSepClosed (ResidueField Rsh) := IsSepClosure.sep_closed (ResidueField R)
  obtain ⟨algebra, tower, closureAlgebra, closure, ⟨hT⟩⟩ :=
    exists_strictHenselization_of_finite_indEtale (Rsh := Rsh) hind
  let := algebra
  let := tower
  let := closureAlgebra
  let := closure
  let localRing := Localization.AtPrime ((maximalIdeal T).comap (algebraMap B T))
  let : IsScalarTower R localRing T := IsScalarTower.to₁₃₄ R B localRing T
  exact genericPointCount_eq hunibranch κR Rsh hRsh
    (maximalIdeal T).ResidueField T hT prime hprime K

private theorem genericSeparableDegree_eq_of_finite_indEtale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hY : IsGeometricallyUnibranch Y) (point : X)
    (B : Type u) [CommRing B] [Algebra B (X.presheaf.stalk point)]
    (q : Ideal B) [q.IsPrime] [IsLocalization.AtPrime (X.presheaf.stalk point) q]
    (κR : Type u) [Field κR]
    [Algebra (maximalIdeal (Y.presheaf.stalk (f point))).ResidueField κR]
    [IsSepClosure (maximalIdeal (Y.presheaf.stalk (f point))).ResidueField κR]
    (Rsh : Type u) [CommRing Rsh] [HenselianLocalRing Rsh]
    [Algebra (Y.presheaf.stalk (f point)) Rsh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization (Y.presheaf.stalk (f point)) κR Rsh)
    (T : Type u) [CommRing T] [HenselianLocalRing T]
    [Algebra Rsh T] [Module.Finite Rsh T] [Algebra B T]
    [Algebra (Y.presheaf.stalk (f point)) T]
    [IsScalarTower (Y.presheaf.stalk (f point)) Rsh T]
    (hq : q = (maximalIdeal T).comap (algebraMap B T))
    (hind : StacksDraft.IndEtale B T)
    (hcomp : ∀ algebra : Algebra (X.presheaf.stalk point) T,
      @IsScalarTower B (X.presheaf.stalk point) T _ algebra.toSMul _ →
        algebraMap (Y.presheaf.stalk (f point)) T =
          (@algebraMap (X.presheaf.stalk point) T _ _ algebra).comp (f.stalkMap point).hom)
    (prime : Ideal Rsh) [prime.IsPrime] (hprime : prime ∈ minimalPrimes Rsh)
    (K : Type u) [Field K] [Algebra prime.ResidueField K]
    [IsAlgClosure prime.ResidueField K] :
    genericSeparableDegree f hY point =
      Nat.card ((prime.ResidueField ⊗[Rsh] T) →ₐ[prime.ResidueField] K) := by
  let := hRsh.isLocalHom
  let := isSepClosure_residueField_of_strictHenselization
    (Y.presheaf.stalk (f point)) κR Rsh hRsh
  let : IsSepClosed (ResidueField Rsh) :=
    IsSepClosure.sep_closed (ResidueField (Y.presheaf.stalk (f point)))
  obtain ⟨algebra, tower, closureAlgebra, closure, ⟨hT⟩⟩ :=
    exists_strictHenselization_of_finite_indEtale_of_isLocalization
      (Rsh := Rsh) (S := X.presheaf.stalk point) q hq hind
  let := algebra
  let := tower
  let := closureAlgebra
  let := closure
  exact genericSeparableDegree_eq f hY point κR Rsh hRsh
    (maximalIdeal T).ResidueField T hT (hcomp algebra tower) prime hprime K

private theorem algHom_card_eq_of_isAlgClosed
    (F B K L : Type u) [Field F] [CommRing B] [Algebra F B] [Module.Finite F B]
    [Field K] [Algebra F K] [IsAlgClosed K]
    [Field L] [Algebra F L] [IsAlgClosed L] :
    Nat.card (B →ₐ[F] K) = Nat.card (B →ₐ[F] L) := by
  obtain ⟨index, _, factors, _, _, _, hfinite, ⟨equiv⟩⟩ :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, u, u}
      F).1 B inferInstance
  let : Fintype index := Fintype.ofFinite index
  let : ∀ element, Module.Finite F (factors element) := hfinite
  rw [algHom_card_eq_of_algEquiv F B _ K equiv,
    algHom_card_eq_of_algEquiv F B _ L equiv, algHom_card_pi, algHom_card_pi]
  apply Finset.sum_congr rfl
  intro element _
  rw [algHom_card_eq_finSepDegree_of_finite_local,
    algHom_card_eq_finSepDegree_of_finite_local]

theorem minimalPrime_comap_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (prime : Ideal S) [prime.IsPrime] (hprime : prime ∈ minimalPrimes S) :
    prime.comap (algebraMap R S) ∈ minimalPrimes R := by
  show IsMinimalPrime (prime.comap (algebraMap R S))
  rw [IsMinimalPrime.iff_minimal]
  refine ⟨Ideal.comap_isPrime _ _, ?_⟩
  intro smaller hsmaller hle
  let : smaller.IsPrime := hsmaller
  let : prime.LiesOver (prime.comap (algebraMap R S)) := ⟨rfl⟩
  obtain ⟨lift, hlift, hprimeLift, hover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := smaller) prime hle
  have heq : prime = lift := le_antisymm (hprime.2 ⟨hprimeLift, bot_le⟩ hlift) hlift
  rw [heq]
  exact hover.over.ge

/-- The residue field of an affine scheme at a point written as a prime of the ring. The ambient
instance is stated for a point of the scheme, whose type is only definitionally a prime
spectrum, so instance search does not see it through that identification. -/
private noncomputable abbrev affineResidueFieldField (A : Type u) [CommRing A]
    (point : PrimeSpectrum A) : Field ((Spec (.of A)).residueField point) :=
  inferInstanceAs (Field ((Spec (.of A)).residueField (show Spec (.of A) from point)))

attribute [local instance] affineResidueFieldField

private theorem weightedFiberSum_of_finite_pi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsSepClosed (ResidueField R)]
    {index : Type u} [Fintype index] (factors : index → Type u)
    [∀ element, CommRing (factors element)] [∀ element, IsLocalRing (factors element)]
    [∀ element, Algebra R (factors element)]
    [∀ element, Module.Finite R (factors element)]
    (B : Type u) [CommRing B] [Algebra R B]
    (equiv : B ≃ₐ[R] ∀ element, factors element) (weight : Spec (.of B) → ℤ) :
    separableDegreeWeightedFiberSum
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) weight (closedPoint R) =
      ∑ element, weight (PrimeSpectrum.comap
        (((Pi.evalAlgHom R factors element).comp equiv.toAlgHom).toRingHom)
        (closedPoint (factors element))) := by
  classical
  let projection (element : index) : B →ₐ[R] factors element :=
    (Pi.evalAlgHom R factors element).comp equiv.toAlgHom
  let point (element : index) : PrimeSpectrum B :=
    PrimeSpectrum.comap (projection element).toRingHom (closedPoint (factors element))
  let fiber := {point : PrimeSpectrum B //
    PrimeSpectrum.comap (algebraMap R B) point = closedPoint R}
  have hpoint (element : index) :
      PrimeSpectrum.comap (algebraMap R B) (point element) = closedPoint R := by
    show PrimeSpectrum.comap (algebraMap R B)
      (PrimeSpectrum.comap (projection element).toRingHom _) = _
    rw [← PrimeSpectrum.comap_comp_apply]
    rw [show (projection element).toRingHom.comp (algebraMap R B) =
      algebraMap R (factors element) from by ext value; exact (projection element).commutes value]
    exact PrimeSpectrum.ext (eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (maximalIdeal (factors element))))
  have hinjective : Function.Injective point := by
    intro first second heq
    have heq' : PrimeSpectrum.sigmaToPi factors ⟨first, closedPoint (factors first)⟩ =
        PrimeSpectrum.sigmaToPi factors ⟨second, closedPoint (factors second)⟩ := by
      apply (PrimeSpectrum.comapEquiv equiv.toRingEquiv).symm.injective
      exact heq
    exact congrArg Sigma.fst (PrimeSpectrum.sigmaToPi_injective factors heq')
  have hsurjective : ∀ target : fiber, ∃ element, point element = target.1 := by
    intro target
    let mapped := (PrimeSpectrum.comapEquiv equiv.toRingEquiv) target.1
    obtain ⟨⟨element, prime⟩, hprime⟩ := PrimeSpectrum.sigmaToPi_bijective factors |>.2 mapped
    have hcomap : prime.asIdeal.comap (algebraMap R (factors element)) = maximalIdeal R := by
      have htarget := congrArg PrimeSpectrum.asIdeal target.2
      have hprimeTarget : PrimeSpectrum.comap (projection element).toRingHom prime = target.1 := by
        have heq := congrArg (PrimeSpectrum.comap equiv.toRingHom) hprime
        show PrimeSpectrum.comap equiv.toRingHom
          (PrimeSpectrum.comap (Pi.evalRingHom factors element) prime) = target.1
        exact heq.trans ((PrimeSpectrum.comapEquiv equiv.toRingEquiv).symm_apply_apply target.1)
      rw [← hprimeTarget] at htarget
      simpa [Ideal.comap_comap, AlgHom.comp_algebraMap, closedPoint] using htarget
    have hmaximal : prime.asIdeal.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) prime.asIdeal
        (by rw [Ideal.under_def, hcomap]; infer_instance)
    have heqprime : prime = closedPoint (factors element) :=
      PrimeSpectrum.ext (eq_maximalIdeal hmaximal)
    refine ⟨element, ?_⟩
    have heq := congrArg (PrimeSpectrum.comap equiv.toRingHom) hprime
    show PrimeSpectrum.comap equiv.toRingHom
      (PrimeSpectrum.comap (Pi.evalRingHom factors element) (closedPoint _)) = target.1
    rw [← heqprime]
    exact heq.trans ((PrimeSpectrum.comapEquiv equiv.toRingEquiv).symm_apply_apply target.1)
  let enumeration : index ≃ fiber := Equiv.ofBijective
    (fun element => ⟨point element, hpoint element⟩)
    ⟨fun _ _ heq => hinjective (congrArg Subtype.val heq), fun target => by
      obtain ⟨element, heq⟩ := hsurjective target
      exact ⟨element, Subtype.ext heq⟩⟩
  have hdegree (element : index) :
      let : Algebra ((Spec (.of R)).residueField
          ((Spec.map (CommRingCat.ofHom (algebraMap R B))) (point element)))
        ((Spec (.of B)).residueField (point element)) :=
        ((Spec.map (CommRingCat.ofHom (algebraMap R B))).residueFieldMap
          (point element)).hom.toAlgebra
      Field.finSepDegree ((Spec (.of R)).residueField
          ((Spec.map (CommRingCat.ofHom (algebraMap R B))) (point element)))
        ((Spec (.of B)).residueField (point element)) = 1 := by
    let hom := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let : Algebra ((Spec (.of R)).residueField (hom (point element)))
        ((Spec (.of B)).residueField (point element)) :=
      (hom.residueFieldMap (point element)).hom.toAlgebra
    let : IsSepClosed ((Spec (.of R)).residueField (hom (point element))) := by
      rw [show hom (point element) = closedPoint R from hpoint element]
      exact IsSepClosed.of_ringEquiv
        ((Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).commRingCatIsoToRingEquiv.trans
          (AlgEquiv.ofBijective (Algebra.ofId (ResidueField R)
            (maximalIdeal R).ResidueField)
            (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm.toRingEquiv)
    let : Module.Finite R B := Module.Finite.equiv equiv.symm.toLinearEquiv
    let : IsFinite hom := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_algebraMap).mpr inferInstance)
    let := module_finite_residueFieldMap hom (point element)
    exact IsPurelyInseparable.finSepDegree_eq_one _ _
  unfold separableDegreeWeightedFiberSum
  show (∑ᶠ target : PrimeSpectrum B, if PrimeSpectrum.comap (algebraMap R B) target =
      closedPoint R then _ else 0) = _
  rw [finsum_eq_sum_of_support_subset_of_finite _ (s := Set.range point) (by
    intro target htarget
    by_cases hmem : PrimeSpectrum.comap (algebraMap R B) target = closedPoint R
    · exact hsurjective ⟨target, hmem⟩
    · simp [hmem] at htarget) (Set.finite_range point)]
  rw [Set.Finite.toFinset_range, Finset.sum_image (by
    intro first _ second _ heq
    exact hinjective heq)]
  apply Finset.sum_congr rfl
  intro element _
  rw [ite_eq_left (hpoint element), hdegree element]
  simp only [Nat.cast_one, mul_one]
  rfl

private noncomputable abbrev affineStalkAlgebra (A : Type u) [CommRing A]
    (point : PrimeSpectrum A) :
    Algebra A ((Spec (.of A)).presheaf.stalk point) :=
  StructureSheaf.stalkAlgebra A point

attribute [local instance] affineStalkAlgebra

private theorem affineStalkLocalization (A : Type u) [CommRing A]
    (point : PrimeSpectrum A) :
    IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk point) point.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A point

attribute [local instance] affineStalkLocalization

private theorem affineStalkLocalRing (A : Type u) [CommRing A]
    (point : PrimeSpectrum A) : IsLocalRing ((Spec (.of A)).presheaf.stalk point) :=
  IsLocalization.AtPrime.isLocalRing _ point.asIdeal

attribute [local instance] affineStalkLocalRing

/-- `affineStalkAlgebra` with the point written as a point of the scheme rather than as a prime
of the ring; the two types agree definitionally but not reducibly. -/
private noncomputable abbrev affineStalkAlgebraAtSchemePoint (A : Type u) [CommRing A]
    (point : Spec (.of A)) : Algebra A ((Spec (.of A)).presheaf.stalk point) :=
  affineStalkAlgebra A point

attribute [local instance] affineStalkAlgebraAtSchemePoint

/-- A point of an affine scheme carries a prime ideal of the ring. -/
private theorem affineSchemePoint_isPrime (A : Type u) [CommRing A] (point : Spec (.of A)) :
    (point : PrimeSpectrum A).asIdeal.IsPrime :=
  (point : PrimeSpectrum A).isPrime

attribute [local instance] affineSchemePoint_isPrime

/-- `affineStalkLocalization` with the point written as a point of the scheme. -/
private theorem affineStalkLocalizationAtSchemePoint (A : Type u) [CommRing A]
    (point : Spec (.of A)) :
    IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk point)
      (point : PrimeSpectrum A).asIdeal :=
  affineStalkLocalization A point

attribute [local instance] affineStalkLocalizationAtSchemePoint

/-- `affineStalkLocalRing` with the point written as a point of the scheme. -/
private theorem affineStalkLocalRingAtSchemePoint (A : Type u) [CommRing A]
    (point : Spec (.of A)) : IsLocalRing ((Spec (.of A)).presheaf.stalk point) :=
  affineStalkLocalRing A point

attribute [local instance] affineStalkLocalRingAtSchemePoint

private theorem genericSeparableDegree_eq_of_affine_factor
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hY : IsGeometricallyUnibranch (Spec (.of A)))
    (point : PrimeSpectrum B)
    (κ : Type u) [Field κ]
    [Algebra (maximalIdeal ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point))).ResidueField κ]
    [IsSepClosure (maximalIdeal ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point))).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [HenselianLocalRing Rsh]
    [Algebra ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) Rsh]
    [Algebra A Rsh] [IsScalarTower A ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) Rsh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization
      ((Spec (.of A)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) κ Rsh)
    (factor : Type u) [CommRing factor] [HenselianLocalRing factor]
    [Algebra Rsh factor] [Module.Finite Rsh factor]
    [Algebra B factor] [Algebra A factor]
    [Algebra ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) factor]
    [IsScalarTower A B factor] [IsScalarTower A Rsh factor]
    [IsScalarTower A ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) factor]
    [IsScalarTower ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) Rsh factor]
    (hq : point.asIdeal = (maximalIdeal factor).comap (algebraMap B factor))
    (hind : StacksDraft.IndEtale B factor)
    (prime : Ideal Rsh) [prime.IsPrime] (hprime : prime ∈ minimalPrimes Rsh)
    (K : Type u) [Field K] [Algebra prime.ResidueField K]
    [IsAlgClosure prime.ResidueField K] :
    genericSeparableDegree (Spec.map (CommRingCat.ofHom (algebraMap A B))) hY point =
      Nat.card ((prime.ResidueField ⊗[Rsh] factor) →ₐ[prime.ResidueField] K) := by
  apply genericSeparableDegree_eq_of_finite_indEtale
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) hY point B point.asIdeal
    κ Rsh hRsh factor hq hind _ prime hprime K
  intro algebra tower
  let := algebra
  let := tower
  apply IsLocalization.ringHom_ext
    (((Spec.map (CommRingCat.ofHom (algebraMap A B))) point).asIdeal.primeCompl)
  ext value
  show algebraMap ((Spec (.of A)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) factor
      (algebraMap A ((Spec (.of A)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) value) =
    algebraMap ((Spec (.of B)).presheaf.stalk point) factor
      (((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap point).hom
        (algebraMap A ((Spec (.of A)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) value))
  have hstalk := ConcreteCategory.congr_hom
    (stalkMap_toStalk (CommRingCat.ofHom (algebraMap A B)) point) value
  change ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap point).hom
      (algebraMap A ((Spec (.of A)).presheaf.stalk
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))) point)) value) =
    algebraMap B ((Spec (.of B)).presheaf.stalk point) (algebraMap A B value) at hstalk
  rw [hstalk, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  exact IsScalarTower.algebraMap_apply A B factor value

private theorem weightedFiberSum_eq_of_affine_strictHenselization
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hY : IsGeometricallyUnibranch (Spec (.of A)))
    (basePoint : PrimeSpectrum A)
    (κ : Type u) [Field κ]
    [Algebra (maximalIdeal ((Spec (.of A)).presheaf.stalk basePoint)).ResidueField κ]
    [IsSepClosure (maximalIdeal ((Spec (.of A)).presheaf.stalk basePoint)).ResidueField κ]
    (Rsh : Type u) [CommRing Rsh] [HenselianLocalRing Rsh]
    [Algebra ((Spec (.of A)).presheaf.stalk basePoint) Rsh]
    [Algebra A Rsh] [IsScalarTower A ((Spec (.of A)).presheaf.stalk basePoint) Rsh]
    (hRsh : Stacks.StrictHenselization.IsStrictHenselization
      ((Spec (.of A)).presheaf.stalk basePoint) κ Rsh)
    (prime : Ideal Rsh) [prime.IsPrime] (hprime : prime ∈ minimalPrimes Rsh)
    (K : Type u) [Field K] [Algebra prime.ResidueField K]
    [IsAlgClosure prime.ResidueField K] :
    separableDegreeWeightedFiberSum
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (fun point => (genericSeparableDegree
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) hY point : ℤ)) basePoint =
      (Nat.card ((prime.ResidueField ⊗[A] B) →ₐ[prime.ResidueField] K) : ℤ) := by
  classical
  let := hRsh.isLocalHom
  let := isSepClosure_residueField_of_strictHenselization
    ((Spec (.of A)).presheaf.stalk basePoint) κ Rsh hRsh
  let : IsSepClosed (ResidueField Rsh) :=
    IsSepClosure.sep_closed (ResidueField ((Spec (.of A)).presheaf.stalk basePoint))
  have hind : StacksDraft.IndEtale A Rsh :=
    StacksDraft.indEtale_comp (StacksDraft.indEtale_atPrime basePoint.asIdeal)
      hRsh.isFilteredColimitEtale
  obtain ⟨index, _, factors, _, _, _, hfinite, equiv, hindFactors⟩ :=
    exists_henselianLocalFactors_indEtale Rsh hind B
  let : ∀ element, Module.Finite Rsh (factors element) := hfinite
  let tensor := Rsh ⊗[A] B
  let original := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let projection := Spec.map (CommRingCat.ofHom (algebraMap Rsh tensor))
  let inclusion := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] tensor).toRingHom)
  let baseMap := Spec.map (CommRingCat.ofHom (algebraMap A Rsh))
  have hsquare : IsPullback inclusion projection original baseMap :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct A Rsh B)).flip
  have hclosed : baseMap (closedPoint Rsh) = basePoint := by
    apply PrimeSpectrum.ext
    show (maximalIdeal Rsh).comap (algebraMap A Rsh) = basePoint.asIdeal
    rw [IsScalarTower.algebraMap_eq A ((Spec (.of A)).presheaf.stalk basePoint) Rsh,
      ← Ideal.comap_comap, maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal
      ((Spec (.of A)).presheaf.stalk basePoint) basePoint.asIdeal
  have hsum := congrFun (separableDegreeWeightedFiberSum_comp_of_isPullback
    original inclusion projection baseMap hsquare original.finite_preimage_singleton
    (fun point => (genericSeparableDegree original hY point : ℤ))) (closedPoint Rsh)
  change separableDegreeWeightedFiberSum original _
    (baseMap (closedPoint Rsh)) = _ at hsum
  rw [hclosed] at hsum
  rw [hsum, weightedFiberSum_of_finite_pi Rsh factors tensor equiv]
  have hdegree (element : index) :
      genericSeparableDegree original hY
        (inclusion (PrimeSpectrum.comap
          (((Pi.evalAlgHom Rsh factors element).comp equiv.toAlgHom).toRingHom)
          (closedPoint (factors element)))) =
        Nat.card ((prime.ResidueField ⊗[Rsh] factors element) →ₐ[prime.ResidueField] K) := by
    let factor := factors element
    let factorProjection := (Pi.evalAlgHom Rsh factors element).comp equiv.toAlgHom
    let : Algebra B factor := (factorProjection.toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
    let : Algebra A factor := ((algebraMap Rsh factor).comp (algebraMap A Rsh)).toAlgebra
    let : IsScalarTower A Rsh factor := .of_algebraMap_eq' rfl
    let : Algebra ((Spec (.of A)).presheaf.stalk basePoint) factor :=
      ((algebraMap Rsh factor).comp
        (algebraMap ((Spec (.of A)).presheaf.stalk basePoint) Rsh)).toAlgebra
    let : IsScalarTower ((Spec (.of A)).presheaf.stalk basePoint) Rsh factor :=
      .of_algebraMap_eq' rfl
    let : IsScalarTower A ((Spec (.of A)).presheaf.stalk basePoint) factor :=
      IsScalarTower.to₁₂₄ A ((Spec (.of A)).presheaf.stalk basePoint) Rsh factor
    let : IsScalarTower A B factor := .of_algebraMap_eq fun value => by
      show algebraMap Rsh factor (algebraMap A Rsh value) =
        factorProjection (Algebra.TensorProduct.includeRight (algebraMap A B value))
      rw [Algebra.TensorProduct.includeRight.commutes]
      exact (factorProjection.commutes (algebraMap A Rsh value)).symm
    let point : PrimeSpectrum B :=
      ⟨(maximalIdeal factor).comap (algebraMap B factor), Ideal.comap_isPrime _ _⟩
    have hover : original point = basePoint := by
      apply PrimeSpectrum.ext
      show ((maximalIdeal factor).comap (algebraMap B factor)).comap
        (algebraMap A B) = basePoint.asIdeal
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A Rsh factor, ← Ideal.comap_comap]
      have hmax : (maximalIdeal factor).comap (algebraMap Rsh factor) =
          maximalIdeal Rsh := eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rsh) (maximalIdeal factor))
      rw [hmax]
      exact congrArg PrimeSpectrum.asIdeal hclosed
    show genericSeparableDegree original hY point = _
    dsimp only [original] at hover
    cases hover
    exact genericSeparableDegree_eq_of_affine_factor A B hY point κ Rsh hRsh
      factor rfl (hindFactors element) prime hprime K
  show (∑ element, (genericSeparableDegree original hY
    (inclusion (PrimeSpectrum.comap _ (closedPoint (factors element)))) : ℤ)) = _
  simp_rw [hdegree]
  rw [← Nat.cast_sum]
  apply congrArg (fun value : ℕ => (value : ℤ))
  calc
    (∑ element, Nat.card ((prime.ResidueField ⊗[Rsh] factors element)
      →ₐ[prime.ResidueField] K)) =
        Nat.card ((prime.ResidueField ⊗[Rsh] tensor) →ₐ[prime.ResidueField] K) := by
      rw [algHom_card_eq_of_algEquiv prime.ResidueField _ _ K
        (Algebra.TensorProduct.congr (AlgEquiv.refl : prime.ResidueField ≃ₐ[prime.ResidueField]
          prime.ResidueField) equiv)]
      exact (algHom_card_tensorProduct_pi Rsh prime.ResidueField K factors).symm
    _ = Nat.card ((prime.ResidueField ⊗[A] B) →ₐ[prime.ResidueField] K) :=
      algHom_card_eq_of_algEquiv prime.ResidueField _ _ K
        (Algebra.TensorProduct.cancelBaseChange A Rsh prime.ResidueField prime.ResidueField B)

end AlgebraicGeometry
