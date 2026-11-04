module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.UnramifiedCompletion
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unramifiedness and étaleness are detected on completions

Let `f : A → B` be a local homomorphism of Noetherian local rings that is essentially of finite
type. Then `f` is unramified, respectively étale, as a homomorphism of local rings exactly when
the induced homomorphism of completions at the maximal ideals is. For the completed homomorphism
the local notions moreover agree with the absolute ones: formally unramified agrees with
unramified, and étale as a local homomorphism agrees with étale as an algebra. In the étale case
the completion of the target is finite free of positive rank over the completion of the source.

## Main definitions

* `AdicCompletion.residueFieldCompletionEquiv` identifies the residue field of a Noetherian
  local ring with the residue field of its completion.

## Main results

* `Algebra.FormallyUnramified.map_maximalIdeal_of_isSeparable`: a formally unramified local
  algebra with separable residue field extension and Noetherian target extends the maximal
  ideal of the base to the maximal ideal of the target.
* `RingHom.formallyUnramified_iff_formallyUnramified_adicCompletion` and
  `RingHom.formallyUnramified_adicCompletion_iff_unramified_adicCompletion` are the three
  equivalent unramifiedness conditions.
* `RingHom.isEtaleLocalHom_iff_isEtaleLocalHom_adicCompletion` and
  `RingHom.isEtaleLocalHom_adicCompletion_iff_etale_adicCompletion` are the three equivalent
  étaleness conditions.
* `RingHom.exists_linearEquiv_fin_adicCompletion_of_isEtaleLocalHom`: the completed target of an
  étale local homomorphism is finite free of positive rank.

## Implementation notes

Unramifiedness of a homomorphism of local rings is `Algebra.FormallyUnramified` together with
`Algebra.EssFiniteType`; étaleness as a homomorphism of local rings is
`RingHom.IsEtaleLocalHom`. The absolute notions are `Algebra.Unramified` and `Algebra.Etale`.

Mathlib's `Algebra.FormallyUnramified.map_maximalIdeal` needs the essentially finite type
hypothesis, which is unavailable for the completions over one another; the replacement proved
here trades it for Noetherianness of the target and separability of the residue field
extension, and runs the Nakayama argument on `m_A B + m_B²` directly.

The finite free basis is obtained from `Module.free_of_flat_of_isLocalRing` and is not
canonical.

## References

* [Stacks Project, Tag 039I](https://stacks.math.columbia.edu/tag/039I)
* [Stacks Project, Tag 039M](https://stacks.math.columbia.edu/tag/039M)
-/

@[expose] public section

universe u v

open AdicCompletion IsLocalRing

namespace AdicCompletion

/-- The residue field of a Noetherian local ring agrees with the residue field of its
completion at the maximal ideal. -/
@[ega "0 7.6.10" "special case"]
noncomputable def residueFieldCompletionEquiv (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    ResidueField R ≃+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)

/-- The homomorphism induced by a local homomorphism of Noetherian local rings on the
completions at the maximal ideals is again local. -/
theorem isLocalHom_adicCompletionMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)) := by
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  have hcomp : fc.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp f :=
    adicCompletionMap_comp_algebraMap f _ _ _
  refine ((IsLocalRing.local_hom_TFAE fc).out 3 1).mp ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomp, ← Ideal.map_map]
  exact (Ideal.map_mono (map_maximalIdeal_le f)).trans
    (AdicCompletion.maximalIdeal_eq_map (R := B)).ge

/-- Completion is compatible with the induced maps of residue fields. -/
theorem residueField_adicCompletionMap_comp {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    letI : IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)) := isLocalHom_adicCompletionMap f
    (ResidueField.map (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
          (map_maximalIdeal_le f))).comp
        (ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) =
      (ResidueField.map (algebraMap B (AdicCompletion (maximalIdeal B) B))).comp
        (ResidueField.map f) := by
  have : IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
    (map_maximalIdeal_le f)) := isLocalHom_adicCompletionMap f
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := residue_surjective x
  simp only [RingHom.comp_apply, ResidueField.map_residue]
  exact congrArg (residue (AdicCompletion (maximalIdeal B) B)) <|
    RingHom.congr_fun
      (adicCompletionMap_comp_algebraMap f (maximalIdeal A) (maximalIdeal B)
        (map_maximalIdeal_le f)) a

/-- A local homomorphism of Noetherian local rings extends the maximal ideal of its source to
the maximal ideal of its target exactly when the induced homomorphism of completions does. -/
theorem map_maximalIdeal_adicCompletionMap_iff {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal A).map f = maximalIdeal B ↔
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
          (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) =
        maximalIdeal (AdicCompletion (maximalIdeal B) B) := by
  set aA : A →+* AdicCompletion (maximalIdeal A) A := algebraMap _ _
  set aB : B →+* AdicCompletion (maximalIdeal B) B := algebraMap _ _
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  have hc : fc.comp aA = aB.comp f := adicCompletionMap_comp_algebraMap f _ _ _
  have hm : ((maximalIdeal A).map aA).map fc = ((maximalIdeal A).map f).map aB := by
    rw [Ideal.map_map, hc, ← Ideal.map_map]
  have : Module.FaithfullyFlat B (AdicCompletion (maximalIdeal B) B) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson (maximalIdeal B)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  rw [AdicCompletion.maximalIdeal_eq_map, AdicCompletion.maximalIdeal_eq_map]
  exact ⟨fun h ↦ by rw [hm, h],
    fun h ↦ Ideal.map_injective_of_faithfullyFlat (by rwa [← hm])⟩

/-- The residue field extension of the completion of an essentially finite type local
homomorphism is again essentially of finite type. -/
theorem essFiniteType_residueField_adicCompletionMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType) :
    letI : IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)) := isLocalHom_adicCompletionMap f
    (ResidueField.map (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f))).EssFiniteType := by
  set eA := residueFieldCompletionEquiv A
  set eB := residueFieldCompletionEquiv B
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  have : IsLocalHom fc := isLocalHom_adicCompletionMap f
  have hsquare : (ResidueField.map fc).comp eA.toRingHom =
      eB.toRingHom.comp (ResidueField.map f) := residueField_adicCompletionMap_comp f
  refine RingHom.EssFiniteType.of_comp eA.toRingHom ?_
  rw [hsquare]
  exact (RingHom.EssFiniteType.residueFieldMap hft).comp
    (RingHom.FiniteType.of_surjective _ eB.surjective).essFiniteType

end AdicCompletion

namespace Algebra.FormallyUnramified

/-- A formally unramified local algebra over a local ring, with Noetherian target and separable
residue field extension, extends the maximal ideal of the base to the maximal ideal of the
target. Unlike `Algebra.FormallyUnramified.map_maximalIdeal` this does not need the algebra to
be essentially of finite type. -/
@[ega "IV 18.8.6" "special case"]
theorem map_maximalIdeal_of_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.FormallyUnramified R S]
    (hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S)) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  classical
  let : Algebra (ResidueField R) (S ⧸ maximalIdeal S) :=
    inferInstanceAs (Algebra (ResidueField R) (ResidueField S))
  have : Algebra.IsSeparable (ResidueField R) (ResidueField S) := hsep
  set mS := (maximalIdeal R).map (algebraMap R S)
  set K := mS ⊔ maximalIdeal S ^ 2 with hK
  set qD : S →+* S ⧸ K := Ideal.Quotient.mk K
  have hmS_le_n : mS ≤ maximalIdeal S := IsLocalRing.map_maximalIdeal_le (algebraMap R S)
  have hK_le_n : K ≤ maximalIdeal S := sup_le hmS_le_n (Ideal.pow_le_self two_ne_zero)
  have hm_le_Kcomap : maximalIdeal R ≤ K.comap (algebraMap R S) :=
    Ideal.map_le_iff_le_comap.mp le_sup_left
  let : Algebra (ResidueField R) (S ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap hm_le_Kcomap
  have : IsScalarTower R (ResidueField R) (S ⧸ K) :=
    IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  have hI2 : (maximalIdeal S).map qD ^ 2 = (⊥ : Ideal (S ⧸ K)) := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mk_eq_bot_of_le (I := maximalIdeal S ^ 2) (J := K) le_sup_right
  let e0 : ((S ⧸ K) ⧸ (maximalIdeal S).map qD) ≃ₐ[ResidueField R] ResidueField S := by
    refine AlgEquiv.ofRingEquiv
      (f := DoubleQuot.quotQuotEquivQuotOfLE (R := S) (I := K) (J := maximalIdeal S) hK_le_n)
      fun x ↦ ?_
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  have : Algebra.FormallyEtale (ResidueField R) (ResidueField S) :=
    Algebra.FormallyEtale.of_isSeparable (ResidueField R) (ResidueField S)
  obtain ⟨lift, hlift⟩ := (Algebra.FormallyEtale.comp_bijective (ResidueField R) (ResidueField S)
    ((maximalIdeal S).map qD) hI2).2 e0.symm.toAlgHom
  have : IsScalarTower R S (S ⧸ K) := IsScalarTower.of_algebraMap_eq' (by ext s; rfl)
  have heq : (IsScalarTower.toAlgHom R S (S ⧸ K)) =
      (lift.restrictScalars R).comp (Ideal.Quotient.mkₐ R (maximalIdeal S)) := by
    refine Algebra.FormallyUnramified.comp_injective ((maximalIdeal S).map qD)
      (by simp [hI2]) (AlgHom.ext fun x ↦ ?_)
    refine e0.injective ?_
    show e0 (Ideal.Quotient.mk ((maximalIdeal S).map qD) (qD x)) =
      e0 (Ideal.Quotient.mk _ ((lift.restrictScalars R) (residue S x)))
    rw [show e0 (Ideal.Quotient.mk ((maximalIdeal S).map qD) (qD x)) = residue S x from rfl,
      show Ideal.Quotient.mk ((maximalIdeal S).map qD)
          ((lift.restrictScalars R) (residue S x)) = e0.symm (residue S x) from by
      simpa using congrArg
        (fun g : ResidueField S →ₐ[ResidueField R] (S ⧸ K) ⧸ (maximalIdeal S).map qD =>
          g (residue S x)) hlift]
    simp
  have hn_le_K : maximalIdeal S ≤ K := fun x hx ↦ by
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    have hval := AlgHom.congr_fun heq x
    change qD x = (lift.restrictScalars R) (residue S x) at hval
    rwa [IsLocalRing.residue_eq_zero_iff x |>.mpr hx,
      _root_.map_zero (lift.restrictScalars R)] at hval
  have hn_le_sup : (maximalIdeal S : Submodule S S) ≤
      mS ⊔ maximalIdeal S • (maximalIdeal S : Submodule S S) := by
    simpa [hK, Ideal.smul_eq_mul, pow_two] using hn_le_K
  exact le_antisymm hmS_le_n
    (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian (maximalIdeal S))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hn_le_sup)

end Algebra.FormallyUnramified

namespace RingHom

/-- **Stacks Project, Tag 039I**, parts (1) and (2). An essentially finite type local
homomorphism of Noetherian local rings is formally unramified if and only if the induced
homomorphism of completions is. -/
@[stacks 039I "parts (1) and (2)", ega "IV 17.4.4" "f')"]
theorem formallyUnramified_iff_formallyUnramified_adicCompletion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType) :
    letI := f.toAlgebra
    Algebra.FormallyUnramified A B ↔
      (letI := (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
        (map_maximalIdeal_le f)).toAlgebra
       Algebra.FormallyUnramified
         (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B)) := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.EssFiniteType A B := hft
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  let : Algebra A (AdicCompletion (maximalIdeal A) A) :=
    (algebraMap A (AdicCompletion (maximalIdeal A) A)).toAlgebra
  let : Algebra B (AdicCompletion (maximalIdeal B) B) :=
    (algebraMap B (AdicCompletion (maximalIdeal B) B)).toAlgebra
  let : Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
    fc.toAlgebra
  have : IsLocalHom fc := AdicCompletion.isLocalHom_adicCompletionMap f
  set eA := AdicCompletion.residueFieldCompletionEquiv A
  set eB := AdicCompletion.residueFieldCompletionEquiv B
  have he : RingHom.comp
      (algebraMap (ResidueField (AdicCompletion (maximalIdeal A) A))
        (ResidueField (AdicCompletion (maximalIdeal B) B))) eA.toRingHom =
      eB.toRingHom.comp (algebraMap (ResidueField A) (ResidueField B)) := by
    show (ResidueField.map fc).comp eA.toRingHom = eB.toRingHom.comp (ResidueField.map f)
    exact AdicCompletion.residueField_adicCompletionMap_comp f
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hcrit := (Algebra.FormallyUnramified.iff_map_maximalIdeal_eq (R := A) (S := B)).mp h
    have : Algebra.IsSeparable (ResidueField (AdicCompletion (maximalIdeal A) A))
        (ResidueField (AdicCompletion (maximalIdeal B) B)) :=
      (Algebra.IsSeparable.iff_of_equiv_equiv eA eB he).mp hcrit.1
    have : Module.Finite (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) :=
      moduleFinite_adicCompletion_of_formallyUnramified f h hft
    exact Algebra.FormallyUnramified.of_map_maximalIdeal
      ((AdicCompletion.map_maximalIdeal_adicCompletionMap_iff f).mp hcrit.2)
  · have : Algebra.FormallyUnramified (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) := h
    have hsepC : Algebra.IsSeparable (ResidueField (AdicCompletion (maximalIdeal A) A))
        (ResidueField (AdicCompletion (maximalIdeal B) B)) := by
      have : Algebra.EssFiniteType (ResidueField (AdicCompletion (maximalIdeal A) A))
          (ResidueField (AdicCompletion (maximalIdeal B) B)) :=
        essFiniteType_algebraMap.mp
          (AdicCompletion.essFiniteType_residueField_adicCompletionMap f hft)
      exact Algebra.FormallyUnramified.isSeparable _ _
    exact (Algebra.FormallyUnramified.iff_map_maximalIdeal_eq (R := A) (S := B)).mpr
      ⟨(Algebra.IsSeparable.iff_of_equiv_equiv eA eB he).mpr hsepC,
        (AdicCompletion.map_maximalIdeal_adicCompletionMap_iff f).mpr
          (Algebra.FormallyUnramified.map_maximalIdeal_of_isSeparable
            (R := AdicCompletion (maximalIdeal A) A)
            (S := AdicCompletion (maximalIdeal B) B) hsepC)⟩

/-- **Stacks Project, Tag 039I**, parts (2) and (3). For the completion of an essentially finite
type local homomorphism of Noetherian local rings, formal unramifiedness and unramifiedness
agree. -/
@[stacks 039I "parts (2) and (3)"]
theorem formallyUnramified_adicCompletion_iff_unramified_adicCompletion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType) :
    letI := (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)).toAlgebra
    Algebra.FormallyUnramified
        (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) ↔
      Algebra.Unramified
        (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) := by
  let : Algebra A B := f.toAlgebra
  let : Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
    (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)).toAlgebra
  refine ⟨fun h ↦ ?_, fun h ↦ h.formallyUnramified⟩
  have hOrig := (formallyUnramified_iff_formallyUnramified_adicCompletion f hft).mpr h
  have : Algebra.FormallyUnramified A B := hOrig
  have : Module.Finite (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) :=
    moduleFinite_adicCompletion_of_formallyUnramified f hOrig hft
  exact ⟨h, inferInstance⟩

/-- **Stacks Project, Tag 039M**, parts (1) and (2). An essentially finite type local
homomorphism of Noetherian local rings is étale if and only if the induced homomorphism of
completions is étale. -/
@[stacks 039M "parts (1) and (2)", ega "IV 17.6.3" "a) <=> e)", sga "1 I 4.2" "special case"]
theorem isEtaleLocalHom_iff_isEtaleLocalHom_adicCompletion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType) :
    letI := AdicCompletion.isLocalHom_adicCompletionMap f
    IsEtaleLocalHom f ↔
      IsEtaleLocalHom
        (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) := by
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  have : IsLocalHom fc := AdicCompletion.isLocalHom_adicCompletionMap f
  let : Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
    fc.toAlgebra
  let : Algebra A B := f.toAlgebra
  show (f.Flat ∧ f.FormallyUnramified ∧ f.EssFiniteType) ↔
    (fc.Flat ∧ fc.FormallyUnramified ∧ fc.EssFiniteType)
  constructor
  · rintro ⟨hflat, hfu, _⟩
    have : Module.Finite (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) :=
      moduleFinite_adicCompletion_of_formallyUnramified f hfu hft
    exact ⟨(adicCompletionMap_flat_iff f).2 hflat,
      (formallyUnramified_iff_formallyUnramified_adicCompletion f hft).mp hfu,
      by change Algebra.EssFiniteType _ _; infer_instance⟩
  · rintro ⟨hflat, hfu, _⟩
    exact ⟨(adicCompletionMap_flat_iff f).1 hflat,
      (formallyUnramified_iff_formallyUnramified_adicCompletion f hft).mpr hfu, hft⟩

/-- **Stacks Project, Tag 039M**, parts (2) and (3). For the completion of an essentially finite
type local homomorphism of Noetherian local rings, étaleness as a homomorphism of local rings
agrees with étaleness as an algebra. -/
@[stacks 039M "parts (2) and (3)"]
theorem isEtaleLocalHom_adicCompletion_iff_etale_adicCompletion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hft : f.EssFiniteType) :
    letI := AdicCompletion.isLocalHom_adicCompletionMap f
    IsEtaleLocalHom
        (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) ↔
      (letI := (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
        (map_maximalIdeal_le f)).toAlgebra
       Algebra.Etale
         (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B)) := by
  set fc := adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)
  have : IsLocalHom fc := AdicCompletion.isLocalHom_adicCompletionMap f
  let : Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
    fc.toAlgebra
  let : Algebra A B := f.toAlgebra
  show (fc.Flat ∧ Algebra.FormallyUnramified _ _ ∧ Algebra.EssFiniteType _ _) ↔
    Algebra.Etale _ _
  constructor
  · rintro ⟨hflat, hfu, _⟩
    have : Module.Finite (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) :=
      moduleFinite_adicCompletion_of_formallyUnramified f
        ((formallyUnramified_iff_formallyUnramified_adicCompletion f hft).mpr hfu) hft
    have : Algebra.FinitePresentation (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Module.Flat (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B) := flat_algebraMap_iff.mp hflat
    exact Algebra.Etale.of_formallyUnramified_of_flat
  · intro h
    have : Algebra.Etale (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) := h
    have : Algebra.FiniteType (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) := inferInstance
    exact ⟨(Etale.iff_flat_and_formallyUnramified.mp (etale_algebraMap.mpr h)).1, inferInstance,
      Algebra.EssFiniteType.of_finiteType _ _⟩

/-- **Stacks Project, Tag 039M.** The completion of the target of an étale local homomorphism of
Noetherian local rings is a finite free module of positive rank over the completion of the
source. -/
@[stacks 039M "finite free conclusion", ega "IV 17.6.3" "e') freeness"]
theorem exists_linearEquiv_fin_adicCompletion_of_isEtaleLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hf : IsEtaleLocalHom f) :
    letI := (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)).toAlgebra
    ∃ n : ℕ, 0 < n ∧ Nonempty
      (AdicCompletion (maximalIdeal B) B ≃ₗ[AdicCompletion (maximalIdeal A) A]
        (Fin n → AdicCompletion (maximalIdeal A) A)) := by
  set Ac := AdicCompletion (maximalIdeal A) A
  set Bc := AdicCompletion (maximalIdeal B) B
  let : Algebra Ac Bc :=
    (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)).toAlgebra
  let : Algebra A B := f.toAlgebra
  have : Module.Finite Ac Bc :=
    moduleFinite_adicCompletion_of_formallyUnramified f hf.2.1 hf.2.2
  have : Module.Flat Ac Bc := flat_algebraMap_iff.mp ((adicCompletionMap_flat_iff f).2 hf.1)
  have : Module.Free Ac Bc := Module.free_of_flat_of_isLocalRing
  set b := Module.Free.chooseBasis Ac Bc with hb
  have : Nontrivial Bc := inferInstance
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex Ac Bc), Fintype.card_pos_iff.mpr
    inferInstance, ⟨?_⟩⟩
  exact ((b.reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex Ac Bc))).repr).trans
    (Finsupp.linearEquivFunOnFinite Ac Ac (Fin _))

end RingHom
