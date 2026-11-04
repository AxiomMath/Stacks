module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.StalkTorAmplitude
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.SingleOfCanonical
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FiniteTypeCriterion
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Localization
public import StacksFrontier.RingTheory.LocalCompleteIntersection.TorCriterion
public import StacksFrontier.RingTheory.PseudoCoherentMap.CompleteIntersection

/-!
# Complete intersections and finite Tor dimension for finite-type maps

Let `A` be a Noetherian ring and let `A → B` be of finite type such that the image of
`Spec B → Spec A` contains every closed point of `Spec A`.  Then `B` is a local complete
intersection and `B` has finite Tor dimension over `A` if and only if `A` is a local complete
intersection and `A → B` is a local complete intersection map.

This is the finite-type reformulation of the local criterion.  Finite Tor dimension of `B` over
`A` is a local condition on `Spec B`, and at a prime `𝔮` of `B` lying over `𝔭` it becomes
eventual vanishing of `Tor_j^{A_𝔭}(B_𝔮, κ(𝔭))`; the criterion for a local homomorphism then says
that `B_𝔮` and `A_𝔭` are complete intersections together with the completion map being a complete
intersection homomorphism.  The hypothesis on closed points is what upgrades the resulting
statement about the primes `𝔭` in the image to all of `Spec A`, and the local-completion criterion
for finite-type maps converts the family of complete intersection homomorphisms into the local
complete intersection property of `A → B`.  In the other direction finite Tor dimension comes
from a local complete intersection map being perfect.

## Main results

* `LocalCompleteIntersection.isLocalCompleteIntersectionRing_and_hasFiniteTorDimension_iff`: the
  equivalence.

## Implementation notes

The image condition says that every maximal ideal of `A` is the contraction of a prime ideal of
`B`.  Finite Tor dimension is evaluated on `B` as an `A`-module through the canonical derived
tensor product, which is the derived tensoring datum that `RingHom.IsLocalCompleteIntersection`
produces a perfect-complex certificate against.  The Noetherian property of `B` follows from the
finite-type hypothesis and is introduced where it is needed rather than assumed.

## References

* [Stacks Project, Tag 09QF](https://stacks.math.columbia.edu/tag/09QF)
-/

@[expose] public section

namespace LocalCompleteIntersection

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open IsLocalRing StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

private theorem hasTorAmplitude0DJF_of_isoComplex
    {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : K ≅ L) (a b : ℤ) (h : FaithfullyFlat.HasTorAmplitude K a b) :
    FaithfullyFlat.HasTorAmplitude L a b := fun M i hi =>
  (h M i hi).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      ((tensorRight (FaithfullyFlat.projResComplex M)).mapIso e)).symm

/-- Avramov's criterion for a finite-type map whose image on spectra contains all closed points
of the source. -/
@[stacks 09QF]
public theorem isLocalCompleteIntersectionRing_and_hasFiniteTorDimension_iff
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hf : f.FiniteType)
    (himage : ∀ (m : Ideal A), m.IsMaximal →
      ∃ q : Ideal B, q.IsPrime ∧ q.comap f = m) :
    (letI : Algebra A B := f.toAlgebra
     letI : Algebra.FiniteType A B := hf
     letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
     IsLocalCompleteIntersectionRing B ∧
       ModuleHasFiniteTorDimension
         (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
         (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A)
         (ModuleCat.of A B)) ↔
      (IsLocalCompleteIntersectionRing A ∧ f.IsLocalCompleteIntersection) := by
  classical
  let : Algebra A B := f.toAlgebra
  let : Algebra.FiniteType A B := hf
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hlocal : ∀ (q : Ideal B) [q.IsPrime],
      letI : q.LiesOver (q.comap f) := ⟨rfl⟩
      letI : Algebra (Localization.AtPrime (q.comap f)) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver (q.comap f) q
      (IsCompleteIntersectionRing (Localization.AtPrime q) ∧
          ∃ n : ℕ, ∀ j : ℕ, n < j →
            IsZero (((Tor (ModuleCat (Localization.AtPrime (q.comap f))) j).obj
              (ModuleCat.of (Localization.AtPrime (q.comap f)) (Localization.AtPrime q))).obj
              (ModuleCat.of (Localization.AtPrime (q.comap f))
                (ResidueField (Localization.AtPrime (q.comap f)))))) ↔
        (IsCompleteIntersectionRing (Localization.AtPrime (q.comap f)) ∧
          IsCompleteIntersectionHom
            (adicCompletionMap
              (Localization.localRingHom (q.comap f) q f rfl)
              (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f)))
              (IsLocalRing.maximalIdeal (Localization.AtPrime q))
              (IsLocalRing.map_maximalIdeal_le
                (Localization.localRingHom (q.comap f) q f rfl)))) := by
    intro q hq
    let p := q.comap f
    let : p.IsPrime := by infer_instance
    let : q.LiesOver p := ⟨rfl⟩
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let hloc := Localization.localRingHom p q f rfl
    let : IsLocalHom hloc := Localization.isLocalHom_localRingHom p q f rfl
    let : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    let : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
    exact isCompleteIntersectionRing_and_eventually_tor_isZero_iff hloc
  constructor
  · rintro ⟨hB, hfinite⟩
    obtain ⟨a, b, hcanonical⟩ : ∃ a b : ℤ,
        HasTorAmplitude
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
          (canonicalTensorComparison A)
          (canonicalTensorIsLeftDerived A)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)) a b := by
      simpa only [ModuleHasFiniteTorDimension, HasFiniteTorDimension] using hfinite
    let eSingle := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
      (ModuleCat.of A B)
    have hcanonicalQ : HasTorAmplitude
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
        (canonicalTensorComparison A)
        (canonicalTensorIsLeftDerived A)
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B))) a b :=
      (hasTorAmplitude_of_iso
        (derivedTensor := (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor)
        (comparison := canonicalTensorComparison A)
        (isLeftDerived := canonicalTensorIsLeftDerived A)
        eSingle.symm a b).mp hcanonical
    have hsingle := StacksDraft.TorAmplitude.hasTorAmplitude0DJF_single_of_canonical
      A (ModuleCat.of A B) a b hcanonicalQ
    let F := ModuleCat.restrictScalars (algebraMap A B)
    have : F.Additive := inferInstance
    have : PreservesFiniteLimits F := inferInstance
    have : PreservesFiniteColimits F := inferInstance
    let eSingleComplex := (F.mapCochainComplexSingleFunctor 0).app (ModuleCat.of B B)
    have hglobal : FaithfullyFlat.HasTorAmplitude
        ((CochainComplex.restrictScalars (algebraMap A B)).obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) a b := by
      have he :
          ((CochainComplex.restrictScalars (algebraMap A B)).obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) ≅
          (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B) := by
        change
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) ≅
          (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (F.obj (ModuleCat.of B B))
        exact eSingleComplex
      exact hasTorAmplitude0DJF_of_isoComplex he.symm a b hsingle
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
    have hlocalized :=
      (hasTorAmplitude_iff_localized_at_primes_iff_maximals
        A B K a b).1.mp hglobal
    have hlocalCriterion : ∀ (q : Ideal B) (hq : q.IsPrime),
        IsCompleteIntersectionRing (Localization.AtPrime (q.comap f)) ∧
          IsCompleteIntersectionHom
            (adicCompletionMap
              (Localization.localRingHom (q.comap f) q f rfl)
              (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap f)))
              (IsLocalRing.maximalIdeal (Localization.AtPrime q))
              (IsLocalRing.map_maximalIdeal_le
                (Localization.localRingHom (q.comap f) q f rfl))) := by
      intro q hq
      let : q.IsPrime := hq
      refine (hlocal q).mp ⟨hB q, ?_⟩
      let p := q.comap f
      let : p.IsPrime := by infer_instance
      let : q.LiesOver p := ⟨rfl⟩
      let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
        Localization.AtPrime.algebraOfLiesOver p q
      have hqAmp : HasTorAmplitudeAt A K q a b := hlocalized q
      let ext := ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q))
      let restr := ModuleCat.restrictScalars
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      have : ext.Additive :=
        (ModuleCat.extendRestrictScalarsAdj
          (algebraMap B (Localization.AtPrime q))).left_adjoint_additive
      have : restr.Additive := inferInstance
      let comp := CategoryTheory.Functor.comp ext restr
      let K' : HomologicalComplex (ModuleCat.{u} B) (ComplexShape.up ℤ) := K
      let eComp :=
        (CategoryTheory.Functor.mapHomologicalComplexCompIso
          (CategoryTheory.Iso.refl comp) (ComplexShape.up ℤ)).app K'
      let eSingle := (HomologicalComplex.singleMapHomologicalComplex
          comp (ComplexShape.up ℤ) 0).app (ModuleCat.of B B)
      let e := eComp ≪≫ eSingle
      have hqAmp' : FaithfullyFlat.HasTorAmplitude
          ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
            (comp.obj (ModuleCat.of B B))) a b := by
        change FaithfullyFlat.HasTorAmplitude
          ((CochainComplex.restrictScalars
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).obj
            ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b
          at hqAmp
        exact hasTorAmplitude0DJF_of_isoComplex e a b hqAmp
      let n : ℕ := max 0 (-a).toNat
      refine ⟨n, fun j hj => ?_⟩
      have hj' : -(j : ℤ) < a := by
        dsimp [n] at hj
        omega
      have hz := hqAmp' (ModuleCat.of (Localization.AtPrime p)
        (ResidueField (Localization.AtPrime p))) (-(j : ℤ)) (Or.inl hj')
      let eModule : (comp.obj (ModuleCat.of B B)) ≅
          ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q) := by
        let eExt : (ext.obj (ModuleCat.of B B)) ≅
            ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q) :=
          (LinearEquiv.trans
            (FaithfullyFlat.extendScalarsCarrierEquiv B (Localization.AtPrime q)
              (ModuleCat.of B B))
            (TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime q)
              (Localization.AtPrime q))).toModuleIso
        show restr.obj (ext.obj (ModuleCat.of B B)) ≅
          restr.obj (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))
        exact restr.mapIso eExt
      have hTor₁ : IsZero (((Tor (ModuleCat (Localization.AtPrime p)) j).obj
          (comp.obj (ModuleCat.of B B))).obj
          (ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)))) :=
        (FaithfullyFlat.derivedTensorHomologySingle₀Iso (comp.obj (ModuleCat.of B B))
          (ModuleCat.of (Localization.AtPrime p)
            (ResidueField (Localization.AtPrime p))) j).isZero_iff.mp hz
      let eTor := (Tor (ModuleCat (Localization.AtPrime p)) j).mapIso eModule
      exact (eTor.app (ModuleCat.of (Localization.AtPrime p)
        (ResidueField (Localization.AtPrime p)))).isZero_iff.mp hTor₁
    have hAmax : ∀ (m : Ideal A) (hm : m.IsMaximal),
        IsCompleteIntersectionRing (Localization.AtPrime m) := by
      intro m hm
      obtain ⟨q, hq, hqm⟩ := himage m hm
      subst m
      exact (hlocalCriterion q hq).1
    have hA :=
      (isLocalCompleteIntersectionRing_iff_localizationsAtMaximal A).2 hAmax
    refine ⟨hA, ?_⟩
    apply (isLocalCompleteIntersection_iff_forall_isCompleteIntersectionHom
      f hf).mpr
    intro q hq
    let p := q.comap f
    let : q.IsPrime := hq
    let : p.IsPrime := by infer_instance
    let : q.LiesOver p := ⟨rfl⟩
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let hloc := Localization.localRingHom p q f rfl
    let : IsLocalHom hloc := Localization.isLocalHom_localRingHom p q f rfl
    have hcomp := (hlocalCriterion q hq).2
    simpa only [p, hloc] using hcomp
  · rintro ⟨hA, hfLci⟩
    constructor
    · intro q hq
      let : q.IsPrime := hq
      have hcompletion :=
        (isLocalCompleteIntersection_iff_forall_isCompleteIntersectionHom f hf).mp hfLci q
      exact ((hlocal q).2 ⟨hA _, hcompletion⟩).1
    · exact (RingHom.IsLocalCompleteIntersection.isPerfectRingMap f hfLci
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
        (canonicalTensorComparison A)
        (canonicalTensorIsLeftDerived A)).2

end LocalCompleteIntersection

end
