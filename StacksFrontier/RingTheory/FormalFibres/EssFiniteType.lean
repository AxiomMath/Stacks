module

public import Mathlib
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.RegularRing.Defs

@[expose] public section

/-!
# Formal fibre properties for algebras essentially of finite type

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

0BIV.

## Tag 0BIV — Essentially finite-type algebras over rings with prescribed formal fibres

Let `P` be a property of maps from fields to Noetherian rings. If `P` is preserved by
finitely generated field extension, can be checked locally, ascends through regular maps, and
descends through faithfully flat maps, then every essentially finite-type algebra over a
`P`-ring is again a `P`-ring.

### Main definitions

There are no new definitions.

### Main results

* `isPRing_of_essFiniteType`: the `P`-ring property ascends along an essentially
  finite-type algebra.

### Implementation notes

The four hypotheses are the properties (A)--(D) from the source. Regularity in (C) is expressed
as flatness together with geometric regularity of every fibre. The universe-polymorphic notions
of formal fibres and `P`-rings are those introduced in Stacks Project, Tag 0BIT.

### References

* [Stacks Project, Tag 0BIV](https://stacks.math.columbia.edu/tag/0BIV)

-/

/-! ### Stacks Tag 0BIV -/

section

section

open IsLocalRing
open scoped TensorProduct

universe u v w x

private theorem holds_iff
    (P : RingMapProperty.{u, u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    P.Holds f ↔ P f := by
  show P (RingHom.ulift.{u, u} f) ↔ P f
  exact ⟨fun h ↦ P.respectsIso.2 _ (ULift.ringEquiv.symm : A ≃+* ULift.{u} A)
      (P.respectsIso.1 _ (ULift.ringEquiv : ULift.{u} B ≃+* B) h),
    fun h ↦ P.respectsIso.2 _ (ULift.ringEquiv : ULift.{u} A ≃+* A)
      (P.respectsIso.1 _ (ULift.ringEquiv.symm : B ≃+* ULift.{u} B) h)⟩

private abbrev FiniteFieldBaseChange (P : RingMapProperty.{u, u}) : Prop :=
  ∀ (k K A : Type (u)) [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [IsNoetherianRing A] [Algebra.EssFiniteType k K]
      [IsNoetherianRing (A ⊗[k] K)],
      P (algebraMap k A) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom

private theorem formalFibersHaveAt_of_flat_localHom
    (P : RingMapProperty.{u, u})
    (hC : RegularAscent.{u, u} P)
    (hD : FaithfullyFlatDescent.{u, u} P)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (hfibers : ∀ p : PrimeSpectrum A,
      P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))
    (hregular : ∀ q : PrimeSpectrum B,
      Algebra.IsGeometricallyRegular q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal B) B))) :
    FormalFibersHaveAt P A := by
  let g := adicCompletionMap (algebraMap A B)
    (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le (algebraMap A B))
  let : Algebra (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) := g.toAlgebra
  have : IsScalarTower A (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (RingHom.congr_fun
        (adicCompletionMap_comp_algebraMap (algebraMap A B)
          (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le (algebraMap A B))) a).symm
  have : Module.Flat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.flat_of_isNoetherian _
  have : Module.Flat B (AdicCompletion (maximalIdeal B) B) :=
    AdicCompletion.flat_of_isNoetherian _
  have hcomp := hC A B (AdicCompletion (maximalIdeal B) B) hfibers hregular
  have : Module.Flat (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) :=
    (adicCompletionMap_flat_iff (algebraMap A B)).mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : IsLocalHom
      (algebraMap (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B)) :=
    Stacks.FormalFibres.adicCompletionMap_isLocalHom (algebraMap A B)
  have : Module.FaithfullyFlat (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (Stacks.FormalFibres.formalFibersHaveAt_iff P A).mpr
    (hD A (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) hcomp)

private theorem fibersHave_baseChange
    (P : RingMapProperty.{u, u})
    (hA : FiniteFieldBaseChange P)
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsNoetherianRing T] [Algebra.EssFiniteType R S]
    (h : ∀ p : PrimeSpectrum R,
      P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber T))) :
    ∀ q : PrimeSpectrum S,
      P.Holds (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber (S ⊗[R] T))) := by
  intro q
  let p : PrimeSpectrum R := ⟨q.asIdeal.comap (algebraMap R S), inferInstance⟩
  let k := p.asIdeal.ResidueField
  let K := q.asIdeal.ResidueField
  let : Algebra k K :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl).toAlgebra
  let : Module k K := Algebra.toModule
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R K r = Ideal.ResidueField.map p.asIdeal q.asIdeal
      (algebraMap R S) rfl (algebraMap R k r)
    rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType R K := .comp R S K
  have : Algebra.EssFiniteType k K := .of_comp R k K
  let F := k ⊗[R] T
  have : IsNoetherianRing (T ⊗[R] k) := Algebra.EssFiniteType.isNoetherianRing T _
  have : IsNoetherianRing F := isNoetherianRing_of_ringEquiv (T ⊗[R] k)
    (Algebra.TensorProduct.comm R T k).toRingEquiv
  have : IsNoetherianRing (F ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing F _
  have hF : P (algebraMap k F) := (holds_iff P _).mp (h p)
  have hK := hA k K F hF
  let e₁ := (Algebra.TensorProduct.comm k F K).toRingEquiv
  let e₂ := (Algebra.TensorProduct.cancelBaseChange R k K K T).toRingEquiv
  let e₃ := (Algebra.TensorProduct.cancelBaseChange R S K K T).symm.toRingEquiv
  let e := e₁.trans (e₂.trans e₃)
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := k) (A := F) (B := K)).toRingHom =
      algebraMap K (q.asIdeal.Fiber (S ⊗[R] T)) := by
    refine RingHom.ext fun a => ?_
    show (Algebra.TensorProduct.cancelBaseChange R S K K T).symm
      ((Algebra.TensorProduct.cancelBaseChange R k K K T)
        ((Algebra.TensorProduct.comm k F K) (1 ⊗ₜ[k] a))) = _
    rw [Algebra.TensorProduct.comm_tmul]
    show (Algebra.TensorProduct.cancelBaseChange R S K K T).symm
      ((Algebra.TensorProduct.cancelBaseChange R k K K T)
        (a ⊗ₜ[k] ((1 : k) ⊗ₜ[R] (1 : T)))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl
  rw [holds_iff, ← he]
  exact P.respectsIso.1 _ e hK

-- The tensor product and its localizations carry several compatible scalar actions;
-- checking the resulting completion towers requires a larger elaboration budget.
private theorem formalFibersHaveAt_of_essFiniteType_local
    (P : RingMapProperty.{u, u})
    (hA : FiniteFieldBaseChange P) (hC : RegularAscent.{u, u} P)
    (hD : FaithfullyFlatDescent.{u, u} P)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.EssFiniteType R S]
    (hR : FormalFibersHaveAt P R) : FormalFibersHaveAt P S := by
  let T := AdicCompletion (maximalIdeal R) R
  let : Module.Flat R T := AdicCompletion.flat_of_isNoetherian _
  let : Module.FaithfullyFlat R T := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let B := S ⊗[R] T
  let : Algebra T B := Algebra.TensorProduct.rightAlgebra
  let e : (T ⊗[R] S) ≃ₐ[T] B :=
    { (Algebra.TensorProduct.comm R T S).toRingEquiv with
      commutes' := fun _ => rfl }
  have : Algebra.EssFiniteType T B :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing T B
  have hG : IsGRing B := isGRing_of_essFiniteType
    (isGRing_of_isPrecomplete_maximalIdeal T)
  have hB := fibersHave_baseChange P hA (R := R) (S := S) (T := T)
    ((Stacks.FormalFibres.formalFibersHaveAt_iff P R).mp hR)
  obtain ⟨q, hq⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := B))
    ⟨maximalIdeal S, inferInstance⟩
  let C := Localization.AtPrime q.asIdeal
  have : Module.Flat S C := Module.Flat.trans S B C
  have : IsLocalHom (algebraMap S C) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq S B C, ← Ideal.comap_comap]
    have hmax : (maximalIdeal C).comap (algebraMap B C) = q.asIdeal :=
      IsLocalization.AtPrime.under_maximalIdeal C q.asIdeal
    rw [hmax]
    exact congrArg PrimeSpectrum.asIdeal hq
  have hCfib : ∀ p : PrimeSpectrum S,
      P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)) :=
    hC S B C hB (Stacks.FormalFibres.isGeometricallyRegular_fiber_of_isLocalization
      q.asIdeal.primeCompl)
  have hreg := hG.2 q.asIdeal
  rw [isRegularRingHom_algebraMap_iff] at hreg
  exact formalFibersHaveAt_of_flat_localHom P hC hD (A := S) (B := C) hCfib
    (fun p => (hreg.2 p.asIdeal).2)

/-- Being a `P`-ring transports along a ring isomorphism. -/
private theorem isPRingAt_of_ringEquiv
    (P : RingMapProperty.{max u v w, max u v w x})
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : IsPRingAt.{u, max v w, x} P A) : IsPRingAt.{v, max u w, x} P B := by
  have := h.1
  refine ⟨isNoetherianRing_of_ringEquiv A e, fun q => ?_⟩
  let p : PrimeSpectrum A := ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩
  exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, v, w, x} P
    (Localization.localRingEquiv p.asIdeal q.asIdeal e rfl) (h.2 p)

private theorem isPRingAt_of_essFiniteType_same_universe
    (P : RingMapProperty.{u, u})
    (hA : FiniteFieldBaseChange P) (hC : RegularAscent.{u, u} P)
    (hD : FaithfullyFlatDescent.{u, u} P)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsPRingAt P R) :
    IsPRingAt P S := by
  have : IsNoetherianRing R := hR.1
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  refine ⟨inferInstance, fun q => ?_⟩
  let p : PrimeSpectrum R := ⟨q.asIdeal.under R, inferInstance⟩
  let A := Localization.AtPrime p.asIdeal
  let B := Localization.AtPrime q.asIdeal
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_comp R A B
  exact formalFibersHaveAt_of_essFiniteType_local P hA hC hD (R := A) (S := B) (hR.2 p)

/-- **Stacks 0BIV.** If a property of maps from fields to Noetherian rings satisfies
properties (A)--(D), then an essentially finite-type algebra over a `P`-ring is a `P`-ring. -/
@[stacks 0BIV, ega "IV 7.4.3" "(ii)", ega "IV 7.6.5"]
public theorem isPRing_of_essFiniteType
    (P : RingMapProperty.{max u v, max u v})
    (hA : ∀ (k K A : Type (max u v)) [Field k] [Field K] [CommRing A]
      [Algebra k K] [Algebra k A] [IsNoetherianRing A] [Algebra.EssFiniteType k K]
      [IsNoetherianRing (A ⊗[k] K)],
      P (algebraMap k A) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := K)).toRingHom)
    (_hB : ∀ (k A : Type (max u v)) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A],
      (∀ q : PrimeSpectrum A, P (algebraMap k (Localization.AtPrime q.asIdeal))) ↔
        P (algebraMap k A))
    (hC : ∀ (A B C : Type (max u v))
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C)))
    (hD : ∀ (A B C : Type (max u v))
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
      ∀ p : PrimeSpectrum A,
        P.Holds (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S]
    (hR : IsPRingAt.{u, v, v} P R) :
    IsPRingAt.{v, u, u} P S  := by
  let R' := ULift.{v} R
  let S' := ULift.{u} S
  let eR : R' ≃+* R := ULift.ringEquiv
  let eS : S' ≃+* S := ULift.ringEquiv
  let : Algebra R' S' := (RingHom.ulift.{v, u} (algebraMap R S)).toAlgebra
  have : Algebra.EssFiniteType R' S' := by
    show (RingHom.ulift.{v, u} (algebraMap R S)).EssFiniteType
    have hf : (algebraMap R S).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr inferInstance
    have hpre := (RingHom.FiniteType.of_surjective eR.toRingHom eR.surjective).essFiniteType
    have hpost :=
      (RingHom.FiniteType.of_surjective eS.symm.toRingHom eS.symm.surjective).essFiniteType
    exact (hpre.comp hf).comp hpost
  have hR' : IsPRingAt.{max u v, 0, 0} P R' :=
    isPRingAt_of_ringEquiv.{u, max u v, 0, 0} P eR.symm hR
  exact isPRingAt_of_ringEquiv.{max u v, v, 0, 0} P eS
    (isPRingAt_of_essFiniteType_same_universe P hA hC hD (R := R') (S := S') hR')

end

end

end
