module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange.LocalStructure
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationIndependence

/-!
# Arbitrary base change for the dualizing module: localizing the target

For a finite open factorization `F` of `A → B` and `e : B`, this part constructs the finite open
factorization `targetAwayFactorization F e` of `A → B_e`, identifies its dualizing module with
`B_e ⊗_B ω_{B/A}` (`targetAwayDualizingEquiv`) and computes `baseChangeLinearMap` through that
identification. It also proves the auxiliary facts on finite factorizations used for the finite
projective target case: integral open embeddings of spectra have clopen image, maps of spectra
that are open embeddings and bijective on basic opens are open immersions, and for a finite open
factorization of a finite algebra the middle ring maps onto the target, which is finitely
presented over it when the algebra is projective.

## References

* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section


open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open Topology CategoryTheory Opposite AlgebraicGeometry

/-! An integral open embedding has clopen image on prime spectra. -/

private lemma isClopen_range_of_isOpenEmbedding_integral
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap f)) (hint : f.IsIntegral) :
    IsClopen (Set.range (PrimeSpectrum.comap f)) := by
  exact ⟨(PrimeSpectrum.isClosedMap_comap_of_isIntegral f hint).isClosed_range,
    hopen.isOpen_range⟩

private lemma finite_open_component_range_isClopen
    {R S D : Type*} [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] (F : FiniteOpenFactorization R S)
    [Algebra F.middle D] [Module.Finite F.middle D]
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap (algebraMap F.middle D))) :
    IsClopen (Set.range (PrimeSpectrum.comap (algebraMap F.middle D))) := by
  have hint : (algebraMap F.middle D).IsIntegral := by
    exact (algebraMap_isIntegral_iff).mpr (Algebra.IsIntegral.of_finite F.middle D)
  exact isClopen_range_of_isOpenEmbedding_integral (algebraMap F.middle D) hopen hint

private theorem specMap_isOpenImmersion_of_openEmbedding_awayMap
    {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D)
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap f))
    (haway : ∀ g : C,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap f) →
      Function.Bijective (Localization.awayMap f g)) :
    IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := by
  classical
  let schemeMap := AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)
  apply IsOpenImmersion.of_forall_source_exists schemeMap
    (fun x y hxy => hopen.injective hxy)
  intro q
  let p := PrimeSpectrum.comap f q
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hp, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ Set.range (PrimeSpectrum.comap f) from ⟨q, rfl⟩)
      hopen.isOpen_range
  have hfg : f g ∉ q.asIdeal := hp
  let Cg := Localization.Away g
  let Dg := Localization.Away (f g)
  let iC : C →+* Cg := algebraMap C Cg
  let iD : D →+* Dg := algebraMap D Dg
  have hCopen : IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iC)) :=
    IsOpenImmersion.of_isLocalization g
  have hDopen : IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD)) :=
    IsOpenImmersion.of_isLocalization (f g)
  have hsq : AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD) ≫ schemeMap =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Localization.awayMap f g)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom iC) := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext x
    show algebraMap D Dg (f x) =
      Localization.awayMap f g (algebraMap C Cg x)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hawayIso : IsIso (CommRingCat.ofHom (Localization.awayMap f g)) := by
    let e := RingEquiv.ofBijective (Localization.awayMap f g) (haway g hg)
    exact e.toCommRingCatIso.isIso_hom
  have hcomp : IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD) ≫ schemeMap) := by
    rw [hsq]
    infer_instance
  have hq : q ∈ (AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD)).opensRange := by
    show q ∈ Set.range (PrimeSpectrum.comap iD)
    rw [PrimeSpectrum.localization_away_comap_range Dg (f g)]
    exact hfg
  exact ⟨Scheme.Spec.obj (op (CommRingCat.of Dg)),
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom iD), hDopen, hq, hcomp⟩

private theorem specMap_isOpenImmersion_of_openEmbedding_awayMap_universes
    {C : Type u} {D : Type v} [CommRing C] [CommRing D] (f : C →+* D)
    (hopen : IsOpenEmbedding (PrimeSpectrum.comap f))
    (haway : ∀ g : C,
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap f) →
      Function.Bijective (Localization.awayMap f g)) :
    IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (RingHom.ulift.{max u v, max u v} f))) := by
  let C' := ULift.{max u v} C
  let D' := ULift.{max u v} D
  let eC : C' ≃+* C := ULift.ringEquiv
  let eD : D' ≃+* D := ULift.ringEquiv
  let f' : C' →+* D' := RingHom.ulift.{max u v, max u v} f
  let HC := PrimeSpectrum.homeomorphOfRingEquiv eC
  let HD := PrimeSpectrum.homeomorphOfRingEquiv eD
  have hring : f'.comp eC.symm.toRingHom = eD.symm.toRingHom.comp f := by
    ext x
    rfl
  have hcomp : HC ∘ PrimeSpectrum.comap f' = PrimeSpectrum.comap f ∘ HD := by
    funext q
    show PrimeSpectrum.comap (f'.comp eC.symm.toRingHom) q =
      PrimeSpectrum.comap (eD.symm.toRingHom.comp f) q
    rw [hring]
  have hopen' : IsOpenEmbedding (PrimeSpectrum.comap f') := by
    have hmap : PrimeSpectrum.comap f' = (HC.symm :
        PrimeSpectrum C ≃ₜ PrimeSpectrum C') ∘ PrimeSpectrum.comap f ∘ HD := by
      funext q
      apply HC.injective
      simpa [Function.comp_apply] using congrFun hcomp q
    rw [hmap]
    exact HC.symm.isOpenEmbedding.comp (hopen.comp HD.isOpenEmbedding)
  have haway' (g : C')
      (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C')) ⊆
        Set.range (PrimeSpectrum.comap f')) :
      Function.Bijective (Localization.awayMap f' g) := by
    let c := eC g
    have hc : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum C)) ⊆
        Set.range (PrimeSpectrum.comap f) := by
      intro q hq
      have hq' : HC.symm q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum C')) := by
        show g ∉ Ideal.comap eC.toRingHom q.asIdeal
        change c ∉ q.asIdeal at hq
        simpa [c, Ideal.mem_comap] using hq
      obtain ⟨r, hr⟩ := hg hq'
      refine ⟨HD r, ?_⟩
      exact (congrFun hcomp r).symm.trans (congrArg HC hr)
    have hCpow : (Submonoid.powers g).map eC.toMonoidHom = Submonoid.powers c := by
      simpa [c] using Submonoid.map_powers eC.toMonoidHom g
    have hDpow : (Submonoid.powers (f' g)).map eD.toMonoidHom =
        Submonoid.powers (f c) := by
      rw [Submonoid.map_powers]
      rfl
    let eCLoc := IsLocalization.ringEquivOfRingEquiv
      (Localization.Away g) (Localization.Away c) eC hCpow
    let eDLoc := IsLocalization.ringEquivOfRingEquiv
      (Localization.Away (f' g)) (Localization.Away (f c)) eD hDpow
    have hnat : eDLoc.toRingHom.comp (Localization.awayMap f' g) =
        (Localization.awayMap f c).comp eCLoc.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext x
      simp [eCLoc, eDLoc, IsLocalization.ringEquivOfRingEquiv_eq,
        Localization.awayMap, IsLocalization.Away.map, RingHom.ulift_apply,
        eC, eD, f']
      rfl
    have hb := haway c hc
    constructor
    · intro x y hxy
      apply eCLoc.injective
      apply hb.1
      calc
        Localization.awayMap f c (eCLoc x) = eDLoc (Localization.awayMap f' g x) :=
          (congrFun (congrArg DFunLike.coe hnat) x).symm
        _ = eDLoc (Localization.awayMap f' g y) := congrArg eDLoc hxy
        _ = Localization.awayMap f c (eCLoc y) :=
          congrFun (congrArg DFunLike.coe hnat) y
    · intro y
      obtain ⟨x, hx⟩ := hb.2 (eDLoc y)
      refine ⟨eCLoc.symm x, ?_⟩
      apply eDLoc.injective
      calc
        eDLoc (Localization.awayMap f' g (eCLoc.symm x)) =
            Localization.awayMap f c (eCLoc (eCLoc.symm x)) :=
          congrFun (congrArg DFunLike.coe hnat) _
        _ = Localization.awayMap f c x := by simp
        _ = eDLoc y := hx
  exact specMap_isOpenImmersion_of_openEmbedding_awayMap f' hopen' haway'

private theorem awayMap_bijective_of_isOpenImmersion
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))]
    (g : R) (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap f)) :
    Function.Bijective (Localization.awayMap f g) := by
  let i := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap S (Localization.Away (f g))))
  let j := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  let k := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (Localization.awayMap f g))
  have : IsOpenImmersion i := IsOpenImmersion.of_isLocalization (f g)
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  have hi : i ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) = k ≫ j := by
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  have : IsOpenImmersion (k ≫ j) := hi ▸ inferInstance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  apply (isIso_SpecMap_iff
    (f := CommRingCat.ofHom (Localization.awayMap f g))).mp
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top k
  apply TopologicalSpace.Opens.ext
  show Set.range (PrimeSpectrum.comap (Localization.awayMap f g)) = Set.univ
  apply Set.eq_univ_of_forall
  intro p
  have hp : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) p ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact Set.mem_range_self p
  obtain ⟨q, hq⟩ := hg hp
  have hqg : q ∈ (PrimeSpectrum.basicOpen (f g) : Set (PrimeSpectrum S)) := by
    show g ∉ (PrimeSpectrum.comap f q).asIdeal
    rw [hq]
    exact hp
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (f g)) (f g)] at hqg
  obtain ⟨Q, rfl⟩ := hqg
  refine ⟨Q, ?_⟩
  apply (show Function.Injective j from j.isOpenEmbedding.injective)
  show (k ≫ j) Q = j p
  rw [← hi]
  exact hq

noncomputable def targetAwayFactorization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) (e : S) :
    FiniteOpenFactorization.{u, v, w} R (Localization.Away e) := by
  let D := Localization.Away e
  letI : CommRing F.middle := F.commRingMiddle
  letI : Algebra R F.middle := F.algebraMiddle
  letI : Algebra F.middle S := F.algebraTarget
  letI : IsScalarTower R F.middle S := F.scalarTower
  letI : Algebra S D := inferInstance
  letI : Algebra R D := inferInstance
  letI : Algebra F.middle D := inferInstance
  letI : IsScalarTower R S D := inferInstance
  letI : IsScalarTower F.middle S D := inferInstance
  letI : IsScalarTower R F.middle D := by
    apply IsScalarTower.of_algebraMap_eq (fun r => ?_)
    calc
      algebraMap R D r = algebraMap S D (algebraMap R S r) :=
        IsScalarTower.algebraMap_apply R S D r
      _ = algebraMap S D (algebraMap F.middle S (algebraMap R F.middle r)) := by
        rw [IsScalarTower.algebraMap_apply R F.middle S r]
      _ = algebraMap F.middle D (algebraMap R F.middle r) :=
        (IsScalarTower.algebraMap_apply F.middle S D _).symm
  have hmap : algebraMap F.middle D =
      (algebraMap S D).comp (algebraMap F.middle S) := by
    ext c
    exact (IsScalarTower.algebraMap_apply F.middle S D c).symm
  refine ⟨F.middle, F.commRingMiddle, F.algebraMiddle,
    inferInstance, inferInstance, F.finite_middle, ?_, ?_⟩
  · change IsOpenEmbedding (PrimeSpectrum.comap (algebraMap F.middle D))
    rw [hmap, PrimeSpectrum.comap_comp]
    exact F.isOpenEmbedding_comap.comp
      (PrimeSpectrum.localization_away_isOpenEmbedding D e)
  · intro g hg
    let f : F.middle →+* S := algebraMap F.middle S
    let fD : F.middle →+* D := algebraMap F.middle D
    let Sg := Localization.Away (f g)
    let Dg := Localization.Away (fD g)
    have hgS : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap f) := by
      intro p hp
      obtain ⟨q, hq⟩ := hg hp
      refine ⟨PrimeSpectrum.comap (algebraMap S D) q, ?_⟩
      change PrimeSpectrum.comap ((algebraMap S D).comp f) q = p
      rw [← hmap]
      exact hq
    have haway := F.awayMap_bijective g hgS
    have hincl : PrimeSpectrum.basicOpen (f g) ≤ PrimeSpectrum.basicOpen e := by
      intro q hq
      have hq' : (f g) ∉ q.asIdeal := by
        change q ∈ (PrimeSpectrum.basicOpen (f g) : Set (PrimeSpectrum S)) at hq
        exact hq
      have hqRange : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sg)) := by
        rw [PrimeSpectrum.localization_away_comap_range Sg (f g)]
        exact hq'
      obtain ⟨qg, hqg⟩ := hqRange
      let pCg : PrimeSpectrum (Localization.Away g) :=
        PrimeSpectrum.comap (Localization.awayMap f g)
          ⟨qg.asIdeal, by infer_instance⟩
      let pC : PrimeSpectrum F.middle :=
        PrimeSpectrum.comap (algebraMap F.middle (Localization.Away g)) pCg
      have hpCg : pC ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) := by
        rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
        exact ⟨pCg, rfl⟩
      obtain ⟨qD, hqD⟩ := hg hpCg
      let qS : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S D) qD
      have hcomp : PrimeSpectrum.comap f qS = pC := by
        change PrimeSpectrum.comap ((algebraMap S D).comp f) qD = pC
        rw [← hmap]
        exact hqD
      have hqS : qS = q := by
        apply F.isOpenEmbedding_comap.injective
        have hpC : pC = PrimeSpectrum.comap f q := by
          change PrimeSpectrum.comap
              ((Localization.awayMap f g).comp
                (algebraMap F.middle (Localization.Away g))) qg =
            PrimeSpectrum.comap f q
          rw [show (Localization.awayMap f g).comp
                (algebraMap F.middle (Localization.Away g)) =
              (algebraMap S Sg).comp f from by
                ext x
                change Localization.awayMap f g
                    (algebraMap F.middle (Localization.Away g) x) =
                  algebraMap S Sg (f x)
                rw [Localization.awayMap, IsLocalization.Away.map,
                  IsLocalization.map_eq]]
          rw [PrimeSpectrum.comap_comp]
          change PrimeSpectrum.comap f
              (PrimeSpectrum.comap (algebraMap S Sg) qg) = PrimeSpectrum.comap f q
          rw [hqg]
        exact hcomp.trans hpC
      have heq : e ∉ qS.asIdeal := by
        change algebraMap S D e ∉ qD.asIdeal
        apply Ideal.notMem_of_isUnit qD.asIdeal
        exact IsLocalization.Away.algebraMap_isUnit (R := S) (S := D) e
      simpa [qS, hqS, PrimeSpectrum.comap_asIdeal] using heq
    have hunit : IsUnit (algebraMap S Sg e) :=
      (@PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit S Sg
        inferInstance inferInstance (f g) e inferInstance inferInstance).1 hincl
    letI : Algebra Sg Dg :=
      Algebra.compHom Dg (Localization.awayMap (algebraMap S D) (f g))
    letI : IsScalarTower S Sg Dg := IsScalarTower.of_algebraMap_eq' (by
      ext r
      calc
        algebraMap S Dg r = algebraMap D Dg (algebraMap S D r) :=
          IsScalarTower.algebraMap_apply S D Dg r
        _ = Localization.awayMap (algebraMap S D) (f g)
            (algebraMap S (Localization.Away (f g)) r) := by
          rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
          rfl)
    haveI : IsLocalization.Away e D := inferInstance
    haveI : IsLocalization.Away (algebraMap S D (f g)) Dg := inferInstance
    letI : IsLocalization.Away (algebraMap S Sg e) Dg := by
      have hcomm := IsLocalization.Away.commutes Sg D Dg (f g) e
      simpa [Sg, Dg] using hcomm
    let eS : Sg ≃ₐ[Sg] Dg :=
      IsLocalization.atUnit Sg Dg (algebraMap S Sg e) hunit
    have hmaps : (eS.toRingEquiv : Sg ≃+* Dg).toRingHom.comp
        (Localization.awayMap f g) = Localization.awayMap fD g := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext c
      change eS (Localization.awayMap f g
          (algebraMap F.middle (Localization.Away g) c)) =
        Localization.awayMap fD g (algebraMap F.middle (Localization.Away g) c)
      rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      conv_rhs => rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rw [← IsScalarTower.algebraMap_apply F.middle S Sg c]
      change eS (algebraMap Sg Sg (algebraMap F.middle Sg c)) = _
      rw [eS.commutes]
      have hfD : fD c = algebraMap S D (f c) := by
        change algebraMap F.middle D c =
          algebraMap S D (algebraMap F.middle S c)
        exact congrArg (fun h : F.middle →+* D => h c) hmap
      rw [hfD]
      rw [← IsScalarTower.algebraMap_apply S D Dg (f c)]
      rw [IsScalarTower.algebraMap_apply S Sg Dg (f c)]
      rw [← IsScalarTower.algebraMap_apply F.middle S Sg c]
    have hbij : Function.Bijective
        ((eS.toRingEquiv : Sg ≃+* Dg).toRingHom.comp
          (Localization.awayMap f g)) := eS.bijective.comp haway
    rw [hmaps] at hbij
    exact hbij

noncomputable def targetAwayDualizingEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) (e : S) :
    let D := Localization.Away e
    letI : Algebra S D := inferInstance
    D ⊗[S] dualizingModule F ≃ₗ[D]
      dualizingModule (targetAwayFactorization F e) := by
  let D := Localization.Away e
  let C := F.middle
  let H := targetAwayFactorization F e
  letI : CommRing C := F.commRingMiddle
  letI : Algebra R C := F.algebraMiddle
  letI : Algebra C S := F.algebraTarget
  letI : IsScalarTower R C S := F.scalarTower
  letI : Algebra S D := inferInstance
  letI : Algebra C D := H.algebraTarget
  letI : IsScalarTower C S D := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  letI : Algebra D D := Algebra.id D
  let hCD : IsScalarTower C D D := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap C D c = algebraMap D D (algebraMap C D c)
    rfl)
  letI : IsScalarTower C D D := hCD
  letI : IsScalarTower S D D := IsScalarTower.of_algebraMap_eq' (by
    ext s
    simp)
  let M := Module.Dual R C
  letI : Module C M := algebraDualModule R C
  letI : AddCommGroup (dualizingModule F) :=
    dualizingModule.instAddCommGroup F
  letI : Module S (dualizingModule F) := dualizingModule.instModule F
  letI : AddCommGroup (dualizingModule H) :=
    dualizingModule.instAddCommGroup H
  letI : Module D (dualizingModule H) := dualizingModule.instModule H
  letI : Module S (M ⊗[C] S) := by
    change Module S (dualizingModule F)
    exact dualizingModule.instModule F
  let eDual : dualizingModule F ≃ₗ[S] M ⊗[C] S := by
    letI : Module S (S ⊗[C] M) := TensorProduct.leftModule
    let eAdd : dualizingModule F ≃+ (M ⊗[C] S) := {
      toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intro x y; rfl }
    exact eAdd.toLinearEquiv (by intro s m; rfl)
  let es := TensorProduct.comm C M S
  let eSwapRaw : (M ⊗[C] S) ≃ₗ[S] S ⊗[C] M :=
    es.toAddEquiv.toLinearEquiv (by
      intro s z
      change es.toAddEquiv (es.toAddEquiv.symm (s • es.toAddEquiv z)) = _
      exact es.toAddEquiv.apply_symm_apply _)
  let eSwap := eDual.trans eSwapRaw
  let eBase := eSwap.baseChange S D
  letI : Module D (D ⊗[C] M) := TensorProduct.leftModule
  letI : Module D (M ⊗[C] D) := by
    change Module D (dualizingModule H)
    exact dualizingModule.instModule H
  let eCancel := @TensorProduct.AlgebraTensorModule.cancelBaseChange
    C S D D M inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance hCD inferInstance
    inferInstance inferInstance inferInstance inferInstance
  let eComm := TensorProduct.comm C D M
  let eComm' : D ⊗[C] M ≃ₗ[D] dualizingModule H :=
    eComm.toAddEquiv.toLinearEquiv (by
      intro d z
      change eComm (d • z) = eComm (d • eComm.symm (eComm z))
      rw [eComm.symm_apply_apply])
  exact eBase.trans (eCancel.trans eComm')

theorem targetAwayDualizingEquiv_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) (e : S)
    (φ : Module.Dual R F.middle) (b : S) :
    targetAwayDualizingEquiv F e
        (1 ⊗ₜ[S] dualizingModule.tmul F φ b) =
      dualizingModule.tmul (targetAwayFactorization F e) φ
        (algebraMap S (Localization.Away e) b) := by
  let D := Localization.Away e
  let C := F.middle
  let H := targetAwayFactorization F e
  let : CommRing C := F.commRingMiddle
  let : Algebra R C := F.algebraMiddle
  let : Algebra C S := F.algebraTarget
  let : IsScalarTower R C S := F.scalarTower
  let : Algebra S D := inferInstance
  let : Algebra C D := H.algebraTarget
  let : IsScalarTower C S D := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  let : Algebra D D := Algebra.id D
  let hCD : IsScalarTower C D D := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap C D c = algebraMap D D (algebraMap C D c)
    rfl)
  let : IsScalarTower C D D := hCD
  let : IsScalarTower S D D := IsScalarTower.of_algebraMap_eq' (by
    ext s
    simp)
  let M := Module.Dual R C
  let : Module C M := algebraDualModule R C
  let : AddCommGroup (dualizingModule F) :=
    dualizingModule.instAddCommGroup F
  let : Module S (dualizingModule F) := dualizingModule.instModule F
  let : AddCommGroup (dualizingModule H) :=
    dualizingModule.instAddCommGroup H
  let : Module D (dualizingModule H) := dualizingModule.instModule H
  let : Module S (M ⊗[C] S) := by
    show Module S (dualizingModule F)
    exact dualizingModule.instModule F
  let eDual : dualizingModule F ≃ₗ[S] M ⊗[C] S := by
    let : Module S (S ⊗[C] M) := TensorProduct.leftModule
    let eAdd : dualizingModule F ≃+ (M ⊗[C] S) := {
      toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intro x y; rfl }
    exact eAdd.toLinearEquiv (by intro s m; rfl)
  let es := TensorProduct.comm C M S
  let eSwapRaw : (M ⊗[C] S) ≃ₗ[S] S ⊗[C] M :=
    es.toAddEquiv.toLinearEquiv (by
      intro s z
      show es.toAddEquiv (es.toAddEquiv.symm (s • es.toAddEquiv z)) = _
      exact es.toAddEquiv.apply_symm_apply _)
  let eSwap := eDual.trans eSwapRaw
  let eBase := eSwap.baseChange S D
  let : Module D (D ⊗[C] M) := TensorProduct.leftModule
  let : Module D (M ⊗[C] D) := by
    show Module D (dualizingModule H)
    exact dualizingModule.instModule H
  let eCancel := @TensorProduct.AlgebraTensorModule.cancelBaseChange
    C S D D M inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance hCD inferInstance
    inferInstance inferInstance inferInstance inferInstance
  let eComm := TensorProduct.comm C D M
  let eComm' : D ⊗[C] M ≃ₗ[D] dualizingModule H :=
    eComm.toAddEquiv.toLinearEquiv (by
      intro d z
      show eComm (d • z) = eComm (d • eComm.symm (eComm z))
      rw [eComm.symm_apply_apply])
  have hSwap : eSwap (dualizingModule.tmul F φ b) = b ⊗ₜ[C] φ := by
    show eSwapRaw (φ ⊗ₜ[C] b) = b ⊗ₜ[C] φ
    rfl
  have hBase : eBase (1 ⊗ₜ[S] dualizingModule.tmul F φ b) =
      1 ⊗ₜ[S] (b ⊗ₜ[C] φ) := by
    simp [eBase, LinearEquiv.baseChange_tmul, hSwap]
  have hCancel : eCancel (1 ⊗ₜ[S] (b ⊗ₜ[C] φ)) =
      (algebraMap S D b) ⊗ₜ[C] φ := by
    simpa [Algebra.smul_def] using
      (@TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
        C S D D M inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance inferInstance hCD
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (1 : D) φ b)
  show eComm' (eCancel (eBase
    (1 ⊗ₜ[S] dualizingModule.tmul F φ b))) = _
  rw [hBase, hCancel]
  rfl

private theorem baseChangeLinearMap_targetAway_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (e : A₁ ⊗[A] B) (φ : Module.Dual A F.middle) (b : B) :
    let B₁ := A₁ ⊗[A] B
    letI : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    targetAwayDualizingEquiv F₁ e
      (1 ⊗ₜ[B₁] baseChangeLinearMap F A₁
        (1 ⊗ₜ[B] dualizingModule.tmul F φ b)) =
      dualizingModule.tmul (targetAwayFactorization F₁ e)
        (Module.Dual.baseChange A₁ φ)
        (algebraMap B₁ (Localization.Away e) (1 ⊗ₜ[A] b)) := by
  let B₁ := A₁ ⊗[A] B
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  show targetAwayDualizingEquiv F₁ e
      (1 ⊗ₜ[B₁] baseChangeLinearMap F A₁
        (1 ⊗ₜ[B] dualizingModule.tmul F φ b)) = _
  rw [baseChangeLinearMap_one_tmul, dualizingModule.baseChange_tmul]
  exact targetAwayDualizingEquiv_tmul F₁ e (Module.Dual.baseChange A₁ φ)
    (1 ⊗ₜ[A] b)

/-- The universe-lifted map `F.middle → S` of a finite open factorization is an open
immersion on spectra. -/
private theorem factorization_ulift_isOpenImmersion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) :
    IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (RingHom.ulift.{max v w, max v w} (algebraMap F.middle S)))) :=
  specMap_isOpenImmersion_of_openEmbedding_awayMap_universes _
    F.isOpenEmbedding_comap F.awayMap_bijective

/-- A ring map whose induced map on spectra is an open immersion is an epimorphism. -/
private theorem epi_of_isOpenImmersion_specMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))) :
    Epi (CommRingCat.ofHom f) :=
  (op_mono_iff _).mp ((Scheme.Spec).mono_of_mono_map (by simpa using h.mono))

private theorem surjective_of_finite_openImmersion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap R S)))) :
    Function.Surjective (algebraMap R S) := by
  have he : Epi (CommRingCat.ofHom (algebraMap R S)) := epi_of_isOpenImmersion_specMap _ h
  have hfinite : RingHom.Finite (algebraMap R S) := by
    rw [RingHom.finite_algebraMap]
    infer_instance
  exact (RingHom.surjective_iff_epi_and_finite).mpr ⟨he, hfinite⟩

private theorem finite_factorization_map_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) [Module.Finite R S] :
    Function.Surjective (algebraMap F.middle S) := by
  let : Module.Finite F.middle S := Module.Finite.of_restrictScalars_finite R F.middle S
  let C' := ULift.{max v w} F.middle
  let S' := ULift.{max v w} S
  let eC : C' ≃+* F.middle := ULift.ringEquiv
  let eS : S' ≃+* S := ULift.ringEquiv
  let f' : C' →+* S' := RingHom.ulift.{max v w, max v w} (algebraMap F.middle S)
  let : Algebra F.middle S' := ULift.algebra
  let : Algebra C' S' := Algebra.compHom S' eC.toRingHom
  let : Algebra C' F.middle := eC.toRingHom.toAlgebra
  let : Algebra C' S := Algebra.compHom S eC.toRingHom
  let : IsScalarTower C' F.middle S := IsScalarTower.of_algebraMap_eq'
    (Algebra.compHom_algebraMap_eq S eC.toRingHom)
  have : Module.Finite C' F.middle := RingEquiv.finite eC
  have : Module.Finite C' S := Module.Finite.trans F.middle S
  let eSlin : S' ≃ₗ[C'] S := {
    eS.toAddEquiv with
    map_smul' := by
      intro c s
      rfl }
  have hfinite' : Module.Finite C' S' := Module.Finite.equiv eSlin.symm
  have hopen := factorization_ulift_isOpenImmersion F
  have hf' : f' = algebraMap C' S' := by
    ext c
    rfl
  have hopen' : IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap C' S'))) := by
    rw [← hf']
    exact hopen
  have hs' : Function.Surjective (algebraMap C' S') :=
    @surjective_of_finite_openImmersion C' S' inferInstance inferInstance
      (Algebra.compHom S' eC.toRingHom) hfinite' hopen'
  rw [← hf'] at hs'
  intro s
  obtain ⟨c, hc⟩ := hs' (ULift.up s)
  exact ⟨c.down, congrArg ULift.down hc⟩

private lemma finite_openImmersion_is_idempotent_localization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : IsOpenImmersion (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap R S)))) :
    ∃ e : R, IsIdempotentElem e ∧ IsLocalization.Away (1 - e) S := by
  have hsurj := surjective_of_finite_openImmersion h
  obtain ⟨e, he, hker⟩ :=
    (AlgebraicGeometry.isOpenImmersion_SpecMap_iff_of_surjective
      (CommRingCat.ofHom (algebraMap R S)) hsurj).mp h
  refine ⟨e, he, ?_⟩
  apply IsLocalization.away_of_isIdempotentElem he.one_sub
  · convert hker using 1 <;> congr 1 <;> ring_nf
  · exact hsurj

lemma finite_factorization_middle_finitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) [Module.Finite R S]
    [Module.Projective R S] :
    Module.FinitePresentation F.middle S := by
  let : Module.Finite F.middle S := Module.Finite.of_restrictScalars_finite R F.middle S
  let f : F.middle →ₗ[F.middle] S := Algebra.linearMap F.middle S
  let fR := f.restrictScalars R
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := finite_factorization_map_surjective F y
    exact ⟨x, hx⟩
  obtain ⟨g, hg⟩ := fR.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let p : F.middle →ₗ[R] F.middle := LinearMap.id - g.comp fR
  have hpRange : p.range = fR.ker := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      show fR (p y) = 0
      have hy := LinearMap.congr_fun hg (fR y)
      change fR (g (fR y)) = fR y at hy
      show fR (y - g (fR y)) = 0
      rw [map_sub, hy]
      simp
    · intro x hx
      refine ⟨x, ?_⟩
      show p x = x
      simp [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hx]
  have hkerFin : Module.Finite R fR.ker := by
    rw [← hpRange]
    infer_instance
  have hfg : f.ker.FG := by
    have hkerFin' : Module.Finite R f.ker := by
      show Module.Finite R fR.ker
      exact hkerFin
    have : Module.Finite F.middle f.ker :=
      Module.Finite.of_restrictScalars_finite R F.middle f.ker
    exact Module.Finite.iff_fg.mp inferInstance
  exact (Module.FinitePresentation.fg_ker_iff f hsurj).mp hfg

/-! These bridge facts are reproved locally because the modules proving the statements of other
tags are not imported here. -/

theorem factorization_flat_bridge
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) : Module.Flat F.middle S := by
  let f : F.middle →+* S := algebraMap F.middle S
  have := factorization_ulift_isOpenImmersion F
  have hFlatRing : RingHom.Flat f.ulift.{max v w, max v w} :=
    (AlgebraicGeometry.Flat.SpecMap_iff
      (f := CommRingCat.ofHom f.ulift.{max v w, max v w})).mp inferInstance
  have hf : RingHom.Flat f := (RingHom.Flat.ulift_iff (f := f)).mp hFlatRing
  exact (RingHom.flat_algebraMap_iff (R := F.middle) (S := S)).mp hf

theorem factorization_epi_bridge
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S) : Algebra.IsEpi F.middle S := by
  have hEpi := epi_of_isOpenImmersion_specMap _ (factorization_ulift_isOpenImmersion F)
  let : Algebra (ULift.{max v w} F.middle) (ULift.{max v w} S) :=
    ULift.algebra' F.middle (ULift.{max v w} S)
  have hEpiAlg : Algebra.IsEpi (ULift.{max v w} F.middle) (ULift.{max v w} S) :=
    CommRingCat.epi_iff_epi.mp hEpi
  exact algebraEpi_of_ulift (R := F.middle) (S := S) hEpiAlg

end dualizingModule
end Stacks.Discriminant
