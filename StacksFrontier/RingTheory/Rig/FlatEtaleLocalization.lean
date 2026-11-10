module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Flat.LocalBaseChange
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint.EtaleReduction
public import StacksFrontier.RingTheory.Rig.ClosedPoint.Regular
public import StacksFrontier.RingTheory.Rig.FlatDescent
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse

/-!
# Rig-flatness ascends in a flat square with étale reduction

Consider a commutative square of adic homomorphisms of topological finite type between Noetherian
weakly admissible topological rings
```
B ---β--> B'
↑         ↑
φ         φ'
|         |
A ---α--> A'
```
with `α` and `β` flat, and suppose that `α` is étale modulo an ideal of definition `I ⊆ A`.  Then
rig-flatness of `φ` forces rig-flatness of `φ'`.  The square is only required to commute, not to
be cartesian.

Rig-flatness of `φ'` is tested on the rig-closed primes of the completed principal localizations
of its target, which is the fourth condition of `Rig.naivelyRigFlat_tfae`.  A rig-closed prime
`q'` there is pushed down to the corresponding square of completed principal localizations, where
`Rig.exists_isClosedPointAwayFrom_completedAway_comap` produces the localizing element and
`Rig.rigPoint_relative_tfae` propagates rig-closedness along the two legs.  At that point
`Rig.map_comap_eq_map_of_rigPoint_of_etale_quotient` says the contraction of `q'` to the bottom
ring generates the maximal ideal upstairs, and the local criterion for flatness transports
flatness from the left leg — supplied by rig-flatness of `φ` — to the right leg.

## Main results

* `Rig.isRigFlat_of_flat_etale_square` — the ascent of rig-flatness.

The `WAdm^Noeth` bookkeeping that the ascent needs about completed principal localizations is
also stated for general use, since the same facts are what put the square of Stacks 0GGR's
fourth paragraph into `WAdm^Noeth`:

* `Rig.completedAway_weaklyAdmissible` — `R_{\{f\}}` is a weakly admissible topological ring.
* `Rig.completedAway_canonical_properties` — `R → R_{\{f\}}` is continuous, adic, topologically
  of finite type and flat, and `Localization.Away f` is dense in `R_{\{f\}}`.
* `Rig.completedAwayMap_properties` — `R_{\{f\}} → S_{\{hom f\}}` commutes with the structure
  maps, is adic on the nose, continuous and topologically of finite type.
* `Rig.exists_completedAwayMap_properties` — the same arrow, plus its flatness, delivered at a
  caller-chosen presentation of the target's ideal of definition and localizing element.
* `Rig.finiteType_isTopologicallyOfFiniteType` and
  `Rig.topologicallyOfFiniteType_of_dense_extension` — the two ways topological finite type is
  produced here.
* `Rig.completedHom_ext` — a continuous map out of `R_{\{f\}}` is determined by its restriction
  to `R`.

## Implementation notes

The étale reduction hypothesis is on the canonical map `A / I → A' / I A'`.  All four arrows are
required to be continuous, adic and topologically of finite type; the source arrow's adicness and
finite type are also part of its rig-flatness hypothesis and are passed separately so that the
lemma can be applied without destructuring it.

The four rings lie in a single universe.  That is the generality of the whole local-property
framework this feeds (`TopologicalRing.PropertyIsLocal` and everything built on it quantify over
`Type u`), and of the composition lemma
`TopologicalRing.isTopologicallyOfFiniteType_comp` used on the diagonal of the square.

The completion-comparison infrastructure — flatness of the induced maps of adic completions and
of principal localizations, density of a ring in its completion, and topological finite type of
the localized map — is shared with the descent lemma of Stacks 0GGT and imported from
`StacksFrontier.RingTheory.Rig.FlatDescent`.

## References

* [Stacks Project, Tag 0GGS](https://stacks.math.columbia.edu/tag/0GGS)
-/

@[expose] public section

namespace Rig


open Filter

open scoped TensorProduct
open scoped Topology
open CategoryTheory.Limits

universe u










/-- The map of principal localizations induced by `hom` carries the extended ideal of `ideal`
onto the extended ideal of `ideal.map hom`. -/
private lemma map_away_map_eq
    {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S) (ideal : Ideal R) (element : R) :
    (ideal.map (algebraMap R (Localization.Away element))).map
      (IsLocalization.Away.map (Localization.Away element) (Localization.Away (hom element))
        hom element) =
      (ideal.map hom).map (algebraMap S (Localization.Away (hom element))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext value
  simp [IsLocalization.Away.map]

private lemma completedAwayMap_flat
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (hom : R →+* S) (ideal : Ideal R) (element : R) (hflat : hom.Flat) :
    (RingHom.completedAwayMap hom ideal element).Flat := by
  let source := Localization.Away element
  let target := Localization.Away (hom element)
  let localized := IsLocalization.Away.map source target hom element
  let sourceIdeal := ideal.map (algebraMap R source)
  let targetIdeal := (ideal.map hom).map (algebraMap S target)
  have hmap : sourceIdeal.map localized = targetIdeal := map_away_map_eq hom ideal element
  let : Algebra source target := localized.toAlgebra
  exact flat_mapAdicCompletion_of_eq sourceIdeal targetIdeal hmap
    (flat_awayMap hom element hflat)

private lemma etale_of_etale_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (hom : R →+* S) (next : S →+* T) (hhom : hom.Etale)
    (hcomp : (next.comp hom).Etale) : next.Etale := by
  let : Algebra R S := hom.toAlgebra
  let : Algebra S T := next.toAlgebra
  let : Algebra R T := (next.comp hom).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale R S := hhom
  let : Algebra.Etale R T := hcomp
  exact Algebra.Etale.of_restrictScalars R S T

private lemma etale_quotient_of_commutative_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (hom : R →+* S) (hom' : R' →+* S') (source : R →+* R') (target : S →+* S')
    (hsquare : hom'.comp source = target.comp hom) (ideal : Ideal R)
    (hhom : (Ideal.quotientMap (ideal.map hom) hom Ideal.le_comap_map).Etale)
    (hsource : (Ideal.quotientMap (ideal.map source) source Ideal.le_comap_map).Etale)
    (htarget : (Ideal.quotientMap ((ideal.map hom).map target) target
      Ideal.le_comap_map).Etale) :
    (Ideal.quotientMap ((ideal.map source).map hom') hom' Ideal.le_comap_map).Etale := by
  have hmap : (ideal.map source).map hom' = (ideal.map hom).map target := by
    calc
      _ = ideal.map (hom'.comp source) := Ideal.map_map _ _
      _ = ideal.map (target.comp hom) := congrArg ideal.map hsquare
      _ = _ := (Ideal.map_map _ _).symm
  let quotientHom := Ideal.quotientMap (ideal.map hom) hom Ideal.le_comap_map
  let quotientSource := Ideal.quotientMap (ideal.map source) source Ideal.le_comap_map
  let quotientTarget := Ideal.quotientMap ((ideal.map hom).map target) target
    Ideal.le_comap_map
  let quotientHom' := Ideal.quotientMap ((ideal.map hom).map target) hom'
    (Ideal.map_le_iff_le_comap.mp hmap.le)
  have hquotSquare : quotientHom'.comp quotientSource = quotientTarget.comp quotientHom := by
    apply RingHom.ext
    intro value
    obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective value
    change Ideal.Quotient.mk _ (hom' (source representative)) =
      Ideal.Quotient.mk _ (target (hom representative))
    exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun hsquare representative)
  have hquot := etale_of_etale_comp quotientSource quotientHom' hsource (by
    rw [hquotSquare]
    exact StacksDraft.etale_comp quotientHom quotientTarget hhom htarget)
  let changeQuotient := Ideal.quotEquivOfEq hmap
  have hfinal := StacksDraft.etale_comp quotientHom' changeQuotient.symm.toRingHom hquot
    (RingHom.Etale.of_bijective changeQuotient.symm.bijective)
  convert hfinal using 1
  apply RingHom.ext
  intro value
  obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective value
  apply changeQuotient.injective
  change changeQuotient (Ideal.Quotient.mk _ (hom' representative)) =
    changeQuotient (changeQuotient.symm (Ideal.Quotient.mk _ (hom' representative)))
  simp only [changeQuotient, Ideal.quotEquivOfEq_mk, RingEquiv.apply_symm_apply]

private lemma etale_quotient_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (first : R →+* S) (second : S →+* T) (ideal : Ideal R)
    (hfirst : (Ideal.quotientMap (ideal.map first) first Ideal.le_comap_map).Etale)
    (hsecond : (Ideal.quotientMap ((ideal.map first).map second)
      second Ideal.le_comap_map).Etale) :
    (Ideal.quotientMap (ideal.map (second.comp first)) (second.comp first)
      Ideal.le_comap_map).Etale := by
  let firstQuot := Ideal.quotientMap (ideal.map first) first Ideal.le_comap_map
  let secondQuot := Ideal.quotientMap ((ideal.map first).map second) second Ideal.le_comap_map
  let changeQuotient := Ideal.quotEquivOfEq (Ideal.map_map (I := ideal) first second)
  have hfinal := StacksDraft.etale_comp (secondQuot.comp firstQuot) changeQuotient.toRingHom
    (StacksDraft.etale_comp firstQuot secondQuot hfirst hsecond)
    (RingHom.Etale.of_bijective changeQuotient.bijective)
  convert hfinal using 1
  apply RingHom.ext
  intro value
  obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective value
  rfl

private lemma kernel_eval
    {R : Type*} [CommRing R] [IsNoetherianRing R] (ideal : Ideal R) (index : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ ideal index).toRingHom =
      (ideal ^ index).map (algebraMap R (AdicCompletion ideal R)) := by
  ext value
  have he : AdicCompletion.evalₐ ideal index value = 0 ↔
      AdicCompletion.eval ideal R index value = 0 := by
    change (Ideal.quotientEquivAlgOfEq R
        (show (ideal ^ index • ⊤ : Ideal R) = ideal ^ index by simp))
      (AdicCompletion.eval ideal R index value) = 0 ↔ _
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  rw [RingHom.mem_ker]
  change AdicCompletion.evalₐ ideal index value = 0 ↔ _
  rw [he, ← LinearMap.mem_ker,
    ← AdicCompletion.pow_smul_top_eq_ker_eval ideal.fg_of_isNoetherianRing,
    Ideal.smul_top_eq_map]
  rfl
private lemma kernel_factor_eval
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (ideal quotientIdeal : Ideal R) (index : ℕ) (hpow : ideal ^ index ≤ quotientIdeal) :
    RingHom.ker ((Ideal.Quotient.factor hpow).comp
      (AdicCompletion.evalₐ ideal index).toRingHom) =
      quotientIdeal.map (algebraMap R (AdicCompletion ideal R)) := by
  let target := AdicCompletion ideal R
  let extended := quotientIdeal.map (algebraMap R target)
  let hom := (Ideal.Quotient.factor hpow).comp (AdicCompletion.evalₐ ideal index).toRingHom
  have hcomm : hom.comp (algebraMap R target) = Ideal.Quotient.mk quotientIdeal := by
    ext value
    change Ideal.Quotient.factor hpow
      (AdicCompletion.evalₐ ideal index (AdicCompletion.of ideal R value)) = _
    rw [AdicCompletion.evalₐ_of, Ideal.Quotient.factor_mk]
  have hker : RingHom.ker hom = extended := by
    apply le_antisymm
    · intro value hvalue
      obtain ⟨representative, hrepresentative⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ ideal index value)
      have hmem : representative ∈ quotientIdeal := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [← DFunLike.congr_fun hcomm representative]
        change hom (algebraMap R target representative) = 0
        change Ideal.Quotient.factor hpow (AdicCompletion.evalₐ ideal index
          (AdicCompletion.of ideal R representative)) = 0
        rw [AdicCompletion.evalₐ_of, hrepresentative]
        exact hvalue
      have hdiff : value - algebraMap R target representative ∈ RingHom.ker
          (AdicCompletion.evalₐ ideal index).toRingHom := by
        change AdicCompletion.evalₐ ideal index
          (value - AdicCompletion.of ideal R representative) = 0
        rw [map_sub, AdicCompletion.evalₐ_of, hrepresentative, sub_self]
      rw [kernel_eval] at hdiff
      exact (by
        have hd := Ideal.map_mono hpow hdiff
        have hr := Ideal.mem_map_of_mem (algebraMap R target) hmem
        convert extended.add_mem hd hr using 1
        ring)
    · apply Ideal.map_le_iff_le_comap.mpr
      intro value hvalue
      change hom (algebraMap R target value) = 0
      change (hom.comp (algebraMap R target)) value = 0
      rw [hcomm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hvalue
  exact hker

private noncomputable def quotientCompletionEquiv
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (ideal quotientIdeal : Ideal R) (index : ℕ) (hpow : ideal ^ index ≤ quotientIdeal) :
    (AdicCompletion ideal R ⧸ quotientIdeal.map (algebraMap R (AdicCompletion ideal R))) ≃+*
      (R ⧸ quotientIdeal) :=
  (Ideal.quotEquivOfEq (kernel_factor_eval ideal quotientIdeal index hpow).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((Ideal.Quotient.factor_surjective hpow).comp (AdicCompletion.surjective_evalₐ ideal index)))
private lemma quotientCompletionEquiv_apply_mk
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (ideal quotientIdeal : Ideal R) (index : ℕ) (hpow : ideal ^ index ≤ quotientIdeal)
    (value : AdicCompletion ideal R) :
    quotientCompletionEquiv ideal quotientIdeal index hpow (Ideal.Quotient.mk _ value) =
      Ideal.Quotient.factor hpow (AdicCompletion.evalₐ ideal index value) := by
  unfold quotientCompletionEquiv
  change RingHom.quotientKerEquivOfSurjective
    (f := (Ideal.Quotient.factor hpow).comp (AdicCompletion.evalₐ ideal index).toRingHom)
    ((Ideal.Quotient.factor_surjective hpow).comp (AdicCompletion.surjective_evalₐ ideal index))
    (Ideal.Quotient.mk (RingHom.ker ((Ideal.Quotient.factor hpow).comp
      (AdicCompletion.evalₐ ideal index).toRingHom)) value) = _
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

private lemma isAdic_map_of_isAdic_of_continuous
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ)
    (hφ_adic : _root_.RingHom.IsAdic φ)
    {I : Ideal A} (hI : IsAdic I) : IsAdic (I.map φ) := by
  rcases hφ_adic with ⟨J, hJ, hJφ⟩
  rcases isAdic_iff.mp hI with ⟨hIopen, hIcofinal⟩
  rcases isAdic_iff.mp hJ with ⟨hJopen, hJcofinal⟩
  have hIopen' : IsOpen (I : Set A) := by simpa using hIopen 1
  obtain ⟨n, hn⟩ := hJcofinal I (hIopen'.mem_nhds (Ideal.zero_mem I))
  have hnI : J ^ n ≤ I := fun x hx => hn hx
  have hpow : (J.map φ) ^ n ≤ I.map φ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_mono hnI
  rcases isAdic_iff.mp hJφ with ⟨hJφopen, hJφcofinal⟩
  refine isAdic_iff.mpr ⟨?_, ?_⟩
  · intro m
    have hpowm : (J.map φ) ^ (n * m) ≤ (I.map φ) ^ m :=
      (by rw [pow_mul]; exact Ideal.pow_right_mono hpow m)
    apply Ideal.isOpen_of_isOpen_subideal hpowm
    simpa [pow_mul] using hJφopen (n * m)
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := IsLinearTopology.hasBasis_ideal.mem_iff.mp hU
    have hpre : φ ⁻¹' (V : Set B) ∈ nhds (0 : A) := by
      have hV' : (V : Set B) ∈ nhds (φ 0) := by simpa only [RingHom.map_zero] using hV
      exact Filter.mem_map.mp (hφ.continuousAt hV')
    obtain ⟨m, hm⟩ := hIcofinal (φ ⁻¹' (V : Set B)) hpre
    have hmap : (I ^ m).map φ ≤ V := by
      rw [Ideal.map_le_iff_le_comap]
      exact fun x hx => hm hx
    have hpowm : (I.map φ) ^ m ≤ V := by
      rw [← Ideal.map_pow]
      exact hmap
    refine ⟨m, ?_⟩
    exact (SetLike.coe_subset_coe.mpr hpowm).trans hVU

private lemma adic_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [TopologicalSpace T] [IsTopologicalRing T] [IsLinearTopology T T]
    (first : R →+* S) (second : S →+* T)
    (hsecondCont : Continuous second)
    (hfirst : _root_.RingHom.IsAdic first)
    (hsecond : _root_.RingHom.IsAdic second) :
    _root_.RingHom.IsAdic (second.comp first) := by
  obtain ⟨ideal, hideal, hmap⟩ := hfirst
  exact ⟨ideal, hideal, by
    simpa only [Ideal.map_map] using
      isAdic_map_of_isAdic_of_continuous second hsecondCont hsecond hmap⟩

private lemma exists_pow_map_le_of_continuous_of_isAdic
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (hφ : Continuous φ)
    {I : Ideal A} (hI : IsAdic I) {J : Ideal B} (hJ : IsAdic J) :
    ∃ n : ℕ, (I ^ n).map φ ≤ J := by
  rcases isAdic_iff.mp hI with ⟨_, hIcofinal⟩
  have hJopen : IsOpen (J : Set B) := by
    simpa using (isAdic_iff.mp hJ).1 1
  have hpreopen : IsOpen (φ ⁻¹' (J : Set B)) := hφ.isOpen_preimage _ hJopen
  obtain ⟨n, hn⟩ := hIcofinal (φ ⁻¹' (J : Set B))
    (hpreopen.mem_nhds (by simp))
  refine ⟨n, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  exact fun x hx => hn hx

private lemma rigPointLocalCondition_of_closedPointAwayFrom_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsNoetherianRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (hI : ∃ I : Ideal R, IsAdic I)
    (q : Ideal R) [q.IsPrime]
  (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical R) q) :
  Ideal.IsRigPointLocalCondition q := by
  let : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := hR.2.1
  let : T2Space R := hR.2.2
  obtain ⟨I, hI⟩ := hI
  have hdef := isIdealOfDefinition_topologicalNilradical_of_isAdic I hI
  have hclosed : ∃ J : Ideal R, TopologicalRing.IsIdealOfDefinition J ∧
      Ideal.IsClosedPointAwayFrom J q := ⟨_, hdef, hq⟩
  exact ((rigPoint_tfae ⟨I, hI⟩ q).out 2 8).mp hclosed

private theorem flat_of_localFlatSquare
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R'] [IsNoetherianRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalHom (algebraMap R' S')]
    [Module.Flat R R'] [Module.Flat S S']
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R R') =
      IsLocalRing.maximalIdeal R')
    (hflat : Module.Flat R S) :
    _root_.RingHom.Flat (algebraMap R' S') := by
  let f : S →ₗ[S] S' := Algebra.linearMap S S'
  have hf : IsBaseChange S' f := IsBaseChange.linearMap S S'
  have hflat' : Module.Flat R' S' :=
    Module.Flat.baseChange_of_map_maximalIdeal_eq_maximalIdeal
      hmax f hf
  exact RingHom.flat_algebraMap_iff.mpr hflat'

/-- **Topological finite type passes to a densely extended arrow.**  Let `ψ ∘ g = k ∘ φ` be a
commuting square of ring homomorphisms whose two targets carry topologies.  If `φ` is
topologically of finite type and `k` is continuous with dense image, then so is `ψ`: the
polynomial presentation of `φ` is pushed along `g` and `k`, and its image stays dense because a
continuous map with dense image carries a dense set to a dense set. -/
public lemma topologicallyOfFiniteType_of_dense_extension
    {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [TopologicalSpace B] [TopologicalSpace D]
    (φ : A →+* B) (ψ : C →+* D) (g : A →+* C) (k : B →+* D)
    (hcomm : ψ.comp g = k.comp φ)
    (hφ : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hk_cont : Continuous k) (hk_dense : DenseRange k) :
    TopologicalRing.IsTopologicallyOfFiniteType ψ := by
  obtain ⟨n, p, hpconst, hpdense⟩ := hφ
  let : Algebra C D := ψ.toAlgebra
  let q : MvPolynomial (Fin n) C →ₐ[C] D :=
    MvPolynomial.aeval (fun i => k (p (MvPolynomial.X i)))
  let mapg : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C :=
    MvPolynomial.map g
  have hconst : q.toRingHom.comp MvPolynomial.C = ψ := by
    ext c
    change q (algebraMap C (MvPolynomial (Fin n) C) c) = ψ c
    rw [q.commutes]
    rfl
  have hpoly : q.toRingHom.comp mapg = k.comp p := by
    apply MvPolynomial.ringHom_ext'
    · ext a
      change q (MvPolynomial.map g (MvPolynomial.C a)) =
        k (p (MvPolynomial.C a))
      rw [MvPolynomial.map_C]
      calc
        q (MvPolynomial.C (g a)) = ψ (g a) := by
          change (q.toRingHom.comp MvPolynomial.C) (g a) = ψ (g a)
          exact DFunLike.congr_fun hconst (g a)
        _ = k (φ a) := DFunLike.congr_fun hcomm a
        _ = k (p (MvPolynomial.C a)) :=
          congrArg k (DFunLike.congr_fun hpconst a).symm
    · intro i
      simp [q, mapg]
  refine ⟨n, q.toRingHom, hconst, ?_⟩
  apply DenseRange.of_comp
  show DenseRange ((q.toRingHom.comp mapg))
  rw [hpoly]
  exact hk_dense.comp hpdense hk_cont



private lemma continuous_of_map_ideal
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsLinearTopology R R] [IsLinearTopology S S]
    [IsTopologicalAddGroup R] [IsTopologicalAddGroup S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hI : IsAdic I) (hJ : IsAdic J) (hmap : I.map f = J) : Continuous f := by
  have hzero : Tendsto f (nhds 0) (nhds 0) := by
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨n, hn⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp hU
    apply hI.hasBasis_nhds_zero.mem_iff.mpr
    refine ⟨n, trivial, ?_⟩
    intro x hx
    apply hn.2
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have hzero' : ContinuousAt f 0 := by
    simpa only [ContinuousAt, map_zero] using hzero
  exact continuous_of_continuousAt_zero f hzero'

/-- Extending an ideal along `R → S` and then `S → T` is extending it along `R → T`. -/
private lemma map_map_algebraMap_of_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (I : Ideal R) :
    (I.map (algebraMap R S)).map (algebraMap S T) = I.map (algebraMap R T) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

private lemma completedAway_canonical_etale_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (ideal quotientIdeal : Ideal R) (element : R) (index : ℕ)
    (hpow : ideal ^ index ≤ quotientIdeal) :
    let target := CompletedAway ideal element
    (Ideal.quotientMap (quotientIdeal.map (algebraMap R target))
      (algebraMap R target) Ideal.le_comap_map).Etale := by
  let localized := Localization.Away element
  let localizedIdeal := ideal.map (algebraMap R localized)
  let quotientLocIdeal := quotientIdeal.map (algebraMap R localized)
  let target := CompletedAway ideal element
  let extended := quotientIdeal.map (algebraMap R target)
  let extendedLoc := quotientLocIdeal.map (algebraMap localized target)
  have hpowLoc : localizedIdeal ^ index ≤ quotientLocIdeal := by
    dsimp [localizedIdeal, quotientLocIdeal]
    rw [← Ideal.map_pow]
    exact Ideal.map_mono hpow
  let equiv := quotientCompletionEquiv localizedIdeal quotientLocIdeal index hpowLoc
  have hextended : extendedLoc = extended := map_map_algebraMap_of_tower quotientIdeal
  let changeQuotient := Ideal.quotEquivOfEq hextended
  let quotientLoc := Ideal.quotientMap quotientLocIdeal (algebraMap R localized)
    Ideal.le_comap_map
  let : Algebra (R ⧸ quotientIdeal) (localized ⧸ quotientLocIdeal) := quotientLoc.toAlgebra
  let : IsLocalization.Away (Ideal.Quotient.mk quotientIdeal element)
      (localized ⧸ quotientLocIdeal) := isLocalization_away_quotient quotientIdeal element
  have hetale : quotientLoc.Etale :=
    Algebra.Etale.of_isLocalizationAway (Ideal.Quotient.mk quotientIdeal element)
  have hfinal := StacksDraft.etale_comp quotientLoc
    (changeQuotient.toRingHom.comp equiv.symm.toRingHom)
    hetale (StacksDraft.etale_comp equiv.symm.toRingHom changeQuotient.toRingHom
      (RingHom.Etale.of_bijective equiv.symm.bijective)
      (RingHom.Etale.of_bijective changeQuotient.bijective))
  convert hfinal using 1
  apply RingHom.ext
  intro value
  obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective value
  apply (changeQuotient.symm.trans equiv).injective
  simp only [RingEquiv.trans_apply, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply, Ideal.quotientMap_mk]
  change (changeQuotient.symm.trans equiv)
    (Ideal.Quotient.mk extended (algebraMap R target representative)) = quotientLoc _
  change equiv (changeQuotient.symm
    (Ideal.Quotient.mk extended (algebraMap R target representative))) = quotientLoc _
  have hmk : changeQuotient.symm
      (Ideal.Quotient.mk extended (algebraMap R target representative)) =
      Ideal.Quotient.mk extendedLoc (algebraMap R target representative) := by
    apply changeQuotient.injective
    simp only [RingEquiv.apply_symm_apply, changeQuotient, Ideal.quotEquivOfEq_mk]
  rw [hmk, quotientCompletionEquiv_apply_mk]
  change Ideal.Quotient.factor hpowLoc (AdicCompletion.evalₐ localizedIdeal index
    (AdicCompletion.of localizedIdeal localized (algebraMap R localized representative))) = _
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.factor_mk]
  rfl

/-- **An algebra of finite type is topologically of finite type.**  A polynomial presentation
with surjective evaluation is in particular one with dense image, for any topology on the
target. -/
public lemma finiteType_isTopologicallyOfFiniteType
    {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace S]
    (hom : R →+* S) (hfinite : hom.FiniteType) :
    TopologicalRing.IsTopologicallyOfFiniteType hom := by
  let : Algebra R S := hom.toAlgebra
  let : Algebra.FiniteType R S := hfinite
  obtain ⟨count, presentation, hsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfinite
  exact ⟨count, presentation.toRingHom, by ext value; exact presentation.commutes value,
    hsurj.denseRange⟩

/-- **The induced map of completed principal localizations is an arrow of `WAdm^Noeth`.**  For
an arrow `hom : R → S` of topological finite type between Noetherian rings and an ideal of `R`
whose extension defines the topology of `S`, the map `R_{\{f\}} → S_{\{hom f\}}` of completed
principal localizations commutes with the two structure maps, carries the extended ideal of the
source exactly onto the extended ideal of the target, and is continuous and topologically of
finite type for the two extended-ideal adic topologies. -/
public lemma completedAwayMap_properties
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hom : R →+* S) (ideal : Ideal R) (element : R)
    (hfinite : TopologicalRing.IsTopologicallyOfFiniteType hom) (hadic : IsAdic (ideal.map hom)) :
    let source := CompletedAway ideal element
    let target := CompletedAway (ideal.map hom) (hom element)
    let sourceIdeal := ideal.map (algebraMap R source)
    let targetIdeal := (ideal.map hom).map (algebraMap S target)
    letI : TopologicalSpace source := sourceIdeal.adicTopology
    letI : TopologicalSpace target := targetIdeal.adicTopology
    let completed := RingHom.completedAwayMap hom ideal element
    completed.comp (algebraMap R source) = (algebraMap S target).comp hom ∧
      sourceIdeal.map completed = targetIdeal ∧ Continuous completed ∧
      TopologicalRing.IsTopologicallyOfFiniteType completed := by
  let sourceLoc := Localization.Away element
  let targetLoc := Localization.Away (hom element)
  let sourceLocIdeal := ideal.map (algebraMap R sourceLoc)
  let targetLocIdeal := (ideal.map hom).map (algebraMap S targetLoc)
  let source := AdicCompletion sourceLocIdeal sourceLoc
  let target := AdicCompletion targetLocIdeal targetLoc
  let sourceIdeal := ideal.map (algebraMap R source)
  let targetIdeal := (ideal.map hom).map (algebraMap S target)
  let : TopologicalSpace source := sourceIdeal.adicTopology
  let : TopologicalSpace target := targetIdeal.adicTopology
  let : IsTopologicalRing source := sourceIdeal.nonarchimedean.toIsTopologicalRing
  let : IsTopologicalRing target := targetIdeal.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology source source := sourceIdeal.isLinearTopology
  let : IsLinearTopology target target := targetIdeal.isLinearTopology
  have htargetIdeal : targetLocIdeal.map (algebraMap targetLoc target) = targetIdeal :=
    map_map_algebraMap_of_tower (ideal.map hom)
  let localized := IsLocalization.Away.map sourceLoc targetLoc hom element
  let completed := RingHom.completedAwayMap hom ideal element
  have hcommLoc : completed.comp (algebraMap sourceLoc source) =
      (algebraMap targetLoc target).comp localized := by
    let : Algebra sourceLoc targetLoc := localized.toAlgebra
    apply RingHom.ext
    intro value
    change Stacks.Nagata.PthRootDescent.mapAdicCompletion sourceLocIdeal targetLocIdeal _
      (algebraMap sourceLoc source value) = algebraMap targetLoc target (localized value)
    exact Stacks.Nagata.PthRootDescent.mapAdicCompletion_of
      (map_away_map_eq hom ideal element).le value
  have hcomm : completed.comp (algebraMap R source) =
      (algebraMap S target).comp hom := by
    apply RingHom.ext
    intro value
    change completed (algebraMap R source value) = algebraMap S target (hom value)
    rw [IsScalarTower.algebraMap_apply R sourceLoc source,
      show completed (algebraMap sourceLoc source (algebraMap R sourceLoc value)) =
        algebraMap targetLoc target (localized (algebraMap R sourceLoc value)) from
          DFunLike.congr_fun hcommLoc (algebraMap R sourceLoc value)]
    simp [localized, IsLocalization.Away.map, IsLocalization.map_eq,
      IsScalarTower.algebraMap_apply S targetLoc target]
  have hmap : sourceIdeal.map completed = targetIdeal := by
    change (ideal.map (algebraMap R source)).map completed =
      (ideal.map hom).map (algebraMap S target)
    calc
      _ = ideal.map (completed.comp (algebraMap R source)) := Ideal.map_map _ _
      _ = ideal.map ((algebraMap S target).comp hom) := congrArg (ideal.map) hcomm
      _ = _ := (Ideal.map_map _ _).symm
  have hcont : Continuous completed :=
    continuous_of_map_ideal completed sourceIdeal targetIdeal rfl rfl hmap
  let : TopologicalSpace targetLoc := targetLocIdeal.adicTopology
  let : IsTopologicalRing targetLoc := targetLocIdeal.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology targetLoc targetLoc := targetLocIdeal.isLinearTopology
  have hfiniteLoc := isTopologicallyOfFiniteType_awayMap hom hfinite (ideal.map hom) hadic element
  have hcontCompletion : Continuous (algebraMap targetLoc target) :=
    continuous_of_map_ideal (algebraMap targetLoc target)
      targetLocIdeal targetIdeal rfl rfl htargetIdeal
  have hfiniteCompletion := topologicallyOfFiniteType_of_dense_extension
    localized completed (algebraMap sourceLoc source) (algebraMap targetLoc target)
    hcommLoc hfiniteLoc hcontCompletion (by
      have hdense := denseRange_algebraMap_adicCompletion targetLocIdeal
        targetLocIdeal.fg_of_isNoetherianRing
      change @DenseRange target
        (targetLocIdeal.map (algebraMap targetLoc target)).adicTopology targetLoc
        (algebraMap targetLoc target) at hdense
      rw [htargetIdeal] at hdense
      change @DenseRange target targetIdeal.adicTopology targetLoc _
      exact hdense)
  exact ⟨hcomm, hmap, hcont, hfiniteCompletion⟩

/-- **The induced map of completed principal localizations, at a caller-chosen presentation of
the target.**  `Rig.completedAwayMap_properties` builds the arrow `R_{\{f\}} → S_{\{hom f\}}` at
the ideal `sourceIdeal · S` and the element `hom f` exactly as written, which is often not how a
consumer has them: `S_{\{g\}}` for an ideal and an element it knows to be *equal* to those is a
different type, and rewriting inside a type that depends on them is not pleasant.  Here the
target ideal and element are arguments, equated to the computed ones by hypothesis, so a
consumer receives the arrow — with the commuting square, the exact transport of the ideal,
continuity, topological finite type and preservation of flatness — at its own presentation.

Also strictly stronger than `Rig.completedAwayMap_properties`, which has no flatness clause. -/
public lemma exists_completedAwayMap_properties
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hom : R →+* S) (sourceIdeal : Ideal R) (targetIdeal : Ideal S)
    (sourceElement : R) (targetElement : S)
    (hideal : sourceIdeal.map hom = targetIdeal) (helement : hom sourceElement = targetElement)
    (hfinite : TopologicalRing.IsTopologicallyOfFiniteType hom) (hadic : IsAdic targetIdeal) :
    let source := CompletedAway sourceIdeal sourceElement
    let target := CompletedAway targetIdeal targetElement
    let sourceExtended := sourceIdeal.map (algebraMap R source)
    let targetExtended := targetIdeal.map (algebraMap S target)
    letI : TopologicalSpace source := sourceExtended.adicTopology
    letI : TopologicalSpace target := targetExtended.adicTopology
    ∃ completed : source →+* target,
      completed.comp (algebraMap R source) = (algebraMap S target).comp hom ∧
      sourceExtended.map completed = targetExtended ∧ Continuous completed ∧
      TopologicalRing.IsTopologicallyOfFiniteType completed ∧ (hom.Flat → completed.Flat) := by
  subst targetIdeal targetElement
  obtain ⟨hcomm, hmap, hcont, hfinite⟩ :=
    completedAwayMap_properties hom sourceIdeal sourceElement hfinite hadic
  exact ⟨RingHom.completedAwayMap hom sourceIdeal sourceElement,
    hcomm, hmap, hcont, hfinite, completedAwayMap_flat hom sourceIdeal sourceElement⟩

/-- **A completed principal localization is weakly admissible.**  For an ideal of a Noetherian
ring `R` and an element `f`, the ring `R_{\{f\}}` with the topology of the ideal extended from
`R` is a weakly admissible topological ring — so, being Noetherian, an object of `WAdm^Noeth`.
This is `Rig.isWeaklyAdmissible_adicCompletion` with the topology phrased by the ideal extended
from `R` rather than from `Localization.Away f`. -/
public lemma completedAway_weaklyAdmissible
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (ideal : Ideal R) (element : R) :
    let target := CompletedAway ideal element
    let extended := ideal.map (algebraMap R target)
    letI : TopologicalSpace target := extended.adicTopology
    letI : IsTopologicalRing target := extended.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology target target := extended.isLinearTopology
    TopologicalRing.IsWeaklyAdmissible target := by
  let localized := Localization.Away element
  let localizedIdeal := ideal.map (algebraMap R localized)
  let target := CompletedAway ideal element
  have hmap : localizedIdeal.map (algebraMap localized target) =
      ideal.map (algebraMap R target) := map_map_algebraMap_of_tower ideal
  have hweak :=
    isWeaklyAdmissible_adicCompletion localizedIdeal localizedIdeal.fg_of_isNoetherianRing
  exact Eq.mp (congrArg (fun extended : Ideal target =>
    let : TopologicalSpace target := extended.adicTopology
    let : IsTopologicalRing target := extended.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology target target := extended.isLinearTopology
    TopologicalRing.IsWeaklyAdmissible target) hmap) hweak

private lemma adic_of_map_eq
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    (hom : R →+* S) (sourceIdeal : Ideal R) (targetIdeal : Ideal S)
    (hsource : IsAdic sourceIdeal) (htarget : IsAdic targetIdeal)
    (hmap : sourceIdeal.map hom = targetIdeal) : _root_.RingHom.IsAdic hom :=
  ⟨sourceIdeal, hsource, hmap.symm ▸ htarget⟩

/-- **The structure map of a completed principal localization is an arrow of `WAdm^Noeth`, and
is flat.**  For an ideal defining the topology of a Noetherian ring `R` and an element `f`, the
canonical map `R → R_{\{f\}}` is continuous, adic and topologically of finite type for the
extended-ideal adic topology on the target, and is flat; moreover `Localization.Away f` has
dense image in `R_{\{f\}}`, which is what pins down maps out of it. -/
public lemma completedAway_canonical_properties
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R]
    (ideal : Ideal R) (element : R) (hadic : IsAdic ideal) :
    let target := CompletedAway ideal element
    let targetIdeal := ideal.map (algebraMap R target)
    letI : TopologicalSpace target := targetIdeal.adicTopology
    Continuous (algebraMap R target) ∧
      _root_.RingHom.IsAdic (algebraMap R target) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap R target) ∧
      (algebraMap R target).Flat ∧ DenseRange (algebraMap (Localization.Away element) target) := by
  let localized := Localization.Away element
  let localizedIdeal := ideal.map (algebraMap R localized)
  let target := CompletedAway ideal element
  let targetIdeal := ideal.map (algebraMap R target)
  let : TopologicalSpace target := targetIdeal.adicTopology
  let : IsTopologicalRing target := targetIdeal.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology target target := targetIdeal.isLinearTopology
  have hmap : localizedIdeal.map (algebraMap localized target) = targetIdeal :=
    map_map_algebraMap_of_tower ideal
  have hcont := continuous_of_map_ideal (algebraMap R target) ideal targetIdeal hadic rfl rfl
  let : TopologicalSpace localized := localizedIdeal.adicTopology
  let : IsTopologicalRing localized := localizedIdeal.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology localized localized := localizedIdeal.isLinearTopology
  have hcontLoc := continuous_of_map_ideal (algebraMap localized target)
    localizedIdeal targetIdeal rfl rfl hmap
  have hdense := denseRange_algebraMap_adicCompletion localizedIdeal
    localizedIdeal.fg_of_isNoetherianRing
  change @DenseRange target
    (localizedIdeal.map (algebraMap localized target)).adicTopology localized _ at hdense
  rw [hmap] at hdense
  have hfiniteLoc := finiteType_isTopologicallyOfFiniteType (algebraMap R localized)
    (show (algebraMap R localized).FiniteType from
      RingHom.finiteType_holdsForLocalizationAway localized element)
  have hfiniteCompletion :
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap localized target) :=
    ⟨0, (algebraMap localized target).comp
      (MvPolynomial.isEmptyAlgEquiv localized (Fin 0)).toRingHom,
      RingHom.ext fun value ↦ congrArg (algebraMap localized target)
        ((MvPolynomial.isEmptyAlgEquiv localized (Fin 0)).commutes value),
      hdense.comp (MvPolynomial.isEmptyAlgEquiv localized (Fin 0)).surjective.denseRange
        hcontLoc⟩
  have hfinite := TopologicalRing.isTopologicallyOfFiniteType_comp (algebraMap localized target)
    (algebraMap R localized) hcontLoc hfiniteCompletion hfiniteLoc
  have hflat : (algebraMap R target).Flat := by
    rw [IsScalarTower.algebraMap_eq R localized target]
    exact (RingHom.flat_algebraMap_iff.mpr inferInstance).comp
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ⟨hcont, ⟨ideal, hadic, rfl⟩,
    by simpa only [← IsScalarTower.algebraMap_eq R localized target] using hfinite,
    hflat, hdense⟩

/-- **A continuous map out of a completed principal localization is determined by its
restriction to the base.**  If `Localization.Away element` has dense image in `C` and the target
is Hausdorff, two continuous ring homomorphisms out of `C` which agree on the image of `R` are
equal: they already agree on `Localization.Away element`, because a map out of a localization is
determined by its restriction, and then on all of `C` by density. -/
@[ega "0 7.6.7" "partial"]
public lemma completedHom_ext
    {R C T : Type*} [CommRing R] [CommRing C] [CommRing T]
    [TopologicalSpace C] [TopologicalSpace T] [T2Space T]
    [Algebra R C] (element : R) [Algebra (Localization.Away element) C]
    [IsScalarTower R (Localization.Away element) C]
    (hdense : DenseRange (algebraMap (Localization.Away element) C))
    (first second : C →+* T) (hfirst : Continuous first) (hsecond : Continuous second)
    (hbase : first.comp (algebraMap R C) = second.comp (algebraMap R C)) :
    first = second := by
  have hloc : first.comp (algebraMap (Localization.Away element) C) =
      second.comp (algebraMap (Localization.Away element) C) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers element)
    simpa only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] using hbase
  exact RingHom.ext <| congrFun <| hdense.equalizer hfirst hsecond <|
    funext fun value => DFunLike.congr_fun hloc value

private lemma completedSquare_commutes
    {R S R' S' C D C' D' : Type*}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [CommRing C] [CommRing D] [CommRing C'] [CommRing D']
    [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace C']
    [TopologicalSpace D'] [T2Space D']
    [Algebra R C] [Algebra S D] [Algebra R' C'] [Algebra S' D']
    (hom : R →+* S) (hom' : R' →+* S') (source : R →+* R') (target : S →+* S')
    (completed : C →+* D) (completed' : C' →+* D')
    (completedSource : C →+* C') (completedTarget : D →+* D')
    (element : R) [Algebra (Localization.Away element) C]
    [IsScalarTower R (Localization.Away element) C]
    (hdense : DenseRange (algebraMap (Localization.Away element) C))
    (hsquare : hom'.comp source = target.comp hom)
    (hcomm : completed.comp (algebraMap R C) = (algebraMap S D).comp hom)
    (hcomm' : completed'.comp (algebraMap R' C') = (algebraMap S' D').comp hom')
    (hsource : completedSource.comp (algebraMap R C) = (algebraMap R' C').comp source)
    (htarget : completedTarget.comp (algebraMap S D) = (algebraMap S' D').comp target)
    (hcont : Continuous completed) (hcont' : Continuous completed')
    (hcontSource : Continuous completedSource) (hcontTarget : Continuous completedTarget) :
    completed'.comp completedSource = completedTarget.comp completed := by
  have hbase : (completed'.comp completedSource).comp (algebraMap R C) =
      (completedTarget.comp completed).comp (algebraMap R C) := by
    rw [RingHom.comp_assoc, hsource, ← RingHom.comp_assoc, hcomm', RingHom.comp_assoc,
      hsquare, ← RingHom.comp_assoc, ← htarget, RingHom.comp_assoc,
      ← hcomm, ← RingHom.comp_assoc]
  exact completedHom_ext element hdense _ _ (hcont'.comp hcontSource)
    (hcontTarget.comp hcont) hbase

private lemma closedPointAway_topologicalNilradical_of_closedPointAway
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (ideal prime : Ideal R) [prime.IsPrime]
    (hadic : IsAdic ideal) (hclosed : Ideal.IsClosedPointAwayFrom ideal prime) :
    Ideal.IsClosedPointAwayFrom (topologicalNilradical R) prime := by
  unfold Ideal.IsClosedPointAwayFrom at hclosed ⊢
  rwa [← radical_eq_topologicalNilradical_of_isAdic ideal hadic,
    PrimeSpectrum.zeroLocus_radical]

private lemma closedPoint_comap_of_finite_quotient
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hS : TopologicalRing.IsWeaklyAdmissible S)
    (hom : R →+* S) (hcont : Continuous hom) (hadic : _root_.RingHom.IsAdic hom)
    (hfinite : TopologicalRing.IsTopologicallyOfFiniteType hom)
    (prime : Ideal S) [prime.IsPrime]
    (hclosed : Ideal.IsClosedPointAwayFrom (topologicalNilradical S) prime)
    (hquot : (Ideal.quotientMap prime hom
      (show prime.comap hom ≤ prime.comap hom from le_rfl)).Finite) :
    Ideal.IsClosedPointAwayFrom (topologicalNilradical R) (prime.comap hom) :=
  ((rigPoint_relative_tfae hR hS hom hcont hadic hfinite prime hclosed).out 3 2).mp hquot

private lemma finite_quotient_of_closedPoint_comap
    {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hS : TopologicalRing.IsWeaklyAdmissible S)
    (hom : R →+* S) (hcont : Continuous hom) (hadic : _root_.RingHom.IsAdic hom)
    (hfinite : TopologicalRing.IsTopologicallyOfFiniteType hom)
    (prime : Ideal S) [prime.IsPrime]
    (hclosed : Ideal.IsClosedPointAwayFrom (topologicalNilradical S) prime)
    (hcomap : Ideal.IsClosedPointAwayFrom (topologicalNilradical R) (prime.comap hom)) :
    (Ideal.quotientMap prime hom (show prime.comap hom ≤ prime.comap hom from le_rfl)).Finite :=
  ((rigPoint_relative_tfae hR hS hom hcont hadic hfinite prime hclosed).out 2 3).mp hcomap

private lemma closedPoint_comap_of_closedPoint_comap_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLinearTopology S S]
    [TopologicalSpace T] [IsTopologicalRing T] [IsLinearTopology T T]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing T]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hS : TopologicalRing.IsWeaklyAdmissible S)
    (hT : TopologicalRing.IsWeaklyAdmissible T)
    (hom : R →+* S) (next : S →+* T)
    (hcont : Continuous hom) (hcontNext : Continuous next)
    (hadic : _root_.RingHom.IsAdic hom) (hadicNext : _root_.RingHom.IsAdic next)
    (hfinite : TopologicalRing.IsTopologicallyOfFiniteType hom)
    (hfiniteNext : TopologicalRing.IsTopologicallyOfFiniteType next)
    (prime : Ideal T) [prime.IsPrime]
    (hclosed : Ideal.IsClosedPointAwayFrom (topologicalNilradical T) prime)
    (hcomap : Ideal.IsClosedPointAwayFrom (topologicalNilradical R)
      (prime.comap (next.comp hom))) :
    Ideal.IsClosedPointAwayFrom (topologicalNilradical S) (prime.comap next) := by
  have hcompAdic := adic_comp hom next hcontNext hadic hadicNext
  have hcompFinite := TopologicalRing.isTopologicallyOfFiniteType_comp next hom hcontNext
    hfiniteNext hfinite
  have hquot := finite_quotient_of_closedPoint_comap hR hT (next.comp hom)
    (hcontNext.comp hcont) hcompAdic hcompFinite prime hclosed hcomap
  let sourcePrime := (prime.comap next).comap hom
  let first := Ideal.quotientMap (prime.comap next) hom
    (show sourcePrime ≤ (prime.comap next).comap hom from le_rfl)
  let second := Ideal.quotientMap prime next
    (show prime.comap next ≤ prime.comap next from le_rfl)
  let quotientEquiv := Ideal.quotEquivOfEq
    (show sourcePrime = prime.comap (next.comp hom) from Ideal.comap_comap hom next)
  have hfiniteComp : (second.comp first).Finite := by
    have heq : second.comp first =
        (Ideal.quotientMap prime (next.comp hom) le_rfl).comp quotientEquiv.toRingHom := by
      apply RingHom.ext
      intro value
      obtain ⟨representative, rfl⟩ := Ideal.Quotient.mk_surjective value
      rfl
    rw [heq]
    exact hquot.comp (RingHom.Finite.of_surjective _ quotientEquiv.surjective)
  exact closedPoint_comap_of_finite_quotient hS hT next hcontNext hadicNext hfiniteNext
    prime hclosed (RingHom.Finite.of_comp_finite hfiniteComp)

/-- If a composite of ring maps is flat and the second factor is faithfully flat, then the first
factor is flat.

This is `Rig.flat_of_faithfullyFlat_square` at the square whose lower edge is the identity. -/
private lemma flat_of_faithfullyFlat_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (hom : R →+* S) (next : S →+* T) (hnext : next.FaithfullyFlat)
    (hcomp : (next.comp hom).Flat) : hom.Flat :=
  flat_of_faithfullyFlat_square hom (RingHom.id R) next (next.comp hom)
    (RingHom.comp_id _).symm (RingHom.Flat.id R) hnext hcomp

private theorem flatAtPrime_of_naivelyRigFlat_rigClosed
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hφ_adic : _root_.RingHom.IsAdic φ)
    (hφ_naive : RingHom.IsNaivelyRigFlat φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical B) q) :
    _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ) := by
  classical
  have hφ_adic_orig := hφ_adic
  rcases hφ_adic with ⟨I, hI, hJ⟩
  have hAstar : ∃ I : Ideal A, IsAdic I ∧ I.FG :=
    ⟨I, hI, Ideal.fg_of_isNoetherianRing I⟩
  have hBstar : ∃ J : Ideal B, IsAdic J ∧ J.FG :=
    ⟨I.map φ, hJ, Ideal.fg_of_isNoetherianRing _⟩
  let : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := hB.2.1
  let : T2Space B := hB.2.2
  have hrig := (rigPoint_tfae ⟨I.map φ, hJ⟩ q).out 2 1
  have havoid : ∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧
      Ideal.IsMaximalAmongPrimesAvoiding J q :=
    hrig.mp ⟨topologicalNilradical B,
      isIdealOfDefinition_topologicalNilradical_of_isAdic (I.map φ) hJ, hq⟩
  have hcrit := naivelyRigFlat_tfae φ hφ hA hB hAstar hBstar hφ_adic_orig
  have hflat := (hcrit.out 1 4).mp hφ_naive.2.2
  exact hflat q havoid

private theorem flatAtPrime_of_flat_etale_square_of_rigPoint
    {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [IsNoetherianRing A] [IsNoetherianRing A'] [IsNoetherianRing B']
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hA' : TopologicalRing.IsWeaklyAdmissible A')
    (φ : A →+* B) (φ' : A' →+* B') (α : A →+* A') (β : B →+* B')
    (hsquare : φ'.comp α = β.comp φ)
    (hα_cont : Continuous α) (hα_adic : _root_.RingHom.IsAdic α)
    (hα_ft : TopologicalRing.IsTopologicallyOfFiniteType α)
    (hα_flat : α.Flat) (hβ_flat : β.Flat)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (hα_etale : (Ideal.quotientMap (I.map α) α Ideal.le_comap_map).Etale)
    (q' : Ideal B') [q'.IsPrime]
    (hp' : Ideal.IsRigPointLocalCondition (q'.comap φ'))
    (hp : Ideal.IsRigPointLocalCondition ((q'.comap φ').comap α))
    (hφ_flat : ((algebraMap B (Localization.AtPrime (q'.comap β))).comp φ).Flat) :
    ((algebraMap B' (Localization.AtPrime q')).comp φ').Flat := by
  let p' := q'.comap φ'
  let p := p'.comap α
  let q := q'.comap β
  have hpq : p = q.comap φ := by
    dsimp [p, p', q]
    rw [Ideal.comap_comap, Ideal.comap_comap, hsquare]
  let φp := Localization.localRingHom p q φ hpq
  let αp := Localization.localRingHom p p' α rfl
  let βq := Localization.localRingHom q q' β rfl
  let φ'p := Localization.localRingHom p' q' φ' rfl
  have hlocsquare : φ'p.comp αp = βq.comp φp := by
    dsimp [φp, αp, βq, φ'p]
    rw [← Localization.localRingHom_comp, ← Localization.localRingHom_comp]
    congr 1
  have hαp : αp.Flat := hα_flat.localRingHom p' p rfl
  have hβq : βq.Flat := hβ_flat.localRingHom q' q rfl
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := φp.toAlgebra
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime p') := αp.toAlgebra
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime q') := βq.toAlgebra
  let : Algebra (Localization.AtPrime p') (Localization.AtPrime q') := φ'p.toAlgebra
  let : IsLocalHom (algebraMap (Localization.AtPrime p') (Localization.AtPrime q')) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p' q' φ' rfl))
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q') :=
    (βq.comp φp).toAlgebra
  let : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
      (Localization.AtPrime q') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime p')
      (Localization.AtPrime q') := IsScalarTower.of_algebraMap_eq' hlocsquare.symm
  let : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p') := hαp
  let : Module.Flat (Localization.AtPrime q) (Localization.AtPrime q') := hβq
  let : Algebra A (Localization.AtPrime q) :=
    ((algebraMap B (Localization.AtPrime q)).comp φ).toAlgebra
  let : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      exact (Localization.localRingHom_to_map p q φ hpq x).symm)
  let : Module.Flat A (Localization.AtPrime q) := hφ_flat
  have hφp : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr
      inferInstance
  have hmax := map_comap_eq_map_of_rigPoint_of_etale_quotient
    hA hA' α hα_cont hα_adic hα_ft hα_flat I hI hα_etale p' hp' hp
  have hmaxp : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map αp =
      IsLocalRing.maximalIdeal (Localization.AtPrime p') := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
      Ideal.map_map]
    have hcomm : αp.comp (algebraMap A (Localization.AtPrime p)) =
        (algebraMap A' (Localization.AtPrime p')).comp α := by
      ext x
      exact Localization.localRingHom_to_map p p' α rfl x
    rw [hcomm]
    exact hmax.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p' _)
  have hφ'p : φ'p.Flat := flat_of_localFlatSquare hmaxp hφp
  have hφ'pcomp : φ'p.comp (algebraMap A' (Localization.AtPrime p')) =
      (algebraMap B' (Localization.AtPrime q')).comp φ' := by
    ext x
    exact Localization.localRingHom_to_map p' q' φ' rfl x
  rw [← hφ'pcomp]
  exact (RingHom.flat_algebraMap_iff.mpr inferInstance).comp hφ'p

private theorem flatAtPrime_of_rigFlat_flat_etale_square
    {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [IsNoetherianRing A] [IsNoetherianRing A']
    [IsNoetherianRing B] [IsNoetherianRing B']
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB' : TopologicalRing.IsWeaklyAdmissible B')
    (φ : A →+* B) (φ' : A' →+* B') (α : A →+* A') (β : B →+* B')
    (hsquare : φ'.comp α = β.comp φ)
    (hφ_cont : Continuous φ) (hφ'_cont : Continuous φ')
    (hα_cont : Continuous α)
    (hφ_adic : _root_.RingHom.IsAdic φ) (hφ'_adic : _root_.RingHom.IsAdic φ')
    (hα_adic : _root_.RingHom.IsAdic α)
    (hφ_ft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hφ'_ft : TopologicalRing.IsTopologicallyOfFiniteType φ')
    (hα_ft : TopologicalRing.IsTopologicallyOfFiniteType α)
    (hβ_ft : TopologicalRing.IsTopologicallyOfFiniteType β)
    (hα_flat : α.Flat) (hβ_flat : β.Flat)
    (ideal : Ideal A) (hideal : TopologicalRing.IsIdealOfDefinition ideal)
    (hrig : RingHom.IsRigFlat φ)
    (hetale : (Ideal.quotientMap (ideal.map α) α Ideal.le_comap_map).Etale)
    (prime : Ideal B') [prime.IsPrime]
    (hclosed : Ideal.IsClosedPointAwayFrom (topologicalNilradical B') prime) :
    ((algebraMap B' (Localization.AtPrime prime)).comp φ').Flat := by
  classical
  let composite := φ'.comp α
  have hcompCont : Continuous composite := hφ'_cont.comp hα_cont
  have hcompAdic : _root_.RingHom.IsAdic composite := adic_comp α φ' hφ'_cont hα_adic hφ'_adic
  have hcompFinite : TopologicalRing.IsTopologicallyOfFiniteType composite :=
    TopologicalRing.isTopologicallyOfFiniteType_comp φ' α hφ'_cont hφ'_ft hα_ft
  obtain ⟨element, hunit, hcompletion⟩ :=
    exists_isClosedPointAwayFrom_completedAway_comap
      hA hB' composite hcompCont hcompAdic hcompFinite prime hclosed
  let idealBase := hcompAdic.choose
  let idealLeft := idealBase.map φ
  let idealRight := idealBase.map α
  let idealTarget := idealBase.map composite
  have hbaseAdic : IsAdic idealBase := hcompAdic.choose_spec.1
  have htargetAdic : IsAdic idealTarget := hcompAdic.choose_spec.2
  have hleftAdic : IsAdic idealLeft :=
    isAdic_map_of_isAdic_of_continuous φ hφ_cont hφ_adic hbaseAdic
  have hrightAdic : IsAdic idealRight :=
    isAdic_map_of_isAdic_of_continuous α hα_cont hα_adic hbaseAdic
  let baseHat := CompletedAway idealBase element
  let leftHat := CompletedAway idealLeft (φ element)
  let rightHat := CompletedAway idealRight (α element)
  let targetHat := CompletedAway idealTarget (composite element)
  let baseExtended := idealBase.map (algebraMap A baseHat)
  let leftExtended := idealLeft.map (algebraMap B leftHat)
  let rightExtended := idealRight.map (algebraMap A' rightHat)
  let targetExtended := idealTarget.map (algebraMap B' targetHat)
  let : TopologicalSpace baseHat := baseExtended.adicTopology
  let : TopologicalSpace leftHat := leftExtended.adicTopology
  let : TopologicalSpace rightHat := rightExtended.adicTopology
  let : TopologicalSpace targetHat := targetExtended.adicTopology
  let : IsTopologicalRing baseHat := baseExtended.nonarchimedean.toIsTopologicalRing
  let : IsTopologicalRing leftHat := leftExtended.nonarchimedean.toIsTopologicalRing
  let : IsTopologicalRing rightHat := rightExtended.nonarchimedean.toIsTopologicalRing
  let : IsTopologicalRing targetHat := targetExtended.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology baseHat baseHat := baseExtended.isLinearTopology
  let : IsLinearTopology leftHat leftHat := leftExtended.isLinearTopology
  let : IsLinearTopology rightHat rightHat := rightExtended.isLinearTopology
  let : IsLinearTopology targetHat targetHat := targetExtended.isLinearTopology
  let : IsNoetherianRing baseHat := AdicCompletion.isNoetherianRing _
  let : IsNoetherianRing leftHat := AdicCompletion.isNoetherianRing _
  let : IsNoetherianRing rightHat := AdicCompletion.isNoetherianRing _
  let : IsNoetherianRing targetHat := AdicCompletion.isNoetherianRing _
  have hbaseWeak : TopologicalRing.IsWeaklyAdmissible baseHat :=
    completedAway_weaklyAdmissible idealBase element
  have hleftWeak : TopologicalRing.IsWeaklyAdmissible leftHat :=
    completedAway_weaklyAdmissible idealLeft (φ element)
  have hrightWeak : TopologicalRing.IsWeaklyAdmissible rightHat :=
    completedAway_weaklyAdmissible idealRight (α element)
  have htargetWeak : TopologicalRing.IsWeaklyAdmissible targetHat :=
    completedAway_weaklyAdmissible idealTarget (composite element)
  let : T2Space targetHat := htargetWeak.2.2
  have hbaseCanon := completedAway_canonical_properties idealBase element hbaseAdic
  have hrightCanon := completedAway_canonical_properties idealRight (α element) hrightAdic
  have htargetCanon :=
    completedAway_canonical_properties idealTarget (composite element) htargetAdic
  let leftMap := RingHom.completedAwayMap φ idealBase element
  obtain ⟨hleftComm, hleftIdeal, hleftCont, hleftFinite⟩ :=
    completedAwayMap_properties φ idealBase element hφ_ft hleftAdic
  have hleftMapAdic : _root_.RingHom.IsAdic leftMap :=
    adic_of_map_eq leftMap baseExtended leftExtended rfl rfl hleftIdeal
  obtain ⟨bottomMap, hbottomComm, hbottomIdeal, hbottomCont, hbottomFinite, hbottomFlat⟩ :=
    exists_completedAwayMap_properties α idealBase idealRight element (α element)
      rfl rfl hα_ft hrightAdic
  obtain ⟨topMap, htopComm, htopIdeal, htopCont, htopFinite, htopFlat⟩ :=
    exists_completedAwayMap_properties β idealLeft idealTarget (φ element) (composite element)
      (by dsimp [idealLeft, idealTarget, composite]; rw [Ideal.map_map, ← hsquare])
      (DFunLike.congr_fun hsquare element).symm hβ_ft htargetAdic
  obtain ⟨rightMap, hrightComm, hrightIdeal, hrightCont, hrightFinite, hrightFlat⟩ :=
    exists_completedAwayMap_properties φ' idealRight idealTarget (α element) (composite element)
      (by dsimp [idealRight, idealTarget, composite]; rw [Ideal.map_map])
      rfl hφ'_ft htargetAdic
  have hbottomAdic : _root_.RingHom.IsAdic bottomMap :=
    adic_of_map_eq bottomMap baseExtended rightExtended rfl rfl hbottomIdeal
  have hrightMapAdic : _root_.RingHom.IsAdic rightMap :=
    adic_of_map_eq rightMap rightExtended targetExtended rfl rfl hrightIdeal
  have hhatSquare : rightMap.comp bottomMap = topMap.comp leftMap :=
    completedSquare_commutes φ φ' α β leftMap rightMap bottomMap topMap element
      hbaseCanon.2.2.2.2 hsquare hleftComm hrightComm hbottomComm htopComm
      hleftCont hrightCont hbottomCont htopCont
  let compositeMap := RingHom.completedAwayMap composite idealBase element
  have hcompositeProperties := completedAwayMap_properties composite idealBase element
    hcompFinite htargetAdic
  have hhatComposite : rightMap.comp bottomMap = compositeMap := by
    apply completedHom_ext element hbaseCanon.2.2.2.2 _ _
      (hrightCont.comp hbottomCont) hcompositeProperties.2.2.1
    rw [RingHom.comp_assoc, hbottomComm, ← RingHom.comp_assoc, hrightComm,
      RingHom.comp_assoc, ← hcompositeProperties.1]
  let targetPrime := extendedIdeal idealTarget prime (composite element)
  change compositeMap.comp (algebraMap A baseHat) =
    (algebraMap B' targetHat).comp composite ∧ _ at hcompletion
  obtain ⟨_, hprime, hbasePrime, htargetClosed, hbaseClosed⟩ := hcompletion
  let : targetPrime.IsPrime := hprime
  have htargetExtended :
      (idealTarget.map (algebraMap B' (Localization.Away (composite element)))).map
        (algebraMap (Localization.Away (composite element)) targetHat) = targetExtended :=
    map_map_algebraMap_of_tower _
  have hbaseExtended :
      (idealBase.map (algebraMap A (Localization.Away element))).map
        (algebraMap (Localization.Away element) baseHat) = baseExtended :=
    map_map_algebraMap_of_tower _
  have hleftExtended :
      (idealLeft.map (algebraMap B (Localization.Away (φ element)))).map
        (algebraMap (Localization.Away (φ element)) leftHat) = leftExtended :=
    map_map_algebraMap_of_tower _
  change Ideal.IsClosedPointAwayFrom _ targetPrime at htargetClosed
  rw [htargetExtended] at htargetClosed
  change Ideal.IsClosedPointAwayFrom _ (targetPrime.comap compositeMap) at hbaseClosed
  rw [hbaseExtended] at hbaseClosed
  have htargetClosedNil : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical targetHat) targetPrime :=
    closedPointAway_topologicalNilradical_of_closedPointAway targetExtended targetPrime
      (by change targetExtended.adicTopology = _; rfl) htargetClosed
  have hbaseClosedNil : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical baseHat) (targetPrime.comap (rightMap.comp bottomMap)) := by
    rw [hhatComposite]
    exact closedPointAway_topologicalNilradical_of_closedPointAway baseExtended _
      (by change baseExtended.adicTopology = _; rfl) hbaseClosed
  have hrightClosedNil := closedPoint_comap_of_closedPoint_comap_comp
    hbaseWeak hrightWeak htargetWeak bottomMap rightMap hbottomCont hrightCont
    hbottomAdic hrightMapAdic hbottomFinite hrightFinite targetPrime
    htargetClosedNil hbaseClosedNil
  have htopAdic : _root_.RingHom.IsAdic topMap :=
    adic_of_map_eq topMap leftExtended targetExtended rfl rfl htopIdeal
  have hleftClosedNil := closedPoint_comap_of_closedPoint_comap_comp
    hbaseWeak hleftWeak htargetWeak leftMap topMap hleftCont htopCont
    hleftMapAdic htopAdic hleftFinite htopFinite targetPrime htargetClosedNil
    (by rwa [← hhatSquare])
  have hleftNaive : RingHom.IsNaivelyRigFlat leftMap := by
    have hnaive := hrig.2.2 idealBase hbaseAdic hleftAdic element
    dsimp only at hnaive
    change @RingHom.IsNaivelyRigFlat baseHat leftHat _ _
      ((idealBase.map (algebraMap A (Localization.Away element))).map
        (algebraMap (Localization.Away element) baseHat)).adicTopology
      ((idealLeft.map (algebraMap B (Localization.Away (φ element)))).map
        (algebraMap (Localization.Away (φ element)) leftHat)).adicTopology leftMap at hnaive
    rw [hbaseExtended, hleftExtended] at hnaive
    exact hnaive
  have hleftLocal := flatAtPrime_of_naivelyRigFlat_rigClosed hbaseWeak hleftWeak
    leftMap hleftCont hleftMapAdic hleftNaive (targetPrime.comap topMap) hleftClosedNil
  have hidealAdic : IsAdic ideal :=
    (isIdealOfDefinition_iff_isAdic ⟨idealBase, hbaseAdic⟩ ideal).mp hideal
  obtain ⟨power, hpower⟩ := exists_pow_map_le_of_continuous_of_isAdic
    (RingHom.id A) continuous_id hbaseAdic hidealAdic
  have hpowerBase : idealBase ^ power ≤ ideal := by simpa using hpower
  have hpowerRight : idealRight ^ power ≤ ideal.map α := by
    dsimp [idealRight]
    rw [← Ideal.map_pow]
    exact Ideal.map_mono hpowerBase
  have hbottomEtale := etale_quotient_of_commutative_square α bottomMap
    (algebraMap A baseHat) (algebraMap A' rightHat) hbottomComm ideal hetale
    (completedAway_canonical_etale_quotient idealBase ideal element power hpowerBase)
    (completedAway_canonical_etale_quotient idealRight (ideal.map α) (α element)
      power hpowerRight)
  have hidealHatAdic := isAdic_map_of_isAdic_of_continuous (algebraMap A baseHat)
    hbaseCanon.1 hbaseCanon.2.1 hidealAdic
  have hlocal := flatAtPrime_of_flat_etale_square_of_rigPoint hbaseWeak hrightWeak
    leftMap rightMap bottomMap topMap hhatSquare hbottomCont hbottomAdic hbottomFinite
    (hbottomFlat hα_flat) (htopFlat hβ_flat) (ideal.map (algebraMap A baseHat))
    (isIdealOfDefinition_of_isAdic hidealHatAdic) hbottomEtale targetPrime
    (rigPointLocalCondition_of_closedPointAwayFrom_topologicalNilradical hrightWeak
      ⟨rightExtended, rfl⟩ _ hrightClosedNil)
    (rigPointLocalCondition_of_closedPointAwayFrom_topologicalNilradical hbaseWeak
      ⟨baseExtended, rfl⟩ _ (by simpa only [Ideal.comap_comap] using hbaseClosedNil))
    hleftLocal
  let : UniformSpace B' := IsTopologicalAddGroup.rightUniformSpace B'
  let : IsUniformAddGroup B' := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace B' := hB'.2.1
  let : T2Space B' := hB'.2.2
  let : IsAdicComplete idealTarget B' := htargetAdic.isAdicComplete_iff.mpr ⟨hB'.2.1, hB'.2.2⟩
  have hprimeComap := comap_extendedIdeal_eq idealTarget prime (composite element) hunit
  let localMap := Localization.localRingHom prime targetPrime
    (algebraMap B' targetHat) hprimeComap.symm
  have hlocalMapFlat : localMap.Flat :=
    htargetCanon.2.2.2.1.localRingHom targetPrime prime hprimeComap.symm
  have hlocalMapFaithful : localMap.FaithfullyFlat := by
    let : Algebra (Localization.AtPrime prime) (Localization.AtPrime targetPrime) :=
      localMap.toAlgebra
    have : Module.Flat (Localization.AtPrime prime) (Localization.AtPrime targetPrime) :=
      hlocalMapFlat
    have : IsLocalHom
        (algebraMap (Localization.AtPrime prime) (Localization.AtPrime targetPrime)) :=
      inferInstanceAs (IsLocalHom
        (Localization.localRingHom prime targetPrime (algebraMap B' targetHat)
          hprimeComap.symm))
    change Module.FaithfullyFlat (Localization.AtPrime prime) (Localization.AtPrime targetPrime)
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply flat_of_faithfullyFlat_comp _ localMap hlocalMapFaithful
  have hlocalComm : localMap.comp (algebraMap B' (Localization.AtPrime prime)) =
      (algebraMap targetHat (Localization.AtPrime targetPrime)).comp
        (algebraMap B' targetHat) :=
    RingHom.ext <| Localization.localRingHom_to_map prime targetPrime _ hprimeComap.symm
  rw [← RingHom.comp_assoc, hlocalComm, RingHom.comp_assoc, ← hrightComm,
    ← RingHom.comp_assoc]
  exact hrightCanon.2.2.2.1.comp hlocal

/-- **Stacks 0GGS.** Rig-flatness ascends across the flat horizontal maps of a commutative
square of adic homomorphisms of topological finite type between Noetherian weakly admissible
rings whose lower map is étale modulo an ideal of definition: if `φ` is rig-flat, so is `φ'`. -/
@[stacks 0GGS]
public theorem isRigFlat_of_flat_etale_square
    {A A' B B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
    [IsNoetherianRing A] [IsNoetherianRing A']
    [IsNoetherianRing B] [IsNoetherianRing B']
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (_hA' : TopologicalRing.IsWeaklyAdmissible A')
    (_hB : TopologicalRing.IsWeaklyAdmissible B)
    (_hB' : TopologicalRing.IsWeaklyAdmissible B')
    (φ : A →+* B) (φ' : A' →+* B')
    (α : A →+* A') (β : B →+* B')
    (hsquare : φ'.comp α = β.comp φ)
    (hφ_cont : Continuous φ) (_hφ'_cont : Continuous φ')
    (hα_cont : Continuous α) (_hβ_cont : Continuous β)
    (hφ_adic : _root_.RingHom.IsAdic φ)
    (hφ'_adic : _root_.RingHom.IsAdic φ')
    (hα_adic : _root_.RingHom.IsAdic α)
    (_hβ_adic : _root_.RingHom.IsAdic β)
    (hφ_ft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hφ'_ft : TopologicalRing.IsTopologicallyOfFiniteType φ')
    (hα_ft : TopologicalRing.IsTopologicallyOfFiniteType α)
    (hβ_ft : TopologicalRing.IsTopologicallyOfFiniteType β)
    (hα_flat : α.Flat) (hβ_flat : β.Flat)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (hφ_rigFlat : RingHom.IsRigFlat φ)
    (hα_etale : (Ideal.quotientMap (I.map α) α Ideal.le_comap_map).Etale) :
    RingHom.IsRigFlat φ' := by
  rcases hφ_rigFlat with ⟨hφ_adic', hφ_ft', hφ_completed⟩
  refine ⟨hφ'_adic, hφ'_ft, ?_⟩
  intro I' hI' hJ' f'
  let A'_f := Localization.Away f'
  let B'_f := Localization.Away (φ' f')
  let I'_f := I'.map (algebraMap A' A'_f)
  let J'_f := (I'.map φ').map (algebraMap B' B'_f)
  let A'_hat := AdicCompletion I'_f A'_f
  let B'_hat := AdicCompletion J'_f B'_f
  let ψ' := RingHom.completedAwayMap φ' I' f'
  let I'_hat := I'_f.map (algebraMap A'_f A'_hat)
  let J'_hat := J'_f.map (algebraMap B'_f B'_hat)
  let : TopologicalSpace A'_hat := I'_hat.adicTopology
  let : TopologicalSpace B'_hat := J'_hat.adicTopology
  have hrightExtendedEq : I'.map (algebraMap A' A'_hat) = I'_hat :=
    (map_map_algebraMap_of_tower I').symm
  have htargetExtendedEq : (I'.map φ').map (algebraMap B' B'_hat) = J'_hat :=
    (map_map_algebraMap_of_tower (I'.map φ')).symm
  have hprops := completedAwayMap_properties φ' I' f' hφ'_ft hJ'
  dsimp only at hprops
  rw [hrightExtendedEq, htargetExtendedEq] at hprops
  change ψ'.comp (algebraMap A' A'_hat) = (algebraMap B' B'_hat).comp φ' ∧
    I'_hat.map ψ' = J'_hat ∧ Continuous ψ' ∧
    TopologicalRing.IsTopologicallyOfFiniteType ψ' at hprops
  change RingHom.IsNaivelyRigFlat ψ'
  refine ⟨⟨I'_hat, rfl, congrArg Ideal.adicTopology hprops.2.1.symm⟩,
    hprops.2.2.2, ?_⟩
  · let : TopologicalSpace A'_f := I'_f.adicTopology
    let : IsLinearTopology A'_f A'_f := I'_f.isLinearTopology
    let : IsTopologicalRing A'_f := inferInstance
    let : TopologicalSpace B'_f := J'_f.adicTopology
    let : IsLinearTopology B'_f B'_f := J'_f.isLinearTopology
    let : IsTopologicalRing B'_f := inferInstance
    let : IsLinearTopology A'_hat A'_hat := I'_hat.isLinearTopology
    let : IsTopologicalRing A'_hat := inferInstance
    let : IsLinearTopology B'_hat B'_hat := J'_hat.isLinearTopology
    let : IsTopologicalRing B'_hat := inferInstance
    let : IsNoetherianRing A'_f := inferInstance
    let : IsNoetherianRing B'_f := inferInstance
    let : IsNoetherianRing A'_hat := AdicCompletion.isNoetherianRing I'_f
    let : IsNoetherianRing B'_hat := AdicCompletion.isNoetherianRing J'_f
    have hψadic : _root_.RingHom.IsAdic ψ' := by
      refine ⟨I'_hat, rfl, ?_⟩
      exact congrArg Ideal.adicTopology hprops.2.1.symm
    have hψcont : Continuous ψ' := hprops.2.2.1
    have hψft : TopologicalRing.IsTopologicallyOfFiniteType ψ' := hprops.2.2.2
    let : @CompleteSpace A'_hat (IsTopologicalAddGroup.rightUniformSpace A'_hat) :=
      (isWeaklyAdmissible_adicCompletion I'_f I'_f.fg_of_isNoetherianRing).2.1
    let : T2Space A'_hat := (isWeaklyAdmissible_adicCompletion I'_f I'_f.fg_of_isNoetherianRing).2.2
    let : @CompleteSpace B'_hat (IsTopologicalAddGroup.rightUniformSpace B'_hat) :=
      (isWeaklyAdmissible_adicCompletion J'_f J'_f.fg_of_isNoetherianRing).2.1
    let : T2Space B'_hat := (isWeaklyAdmissible_adicCompletion J'_f J'_f.fg_of_isNoetherianRing).2.2
    have hweakA : TopologicalRing.IsWeaklyAdmissible A'_hat :=
      isWeaklyAdmissible_adicCompletion I'_f I'_f.fg_of_isNoetherianRing
    have hweakB : TopologicalRing.IsWeaklyAdmissible B'_hat :=
      isWeaklyAdmissible_adicCompletion J'_f J'_f.fg_of_isNoetherianRing
    have hAstar : ∃ K : Ideal A'_hat, IsAdic K ∧ K.FG :=
      ⟨I'_hat, rfl, Ideal.fg_of_isNoetherianRing I'_hat⟩
    have hBstar : ∃ K : Ideal B'_hat, IsAdic K ∧ K.FG :=
      ⟨J'_hat, rfl, Ideal.fg_of_isNoetherianRing J'_hat⟩
    have hcrit := naivelyRigFlat_tfae ψ' hψcont hweakA hweakB
      hAstar hBstar hψadic
    apply (hcrit.out 1 4).symm.mp
    intro q hq hmax
    obtain ⟨K, hK, hclosedK⟩ :=
      ((rigPoint_tfae ⟨J'_hat, rfl⟩ q).out 1 2).mp hmax
    have hKadic : IsAdic K :=
      (isIdealOfDefinition_iff_isAdic ⟨J'_hat, rfl⟩ K).mp hK
    have hqClosed :=
      closedPointAway_topologicalNilradical_of_closedPointAway K q hKadic hclosedK
    have hbaseIdealAdic : IsAdic I :=
      (isIdealOfDefinition_iff_isAdic
        ⟨hφ_adic.choose, hφ_adic.choose_spec.1⟩ I).mp hI
    have hrightIdealAdic : IsAdic (I.map α) :=
      isAdic_map_of_isAdic_of_continuous α hα_cont hα_adic hbaseIdealAdic
    have hrightCanonical := completedAway_canonical_properties I' f' hI'
    have htargetCanonical := completedAway_canonical_properties (I'.map φ') (φ' f') hJ'
    dsimp only at hrightCanonical htargetCanonical
    rw [hrightExtendedEq] at hrightCanonical
    rw [htargetExtendedEq] at htargetCanonical
    let bottom := (algebraMap A' A'_hat).comp α
    let top := (algebraMap B' B'_hat).comp β
    have hcompletedComm : ψ'.comp (algebraMap A' A'_hat) =
        (algebraMap B' B'_hat).comp φ' := hprops.1
    have hsquareHat : ψ'.comp bottom = top.comp φ := by
      dsimp only [bottom, top]
      rw [← RingHom.comp_assoc, hcompletedComm, RingHom.comp_assoc, hsquare,
        ← RingHom.comp_assoc]
    obtain ⟨power, hpower⟩ := exists_pow_map_le_of_continuous_of_isAdic
      (RingHom.id A') continuous_id hI' hrightIdealAdic
    have hpowerRight : I' ^ power ≤ I.map α := by simpa using hpower
    have hcanonicalEtale := completedAway_canonical_etale_quotient I' (I.map α) f'
      power hpowerRight
    have hbottomEtale := etale_quotient_comp α (algebraMap A' A'_hat) I hα_etale hcanonicalEtale
    exact flatAtPrime_of_rigFlat_flat_etale_square hA hweakB φ ψ' bottom top
      hsquareHat hφ_cont hψcont (hrightCanonical.1.comp hα_cont)
      hφ_adic hψadic
      (adic_comp α _ hrightCanonical.1 hα_adic hrightCanonical.2.1)
      hφ_ft hψft
      (TopologicalRing.isTopologicallyOfFiniteType_comp _ α hrightCanonical.1
        hrightCanonical.2.2.1 hα_ft)
      (TopologicalRing.isTopologicallyOfFiniteType_comp _ β htargetCanonical.1
        htargetCanonical.2.2.1 hβ_ft)
      (hα_flat.comp hrightCanonical.2.2.2.1) (hβ_flat.comp htargetCanonical.2.2.2.1)
      I hI ⟨hφ_adic', hφ_ft', hφ_completed⟩ hbottomEtale q hqClosed


end Rig

end
