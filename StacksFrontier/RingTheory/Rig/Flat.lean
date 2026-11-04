module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Nagata.PthRoot
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Rig-flat ring homomorphisms

An adic homomorphism `φ : A →+* B` of topologically finite type is *naively rig-flat* when
`B[1/φ(f)]` is flat over `A` for every topologically nilpotent `f : A`; it is *rig-flat* when
all the induced maps between the completed principal localizations of `A` and `B` are naively
rig-flat.

For an adic morphism of weakly admissible adic rings with a finitely generated ideal of
definition, the flatness clause in naive rig-flatness can be tested in four equivalent ways: on
topologically nilpotent elements of the source, on topologically nilpotent elements of the
target, at all primes of the target avoiding an ideal of definition, or only at the rig-closed
primes.  The passage between the last two enlarges a prime avoiding an ideal of definition to a
maximal such prime; finite generation of that ideal is what keeps a chain of such primes
avoiding it in the limit, so Zorn's lemma suffices and the target need not be Noetherian.

## Main definitions

* `Rig.RingHom.IsNaivelyRigFlat` — naive rig-flatness of a ring homomorphism.
* `Rig.RingHom.completedAwayMap` — the canonical map between the completions of corresponding
  principal localizations.
* `Rig.RingHom.IsRigFlat` — rig-flatness of a ring homomorphism.

## Main results

* `Rig.naivelyRigFlat_tfae` — the four equivalent flatness tests.
* `IsAdic.exists_pow_le` — two ideals defining the same topology are cofinal in one another's
  powers.
* `RingHom.isAdic_map_of_isAdic` — an adic homomorphism carries any ideal of definition of the
  source to an ideal of definition of the target.

## Implementation notes

The flatness clause uses condition (1) of the equivalent conditions in the source: for every
topologically nilpotent `f : A`, the composite from `A` to the localization of `B` away from
`φ f` is flat.  It is expressed using Mathlib's `RingHom.Flat`, so the scalar action is
determined by that composite.  Principal and prime localizations are represented by
`Localization.Away` and `Localization.AtPrime`, and a rig-closed prime is expressed by
`Rig.Ideal.IsMaximalAmongPrimesAvoiding`: maximal among primes avoiding an ideal of definition,
which is condition (1) of the source's rig-point criterion.

The completed principal localization of `A` at `f`, relative to an ideal `I`, is the adic
completion of `Localization.Away f` along the extension of `I`; the map between two such
completions is induced by `IsLocalization.Away.map` and functoriality of adic completion.
Rig-flatness quantifies over every ideal whose adic topology is the given topology on the
source and whose extension induces the given topology on the target, so it is independent of
the choice implicit in the source's phrase "with respect to any ideal of definition".

The ambient continuity and weak admissibility hypotheses from the source are imposed by
applications rather than built into the predicates, which are abbreviations so that clients can
use the conjunction and universal-quantifier API directly.

## References

* [Stacks Project, Tag 0GGL](https://stacks.math.columbia.edu/tag/0GGL)
* [Stacks Project, Tag 0GGM](https://stacks.math.columbia.edu/tag/0GGM)
* [Stacks Project, Tag 0GGP](https://stacks.math.columbia.edu/tag/0GGP)
-/

@[expose] public section

/-- If two ideals both define the topology of `R`, then every power of one contains a power of
the other. -/
public theorem IsAdic.exists_pow_le {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I J : Ideal R} (hI : IsAdic I) (hJ : IsAdic J) (n : ℕ) :
    ∃ m : ℕ, I ^ m ≤ J ^ n := by
  obtain ⟨m, -, hm⟩ := hI.hasBasis_nhds_zero.mem_iff.mp
    (hJ.hasBasis_nhds_zero.mem_iff.mpr ⟨n, trivial, Set.Subset.rfl⟩)
  exact ⟨m, SetLike.coe_subset_coe.mp hm⟩

/-- An adic ring homomorphism carries every ideal defining the topology of its source to an
ideal defining the topology of its target, not just the one witnessing adicness. -/
public theorem RingHom.isAdic_map_of_isAdic {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : _root_.RingHom.IsAdic f) {I : Ideal A} (hI : _root_.IsAdic I) :
    _root_.IsAdic (I.map f) := by
  obtain ⟨J, hJ, hJmap⟩ := hf
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun U hU => ?_⟩
  · obtain ⟨m, hm⟩ := hJ.exists_pow_le hI 1
    have hpow : (J.map f) ^ m ≤ I.map f := by
      rw [← Ideal.map_pow]
      exact Ideal.map_mono (by simpa using hm)
    refine Ideal.isOpen_of_isOpen_subideal (U := (J.map f) ^ (m * n)) ?_
      ((isAdic_iff.mp hJmap).1 (m * n))
    calc (J.map f) ^ (m * n) = ((J.map f) ^ m) ^ n := by rw [pow_mul]
      _ ≤ (I.map f) ^ n := pow_le_pow_left' hpow n
  · obtain ⟨m, -, hm⟩ := hJmap.hasBasis_nhds_zero.mem_iff.mp hU
    obtain ⟨n, hn⟩ := hI.exists_pow_le hJ m
    refine ⟨n, Set.Subset.trans (SetLike.coe_subset_coe.mpr ?_) hm⟩
    calc (I.map f) ^ n ≤ (J ^ m).map f := by
          rw [← Ideal.map_pow]; exact Ideal.map_mono hn
      _ = (J.map f) ^ m := Ideal.map_pow _ _ _

namespace Rig

namespace RingHom

/-- A ring homomorphism `φ : A →+* B` is naively rig-flat if it is adic, topologically of finite
type, and `B[1 / φ(f)]` is flat over `A` for every topologically nilpotent `f : A`. -/
@[stacks 0GGM]
public abbrev IsNaivelyRigFlat {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (φ : A →+* B) : Prop :=
  _root_.RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ ∧
    (∀ f : A, IsTopologicallyNilpotent f →
      _root_.RingHom.Flat ((algebraMap B (Localization.Away (φ f))).comp φ))

/-- The canonical map from the completed principal localization of `A` at `f`
to that of `B` at `φ f`, using the extension of `I` on both sides. -/
public noncomputable def completedAwayMap {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (f : A) :
    AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f) →+*
      AdicCompletion ((I.map φ).map (algebraMap B (Localization.Away (φ f))))
        (Localization.Away (φ f)) := by
  let φf : Localization.Away f →+* Localization.Away (φ f) :=
    IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f
  letI : Algebra (Localization.Away f) (Localization.Away (φ f)) := φf.toAlgebra
  apply Stacks.Nagata.PthRootDescent.mapAdicCompletion
  rw [Ideal.map_map, Ideal.map_map]
  apply le_of_eq
  congr 1
  ext a
  change φf (algebraMap A (Localization.Away f) a) = _
  dsimp [φf, IsLocalization.Away.map]
  apply IsLocalization.map_eq

/-- The map of completed principal localizations commutes with the maps from the uncompleted
localizations. -/
@[ega "0 7.6.7" "partial"]
public theorem completedAwayMap_comp_algebraMap
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (f : A) :
    let A_f := Localization.Away f
    let B_f := Localization.Away (φ f)
    let I_f := I.map (algebraMap A A_f)
    let J_f := (I.map φ).map (algebraMap B B_f)
    (completedAwayMap φ I f).comp (algebraMap A_f (AdicCompletion I_f A_f)) =
      (algebraMap B_f (AdicCompletion J_f B_f)).comp (IsLocalization.Away.map A_f B_f φ f) := by
  dsimp
  let φf : Localization.Away f →+* Localization.Away (φ f) :=
    IsLocalization.Away.map (Localization.Away f) (Localization.Away (φ f)) φ f
  let : Algebra (Localization.Away f) (Localization.Away (φ f)) := φf.toAlgebra
  apply RingHom.ext
  intro x
  show Stacks.Nagata.PthRootDescent.mapAdicCompletion _ _ _ _ = _
  rw [Stacks.Nagata.PthRootDescent.mapAdicCompletion_of]
  congr 1

/-- The map of completed principal localizations commutes with the maps from the base rings. -/
@[ega "0 7.6.7" "partial"]
public theorem completedAwayMap_comp_base
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (f : A) :
    (completedAwayMap φ I f).comp (algebraMap A (CompletedAway I f)) =
      (algebraMap B (CompletedAway (I.map φ) (φ f))).comp φ := by
  rw [IsScalarTower.algebraMap_eq A (Localization.Away f) (CompletedAway I f),
    ← RingHom.comp_assoc, completedAwayMap_comp_algebraMap, RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq B (Localization.Away (φ f)) (CompletedAway (I.map φ) (φ f)),
    RingHom.comp_assoc]
  congr 1
  ext x
  dsimp [IsLocalization.Away.map]
  apply IsLocalization.map_eq

/-- A ring homomorphism is rig-flat if it is adic and topologically of finite
type, and all the induced maps between completed principal localizations are
naively rig-flat. -/
@[stacks 0GGP]
public abbrev IsRigFlat {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (φ : A →+* B) : Prop :=
  _root_.RingHom.IsAdic φ ∧
    TopologicalRing.IsTopologicallyOfFiniteType φ ∧
      (∀ (I : Ideal A), _root_.IsAdic I → _root_.IsAdic (I.map φ) → ∀ f : A,
        let A_f := Localization.Away f
        let B_f := Localization.Away (φ f)
        let I_f := I.map (algebraMap A A_f)
        let J_f := (I.map φ).map (algebraMap B B_f)
        let I_hat := I_f.map (algebraMap A_f (AdicCompletion I_f A_f))
        let J_hat := J_f.map (algebraMap B_f (AdicCompletion J_f B_f))
        letI : TopologicalSpace (AdicCompletion I_f A_f) := I_hat.adicTopology
        letI : TopologicalSpace (AdicCompletion J_f B_f) := J_hat.adicTopology
        IsNaivelyRigFlat (completedAwayMap φ I f))

end RingHom

section

open Filter
open scoped Topology

/-- A prime not containing a finitely generated ideal `J` is contained in a prime that is maximal
among the primes not containing `J`.  Finite generation of `J` is what makes the union of a chain
of primes avoiding `J` avoid `J` again, so Zorn's lemma applies with no Noetherian hypothesis on
the ring. -/
public lemma exists_maximal_prime_avoiding
    {B : Type*} [CommRing B]
    (J q : Ideal B) (hJfg : J.FG) (hq : q.IsPrime) (hJq : ¬ J ≤ q) :
    ∃ p : Ideal B, p.IsPrime ∧ q ≤ p ∧ ¬ J ≤ p ∧
      ∀ p' : Ideal B, p'.IsPrime → p ≤ p' → ¬ J ≤ p' → p' = p := by
  classical
  obtain ⟨G, hG⟩ := hJfg
  have hGJ : (G : Set B) ⊆ (J : Set B) := by rw [← hG]; exact Ideal.subset_span
  have hub : ∀ c ⊆ {p : Ideal B | p.IsPrime ∧ q ≤ p ∧ ¬ J ≤ p}, IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {p : Ideal B | p.IsPrime ∧ q ≤ p ∧ ¬ J ≤ p}, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hchain y hy
    have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
    have hmem : ∀ x : B, x ∈ sSup c ↔ ∃ p ∈ c, x ∈ p := fun x =>
      Submodule.mem_sSup_of_directed ⟨y, hy⟩ hdir
    have hJsup : ¬ J ≤ sSup c := by
      intro hle
      obtain ⟨p, hpc, hGp⟩ : ∃ p ∈ c, (G : Set B) ⊆ (p : Set B) := by
        refine hdir.exists_mem_subset_of_finset_subset_biUnion ⟨y, hy⟩ fun x hx => ?_
        simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
        exact (hmem x).1 (hle (hGJ hx))
      exact (hcs hpc).2.2 (by rw [← hG]; exact Ideal.span_le.2 hGp)
    have hne : sSup c ≠ ⊤ := fun htop => hJsup (by rw [htop]; exact le_top)
    refine ⟨sSup c, ⟨⟨hne, ?_⟩, (hcs hy).2.1.trans (le_sSup hy), hJsup⟩, fun z hz => le_sSup hz⟩
    intro x z hxz
    obtain ⟨p, hpc, hmemp⟩ := (hmem _).1 hxz
    exact ((hcs hpc).1.mem_or_mem hmemp).imp (fun hxp => le_sSup hpc hxp)
      (fun hzp => le_sSup hpc hzp)
  obtain ⟨p, hqp, hpmax⟩ :=
    zorn_le_nonempty₀ {p : Ideal B | p.IsPrime ∧ q ≤ p ∧ ¬ J ≤ p} hub q ⟨hq, le_rfl, hJq⟩
  obtain ⟨hp, -, hJp⟩ := hpmax.prop
  exact ⟨p, hp, hqp, hJp, fun p' hp' hpp' hJp' =>
    le_antisymm (hpmax.le_of_ge ⟨hp', hqp.trans hpp', hJp'⟩ hpp') hpp'⟩

private lemma flat_atPrime_of_flat_localization
    {A B : Type*} [CommRing A] [CommRing B]
    (phi : A →+* B) (M : Submonoid B)
    (q : Ideal B) (hq : q.IsPrime) (hdisj : Disjoint (M : Set B) (q : Set B))
    (hflat : RingHom.Flat ((algebraMap B (Localization M)).comp phi)) :
    RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp phi) := by
  let : q.IsPrime := hq
  let S := Localization M
  let T := Localization.AtPrime q
  let N := q.primeCompl
  have hMN : M ≤ N := fun x hx => Set.disjoint_left.mp hdisj hx
  let : Algebra S T := IsLocalization.localizationAlgebraOfSubmonoidLe S T M N hMN
  let : IsScalarTower B S T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S T M N hMN
  have : IsLocalization (N.map (algebraMap B S)) T :=
    IsLocalization.isLocalization_of_submonoid_le S T M N hMN
  have hflatST : RingHom.Flat (algebraMap S T) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat T (N.map (algebraMap B S)))
  have hflatComp : RingHom.Flat ((algebraMap S T).comp ((algebraMap B S).comp phi)) :=
    hflat.comp hflatST
  have heq : (algebraMap S T).comp ((algebraMap B S).comp phi) =
      (algebraMap B T).comp phi := by
    ext x
    simp only [RingHom.comp_apply]
    exact (IsScalarTower.algebraMap_apply B S T (phi x)).symm
  simpa only [heq] using hflatComp

private lemma flat_localizationAtPrime_of_flat_at_comap
    {A B : Type*} [CommRing A] [CommRing B]
    (phi : A →+* B) (M : Submonoid B) (p : Ideal (Localization M)) [p.IsPrime]
    (hflat : RingHom.Flat ((algebraMap B
      (Localization.AtPrime (p.comap (algebraMap B (Localization M))))).comp phi)) :
    RingHom.Flat ((algebraMap B (Localization.AtPrime p)).comp phi) := by
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p
  have hflatComp : RingHom.Flat
      (e.toRingEquiv.toRingHom.comp ((algebraMap B
        (Localization.AtPrime (p.comap (algebraMap B (Localization M))))).comp phi)) :=
    hflat.comp (RingHom.Flat.of_bijective e.bijective)
  have heq : e.toRingEquiv.toRingHom.comp ((algebraMap B
      (Localization.AtPrime (p.comap (algebraMap B (Localization M))))).comp phi) =
      (algebraMap B (Localization.AtPrime p)).comp phi := by
    ext x
    simp [RingHom.comp_apply, e.commutes]
  simpa only [heq] using hflatComp

/-- Flatness of `B[1/g]` over `A` gives flatness of `B_q` over `A` for a prime `q` avoiding `g`. -/
private lemma flat_atPrime_of_flat_away
    {A B : Type*} [CommRing A] [CommRing B] (phi : A →+* B) (g : B) (q : Ideal B) [hq : q.IsPrime]
    (hg : g ∉ q) (hflat : RingHom.Flat ((algebraMap B (Localization.Away g)).comp phi)) :
    RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp phi) :=
  flat_atPrime_of_flat_localization phi (Submonoid.powers g) q hq
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).2 hg) hflat

/-- A topologically nilpotent element lies in every prime containing an ideal of definition. -/
private lemma mem_of_isTopologicallyNilpotent_of_le
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {J q : Ideal B} [hq : q.IsPrime] (hJ : TopologicalRing.IsIdealOfDefinition J) (hJq : J ≤ q)
    {g : B} (hg : IsTopologicallyNilpotent g) : g ∈ q := by
  obtain ⟨n, hn⟩ := hg.exists_pow_mem_of_mem_nhds (hJ.1.mem_nhds (by simp))
  exact hq.mem_of_pow_mem n (hJq hn)

/-- If `B → B_q` composed with `φ : A →+* B` is flat at every prime `q` of `B` not containing `f`,
then `B → B[1/f]` composed with `φ` is flat. -/
public lemma flat_away_of_flat_atPrime
    {A B : Type*} [CommRing A] [CommRing B]
    (phi : A →+* B) (f : B)
    (h : ∀ (q : Ideal B) [q.IsPrime], f ∉ q →
      RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp phi)) :
    RingHom.Flat ((algebraMap B (Localization.Away f)).comp phi) := by
  let S := Localization.Away f
  algebraize_only [((algebraMap B (Localization.Away f)).comp phi)]
  apply Module.flat_of_isLocalized_maximal S S (fun p => Localization.AtPrime p)
    (fun p => Algebra.linearMap S (Localization.AtPrime p))
  intro p hp
  let : p.IsPrime := hp.isPrime
  let q : Ideal B := p.comap (algebraMap B S)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  have hfnq : f ∉ q := by
    intro hmem
    have hmem' : algebraMap B S f ∈ p := hmem
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hmem'
      (IsLocalization.Away.algebraMap_isUnit f))
  have hflatp := flat_localizationAtPrime_of_flat_at_comap phi
    (Submonoid.powers f) p (h q hfnq)
  dsimp only [RingHom.Flat] at hflatp
  convert! hflatp; ext; apply Algebra.smul_def

/-- For an adic morphism of weakly admissible adic topological rings with
finitely generated ideals of definition, flatness after localization may be
tested on topologically nilpotent elements of either ring, on all primes away
from an ideal of definition, or on rig-closed primes. -/
@[stacks 0GGL]
public theorem naivelyRigFlat_tfae
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (phi : A →+* B) (_hphi_continuous : Continuous phi)
    (_hA_weaklyAdmissible : TopologicalRing.IsWeaklyAdmissible A)
    (_hB_weaklyAdmissible : TopologicalRing.IsWeaklyAdmissible B)
    (_hA_adicStar : ∃ I : Ideal A, IsAdic I ∧ I.FG)
    (_hB_adicStar : ∃ J : Ideal B, IsAdic J ∧ J.FG)
    (_hphi_adic : _root_.RingHom.IsAdic phi) :
    List.TFAE
      [ ∀ f : A, IsTopologicallyNilpotent f →
          _root_.RingHom.Flat
            ((algebraMap B (Localization.Away (phi f))).comp phi),
        ∀ g : B, IsTopologicallyNilpotent g →
          _root_.RingHom.Flat
            ((algebraMap B (Localization.Away g)).comp phi),
        ∀ (q : Ideal B) [q.IsPrime],
          (∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧ ¬ J ≤ q) →
            _root_.RingHom.Flat
              ((algebraMap B (Localization.AtPrime q)).comp phi),
        ∀ (q : Ideal B) [q.IsPrime],
          (∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧
            Rig.Ideal.IsMaximalAmongPrimesAvoiding J q) →
              _root_.RingHom.Flat
                ((algebraMap B (Localization.AtPrime q)).comp phi) ] := by
  classical
  rcases _hB_adicStar with ⟨J₀, hJ₀, hJ₀fg⟩
  have hJ₀def := isIdealOfDefinition_of_isAdic hJ₀
  rcases _hphi_adic with ⟨I₀, hI₀, hK₀⟩
  have hI₀def := isIdealOfDefinition_of_isAdic hI₀
  have hK₀def := isIdealOfDefinition_of_isAdic hK₀
  tfae_have 1 → 2 := by
    intro h g hgnil
    apply flat_away_of_flat_atPrime phi g
    intro q hq hgnq
    have hnotI : ¬ I₀ ≤ Ideal.comap phi q := fun hsub =>
      hgnq (mem_of_isTopologicallyNilpotent_of_le hK₀def (Ideal.map_le_iff_le_comap.mpr hsub) hgnil)
    obtain ⟨a, ha, hφanq⟩ := Set.not_subset.mp hnotI
    exact flat_atPrime_of_flat_away phi (phi a) q hφanq
      (h a (isTopologicallyNilpotent_of_mem_isIdealOfDefinition hI₀def ha))
  tfae_have 2 → 3 := by
    intro h q hq haway
    obtain ⟨J, hJ, hJq⟩ := haway
    obtain ⟨g, hgJ, hgq⟩ := Set.not_subset.mp hJq
    exact flat_atPrime_of_flat_away phi g q hgq
      (h g (isTopologicallyNilpotent_of_mem_isIdealOfDefinition hJ hgJ))
  tfae_have 3 → 1 := by
    intro h f hfn
    have hphiTN : IsTopologicallyNilpotent (phi f) :=
      IsTopologicallyNilpotent.map _hphi_continuous hfn
    apply flat_away_of_flat_atPrime phi (phi f)
    intro q hq hphi_not
    exact h q ⟨J₀, hJ₀def, fun hJq =>
      hphi_not (mem_of_isTopologicallyNilpotent_of_le hJ₀def hJq hphiTN)⟩
  tfae_have 3 → 4 := by
    intro h q hq ⟨J, hJ, hJmax⟩
    exact h q ⟨J, hJ, hJmax.1⟩
  tfae_have 4 → 3 := by
    intro h q hq haway
    rcases haway with ⟨J, hJ, hJq⟩
    have hJ₀q : ¬ J₀ ≤ q := by
      intro hle
      obtain ⟨n, hn, -⟩ :=
        TopologicalRing.IsIdealOfDefinition.exists_pow_le_and_pow_le hJ hJ₀def
      exact hJq fun x hx => hq.mem_of_pow_mem n (hle (hn (Ideal.pow_mem_pow hx n)))
    obtain ⟨p, hp, hqp, hJp, hmax⟩ := exists_maximal_prime_avoiding J₀ q hJ₀fg hq hJ₀q
    let : p.IsPrime := hp
    have hflatp := h p ⟨J₀, hJ₀def, hJp, hmax⟩
    have hdisj : Disjoint (p.primeCompl : Set B) (q : Set B) :=
      Set.disjoint_left.mpr (fun x hx hqmem => hx (hqp hqmem))
    exact flat_atPrime_of_flat_localization phi p.primeCompl q hq hdisj hflatp
  tfae_finish

end

end Rig

end
