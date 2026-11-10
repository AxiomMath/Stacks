module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ExtremallyDisconnectedSpectrum
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleTFAE
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.WeaklyEtale.Descent

/-!
# Finite finitely presented algebras over a w-contractible ring

A finite, finitely presented algebra over a w-contractible ring is w-contractible.

## Main results

* `AlgebraicGeometry.ProEtale.isWContractible_of_finite_of_finitePresentation`: w-contractibility
  passes along a finite and finitely presented ring map.

## Implementation notes

The proof runs the three-part characterization of Tag 0982 in both directions. For the w-locality
of `Spec B` a point and two closed specializations of it are pushed into the localization of `B`
at the (unique, by w-locality of `Spec A`) closed point of `Spec A` below them; there the base is
henselian, so Tag 04GH splits the algebra as a finite product of local rings, in which a prime
lies in exactly one factor and therefore has a unique maximal specialization. Strict henselianity
of the local rings of `B` at its maximal ideals is again Tag 04GH, the residue field extension
being finite over a separably closed field. Extremal disconnectedness of `π₀(Spec B)` is
transported to the closed points, where `B` modulo the ideal cutting out the closed points of
`Spec A` is a quasi-finite finitely presented algebra over `A` modulo that ideal, so Tag 0985
applies.

Finiteness of the ring map is `Module.Finite` and finite presentation is
`Algebra.FinitePresentation`. W-contractibility is tested in a universe containing both rings, so
the two rings need not lie in the same universe; both are lifted into that universe along
`ULift.ringEquiv`, w-contractibility being transported along a ring isomorphism because a
bijective ring map is faithfully flat and weakly étale.

## References

* [Stacks Project, Tag 0986](https://stacks.math.columbia.edu/tag/0986)
-/

@[expose] public section

open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

universe u v

/-- In a w-local space, extremal disconnectedness of the space of connected components transfers
to the closed points. -/
private theorem extremallyDisconnected_closedPoints (X : Type u) [TopologicalSpace X]
    [WLocalSpace X] (hED : ExtremallyDisconnected (ConnectedComponents X)) :
    ExtremallyDisconnected (closedPoints X) :=
  extremallyDisconnected_of_homeo (closedPointsHomeomorphConnectedComponents X).symm

/-- In a w-local space, extremal disconnectedness of the closed points transfers to the space of
connected components. -/
private theorem extremallyDisconnected_connectedComponents (X : Type u) [TopologicalSpace X]
    [WLocalSpace X] (hED : ExtremallyDisconnected (closedPoints X)) :
    ExtremallyDisconnected (ConnectedComponents X) :=
  extremallyDisconnected_of_homeo (closedPointsHomeomorphConnectedComponents X)

/-- The spectrum of a quotient ring is homeomorphic to the closed subset of the spectrum cut out
by the ideal. -/
private noncomputable def primeSpectrumQuotientHomeomorph
    {R : Type u} [CommRing R] (I : Ideal R) (Z : Set (PrimeSpectrum R))
    (hZ : PrimeSpectrum.zeroLocus (I : Set R) = Z) :
    PrimeSpectrum (R ⧸ I) ≃ₜ Z := by
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = Z := by
    rw [range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, Ideal.mk_ker, hZ]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I)
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)

/-- A local algebra which is module-finite over a strictly henselian local ring is strictly
henselian: it is henselian over a henselian base by Tag 04GH, and its residue field is finite
over the separably closed residue field of the base. -/
@[ega "IV 18.5.10" "special case"]
private lemma strictlyHenselianLocalRing_of_finite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [StrictlyHenselianLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    StrictlyHenselianLocalRing S := by
  have hS :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, v, 0} R).2.1
      S inferInstance
  have : HenselianLocalRing S := hS.1
  have : IsLocalHom (algebraMap R S) := hS.2
  exact strictlyHenselianLocalRing_of_module_finite R S

/-- For an integral algebra the closed points of the spectrum are exactly the points lying over
closed points of the base. -/
private lemma closedPoints_eq_comap_preimage
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] :
    closedPoints (PrimeSpectrum B) =
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' closedPoints (PrimeSpectrum A) := by
  ext y
  rw [Set.mem_preimage, mem_closedPoints_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal, mem_closedPoints_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact ⟨fun _ => Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) y.asIdeal,
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) y.asIdeal⟩

/-- In a w-local spectrum the ideal of the closed points cuts out exactly the closed points. -/
private lemma zeroLocus_vanishingIdeal_closedPoints (A : Type u) [CommRing A]
    [WLocalSpace (PrimeSpectrum A)] :
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A)) :
      Set A) = closedPoints (PrimeSpectrum A) := by
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (WLocalSpace.isClosed_closedPoints (X := PrimeSpectrum A)).closure_eq]

/-- If `Spec A` is w-local with extremally disconnected space of connected components and strictly
henselian local rings at its maximal ideals, then the spectrum of the base change of a finite
finitely presented `A`-algebra `B` along the quotient cutting out the closed points of `Spec A` is
extremally disconnected: that quotient has separably closed residue fields and Hausdorff
extremally disconnected spectrum, so Tag 0985 applies. -/
private theorem extremallyDisconnected_primeSpectrum_tensor_quotient
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum A)] [Module.Finite A B] [Algebra.FinitePresentation A B]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)))
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m)) :
    ExtremallyDisconnected
      (PrimeSpectrum
        ((A ⧸ PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A))) ⊗[A] B)) := by
  set I : Ideal A := PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A))
  have hzero := zeroLocus_vanishingIdeal_closedPoints A
  let eA : PrimeSpectrum (A ⧸ I) ≃ₜ closedPoints (PrimeSpectrum A) :=
    primeSpectrumQuotientHomeomorph I _ hzero
  have : T2Space (closedPoints (PrimeSpectrum A)) := t2Space_closedPoints (X := PrimeSpectrum A)
  have : T2Space (PrimeSpectrum (A ⧸ I)) := eA.symm.t2Space
  have : ExtremallyDisconnected (closedPoints (PrimeSpectrum A)) :=
    extremallyDisconnected_closedPoints (PrimeSpectrum A) hED
  have : ExtremallyDisconnected (PrimeSpectrum (A ⧸ I)) :=
    extremallyDisconnected_of_homeo eA.symm
  have hres : ∀ x : PrimeSpectrum (A ⧸ I), IsSepClosed x.asIdeal.ResidueField := by
    intro x
    let f : A →+* A ⧸ I := Ideal.Quotient.mk I
    let p : Ideal A := x.asIdeal.comap f
    have : p.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨p, inferInstance⟩).mp
        (mem_closedPoints_iff.mp (eA x).property)
    have hbij := (RingHom.surjectiveOnStalks_of_surjective
      (f := f) Ideal.Quotient.mk_surjective).residueFieldMap_bijective p x.asIdeal rfl
    have : IsSepClosed p.ResidueField := (hsh p).toIsSepClosed
    exact IsSepClosed.of_ringEquiv
      (RingEquiv.ofBijective (Ideal.ResidueField.map p x.asIdeal f rfl) hbij).symm
  exact extremallyDisconnected_primeSpectrum_of_quasiFinite (A ⧸ I) ((A ⧸ I) ⊗[A] B) hres
    inferInstance inferInstance

/-- Under the hypotheses of Tag 0982 for `A`, the closed points of the spectrum of a finite
finitely presented `A`-algebra `B` form an extremally disconnected space: they are cut out by the
extension to `B` of the ideal cutting out the closed points of `Spec A`, and the corresponding
quotient of `B` is the base change of `B` along that quotient of `A`. -/
private theorem extremallyDisconnected_closedPoints_primeSpectrum
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [WLocalSpace (PrimeSpectrum A)] [Module.Finite A B] [Algebra.FinitePresentation A B]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)))
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m)) :
    ExtremallyDisconnected (closedPoints (PrimeSpectrum B)) := by
  set I : Ideal A := PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A))
  set J : Ideal B := I.map (algebraMap A B)
  have hAzero := zeroLocus_vanishingIdeal_closedPoints A
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hzero : PrimeSpectrum.zeroLocus (J : Set B) = closedPoints (PrimeSpectrum B) := by
    ext y
    change I.map (algebraMap A B) ≤ y.asIdeal ↔ y ∈ closedPoints (PrimeSpectrum B)
    rw [Ideal.map_le_iff_le_comap]
    change I ≤ (PrimeSpectrum.comap (algebraMap A B) y).asIdeal ↔
      y ∈ closedPoints (PrimeSpectrum B)
    rw [closedPoints_eq_comap_preimage (A := A), Set.mem_preimage, ← hAzero,
      PrimeSpectrum.mem_zeroLocus]
    rfl
  let e : (B ⧸ J) ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have : ExtremallyDisconnected (PrimeSpectrum ((A ⧸ I) ⊗[A] B)) :=
    extremallyDisconnected_primeSpectrum_tensor_quotient A B hED hsh
  have : ExtremallyDisconnected (PrimeSpectrum (B ⧸ J)) :=
    extremallyDisconnected_of_homeo
      (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm
  exact extremallyDisconnected_of_homeo (primeSpectrumQuotientHomeomorph J _ hzero)

/-- In the spectrum of a finite product of local rings every point specializes to a unique closed
point: the point lies in exactly one factor, whose closed point is that specialization. -/
private lemma existsUnique_specializes_closedPoint_pi
    {ι : Type u} [Finite ι] (R : ι → Type v) [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] :
    ∀ x : PrimeSpectrum (∀ i, R i),
      ∃! c : closedPoints (PrimeSpectrum (∀ i, R i)), Specializes x c.1 := by
  classical
  intro x
  obtain ⟨i, p, hxp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq x
  let evali : (∀ i, R i) →+* R i := Pi.evalRingHom R i
  let ci : PrimeSpectrum (∀ i, R i) :=
    PrimeSpectrum.comap evali (IsLocalRing.closedPoint (R i))
  have hciClosed : IsClosed {ci} := by
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    change (Ideal.comap evali (IsLocalRing.maximalIdeal (R i))).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective evali (Function.surjective_eval i)
  have hxIdeal : x.asIdeal = p.asIdeal.comap evali :=
    (congrArg PrimeSpectrum.asIdeal hxp).symm
  have hSpec : Specializes x ci := (PrimeSpectrum.le_iff_specializes x ci).mp
    (hxIdeal.trans_le (Ideal.comap_mono (IsLocalRing.le_maximalIdeal p.2.1)))
  refine ⟨⟨ci, hciClosed⟩, hSpec, fun d hd => ?_⟩
  obtain ⟨j, q, hdq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq d.1
  let evalj : (∀ i, R i) →+* R j := Pi.evalRingHom R j
  have hdIdeal : d.1.asIdeal = q.asIdeal.comap evalj :=
    (congrArg PrimeSpectrum.asIdeal hdq).symm
  have hqmax : q.asIdeal.IsMaximal := by
    have hdmax : d.1.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal d.1).mp d.2
    have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective (f := evalj)
      (I := d.1.asIdeal) (Function.surjective_eval j) hdmax
    have hmapq : d.1.asIdeal.map evalj = q.asIdeal := by
      rw [hdIdeal, Ideal.map_comap_of_surjective evalj (Function.surjective_eval j)]
    rw [hmapq] at hmap
    exact hmap.resolve_left q.2.ne_top
  have hq : q.asIdeal = IsLocalRing.maximalIdeal (R j) := IsLocalRing.eq_maximalIdeal hqmax
  have hij : i = j := by
    by_contra hne
    have he : Pi.single j (1 : R j) ∈ x.asIdeal := by
      rw [hxIdeal]
      simp [Ideal.mem_comap, evali, Pi.evalRingHom_apply, hne]
    have he' : Pi.single j (1 : R j) ∉ d.1.asIdeal := by
      rw [hdIdeal, Ideal.mem_comap, Pi.evalRingHom_apply]
      simp [hq]
    exact he' ((PrimeSpectrum.le_iff_specializes x d.1).mpr hd he)
  subst j
  refine Subtype.ext (PrimeSpectrum.ext ?_)
  rw [hdIdeal]
  change q.asIdeal.comap evali = (IsLocalRing.closedPoint (R i)).asIdeal.comap evali
  rw [hq]
  simp [IsLocalRing.closedPoint]

/-- In a module-finite algebra over a henselian local ring any two maximal ideals containing a
common prime coincide: Tag 04GH writes the algebra as a finite product of local rings, in which a
prime has a unique maximal specialization. -/
private lemma eq_of_isMaximal_of_le_of_finite_henselian
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Module.Finite R S]
    (p m n : Ideal S) [p.IsPrime] [m.IsMaximal] [n.IsMaximal]
    (hpm : p ≤ m) (hpn : p ≤ n) : m = n := by
  obtain ⟨ι, hι, T, hT, hTalg, hThen, -, ⟨e⟩⟩ :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt.{u, v, 0} R).1
      S inferInstance
  have : Finite ι := hι
  let : ∀ i, CommRing (T i) := hT
  have : ∀ i, IsLocalRing (T i) := fun i => (hThen i).toIsLocalRing
  let f := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
  let x : PrimeSpectrum S := ⟨p, inferInstance⟩
  let c : PrimeSpectrum S := ⟨m, inferInstance⟩
  let d : PrimeSpectrum S := ⟨n, inferInstance⟩
  have hclosed (y : PrimeSpectrum S) (hy : y.asIdeal.IsMaximal) :
      IsClosed ({f y} : Set (PrimeSpectrum (∀ i, T i))) := by
    rw [← Set.image_singleton]
    exact f.isClosedMap _ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 hy)
  obtain ⟨z, -, hu⟩ := existsUnique_specializes_closedPoint_pi T (f x)
  have hm := hu ⟨f c, hclosed c inferInstance⟩
    (((PrimeSpectrum.le_iff_specializes x c).mp hpm).map f.continuous)
  have hn := hu ⟨f d, hclosed d inferInstance⟩
    (((PrimeSpectrum.le_iff_specializes x d).mp hpn).map f.continuous)
  exact congrArg PrimeSpectrum.asIdeal (f.injective (congrArg Subtype.val (hm.trans hn.symm)))

/-- The spectrum of a module-finite algebra over a ring with w-local spectrum and henselian local
rings at its maximal ideals is w-local. The closed points are those lying over closed points of
the base, so they form a closed set; for the uniqueness of closed specializations the point and
its two specializations are pushed into the localization of the algebra at the closed point of the
base below them, where the base is henselian. -/
private lemma wLocalSpace_primeSpectrum_of_finite
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [WLocalSpace (PrimeSpectrum A)]
    (hHens : ∀ (m : Ideal A) [m.IsMaximal], HenselianLocalRing (Localization.AtPrime m)) :
    WLocalSpace (PrimeSpectrum B) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  refine { eq_of_specializes := ?_, isClosed_closedPoints := ?_ }
  · intro x c d hc hd hxc hxd
    have : c.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal c).mp hc
    have : d.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal d).mp hd
    let f := PrimeSpectrum.comap (algebraMap A B)
    have hfmax (y : PrimeSpectrum B) [y.asIdeal.IsMaximal] :
        IsClosed ({f y} : Set (PrimeSpectrum A)) := by
      rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) y.asIdeal
    have hcd : f c = f d := WLocalSpace.eq_of_specializes (hfmax c) (hfmax d)
      (hxc.map (PrimeSpectrum.continuous_comap _)) (hxd.map (PrimeSpectrum.continuous_comap _))
    set m : Ideal A := (f c).asIdeal
    have : m.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (f c)).mp (hfmax c)
    let M := Algebra.algebraMapSubmonoid B m.primeCompl
    let S := Localization M
    have : HenselianLocalRing (Localization.AtPrime m) := hHens m
    have disj (q : Ideal B) (hq : q.comap (algebraMap A B) ≤ m) :
        Disjoint (M : Set B) (q : Set B) := by
      apply Set.disjoint_left.mpr
      rintro b ⟨a, ha, rfl⟩ hb
      exact ha (hq hb)
    have hcm : Disjoint (M : Set B) (c.asIdeal : Set B) := disj _ le_rfl
    have hdm : Disjoint (M : Set B) (d.asIdeal : Set B) :=
      disj _ (le_of_eq (congrArg PrimeSpectrum.asIdeal hcd.symm))
    have hxm : Disjoint (M : Set B) (x.asIdeal : Set B) :=
      disj _ (Ideal.comap_mono ((PrimeSpectrum.le_iff_specializes x c).mpr hxc))
    have : (x.asIdeal.map (algebraMap B S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M S _ x.isPrime hxm
    have : (c.asIdeal.map (algebraMap B S)).IsMaximal :=
      IsLocalization.isMaximal_of_isMaximal_disjoint M S _ hcm
    have : (d.asIdeal.map (algebraMap B S)).IsMaximal :=
      IsLocalization.isMaximal_of_isMaximal_disjoint M S _ hdm
    have heq := eq_of_isMaximal_of_le_of_finite_henselian (Localization.AtPrime m) S
      (x.asIdeal.map (algebraMap B S)) (c.asIdeal.map (algebraMap B S))
      (d.asIdeal.map (algebraMap B S))
      (Ideal.map_mono ((PrimeSpectrum.le_iff_specializes x c).mpr hxc))
      (Ideal.map_mono ((PrimeSpectrum.le_iff_specializes x d).mpr hxd))
    refine PrimeSpectrum.ext ?_
    simpa only [← Ideal.under_def,
      IsLocalization.under_map_of_isPrime_disjoint M S c.isPrime hcm,
      IsLocalization.under_map_of_isPrime_disjoint M S d.isPrime hdm] using
      congrArg (Ideal.comap (algebraMap B S)) heq
  · rw [closedPoints_eq_comap_preimage (A := A)]
    exact WLocalSpace.isClosed_closedPoints.preimage (PrimeSpectrum.continuous_comap _)

/-- The localization of a module-finite algebra at a maximal ideal is strictly henselian as soon
as the base has strictly henselian local rings at its maximal ideals: the localization is
module-finite over the local ring of the base at the maximal ideal below. -/
private lemma strictlyHenselianLocalRing_localization_of_finite
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (hsh : ∀ (m : Ideal A) [m.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime m))
    (q : Ideal B) [q.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime q) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  set m : Ideal A := q.comap (algebraMap A B)
  have : m.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q
  have : q.LiesOver m := ⟨rfl⟩
  let R := Localization.AtPrime m
  let M := Algebra.algebraMapSubmonoid B m.primeCompl
  let S := Localization M
  have : StrictlyHenselianLocalRing R := hsh m
  set Q : Ideal S := q.map (algebraMap B S)
  have : Q.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver B m S q
  have : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver m R S q
  let T := Localization.AtPrime Q
  have hT :=
    (HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt R).2.2.2
      S inferInstance inferInstance Q T
  have : Module.Finite R T := hT.2
  have hQq : Q.comap (algebraMap B S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M S inferInstance
      (Ideal.disjoint_primeCompl_of_liesOver q m)
  have : IsLocalization.AtPrime T q := by
    simpa only [hQq] using
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T Q
  let e : T ≃ₐ[B] Localization.AtPrime q := IsLocalization.algEquiv q.primeCompl _ _
  let : Algebra R (Localization.AtPrime q) := (e.toRingHom.comp (algebraMap R T)).toAlgebra
  have := Module.Finite.of_equiv_equiv (RingEquiv.refl R) e.toRingEquiv (by ext x; rfl)
  exact strictlyHenselianLocalRing_of_finite (R := R)

/-- A universe lift of a module-finite algebra is module-finite. -/
private theorem finite_uLift {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] :
    letI : Algebra (ULift.{max u v} A) (ULift.{max u v} B) :=
      ULift.algebra' A (ULift.{max u v} B)
    Module.Finite (ULift.{max u v} A) (ULift.{max u v} B) := by
  let : Algebra A (ULift.{max u v} B) := ULift.algebra
  let : Algebra (ULift.{max u v} A) (ULift.{max u v} B) := ULift.algebra' A _
  exact Module.Finite.of_equiv_equiv (ULift.ringEquiv (R := A)).symm
    (ULift.ringEquiv (R := B)).symm (by ext a; rfl)

/-- A universe lift of a finitely presented algebra is finitely presented. -/
private theorem finitePresentation_uLift {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B] :
    letI : Algebra (ULift.{max u v} A) (ULift.{max u v} B) :=
      ULift.algebra' A (ULift.{max u v} B)
    Algebra.FinitePresentation (ULift.{max u v} A) (ULift.{max u v} B) := by
  let : Algebra A (ULift.{max u v} B) := ULift.algebra
  let : Algebra (ULift.{max u v} A) A := ULift.algebra' A A
  let : Algebra (ULift.{max u v} A) (ULift.{max u v} B) := ULift.algebra' A _
  have heB : ∀ a : A, (ULift.ringEquiv (R := B)).symm (algebraMap A B a) =
      algebraMap A (ULift.{max u v} B) a := fun _ => rfl
  have hAB : Algebra.FinitePresentation A (ULift.{max u v} B) :=
    Algebra.FinitePresentation.equiv
      (AlgEquiv.ofRingEquiv (f := (ULift.ringEquiv (R := B)).symm) heB)
  have hA'A : Algebra.FinitePresentation (ULift.{max u v} A) A :=
    Algebra.FinitePresentation.equiv
      ({ toRingEquiv := ULift.ringEquiv (R := A), commutes' := fun _ => rfl } :
        ULift.{max u v} A ≃ₐ[ULift.{max u v} A] A)
  have : IsScalarTower (ULift.{max u v} A) A (ULift.{max u v} B) :=
    IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  exact Algebra.FinitePresentation.trans (ULift.{max u v} A) A (ULift.{max u v} B)

/-- W-contractibility transports along a ring isomorphism: an isomorphism is faithfully flat and
weakly étale, so a faithfully flat weakly étale algebra over the target is one over the source,
and a retraction there composes with the isomorphism to a retraction over the target. -/
public theorem isWContractible_of_ringEquiv {A : Type u} {A' : Type v} [CommRing A]
    [CommRing A'] (e : A' ≃+* A)
    (hA : ProetaleWContractible.IsWContractible.{u, max u v} A) :
    ProetaleWContractible.IsWContractible.{v, max u v} A' := by
  let f : A →+* A' := e.symm.toRingHom
  let : Algebra A A' := f.toAlgebra
  let ealg : A ≃ₐ[A] A' := { toRingEquiv := e.symm, commutes' := fun _ => rfl }
  have : IsLocalization (IsUnit.submonoid A) A := IsLocalization.self le_rfl
  have : IsLocalization (IsUnit.submonoid A) A' :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid A) ealg
  have : Algebra.WeaklyEtale A A' :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, max u v} A).1 A'
      (IsUnit.submonoid A)
  have hffAA' : Module.FaithfullyFlat A A' :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (RingHom.FaithfullyFlat.of_bijective (f := algebraMap A A') e.symm.bijective)
  intro T _ _ hweak hff
  let : Algebra A T := Algebra.compHom T f
  have : IsScalarTower A A' T := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have : Algebra.WeaklyEtale A' T := ⟨hweak.1, hweak.2⟩
  have hweakAT : Algebra.WeaklyEtale A T := Algebra.WeaklyEtale.trans A A' T
  obtain ⟨σ⟩ := hA T ⟨hweakAT.flat, hweakAT.flat_lmul'⟩ (Module.FaithfullyFlat.trans A A' T)
  refine ⟨{ toRingHom := f.comp σ.toRingHom, commutes' := fun a => ?_ }⟩
  change f (σ (algebraMap A' T a)) = a
  have hmap : algebraMap A' T a = algebraMap A T (e a) := by
    rw [IsScalarTower.algebraMap_apply A A' T (e a)]
    exact congrArg (algebraMap A' T) (e.symm_apply_apply a).symm
  rw [hmap]
  simp [f]

/-- A finite, finitely presented algebra over a w-contractible ring is w-contractible. -/
@[stacks 0986]
public theorem isWContractible_of_finite_of_finitePresentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.FinitePresentation A B]
    (hA : ProetaleWContractible.IsWContractible.{u, max u v} A) :
    ProetaleWContractible.IsWContractible.{v, max u v} B := by
  let : Algebra A (ULift.{max u v} B) := ULift.algebra
  let : Algebra (ULift.{max u v} A) (ULift.{max u v} B) := ULift.algebra' A _
  have : Module.Finite (ULift.{max u v} A) (ULift.{max u v} B) := finite_uLift (A := A) (B := B)
  have : Algebra.FinitePresentation (ULift.{max u v} A) (ULift.{max u v} B) :=
    finitePresentation_uLift (A := A) (B := B)
  have hA' := isWContractible_of_ringEquiv (ULift.ringEquiv.{u, max u v} (R := A)) hA
  obtain ⟨hwLocal, hED, hsh⟩ :=
    (wContractible_tfae.{max u v} (ULift.{max u v} A) |>.out 1 3).mp hA'
  have : WLocalSpace (PrimeSpectrum (ULift.{max u v} B)) :=
    wLocalSpace_primeSpectrum_of_finite (ULift.{max u v} A) (ULift.{max u v} B)
      fun m _ => (hsh m).toHenselianLocalRing
  have hBfeatures :
      WLocalSpace (PrimeSpectrum (ULift.{max u v} B)) ∧
        ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum (ULift.{max u v} B))) ∧
          ∀ (m : Ideal (ULift.{max u v} B)) [m.IsMaximal],
            StrictlyHenselianLocalRing (Localization.AtPrime m) :=
    ⟨inferInstance,
      extremallyDisconnected_connectedComponents (PrimeSpectrum (ULift.{max u v} B))
        (extremallyDisconnected_closedPoints_primeSpectrum (ULift.{max u v} A)
          (ULift.{max u v} B) hED hsh),
      strictlyHenselianLocalRing_localization_of_finite (ULift.{max u v} A)
        (ULift.{max u v} B) hsh⟩
  have hB' := (wContractible_tfae.{max u v} (ULift.{max u v} B) |>.out 3 1).mp hBfeatures
  exact isWContractible_of_ringEquiv (ULift.ringEquiv.{v, max u v} (R := B)).symm hB'

end AlgebraicGeometry.ProEtale

end
