module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.Ideal.Operations
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension
public import StacksFrontier.RingTheory.RelativeDimension.HorizontalDivisor
public import StacksFrontier.RingTheory.RelativeDimension.ValuationRing
public import StacksFrontier.RingTheory.Valuation.Restriction

/-!
# Closed points between two points of a fibre

Let `f : X ⟶ S` be locally of finite type, let `x ⤳ x'` be a specialization in `X`, set
`s = f x`, and assume `x'` is closed in its own fibre `X_{f x'}`. Stacks 053U asserts that the
points of `X_s` which are closed in `X_s` and lie between `x` and `x'` are dense in the closure
of `x` in `X_s`. This file proves it, and determines exactly when it holds.

## Main results

* `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`: **Stacks 053U**, under the
  tag's own hypotheses and no others: the density conclusion of the tag holds if and only if
  `x = x'` or `f x ≠ f x'`.
* `AlgebraicGeometry.closure_closedPoints_between_fiber_eq`: the density conclusion itself, in
  both of those cases, by the argument of the source. This is the mathematical content of the
  tag and the reverse implication of the result above.

## When the density conclusion holds

A nontrivial specialization inside one fibre is the one situation admitted by the hypotheses of
Stacks 053U in which its conclusion fails, and `closure_closedPoints_between_fiber_eq_iff`
settles it: there the set of the tag is `{x'}`, whose closure is `{x'}`, while the closure of
`x` in `X_s` is larger as soon as `x ≠ x'` — for `X = 𝔸¹` over a field with `x` its generic
point and `x'` a closed point of it the set of the tag is a single closed point and the closure
of `x` is all of `𝔸¹`. That computation is carried out, not asserted, in
`AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`
(`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibres`): when `x'` lies in the
fibre of `x`, the conclusion of the tag forces the closure of `x` in `X_s` to be contained in a
single point. The source relates `f x` and `f x'` by no hypothesis, so this is a gap in its
statement and not an artefact of the formalization.

The proof of the source draws the same line: its prime-avoidance step chooses `g` in the
maximal ideal of `x'` outside the primes of the components of the closed set to be avoided,
which is possible only because those primes do not contain `𝔪_A B`, i.e. because `s ≠ s'`.

## Implementation notes

The proof follows the source. The specialization `x ⤳ x'` is presented by a valuation ring
(`exists_valuation_ring_of_specialization`, from Mathlib's valuative criterion material), the
base is replaced by the spectrum of the valuation subring `A = B ∩ κ(s)`
(`exists_restricted_valuation_local_factor`), and the statement is proved there by induction on
the dimension of the fibre at `x`. The inductive step cuts the closure of `x` by a principal
divisor avoiding the components of the special fibre and the closed set to be avoided, and the
divisor is shown to meet the generic fibre by Stacks 053S,
`IsLocalRing.injective_quotient_of_dimension_add_trdeg_eq` — which is why 053S is needed with no
Noetherian hypothesis on the base: the base here is a valuation ring.

The three steps of the argument are separate declarations, each stated in terms of the data it
uses rather than nested inside the next:

* `exists_gt_mem_of_not_isMaximal`: the extension step, purely about ideals of `C` and of its
  generic fibre `F`, which is where Stacks 053S is applied;
* `exists_closed_specialization_affine_integral`: the step over a valuation ring with an integral
  affine source, which is the source's reduced situation;
* `exists_closed_specialization_near_distinct_base`: the reduction of the general case to it.

Keeping them apart is also what lets each elaborate inside the default heartbeat budget.

Points of `X_s` are `f.fiber s`, carried back to `X` by `f.fiberι s`, with `f.asFiber x` the
canonical point of `f.fiber (f x)` over `x`. Density in the closure of `x` in `X_s` is written
as an equality of closures, which also records the containment.

## References

* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
* [Stacks Project, Tag 053S](https://stacks.math.columbia.edu/tag/053S)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry

/-- Prime avoidance at a maximal ideal: a maximal ideal `q` has an element lying in none of
finitely many primes other than `q`. This is Stacks 00DS, `Ideal.subset_union_prime`, in its
contrapositive form: `q` is contained in none of the primes, since it is maximal and they are
proper and distinct from it. -/
@[sga "3 V 4.1" "x maximal"]
private lemma exists_mem_maximal_avoid_finite_primes
    {B : Type u} [CommRing B] (q : Ideal B) [q.IsMaximal]
    (t : Finset (Ideal B))
    (ht : ∀ p ∈ t, p.IsPrime ∧ p ≠ q) :
    ∃ g ∈ q, ∀ p ∈ t, g ∉ p := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (q : Set B) ⊆ ⋃ p ∈ (t : Set (Ideal B)), (p : Set B) := fun g hg ↦ by
    obtain ⟨p, hp, hgp⟩ := hcon g hg
    exact Set.mem_biUnion hp hgp
  obtain ⟨p, hp, hqp⟩ :=
    (Ideal.subset_union_prime (f := fun p : Ideal B ↦ p) q q
      (fun p hp _ _ ↦ (ht p hp).1)).mp hsub
  exact (ht p hp).2 (‹q.IsMaximal›.eq_of_le (ht p hp).1.ne_top hqp).symm

private lemma topologicalKrullDim_le_zero_of_equidimensional_singleton_component
    (X : Type*) [TopologicalSpace X] (hX : TopologicalSpace.Equidimensional X)
    (x : X) (hcomp : ({x} : Set X) ∈ irreducibleComponents X) :
    topologicalKrullDim X ≤ 0 := by
  have : DiscreteTopology ({x} : Set X) := Subsingleton.discreteTopology
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup_le fun W ↦ iSup_le fun hW ↦ ?_
  exact (hX W hW {x} hcomp).le.trans
    (topologicalKrullDim_zero_of_discreteTopology ({x} : Set X))

private lemma maximal_not_minimal_of_equidimensional_positive
    {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]
    (hequi : TopologicalSpace.Equidimensional (PrimeSpectrum R))
    (hpos : 0 < ringKrullDim R) : q ∉ minimalPrimes R := by
  intro hmin
  let x : PrimeSpectrum R := ⟨q, inferInstance⟩
  have hzero : PrimeSpectrum.zeroLocus (q : Set R) = {x} := by
    ext y
    constructor
    · exact fun hy ↦ PrimeSpectrum.ext (‹q.IsMaximal›.eq_of_le y.isPrime.ne_top hy).symm
    · rintro ⟨rfl⟩
      exact le_refl q
  have hcomp : ({x} : Set (PrimeSpectrum R)) ∈
      irreducibleComponents (PrimeSpectrum R) := by
    rw [← hzero, ← PrimeSpectrum.zeroLocus_minimalPrimes]
    exact ⟨q, hmin, by simp⟩
  have hdim : ringKrullDim R ≤ 0 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_le_zero_of_equidimensional_singleton_component
      (PrimeSpectrum R) hequi x hcomp
  exact (not_lt_of_ge hdim) hpos

private lemma principal_minimal_prime_avoids_nonzero_prime
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (g : R) (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hp : p ∈ (Ideal.span {g}).minimalPrimes)
    (hq : q ≠ ⊥) (hgq : g ∉ q) : ¬ q ≤ p := by
  intro hqp
  by_cases heq : q = p
  · rw [heq] at hgq
    exact hgq (hp.le (Ideal.mem_span_singleton_self g))
  have hlt : q < p := lt_of_le_of_ne hqp heq
  have hpheight : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {g}) p hp
  exact hq (Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp
    ((Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le hpheight)))

private lemma algebraMapSubmonoid_nonZeroDivisors_le
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (h : Function.Injective (algebraMap R S)) :
    Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S := by
  rintro x ⟨r, hr, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h₀ =>
    mem_nonZeroDivisors_iff_ne_zero.mp hr (h (by simpa using h₀))

private alias isDomain_generic_fiber :=
  Stacks.RelativeDimension.ValuationFibres.isDomain_fiber_bot

private lemma topologicalKrullDim_pos_of_nonclosed_genericPoint
    (X : Type*) [TopologicalSpace X] [T0Space X] (η : X)
    (hη : IsGenericPoint η (Set.univ : Set X))
    (hnot : ¬ IsClosed ({η} : Set X)) :
    0 < topologicalKrullDim X := by
  obtain ⟨y, hy⟩ : ∃ y : X, y ≠ η := by
    by_contra h
    push Not at h
    have huniv : ({η} : Set X) = Set.univ := by
      ext y
      simp [h y]
    exact hnot (huniv ▸ isClosed_univ)
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure ({y} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let W : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, hη.isIrreducible, isClosed_univ⟩
  have hZW : Z < W := by
    refine lt_of_le_of_ne (Set.subset_univ _) fun heq ↦ ?_
    have hygen : IsGenericPoint y (Set.univ : Set X) := by
      change closure ({y} : Set X) = Set.univ
      exact congrArg (fun T : TopologicalSpace.IrreducibleCloseds X => (T : Set X)) heq
    exact hy (hygen.eq hη)
  exact Order.krullDim_pos_iff.mpr ⟨Z, W, hZW⟩

/-- The residue field at the zero prime of a domain `A` is any fraction field `K` of `A`. -/
private noncomputable def zeroResidueFieldEquiv {A : Type u} (K : Type u) [CommRing A]
    [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (η : PrimeSpectrum A)
    (hη : η = ⊥) :
    η.asIdeal.ResidueField ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv
    ((Ideal.quotientEquiv η.asIdeal ⊥ (RingEquiv.refl A) (by simp [hη])).trans
      (RingEquiv.quotientBot A))

private noncomputable def genericResidueFractionEquiv
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of L) : FractionRing A ≃+* L :=
  (zeroResidueFieldEquiv (FractionRing A) _ (genericPoint_eq_bot_of_affine _)).symm.trans
    ((Scheme.Spec.residueFieldIso (.of A) _).symm.commRingCatIsoToRingEquiv.trans
      e.commRingCatIsoToRingEquiv)

private noncomputable def valuationSubringOfGenericResidueIso
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of L) : ValuationSubring L :=
  ((ValuationRing.valuation A (FractionRing A)).valuationSubring).comap
    (genericResidueFractionEquiv e).symm.toRingHom

private lemma mem_valuationSubringOfGenericResidueIso_iff
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of L) (z : L) :
    z ∈ valuationSubringOfGenericResidueIso e ↔
      ∃ a : A, genericResidueFractionEquiv e
        (algebraMap A (FractionRing A) a) = z := by
  change (genericResidueFractionEquiv e).symm z ∈
      (ValuationRing.valuation A (FractionRing A)).integer ↔ _
  rw [ValuationRing.mem_integer_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha, RingEquiv.apply_symm_apply]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha, RingEquiv.symm_apply_apply]⟩

private lemma genericPoint_eq_closedPoint_of_isField {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] (h : IsField A) : genericPoint (Spec (.of A)) = IsLocalRing.closedPoint A := by
  apply PrimeSpectrum.ext
  rw [AlgebraicGeometry.genericPoint_eq_bot_of_affine]
  exact (IsLocalRing.isField_iff_maximalIdeal_eq.mp h).symm

private lemma valuationSubringOfGenericResidueIso_ne_top
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of L)
    (hηne : genericPoint (Spec (.of A)) ≠ IsLocalRing.closedPoint A) :
    valuationSubringOfGenericResidueIso e ≠ ⊤ := by
  intro htop
  have hsurj : Function.Surjective (algebraMap A (FractionRing A)) := by
    intro z
    have hz : genericResidueFractionEquiv e z ∈
        valuationSubringOfGenericResidueIso e := by
      rw [htop]
      trivial
    obtain ⟨a, ha⟩ := (mem_valuationSubringOfGenericResidueIso_iff e _).mp hz
    exact ⟨a, (genericResidueFractionEquiv e).injective ha⟩
  exact hηne (genericPoint_eq_closedPoint_of_isField
    (IsFractionRing.surjective_iff_isField.mp hsurj))

private noncomputable def valuationRingEquivSubring
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field L]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of L) : A ≃+* valuationSubringOfGenericResidueIso e := by
  let B := valuationSubringOfGenericResidueIso e
  let φ : A →+* B :=
    ((genericResidueFractionEquiv e).toRingHom.comp
      (algebraMap A (FractionRing A))).codRestrict B.toSubring (fun a =>
        (mem_valuationSubringOfGenericResidueIso_iff e _).mpr ⟨a, rfl⟩)
  refine RingEquiv.ofBijective φ ⟨?_, ?_⟩
  · exact fun a b hab => IsFractionRing.injective A (FractionRing A)
      ((genericResidueFractionEquiv e).injective (congrArg Subtype.val hab))
  · intro b
    obtain ⟨a, ha⟩ := (mem_valuationSubringOfGenericResidueIso_iff e b).mp b.2
    exact ⟨a, Subtype.ext ha⟩

private noncomputable def restrictedValuationSubring
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
      CommRingCat.of (X.residueField x)) :
    ValuationSubring (S.residueField (f x)) := by
  letI : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  exact intersectionSubring (K := S.residueField (f x))
    (valuationSubringOfGenericResidueIso e)

private lemma valuationSubringCap_local_factor
    {R K L : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) (i : R →+* K) (j : R →+* B)
    (hlocal : IsLocalHom j)
    (hcomp : (algebraMap K L).comp i = B.subtype.comp j) :
    ∃ jA : R →+* intersectionSubring (K := K) B,
      IsLocalHom jA ∧
        (intersectionSubring (K := K) B).subtype.comp jA = i := by
  let A := intersectionSubring (K := K) B
  let jA : R →+* A := i.codRestrict A.toSubring (fun r => by
    change algebraMap K L (i r) ∈ B
    exact (congrArg (fun h : R →+* L => h r) hcomp) ▸ (j r).2)
  let k : A →+* B := ((algebraMap K L).comp A.subtype).codRestrict
    B.toSubring (fun a => a.2)
  have hkj : k.comp jA = j := by
    ext r
    exact congrArg (fun h : R →+* L => h r) hcomp
  have : IsLocalHom (k.comp jA) := hkj ▸ hlocal
  exact ⟨jA, isLocalHom_of_comp jA k, RingHom.ext fun _ => rfl⟩

private lemma stalkSpecializes_residue_comp_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    {x x' : X} (hxx' : x ⤳ x') :
    (S.presheaf.stalkSpecializes (hxx'.map f.continuous) ≫ S.residue (f x)) ≫
        f.residueFieldMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes hxx' ≫ X.residue x := by
  rw [Category.assoc, Scheme.residue_residueFieldMap]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ X.residue x) (Scheme.Hom.stalkSpecializes_stalkMap f x x' hxx')

private lemma exists_restricted_valuation_local_factor
    {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X)
    (hxx' : x ⤳ x') :
    ∃ (B : ValuationSubring (X.residueField x)),
      ∃ (jX : X.presheaf.stalk x' →+* B),
      IsLocalHom jX ∧
        B.subtype.comp jX =
          (X.presheaf.stalkSpecializes hxx' ≫ X.residue x).hom ∧
      letI : Algebra (S.residueField (f x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      ∃ (j : S.presheaf.stalk (f x') →+*
          intersectionSubring (K := S.residueField (f x)) B),
        IsLocalHom j ∧
          (intersectionSubring (K := S.residueField (f x)) B).subtype.comp j =
            (S.presheaf.stalkSpecializes (hxx'.map f.continuous) ≫
              S.residue (f x)).hom := by
  let hs : f x ⤳ f x' := hxx'.map f.continuous
  let α : X.presheaf.stalk x' ⟶ CommRingCat.of (X.residueField x) :=
    X.presheaf.stalkSpecializes hxx' ≫ X.residue x
  let β : S.presheaf.stalk (f x') ⟶ CommRingCat.of (S.residueField (f x)) :=
    S.presheaf.stalkSpecializes hs ≫ S.residue (f x)
  obtain ⟨B, hB, hBlocal⟩ := IsLocalRing.exists_factor_valuationRing α.hom
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hcomm : β ≫ f.residueFieldMap x = f.stalkMap x' ≫ α :=
    stalkSpecializes_residue_comp_residueFieldMap f hxx'
  let jX : X.presheaf.stalk x' →+* B := α.hom.codRestrict B.toSubring hB
  let jB : S.presheaf.stalk (f x') →+* B := jX.comp (f.stalkMap x').hom
  have hlocalB : IsLocalHom jB := by
    have : IsLocalHom jX := hBlocal
    infer_instance
  have hcomp : (algebraMap (S.residueField (f x)) (X.residueField x)).comp β.hom =
      B.subtype.comp jB :=
    RingHom.ext fun r => congrArg (fun h : S.presheaf.stalk (f x') ⟶
        CommRingCat.of (X.residueField x) => h r) hcomm
  obtain ⟨j, hj, hβ⟩ := valuationSubringCap_local_factor B β.hom jB hlocalB hcomp
  exact ⟨B, jX, hBlocal, rfl, j, hj, hβ⟩

/-- An injective ring map of domains sends the generic point of `Spec B` to that of `Spec A`. -/
private lemma comap_genericPoint_eq_of_injective {A B : Type u} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (k : A →+* B) (hk : Function.Injective k) :
    Spec.map (CommRingCat.ofHom k) (genericPoint (Spec (.of B))) = genericPoint (Spec (.of A)) := by
  apply PrimeSpectrum.ext
  change Ideal.comap k (genericPoint (Spec (.of B))).asIdeal = _
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  exact Ideal.comap_bot_of_injective k hk

private lemma valuation_local_factor_maps_endpoints
    {S : Scheme.{u}} {s s' : S} (h : s ⤳ s')
    (C : ValuationSubring (S.residueField s))
    (j : S.presheaf.stalk s' →+* C) (hjlocal : IsLocalHom j)
    (hj : C.subtype.comp j =
      (S.presheaf.stalkSpecializes h ≫ S.residue s).hom) :
    let g : Spec (.of C) ⟶ S :=
      Spec.map (CommRingCat.ofHom j) ≫ S.fromSpecStalk s'
    g (IsLocalRing.closedPoint C) = s' ∧
      g (genericPoint (Spec (.of C))) = s ∧
        Spec.map (CommRingCat.ofHom C.subtype) ≫ g =
          S.fromSpecResidueField s := by
  let g : Spec (.of C) ⟶ S :=
    Spec.map (CommRingCat.ofHom j) ≫ S.fromSpecStalk s'
  have hclosed : g (IsLocalRing.closedPoint C) = s' := by
    dsimp only [g]
    change S.fromSpecStalk s' (PrimeSpectrum.comap j (IsLocalRing.closedPoint C)) = s'
    rw [IsLocalRing.comap_closedPoint j, Scheme.fromSpecStalk_closedPoint]
  let q : Spec (.of (S.residueField s)) ⟶ Spec (.of C) :=
    Spec.map (CommRingCat.ofHom C.subtype)
  have hq : q (IsLocalRing.closedPoint (S.residueField s)) =
      genericPoint (Spec (.of C)) := by
    rw [← genericPoint_eq_closedPoint_of_isField (Field.toIsField _)]
    exact comap_genericPoint_eq_of_injective _ fun _ _ h => Subtype.ext h
  have hqg : q ≫ g = S.fromSpecResidueField s := by
    calc
      q ≫ g = Spec.map (CommRingCat.ofHom (C.subtype.comp j)) ≫
          S.fromSpecStalk s' := by
            simp only [q, g, ← Spec.map_comp_assoc, CommRingCat.ofHom_comp]
      _ = Spec.map (S.presheaf.stalkSpecializes h ≫ S.residue s) ≫
          S.fromSpecStalk s' := by
            rw [hj]
            rfl
      _ = S.fromSpecResidueField s := by
        rw [Scheme.fromSpecResidueField]
        calc
          _ = Spec.map (S.residue s) ≫
              (Spec.map (S.presheaf.stalkSpecializes h) ≫ S.fromSpecStalk s') :=
            Scheme.Spec.map_comp_assoc _ _ _
          _ = Spec.map (S.residue s) ≫ S.fromSpecStalk s :=
            congrArg _ (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h)
  have hgeneric : g (genericPoint (Spec (.of C))) = s := by
    have h := congrArg (fun k : Spec (.of (S.residueField s)) ⟶ S =>
      k (IsLocalRing.closedPoint (S.residueField s))) hqg
    change g (q (IsLocalRing.closedPoint (S.residueField s))) = _ at h
    rw [hq] at h
    exact h.trans (Scheme.fromSpecResidueField_apply s _)
  exact ⟨hclosed, hgeneric, hqg⟩

private lemma genericPoint_eq_closedPoint_of_valuationSubring_eq_top
    {K : Type u} [Field K] (C : ValuationSubring K) (hC : C = ⊤) :
    genericPoint (Spec (.of C)) = IsLocalRing.closedPoint C := by
  have hsurj : Function.Surjective (algebraMap C K) := by
    intro z
    change ∃ c : C, (c : K) = z
    exact ⟨⟨z, by simp [hC]⟩, rfl⟩
  exact genericPoint_eq_closedPoint_of_isField (IsFractionRing.surjective_iff_isField.mp hsurj)

private noncomputable def genericResidueIsoOfValuationSubring
    {K : Type u} [Field K] (C : ValuationSubring K) :
    (Spec (.of C)).residueField (genericPoint (Spec (.of C))) ≅
      CommRingCat.of K :=
  Scheme.Spec.residueFieldIso (.of C) _ ≪≫
    (zeroResidueFieldEquiv K _ (genericPoint_eq_bot_of_affine _)).toCommRingCatIso

private lemma specMap_subtype_eq_genericResidueIso
    {K : Type u} [Field K] (C : ValuationSubring K) :
    Spec.map (CommRingCat.ofHom C.subtype) =
      Spec.map (genericResidueIsoOfValuationSubring C).hom ≫
        (Spec (.of C)).fromSpecResidueField (genericPoint (Spec (.of C))) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [← Spec.map_comp]
  rw [Spec.map_inj]
  ext a
  simp only [genericResidueIsoOfValuationSubring, Iso.trans_hom, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply]
  change C.subtype a = zeroResidueFieldEquiv K _ _ (algebraMap C _ a)
  rw [← Ideal.algebraMap_quotient_residueField_mk]
  unfold zeroResidueFieldEquiv
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp [ValuationSubring.subtype, ValuationSubring.subtype]
  rfl

private lemma exists_valuation_ring_of_specialization
    {X : Scheme.{u}} (x x' : X) (hxx' : x ⤳ x') :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (φ : Spec (.of A) ⟶ X)
      (e : (Spec (.of A)).residueField (genericPoint (Spec (.of A))) ≅
        CommRingCat.of (X.residueField x))
      (hη : φ (genericPoint (Spec (.of A))) = x),
      φ (IsLocalRing.closedPoint A) = x' ∧
        (X.residueFieldCongr hη).inv ≫
          φ.residueFieldMap (genericPoint (Spec (.of A))) ≫ e.hom = 𝟙 _ :=
  AlgebraicGeometry.exists_valuation_ring_of_specializes X hxx' (X.residueField x) (𝟙 _)

private lemma fiber_specialization_mem_closure_asFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (y : f.fiber (f x))
    (hxy : x ⤳ (f.fiberι (f x) y)) :
    y ∈ closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  rw [← specializes_iff_mem_closure]
  apply (f.fiberι (f x)).isEmbedding.specializes_iff.mp
  simpa only [Scheme.Hom.fiberι_asFiber] using hxy

private lemma intermediate_closed_points_subset_closure
    {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X) :
    {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y) ∧
          (f.fiberι (f x) y) ⤳ x'} ⊆
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  fun y hy ↦ fiber_specialization_mem_closure_asFiber f x y hy.2.1

private lemma closed_points_specializing_from_dense
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    closure {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y)} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  let Z : Set (f.fiber (f x)) := closure ({f.asFiber x} : Set (f.fiber (f x)))
  have hset : {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y)} =
      Z ∩ closedPoints (f.fiber (f x)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_closedPoints_iff]
    constructor
    · rintro ⟨hy, hxy⟩
      exact ⟨fiber_specialization_mem_closure_asFiber f x y hxy, hy⟩
    · rintro ⟨hy, hclosed⟩
      refine ⟨hclosed, ?_⟩
      simpa only [Scheme.Hom.fiberι_asFiber] using
        (f.fiberι (f x)).isEmbedding.specializes_iff.mpr (specializes_iff_mem_closure.mpr hy)
  rw [hset]
  exact JacobsonSpace.closure_inter_closedPoints isClosed_closure

private lemma exists_closed_specialization_in_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (U : Set (f.fiber (f x))) (hU : IsOpen U) (hxU : f.asFiber x ∈ U) :
    ∃ y : f.fiber (f x), y ∈ U ∧
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y) := by
  have hx : f.asFiber x ∈ closure {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y)} := by
    rw [closed_points_specializing_from_dense]
    exact subset_closure (Set.mem_singleton _)
  exact (mem_closure_iff.mp hx) U hU hxU

private noncomputable def fiberHomeoOfEq {X S : Scheme.{u}} (f : X ⟶ S)
    {s t : S} (h : s = t) : f.fiber s ≃ₜ f.fiber t := by
  cases h
  exact Homeomorph.refl _

private lemma fiberHomeoOfEq_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    {s t : S} (h : s = t) (z : f.fiber s) :
    f.fiberι t (fiberHomeoOfEq f h z) = f.fiberι s z := by
  cases h
  rfl

/-- A point of a fibre is closed in it iff its canonical point in its own fibre is. -/
private lemma isClosed_asFiber_fiberι_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (w : f.fiber s) :
    IsClosed ({f.asFiber (f.fiberι s w)} : Set (f.fiber (f (f.fiberι s w)))) ↔
      IsClosed ({w} : Set (f.fiber s)) := by
  let v := f.fiberι s w
  have hv : f v = s := (f.fiberHomeo s w).2
  let e : f.fiber s ≃ₜ f.fiber (f v) := fiberHomeoOfEq f hv.symm
  have he : e w = f.asFiber v := by
    apply (f.fiberι (f v)).isEmbedding.injective
    rw [fiberHomeoOfEq_fiberι]
    simp [v]
  have := e.isClosed_image (s := {w})
  rwa [Set.image_singleton, he] at this

private lemma isClosed_point_of_closed_asFiber_over_closed_base
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hx : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hs : IsClosed ({f x} : Set S)) : IsClosed ({x} : Set X) := by
  let W : Set X := f ⁻¹' {f x}
  have hW : IsClosed W := hs.preimage f.continuous
  let e := f.fiberHomeo (f x)
  have he : e (f.asFiber x) = (⟨x, rfl⟩ : W) := by
    apply Subtype.ext
    simp [e]
  have hclosedW : IsClosed ({(⟨x, rfl⟩ : W)} : Set W) := by
    rw [← he]
    simpa only [Set.image_singleton] using e.isClosed_image.mpr hx
  simpa only [Set.image_singleton] using hW.isClosedEmbedding_subtypeVal.isClosedMap _ hclosedW

private lemma isClosed_asFiber_of_isEmbedding
    {Z X S : Scheme.{u}} (i : Z ⟶ X) (hi : Topology.IsEmbedding i)
    (f : X ⟶ S) (z : Z)
    (hclosed : IsClosed ({f.asFiber (i z)} : Set (f.fiber (f (i z))))) :
    IsClosed ({(i ≫ f).asFiber z} : Set ((i ≫ f).fiber ((i ≫ f) z))) := by
  let g := i ≫ f
  have hbase (w : g.fiber (g z)) :
      f (i (g.fiberι (g z) w)) = f (i z) := by
    have hfac := congrArg (fun m : g.fiber (g z) ⟶ S => m w)
      (g.fiber_fac (g z))
    change f (i (g.fiberι (g z) w)) =
      S.fromSpecResidueField (g z) (g.fiberToSpecResidueField (g z) w) at hfac
    rwa [Scheme.fromSpecResidueField_apply] at hfac
  let j : g.fiber (g z) → f.fiber (f (i z)) := fun w =>
    (f.fiberHomeo (f (i z))).symm ⟨i (g.fiberι (g z) w), hbase w⟩
  have hjcont : Continuous j := (f.fiberHomeo (f (i z))).symm.continuous.comp
    ((i.continuous.comp (g.fiberι (g z)).continuous).subtype_mk _)
  have hjpre : j ⁻¹' {f.asFiber (i z)} = {g.asFiber z} := by
    ext w
    constructor
    · intro (hw' : j w = f.asFiber (i z))
      have hiw : i (g.fiberι (g z) w) = i z := by
        simpa [j] using congrArg (f.fiberι (f (i z))) hw'
      have hwz : g.fiberι (g z) w = z := hi.injective hiw
      exact Set.mem_singleton_iff.mpr
        ((g.fiberι (g z)).isEmbedding.injective (by
          simpa only [Scheme.Hom.fiberι_asFiber] using hwz))
    · rintro rfl
      apply Set.mem_singleton_iff.mpr
      apply (f.fiberι (f (i z))).isEmbedding.injective
      simp [j]
  rw [← hjpre]
  exact hclosed.preimage hjcont

private lemma isClosed_asFiber_image
    {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)] (z : Z)
    (hclosed : IsClosed
      ({(i ≫ f).asFiber z} : Set ((i ≫ f).fiber ((i ≫ f) z)))) :
    IsClosed ({f.asFiber (i z)} : Set (f.fiber (f (i z)))) := by
  let K := S.residueField (f (i z))
  let L := X.residueField (i z)
  let M := Z.residueField z
  let : Algebra K L := (f.residueFieldMap (i z)).hom.toAlgebra
  let : Algebra L M := (i.residueFieldMap z).hom.toAlgebra
  let : Algebra K M := ((i ≫ f).residueFieldMap z).hom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i f z))
  have : Module.Finite K M :=
    (AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField (i ≫ f) z).mp hclosed
  exact (AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField f (i z)).mpr
    (FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
      (RingHom.injective (i.residueFieldMap z).hom))

private lemma dense_of_closed_specializations_in_every_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X)
    (h : ∀ U : Set (f.fiber (f x)), IsOpen U → f.asFiber x ∈ U →
      ∃ y : f.fiber (f x), y ∈ U ∧
        IsClosed ({y} : Set (f.fiber (f x))) ∧
          x ⤳ (f.fiberι (f x) y) ∧
            (f.fiberι (f x) y) ⤳ x') :
    closure {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y) ∧
          (f.fiberι (f x) y) ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  le_antisymm
    (closure_minimal (intermediate_closed_points_subset_closure f x x') isClosed_closure)
    (closure_minimal (Set.singleton_subset_iff.mpr (mem_closure_iff.mpr h)) isClosed_closure)

private lemma dense_of_initial_point_closed_in_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X)
    (hxx' : x ⤳ x')
    (hx : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    closure {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y) ∧
          (f.fiberι (f x) y) ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  dense_of_closed_specializations_in_every_neighborhood f x x' fun U _ hxU =>
    ⟨f.asFiber x, hxU, hx, by simpa only [Scheme.Hom.fiberι_asFiber] using specializes_refl x,
      by simpa only [Scheme.Hom.fiberι_asFiber] using hxx'⟩

private lemma disjoint_algebraMapSubmonoid_of_comap_eq_bot {A C : Type*} [CommRing A]
    [Nontrivial A] [CommRing C] [Algebra A C] {p : Ideal C}
    (hp : p.comap (algebraMap A C) = ⊥) :
    Disjoint (Algebra.algebraMapSubmonoid C (nonZeroDivisors A) : Set C) p := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨a, ha, rfl⟩ hap
  have h : a ∈ p.comap (algebraMap A C) := hap
  rw [hp, Ideal.mem_bot] at h
  exact nonZeroDivisors.ne_zero ha h

private lemma exists_prime_gt_of_prime_quotient
    {A₁ C F : Type*} [CommRing A₁] [Nontrivial A₁] [CommRing C] [Algebra A₁ C]
    [CommRing F] [Algebra C F] (M : Submonoid C) [IsLocalization M F]
    (hMdef : M = Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁))
    (q : Ideal C) (c : C) (P : Ideal F)
    (hPq : P.comap (algebraMap C F) ≤ q)
    (j : Ideal (C ⧸ P.comap (algebraMap C F))) (hj : j.IsPrime)
    (hjq : j ≤ q.map (Ideal.Quotient.mk _))
    (hjA : (j.comap (Ideal.Quotient.mk _)).comap (algebraMap A₁ C) = ⊥)
    (hcj : Ideal.Quotient.mk _ c ∉ j) (hjne : j ≠ ⊥) :
    ∃ Q ∈ {Q : Ideal F | Q.IsPrime ∧ Q.comap (algebraMap C F) ≤ q ∧
      algebraMap C F c ∉ Q}, P < Q := by
  let π := Ideal.Quotient.mk (P.comap (algebraMap C F))
  let pNew : Ideal C := j.comap π
  have : pNew.IsPrime := Ideal.IsPrime.comap π
  have hp₂pNew : P.comap (algebraMap C F) < pNew := by
    have h := (Ideal.orderEmbeddingOfSurjective π
      Ideal.Quotient.mk_surjective).strictMono (bot_lt_iff_ne_bot.mpr hjne)
    change (⊥ : Ideal _).comap π < pNew at h
    rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  have hpNewq : pNew ≤ q := (Ideal.comap_mono hjq).trans_eq (Ideal.comap_map_mk hPq)
  have hpNewDisj : Disjoint (M : Set C) pNew := by
    rw [hMdef]
    exact disjoint_algebraMapSubmonoid_of_comap_eq_bot hjA
  let QNew : Ideal F := pNew.map (algebraMap C F)
  have hQNewUnder : QNew.comap (algebraMap C F) = pNew :=
    IsLocalization.under_map_of_isPrime_disjoint M F inferInstance hpNewDisj
  refine ⟨QNew, ⟨IsLocalization.isPrime_of_isPrime_disjoint M F pNew inferInstance hpNewDisj,
    hQNewUnder.symm ▸ hpNewq, fun hc => hcj ?_⟩, lt_of_le_of_ne ?_ fun heq => ?_⟩
  · have hh : c ∈ QNew.comap (algebraMap C F) := hc
    rwa [hQNewUnder] at hh
  · have hh : (P.comap (algebraMap C F)).map (algebraMap C F) ≤ QNew :=
      Ideal.map_mono hp₂pNew.le
    change Ideal.map (algebraMap C F) (Ideal.under C P) ≤ QNew at hh
    rwa [IsLocalization.map_under M F P] at hh
  · have hh := congrArg (fun I : Ideal F => I.comap (algebraMap C F)) heq
    rw [hQNewUnder] at hh
    exact (ne_of_gt hp₂pNew) hh.symm

private lemma flat_of_injective_algebraMap {A B : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr h
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

private lemma injective_quotient_span_algebraMap_localization_atPrime
    {A₁ C : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁]
    [CommRing C] [IsDomain C] [Algebra A₁ C] [Algebra.FiniteType A₁ C]
    (hαinj : Function.Injective (algebraMap A₁ C)) (q : Ideal C) [q.IsMaximal]
    (hqover : q.comap (algebraMap A₁ C) = IsLocalRing.maximalIdeal A₁) (g : C) (hgq : g ∈ q)
    (hnot : ∀ p ∈ ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ C)).minimalPrimes,
      g ∉ p) :
    Function.Injective
      ((Ideal.Quotient.mk (Ideal.span {algebraMap C (Localization.AtPrime q) g})).comp
        (algebraMap A₁ (Localization.AtPrime q))) := by
  let D := Localization.AtPrime q
  have : IsScalarTower A₁ C D := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hαDinj : Function.Injective (algebraMap A₁ D) :=
    (IsLocalization.injective D q.primeCompl_le_nonZeroDivisors).comp hαinj
  have : Module.Flat A₁ C := flat_of_injective_algebraMap hαinj
  have : Module.Flat A₁ D := Module.Flat.trans A₁ C D
  have : IsLocalHom (algebraMap A₁ D) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
    change (IsLocalRing.maximalIdeal D).under A₁ = _
    rw [← Ideal.under_under (A := A₁) (B := C),
      IsLocalization.AtPrime.under_maximalIdeal D q]
    exact hqover
  have hfiniteD : IsEssentiallyOfFiniteType A₁ D (algebraMap A₁ D) := by
    unfold IsEssentiallyOfFiniteType
    rw [toAlgebra_algebraMap]
    exact ⟨C, inferInstance, inferInstance, inferInstance,
      q.primeCompl, inferInstance, inferInstance, inferInstance⟩
  have hdimD := IsLocalRing.ringKrullDim_closedFiber_add_trdeg_eq_trdeg hαDinj hfiniteD
  let gD : D := algebraMap C D g
  have hgD : gD ∈ IsLocalRing.maximalIdeal D := by
    change g ∈ (IsLocalRing.maximalIdeal D).under C
    rwa [IsLocalization.AtPrime.under_maximalIdeal D q]
  have hJmap : ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ C)).map (algebraMap C D) =
      (IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ D) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A₁ C D]
  have hnotD : ∀ r ∈ ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ D)).minimalPrimes,
      gD ∉ r := by
    intro r hr hgr
    have hrcomap : r.comap (algebraMap C D) ∈
        ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ C)).minimalPrimes := by
      rwa [← hJmap, IsLocalization.minimalPrimes_map q.primeCompl D] at hr
    exact hnot _ hrcomap hgr
  exact IsLocalRing.injective_quotient_of_dimension_add_trdeg_eq
    hαDinj hfiniteD gD hgD hnotD hdimD

private lemma exists_mem_minimalPrimes_span_le_comap_eq_bot
    {A₁ C : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁]
    [CommRing C] [IsDomain C] [Algebra A₁ C] [Algebra.FiniteType A₁ C]
    (hαinj : Function.Injective (algebraMap A₁ C)) (q : Ideal C) [q.IsMaximal]
    (hqover : q.comap (algebraMap A₁ C) = IsLocalRing.maximalIdeal A₁) (g : C) (hgq : g ∈ q)
    (hnot : ∀ p ∈ ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ C)).minimalPrimes,
      g ∉ p) :
    ∃ p ∈ (Ideal.span {g} : Ideal C).minimalPrimes, p ≤ q ∧
      p.comap (algebraMap A₁ C) = ⊥ := by
  let D := Localization.AtPrime q
  have : IsScalarTower A₁ C D := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hcut := injective_quotient_span_algebraMap_localization_atPrime hαinj q hqover g hgq hnot
  let gD : D := algebraMap C D g
  let S₀ : Submonoid D := (nonZeroDivisors A₁).map (algebraMap A₁ D)
  have hdisjoint : Disjoint ((Ideal.span {gD} : Ideal D) : Set D) S₀ := by
    refine Set.disjoint_left.mpr ?_
    rintro z hz ⟨a, ha, rfl⟩
    have hzero : ((Ideal.Quotient.mk (Ideal.span {gD})).comp
        (algebraMap A₁ D)) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact nonZeroDivisors.ne_zero ha (hcut (by simpa only [map_zero] using hzero))
  obtain ⟨r₀, hr₀prime, hgr₀, hrdis₀⟩ :=
    (Ideal.span {gD} : Ideal D).exists_le_prime_disjoint S₀ hdisjoint
  have : r₀.IsPrime := hr₀prime
  obtain ⟨r, hrmin, hrr₀⟩ := Ideal.exists_minimalPrimes_le (J := r₀) hgr₀
  have : r.IsPrime := hrmin.isPrime
  have hrdis : Disjoint (r : Set D) S₀ := hrdis₀.mono_left hrr₀
  refine ⟨r.comap (algebraMap C D), ?_, ?_, ?_⟩
  · have hminD : r ∈ ((Ideal.span {g} : Ideal C).map (algebraMap C D)).minimalPrimes := by
      simpa only [Ideal.map_span, Set.image_singleton] using hrmin
    rwa [IsLocalization.minimalPrimes_map q.primeCompl D] at hminD
  · exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime r)).trans_eq
      (IsLocalization.AtPrime.under_maximalIdeal D q)
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A₁ C D]
    refine le_antisymm (fun a ha ↦ ?_) bot_le
    by_contra ha0
    have haS : algebraMap A₁ D a ∈ S₀ := ⟨a, mem_nonZeroDivisors_of_ne_zero ha0, rfl⟩
    exact Set.disjoint_left.mp hrdis ha haS

private lemma notMem_of_mem_minimalPrimes_span_of_forall_notMem
    {A₁ C F : Type*} [CommRing A₁] [Nontrivial A₁] [CommRing C] [Algebra A₁ C]
    [CommRing F] [IsDomain F] [IsNoetherianRing F] [Algebra C F]
    (M : Submonoid C) [IsLocalization M F]
    (hMdef : M = Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁))
    {g c : C} {p : Ideal C} (hp : p ∈ (Ideal.span {g} : Ideal C).minimalPrimes)
    (hpA : p.comap (algebraMap A₁ C) = ⊥) (hcF : algebraMap C F c ≠ 0)
    (hg : ∀ Q ∈ (Ideal.span {algebraMap C F c} : Ideal F).minimalPrimes,
      algebraMap C F g ∉ Q) :
    c ∉ p := by
  have : p.IsPrime := hp.isPrime
  have hdisj : Disjoint (M : Set C) p := by
    rw [hMdef]
    exact disjoint_algebraMapSubmonoid_of_comap_eq_bot hpA
  let pF : Ideal F := p.map (algebraMap C F)
  have : pF.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M F p inferInstance hdisj
  have hpFunder : pF.comap (algebraMap C F) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M F inferInstance hdisj
  have hpFmin : pF ∈ (Ideal.span {algebraMap C F g} : Ideal F).minimalPrimes := by
    have hh : pF ∈ ((Ideal.span {g} : Ideal C).map (algebraMap C F)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map M F]
      change pF.comap (algebraMap C F) ∈ (Ideal.span {g} : Ideal C).minimalPrimes
      rwa [hpFunder]
    simpa only [Ideal.map_span, Set.image_singleton] using hh
  intro hc
  have hcFpF : algebraMap C F c ∈ pF := Ideal.mem_map_of_mem _ hc
  obtain ⟨Q, hQ, hQpF⟩ := Ideal.exists_minimalPrimes_le
    (J := pF) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hcFpF))
  have : Q.IsPrime := hQ.isPrime
  have hQne : Q ≠ ⊥ := fun hzero ↦ hcF <| by
    simpa only [hzero, Ideal.mem_bot] using hQ.le (Ideal.mem_span_singleton_self _)
  exact principal_minimal_prime_avoids_nonzero_prime _ pF Q hpFmin hQne (hg Q hQ) hQpF

/-- Let `R` be a domain of finite type over a valuation ring `A₁` whose generic fibre has positive
dimension, and let `q` be a maximal ideal of `R` over the closed point. Then `q` is not a minimal
prime over `𝔪_{A₁} R`, and some element of `q` lies in none of those minimal primes nor in any of
finitely many given primes other than `q`. -/
private lemma exists_mem_notMem_minimalPrimes_map_maximalIdeal
    {A₁ R : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁]
    [CommRing R] [IsDomain R] [Algebra A₁ R] [Algebra.FiniteType A₁ R]
    (hinj : Function.Injective (algebraMap A₁ R))
    (q : Ideal R) [q.IsMaximal]
    (hq : q.comap (algebraMap A₁ R) = IsLocalRing.maximalIdeal A₁)
    (hpos : 0 < ringKrullDim ((⊥ : Ideal A₁).Fiber R))
    (s : Finset (Ideal R)) (hs : ∀ p ∈ s, p.IsPrime ∧ p ≠ q) :
    ∃ g ∈ q,
      (∀ p ∈ ((IsLocalRing.maximalIdeal A₁).map (algebraMap A₁ R)).minimalPrimes, g ∉ p) ∧
        ∀ p ∈ s, g ∉ p := by
  classical
  let mA : Ideal A₁ := IsLocalRing.maximalIdeal A₁
  have : mA.IsPrime := (IsLocalRing.maximalIdeal.isMaximal A₁).isPrime
  have : q.LiesOver mA := ⟨hq.symm⟩
  let eG := PrimeSpectrum.primesOverOrderIsoFiber A₁ R mA
  let qOver : mA.primesOver R := ⟨q, inferInstance, inferInstance⟩
  let qG : PrimeSpectrum (mA.Fiber R) := eG qOver
  have : Nontrivial (mA.Fiber R) := qG.nontrivial
  have : FaithfulSMul A₁ R := (faithfulSMul_iff_algebraMap_injective A₁ R).mpr hinj
  have hdim :=
    ValuationRing.ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional
      (R := A₁) (S := R) inferInstance
  have hposSpecial : 0 < ringKrullDim (mA.Fiber R) := by
    rwa [hdim.1]
  have hqGclosed : IsClosed ({qG} : Set (PrimeSpectrum (mA.Fiber R))) := by
    apply isClosed_of_closure_subset
    intro z hz
    have hle : qG ≤ z :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr (specializes_iff_mem_closure.mpr hz)
    have hleR : qOver ≤ eG.symm z :=
      eG.le_iff_le.mp (by simpa only [eG.apply_symm_apply] using hle)
    have heqR : q = (eG.symm z).1 :=
      ‹q.IsMaximal›.eq_of_le (eG.symm z).2.1.ne_top hleR
    have heqOver : qOver = eG.symm z := Subtype.ext heqR
    have heq : qG = z := (congrArg eG heqOver).trans (eG.apply_symm_apply z)
    exact Set.mem_singleton_iff.mpr heq.symm
  have hposSpecialTop : 0 < topologicalKrullDim (PrimeSpectrum (mA.Fiber R)) := by
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have hqGnotcomp : ({qG} : Set (PrimeSpectrum (mA.Fiber R))) ∉
      irreducibleComponents (PrimeSpectrum (mA.Fiber R)) := fun hcomp ↦
    not_lt_of_ge (topologicalKrullDim_le_zero_of_equidimensional_singleton_component
      (PrimeSpectrum (mA.Fiber R)) hdim.2 qG hcomp) hposSpecialTop
  have : IsNoetherianRing (mA.Fiber R) :=
    Algebra.FiniteType.isNoetherianRing mA.ResidueField _
  let H : Set (PrimeSpectrum (mA.Fiber R)) := {w | IsMin w}
  have hHfinite : H.Finite := PrimeSpectrum.finite_setOfPred_isMin (mA.Fiber R)
  let ρ : PrimeSpectrum (mA.Fiber R) → Ideal R := fun w => (eG.symm w).1
  let t : Finset (Ideal R) := (hHfinite.image ρ).toFinset
  have ht : ∀ p ∈ t, p.IsPrime ∧ p ≠ q := by
    intro p hp
    have hp' : p ∈ ρ '' H := by
      simpa only [t, Set.Finite.mem_toFinset] using hp
    obtain ⟨w, hwmin, rfl⟩ := hp'
    refine ⟨(eG.symm w).2.1, fun heq ↦ ?_⟩
    have heqOver : eG.symm w = qOver := Subtype.ext heq
    have hwq : w = qG := (eG.apply_symm_apply w).symm.trans (congrArg eG heqOver)
    have hcomp : PrimeSpectrum.zeroLocus (qG.asIdeal : Set (mA.Fiber R)) ∈
        irreducibleComponents (PrimeSpectrum (mA.Fiber R)) := by
      rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact ⟨qG.asIdeal, PrimeSpectrum.isMin_iff.mp (hwq ▸ hwmin), rfl⟩
    rw [← PrimeSpectrum.closure_singleton qG, hqGclosed.closure_eq] at hcomp
    exact hqGnotcomp hcomp
  have hmin : ∀ p ∈ (mA.map (algebraMap A₁ R)).minimalPrimes, p ∈ t := by
    intro p hp
    have : p.IsPrime := hp.isPrime
    have hlie : p.comap (algebraMap A₁ R) = mA :=
      ((inferInstance : mA.IsMaximal).eq_of_le
        (Ideal.comap_ne_top _ (inferInstance : p.IsPrime).ne_top)
        (Ideal.map_le_iff_le_comap.mp hp.le)).symm
    have : p.LiesOver mA := ⟨hlie.symm⟩
    let pOver : mA.primesOver R := ⟨p, inferInstance, inferInstance⟩
    have hpOverMin : IsMin pOver := fun b hb =>
      hp.2 ⟨b.2.1, Ideal.map_le_iff_le_comap.mpr b.2.2.1.le⟩ hb
    have hρw : ρ (eG pOver) = p := by
      change (eG.symm (eG pOver)).1 = p
      rw [eG.symm_apply_apply]
    simp only [t, Set.Finite.mem_toFinset]
    exact ⟨eG pOver, (eG.isMin_apply).mpr hpOverMin, hρw⟩
  obtain ⟨g, hgq, hg⟩ := exists_mem_maximal_avoid_finite_primes q (t ∪ s)
    (fun p hp ↦ (Finset.mem_union.mp hp).elim (ht p) (hs p))
  exact ⟨g, hgq, fun p hp ↦ hg p (Finset.mem_union_left s (hmin p hp)),
    fun p hp ↦ hg p (Finset.mem_union_right t hp)⟩

private lemma exists_isPrime_le_comap_eq_bot_notMem
    {A₁ C : Type u} {F : Type*} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁]
    [CommRing C] [IsDomain C] [Algebra A₁ C] [Algebra.FiniteType A₁ C]
    [CommRing F] [IsDomain F] [IsNoetherianRing F] [Algebra C F]
    (M : Submonoid C) [IsLocalization M F]
    (hMdef : M = Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁))
    (hαinj : Function.Injective (algebraMap A₁ C)) (q : Ideal C) [q.IsMaximal]
    (hqover : q.comap (algebraMap A₁ C) = IsLocalRing.maximalIdeal A₁)
    (hmAne : IsLocalRing.maximalIdeal A₁ ≠ (⊥ : Ideal A₁))
    (hpos : 0 < ringKrullDim ((⊥ : Ideal A₁).Fiber C))
    (hgenericComap : ∀ (Q : Ideal F) [Q.IsPrime],
      (Q.comap (algebraMap C F)).comap (algebraMap A₁ C) = ⊥)
    {c : C} (hcF : algebraMap C F c ≠ 0) :
    ∃ p : Ideal C, p.IsPrime ∧ p ≠ ⊥ ∧ p ≤ q ∧ p.comap (algebraMap A₁ C) = ⊥ ∧ c ∉ p := by
  let tc : Finset (Ideal C) :=
    (((Ideal.span {algebraMap C F c} : Ideal F).finite_minimalPrimes_of_isNoetherianRing F).image
      (fun Q => Q.comap (algebraMap C F))).toFinset
  have htc : ∀ p ∈ tc, p.IsPrime ∧ p ≠ q := by
    intro p hp
    obtain ⟨Q, hQ, rfl⟩ : p ∈ (Ideal.span {algebraMap C F c} : Ideal F).minimalPrimes.image
        (fun Q => Q.comap (algebraMap C F)) := by
      simpa only [tc, Set.Finite.mem_toFinset] using hp
    have : Q.IsPrime := hQ.isPrime
    refine ⟨inferInstance, fun heq ↦ hmAne ?_⟩
    rw [← hqover, ← heq]
    exact hgenericComap Q
  obtain ⟨g, hgq, hnot, hgtc⟩ :=
    exists_mem_notMem_minimalPrimes_map_maximalIdeal hαinj q hqover hpos tc htc
  obtain ⟨p, hpmin, hpq, hpA⟩ :=
    exists_mem_minimalPrimes_span_le_comap_eq_bot hαinj q hqover g hgq hnot
  refine ⟨p, hpmin.isPrime, fun hp ↦ ?_, hpq, hpA,
    notMem_of_mem_minimalPrimes_span_of_forall_notMem M hMdef hpmin hpA hcF
      fun Q hQ ↦ hgtc (Q.comap (algebraMap C F)) (by
        simp only [tc, Set.Finite.mem_toFinset]
        exact ⟨Q, hQ, rfl⟩)⟩
  have hg0 : g = 0 := by
    simpa only [hp, Ideal.mem_bot] using hpmin.le (Ideal.mem_span_singleton_self g)
  obtain ⟨v, hvmin, -⟩ :=
    Ideal.exists_minimalPrimes_le (J := q) (Ideal.map_le_iff_le_comap.mpr hqover.ge)
  exact hnot v hvmin (hg0 ▸ v.zero_mem)

/-- A domain with a nonzero prime ideal has positive Krull dimension. -/
lemma ringKrullDim_pos_of_isPrime_ne_bot {G : Type*} [CommRing G] [IsDomain G] (J : Ideal G)
    [J.IsPrime] (hJ : J ≠ ⊥) : 0 < ringKrullDim G := by
  by_contra hn
  have : Ring.KrullDimLE 0 G := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr
    (le_antisymm (le_of_not_gt hn) ringKrullDim_nonneg_of_nontrivial)
  exact hJ (((Ideal.isMaximal_of_isPrime ⊥ : (⊥ : Ideal G).IsMaximal).eq_of_le
    (inferInstance : J.IsPrime).ne_top bot_le).symm)

/-- **The extension step inside the inductive step of Stacks 053U.** In the situation of
`exists_closed_specialization_affine_integral` — `C` of finite type over the valuation ring `A₁`,
`F = κ(A₁) ⊗ C` its generic fibre, `q` the maximal ideal of the chosen closed point and `c` a
nonzero element cutting out the neighbourhood to stay inside — a prime `P` of `F` whose contraction
lies under `q` and which avoids `c` is *not* maximal only if a strictly larger prime of `F` has the
same two properties.

The proof repeats the argument of the source for `R = C/P ∩ C`: the horizontal divisor cut out of
`R` by an element of `q` avoiding the components of the special fibre meets the generic fibre, by
Stacks 053S, and the prime it produces is the required larger one. Maximality of `P` in that set
of primes therefore follows, and that is what makes the point it defines closed in the fibre. -/
private lemma exists_gt_mem_of_not_isMaximal
    {A₁ C F : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁] [IsLocalRing A₁]
    [CommRing C] [IsDomain C] [Algebra A₁ C] [Algebra.FiniteType A₁ C]
    [CommRing F] [IsDomain F] [IsNoetherianRing F] [Algebra C F]
    (M : Submonoid C) [IsLocalization M F]
    (hMdef : M = Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁))
    (hαft : (algebraMap A₁ C).FiniteType)
    (q : PrimeSpectrum C) [q.asIdeal.IsMaximal]
    (hqover : q.asIdeal.comap (algebraMap A₁ C) = IsLocalRing.maximalIdeal A₁)
    (hmAne : IsLocalRing.maximalIdeal A₁ ≠ (⊥ : Ideal A₁))
    (c : C)
    (hgenericComap : ∀ (Q : Ideal F) [Q.IsPrime],
      (Q.comap (algebraMap C F)).comap (algebraMap A₁ C) = ⊥)
    (P : Ideal F)
    (hP : P.IsPrime ∧ P.comap (algebraMap C F) ≤ q.asIdeal ∧ algebraMap C F c ∉ P)
    (hnot : ¬ Ideal.IsMaximal P) :
    ∃ Q ∈ {Q : Ideal F | Q.IsPrime ∧ Q.comap (algebraMap C F) ≤ q.asIdeal ∧
      algebraMap C F c ∉ Q}, P < Q := by
  let α : A₁ →+* C := algebraMap A₁ C
  let fC : C →+* F := algebraMap C F
  have : P.IsPrime := hP.1
  let p₂ : Ideal C := Ideal.comap fC P
  have : p₂.IsPrime := Ideal.IsPrime.comap fC
  obtain ⟨Q₀, hQ₀max, hPQ₀⟩ := Ideal.exists_le_maximal P hP.1.ne_top
  have hPQ₀strict : P < Q₀ := lt_of_le_of_ne hPQ₀ fun h => hnot (h.symm ▸ hQ₀max)
  let R := C ⧸ p₂
  let π : C →+* R := Ideal.Quotient.mk p₂
  let αR : A₁ →+* R := π.comp α
  let : Algebra A₁ R := inferInstance
  have : IsDomain R := Ideal.Quotient.isDomain p₂
  have hαRinj : Function.Injective αR := by
    rw [RingHom.injective_iff_ker_eq_bot]
    change Ideal.comap α (Ideal.comap π ⊥) = ⊥
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hgenericComap P
  have : Algebra.FiniteType A₁ R :=
    (RingHom.finiteType_algebraMap).mp
      (RingHom.FiniteType.comp
        (RingHom.FiniteType.of_surjective π Ideal.Quotient.mk_surjective)
        hαft)
  have : Module.Flat A₁ R := flat_of_injective_algebraMap (A := A₁) (B := R) hαRinj
  let qR : Ideal R := q.asIdeal.map π
  have hp₂q : p₂ ≤ q.asIdeal := hP.2.1
  have : qR.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hqRover : qR.comap αR = IsLocalRing.maximalIdeal A₁ := by
    change (q.asIdeal.map π).comap (π.comp α) = _
    rw [← Ideal.comap_comap,
      show (q.asIdeal.map π).comap π = q.asIdeal from Ideal.comap_map_mk hp₂q]
    exact hqover
  let cR : R := π c
  have hcRne : cR ≠ 0 := fun hc => hP.2.2 (Ideal.Quotient.eq_zero_iff_mem (I := p₂).mp hc)
  let p₀ : Ideal C := Q₀.comap fC
  have hp₂p₀ : p₂ < p₀ := by
    apply lt_of_le_of_ne (Ideal.comap_mono hPQ₀strict.le)
    intro heq
    have hQP : Q₀ ≤ P :=
      (IsLocalization.under_le_under_iff M F).mp (le_of_eq heq.symm)
    exact (not_le_of_gt hPQ₀strict) hQP
  let jR : Ideal R := p₀.map π
  have : p₀.IsPrime := Ideal.IsPrime.comap fC
  have : jR.IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hp₂p₀.le
  have hjRne : jR ≠ ⊥ := by
    intro heq
    have hcomp : jR.comap π = p₀ := Ideal.comap_map_mk hp₂p₀.le
    have hp₀p₂ : p₀ = p₂ := by
      rw [← hcomp, heq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (ne_of_gt hp₂p₀) hp₀p₂
  have hjRA : jR.comap αR = ⊥ := by
    change (p₀.map π).comap (π.comp α) = ⊥
    rw [← Ideal.comap_comap,
      show (p₀.map π).comap π = p₀ from Ideal.comap_map_mk hp₂p₀.le]
    exact hgenericComap Q₀
  let G := (⊥ : Ideal A₁).Fiber R
  let : Algebra R G := Algebra.TensorProduct.rightAlgebra
  let M_R : Submonoid R :=
    Algebra.algebraMapSubmonoid R (nonZeroDivisors A₁)
  have hM_R : M_R ≤ nonZeroDivisors R := algebraMapSubmonoid_nonZeroDivisors_le hαRinj
  have : IsLocalization M_R G :=
    IsLocalization.tensorRight ((⊥ : Ideal A₁).ResidueField)
      (nonZeroDivisors A₁)
  have : IsDomain G :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hM_R
  have hjRdisj : Disjoint (M_R : Set R) jR :=
    disjoint_algebraMapSubmonoid_of_comap_eq_bot hjRA
  let JG : Ideal G := jR.map (algebraMap R G)
  have : JG.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M_R G jR inferInstance hjRdisj
  have hJGunder : JG.comap (algebraMap R G) = jR :=
    IsLocalization.under_map_of_isPrime_disjoint M_R G inferInstance hjRdisj
  have hJGne : JG ≠ ⊥ := by
    intro heq
    apply hjRne
    rw [← hJGunder, heq]
    exact Ideal.comap_bot_of_injective _
      (IsLocalization.injective G hM_R)
  have hposG : 0 < ringKrullDim G := ringKrullDim_pos_of_isPrime_ne_bot JG hJGne
  let fR : R →+* G := algebraMap R G
  let cG : G := fR cR
  have hcGne : cG ≠ 0 := fun hc =>
    hcRne (IsLocalization.injective G hM_R (by simpa only [map_zero] using hc))
  have : Algebra.FiniteType ((⊥ : Ideal A₁).ResidueField) G :=
    inferInstance
  have : IsNoetherianRing G :=
    Algebra.FiniteType.isNoetherianRing ((⊥ : Ideal A₁).ResidueField) G
  have hgenericComapR (Q : Ideal G) [Q.IsPrime] :
      (Q.comap fR).comap αR = ⊥ :=
    ((PrimeSpectrum.primesOverOrderIsoFiber A₁ R (⊥ : Ideal A₁)).symm
      (⟨Q, inferInstance⟩ : PrimeSpectrum G)).2.2.1.symm
  obtain ⟨jNew, hjNew, hjNewne, hjNewq, hjNewA, hcnotjNew⟩ :=
    exists_isPrime_le_comap_eq_bot_notMem M_R rfl hαRinj qR hqRover hmAne hposG hgenericComapR
      hcGne
  exact exists_prime_gt_of_prime_quotient M hMdef q.asIdeal c P hp₂q jNew hjNew
    hjNewq (by rwa [Ideal.comap_comap]) hcnotjNew hjNewne

private lemma exists_isMaximal_comap_le_notMem
    {A₁ C F : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁]
    [CommRing C] [IsDomain C] [Algebra A₁ C] [Algebra.FiniteType A₁ C]
    [CommRing F] [IsDomain F] [IsNoetherianRing F] [Algebra C F]
    (M : Submonoid C) [IsLocalization M F]
    (hMdef : M = Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁))
    (hαft : (algebraMap A₁ C).FiniteType)
    (hαinj : Function.Injective (algebraMap A₁ C))
    (q : PrimeSpectrum C) [q.asIdeal.IsMaximal]
    (hqover : q.asIdeal.comap (algebraMap A₁ C) = IsLocalRing.maximalIdeal A₁)
    (hmAne : IsLocalRing.maximalIdeal A₁ ≠ (⊥ : Ideal A₁))
    (hpos : 0 < ringKrullDim ((⊥ : Ideal A₁).Fiber C))
    (hgenericComap : ∀ (Q : Ideal F) [Q.IsPrime],
      (Q.comap (algebraMap C F)).comap (algebraMap A₁ C) = ⊥)
    (c : C) (hcF : algebraMap C F c ≠ 0) :
    ∃ P : Ideal F, P.IsMaximal ∧ P.comap (algebraMap C F) ≤ q.asIdeal ∧
      algebraMap C F c ∉ P := by
  subst hMdef
  obtain ⟨p₁, hp₁, -, hp₁q, hp₁A, hcnotp₁⟩ :=
    exists_isPrime_le_comap_eq_bot_notMem _ rfl hαinj q.asIdeal hqover hmAne hpos
      hgenericComap hcF
  have hp₁disj := disjoint_algebraMapSubmonoid_of_comap_eq_bot hp₁A
  let pF : Ideal F := p₁.map (algebraMap C F)
  have : pF.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ F p₁ hp₁ hp₁disj
  have hpFunder : pF.comap (algebraMap C F) = p₁ :=
    IsLocalization.under_map_of_isPrime_disjoint _ F hp₁ hp₁disj
  obtain ⟨P, hP, hPmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr (inferInstance : _root_.IsNoetherian F F))
      ({P | P.IsPrime ∧ P.comap (algebraMap C F) ≤ q.asIdeal ∧ algebraMap C F c ∉ P} :
        Set (Ideal F))
      ⟨pF, inferInstance, by rwa [hpFunder], fun hc => hcnotp₁ (hpFunder ▸ hc)⟩
  refine ⟨P, ?_, hP.2⟩
  by_contra hnot
  obtain ⟨Q, hQE, hPQ⟩ := exists_gt_mem_of_not_isMaximal _ rfl hαft q hqover hmAne c
    hgenericComap P hP hnot
  exact hPmax Q hQE hPQ

private lemma eq_comap_of_isMaximal_of_comap_le {C F : Type u} [CommRing C] [CommRing F]
    [Algebra C F] (M : Submonoid C) [IsLocalization M F] {P : Ideal F} (hP : P.IsMaximal)
    (Q : Ideal C) [Q.IsPrime] (hQ : Disjoint (M : Set C) Q)
    (hPQ : P.comap (algebraMap C F) ≤ Q) : Q = P.comap (algebraMap C F) := by
  have : (Q.map (algebraMap C F)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M F Q inferInstance hQ
  have hle : P ≤ Q.map (algebraMap C F) := by
    have hh := Ideal.map_mono (f := algebraMap C F) hPQ
    change Ideal.map (algebraMap C F) (Ideal.under C P) ≤ _ at hh
    rwa [IsLocalization.map_under M F P] at hh
  rw [hP.eq_of_le this.ne_top hle]
  exact (IsLocalization.under_map_of_isPrime_disjoint M F inferInstance hQ).symm

private lemma injective_appTop_comp_ΓSpecIso_inv {A : Type u} [CommRing A] [IsDomain A]
    {Z : Scheme.{u}} (pZ : Z ⟶ Spec (.of A)) [IsIntegral Z] [IsAffine Z] [IsDominant pZ] :
    Function.Injective ((pZ.appTop.hom).comp (Scheme.ΓSpecIso (.of A)).inv.hom) := by
  have : IsAffineHom pZ := isAffineHom_of_isAffine pZ
  have : IsSchemeTheoreticallyDominant pZ := IsSchemeTheoreticallyDominant.of_isDominant pZ
  exact (pZ.app_injective ⊤).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).1

private lemma finiteType_appTop_comp_ΓSpecIso_inv {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (pZ : Z ⟶ Spec (.of A)) [IsAffine Z] [LocallyOfFiniteType pZ] :
    ((pZ.appTop.hom).comp (Scheme.ΓSpecIso (.of A)).inv.hom).FiniteType := by
  apply RingHom.FiniteType.comp
  · simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      pZ.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  · exact RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2

private lemma isoSpec_hom_comp_spec_map_appTop {A : Type u} [CommRing A] {Z : Scheme.{u}}
    [IsAffine Z] (pZ : Z ⟶ Spec (.of A)) :
    Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((pZ.appTop.hom).comp (Scheme.ΓSpecIso (.of A)).inv.hom)) = pZ := by
  calc
    _ = (Z.isoSpec.hom ≫ Spec.map pZ.appTop) ≫ (Spec (.of A)).isoSpec.inv := by
      simp only [Scheme.isoSpec_Spec_inv, CommRingCat.ofHom_comp]
      rw [Category.assoc, ← Spec.map_comp]
      simp
    _ = (pZ ≫ (Spec (.of A)).isoSpec.hom) ≫ (Spec (.of A)).isoSpec.inv := by
      rw [Scheme.isoSpec_hom_naturality]
    _ = pZ := by simp

private lemma topologicalKrullDim_fiber_eq_ringKrullDim_of_comp_eq
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {Z : Scheme.{u}}
    (pZ : Z ⟶ Spec (.of A)) (e : Z ⟶ Spec (.of C)) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = pZ) (s : Spec (.of A)) :
    letI : s.asIdeal.IsPrime := s.isPrime
    topologicalKrullDim (pZ.fiber s) = ringKrullDim (s.asIdeal.Fiber C) := by
  have : s.asIdeal.IsPrime := s.isPrime
  let β : pZ.fiber s ⟶ (Spec.map (CommRingCat.ofHom (algebraMap A C))).fiber s :=
    pullback.map _ _ _ _ e (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id, Category.id_comp] using he.symm) (by simp)
  have : IsIso β := pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso β)).isHomeomorph).trans
    ((IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso
      (CategoryTheory.Arrow.leftFunc.mapIso
        (Spec.fiberToSpecResidueFieldIso A C s))).isHomeomorph).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _))

/-- Every open neighbourhood of a point `zv` in its fibre under a morphism from an affine scheme
contains the trace on the fibre of a basic open `D(c)` through `zv`. -/
private lemma exists_basicOpen_subset_of_mem_fiber {Z S : Scheme.{u}} [IsAffine Z]
    (pZ : Z ⟶ S) (η : S) (UZ : Set (pZ.fiber η)) (hUZ : IsOpen UZ) (zv : Z)
    (hzv : pZ zv = η) (hzUZ : (pZ.fiberHomeo η).symm ⟨zv, hzv⟩ ∈ UZ) :
    ∃ c : Γ(Z, ⊤), zv ∈ Z.basicOpen c ∧
      ∀ w : pZ.fiber η, pZ.fiberι η w ∈ Z.basicOpen c → w ∈ UZ := by
  let W : Set (pZ ⁻¹' ({η} : Set S)) := (pZ.fiberHomeo η).symm ⁻¹' UZ
  have hW : IsOpen W := hUZ.preimage (pZ.fiberHomeo η).symm.continuous
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp hW
  have hzO : zv ∈ O := by
    have hzW : (⟨zv, hzv⟩ : pZ ⁻¹' ({η} : Set S)) ∈ W := hzUZ
    rwa [← hpre] at hzW
  obtain ⟨_, ⟨c, rfl⟩, hzbasic, hbasicO⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Z))
      (show zv ∈ (⟨O, hO⟩ : Z.Opens) from hzO)
  refine ⟨c, hzbasic, fun w hw => ?_⟩
  let zw : pZ ⁻¹' ({η} : Set S) := ⟨pZ.fiberι η w, (pZ.fiberHomeo η w).2⟩
  have hzwW : zw ∈ W := by
    rw [← hpre]
    exact hbasicO hw
  have hzw : zw = pZ.fiberHomeo η w := Subtype.ext rfl
  change (pZ.fiberHomeo η).symm zw ∈ UZ at hzwW
  rwa [hzw, Homeomorph.symm_apply_apply] at hzwW

/-- **The heart of the inductive step of Stacks 053U, over a valuation ring.** Let `A₁` be a
valuation ring, let `Z` be an integral affine scheme dominating `Spec A₁` by a morphism locally
of finite type, let `zv` be the generic point of `Z` (so it lies over the generic point of
`Spec A₁`), and let `zv'` be a point over the closed point of `Spec A₁` which is closed in `Z`
and in its own fibre. Then every open neighbourhood `UZ` of `zv` inside the generic fibre
contains a point `w` closed in the generic fibre with `zv ⤳ w ⤳ zv'`.

This is the dimension-reducing step of the source: a principal divisor through `zv'` avoiding the
components of the special fibre and the closed set to be avoided meets the generic fibre, by
Stacks 053S. -/
private lemma exists_closed_specialization_affine_integral
    {A₁ : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁] [IsLocalRing A₁]
    {Z : Scheme.{u}} (pZ : Z ⟶ Spec (.of A₁))
    [IsIntegral Z] [IsAffine Z] [IsDominant pZ] [LocallyOfFiniteType pZ]
    (ηA : Spec (.of A₁)) (hηA : ηA = genericPoint (Spec (.of A₁)))
    (zv zv' : Z) (hzg : IsGenericPoint zv (Set.univ : Set Z)) (hspecz : zv ⤳ zv')
    (hpZgeneric : pZ zv = ηA)
    (hpZclosed : pZ zv' = IsLocalRing.closedPoint A₁)
    (hzv'closedZ : IsClosed ({zv'} : Set Z))
    (hηAne : ηA ≠ IsLocalRing.closedPoint A₁)
    (UZ : Set (pZ.fiber ηA)) (hUZ : IsOpen UZ)
    (hzUZ : (pZ.fiberHomeo ηA).symm ⟨zv, hpZgeneric⟩ ∈ UZ) :
    ∃ w : pZ.fiber ηA, w ∈ UZ ∧ IsClosed ({w} : Set (pZ.fiber ηA)) ∧
      zv ⤳ (pZ.fiberι ηA w) ∧ (pZ.fiberι ηA w) ⤳ zv' := by
  let zη : pZ.fiber ηA := (pZ.fiberHomeo ηA).symm ⟨zv, hpZgeneric⟩
  have hzη : pZ.fiberι ηA zη = zv := pZ.fiberι_fiberHomeo_symm ηA ⟨zv, hpZgeneric⟩
  by_cases hzηclosed : IsClosed ({zη} : Set (pZ.fiber ηA))
  · exact ⟨zη, hzUZ, hzηclosed, by rw [hzη], by rwa [hzη]⟩
  have : IsAffineHom pZ := isAffineHom_of_isAffine pZ
  obtain ⟨c, hzbasic, hbasicU⟩ :=
    exists_basicOpen_subset_of_mem_fiber pZ ηA UZ hUZ zv hpZgeneric hzUZ
  let C := Γ(Z, ⊤)
  let q : Spec Γ(Z, ⊤) := Z.isoSpec.hom zv'
  have hqclosed : IsClosed ({q} : Set (Spec Γ(Z, ⊤))) := by
    let e := Scheme.homeoOfIso Z.isoSpec
    have he : e zv' = q := rfl
    simpa only [Set.image_singleton, he] using
      e.isClosed_image.mpr hzv'closedZ
  have : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hqclosed
  let α : A₁ →+* C :=
    (pZ.appTop.hom).comp (Scheme.ΓSpecIso (.of A₁)).inv.hom
  let : Algebra A₁ C := α.toAlgebra
  have hαinj : Function.Injective α := injective_appTop_comp_ΓSpecIso_inv pZ
  have hαft : α.FiniteType := finiteType_appTop_comp_ΓSpecIso_inv pZ
  have : Algebra.FiniteType A₁ C :=
    (RingHom.finiteType_algebraMap).mp hαft
  have : Module.Flat A₁ C := flat_of_injective_algebraMap (A := A₁) (B := C) hαinj
  have : FaithfulSMul A₁ C :=
    (faithfulSMul_iff_algebraMap_injective A₁ C).mpr hαinj
  have : Algebra.FiniteType ((⊥ : Ideal A₁).ResidueField)
      ((⊥ : Ideal A₁).Fiber C) := inferInstance
  have : IsNoetherianRing ((⊥ : Ideal A₁).Fiber C) :=
    Algebra.FiniteType.isNoetherianRing ((⊥ : Ideal A₁).ResidueField) _
  have : IsDomain ((⊥ : Ideal A₁).Fiber C) := isDomain_generic_fiber
  let F := (⊥ : Ideal A₁).Fiber C
  let : Algebra C F := Algebra.TensorProduct.rightAlgebra
  let fC : C →+* F := algebraMap C F
  let M : Submonoid C :=
    Algebra.algebraMapSubmonoid C (nonZeroDivisors A₁)
  have hM : M ≤ nonZeroDivisors C := algebraMapSubmonoid_nonZeroDivisors_le hαinj
  have : IsLocalization M F :=
    IsLocalization.tensorRight ((⊥ : Ideal A₁).ResidueField)
      (nonZeroDivisors A₁)
  have hcne : c ≠ 0 := by
    intro hc
    subst c
    rwa [Z.basicOpen_zero] at hzbasic
  let cF : F := fC c
  have hcFne : cF ≠ 0 := fun hc =>
    hcne (IsLocalization.injective F hM (by simpa only [map_zero] using hc))
  let φ : Spec (.of C) ⟶ Spec (.of A₁) :=
    Spec.map (CommRingCat.ofHom α)
  have hfactor : Z.isoSpec.hom ≫ φ = pZ := isoSpec_hom_comp_spec_map_appTop pZ
  have hqover : q.asIdeal.comap α = IsLocalRing.maximalIdeal A₁ :=
    congrArg PrimeSpectrum.asIdeal
      ((congrArg (fun m : Z ⟶ Spec (.of A₁) => m zv') hfactor).trans hpZclosed)
  have hgenericComap (Q : Ideal F) [Q.IsPrime] :
      (Q.comap fC).comap α = ⊥ :=
    ((PrimeSpectrum.primesOverOrderIsoFiber A₁ C (⊥ : Ideal A₁)).symm
      (⟨Q, inferInstance⟩ : PrimeSpectrum F)).2.2.1.symm
  have hmAne : IsLocalRing.maximalIdeal A₁ ≠ (⊥ : Ideal A₁) := by
    intro heq
    apply hηAne
    apply PrimeSpectrum.ext
    rw [hηA, AlgebraicGeometry.genericPoint_eq_bot_of_affine]
    exact heq.symm
  have hzηgen : IsGenericPoint zη (Set.univ : Set (pZ.fiber ηA)) :=
    isGenericPoint_iff_specializes.mpr fun w => iff_of_true
      ((pZ.fiberι ηA).isEmbedding.specializes_iff.mp
        (by simpa only [hzη] using hzg.specializes (Set.mem_univ (pZ.fiberι ηA w)))) trivial
  have hposGeneric : 0 < topologicalKrullDim (pZ.fiber ηA) :=
    topologicalKrullDim_pos_of_nonclosed_genericPoint
      (pZ.fiber ηA) zη hzηgen hzηclosed
  have hposGenericRing : 0 < ringKrullDim ((⊥ : Ideal A₁).Fiber C) := by
    have hd := topologicalKrullDim_fiber_eq_ringKrullDim_of_comp_eq pZ Z.isoSpec.hom hfactor ηA
    have hηpoint : ηA = (⊥ : PrimeSpectrum A₁) :=
      hηA.trans (AlgebraicGeometry.genericPoint_eq_bot_of_affine _)
    rw [hηpoint] at hd hposGeneric
    exact hposGeneric.trans_eq hd
  obtain ⟨P, hmaximal, hPq, hPc⟩ := exists_isMaximal_comap_le_notMem M rfl hαft hαinj q
    hqover hmAne hposGenericRing hgenericComap c hcFne
  have : Ideal.IsPrime P := hmaximal.isPrime
  let p₂ : Ideal C := Ideal.comap fC P
  have : Ideal.IsPrime p₂ := Ideal.IsPrime.comap fC
  let ξ₂ : PrimeSpectrum C := ⟨p₂, inferInstance⟩
  let z₂ : Z := Z.isoSpec.inv ξ₂
  have hz₂base : pZ z₂ = ηA := by
    rw [← hfactor]
    change φ (Z.isoSpec.hom (Z.isoSpec.inv ξ₂)) = ηA
    rw [Scheme.inv_hom_apply Z.isoSpec ξ₂]
    apply PrimeSpectrum.ext
    change p₂.comap α = ηA.asIdeal
    rw [hgenericComap P, hηA, AlgebraicGeometry.genericPoint_eq_bot_of_affine]
    rfl
  have hz₂spec : z₂ ⤳ zv' := by
    have hspec : ξ₂ ⤳ q :=
      (PrimeSpectrum.le_iff_specializes ξ₂ q).mp hPq
    have h := hspec.map Z.isoSpec.inv.continuous
    simpa [z₂, q, Scheme.hom_inv_apply] using h
  let w₂ : pZ.fiber ηA :=
    (pZ.fiberHomeo ηA).symm ⟨z₂, hz₂base⟩
  have hw₂ : pZ.fiberι ηA w₂ = z₂ :=
    pZ.fiberι_fiberHomeo_symm ηA ⟨z₂, hz₂base⟩
  have hw₂UZ : w₂ ∈ UZ := by
    apply hbasicU w₂
    rw [hw₂, ← Z.toSpecΓ_preimage_basicOpen c]
    change Z.isoSpec.hom z₂ ∈ PrimeSpectrum.basicOpen c
    rw [Scheme.inv_hom_apply Z.isoSpec ξ₂]
    exact (PrimeSpectrum.mem_basicOpen c ξ₂).mpr hPc
  have hw₂closed : IsClosed ({w₂} : Set (pZ.fiber ηA)) := by
    apply isClosed_of_closure_subset
    intro w hw
    have hspec : w₂ ⤳ w := specializes_iff_mem_closure.mpr hw
    have hspecC : (Z.isoSpec.hom (pZ.fiberι ηA w₂)) ⤳
        Z.isoSpec.hom (pZ.fiberι ηA w) :=
      (hspec.map (pZ.fiberι ηA).continuous).map Z.isoSpec.hom.continuous
    let Q : Ideal C := (Z.isoSpec.hom (pZ.fiberι ηA w)).asIdeal
    have : Q.IsPrime := (Z.isoSpec.hom (pZ.fiberι ηA w)).isPrime
    have hp₂Q : p₂ ≤ Q := by
      have hh := (PrimeSpectrum.le_iff_specializes _ _).mpr hspecC
      rwa [hw₂, Scheme.inv_hom_apply Z.isoSpec ξ₂] at hh
    have hQA : Q.comap α = ⊥ := by
      have hwbase : pZ (pZ.fiberι ηA w) = ηA :=
        (pZ.fiberHomeo ηA w).2
      have hφ : φ (Z.isoSpec.hom (pZ.fiberι ηA w)) = ηA :=
        (congrArg (fun m : Z ⟶ Spec (.of A₁) => m (pZ.fiberι ηA w)) hfactor).trans hwbase
      have hcomap := congrArg PrimeSpectrum.asIdeal hφ
      change Q.comap α = ηA.asIdeal at hcomap
      rw [hcomap, hηA, AlgebraicGeometry.genericPoint_eq_bot_of_affine]
      rfl
    have hQp₂ : Q = p₂ := eq_comap_of_isMaximal_of_comap_le M hmaximal Q
      (disjoint_algebraMapSubmonoid_of_comap_eq_bot hQA) hp₂Q
    have hz : pZ.fiberι ηA w = pZ.fiberι ηA w₂ := by
      apply (Scheme.homeoOfIso Z.isoSpec).injective
      apply PrimeSpectrum.ext
      change (Z.isoSpec.hom (pZ.fiberι ηA w)).asIdeal =
        (Z.isoSpec.hom (pZ.fiberι ηA w₂)).asIdeal
      rwa [hw₂, Scheme.inv_hom_apply Z.isoSpec ξ₂]
    exact Set.mem_singleton_iff.mpr
      ((pZ.fiberι ηA).isEmbedding.injective hz)
  exact ⟨w₂, hw₂UZ, hw₂closed,
    by simpa only [hw₂] using hzg.specializes (Set.mem_univ z₂),
    by simpa only [hw₂] using hz₂spec⟩

/-- For a valuation subring `A₁` of `κ(s)` and a morphism `g : Spec A₁ ⟶ S` sending the generic
point to `s` and restricting to `Spec κ(s) ⟶ S` along `A₁ ⊆ κ(s)`, the residue field map of `g`
at the generic point is an isomorphism. -/
private lemma isIso_residueFieldMap_genericPoint_of_valuationSubring {S : Scheme.{u}} {s : S}
    (A₁ : ValuationSubring (S.residueField s)) (g : Spec (.of A₁) ⟶ S)
    (hg : g (genericPoint (Spec (.of A₁))) = s)
    (hgs : Spec.map (CommRingCat.ofHom A₁.subtype) ≫ g = S.fromSpecResidueField s) :
    IsIso (g.residueFieldMap (genericPoint (Spec (.of A₁)))) := by
  let ηA := genericPoint (Spec (.of A₁))
  let eA := genericResidueIsoOfValuationSubring A₁
  have heq : g.residueFieldMap ηA ≫ eA.hom = (S.residueFieldCongr hg).hom := by
    rw [specMap_subtype_eq_genericResidueIso, Category.assoc,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc] at hgs
    have ht' : (Scheme.SpecToEquivOfField (S.residueField s) S).symm
        ⟨g ηA, g.residueFieldMap ηA ≫ eA.hom⟩ =
      (Scheme.SpecToEquivOfField (S.residueField s) S).symm
        ⟨s, 𝟙 _⟩ := by
      simp only [Scheme.SpecToEquivOfField_symm_apply]
      convert hgs using 1
      rw [Spec.map_id]
      exact Category.id_comp (S.fromSpecResidueField s)
    have hh := congrArg (Scheme.SpecToEquivOfField (S.residueField s) S) ht'
    simp only [Equiv.apply_symm_apply] at hh
    rw [Scheme.SpecToEquivOfField_eq_iff] at hh
    obtain ⟨_, he⟩ := hh
    change g.residueFieldMap ηA ≫ eA.hom =
      (S.residueFieldCongr hg).hom ≫ 𝟙 _ at he
    exact he.trans (Category.comp_id _)
  have : IsIso (g.residueFieldMap ηA ≫ eA.hom) := heq ▸ inferInstance
  exact IsIso.of_isIso_comp_right (g.residueFieldMap ηA) eA.hom

/-- For a field extension `K → L` and a valuation subring `B` of `L`, the inclusion of
`K ∩ B` into `B` is a local homomorphism. -/
private lemma isLocalHom_codRestrict_intersectionSubring {K L : Type u} [Field K] [Field L]
    [Algebra K L] (B : ValuationSubring L) :
    IsLocalHom (((algebraMap K L).comp (intersectionSubring (K := K) B).subtype).codRestrict
      B.toSubring (fun a => a.2)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hfield : algebraMap K L (a : K) * (b : L) = 1 := by
    have h := congrArg B.subtype hb
    simp only [map_mul, map_one] at h
    exact h
  have ha0 : (a : K) ≠ 0 := by
    rintro ha0
    simp [ha0] at hfield
  have hinv : (a : K)⁻¹ ∈ intersectionSubring (K := K) B := by
    change algebraMap K L (a : K)⁻¹ ∈ B
    have hbeq : (b : L) = (algebraMap K L (a : K))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hfield)
    rw [map_inv₀, ← hbeq]
    exact b.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/-- Let `p : P ⟶ Spec A₁` be locally of finite type over a valuation ring `A₁` which is not a
field, and let `xA ⤳ xA'` lie over the generic and the closed point of `Spec A₁`, with `xA'`
closed in its fibre. Then every open neighbourhood of `xA` in the generic fibre contains a point
closed in the generic fibre lying between `xA` and `xA'`. -/
private lemma exists_closed_specialization_over_valuationRing
    {A₁ : Type u} [CommRing A₁] [IsDomain A₁] [ValuationRing A₁] [IsLocalRing A₁]
    {P : Scheme.{u}} (p : P ⟶ Spec (.of A₁)) [LocallyOfFiniteType p]
    (ηA : Spec (.of A₁)) (hηA : ηA = genericPoint (Spec (.of A₁)))
    (hηAne : ηA ≠ IsLocalRing.closedPoint A₁)
    (xA xA' : P) (hspecA : xA ⤳ xA') (hsA : p xA = ηA)
    (hsA' : p xA' = IsLocalRing.closedPoint A₁)
    (hxA'closed : IsClosed ({p.asFiber xA'} : Set (p.fiber (p xA'))))
    (Uη : Set (p.fiber ηA)) (hUη : IsOpen Uη)
    (hxUη : (p.fiberHomeo ηA).symm ⟨xA, hsA⟩ ∈ Uη) :
    ∃ z : p.fiber ηA, z ∈ Uη ∧ IsClosed ({z} : Set (p.fiber ηA)) ∧
      xA ⤳ (p.fiberι ηA z) ∧ (p.fiberι ηA z) ⤳ xA' := by
  let xη : p.fiber ηA := (p.fiberHomeo ηA).symm ⟨xA, hsA⟩
  have hxη : p.fiberι ηA xη = xA := p.fiberι_fiberHomeo_symm ηA ⟨xA, hsA⟩
  obtain ⟨V, hVaffine, hxA'V, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := P) (x := xA')
      (U := ⊤) (Set.mem_univ xA')
  have hxAV : xA ∈ V.1 := hspecA.mem_open V.2 hxA'V
  let Y : Scheme.{u} := V.toScheme
  let xv : Y := ⟨xA, hxAV⟩
  let xv' : Y := ⟨xA', hxA'V⟩
  have hspecv : xv ⤳ xv' := by
    apply V.ι.isEmbedding.isInducing.specializes_iff.mp
    simpa [xv, xv'] using hspecA
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({xv} : Set Y), isClosed_closure⟩
  let Z : Scheme.{u} := I.subscheme
  have : IsIntegral Z := by
    have : IsReduced Z :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    have : IrreducibleSpace Z := by
      apply Scheme.IdealSheafData.irreducibleSpace_subscheme Y I
      rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact isIrreducible_singleton.closure
    exact isIntegral_of_irreducibleSpace_of_isReduced Z
  have hrange : Set.range I.subschemeι = closure ({xv} : Set Y) := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨zv', hzv'⟩ : ∃ zv' : Z, I.subschemeι zv' = xv' :=
    hrange.symm.subset (specializes_iff_mem_closure.mp hspecv)
  obtain ⟨zv, hzv⟩ : ∃ zv : Z, I.subschemeι zv = xv :=
    hrange.symm.subset (subset_closure (Set.mem_singleton xv))
  have hspecz : zv ⤳ zv' := by
    apply I.subschemeι.isEmbedding.isInducing.specializes_iff.mp
    simpa [hzv, hzv'] using hspecv
  let pZ : Z ⟶ Spec (.of A₁) := I.subschemeι ≫ V.ι ≫ p
  have hpZgeneric : pZ zv = ηA := by
    change p (V.ι (I.subschemeι zv)) = ηA
    rwa [hzv]
  have hpZclosed : pZ zv' = IsLocalRing.closedPoint A₁ := by
    change p (V.ι (I.subschemeι zv')) = IsLocalRing.closedPoint A₁
    rwa [hzv']
  have hzg : IsGenericPoint zv (Set.univ : Set Z) := by
    refine isGenericPoint_iff_specializes.mpr fun w => iff_of_true ?_ trivial
    have hwcl : I.subschemeι w ∈ closure ({xv} : Set Y) := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    apply I.subschemeι.isEmbedding.isInducing.specializes_iff.mp
    simpa [hzv] using specializes_iff_mem_closure.mpr hwcl
  have : IsDominant pZ := ⟨by
    rw [denseRange_iff_closure_range]
    have hsub : ({ηA} : Set (Spec (.of A₁))) ⊆ Set.range pZ :=
      Set.singleton_subset_iff.mpr ⟨zv, hpZgeneric⟩
    refine Set.eq_univ_of_forall fun t => ?_
    have ht : t ∈ closure ({ηA} : Set (Spec (.of A₁))) := by
      simpa only [hηA, genericPoint_closure] using (Set.mem_univ t)
    exact closure_mono hsub ht⟩
  have : IsAffine Y := hVaffine
  have : IsAffine Z := isAffine_of_isAffineHom I.subschemeι
  have : LocallyOfFiniteType pZ := inferInstance
  let j : Z ⟶ P := I.subschemeι ≫ V.ι
  have hjzv' : j zv' = xA' := by
    change V.ι (I.subschemeι zv') = xA'
    rw [hzv']
    rfl
  have hzv'closed : IsClosed
      ({pZ.asFiber zv'} : Set (pZ.fiber (pZ zv'))) := by
    change IsClosed ({(j ≫ p).asFiber zv'} : Set ((j ≫ p).fiber ((j ≫ p) zv')))
    apply isClosed_asFiber_of_isEmbedding j j.isEmbedding p zv'
    rwa [hjzv']
  have hzv'closedZ : IsClosed ({zv'} : Set Z) := by
    apply isClosed_point_of_closed_asFiber_over_closed_base pZ zv' hzv'closed
    rw [hpZclosed]
    exact IsLocalRing.isClosed_singleton_closedPoint A₁
  have hjzv : j zv = xA := by
    change V.ι (I.subschemeι zv) = xA
    rw [hzv]
    rfl
  let σ : pZ.fiber ηA ⟶ p.fiber ηA :=
    pullback.map _ _ _ _ j (𝟙 _) (𝟙 _)
      (by simp [pZ, j]) (by simp)
  have hσfst : σ ≫ p.fiberι ηA = pZ.fiberι ηA ≫ j := by
    change (pullback.lift _ _ _) ≫ pullback.fst p
      ((Spec (.of A₁)).fromSpecResidueField ηA) = _
    exact pullback.lift_fst _ _ _
  have hσ (w : pZ.fiber ηA) : p.fiberι ηA (σ w) = j (pZ.fiberι ηA w) :=
    congrArg (fun m : pZ.fiber ηA ⟶ P => m w) hσfst
  let zη : pZ.fiber ηA := (pZ.fiberHomeo ηA).symm ⟨zv, hpZgeneric⟩
  have hzη : pZ.fiberι ηA zη = zv :=
    pZ.fiberι_fiberHomeo_symm ηA ⟨zv, hpZgeneric⟩
  have hσz : σ zη = xη := by
    apply (p.fiberι ηA).isEmbedding.injective
    simpa only [hzη, hjzv, hxη] using hσ zη
  let UZ : Set (pZ.fiber ηA) := σ ⁻¹' Uη
  have hUZ : IsOpen UZ := hUη.preimage σ.continuous
  have hzUZ : zη ∈ UZ := by
    change σ zη ∈ Uη
    rwa [hσz]
  obtain ⟨w, hwUZ, hwclosed, hzvw, hwzv'⟩ :=
    exists_closed_specialization_affine_integral pZ ηA hηA zv zv' hzg hspecz hpZgeneric
      hpZclosed hzv'closedZ hηAne UZ hUZ hzUZ
  refine ⟨σ w, hwUZ, ?_, ?_, ?_⟩
  · refine (isClosed_asFiber_fiberι_iff p ηA (σ w)).mp ?_
    rw [hσ w]
    exact isClosed_asFiber_image j p _ ((isClosed_asFiber_fiberι_iff pZ ηA w).mpr hwclosed)
  · rw [← hjzv, hσ w]
    exact hzvw.map j.continuous
  · rw [← hjzv', hσ w]
    exact hwzv'.map j.continuous

private lemma exists_closed_specialization_near_distinct_base
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))))
    (hbase : f x ≠ f x')
    (U : Set (f.fiber (f x))) (hU : IsOpen U) (hxU : f.asFiber x ∈ U) :
    ∃ y : f.fiber (f x), y ∈ U ∧
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ (f.fiberι (f x) y) ∧
          (f.fiberι (f x) y) ⤳ x' := by
  obtain ⟨B₁, jX, hjXlocal, hjX, jS, hjSlocal, hjS⟩ :=
    exists_restricted_valuation_local_factor f x x' hxx'
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let A₁ : ValuationSubring (S.residueField (f x)) :=
    intersectionSubring (K := S.residueField (f x)) B₁
  let g : Spec (.of A₁) ⟶ S :=
    Spec.map (CommRingCat.ofHom jS) ≫ S.fromSpecStalk (f x')
  have hgend : g (IsLocalRing.closedPoint A₁) = f x' ∧
      g (genericPoint (Spec (.of A₁))) = f x ∧
        Spec.map (CommRingCat.ofHom A₁.subtype) ≫ g =
          S.fromSpecResidueField (f x) :=
    valuation_local_factor_maps_endpoints (hxx'.map f.continuous) A₁ jS hjSlocal hjS
  let k : A₁ →+* B₁ := ((f.residueFieldMap x).hom.comp A₁.subtype).codRestrict
    B₁.toSubring (fun a => a.2)
  have hklocal : IsLocalHom k := isLocalHom_codRestrict_intersectionSubring B₁
  let q : Spec (.of B₁) ⟶ Spec (.of A₁) := Spec.map (CommRingCat.ofHom k)
  let φ₁ : Spec (.of B₁) ⟶ X :=
    Spec.map (CommRingCat.ofHom jX) ≫ X.fromSpecStalk x'
  have hring : k.comp jS = jX.comp (f.stalkMap x').hom := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    let hs : f x ⤳ f x' := hxx'.map f.continuous
    have hnat : (S.presheaf.stalkSpecializes hs ≫ S.residue (f x)) ≫
        f.residueFieldMap x =
        f.stalkMap x' ≫ (X.presheaf.stalkSpecializes hxx' ≫ X.residue x) :=
      stalkSpecializes_residue_comp_residueFieldMap f hxx'
    have hnat' := congrArg (fun a : S.presheaf.stalk (f x') ⟶
      CommRingCat.of (X.residueField x) => a r) hnat
    have hjS'' : A₁.subtype (jS r) =
        (S.presheaf.stalkSpecializes hs ≫ S.residue (f x)).hom r := by
      simpa only [RingHom.comp_apply] using congrArg (fun a : S.presheaf.stalk (f x') →+*
        S.residueField (f x) => a r) hjS
    have hjX'' : B₁.subtype (jX ((f.stalkMap x').hom r)) =
        (X.presheaf.stalkSpecializes hxx' ≫ X.residue x).hom
          ((f.stalkMap x').hom r) := by
      simpa only [RingHom.comp_apply] using congrArg (fun a : X.presheaf.stalk x' →+*
        X.residueField x => a ((f.stalkMap x').hom r)) hjX
    change (f.residueFieldMap x).hom (A₁.subtype (jS r)) =
      B₁.subtype (jX ((f.stalkMap x').hom r))
    rw [hjS'', hjX'']
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using hnat'
  have hsq : q ≫ g = φ₁ ≫ f := by
    calc
      q ≫ g = Spec.map (CommRingCat.ofHom (k.comp jS)) ≫
          S.fromSpecStalk (f x') := by
            simp only [q, g, ← Spec.map_comp_assoc, CommRingCat.ofHom_comp]
      _ = Spec.map (CommRingCat.ofHom (jX.comp (f.stalkMap x').hom)) ≫
          S.fromSpecStalk (f x') := by rw [hring]
      _ = Spec.map (CommRingCat.ofHom jX) ≫
          (Spec.map (f.stalkMap x') ≫ S.fromSpecStalk (f x')) := by
            rw [← Spec.map_comp_assoc]
            rfl
      _ = φ₁ ≫ f := by
        rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
        rfl
  have hφend : φ₁ (IsLocalRing.closedPoint B₁) = x' ∧
      φ₁ (genericPoint (Spec (.of B₁))) = x ∧
        Spec.map (CommRingCat.ofHom B₁.subtype) ≫ φ₁ =
          X.fromSpecResidueField x :=
    valuation_local_factor_maps_endpoints hxx' B₁ jX hjXlocal hjX
  have hqclosed : q (IsLocalRing.closedPoint B₁) =
      IsLocalRing.closedPoint A₁ :=
    IsLocalRing.comap_closedPoint k
  have hqgeneric : q (genericPoint (Spec (.of B₁))) =
      genericPoint (Spec (.of A₁)) := by
    exact comap_genericPoint_eq_of_injective k fun a b hab =>
      Subtype.ext ((f.residueFieldMap x).hom.injective (congrArg B₁.subtype hab))
  let P : Scheme.{u} := pullback f g
  let ψ : Spec (.of B₁) ⟶ P := pullback.lift φ₁ q hsq.symm
  let xA : P := ψ (genericPoint (Spec (.of B₁)))
  let xA' : P := ψ (IsLocalRing.closedPoint B₁)
  have hxA' : (pullback.fst f g) xA' = x' :=
    (congrArg (fun t : Spec (.of B₁) ⟶ X => t (IsLocalRing.closedPoint B₁))
      (pullback.lift_fst φ₁ q hsq.symm)).trans hφend.1
  have hsA' : (pullback.snd f g) xA' = IsLocalRing.closedPoint A₁ :=
    (congrArg (fun t : Spec (.of B₁) ⟶ Spec (.of A₁) => t (IsLocalRing.closedPoint B₁))
      (pullback.lift_snd φ₁ q hsq.symm)).trans hqclosed
  have hxA : (pullback.fst f g) xA = x :=
    (congrArg (fun t : Spec (.of B₁) ⟶ X => t (genericPoint (Spec (.of B₁))))
      (pullback.lift_fst φ₁ q hsq.symm)).trans hφend.2.1
  have hsA : (pullback.snd f g) xA = genericPoint (Spec (.of A₁)) :=
    (congrArg (fun t : Spec (.of B₁) ⟶ Spec (.of A₁) => t (genericPoint (Spec (.of B₁))))
      (pullback.lift_snd φ₁ q hsq.symm)).trans hqgeneric
  have hspecA : xA ⤳ xA' := (genericPoint_specializes _).map ψ.continuous
  have hxA'closed : IsClosed
      ({(pullback.snd f g).asFiber xA'} :
        Set ((pullback.snd f g).fiber ((pullback.snd f g) xA'))) := by
    apply AlgebraicGeometry.isClosed_asFiber_of_isPullback
      (IsPullback.of_hasPullback f g) xA'
    rwa [hxA']
  let ηA := genericPoint (Spec (.of A₁))
  have hgiso : IsIso (g.residueFieldMap ηA) :=
    isIso_residueFieldMap_genericPoint_of_valuationSubring A₁ g hgend.2.1 hgend.2.2
  let p := pullback.snd f g
  let ρ : p.fiber ηA ⟶ f.fiber (g ηA) :=
    pullback.map _ _ _ _ (pullback.fst f g)
      (Spec.map (g.residueFieldMap ηA)) g
      (IsPullback.of_hasPullback f g).w.symm (by simp)
  have hρiso : IsIso ρ :=
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) ηA).isIso_fst_of_isIso
  have hρfst : ρ ≫ f.fiberι (g ηA) = p.fiberι ηA ≫ pullback.fst f g := by
    change (pullback.lift _ _ _) ≫ pullback.fst f (S.fromSpecResidueField (g ηA)) = _
    exact pullback.lift_fst _ _ _
  have hρ (z : p.fiber ηA) :
      f.fiberι (g ηA) (ρ z) = (pullback.fst f g) (p.fiberι ηA z) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : p.fiber ηA ⟶ X => m z) hρfst
  have hpη : p xA = ηA := hsA
  let xη : p.fiber ηA := (p.fiberHomeo ηA).symm ⟨xA, hpη⟩
  have hxη : p.fiberι ηA xη = xA := p.fiberι_fiberHomeo_symm ηA ⟨xA, hpη⟩
  have hρx : f.fiberι (g ηA) (ρ xη) = x := by
    simpa only [hxη, hxA] using hρ xη
  let eη : f.fiber (g ηA) ≃ₜ f.fiber (f x) :=
    fiberHomeoOfEq f hgend.2.1
  let eF : p.fiber ηA ≃ₜ f.fiber (f x) :=
    (Scheme.homeoOfIso (asIso ρ)).trans eη
  have heFx : eF xη = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    change f.fiberι (f x) (eη (ρ xη)) = f.fiberι (f x) (f.asFiber x)
    rw [fiberHomeoOfEq_fiberι]
    simpa only [Scheme.Hom.fiberι_asFiber] using hρx
  have heFcomp (z : p.fiber ηA) :
      f.fiberι (f x) (eF z) = (pullback.fst f g) (p.fiberι ηA z) := by
    change f.fiberι (f x) (eη (ρ z)) = _
    rw [fiberHomeoOfEq_fiberι]
    exact hρ z
  let Uη : Set (p.fiber ηA) := eF ⁻¹' U
  have hUη : IsOpen Uη := hU.preimage eF.continuous
  have hxUη : xη ∈ Uη := by
    change eF xη ∈ U
    rwa [heFx]
  have hηAne : ηA ≠ IsLocalRing.closedPoint A₁ := fun heq ↦
    hbase (hgend.2.1.symm.trans ((congrArg g heq).trans hgend.1))
  obtain ⟨z, hzU, hzclosed, hxAz, hzxA'⟩ :=
    exists_closed_specialization_over_valuationRing p ηA rfl hηAne xA xA' hspecA hpη hsA'
      hxA'closed Uη hUη hxUη
  refine ⟨eF z, hzU, ?_, ?_, ?_⟩
  · simpa only [Set.image_singleton] using eF.isClosed_image.mpr hzclosed
  · simpa only [hxA, ← heFcomp z] using hxAz.map (pullback.fst f g).continuous
  · simpa only [hxA', ← heFcomp z] using hzxA'.map (pullback.fst f g).continuous

/-- **The density conclusion of Stacks 053U**, by the argument of the source. Let
`f : X ⟶ S` be locally of finite type, let `x ⤳ x'` be a specialization in `X`, and assume `x'`
is closed in its fibre `X_{f x'}`. If `x = x'`, or if `x` and `x'` lie over different points of
`S`, then the points of `X_s`, `s = f x`, which are closed in `X_s` and lie between `x` and `x'`
are dense in the closure of `x` in `X_s`.

Those two cases are every case in which the conclusion holds, by
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`, which this theorem is the reverse
implication of. -/
public theorem closure_closedPoints_between_fiber_eq
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x'))))
    (hbase : x = x' ∨ f x ≠ f x') :
    closure {y : f.fiber (f x) |
      IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ ((f.fiberι (f x)) y) ∧
          ((f.fiberι (f x)) y) ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  rcases hbase with rfl | hbase
  · exact dense_of_initial_point_closed_in_fiber f x x hxx' hx'
  · by_cases hq : f.QuasiFiniteAt x
    · exact dense_of_initial_point_closed_in_fiber f x x' hxx'
        hq.isClopen_singleton_asFiber.isClosed
    · exact dense_of_closed_specializations_in_every_neighborhood f x x'
        (exists_closed_specialization_near_distinct_base f x x' hxx' hx' hbase)

/-- **Stacks 053U**, under the hypotheses of the tag and no others. Let `f : X ⟶ S` be locally
of finite type, let `x ⤳ x'` be a specialization in `X` with `x'` closed in its fibre
`X_{f x'}`, and set `s = f x`. Then the points of `X_s` which are closed in `X_s` and lie
between `x` and `x'` are dense in the closure of `x` in `X_s` if and only if `x = x'` or
`f x ≠ f x'`.

The reverse implication is the assertion of the tag and carries its mathematical content: it is
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq`, proved by the argument of the source.

The forward implication settles the one remaining situation, a nontrivial specialization inside
one fibre, where the density fails: a point of `X_s` closed in `X_s` which specializes to `x'`
*is* `x'`, so the set of the tag is `{x'}`, whose closure is `{x'}`, while the closure of `x` in
`X_s` is larger whenever `x ≠ x'` — for `X = 𝔸¹` over a field with `x` its generic point and
`x'` a closed point it is all of `𝔸¹`. The implication is exactly that computation, through
`AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`. Since the
source relates `f x` and `f x'` by no hypothesis, its statement overreaches there; its proof
does not, drawing the same line at the prime-avoidance step (see the module docstring). -/
@[stacks 053U "the density conclusion of the tag, under the tag's own hypotheses — `f` locally \
of finite type, `x ⤳ x'`, `x'` closed in `X_{f x'}` — together with its exact range of \
validity: the points of `X_s` closed in `X_s` and lying between `x` and `x'` are dense in the \
closure of `x` in `X_s` if and only if `x = x'` or `f x ≠ f x'`. The reverse implication is the \
tag itself, proved by the argument of the source in \
`closure_closedPoints_between_fiber_eq`; the forward implication disposes of the only remaining \
situation, a nontrivial specialization inside one fibre, where the tag's set is the single \
closed point `x'` and the density is false — a gap in the source's statement, computed in \
`closure_closedPoints_between_fiber_subset_singleton_of_eq_base` and respected by the source's \
own proof."]
public theorem closure_closedPoints_between_fiber_eq_iff
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x x' : X) (hxx' : x ⤳ x')
    (hx' : IsClosed ({f.asFiber x'} : Set (f.fiber (f x')))) :
    closure {y : f.fiber (f x) |
          IsClosed ({y} : Set (f.fiber (f x))) ∧
            x ⤳ ((f.fiberι (f x)) y) ∧
              ((f.fiberι (f x)) y) ⤳ x'} =
        closure ({f.asFiber x} : Set (f.fiber (f x))) ↔
      x = x' ∨ f x ≠ f x' := by
  refine ⟨fun h ↦ ?_, closure_closedPoints_between_fiber_eq f x x' hxx' hx'⟩
  by_cases hfe : f x = f x'
  · refine Or.inl ?_
    obtain ⟨z, hzι⟩ : ∃ z : f.fiber (f x), f.fiberι (f x) z = x' :=
      ⟨fiberHomeoOfEq f hfe.symm (f.asFiber x'), by
        rw [fiberHomeoOfEq_fiberι]
        simp only [Scheme.Hom.fiberι_asFiber]⟩
    rw [← hzι] at h
    have hmem := closure_closedPoints_between_fiber_subset_singleton_of_eq_base f x z h
      (subset_closure rfl)
    have hfin : f.fiberι (f x) (f.asFiber x) = x' := by rw [Set.mem_singleton_iff.mp hmem, hzι]
    simpa only [Scheme.Hom.fiberι_asFiber] using hfin
  · exact Or.inr hfe

end AlgebraicGeometry
