module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Witness
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossSingularityCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Curves.PushoutCompletedLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Seminormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.BranchBound
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
import all StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingUnitsSequence
import all StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardCokernelVanishing
import all StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingUnitsSequence
import all StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.SeminormalLift
import all StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
import all StacksFrontier.AlgebraicGeometry.Seminormalization.Defs
import all StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.MulticrossDelta
import all StacksFrontier.RingTheory.Branches.Completion
import all StacksFrontier.RingTheory.Serre.Reduced

/-!
# Multicross singularities and towers of glueings of two points

Let `k` be an algebraically closed field and `X` a reduced algebraic one-dimensional `k`-scheme.
At a closed point `x` of `X` whose local ring is not regular, the three conditions of
[Stacks, Tag 0C1X] are equivalent: `x` defines a multicross singularity; the delta invariant of
`X` at `x` is the number of branches of `X` at `x` minus one; and some open neighbourhood of `x`
is obtained from a nonsingular scheme by finitely many glueings of two rational points.

## Main definitions

* `Stacks.Curves.IsGlueingTower` — a tower `X_n ⟶ X_{n-1} ⟶ … ⟶ X_0 = X` of glueings of two
  rational points with `X_n` nonsingular, recursively on its length.
* `Stacks.Curves.HasNonsingularGlueingResolution` — clause (3) of [Stacks, Tag 0C1X]: such a
  tower exists over an open neighbourhood of the point.

## Main results

* `Stacks.Curves.isMulticrossSingularity_tfae` — the equivalence of the three clauses.
* `Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point`
  and
  `Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_specPolynomial` — the
  equivalence as displayed is false at a nonsingular closed point, and at the origin of the
  affine line.

## Implementation notes

The equivalence of clauses (1) and (2) is not reproved here: it is
`Stacks.Curves.isMulticrossSingularity_iff_deltaInvariant_eq_of_not_isRegularLocalRing`, the
scheme-level form of [Stacks, Tag 0C1V]. Like it, the statement is restricted to a closed point
whose local ring is not regular, because the source's unrestricted equivalence is false at a
nonsingular closed point: there the delta invariant is `0` and the number of branches is `1`, so
clause (2) holds while clause (1) fails, Definition 0C1W asking for at least two branches. That
is not an assertion about the source but a proved statement of this file:
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point`
refutes the displayed equivalence at any nonsingular closed point, and
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_specPolynomial` does so
at the origin of the affine line, a scheme whose hypotheses are discharged rather than carried.

Clause (3) implies clause (1) through the local structure of one glueing step. The completed
local ring at the glued point is the fibre product of the completed local rings at the two points
above it over the residue field, by [Stacks, Tag 0E36] applied to the pushout presentation of the
glueing; such a fibre product is a multicross ring or a field, and over every other point the
step is an isomorphism on stalks. Both statements are carried by
`Stacks.Curves.HasMulticrossOrFieldCompletion`, which has to allow a field because the top of the
tower is merely nonsingular, not singular.

Clause (1) implies clause (3) on an open neighbourhood on which `x` is the only singular point.
[Stacks, Tag 0C1L] factors the normalization morphism of that neighbourhood into glueings of two
points and squishings of tangent vectors, and the work is to rule out the squishings. The source
does so numerically: at the first squishing the number of branches is unchanged while the delta
invariant drops by one, which by [Stacks, Tag 0C1V] contradicts the point below being multicross.
The argument here reads the same obstruction off the completion instead, since a multicross ring
is seminormal and a squishing produces a non-seminormal completion; seminormality propagates up
the chain through the glueings, so no step anywhere in it can be a squishing.

The chain of [Stacks, Tag 0C1L] is an inductive predicate on one morphism, while clause (3) is a
sequence indexed by its length, so the two are joined by `Stacks.Curves.HasGlueingTowerTo`, a
tower whose top is only identified up to isomorphism. That is what makes the two halves of a
composite chain stackable: the isomorphism between them is absorbed into the first glueing step
by `Stacks.Curves.isGlueingTwoPoints_comp_iso`.

## References

* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
* [Stacks Project, Tag 0E36](https://stacks.math.columbia.edu/tag/0E36)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.Normalization (finite_irreducibleComponents_of_isNagataScheme)

universe u v w

namespace Stacks.Curves

private theorem isSeminormalRing_multicross (k : Type*) [Field k] (n : ℕ) :
    IsSeminormalRing (Stacks.Curves.multicross k n) := by
  intro x y hxy
  have h (i : Fin n) : ∃ z : PowerSeries k, x.1 i = z ^ 2 ∧ y.1 i = z ^ 3 := by
    apply ExistsUnique.exists
    apply isSeminormalRing_of_isIntegrallyClosed
    exact congrArg (fun f : Stacks.Curves.multicross k n => f.1 i) hxy
  choose z hz₂ hz₃ using h
  have hz : z ∈ Stacks.Curves.multicross k n := by
    intro i j
    apply Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
    · rw [← map_pow, ← map_pow, ← hz₂ i, ← hz₂ j]
      exact x.2 i j
    · rw [← map_pow, ← map_pow, ← hz₃ i, ← hz₃ j]
      exact y.2 i j
  let z' : Stacks.Curves.multicross k n := ⟨z, hz⟩
  have hx : x = z' ^ 2 := Subtype.ext (funext hz₂)
  have hy : y = z' ^ 3 := Subtype.ext (funext hz₃)
  refine ⟨z', ⟨hx, hy⟩, fun w hw => ?_⟩
  apply Subtype.ext
  funext i
  exact Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
    (congrArg (fun f : Stacks.Curves.multicross k n => f.1 i) (hw.1.symm.trans hx))
    (congrArg (fun f : Stacks.Curves.multicross k n => f.1 i) (hw.2.symm.trans hy))

private theorem isSeminormalRing_of_retract {R S : Type*} [CommRing R] [CommRing S]
    (i : R →+* S) (r : S →+* R) (h : r.comp i = RingHom.id R)
    (hS : IsSeminormalRing S) : IsSeminormalRing R := by
  have hr (x : R) : r (i x) = x := congrArg (fun f => f x) h
  intro x y hxy
  obtain ⟨z, hz, hu⟩ := hS (i x) (i y) (by simpa only [← map_pow] using congrArg i hxy)
  have hx : x = r z ^ 2 := by simpa only [map_pow, hr] using congrArg r hz.1
  have hy : y = r z ^ 3 := by simpa only [map_pow, hr] using congrArg r hz.2
  refine ⟨r z, ⟨hx, hy⟩, fun w hw => ?_⟩
  have hiw : i w = z := hu _ ⟨by rw [hw.1, map_pow], by rw [hw.2, map_pow]⟩
  simpa only [hr] using congrArg r hiw


private theorem map_mem_range_of_sq_cube_mem_range
    {A B S T : Type*} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [IsReduced T]
    (f : A →+* B) (g : A →+* S) (i : B →+* T) (j : S →+* T)
    (hcomm : i.comp f = j.comp g) (hinj : Function.Injective f)
    (hS : IsSeminormalRing S)
    (b : B) (h₂ : b ^ 2 ∈ f.range) (h₃ : b ^ 3 ∈ f.range) :
    i b ∈ j.range := by
  obtain ⟨a₂, ha₂⟩ := h₂
  obtain ⟨a₃, ha₃⟩ := h₃
  have ha : a₂ ^ 3 = a₃ ^ 2 := hinj (by simp only [map_pow, ha₂, ha₃, ← pow_mul])
  obtain ⟨z, hz, _⟩ := hS (g a₂) (g a₃)
    (by simpa only [← map_pow] using congrArg g ha)
  refine ⟨z, ?_⟩
  apply Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
  · rw [← map_pow, ← map_pow, ← hz.1, ← ha₂]
    exact congrArg (fun φ => φ a₂) hcomm.symm
  · rw [← map_pow, ← map_pow, ← hz.2, ← ha₃]
    exact congrArg (fun φ => φ a₃) hcomm.symm

private theorem isSeminormalRing_factors_of_eqLocus
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (ρ : R →+* k) (σ : S →+* k)
    (hρ : ρ.comp (algebraMap k R) = RingHom.id k)
    (hσ : σ.comp (algebraMap k S) = RingHom.id k)
    (h : IsSeminormalRing ((ρ.comp (RingHom.fst R S)).eqLocus
      (σ.comp (RingHom.snd R S)))) : IsSeminormalRing R ∧ IsSeminormalRing S := by
  let E := (ρ.comp (RingHom.fst R S)).eqLocus (σ.comp (RingHom.snd R S))
  let iR : R →+* E := ((RingHom.id R).prod ((algebraMap k S).comp ρ)).codRestrict E (by
    intro r
    exact (congrArg (fun f => f (ρ r)) hσ).symm)
  let iS : S →+* E := (((algebraMap k R).comp σ).prod (RingHom.id S)).codRestrict E (by
    intro s
    exact congrArg (fun f => f (σ s)) hρ)
  exact ⟨isSeminormalRing_of_retract iR ((RingHom.fst R S).comp E.subtype) rfl h,
    isSeminormalRing_of_retract iS ((RingHom.snd R S).comp E.subtype) rfl h⟩

open scoped TensorProduct in
private theorem isReduced_tensor_adicCompletion_of_isNagataRing
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B] [IsReduced B]
    (hB : IsNagataRing B) (p : Ideal A) [p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p] [IsLocalRing Ap] :
    IsReduced (AdicCompletion (maximalIdeal Ap) Ap ⊗[A] B) := by
  haveI : IsNoetherianRing B := hB.1
  have hred (q : p.primesOver B) :
      IsReduced (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)) := by
    have hq : IsNagataRing (Localization.AtPrime q.1) :=
      isNagata_of_isLocalization B q.1.primeCompl (Localization.AtPrime q.1) hB
    exact (reducedness_and_adicCompletion.{_, 0} (Localization.AtPrime q.1)).2.2 hq
      |>.mp inferInstance
  letI := hred
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := B) p Ap
    (fun q => Localization.AtPrime q.1)
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A _ _).toRingEquiv.trans e.toRingEquiv).toRingHom
    ((Algebra.TensorProduct.comm A _ _).toRingEquiv.trans e.toRingEquiv).injective

private theorem isField_of_reduced_dim_zero (S : Type*) [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] [IsReduced S]
    (hdim : ringKrullDim S = 0) : IsField S := by
  have hmh : (IsLocalRing.maximalIdeal S).height = 0 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)
    rw [hdim] at h
    exact_mod_cast h
  have hmin : IsLocalRing.maximalIdeal S ∈ minimalPrimes S := by
    rw [← Ideal.height_eq_zero_iff]
    exact hmh
  have huniq : ∀ (p : Ideal S), p.IsPrime → p = IsLocalRing.maximalIdeal S := by
    intro p hp
    have hpm : p ≤ IsLocalRing.maximalIdeal S :=
      IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    obtain ⟨⟨_, _⟩, hmindown⟩ := hmin
    exact ((hmindown ⟨inferInstance, bot_le⟩ hpm).antisymm hpm).symm
  have hmle : IsLocalRing.maximalIdeal S ≤ nilradical S := by
    rw [nilradical_eq_sInf_minimalPrimes]
    apply le_sInf
    intro q hq
    have hq' : q.IsPrime := hq.isPrime
    rw [huniq q hq']
  have hm0 : IsLocalRing.maximalIdeal S = ⊥ := by
    rw [nilradical_eq_zero S] at hmle
    exact le_bot_iff.mp hmle
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm0

private theorem ringKrullDim_stalk_eq_one_of_singular
    (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [IsReduced X] (hX : topologicalKrullDim X = 1) (x : X)
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  let A := X.presheaf.stalk x
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  letI : IsNoetherianRing A := inferInstance
  letI : IsReduced A := inferInstance
  have hle : ringKrullDim A ≤ 1 := by
    have h := AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim x
    rwa [hX] at h
  have hnezero : ringKrullDim A ≠ 0 := by
    intro hdim
    -- A reduced Noetherian local ring of dimension `0` is a field, and a field is regular:
    -- its maximal ideal is `⊥`, which is generated by `0 = dim A` elements.
    refine hsing ((isRegularLocalRing_iff A).mpr ?_)
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (isField_of_reduced_dim_zero A hdim),
      Submodule.spanFinrank_bot, hdim]
    rfl
  have hnebot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have hnetop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  rcases hdimA : ringKrullDim A with _ | d
  · exact (hnebot hdimA).elim
  · rcases d with _ | n
    · exact (hnetop hdimA).elim
    · have hnle : n ≤ 1 := by
        have hle' := hle
        rw [hdimA] at hle'
        exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hle')
      have hnzero : n ≠ 0 := by
        intro hz
        apply hnezero
        rw [hdimA, hz]
        rfl
      have hn : n = 1 := by omega
      change ((n : ℕ∞) : WithBot ℕ∞) = (1 : WithBot ℕ∞)
      exact congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hn

private theorem stalk_residueField_algEquiv {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Nonempty (X.residueField x ≃ₐ[k] k) := by
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  letI : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have hclosed := isClosed_singleton_iff_isClosedImmersion.mp hx
    infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @LocallyOfFiniteType)] at hcomp
  letI : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    · rfl
    · simp only [RingHom.algebraMap_toAlgebra]
      rw [← Scheme.Γevaluation_naturality]
      simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  letI : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  letI : Algebra.IsAlgebraic k (X.residueField x) :=
    Algebra.IsAlgebraic.of_finite _ _
  letI : Algebra.IsIntegral k (X.residueField x) := inferInstance
  have hbij : Function.Bijective (algebraMap k (X.residueField x)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] X.residueField x :=
    AlgEquiv.ofBijective (Algebra.ofId k (X.residueField x)) hbij
  exact ⟨e.symm⟩

private theorem exists_open_meets_singularLocus_only_at
    {k : Type u} [Field k] {X : Scheme.{u}} [IsReduced X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ AlgebraicGeometry.singularLocus X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∀ y ∈ U, y ∈ AlgebraicGeometry.singularLocus X → y = x := by
  let D : Set X := AlgebraicGeometry.singularLocus X
  haveI : DiscreteTopology D :=
    AlgebraicGeometry.discreteTopology_singularLocus_of_isNagataScheme X hNagata hdim.le
  have hD : _root_.IsDiscrete D := isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨U, hU, hUcap⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp hD) x hx
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · have hxU : x ∈ U ∩ D := by rw [hUcap]; simp
    exact hxU.1
  · intro y hyU hyD
    have hyCap : y ∈ U ∩ D := ⟨hyU, hyD⟩
    have hySingleton : y ∈ ({x} : Set X) := by
      simpa [hUcap] using hyCap
    exact Set.mem_singleton_iff.mp hySingleton

private def multicrossResidue {k : Type*} [CommRing k] {n : ℕ} (i : Fin n) :
    Stacks.Curves.multicross k n →+* k :=
  PowerSeries.constantCoeff.comp ((Pi.evalRingHom _ i).comp (Stacks.Curves.multicross k n).subtype)

private def multicrossEqLocusRingEquiv {k : Type*} [CommRing k] {m n : ℕ}
    (i : Fin m) (j : Fin n) :
    ((multicrossResidue (k := k) i).comp
        (RingHom.fst (Stacks.Curves.multicross k m) (Stacks.Curves.multicross k n))).eqLocus
      ((multicrossResidue (k := k) j).comp
        (RingHom.snd (Stacks.Curves.multicross k m) (Stacks.Curves.multicross k n))) ≃+*
        Stacks.Curves.multicross k (m + n) where
  toFun f := ⟨Fin.append f.1.1.1 f.1.2.1, by
    intro a b
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;>
      refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · simpa using f.1.1.2 a b
    · simp only [Fin.append_left, Fin.append_right]
      exact (f.1.1.2 a i).trans (f.2.trans (f.1.2.2 j b))
    · simp only [Fin.append_left, Fin.append_right]
      exact (f.1.2.2 a j).trans (f.2.symm.trans (f.1.1.2 i b))
    · simpa using f.1.2.2 a b⟩
  invFun f := ⟨(⟨fun a => f.1 (a.castAdd n), fun a b => f.2 _ _⟩,
    ⟨fun b => f.1 (b.natAdd m), fun a b => f.2 _ _⟩), f.2 _ _⟩
  left_inv f := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> funext a <;> simp
  right_inv f := by
    apply Subtype.ext
    funext a
    exact Fin.addCases (fun a => by simp) (fun a => by simp) a
  map_mul' f g := by
    apply Subtype.ext
    funext a
    exact Fin.addCases (fun a => by simp) (fun a => by simp) a
  map_add' f g := by
    apply Subtype.ext
    funext a
    exact Fin.addCases (fun a => by simp) (fun a => by simp) a

private theorem multicrossEqLocusRingEquiv_coefficients {k : Type*} [CommRing k]
    {m n : ℕ} (i : Fin m) (j : Fin n) (a : k) :
    multicrossEqLocusRingEquiv i j
      ⟨(⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩,
          ⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩), rfl⟩ =
        ⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩ := by
  apply Subtype.ext
  funext x
  exact Fin.addCases (fun _ => by simp [multicrossEqLocusRingEquiv])
    (fun _ => by simp [multicrossEqLocusRingEquiv]) x

private def ringEquivEqLocusOfIsPullback
    {k A R S : Type u} [CommRing k] [CommRing A] [CommRing R] [CommRing S]
    (f : A →+* k) (g : A →+* R × S) (ρ : R →+* k) (σ : S →+* k)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prodMap σ))) :
    A ≃+* ((ρ.comp (RingHom.fst R S)).eqLocus (σ.comp (RingHom.snd R S))) := by
  have hw (a : A) : (f a, f a) = (ρ (g a).1, σ (g a).2) :=
    congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of (k × k) => q.hom a) h.w
  let φ : A →+* ((ρ.comp (RingHom.fst R S)).eqLocus (σ.comp (RingHom.snd R S))) :=
    g.codRestrict _ (fun a => (congrArg Prod.fst (hw a)).symm.trans (congrArg Prod.snd (hw a)))
  have ht := h.map (forget CommRingCat)
  refine RingEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro a b hab
    have hgab : g a = g b := congrArg Subtype.val hab
    apply CategoryTheory.Limits.Types.ext_of_isPullback ht
    · change f a = f b
      exact (congrArg Prod.fst (hw a)).trans
        ((congrArg (fun q : R × S => ρ q.1) hgab).trans
          (congrArg Prod.fst (hw b)).symm)
    · exact hgab
  · intro b
    obtain ⟨a, ha, hb⟩ := CategoryTheory.Limits.Types.exists_of_isPullback ht (ρ b.1.1) b.1 (by
      change (ρ b.1.1, ρ b.1.1) = (ρ b.1.1, σ b.1.2)
      exact Prod.ext rfl b.2)
    exact ⟨a, Subtype.ext hb⟩

private def eqLocus_left_id_ringEquiv {k R : Type u} [CommRing k] [CommRing R]
    (ρ : R →+* k) :
    ((RingHom.id k).comp (RingHom.fst k R)).eqLocus
      (ρ.comp (RingHom.snd k R)) ≃+* R where
  toFun x := x.1.2
  invFun r := ⟨(ρ r, r), rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact x.2.symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def ringEquiv_right_of_isPullback_left_id
    {k A R : Type u} [CommRing k] [CommRing A] [CommRing R]
    (f : A →+* k) (g : A →+* k × R) (ρ : R →+* k)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((RingHom.id k).prodMap ρ))) :
    A ≃+* R :=
  (ringEquivEqLocusOfIsPullback f g (RingHom.id k) ρ h).trans
    (eqLocus_left_id_ringEquiv ρ)

private theorem nonempty_algEquiv_right_of_isPullback_left_id
    {k A R : Type u} [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R]
    (f : A →+* k) (g : A →+* k × R) (ρ : R →+* k)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((RingHom.id k).prodMap ρ)))
    (hg : ∀ c : k, g (algebraMap k A c) = (c, algebraMap k R c)) :
    Nonempty (A ≃ₐ[k] R) := by
  let e := ringEquiv_right_of_isPullback_left_id f g ρ h
  refine ⟨{ e with commutes' := ?_ }⟩
  intro c
  exact congrArg Prod.snd (hg c)

private theorem nonempty_algEquiv_multicross_of_isPullback
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {m n : ℕ} (i : Fin m) (j : Fin n)
    (f : A →+* k) (g : A →+* Stacks.Curves.multicross k m × Stacks.Curves.multicross k n)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((multicrossResidue i).prodMap (multicrossResidue j))))
    (hg : ∀ a : k, g (algebraMap k A a) =
      (⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩,
        ⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩)) :
    letI : Algebra k (Stacks.Curves.multicross k (m + n)) :=
      Stacks.Curves.multicrossAlgebra k (m + n)
    Nonempty (A ≃ₐ[k] Stacks.Curves.multicross k (m + n)) := by
  letI : Algebra k (Stacks.Curves.multicross k (m + n)) := Stacks.Curves.multicrossAlgebra k (m + n)
  let e₀ := ringEquivEqLocusOfIsPullback f g (multicrossResidue i) (multicrossResidue j) h
  let e := e₀.trans (multicrossEqLocusRingEquiv i j)
  refine ⟨{ e with commutes' := ?_ }⟩
  intro a
  have he : e₀ (algebraMap k A a) =
      ⟨(⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩,
          ⟨fun _ => PowerSeries.C a, by simp [Stacks.Curves.mem_multicross]⟩), rfl⟩ :=
    Subtype.ext (hg a)
  change multicrossEqLocusRingEquiv i j (e₀ (algebraMap k A a)) = _
  rw [he]
  exact multicrossEqLocusRingEquiv_coefficients i j a

private theorem isPullback_piFinTwo
    {k A : Type u} [CommRing k] [CommRing A]
    (R : Fin 2 → Type u) [∀ i, CommRing (R i)]
    (f : A →+* k) (g : A →+* (∀ i, R i)) (ρ : ∀ i, R i →+* k)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (RingHom.pi fun _ : Fin 2 => RingHom.id k))
      (CommRingCat.ofHom (RingHom.pi fun i => (ρ i).comp (Pi.evalRingHom R i)))) :
    IsPullback (CommRingCat.ofHom f)
      (CommRingCat.ofHom ((RingEquiv.piFinTwo R).toRingHom.comp g))
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((ρ 0).prodMap (ρ 1))) := by
  apply h.of_iso (Iso.refl _) (Iso.refl _)
    (RingEquiv.piFinTwo R).toCommRingCatIso
    (RingEquiv.piFinTwo (fun _ : Fin 2 => k)).toCommRingCatIso
  · simp
  · rfl
  · ext x <;> rfl
  · ext x <;> rfl

private theorem isPullback_prod_to_piFinTwo
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (f : A →+* k) (g : A →+* B) (ρ σ : B →+* k)
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prod σ))) :
    IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (RingHom.pi fun _ : Fin 2 => RingHom.id k))
      (CommRingCat.ofHom
        ((RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toRingHom.comp (ρ.prod σ))) := by
  apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toCommRingCatIso
  · rfl
  · rfl
  · ext x i
    fin_cases i <;> rfl
  · rfl

private theorem isPullback_congr_ringEquiv
    {A B C D A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [CommRing A'] [CommRing B']
    (f : A →+* C) (g : A →+* B) (h : C →+* D) (j : B →+* D)
    (eA : A' ≃+* A) (eB : B' ≃+* B)
    (hp : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom j)) :
    IsPullback (CommRingCat.ofHom (f.comp eA.toRingHom))
      (CommRingCat.ofHom (eB.symm.toRingHom.comp (g.comp eA.toRingHom)))
      (CommRingCat.ofHom h)
      (CommRingCat.ofHom (j.comp eB.toRingHom)) := by
  apply hp.of_iso eA.symm.toCommRingCatIso (Iso.refl _)
    eB.symm.toCommRingCatIso (Iso.refl _)
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp

private theorem specMap_piFinTwo_eval_zero
    {k B : Type u} [CommRing k] [CommRing B] (ρ σ : B →+* k) :
    (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 0)) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          ((RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toRingHom.comp
            (ρ.prod σ)))) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ) := by
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1

private theorem specMap_piFinTwo_eval_one
    {k B : Type u} [CommRing k] [CommRing B] (ρ σ : B →+* k) :
    (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 1)) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          ((RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toRingHom.comp
            (ρ.prod σ)))) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ) := by
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1

section

private theorem app_injective_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) (V : X.Opens) :
    Function.Injective (f.app V) := by
  obtain ⟨_, _, _, _, _, _, _, _, hab, _, ⟨U, hU, hIso⟩, hinj, _⟩ := h
  let := hIso
  suffices hz : ∀ s : Γ(X, V), f.app V s = 0 → s = 0 by
    intro s t hst
    exact sub_eq_zero.mp (hz (s - t) (by simp [hst]))
  intro s hs
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.2
  intro y hy
  by_cases heq : y = (a ≫ f) (IsLocalRing.closedPoint k)
  · subst y
    obtain ⟨W, hWV, hxW, hW⟩ := hinj V hy s
      ⟨V, le_rfl, hy, by simpa using hs⟩
    refine ⟨W, hWV, hxW, ?_⟩
    change X.presheaf.map (homOfLE hWV).op s = X.presheaf.map (homOfLE hWV).op 0
    simpa using hW
  · have hyU : y ∈ U := by
      rw [← SetLike.mem_coe, hU]
      exact heq
    let W := U ⊓ V
    let : IsIso (f.app W) :=
      Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict f U W inf_le_left
    refine ⟨W, inf_le_right, ⟨hyU, hy⟩, ?_⟩
    change X.presheaf.map (homOfLE (show W ≤ V from inf_le_right)).op s =
      X.presheaf.map (homOfLE (show W ≤ V from inf_le_right)).op 0
    apply (ConcreteCategory.bijective_of_isIso (f.app W)).1
    have hn := congrArg (fun g : Γ(X, V) ⟶ Γ(X', f ⁻¹ᵁ W) => g s)
      (f.naturality (homOfLE (show W ≤ V from inf_le_right)).op)
    simpa only [CommRingCat.comp_apply, hs, map_zero] using hn

private theorem exists_section_of_locally_mem_range
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hinj : ∀ U, Function.Injective (f.app U)) (U : Y.Opens)
    (s : Γ(X, f ⁻¹ᵁ U))
    (hlocal : ∀ y ∈ U, ∃ (V : Y.Opens) (_hyV : y ∈ V) (hVU : V ≤ U)
      (t : Γ(Y, V)), f.app V t =
        X.presheaf.map (homOfLE (f.preimage_mono hVU)).op s) :
    ∃ t : Γ(Y, U), f.app U t = s := by
  choose V hyV hVU t ht using fun y : U => hlocal y.1 y.2
  have hcover : U ≤ iSup V := by
    intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  have hc : TopCat.Presheaf.IsCompatible Y.presheaf V t := by
    intro y z
    apply hinj (V y ⊓ V z)
    have hleft := f.naturality (Opens.infLELeft (V y) (V z)).op
    have hright := f.naturality (Opens.infLERight (V y) (V z)).op
    rw [← CommRingCat.comp_apply, hleft, CommRingCat.comp_apply, ht]
    conv_rhs =>
      rw [← CommRingCat.comp_apply, hright, CommRingCat.comp_apply, ht]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  obtain ⟨r, hr, _⟩ := Y.sheaf.existsUnique_gluing' V U
    (fun y => homOfLE (hVU y)) hcover t hc
  refine ⟨r, ?_⟩
  apply X.sheaf.eq_of_locally_eq' (fun y => f ⁻¹ᵁ V y) (f ⁻¹ᵁ U)
    (fun y => homOfLE (f.preimage_mono (hVU y)))
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨f y, hy⟩, hyV ⟨f y, hy⟩⟩
  · intro y
    have hn := f.naturality (homOfLE (hVU y)).op
    change ((f.app U ≫
      X.presheaf.map ((Opens.map f.base).map (homOfLE (hVU y)).op.unop).op).hom r) = _
    rw [← hn]
    change (f.app (V y)).hom ((Y.sheaf.obj.map (homOfLE (hVU y)).op).hom r) = _
    rw [hr]
    exact ht y

private theorem sectionAt_app
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : AlgebraicGeometry.Spec (.of k) ⟶ X) (U : Y.Opens)
    (ha : (a ≫ f) (IsLocalRing.closedPoint k) ∈ U) (s : Γ(Y, U)) :
    AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) ha (f.app U s) =
      AlgebraicGeometry.sectionAt (a ≫ f) U ha s := by
  change (f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) _ ha ≫
    Scheme.stalkClosedPointTo a).hom s =
    (Y.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f)).hom s
  rw [Scheme.stalkClosedPointTo_comp]
  exact congrArg (fun g : Γ(Y, U) ⟶ CommRingCat.of k => g.hom s)
    ((Scheme.Hom.germ_stalkMap_assoc f U (a (IsLocalRing.closedPoint k)) ha
      (Scheme.stalkClosedPointTo a)).symm)

private theorem mem_range_app_iff_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (U : X.Opens) (ha : (a ≫ f) (IsLocalRing.closedPoint k) ∈ U)
    (hb : (b ≫ f) (IsLocalRing.closedPoint k) ∈ U)
    (s : Γ(X', f ⁻¹ᵁ U)) :
    s ∈ Set.range (f.app U) ↔
      AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ U) ha s =
        AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) hb s := by
  have hinj := app_injective_of_isGlueingTwoPoints f a b h
  obtain ⟨_, _, _, _, _, _, _, _, hab, _, ⟨V, hV, hIso⟩, _, hexact, _⟩ := h
  constructor
  · rintro ⟨t, rfl⟩
    rw [sectionAt_app, sectionAt_app]
    congr 1
  · intro hs
    apply exists_section_of_locally_mem_range f hinj U s
    intro y hy
    by_cases heq : y = (a ≫ f) (IsLocalRing.closedPoint k)
    · subst y
      obtain ⟨W, hWU, hxW, t, ht⟩ := hexact U ha s (sub_eq_zero.mpr hs)
      exact ⟨W, hxW, hWU, t, ht.symm⟩
    · have hyV : y ∈ V := by
        rw [← SetLike.mem_coe, hV]
        exact heq
      let W := V ⊓ U
      let := hIso
      let : IsIso (f.app W) :=
        Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict f V W inf_le_left
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (f.app W)).2
        (X'.presheaf.map (homOfLE (f.preimage_mono (show W ≤ U from inf_le_right))).op s)
      exact ⟨W, ⟨hyV, hy⟩, inf_le_right, t, ht⟩

private theorem isPullback_of_injective_of_range_eqLocus
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    (f : A →+* k) (g : A →+* B) (ρ σ : B →+* k)
    (hρ : ρ.comp g = f) (hσ : σ.comp g = f)
    (hinj : Function.Injective g)
    (hrange : ∀ b, b ∈ Set.range g ↔ ρ b = σ b) :
    IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prod σ)) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  rw [CategoryTheory.Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    change (f a, f a) = (ρ (g a), σ (g a))
    exact Prod.ext (congrArg (fun h : A →+* k => h a) hρ).symm
      (congrArg (fun h : A →+* k => h a) hσ).symm
  · intro a b hab
    exact hinj hab.2
  · intro c b hcb
    have hρb : c = ρ b := congrArg Prod.fst hcb
    have hσb : c = σ b := congrArg Prod.snd hcb
    obtain ⟨a, rfl⟩ := (hrange b).mpr (hρb.symm.trans hσb)
    exact ⟨a, (congrArg (fun h : A →+* k => h a) hρ).symm.trans hρb.symm, rfl⟩

private theorem isPullback_sections_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (U : X.Opens) (ha : (a ≫ f) (IsLocalRing.closedPoint k) ∈ U)
    (hb : (b ≫ f) (IsLocalRing.closedPoint k) ∈ U) :
    IsPullback (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f))
      (f.app U) (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom
        ((X'.presheaf.germ (f ⁻¹ᵁ U) _ ha ≫ Scheme.stalkClosedPointTo a).hom.prod
          (X'.presheaf.germ (f ⁻¹ᵁ U) _ hb ≫ Scheme.stalkClosedPointTo b).hom)) := by
  apply isPullback_of_injective_of_range_eqLocus
  · ext s
    exact sectionAt_app f a U ha s
  · ext s
    have hab : a ≫ f = b ≫ f := h.2.2.2.2.2.2.2.2.choose
    have heq := sectionAt_app f b U hb s
    change AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ U) hb (f.app U s) =
      AlgebraicGeometry.sectionAt (a ≫ f) U ha s
    rw [heq]
    congr 1
    exact hab.symm
  · exact app_injective_of_isGlueingTwoPoints f a b h U
  · exact mem_range_app_iff_of_isGlueingTwoPoints f a b h U ha hb

private theorem sectionAt_coefficient
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (.of k))]
    (a : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (haover : a ≫ (X ↘ AlgebraicGeometry.Spec (.of k)) = 𝟙 _)
    (U : X.Opens) (ha : a (IsLocalRing.closedPoint k) ∈ U) (c : k) :
    AlgebraicGeometry.sectionAt a U ha
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom c) = c := by
  refine (AlgebraicGeometry.sectionAt_map a (homOfLE (show U ≤ ⊤ from le_top)) ha
    ((X ↘ AlgebraicGeometry.Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c))).trans ?_
  refine (sectionAt_app (X ↘ AlgebraicGeometry.Spec (.of k)) a ⊤ trivial
    ((Scheme.ΓSpecIso (.of k)).inv c)).trans ?_
  simp only [haover]
  have hid := Scheme.germ_stalkClosedPointTo_Spec (𝟙 (CommRingCat.of k))
  rw [AlgebraicGeometry.Spec.map_id, Category.comp_id] at hid
  change (((Scheme.ΓSpecIso (.of k)).inv ≫
    (AlgebraicGeometry.Spec (.of k)).presheaf.germ ⊤ _ trivial ≫
      Scheme.stalkClosedPointTo (𝟙 _)).hom c) = c
  rw [hid, Iso.inv_hom_id]
  rfl

private theorem prod_surjective_of_common_section_of_sub_eq_one
    {k R : Type*} [CommRing k] [CommRing R] (ρ σ : R →+* k) (ι : k →+* R)
    (hρ : ρ.comp ι = RingHom.id k) (hσ : σ.comp ι = RingHom.id k)
    (s : R) (hs : ρ s - σ s = 1) : Function.Surjective (ρ.prod σ) := by
  have hρ' (c : k) : ρ (ι c) = c := congrArg (fun h : k →+* k => h c) hρ
  have hσ' (c : k) : σ (ι c) = c := congrArg (fun h : k →+* k => h c) hσ
  rintro ⟨c, d⟩
  refine ⟨ι (c - d) * (s - ι (σ s)) + ι d, ?_⟩
  apply Prod.ext
  · change ρ _ = c
    simp only [map_add, map_mul, map_sub, hρ', hs, mul_one]
    ring
  · change σ _ = d
    simp only [map_add, map_mul, map_sub, hσ', sub_self, mul_zero, zero_add]

private theorem exists_isAffineOpen_pairEvaluation_surjective
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (U : X.Opens) (hx : (a ≫ f) (IsLocalRing.closedPoint k) ∈ U) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U)
      (ha : (a ≫ f) (IsLocalRing.closedPoint k) ∈ V)
      (hb : (b ≫ f) (IsLocalRing.closedPoint k) ∈ V),
      Function.Surjective
        ((X'.presheaf.germ (f ⁻¹ᵁ V) _ ha ≫ Scheme.stalkClosedPointTo a).hom.prod
          (X'.presheaf.germ (f ⁻¹ᵁ V) _ hb ≫ Scheme.stalkClosedPointTo b).hom) := by
  obtain ⟨haover, hbover, _, _, _, _, _, _, hab, _, _, _, _, hsurj⟩ := h
  obtain ⟨W, hxW, s, hs⟩ := hsurj 1
  obtain ⟨V, hV, hxV, hVWU⟩ := exists_isAffineOpen_mem_and_subset
    (show (a ≫ f) (IsLocalRing.closedPoint k) ∈ W ⊓ U from ⟨hxW, hx⟩)
  have hb : (b ≫ f) (IsLocalRing.closedPoint k) ∈ V := by rwa [← hab]
  refine ⟨V, hV, hVWU.trans inf_le_right, hxV, hb, ?_⟩
  let ρ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ hxV ≫ Scheme.stalkClosedPointTo a).hom
  let σ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ hb ≫ Scheme.stalkClosedPointTo b).hom
  let ι : k →+* Γ(X', f ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X' ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
      X'.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ ⊤ from le_top)).op).hom
  have hρ : ρ.comp ι = RingHom.id k := by
    ext c
    exact sectionAt_coefficient a haover.comp_over (f ⁻¹ᵁ V) hxV c
  have hσ : σ.comp ι = RingHom.id k := by
    ext c
    exact sectionAt_coefficient b hbover.comp_over (f ⁻¹ᵁ V) hb c
  let hVW : V ≤ W := hVWU.trans inf_le_left
  let t := X'.presheaf.map (homOfLE (f.preimage_mono hVW)).op s
  have ha' := AlgebraicGeometry.sectionAt_map a (homOfLE (f.preimage_mono hVW)) hxV s
  have hb' := AlgebraicGeometry.sectionAt_map b (homOfLE (f.preimage_mono hVW)) hb s
  have key : AlgebraicGeometry.sectionAt a (f ⁻¹ᵁ V) hxV t -
      AlgebraicGeometry.sectionAt b (f ⁻¹ᵁ V) hb t = 1 := by
    dsimp only [t]
    rw [ha', hb']
    exact hs
  exact prod_surjective_of_common_section_of_sub_eq_one ρ σ ι hρ hσ t key

private theorem exists_isAffineOpen_piPullback_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (U : X.Opens) (hx : (a ≫ f) (IsLocalRing.closedPoint k) ∈ U) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U)
      (ha : (a ≫ f) (IsLocalRing.closedPoint k) ∈ V)
      (hb : (b ≫ f) (IsLocalRing.closedPoint k) ∈ V),
      let ρ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ ha ≫ Scheme.stalkClosedPointTo a).hom
      let σ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ hb ≫ Scheme.stalkClosedPointTo b).hom
      let π := (RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toRingHom.comp (ρ.prod σ)
      IsPullback (X.presheaf.germ V _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f))
        (f.app V)
        (CommRingCat.ofHom (RingHom.pi fun _ : Fin 2 => RingHom.id k))
        (CommRingCat.ofHom π) ∧ Function.Surjective π := by
  obtain ⟨V, hV, hVU, ha, hb, hsurj⟩ :=
    exists_isAffineOpen_pairEvaluation_surjective f a b h U hx
  refine ⟨V, hV, hVU, ha, hb, ?_, ?_⟩
  · exact isPullback_prod_to_piFinTwo _ _ _ _
      (isPullback_sections_of_isGlueingTwoPoints f a b h V ha hb)
  · intro z
    let e := RingEquiv.piFinTwo (fun _ : Fin 2 => k)
    obtain ⟨s, hs⟩ := hsurj (e z)
    refine ⟨s, ?_⟩
    change e.symm ((X'.presheaf.germ (f ⁻¹ᵁ V) _ ha ≫
      Scheme.stalkClosedPointTo a).hom.prod
        (X'.presheaf.germ (f ⁻¹ᵁ V) _ hb ≫
          Scheme.stalkClosedPointTo b).hom s) = z
    rw [hs, e.symm_apply_apply]

private theorem prime_eq_ker_or_ker_of_comap_eq
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    (f : A →+* k) (g : A →+* B) (ρ σ : B →+* k)
    (hρ : ρ.comp g = f)
    (hρsurj : Function.Surjective ρ) (hσsurj : Function.Surjective σ)
    (hrange : ∀ b, b ∈ Set.range g ↔ ρ b = σ b)
    (p : Ideal B) (hp : p.IsPrime) (hcomap : p.comap g = RingHom.ker f) :
    p = RingHom.ker ρ ∨ p = RingHom.ker σ := by
  have hle : RingHom.ker ρ ⊓ RingHom.ker σ ≤ p := by
    intro b hb
    have hbρ : ρ b = 0 := hb.1
    have hbσ : σ b = 0 := hb.2
    obtain ⟨a, rfl⟩ := (hrange b).mpr (hbρ.trans hbσ.symm)
    change a ∈ p.comap g
    rw [hcomap]
    change f a = 0
    rw [← hρ]
    exact hbρ
  rcases hp.mul_le.mp (Ideal.mul_le_inf.trans hle) with h | h
  · exact Or.inl ((RingHom.ker_isMaximal_of_surjective ρ hρsurj).eq_of_le hp.ne_top h).symm
  · exact Or.inr ((RingHom.ker_isMaximal_of_surjective σ hσsurj).eq_of_le hp.ne_top h).symm

private theorem isReduced_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsReduced X'] (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) : IsReduced X := by
  refine ⟨fun U => ?_⟩
  exact _root_.isReduced_of_injective (f.app U).hom
    (app_injective_of_isGlueingTwoPoints f a b h U)

private def affinePushoutSituation
    {k A B : Type u} [Field k] [CommRing A] [CommRing B] {n : ℕ}
    (f : A →+* k) (g : A →+* B) (π : B →+* (Fin n → k))
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (algebraMap k (Fin n → k))) (CommRingCat.ofHom π))
    (hπ : Function.Surjective π) :
    AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation.{u} where
  S := AlgebraicGeometry.Spec (.of A)
  X := AlgebraicGeometry.Spec (.of B)
  Y := AlgebraicGeometry.Spec (.of k)
  Z := AlgebraicGeometry.Spec (.of (Fin n → k))
  pX := AlgebraicGeometry.Spec.map (CommRingCat.ofHom g)
  pY := AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)
  pZ := AlgebraicGeometry.Spec.map (CommRingCat.ofHom π) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom g)
  i := AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)
  j := AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Fin n → k)))
  i_over := rfl
  j_over := by rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp, h.w]
  isClosedImmersion_i := IsClosedImmersion.spec_of_surjective _ hπ
  isIntegralHom_j := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  fiber_preimage_subset_affine := fun _ => ⟨⊤, isAffineOpen_top _, fun _ _ => trivial⟩

private theorem affinePushoutSituation_surjective
    {k A B : Type u} [Field k] [CommRing A] [CommRing B] {n : ℕ} (hn : 0 < n)
    (f : A →+* k) (g : A →+* B) (π : B →+* (Fin n → k))
    (h : IsPullback (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (algebraMap k (Fin n → k))) (CommRingCat.ofHom π))
    (hπ : Function.Surjective π) :
    Surjective (affinePushoutSituation f g π h hπ).j := by
  constructor
  intro y
  refine ⟨AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => k) ⟨0, hn⟩)) (closedPoint k), ?_⟩
  exact @Subsingleton.elim (PrimeSpectrum k) inferInstance _ _

private theorem exists_completedLocalRing_ringEquiv_of_isIso_stalkMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    let A := X.presheaf.stalk x
    let B := Y.presheaf.stalk (f x)
    let φ : A ≃+* B :=
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm
    ∃ e : AlgebraicGeometry.Scheme.completedLocalRing X x ≃+*
      AlgebraicGeometry.Scheme.completedLocalRing Y (f x),
      ∀ a : A, e (algebraMap A (AlgebraicGeometry.Scheme.completedLocalRing X x) a) =
        algebraMap B (AlgebraicGeometry.Scheme.completedLocalRing Y (f x)) (φ a) := by
  let A := X.presheaf.stalk x
  let B := Y.presheaf.stalk (f x)
  let φ : A ≃+* B :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm
  letI : Algebra A B := φ.toRingHom.toAlgebra
  let eL : A ≃ₗ[A] B :=
    { toFun := φ
      invFun := φ.symm
      left_inv := φ.symm_apply_apply
      right_inv := φ.apply_symm_apply
      map_add' := φ.map_add
      map_smul' := by
        intro a b
        change φ (a * b) = φ a * φ b
        exact φ.map_mul a b }
  letI : Module.Free A B :=
    Module.Free.of_equiv' (inferInstance : Module.Free A A) eL
  letI : Module.Flat A B := Module.Flat.of_free
  letI : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ φ.surjective
  have hmax :
      Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B := by
    change Ideal.map φ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B
    exact IsLocalRing.map_ringEquiv_maximalIdeal φ
  have hres : Function.Bijective ⇑(IsLocalRing.ResidueField.map (algebraMap A B)) := by
    change Function.Bijective (IsLocalRing.ResidueField.mapEquiv φ)
    exact (IsLocalRing.ResidueField.mapEquiv φ).bijective
  exact exists_adicCompletion_ringEquiv_of_flat
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing hmax hres

private noncomputable def completedLocalRing_ringEquiv_of_isIso_stalkMap
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] :
    AlgebraicGeometry.Scheme.completedLocalRing X x ≃+*
      AlgebraicGeometry.Scheme.completedLocalRing Y (f x) :=
  Classical.choose (exists_completedLocalRing_ringEquiv_of_isIso_stalkMap f x)

private theorem completedLocalRing_ringEquiv_of_isIso_stalkMap_commutes
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)]
    (a : X.presheaf.stalk x) :
    completedLocalRing_ringEquiv_of_isIso_stalkMap f x
      (algebraMap (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.completedLocalRing X x) a) =
      algebraMap (Y.presheaf.stalk (f x))
        (AlgebraicGeometry.Scheme.completedLocalRing Y (f x))
        ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm a) :=
  (Classical.choose_spec (exists_completedLocalRing_ringEquiv_of_isIso_stalkMap f x)) a

private theorem completedLocalRing_ringEquiv_of_isIso_stalkMap_commutes_base
    {K : Type u} [CommRing K]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)]
    (tX : K →+* X.presheaf.stalk x)
    (tY : K →+* Y.presheaf.stalk (f x))
    (h : (f.stalkMap x).hom.comp tY = tX) (a : K) :
    completedLocalRing_ringEquiv_of_isIso_stalkMap f x
      (algebraMap (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.completedLocalRing X x) (tX a)) =
    algebraMap (Y.presheaf.stalk (f x))
      (AlgebraicGeometry.Scheme.completedLocalRing Y (f x)) (tY a) := by
  rw [completedLocalRing_ringEquiv_of_isIso_stalkMap_commutes]
  have ht : (f.stalkMap x).hom (tY a) = tX a :=
    congrArg (fun g : K →+* X.presheaf.stalk x => g a) h
  have ht' : (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv (tY a) =
      tX a := by
    change (f.stalkMap x).hom (tY a) = tX a
    exact ht
  exact congrArg (algebraMap (Y.presheaf.stalk (f x))
    (AlgebraicGeometry.Scheme.completedLocalRing Y (f x)))
    (by simpa only [← ht'] using
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm_apply_apply (tY a))

private abbrev stalkScalarMap {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (.of k)) (x : X) : k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

private abbrev completionScalarMap {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (.of k)) (x : X) :
    k →+* AlgebraicGeometry.Scheme.completedLocalRing X x :=
  (algebraMap _ _).comp (stalkScalarMap p x)

private theorem stalkScalarMap_naturality {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ AlgebraicGeometry.Spec (.of k))
    (x : X) :
    (f.stalkMap x).hom.comp (stalkScalarMap p (f x)) =
      stalkScalarMap (f ≫ p) x := by
  ext a
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
    Y.presheaf.germ ⊤ (f x) (TopologicalSpace.Opens.mem_top _) ≫ f.stalkMap x).hom a = _
  rw [← Category.assoc, Scheme.Hom.germ_stalkMap]
  simp only [stalkScalarMap, Scheme.Hom.comp_appTop, Scheme.Hom.appTop,
    Scheme.Hom.preimage_top]
  congr 1

private theorem stalkScalarMap_naturality_of_eq {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ AlgebraicGeometry.Spec (.of k))
    (x : X) {y : Y} (h : f x = y) :
    (eqToHom (congrArg (fun z => Y.presheaf.stalk z) h.symm) ≫ f.stalkMap x).hom.comp
      (stalkScalarMap p y) = stalkScalarMap (f ≫ p) x := by
  subst y
  simpa using stalkScalarMap_naturality f p x

private theorem completedLocalRing_ringEquiv_scalar {k : Type u} [CommRing k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (p : Y ⟶ AlgebraicGeometry.Spec (.of k))
    (x : X) [IsIso (f.stalkMap x)] {y : Y} (h : f x = y) (c : k) :
    (h ▸ completedLocalRing_ringEquiv_of_isIso_stalkMap f x)
      (completionScalarMap (f ≫ p) x c) = completionScalarMap p y c := by
  subst y
  exact completedLocalRing_ringEquiv_of_isIso_stalkMap_commutes_base f x
    (stalkScalarMap (f ≫ p) x) (stalkScalarMap p (f x))
    (stalkScalarMap_naturality f p x) c

private noncomputable def completedLocalRing_ringEquiv_of_schemeIso
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (x : X) :
    AlgebraicGeometry.Scheme.completedLocalRing X x ≃+*
      AlgebraicGeometry.Scheme.completedLocalRing Y (e.hom x) :=
  completedLocalRing_ringEquiv_of_isIso_stalkMap e.hom x

private noncomputable def completedLocalRing_ringEquiv_of_affineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    AlgebraicGeometry.Scheme.completedLocalRing X (U.ι x) ≃+*
    AlgebraicGeometry.Scheme.completedLocalRing
        (AlgebraicGeometry.Spec (.of Γ(X, U))) (hU.isoSpec.hom x) := by
  letI : IsLocallyNoetherian U.toScheme := by infer_instance
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsIso (U.ι.stalkMap x) := by
    rw [← Scheme.Opens.stalkIso_inv]
    exact (U.stalkIso x).isIso_inv
  haveI : IsIso (hU.isoSpec.hom.stalkMap x) :=
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap hU.isoSpec.hom).mp inferInstance).2 x
  exact (completedLocalRing_ringEquiv_of_isIso_stalkMap U.ι x).symm.trans
    (completedLocalRing_ringEquiv_of_schemeIso hU.isoSpec x)

private theorem completedLocalRing_ringEquiv_of_affineOpen_scalar
    {k : Type u} [CommRing k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U)
    (p : X ⟶ AlgebraicGeometry.Spec (.of k))
    (q : AlgebraicGeometry.Spec (.of Γ(X, U)) ⟶ AlgebraicGeometry.Spec (.of k))
    (hq : hU.isoSpec.hom ≫ q = U.ι ≫ p) (x : U) (c : k) :
    completedLocalRing_ringEquiv_of_affineOpen U hU x
      (completionScalarMap p (U.ι x) c) =
        completionScalarMap q (hU.isoSpec.hom x) c := by
  letI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsIso (U.ι.stalkMap x) := by
    rw [← Scheme.Opens.stalkIso_inv]
    exact (U.stalkIso x).isIso_inv
  haveI : IsIso (hU.isoSpec.hom.stalkMap x) :=
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap hU.isoSpec.hom).mp inferInstance).2 x
  have hι := completedLocalRing_ringEquiv_scalar U.ι p x rfl c
  have hchart := completedLocalRing_ringEquiv_scalar hU.isoSpec.hom q x rfl c
  rw [hq] at hchart
  change completedLocalRing_ringEquiv_of_isIso_stalkMap hU.isoSpec.hom x
    ((completedLocalRing_ringEquiv_of_isIso_stalkMap U.ι x).symm
      (completionScalarMap p (U.ι x) c)) = _
  rw [← hι, RingEquiv.symm_apply_apply]
  exact hchart

private theorem affineOpen_isoSpec_hom_rationalPoint
    {k : Type u} [Field k] {X : Scheme.{u}}
    (r : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hr : r (IsLocalRing.closedPoint k) ∈ U) :
    hU.isoSpec.hom ⟨r (IsLocalRing.closedPoint k), hr⟩ =
      (AlgebraicGeometry.Spec.map
        (X.presheaf.germ U _ hr ≫ Scheme.stalkClosedPointTo r))
        (IsLocalRing.closedPoint k) := by
  haveI : IsLocalHom (Scheme.stalkClosedPointTo r).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' r
  have hpt : (AlgebraicGeometry.Spec.map (Scheme.stalkClosedPointTo r))
      (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (X.presheaf.stalk (r (IsLocalRing.closedPoint k))) :=
    IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo r).hom
  rw [hU.isoSpec_hom_apply]
  simp only [AlgebraicGeometry.Spec.map_comp, Scheme.Hom.comp_apply,
    AlgebraicGeometry.Spec.map_apply, IsLocalRing.comap_closedPoint]
  exact congrArg (AlgebraicGeometry.Spec.map (X.presheaf.germ U _ hr)) hpt.symm

private theorem primeIdealOf_rationalPoint_eq_ker
    {k : Type u} [Field k] {X : Scheme.{u}}
    (a : AlgebraicGeometry.Spec (.of k) ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (ha : a (closedPoint k) ∈ U) :
    (hU.primeIdealOf ⟨a (closedPoint k), ha⟩).asIdeal =
      RingHom.ker (X.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom := by
  change (hU.isoSpec.hom ⟨a (closedPoint k), ha⟩).asIdeal = _
  rw [affineOpen_isoSpec_hom_rationalPoint]
  change (maximalIdeal k).comap _ = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

private theorem eq_or_eq_of_isGlueingTwoPoints_of_image_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (y : X') (hy : f y = (a ≫ f) (closedPoint k)) :
    y = a (closedPoint k) ∨ y = b (closedPoint k) := by
  letI : IsFinite f := h.2.2.2.2.2.2.2.2.choose_spec.1
  obtain ⟨V, hV, _, ha, hb, hsurj⟩ :=
    exists_isAffineOpen_pairEvaluation_surjective f a b h ⊤ trivial
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage V hV
  have hyV : f y ∈ V := by rw [hy]; exact ha
  let ρ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ ha ≫ Scheme.stalkClosedPointTo a).hom
  let σ := (X'.presheaf.germ (f ⁻¹ᵁ V) _ hb ≫ Scheme.stalkClosedPointTo b).hom
  let q := (X.presheaf.germ V _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f)).hom
  have hcomap : (hW.primeIdealOf ⟨y, hyV⟩).asIdeal.comap (f.app V).hom = RingHom.ker q := by
    have hc := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hW le_rfl hyV
    rw [Scheme.Hom.appLE_eq_app] at hc
    change (PrimeSpectrum.comap (f.app V).hom (hW.primeIdealOf ⟨y, hyV⟩)).asIdeal = _
    exact (congrArg PrimeSpectrum.asIdeal hc).trans (by
      convert primeIdealOf_rationalPoint_eq_ker (a ≫ f) V hV ha using 1
      exact congrArg (fun z : V => (hV.primeIdealOf z).asIdeal) (Subtype.ext hy))
  have hp := prime_eq_ker_or_ker_of_comap_eq q (f.app V).hom ρ σ
    (by ext s; exact sectionAt_app f a V ha s)
    (fun c => by obtain ⟨s, hs⟩ := hsurj (c, 0); exact ⟨s, congrArg Prod.fst hs⟩)
    (fun c => by obtain ⟨s, hs⟩ := hsurj (0, c); exact ⟨s, congrArg Prod.snd hs⟩)
    (fun s => mem_range_app_iff_of_isGlueingTwoPoints f a b h V ha hb s)
    (hW.primeIdealOf ⟨y, hyV⟩).asIdeal inferInstance hcomap
  have he (r : AlgebraicGeometry.Spec (.of k) ⟶ X') (hr : r (closedPoint k) ∈ f ⁻¹ᵁ V)
      (he : (hW.primeIdealOf ⟨y, hyV⟩).asIdeal =
        RingHom.ker (X'.presheaf.germ (f ⁻¹ᵁ V) _ hr ≫ Scheme.stalkClosedPointTo r).hom) :
      y = r (closedPoint k) := by
    have he' : hW.primeIdealOf ⟨y, hyV⟩ = hW.primeIdealOf ⟨r (closedPoint k), hr⟩ :=
      PrimeSpectrum.ext (he.trans (primeIdealOf_rationalPoint_eq_ker r _ hW hr).symm)
    simpa only [hW.fromSpec_primeIdealOf] using congrArg hW.fromSpec he'
  exact hp.imp (he a ha) (he b hb)

private theorem specMap_evaluation_fromSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (r : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U) (hr : r (closedPoint k) ∈ U) :
    AlgebraicGeometry.Spec.map (X.presheaf.germ U _ hr ≫ Scheme.stalkClosedPointTo r) ≫
      hU.fromSpec = r := by
  rw [AlgebraicGeometry.Spec.map_comp, Category.assoc,
    ← IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk r

private theorem exists_completedLocalRing_ringEquiv_of_affineOpen_rationalPoint_scalar
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (r : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (U : X.Opens) (hU : IsAffineOpen U) (hr : r (closedPoint k) ∈ U)
    (p : X ⟶ AlgebraicGeometry.Spec (.of k)) :
    let z := AlgebraicGeometry.Spec.map
      (X.presheaf.germ U _ hr ≫ Scheme.stalkClosedPointTo r) (closedPoint k)
    ∃ e : AlgebraicGeometry.Scheme.completedLocalRing X (r (closedPoint k)) ≃+*
      AlgebraicGeometry.Scheme.completedLocalRing (AlgebraicGeometry.Spec (.of Γ(X, U))) z,
      ∀ c : k, e (completionScalarMap p (r (closedPoint k)) c) =
        completionScalarMap (hU.fromSpec ≫ p) z c := by
  dsimp only
  rw [← affineOpen_isoSpec_hom_rationalPoint r U hU hr]
  refine ⟨completedLocalRing_ringEquiv_of_affineOpen U hU ⟨r (closedPoint k), hr⟩, ?_⟩
  intro c
  exact completedLocalRing_ringEquiv_of_affineOpen_scalar U hU p (hU.fromSpec ≫ p)
    (by rw [← Category.assoc, hU.isoSpec_hom_fromSpec]) ⟨r (closedPoint k), hr⟩ c

end

private theorem surjective_of_isGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    Surjective f := by
  obtain ⟨_, _, _, _, _, _, _, _, hab, _, ⟨U, hU, hIso⟩, _⟩ := h
  have := hIso
  constructor
  intro y
  by_cases hy : y = (a ≫ f) (IsLocalRing.closedPoint k)
  · exact ⟨a (IsLocalRing.closedPoint k), hy.symm⟩
  · have hyU : y ∈ U := by
      rw [← SetLike.mem_coe, hU]
      exact hy
    obtain ⟨z, hz⟩ := Surjective.surj (f := f ∣_ U) ⟨y, hyU⟩
    refine ⟨z.1, ?_⟩
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hz

private theorem isIso_stalkMap_of_isGlueingTwoPoints_of_ne
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (y : X') (hy : f y ≠ (a ≫ f) (IsLocalRing.closedPoint k)) :
    IsIso (f.stalkMap y) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨U, hU, hIso⟩, _⟩ := h
  have hyU : f y ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact hy
  let z : f ⁻¹ᵁ U := ⟨y, hyU⟩
  letI : IsIso (f ∣_ U) := hIso
  have hz : IsIso ((f ∣_ U).stalkMap z) :=
    (isIso_iff_isIso_stalkMap (f ∣_ U)).mp hIso |>.2 z
  exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
    (morphismRestrictStalkMap f U z)).mp hz

private theorem isAffineOpen_preimage_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (U : X.Opens) (hU : IsAffineOpen U) : IsAffineOpen (f ⁻¹ᵁ U) := by
  letI : IsFinite f := h.2.2.2.2.2.2.2.2.choose_spec.1
  exact IsAffineHom.isAffine_preimage U hU

/-- A rational point `a` of a `k`-scheme recovers the scalar `c` from its image in the stalk. -/
private theorem stalkClosedPointTo_stalkScalarMap
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (.of k))]
    (a : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (haover : a ≫ (X ↘ AlgebraicGeometry.Spec (.of k)) = 𝟙 _) (c : k) :
    (Scheme.stalkClosedPointTo a).hom
      (stalkScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) (a (closedPoint k)) c) = c := by
  have hc := sectionAt_coefficient a haover ⊤ trivial c
  change AlgebraicGeometry.sectionAt a ⊤ trivial
    (X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op
      ((X ↘ AlgebraicGeometry.Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c))) = c at hc
  exact (AlgebraicGeometry.sectionAt_map a (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl))
    (show a (IsLocalRing.closedPoint k) ∈ (⊤ : X.Opens) from trivial)
    ((X ↘ AlgebraicGeometry.Spec (.of k)).appTop
      ((Scheme.ΓSpecIso (.of k)).inv c))).symm.trans hc

private theorem completedLocalRing_residueMap_comp_baseMap
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (a : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (haover : a ≫ (X ↘ AlgebraicGeometry.Spec (.of k)) = 𝟙 _)
    (ρ : AlgebraicGeometry.Scheme.completedLocalRing X (a (IsLocalRing.closedPoint k)) →+* k)
    (hρ : ρ.comp (algebraMap (X.presheaf.stalk (a (IsLocalRing.closedPoint k)))
      (AlgebraicGeometry.Scheme.completedLocalRing X (a (IsLocalRing.closedPoint k)))) =
        (Scheme.stalkClosedPointTo a).hom) :
    ρ.comp ((algebraMap (X.presheaf.stalk (a (IsLocalRing.closedPoint k)))
      (AlgebraicGeometry.Scheme.completedLocalRing X (a (IsLocalRing.closedPoint k)))).comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
          X.presheaf.germ ⊤ (a (IsLocalRing.closedPoint k)) trivial).hom) =
      RingHom.id k := by
  ext c
  change ρ ((algebraMap (X.presheaf.stalk (a (IsLocalRing.closedPoint k)))
    (AlgebraicGeometry.Scheme.completedLocalRing X (a (IsLocalRing.closedPoint k))))
      (stalkScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) _ c)) = c
  rw [← RingHom.comp_apply, hρ]
  exact stalkClosedPointTo_stalkScalarMap a haover c

private theorem exists_completedLocalRing_isPullback_over_field
    {k : Type u} [Field k]
    (s : AlgebraicGeometry.PushoutAlongClosedImmersionAndIntegralSituation.{u})
    {Q : Scheme.{u}} [IsLocallyNoetherian Q]
    (a : s.X ⟶ Q) (b : s.Y ⟶ Q) (hQ : IsPushout s.i s.j a b)
    (pQ : Q ⟶ AlgebraicGeometry.Spec (.of k)) [Surjective s.j] (n : ℕ)
    (eZ : s.Z ≅ AlgebraicGeometry.Spec (.of (Fin n → k)))
    (eY : s.Y ≅ AlgebraicGeometry.Spec (.of k))
    (hj : s.j = eZ.hom ≫ AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (RingHom.pi fun _ : Fin n ↦ RingHom.id k)) ≫ eY.inv)
    (hpoints : ∀ i : Fin n,
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => k) i)) ≫
          eZ.inv ≫ s.i) ≫ (a ≫ pQ) = 𝟙 _) :
    let point : Fin n → (AlgebraicGeometry.Spec (.of k) ⟶ s.Z) := fun i =>
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => k) i)) ≫ eZ.inv
    let x' : Fin n → s.X := fun i => s.i (point i (closedPoint k))
    let z : Q := b (eY.inv (closedPoint k))
    ∃ (ρ : ∀ i, AlgebraicGeometry.Scheme.completedLocalRing s.X (x' i) →+* k)
      (q : AlgebraicGeometry.Scheme.completedLocalRing Q z →+* k)
      (r : AlgebraicGeometry.Scheme.completedLocalRing Q z →+*
        (∀ i, AlgebraicGeometry.Scheme.completedLocalRing s.X (x' i))),
      IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r)
        (CommRingCat.ofHom (RingHom.pi fun _ : Fin n ↦ RingHom.id k))
        (CommRingCat.ofHom (RingHom.pi fun i => (ρ i).comp (Pi.evalRingHom _ i))) ∧
      (∀ i, (ρ i).comp (completionScalarMap (a ≫ pQ) (x' i)) = RingHom.id k) ∧
      ∀ c : k, r (completionScalarMap pQ z c) =
        fun i => completionScalarMap (a ≫ pQ) (x' i) c := by
  let e := (AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout
    s.X s.Y hQ
  letI : IsLocallyNoetherian (AlgebraicGeometry.pushoutScheme s) :=
    LocallyOfFiniteType.isLocallyNoetherian e.hom
  have ha : AlgebraicGeometry.pushoutInl s ≫ e.hom = a :=
    IsPushout.inl_isoIsPushout_hom s.X s.Y
      (AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral s).isPushout hQ
  have hb : AlgebraicGeometry.pushoutInr s ≫ e.hom = b :=
    IsPushout.inr_isoIsPushout_hom s.X s.Y
      (AlgebraicGeometry.pushoutAlongClosedImmersionAndIntegral s).isPushout hQ
  obtain ⟨hx, q, r, ρ, hq, _, hρ, hp⟩ :=
    AlgebraicGeometry.exists_pushoutCompletedLocalRing_isPullback s n k (fun _ => k) eZ eY hj
  let x := AlgebraicGeometry.pushoutInr s (eY.inv (closedPoint k))
  have hpoint : e.hom x = b (eY.inv (closedPoint k)) :=
    congrArg (fun f : s.Y ⟶ Q => f (eY.inv (closedPoint k))) hb
  let eC : AlgebraicGeometry.Scheme.completedLocalRing (AlgebraicGeometry.pushoutScheme s) x ≃+*
      AlgebraicGeometry.Scheme.completedLocalRing Q (b (eY.inv (closedPoint k))) :=
    hpoint ▸ completedLocalRing_ringEquiv_of_schemeIso e x
  have hscalar (c : k) :
      eC (completionScalarMap (e.hom ≫ pQ) x c) =
        completionScalarMap pQ (b (eY.inv (closedPoint k))) c :=
    completedLocalRing_ringEquiv_scalar e.hom pQ x hpoint c
  refine ⟨ρ, r.comp eC.symm.toRingHom, q.comp eC.symm.toRingHom, ?_, ?_, ?_⟩
  · apply hp.of_iso eC.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · ext t
      exact congrArg r (eC.symm_apply_apply t).symm
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro t
      change q t = q (eC.symm (eC t))
      exact congrArg q (eC.symm_apply_apply t).symm
    · rfl
    · rfl
  · intro i
    letI : s.X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨a ≫ pQ⟩
    exact completedLocalRing_residueMap_comp_baseMap _ (hpoints i) (ρ i) (hρ i)
  · intro c
    change q (eC.symm (completionScalarMap pQ _ c)) = _
    rw [← hscalar c, eC.symm_apply_apply]
    funext i
    have hi := congrArg
      (fun φ => φ (stalkScalarMap (e.hom ≫ pQ) x c)) (hq i)
    change q (completionScalarMap (e.hom ≫ pQ) x c) i = _ at hi
    have ht := congrArg (fun φ => φ c)
      (stalkScalarMap_naturality_of_eq (AlgebraicGeometry.pushoutInl s) (e.hom ≫ pQ) _ (hx i))
    refine hi.trans ?_
    let xi : s.X := s.i ((AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin n => k) i)) ≫ eZ.inv) (closedPoint k))
    exact congrArg (algebraMap (s.X.presheaf.stalk xi)
      (AlgebraicGeometry.Scheme.completedLocalRing s.X xi)) (by
        simpa only [RingHom.comp_apply, Scheme.Hom.comp_apply,
          ← Category.assoc, ha, xi, x] using ht)

private theorem exists_completedLocalRing_pairPullback_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian X]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    let p := IsLocalRing.closedPoint k
    let A := AlgebraicGeometry.Scheme.completedLocalRing X ((a ≫ f) p)
    let R₀ := AlgebraicGeometry.Scheme.completedLocalRing X' (a p)
    let R₁ := AlgebraicGeometry.Scheme.completedLocalRing X' (b p)
    ∃ (ρ₀ : R₀ →+* k) (ρ₁ : R₁ →+* k)
      (q : A →+* k) (r : A →+* R₀ × R₁),
      IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r)
        (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
        (CommRingCat.ofHom (ρ₀.prodMap ρ₁)) ∧
      ρ₀.comp (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (a p)) = RingHom.id k ∧
      ρ₁.comp (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (b p)) = RingHom.id k ∧
      ∀ c : k, r (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) ((a ≫ f) p) c) =
        (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (a p) c,
          completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (b p) c) := by
  let p := IsLocalRing.closedPoint k
  obtain ⟨V, hV, _, ha, hb, hpb, hπ⟩ :=
    exists_isAffineOpen_piPullback_of_isGlueingTwoPoints f a b h ⊤ (by trivial)
  let W := f ⁻¹ᵁ V
  have hW : IsAffineOpen W := isAffineOpen_preimage_of_isGlueingTwoPoints f a b h V hV
  let A := Γ(X, V)
  let B := Γ(X', W)
  letI : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let ρ := (X'.presheaf.germ W _ ha ≫ Scheme.stalkClosedPointTo a).hom
  let σ := (X'.presheaf.germ W _ hb ≫ Scheme.stalkClosedPointTo b).hom
  let π := (RingEquiv.piFinTwo (fun _ : Fin 2 => k)).symm.toRingHom.comp (ρ.prod σ)
  let s := affinePushoutSituation
    (X.presheaf.germ V _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f)).hom
    (f.app V).hom π hpb hπ
  letI : Surjective s.j := affinePushoutSituation_surjective (by decide : 0 < 2) _ _ _ hpb hπ
  let pA := hV.fromSpec ≫ (X ↘ AlgebraicGeometry.Spec (.of k))
  let pB := hW.fromSpec ≫ (X' ↘ AlgebraicGeometry.Spec (.of k))
  have hbase : AlgebraicGeometry.Spec.map (f.app V) ≫ pA = pB := by
    have ht := IsAffineOpen.SpecMap_appLE_fromSpec f hV hW le_rfl
    have ht' : AlgebraicGeometry.Spec.map (f.app V) ≫ hV.fromSpec = hW.fromSpec ≫ f := by
      simpa only [Scheme.Hom.app_eq_appLE] using ht
    dsimp only [pA, pB]
    rw [← Category.assoc, ht', Category.assoc, h.2.2.2.1.comp_over]
  obtain ⟨q₀, q, r, hp, hρscalar, hrscalar⟩ :=
    exists_completedLocalRing_isPullback_over_field s
      (AlgebraicGeometry.Spec.map (f.app V))
      (AlgebraicGeometry.Spec.map
        (X.presheaf.germ V _ ha ≫ Scheme.stalkClosedPointTo (a ≫ f)))
      (Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _ hpb hπ)
      pA 2 (Iso.refl _) (Iso.refl _) (by simp [s, affinePushoutSituation]) (by
        intro i
        change (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) i)) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) ≫
              (AlgebraicGeometry.Spec.map (f.app V) ≫ pA) = 𝟙 _
        rw [hbase]
        fin_cases i
        · rw [specMap_piFinTwo_eval_zero]
          dsimp only [pB]
          have hpa : AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ) ≫ hW.fromSpec = a :=
            specMap_evaluation_fromSpec a W hW ha
          rw [← Category.assoc, hpa]
          exact h.1.comp_over
        · rw [specMap_piFinTwo_eval_one]
          dsimp only [pB]
          have hpb' : AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ) ≫ hW.fromSpec = b :=
            specMap_evaluation_fromSpec b W hW hb
          rw [← Category.assoc, hpb']
          exact h.2.1.comp_over)
  change ∀ i, (q₀ i).comp (completionScalarMap
    (AlgebraicGeometry.Spec.map (f.app V) ≫ pA) _) = RingHom.id k at hρscalar
  rw [hbase] at hρscalar
  change ∀ c : k, r (completionScalarMap pA _ c) =
    fun i => completionScalarMap (AlgebraicGeometry.Spec.map (f.app V) ≫ pA) _ c at hrscalar
  rw [hbase] at hrscalar
  obtain ⟨eX, heX⟩ := exists_completedLocalRing_ringEquiv_of_affineOpen_rationalPoint_scalar
    (a ≫ f) V hV ha (X ↘ AlgebraicGeometry.Spec (.of k))
  have hpoint₀ :
      ((AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 0)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) p) =
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ)) p :=
    congrArg (fun g : AlgebraicGeometry.Spec (.of k) ⟶
      AlgebraicGeometry.Spec (.of B) => g p) (specMap_piFinTwo_eval_zero ρ σ)
  have hpoint₁ :
      ((AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 1)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) p) =
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom σ)) p :=
    congrArg (fun g : AlgebraicGeometry.Spec (.of k) ⟶
      AlgebraicGeometry.Spec (.of B) => g p) (specMap_piFinTwo_eval_one ρ σ)
  obtain ⟨e₀, he₀⟩ :
      ∃ e : AlgebraicGeometry.Scheme.completedLocalRing X' (a p) ≃+*
        AlgebraicGeometry.Scheme.completedLocalRing (AlgebraicGeometry.Spec (.of B))
          ((AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 0)) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) p),
        ∀ c : k, e (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (a p) c) =
          completionScalarMap pB _ c := by
    rw [hpoint₀]
    exact exists_completedLocalRing_ringEquiv_of_affineOpen_rationalPoint_scalar
      a W hW ha (X' ↘ AlgebraicGeometry.Spec (.of k))
  obtain ⟨e₁, he₁⟩ :
      ∃ e : AlgebraicGeometry.Scheme.completedLocalRing X' (b p) ≃+*
        AlgebraicGeometry.Scheme.completedLocalRing (AlgebraicGeometry.Spec (.of B))
          ((AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) 1)) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) p),
        ∀ c : k, e (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (b p) c) =
          completionScalarMap pB _ c := by
    rw [hpoint₁]
    exact exists_completedLocalRing_ringEquiv_of_affineOpen_rationalPoint_scalar
      b W hW hb (X' ↘ AlgebraicGeometry.Spec (.of k))
  let R : Fin 2 → Type u := fun i => AlgebraicGeometry.Scheme.completedLocalRing
    (AlgebraicGeometry.Spec (.of B))
    ((AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 => k) i)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom π)) p)
  let eB := e₀.prodCongr e₁
  let hp' := isPullback_piFinTwo R q r q₀ hp
  let hp'' := isPullback_congr_ringEquiv q
    ((RingEquiv.piFinTwo R).toRingHom.comp r)
    ((RingHom.id k).prod (RingHom.id k))
    ((q₀ 0).prodMap (q₀ 1)) eX eB hp'
  refine ⟨(q₀ 0).comp e₀.toRingHom, (q₀ 1).comp e₁.toRingHom,
    q.comp eX.toRingHom,
    eB.symm.toRingHom.comp ((RingEquiv.piFinTwo R).toRingHom.comp
      (r.comp eX.toRingHom)), ?_, ?_, ?_, ?_⟩
  · convert hp'' using 1 <;> ext x <;> rfl
  · ext c
    change q₀ 0 (e₀ (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (a p) c)) = c
    rw [he₀]
    exact congrArg (fun φ => φ c) (hρscalar 0)
  · ext c
    change q₀ 1 (e₁ (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (b p) c)) = c
    rw [he₁]
    exact congrArg (fun φ => φ c) (hρscalar 1)
  · intro c
    change (e₀.symm (r (eX (completionScalarMap
        (X ↘ AlgebraicGeometry.Spec (.of k)) ((a ≫ f) p) c)) 0),
      e₁.symm (r (eX (completionScalarMap
        (X ↘ AlgebraicGeometry.Spec (.of k)) ((a ≫ f) p) c)) 1)) = _
    rw [heX]
    refine (congrArg (fun z => (e₀.symm (z 0), e₁.symm (z 1))) (hrscalar c)).trans ?_
    apply Prod.ext
    · exact (congrArg e₀.symm (he₀ c).symm).trans (e₀.symm_apply_apply _)
    · exact (congrArg e₁.symm (he₁ c).symm).trans (e₁.symm_apply_apply _)

private theorem algHom_to_coefficientField_eq {k R : Type*} [Field k] [CommRing R]
    [Algebra k R] [IsLocalRing R] (f g : R →ₐ[k] k) : f = g := by
  have hf : Function.Surjective f := fun a => ⟨algebraMap k R a, by simp⟩
  have hg : Function.Surjective g := fun a => ⟨algebraMap k R a, by simp⟩
  have hker : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom := by
    exact (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f.toRingHom hf)).trans
      (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g.toRingHom hg)).symm
  ext r
  have hz : r - algebraMap k R (f r) ∈ RingHom.ker g.toRingHom := by
    rw [← hker]
    change f (r - algebraMap k R (f r)) = 0
    simp
  have hz' : g r - f r = 0 := by simpa using hz
  exact (sub_eq_zero.mp hz').symm

private theorem multicrossResidue_comp_eq_of_scalar
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
    {n : ℕ} (i : Fin n) (e : R ≃+* Stacks.Curves.multicross k n)
    (he : e.toRingHom.comp (algebraMap k R) =
      (RingHom.pi fun _ : Fin n ↦ PowerSeries.C).codRestrict
        (Stacks.Curves.multicross k n) (by
          intro a
          rw [Stacks.Curves.mem_multicross]
          simp))
    (ρ : R →+* k) (hρ : ρ.comp (algebraMap k R) = RingHom.id k) :
    (multicrossResidue i).comp e.toRingHom = ρ := by
  let φ : R →ₐ[k] k :=
    { toRingHom := (multicrossResidue i).comp e.toRingHom
      commutes' := by
        intro a
        have h := congrArg (fun f : k →+* Stacks.Curves.multicross k n =>
          multicrossResidue i (f a)) he
        simpa [multicrossResidue, RingHom.comp_apply] using h }
  let ψ : R →ₐ[k] k :=
    { toRingHom := ρ
      commutes' := by
        intro a
        exact congrArg (fun f : k →+* k => f a) hρ }
  exact congrArg AlgHom.toRingHom (algHom_to_coefficientField_eq φ ψ)

private theorem nonempty_algEquiv_of_pairPullback_of_bijective
    {k A R S : Type u} [Field k] [CommRing A] [CommRing R] [CommRing S]
    [Algebra k A] [Algebra k R] [Algebra k S]
    (q : A →+* k) (r : A →+* R × S) (ρ : R →+* k) (σ : S →+* k)
    (hp : IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prodMap σ)))
    (hρ : ρ.comp (algebraMap k R) = RingHom.id k)
    (hr : ∀ c : k, r (algebraMap k A c) = (algebraMap k R c, algebraMap k S c))
    (hbij : Function.Bijective ρ) : Nonempty (A ≃ₐ[k] S) := by
  let e := (RingEquiv.ofBijective ρ hbij).prodCongr (RingEquiv.refl S)
  have hp' : IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom (e.toRingHom.comp r))
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((RingHom.id k).prodMap σ)) := by
    apply hp.of_iso (Iso.refl _) (Iso.refl _) e.toCommRingCatIso (Iso.refl _)
    · rfl
    · rfl
    · rfl
    · rfl
  apply nonempty_algEquiv_right_of_isPullback_left_id q (e.toRingHom.comp r) σ hp'
  intro c
  change (ρ (r (algebraMap k A c)).1, (r (algebraMap k A c)).2) = _
  rw [hr]
  exact Prod.ext (congrArg (fun φ => φ c) hρ) rfl

private theorem nonempty_algEquiv_multicross_of_pairPullback
    {k A R S : Type u} [Field k] [CommRing A] [CommRing R] [CommRing S]
    [Algebra k A] [Algebra k R] [Algebra k S] [IsLocalRing R] [IsLocalRing S]
    (q : A →+* k) (r : A →+* R × S) (ρ : R →+* k) (σ : S →+* k)
    (hp : IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prodMap σ)))
    (hρ : ρ.comp (algebraMap k R) = RingHom.id k)
    (hσ : σ.comp (algebraMap k S) = RingHom.id k)
    (hr : ∀ c : k, r (algebraMap k A c) = (algebraMap k R c, algebraMap k S c))
    {m n : ℕ} (i : Fin m) (j : Fin n)
    (e₀ : R ≃+* Stacks.Curves.multicross k m) (e₁ : S ≃+* Stacks.Curves.multicross k n)
    (he₀ : e₀.toRingHom.comp (algebraMap k R) =
      (RingHom.pi fun _ : Fin m ↦ PowerSeries.C).codRestrict
        (Stacks.Curves.multicross k m) (by intro a; simp [Stacks.Curves.mem_multicross]))
    (he₁ : e₁.toRingHom.comp (algebraMap k S) =
      (RingHom.pi fun _ : Fin n ↦ PowerSeries.C).codRestrict
        (Stacks.Curves.multicross k n) (by intro a; simp [Stacks.Curves.mem_multicross])) :
    letI : Algebra k (Stacks.Curves.multicross k (m + n)) :=
      Stacks.Curves.multicrossAlgebra k (m + n)
    Nonempty (A ≃ₐ[k] Stacks.Curves.multicross k (m + n)) := by
  let e := e₀.prodCongr e₁
  have hρ' := multicrossResidue_comp_eq_of_scalar i e₀ he₀ ρ hρ
  have hσ' := multicrossResidue_comp_eq_of_scalar j e₁ he₁ σ hσ
  have hp' : IsPullback (CommRingCat.ofHom q)
      (CommRingCat.ofHom (e.toRingHom.comp r))
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom ((multicrossResidue i).prodMap (multicrossResidue j))) := by
    apply hp.of_iso (Iso.refl _) (Iso.refl _) e.toCommRingCatIso (Iso.refl _)
    · rfl
    · rfl
    · rfl
    · ext z
      · exact congrArg (fun φ => φ z.1) hρ'.symm
      · exact congrArg (fun φ => φ z.2) hσ'.symm
  apply nonempty_algEquiv_multicross_of_isPullback i j q (e.toRingHom.comp r) hp'
  intro c
  change (e₀ (r (algebraMap k A c)).1, e₁ (r (algebraMap k A c)).2) = _
  rw [hr]
  exact Prod.ext (congrArg (fun φ => φ c) he₀) (congrArg (fun φ => φ c) he₁)

private def IsMulticrossOrField (k A : Type u) [Field k] [CommRing A] [Algebra k A] : Prop :=
  Nonempty (A ≃ₐ[k] k) ∨ ∃ n : ℕ, 0 < n ∧
    letI : Algebra k (Stacks.Curves.multicross k n) := Stacks.Curves.multicrossAlgebra k n
    Nonempty (A ≃ₐ[k] Stacks.Curves.multicross k n)

private theorem IsMulticrossOrField.of_algEquiv
    {k A B : Type u} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (h : IsMulticrossOrField k B) : IsMulticrossOrField k A := by
  rcases h with h | ⟨n, hn, h⟩
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · letI : Algebra k (Stacks.Curves.multicross k n) := Stacks.Curves.multicrossAlgebra k n
    obtain ⟨f⟩ := h
    exact Or.inr ⟨n, hn, ⟨e.trans f⟩⟩

private theorem residue_bijective_of_algEquiv_field
    {k R : Type u} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
    (ρ : R →+* k) (hρ : ρ.comp (algebraMap k R) = RingHom.id k)
    (e : R ≃ₐ[k] k) : Function.Bijective ρ := by
  let φ : R →ₐ[k] k :=
    { toRingHom := ρ
      commutes' := fun c => congrArg (fun f => f c) hρ }
  have he := congrArg AlgHom.toRingHom (algHom_to_coefficientField_eq φ e.toAlgHom)
  change ρ = e.toRingHom at he
  rw [he]
  exact e.bijective

private theorem isMulticrossOrField_of_pairPullback
    {k A R S : Type u} [Field k] [CommRing A] [CommRing R] [CommRing S]
    [Algebra k A] [Algebra k R] [Algebra k S] [IsLocalRing R] [IsLocalRing S]
    (q : A →+* k) (r : A →+* R × S) (ρ : R →+* k) (σ : S →+* k)
    (hp : IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r)
      (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
      (CommRingCat.ofHom (ρ.prodMap σ)))
    (hρ : ρ.comp (algebraMap k R) = RingHom.id k)
    (hσ : σ.comp (algebraMap k S) = RingHom.id k)
    (hr : ∀ c : k, r (algebraMap k A c) = (algebraMap k R c, algebraMap k S c))
    (hR : IsMulticrossOrField k R) (hS : IsMulticrossOrField k S) :
    IsMulticrossOrField k A := by
  rcases hR with hR | ⟨m, hm, hR⟩
  · obtain ⟨eR⟩ := hR
    obtain ⟨e⟩ := nonempty_algEquiv_of_pairPullback_of_bijective q r ρ σ hp hρ hr
      (residue_bijective_of_algEquiv_field ρ hρ eR)
    exact hS.of_algEquiv e
  letI : Algebra k (Stacks.Curves.multicross k m) := Stacks.Curves.multicrossAlgebra k m
  obtain ⟨eR⟩ := hR
  rcases hS with hS | ⟨n, hn, hS⟩
  · obtain ⟨eS⟩ := hS
    let r' := (RingEquiv.prodComm : R × S ≃+* S × R).toRingHom.comp r
    have hp' : IsPullback (CommRingCat.ofHom q) (CommRingCat.ofHom r')
        (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))
        (CommRingCat.ofHom (σ.prodMap ρ)) := by
      apply hp.of_iso (Iso.refl _) (Iso.refl _)
        (RingEquiv.prodComm : R × S ≃+* S × R).toCommRingCatIso
        (RingEquiv.prodComm : k × k ≃+* k × k).toCommRingCatIso
      · rfl
      · rfl
      · rfl
      · rfl
    have hr' (c : k) : r' (algebraMap k A c) = (algebraMap k S c, algebraMap k R c) :=
      congrArg Prod.swap (hr c)
    obtain ⟨e⟩ := nonempty_algEquiv_of_pairPullback_of_bijective q r' σ ρ hp' hσ hr'
      (residue_bijective_of_algEquiv_field σ hσ eS)
    exact (show IsMulticrossOrField k R from Or.inr ⟨m, hm, ⟨eR⟩⟩).of_algEquiv e
  · letI : Algebra k (Stacks.Curves.multicross k n) := Stacks.Curves.multicrossAlgebra k n
    obtain ⟨eS⟩ := hS
    refine Or.inr ⟨m + n, by omega, ?_⟩
    exact nonempty_algEquiv_multicross_of_pairPullback q r ρ σ hp hρ hσ hr
      ⟨0, hm⟩ ⟨0, hn⟩ eR.toRingEquiv eS.toRingEquiv
      (by apply RingHom.ext; intro c; exact eR.commutes c)
      (by apply RingHom.ext; intro c; exact eS.commutes c)

private def HasMulticrossOrFieldCompletion (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))] (x : X) : Prop :=
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X x) :=
    (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) x).toAlgebra
  IsMulticrossOrField k (AlgebraicGeometry.Scheme.completedLocalRing X x)

private theorem isSeminormalRing_completedLocalRing_of_hasMulticrossOrFieldCompletion
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (.of k))] {x : X}
    (h : HasMulticrossOrFieldCompletion k X x) :
    IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X x) := by
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X x) :=
    (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) x).toAlgebra
  rcases h with h | ⟨n, _, h⟩
  · obtain ⟨e⟩ := h
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv e.toRingEquiv.symm
      (isSeminormalRing_of_isIntegrallyClosed k)
  · letI : Algebra k (Stacks.Curves.multicross k n) := Stacks.Curves.multicrossAlgebra k n
    obtain ⟨e⟩ := h
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv e.toRingEquiv.symm
      (isSeminormalRing_multicross k n)

private theorem isSeminormalRing_completedLocalRing_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian X]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (hX : ∀ x : X, IsClosed ({x} : Set X) →
      IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X x))
    (y : X') (hy : IsClosed ({y} : Set X')) :
    IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X' y) := by
  letI : IsFinite f := h.2.2.2.2.2.2.2.2.choose_spec.1
  have hfy : IsClosed ({f y} : Set X) := by simpa using f.isClosedMap _ hy
  by_cases heq : f y = (a ≫ f) (closedPoint k)
  · have hc := hX (f y) hfy
    rw [heq] at hc
    letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X' (a (closedPoint k))) :=
      (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) _).toAlgebra
    letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X' (b (closedPoint k))) :=
      (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) _).toAlgebra
    obtain ⟨ρ, σ, q, r, hp, hρ, hσ, _⟩ :=
      exists_completedLocalRing_pairPullback_of_isGlueingTwoPoints f a b h
    have hfac := isSeminormalRing_factors_of_eqLocus ρ σ hρ hσ
      (Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
        (ringEquivEqLocusOfIsPullback q r ρ σ hp) hc)
    rcases eq_or_eq_of_isGlueingTwoPoints_of_image_eq f a b h y heq with rfl | rfl
    · exact hfac.1
    · exact hfac.2
  · letI : IsIso (f.stalkMap y) :=
      isIso_stalkMap_of_isGlueingTwoPoints_of_ne f a b h y heq
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
      (completedLocalRing_ringEquiv_of_isIso_stalkMap f y).symm (hX (f y) hfy)

private theorem hasMulticrossOrFieldCompletion_of_isIso_stalkMap
    {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian X]
    (f : X' ⟶ X) (hf : f.IsOver (AlgebraicGeometry.Spec (.of k)))
    (y : X') [IsIso (f.stalkMap y)] (h : HasMulticrossOrFieldCompletion k X' y) :
    HasMulticrossOrFieldCompletion k X (f y) := by
  let R := AlgebraicGeometry.Scheme.completedLocalRing X' y
  let S := AlgebraicGeometry.Scheme.completedLocalRing X (f y)
  letI : Algebra k R := (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) y).toAlgebra
  letI : Algebra k S := (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) (f y)).toAlgebra
  let e : R ≃ₐ[k] S :=
    { completedLocalRing_ringEquiv_of_isIso_stalkMap f y with
      commutes' := by
        intro c
        have hc := completedLocalRing_ringEquiv_scalar f
          (X ↘ AlgebraicGeometry.Spec (.of k)) y rfl c
        rw [hf.comp_over] at hc
        exact hc }
  exact IsMulticrossOrField.of_algEquiv e.symm h

private theorem hasMulticrossOrFieldCompletion_of_isGlueingTwoPoints
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian X]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (ha : HasMulticrossOrFieldCompletion k X' (a (closedPoint k)))
    (hb : HasMulticrossOrFieldCompletion k X' (b (closedPoint k))) :
    HasMulticrossOrFieldCompletion k X ((a ≫ f) (closedPoint k)) := by
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X ((a ≫ f) (closedPoint k))) :=
    (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) ((a ≫ f) (closedPoint k))).toAlgebra
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X' (a (closedPoint k))) :=
    (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (a (closedPoint k))).toAlgebra
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X' (b (closedPoint k))) :=
    (completionScalarMap (X' ↘ AlgebraicGeometry.Spec (.of k)) (b (closedPoint k))).toAlgebra
  obtain ⟨ρ, σ, q, r, hp, hρ, hσ, hr⟩ :=
    exists_completedLocalRing_pairPullback_of_isGlueingTwoPoints f a b h
  exact isMulticrossOrField_of_pairPullback q r ρ σ hp hρ hσ hr ha hb

private theorem exists_adicCompletion_ringEquiv_multicross_one
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [IsRegularLocalRing A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 1)
    (hres : Nonempty (ResidueField A ≃ₐ[k] k)) :
    ∃ e : AdicCompletion (maximalIdeal A) A ≃+* Stacks.Curves.multicross k 1,
      e.toRingHom.comp (algebraMap k (AdicCompletion (maximalIdeal A) A)) =
        (RingHom.pi fun _ : Fin 1 ↦ PowerSeries.C).codRestrict
          (Stacks.Curves.multicross k 1) (by
            intro a
            rw [Stacks.Curves.mem_multicross]
            simp) := by
  have hDVR : ∃ _ : IsDomain A, IsDiscreteValuationRing A :=
    ((isDiscreteValuationRing_tfae A).out 3 1).mp
      (show IsRegularLocalRing A ∧ ringKrullDim A = 1 from ⟨inferInstance, hdim⟩)
  have hzero : Ring.deltaInvariant A = 0 :=
    (Ring.deltaInvariant_eq_zero_iff_isDiscreteValuationRing hNagata hdim).mpr hDVR
  have hbound := Ring.deltaInvariant_ge_numberOfBranches_sub_one k A hNagata hdim hres
  rw [hzero] at hbound
  have heq : Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1 := by
    rw [hzero]
    exact (le_zero_iff.mp hbound).symm
  obtain ⟨n, hn, e, he⟩ :=
    Ring.adicCompletion_algEquiv_multicross_of_deltaInvariant_eq
      k A hNagata hdim hres heq
  have hnle : n ≤ 1 := by
    rw [hn] at hbound
    norm_cast at hbound
    omega
  have hn0 : n ≠ 0 := by
    intro hz
    subst n
    have : Subsingleton (Stacks.Curves.multicross k 0) := inferInstance
    exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))
  have hn1 : n = 1 := by omega
  subst n
  exact ⟨e, he⟩

private theorem hasMulticrossCompletion_one_of_regular
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X] [IsReduced X] (hNagata : IsNagataScheme X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    Stacks.Curves.HasMulticrossCompletion k X x 1 := by
  let A := X.presheaf.stalk x
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  letI : Algebra k A :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x trivial).hom).toAlgebra
  letI : Algebra k (ResidueField A) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation x).hom).toAlgebra
  letI : IsRegularLocalRing A := hreg
  letI : IsSepClosed k := inferInstance
  have hres : Nonempty (ResidueField A ≃ₐ[k] k) :=
    stalk_residueField_algEquiv f x hx
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_multicross_one
    k A (Stacks.AlgebraicGeometry.NormalizationQuotient.stalk_isNagataRing X hNagata x)
      hdim hres
  let Ahat := AdicCompletion (maximalIdeal A) A
  letI : Algebra A Ahat := inferInstance
  letI : Algebra k Ahat :=
    ((algebraMap A Ahat).comp (algebraMap k A)).toAlgebra
  letI : IsScalarTower k A Ahat := inferInstance
  letI : Algebra k (Stacks.Curves.multicross k 1) :=
    Stacks.Curves.multicrossAlgebra k 1
  let eAlg : Ahat ≃ₐ[k] Stacks.Curves.multicross k 1 :=
    { e with
      commutes' := by
        intro c
        have hc := congrArg
          (fun φ : k →+* Stacks.Curves.multicross k 1 => φ c) he
        change e (algebraMap k Ahat c) =
          ((RingHom.pi fun _ : Fin 1 ↦ PowerSeries.C).codRestrict
            (Stacks.Curves.multicross k 1) (by
              intro b
              rw [Stacks.Curves.mem_multicross]
              simp)) c
        exact hc }
  exact (Stacks.Curves.hasMulticrossCompletion_iff k X x 1).2 ⟨eAlg⟩

private theorem exists_completedLocalRing_ringEquiv_base_of_fieldStalk
    (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (a : AlgebraicGeometry.Spec (.of k) ⟶ X)
    (haover : a ≫ (X ↘ AlgebraicGeometry.Spec (.of k)) = 𝟙 _)
    (hfield : IsField (X.presheaf.stalk (a (IsLocalRing.closedPoint k)))) :
    ∃ e : AlgebraicGeometry.Scheme.completedLocalRing X (a (closedPoint k)) ≃+* k,
      ∀ c : k, e (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k))
        (a (closedPoint k)) c) = c := by
  let A := X.presheaf.stalk (a (closedPoint k))
  let C := AlgebraicGeometry.Scheme.completedLocalRing X (a (closedPoint k))
  letI : Field A := IsField.toField hfield
  have hmax : maximalIdeal A = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
  letI : IsAdicComplete (maximalIdeal A) A := by
    rw [hmax]
    exact IsAdicComplete.bot A
  let eC : C ≃ₐ[A] A := (AdicCompletion.ofAlgEquiv (maximalIdeal A)).symm
  let ρ : A →+* k := (Scheme.stalkClosedPointTo a).hom
  have hρ (c : k) : ρ (stalkScalarMap (X ↘ AlgebraicGeometry.Spec (.of k))
      (a (closedPoint k)) c) = c := stalkClosedPointTo_stalkScalarMap a haover c
  have hρsurj : Function.Surjective ρ := fun c => ⟨_, hρ c⟩
  refine ⟨eC.toRingEquiv.trans (RingEquiv.ofBijective ρ
    ⟨RingHom.injective ρ, hρsurj⟩), ?_⟩
  intro c
  change ρ (eC (algebraMap A C (stalkScalarMap
    (X ↘ AlgebraicGeometry.Spec (.of k)) (a (closedPoint k)) c))) = c
  rw [eC.commutes]
  exact hρ c

private theorem ringKrullDim_eq_zero_or_one
    (A : Type*) [CommRing A] [Nontrivial A] (h : ringKrullDim A ≤ 1) :
    ringKrullDim A = 0 ∨ ringKrullDim A = 1 := by
  rcases hd : ringKrullDim A with _ | d
  · have hz := ringKrullDim_nonneg_of_nontrivial (R := A)
    rw [hd] at hz
    exact (not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) hz).elim
  rcases d with _ | n
  · rw [hd] at h
    change ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) at h
    exact (not_le_of_gt (show (1 : ℕ∞) < ⊤ by simp) (WithBot.coe_le_coe.mp h)).elim
  · have hn : n ≤ 1 := by
      rw [hd] at h
      change ((n : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) at h
      exact WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h)
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem hasMulticrossOrFieldCompletion_of_regular
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X] [IsReduced X]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    HasMulticrossOrFieldCompletion k X x := by
  rcases ringKrullDim_eq_zero_or_one (X.presheaf.stalk x) hdim with hzero | hone
  · let p := X ↘ AlgebraicGeometry.Spec (.of k)
    let a := pointOfClosedPoint p x hx
    have hax : a (closedPoint k) = x := pointOfClosedPoint_apply p x hx _
    have hf : IsField (X.presheaf.stalk (a (closedPoint k))) := by
      rw [hax]
      exact isField_of_reduced_dim_zero _ hzero
    obtain ⟨e, he⟩ := exists_completedLocalRing_ringEquiv_base_of_fieldStalk k a
      (pointOfClosedPoint_comp p x hx) hf
    letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X (a (closedPoint k))) :=
      (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) (a (closedPoint k))).toAlgebra
    have hcompletion : HasMulticrossOrFieldCompletion k X (a (closedPoint k)) :=
      Or.inl ⟨AlgEquiv.ofRingEquiv (f := e) he⟩
    rwa [hax] at hcompletion
  · have hNagata := AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field k
      (X ↘ AlgebraicGeometry.Spec (.of k))
    exact Or.inr ⟨1, by decide, hasMulticrossCompletion_one_of_regular k X hNagata x hx hreg hone⟩

private theorem isRegularLocalRing_of_multicrossCompletion_one
    (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (.of k))]
    [IsLocallyNoetherian X] (x : X) (h : Stacks.Curves.HasMulticrossCompletion k X x 1) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X x) :=
    (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) x).toAlgebra
  letI : Algebra k (Stacks.Curves.multicross k 1) := Stacks.Curves.multicrossAlgebra k 1
  obtain ⟨e⟩ := h
  apply isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr
  exact IsRegularLocalRing.of_ringEquiv
    (e.toRingEquiv.trans (Stacks.Curves.multicrossOneRingEquiv k)).symm

private theorem isMulticrossSingularity_of_hasMulticrossOrFieldCompletion
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X))
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (h : HasMulticrossOrFieldCompletion k X x) : Stacks.Curves.IsMulticrossSingularity k X x := by
  letI : Algebra k (AlgebraicGeometry.Scheme.completedLocalRing X x) :=
    (completionScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) x).toAlgebra
  rcases h with h | ⟨n, hn, he⟩
  · obtain ⟨e⟩ := h
    exact (hsing (isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr
      (IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm))).elim
  · have hn2 : 2 ≤ n := by
      by_contra hn2
      have : n = 1 := by omega
      subst n
      exact hsing (isRegularLocalRing_of_multicrossCompletion_one k x he)
    exact ⟨hx, n, hn2, he⟩

private theorem isReduced_of_isRegular {X : Scheme.{u}} (hX : AlgebraicGeometry.IsRegular X) :
    IsReduced X := by
  let := AlgebraicGeometry.isNormal_of_isRegular X hX
  exact isReduced_of_isReduced_stalk X

private theorem isRegularLocalRing_stalk_of_isRegular
    {X : Scheme.{u}} (h : AlgebraicGeometry.IsRegular X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hx, hU⟩ := h x
  letI : IsRegularRing Γ(X, U.1) := hU
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let p := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : IsLocalization p.primeCompl (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularRing.isRegularLocalRing_of_isLocalization p (X.presheaf.stalk x)

section

open CategoryTheory.Limits Opposite
open scoped TensorProduct

private theorem stalkClosedPointTo_scalar
    {k R : Type u} [CommRing k] [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (p : X ⟶ AlgebraicGeometry.Spec (.of k))
    (a : AlgebraicGeometry.Spec (.of R) ⟶ X) (φ : k →+* R)
    (ha : a ≫ p = AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) :
    (Scheme.stalkClosedPointTo a).hom.comp (stalkScalarMap p (a (closedPoint R))) = φ := by
  have hgerm : X.presheaf.germ ⊤ (a (closedPoint R))
        (TopologicalSpace.Opens.mem_top _) ≫ Scheme.stalkClosedPointTo a =
      a.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
    rw [AlgebraicGeometry.germ_stalkClosedPointTo_appLE a ⊤
      (TopologicalSpace.Opens.mem_top _)]
    congr 1
  have he : p.appTop ≫ X.presheaf.germ ⊤ (a (closedPoint R))
        (TopologicalSpace.Opens.mem_top _) ≫ Scheme.stalkClosedPointTo a =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom φ := by
    rw [hgerm, ← Category.assoc, ← Scheme.Hom.comp_appTop, ha]
    exact Scheme.ΓSpecIso_naturality _
  apply RingHom.ext
  intro c
  have he' := congrArg (fun f : Γ(AlgebraicGeometry.Spec (.of k), ⊤) ⟶ CommRingCat.of R =>
    f.hom ((Scheme.ΓSpecIso (.of k)).inv c)) he
  simpa [stalkScalarMap, CommRingCat.hom_comp, RingHom.comp_apply] using he'

attribute [local instance] Classical.propDecidable

/-- The forgetful functor from sheaves of abelian groups to presheaves preserves
monomorphisms: it creates limits, so it preserves pullbacks.  This is stated as a top-level
instance because synthesising it inside the proof of
`Stacks.Curves.exists_coefficient_sequence_of_isSquishingTangentVector`, whose local context
carries the whole short exact sequence, exhausts the typeclass heartbeat budget. -/
private instance preservesMonomorphisms_sheafForget (T : TopCat.{u}) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} T).PreservesMonomorphisms :=
  inferInstance

/-- Applying the identification of two objects of `AddCommGrpCat` to an element transported
along it returns that element.  This is the one place the skyscraper's sections have to be
compared with its fibre across the equality of objects that defines them. -/
private theorem eqToIso_hom_cast {W A : AddCommGrpCat.{u}} (e : W = A) (y : A) :
    (eqToIso e).hom
        (cast (congrArg (fun C : AddCommGrpCat.{u} => (C : Type u)) e.symm) y) = y := by
  cases e
  rfl

private theorem skyscraperObj_eq {T : TopCat.{u}} (x : T)
    (A : AddCommGrpCat.{u}) (U : Opens T) (hx : x ∈ U) :
    (skyscraperPresheaf x A).obj (op U) = A := by
  classical
  exact ite_eq_left hx

private noncomputable def skyscraperSectionIso {T : TopCat.{u}} (x : T)
    (A : AddCommGrpCat.{u}) (U : Opens T) (hx : x ∈ U) :
    (skyscraperPresheaf x A).obj (op U) ≅ A :=
  eqToIso (skyscraperObj_eq x A U hx)

private lemma skyscraperSectionIso_restrict {T : TopCat.{u}} (x : T)
    (A : AddCommGrpCat.{u}) {U V : Opens T} (i : V ⟶ U) (hx : x ∈ V) :
    (skyscraperPresheaf x A).map i.op ≫ (skyscraperSectionIso x A V hx).hom =
      (skyscraperSectionIso x A U (i.le hx)).hom := by
  classical
  have h1 : (skyscraperPresheaf x A).map i.op =
      eqToHom ((skyscraperObj_eq x A U (i.le hx)).trans
        (skyscraperObj_eq x A V hx).symm) := by
    simp [skyscraperPresheaf, hx, i.le hx]
  rw [h1]
  simp only [skyscraperSectionIso, eqToIso.hom, eqToHom_trans]


private lemma sheaf_exact_sections {T : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T))
    (hS : S.Exact) [Mono S.f] (U : Opens T) :
    ∀ b, S.g.hom.app (op U) b = 0 → ∃ a, S.f.hom.app (op U) a = b := by
  let S' : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := S
  have hS' : S'.Exact := hS
  have : Mono S'.f := inferInstanceAs (Mono S.f)
  let E := sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⋙
    (evaluation (Opens T)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  exact (ShortComplex.ab_exact_iff _).mp
    (hS'.map_of_mono_of_preservesKernel E inferInstance inferInstance)

private theorem isReduced_stalk_of_isReduced_sections {T : TopCat.{u}}
    (F : T.Presheaf CommRingCat.{u}) (hF : ∀ U, IsReduced (F.obj (op U))) (x : T) :
    IsReduced (F.stalk x) := by
  constructor
  intro s hs
  obtain ⟨U, hx, t, rfl⟩ := F.exists_germ_eq s
  obtain ⟨n, hn⟩ := hs
  obtain ⟨V, hxV, i, j, hij⟩ := F.germ_eq x hx hx (t ^ n) 0 (by simpa using hn)
  haveI : IsReduced (F.obj (op V)) := hF V
  have ht : F.map i.op t = 0 := eq_zero_of_pow_eq_zero (by simpa using hij)
  rw [← F.germ_res_apply i x hxV, ht, map_zero]

private theorem finite_of_dualNumber_coefficient_sequence
    {A B k : Type u} [CommRing A] [CommRing B] [Field k]
    (i : A →+* B) (q : B →+* DualNumber k) (r : A →+* k)
    (hconst : q.comp i = (algebraMap k (DualNumber k)).comp r)
    (hr : Function.Surjective r)
    (hd : Function.Surjective (fun b => (q b).snd))
    (hker : ∀ b, (q b).snd = 0 → ∃ a, i a = b) :
    (∃ e : B, q e = TrivSqZeroExt.inr (1 : k)) ∧
      @Module.Finite A B _ _ i.toAlgebra.toModule := by
  classical
  obtain ⟨e₀, he₀⟩ := hd 1
  obtain ⟨a₀, ha₀⟩ := hr (q e₀).fst
  have hcf (c : k) : (algebraMap k (DualNumber k) c).fst = c := rfl
  have hcs (c : k) : (algebraMap k (DualNumber k) c).snd = 0 := rfl
  have hc (a : A) : q (i a) = algebraMap k (DualNumber k) (r a) :=
    congrArg (fun f => f a) hconst
  let e := e₀ - i a₀
  have he : q e = TrivSqZeroExt.inr (1 : k) := by
    apply TrivSqZeroExt.ext <;> simp [e, map_sub, hc, ha₀, he₀, hcf, hcs]
  refine ⟨⟨e, he⟩, ?_⟩
  letI : Algebra A B := i.toAlgebra
  apply Module.Finite.of_fg_top
  refine ⟨{1, e}, top_unique ?_⟩
  intro b _
  obtain ⟨c, hc'⟩ := hr (q b).snd
  have hd' : (q (b - i c * e)).snd = 0 := by
    simp [map_sub, map_mul, hc, he, hc', hcf, hcs]
  obtain ⟨a, ha⟩ := hker (b - i c * e) hd'
  have hb : b = a • (1 : B) + c • e := by
    change b = i a * 1 + i c * e
    rw [ha]
    ring
  rw [hb]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem exists_completion_residueMap {A k : Type*} [CommRing A] [IsLocalRing A]
    [Field k] (r : A →+* k) [IsLocalHom r] :
    ∃ ρ : AdicCompletion (maximalIdeal A) A →+* k,
      ρ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = r := by
  have hm : maximalIdeal A ≤ RingHom.ker r := by
    intro a ha
    by_contra hr
    exact (mem_maximalIdeal a).mp ha (isUnit_of_map_unit r a (isUnit_iff_ne_zero.mpr hr))
  let r' : (A ⧸ maximalIdeal A) →+* k := Ideal.Quotient.lift _ r hm
  refine ⟨r'.comp (AdicCompletion.evalOneₐ _).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  exact Ideal.Quotient.lift_comp_mk _ _ _

private theorem not_dualNumber_coefficient_sequence_of_seminormalCompletion
    {A B k : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsReduced B] [Field k]
    (i : A →+* B) (q : B →+* DualNumber k) (r : A →+* k) [IsLocalHom r]
    (hA : IsNagataRing A)
    (hS : IsSeminormalRing (AdicCompletion (maximalIdeal A) A))
    (hinj : Function.Injective i)
    (hconst : q.comp i = (algebraMap k (DualNumber k)).comp r)
    (hr : Function.Surjective r)
    (hd : Function.Surjective (fun b => (q b).snd))
    (hker : ∀ b, (q b).snd = 0 → ∃ a, i a = b) : False := by
  letI : IsNoetherianRing A := hA.1
  obtain ⟨⟨e, he⟩, hfinite⟩ := finite_of_dualNumber_coefficient_sequence i q r hconst hr hd hker
  letI : Algebra A B := i.toAlgebra
  letI : Module.Finite A B := hfinite
  have hAll : ∀ (S : Type u) [CommRing S] [Algebra A S] [Algebra.FiniteType A S],
      IsNagataRing S := ((isNagataRing_tfae (R := A)).out 1 2).mp hA
  have hB : IsNagataRing B := hAll B
  let S := AdicCompletion (maximalIdeal A) A
  letI : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := A)).mp ha
  letI : IsReduced (S ⊗[A] B) :=
    isReduced_tensor_adicCompletion_of_isNagataRing hB (maximalIdeal A) A
  have he₂ : e ^ 2 ∈ i.range := hker _ (by rw [map_pow, he]; simp)
  have he₃ : e ^ 3 ∈ i.range := hker _ (by rw [map_pow, he]; simp [pow_succ])
  have hcomm : (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom.comp i =
      (algebraMap S (S ⊗[A] B)).comp (algebraMap A S) := by
    ext a
    change (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B))
      (algebraMap A B a) = _
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply A S (S ⊗[A] B) a
  obtain ⟨z, hz⟩ := map_mem_range_of_sq_cube_mem_range i (algebraMap A S)
    (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom
    (algebraMap S (S ⊗[A] B)) hcomm hinj hS e he₂ he₃
  obtain ⟨ρ, hρ⟩ := exists_completion_residueMap r
  letI : Algebra A (DualNumber k) := ((algebraMap k (DualNumber k)).comp r).toAlgebra
  let fS : S →ₐ[A] DualNumber k :=
    { toRingHom := (algebraMap k (DualNumber k)).comp ρ
      commutes' := fun a => congrArg (algebraMap k (DualNumber k))
        (congrArg (fun φ => φ a) hρ) }
  let fB : B →ₐ[A] DualNumber k :=
    { toRingHom := q
      commutes' := fun a => congrArg (fun φ => φ a) hconst }
  let F := Algebra.TensorProduct.lift fS fB (fun _ _ => Commute.all _ _)
  have hh := congrArg F hz
  have hFz : F (algebraMap S (S ⊗[A] B) z) = algebraMap k (DualNumber k) (ρ z) := by
    change F (z ⊗ₜ[A] (1 : B)) = _
    simp [F, fS]
  have hFe : F ((Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom e) =
      TrivSqZeroExt.inr (1 : k) := by
    change F ((1 : S) ⊗ₜ[A] e) = _
    simpa [F, fB] using he
  rw [hFz, hFe] at hh
  exact zero_ne_one (congrArg TrivSqZeroExt.snd hh)

private theorem app_injective_of_isSquishingTangentVector
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (θ : AlgebraicGeometry.Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    (U : X.Opens) : Function.Injective (f.app U) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, ψ, hzero, hshort, _⟩
  let φ := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ RingCat AddCommGrpCat)).map (Scheme.Hom.toRingCatSheafHom f)
  haveI hm : Mono φ := hshort.mono_f
  haveI hm' : Mono φ.hom :=
    @Functor.map_mono _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat X) inferInstance _ _ φ hm
  exact (AddCommGrpCat.mono_iff_injective (φ.hom.app (op U))).mp inferInstance

private theorem exists_coefficient_sequence_of_isSquishingTangentVector
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))] [IsReduced X']
    (f : X' ⟶ X) (θ : AlgebraicGeometry.Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    let z := (θ ≫ f) (closedPoint (DualNumber k))
    let A := X.presheaf.stalk z
    ∃ (B : Type u) (_ : CommRing B) (_ : IsReduced B)
      (i : A →+* B) (q : B →+* DualNumber k) (r : A →+* k),
      IsLocalHom r ∧ Function.Injective i ∧
      q.comp i = (algebraMap k (DualNumber k)).comp r ∧
      Function.Surjective r ∧ Function.Surjective (fun b => (q b).snd) ∧
      ∀ b, (q b).snd = 0 → ∃ a, i a = b := by
  classical
  intro z A
  have hinj := app_injective_of_isSquishingTangentVector f θ h
  rcases h with ⟨hfOver, hltX', hqcX', hltX, hqcX, hclosed, hθOver,
    x, hxOver, hcontract, hfinite, ⟨U0, hUeq, hIso⟩, ψ0, hzero0, hshort, hcoeff⟩
  let Y : RingedSpace.{u, u} :=
    { carrier := X
      presheaf := f.base _* X'.presheaf
      IsSheaf := ((TopCat.Sheaf.pushforward CommRingCat f.base).obj
        X'.toRingedSpace.sheaf).property }
  let B := Y.presheaf.stalk z
  let i : A →+* B := ((TopCat.Presheaf.stalkFunctor CommRingCat z).map f.c).hom
  let q : B →+* DualNumber k :=
    (X'.presheaf.stalkPushforward CommRingCat f.base
      (θ (closedPoint (DualNumber k))) ≫ Scheme.stalkClosedPointTo θ).hom
  let r : A →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom.comp
    (Scheme.stalkClosedPointTo (θ ≫ f)).hom
  have hqi (a : A) : q (i a) = (Scheme.stalkClosedPointTo (θ ≫ f)).hom a := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have hqg (U : X.Opens) (hz : z ∈ U) (s : Γ(X', f ⁻¹ᵁ U)) :
      q (Y.presheaf.germ U z hz s) =
        (X'.presheaf.germ (f ⁻¹ᵁ U) _ hz ≫ Scheme.stalkClosedPointTo θ).hom s := by
    change (((f.base _* X'.presheaf).germ U (f.base (θ (closedPoint (DualNumber k)))) hz ≫
      X'.presheaf.stalkPushforward CommRingCat f.base (θ (closedPoint (DualNumber k))) ≫
        Scheme.stalkClosedPointTo θ).hom s) = _
    rw [← Category.assoc,
      TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base X'.presheaf U
        (θ (closedPoint (DualNumber k))) hz]
    rfl
  have hig (U : X.Opens) (hz : z ∈ U) (s : Γ(X, U)) :
      i (X.presheaf.germ U z hz s) = Y.presheaf.germ U z hz ((f.app U).hom s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U z hz f.c s
  have hcoef (U : X.Opens) (hz : z ∈ U) (s : Γ(X', f ⁻¹ᵁ U)) :
      (skyscraperSectionIso z (.of k) U hz).hom (ψ0.hom.app (op U) s) =
        AlgebraicGeometry.epsilonCoefficientAt θ (f ⁻¹ᵁ U) hz s := by
    rw [hcoeff U hz s]
    exact eqToIso_hom_cast (skyscraperObj_eq z (AddCommGrpCat.of k) U hz) _
  let φ0 := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ RingCat AddCommGrpCat)).map (Scheme.Hom.toRingCatSheafHom f)
  let S0 := ShortComplex.mk φ0 ψ0 hzero0
  haveI hm0 : Mono φ0 := hshort.mono_f
  haveI hmS0 : Mono S0.f := hm0
  have hker (U : X.Opens) (b : Γ(X', f ⁻¹ᵁ U))
      (hb : ψ0.hom.app (op U) b = 0) : ∃ a, (f.app U).hom a = b :=
    @sheaf_exact_sections _ S0 hshort.exact hmS0 U b hb
  have hdsnd (a : A) : (q (i a)).snd = 0 := by
    obtain ⟨U, hzU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [hig, hqg]
    have hz0 : ψ0.hom.app (op U) ((f.app U).hom s) = 0 :=
      congrArg (fun a => a.hom.app (op U) s) hzero0
    have hh := congrArg (fun a => (skyscraperSectionIso z (.of k) U hzU).hom a) hz0
    exact ((hcoef U hzU ((f.app U).hom s)).symm.trans hh).trans (map_zero _)
  have hconst : q.comp i = (algebraMap k (DualNumber k)).comp r := by
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · change (q (i a)).fst = r a
      exact congrArg TrivSqZeroExt.fst (hqi a)
    · exact hdsnd a
  have hr : Function.Surjective r := by
    have hc := stalkClosedPointTo_scalar (X ↘ AlgebraicGeometry.Spec (.of k)) (θ ≫ f)
      (algebraMap k (DualNumber k)) (by
        rw [Category.assoc, hfOver.comp_over]
        exact hθOver)
    intro c
    refine ⟨stalkScalarMap (X ↘ AlgebraicGeometry.Spec (.of k)) z c, ?_⟩
    exact congrArg TrivSqZeroExt.fst (congrArg (fun φ => φ c) hc)
  have hrLocal : IsLocalHom r := by
    constructor
    intro a ha
    have hu : IsUnit (q (i a)) := by
      have hc := congrArg (fun φ => φ a) hconst
      change q (i a) = algebraMap k (DualNumber k) (r a) at hc
      rw [hc]
      exact ha.map (algebraMap k (DualNumber k))
    rw [hqi] at hu
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (θ ≫ f)).hom a hu
  have hred : IsReduced B :=
    isReduced_stalk_of_isReduced_sections Y.presheaf
      (fun U => inferInstanceAs (IsReduced Γ(X', f ⁻¹ᵁ U))) z
  have hi0 (a : A) (ha : i a = 0) : a = 0 := by
    obtain ⟨U, hzU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [hig] at ha
    obtain ⟨V, hzV, v, w, hv⟩ :=
      Y.presheaf.germ_eq z hzU hzU ((f.app U).hom s) 0 (by simpa using ha)
    have hs : X.presheaf.map v.op s = 0 := by
      apply (hinj V)
      have hn := congrArg (fun φ => φ s) (f.naturality v.op)
      change X'.presheaf.map ((Opens.map f.base).map v).op ((f.app U).hom s) =
        X'.presheaf.map ((Opens.map f.base).map w).op (0 : Γ(X', f ⁻¹ᵁ U)) at hv
      exact hn.trans (by simpa using hv)
    rw [← X.presheaf.germ_res_apply v z hzV, hs, map_zero]
  refine ⟨B, inferInstance, hred, i, q, r, hrLocal, ?_, hconst, hr, ?_, ?_⟩
  · intro a b hab
    exact sub_eq_zero.mp (hi0 (a - b) (by simp [hab]))
  · have hlocal : TopCat.Presheaf.IsLocallySurjective ψ0.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi ψ0).mpr hshort.epi_g
    intro c
    obtain ⟨V, hV, ⟨s, hs⟩, hzV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff ψ0.hom).mp hlocal ⊤
        ((skyscraperSectionIso z (.of k) ⊤ trivial).inv c) z trivial
    refine ⟨Y.presheaf.germ V z hzV s, ?_⟩
    change (q (Y.presheaf.germ V z hzV s)).snd = c
    refine (congrArg TrivSqZeroExt.snd (hqg V hzV s)).trans ?_
    change AlgebraicGeometry.epsilonCoefficientAt θ (f ⁻¹ᵁ V) hzV s = c
    refine (hcoef V hzV s).symm.trans ?_
    rw [hs]
    change ((skyscraperPresheaf z (AddCommGrpCat.of k)).map (homOfLE hV).op ≫
      (skyscraperSectionIso z (.of k) V hzV).hom)
        ((skyscraperSectionIso z (.of k) ⊤ trivial).inv c) = c
    rw [skyscraperSectionIso_restrict]
    exact (skyscraperSectionIso z (AddCommGrpCat.of k) ⊤ trivial).inv_hom_id_apply c
  · intro b hb
    obtain ⟨U, hzU, s, rfl⟩ := Y.presheaf.exists_germ_eq b
    have hh : ψ0.hom.app (op U) s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (skyscraperSectionIso z (.of k) U hzU).hom).1
      exact (hcoef U hzU s).trans ((((congrArg TrivSqZeroExt.snd
        (hqg U hzU s)).symm.trans hb).trans (map_zero _).symm))
    obtain ⟨a, ha⟩ := hker U s hh
    exact ⟨X.presheaf.germ U z hzU a, by rw [hig, ha]⟩

private theorem not_isSquishingTangentVector_of_seminormal_completions
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))] [IsReduced X']
    (f : X' ⟶ X) (θ : AlgebraicGeometry.Spec (.of (DualNumber k)) ⟶ X')
    (hX : ∀ x : X, IsClosed ({x} : Set X) →
      IsSeminormalRing (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))) :
    ¬ AlgebraicGeometry.IsSquishingTangentVector f θ := by
  intro h
  obtain ⟨B, hB, hred, i, q, r, hrLocal, hinj, hconst, hr, hd, hker⟩ :=
    exists_coefficient_sequence_of_isSquishingTangentVector f θ h
  letI : CommRing B := hB
  letI : _root_.IsReduced B := hred
  letI : IsLocalHom r := hrLocal
  rcases h with ⟨hfOver, hltX', hqcX', hltX, hqcX, hclosed, hθOver,
    x, hxOver, hcontract, _⟩
  letI : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) := hltX
  let z := (θ ≫ f) (closedPoint (DualNumber k))
  have hz : z = x (closedPoint k) := by
    dsimp only [z]
    rw [hcontract]
    change x ((AlgebraicGeometry.dualNumberToBase k) (closedPoint (DualNumber k))) = _
    congr 1
    exact Subsingleton.elim _ _
  have hzclosed : IsClosed ({z} : Set X) := by
    rw [hz]
    exact (pointEquivClosedPoint (X ↘ AlgebraicGeometry.Spec (.of k))
      ⟨x, hxOver.comp_over⟩).property
  have hNag := Stacks.AlgebraicGeometry.NormalizationQuotient.stalk_isNagataRing X
    (AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field k
      (X ↘ AlgebraicGeometry.Spec (.of k))) z
  exact not_dualNumber_coefficient_sequence_of_seminormalCompletion i q r hNag
    (hX z hzclosed) hinj hconst hr hd hker

end

private theorem isGlueingTwoPoints_comp_iso
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X Y : Scheme.{u}} [X'.Over (AlgebraicGeometry.Spec (.of k))]
    [X.Over (AlgebraicGeometry.Spec (.of k))] [Y.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of k))]
    [QuasiCompact (Y ↘ AlgebraicGeometry.Spec (.of k))]
    (f : X' ⟶ X) (a b : AlgebraicGeometry.Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (e : X ≅ Y) (he : e.hom.IsOver (AlgebraicGeometry.Spec (.of k))) :
    AlgebraicGeometry.IsGlueingTwoPoints (f ≫ e.hom) a b := by
  letI : IsFinite f := h.2.2.2.2.2.2.2.2.choose_spec.1
  have hinj (U : Y.Opens) : Function.Injective ((f ≫ e.hom).app U) := by
    rw [Scheme.Hom.comp_app]
    exact (app_injective_of_isGlueingTwoPoints f a b h _).comp
      (ConcreteCategory.bijective_of_isIso (e.hom.app U)).1
  have pre (U : X.Opens) : e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U) = U := by
    rw [← Scheme.Hom.comp_preimage, e.hom_inv_id, Scheme.Hom.id_preimage]
  have hh : a ≫ (f ≫ e.hom) = b ≫ (f ≫ e.hom) := by
    rw [← Category.assoc, ← Category.assoc, h.2.2.2.2.2.2.2.2.choose]
  letI : f.IsOver (AlgebraicGeometry.Spec (.of k)) := h.2.2.2.1
  letI : e.hom.IsOver (AlgebraicGeometry.Spec (.of k)) := he
  refine ⟨h.1, h.2.1, h.2.2.1, inferInstance,
    h.2.2.2.2.1, h.2.2.2.2.2.1, inferInstance, inferInstance, hh,
    inferInstance, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hres⟩ := h.2.2.2.2.2.2.2.2.choose_spec.2.1
    refine ⟨e.inv ⁻¹ᵁ U, ?_, ?_⟩
    · ext y
      change e.inv y ∈ (U : Set X) ↔ _
      rw [hU]
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hinv (w : X) : e.inv (e.hom w) = w := by
        change (e.hom ≫ e.inv) w = w
        rw [e.hom_inv_id]
        rfl
      have hfwd (w : Y) : e.hom (e.inv w) = w := by
        change (e.inv ≫ e.hom) w = w
        rw [e.inv_hom_id]
        rfl
      have hcomp (w : AlgebraicGeometry.Spec (.of k)) :
          (a ≫ (f ≫ e.hom)) w = e.hom ((a ≫ f) w) := by
        simp only [Scheme.Hom.comp_apply]
      have heq : e.inv y = (a ≫ f) (closedPoint k) ↔
          y = (a ≫ (f ≫ e.hom)) (closedPoint k) := by
        constructor
        · intro hy
          exact ((hfwd y).symm.trans (congrArg (fun w : X => e.hom w) hy)).trans
            (hcomp (closedPoint k)).symm
        · intro hy
          exact (congrArg (fun w : Y => e.inv w) hy).trans
            ((congrArg (fun w : Y => e.inv w) (hcomp (closedPoint k))).trans (hinv _))
      exact not_congr heq
    · rw [morphismRestrict_comp]
      letI : IsIso (f ∣_ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U)) := by rw [pre]; exact hres
      exact (asIso (f ∣_ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ U)) ≪≫
        asIso (e.hom ∣_ (e.inv ⁻¹ᵁ U))).isIso_hom
  · intro U hx s hs
    obtain ⟨V, hVU, hxV, hsV⟩ := hs
    refine ⟨V, hVU, hxV, ?_⟩
    apply hinj V
    rw [map_zero]
    change ((f ≫ e.hom).app V).hom
      (Y.presheaf.map (homOfLE hVU).op s) = 0
    rw [← CommRingCat.comp_apply, (f ≫ e.hom).naturality]
    exact hsV
  · intro U hx s hs
    have ha : (a ≫ f) (closedPoint k) ∈ e.hom ⁻¹ᵁ U := hx
    have hb : (b ≫ f) (closedPoint k) ∈ e.hom ⁻¹ᵁ U := by
      rw [← h.2.2.2.2.2.2.2.2.choose]; exact ha
    obtain ⟨t, ht⟩ := (mem_range_app_iff_of_isGlueingTwoPoints f a b h
      (e.hom ⁻¹ᵁ U) ha hb s).mpr (sub_eq_zero.mp hs)
    obtain ⟨t', rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app U)).2 t
    refine ⟨U, le_rfl, hx, t', ?_⟩
    have hmap : ∀ h : (f ≫ e.hom) ⁻¹ᵁ U ⟶ (f ≫ e.hom) ⁻¹ᵁ U,
        X'.presheaf.map h.op = 𝟙 _ := by
      intro h
      rw [Subsingleton.elim h (𝟙 ((f ≫ e.hom) ⁻¹ᵁ U))]
      simp
    rw [hmap]
    exact ht.symm
  · intro c
    obtain ⟨U, hx, s, hs⟩ := h.2.2.2.2.2.2.2.2.choose_spec.2.2.2.2 c
    generalize hV : e.inv ⁻¹ᵁ U = V
    have hp : e.hom ⁻¹ᵁ V = U := by rw [← hV, pre]
    subst U
    exact ⟨V, hx, s, hs⟩

private theorem normalizationScheme_isRegular
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hNagata : IsNagataScheme X)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim X ≤ 1) :
    AlgebraicGeometry.IsRegular (AlgebraicGeometry.Scheme.normalizationScheme X hfin) := by
  letI : IsFinite (AlgebraicGeometry.Scheme.normalization X hfin) :=
    AlgebraicGeometry.Scheme.isFinite_normalization hNagata hfin
  letI : IsLocallyNoetherian (AlgebraicGeometry.Scheme.normalizationScheme X hfin) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.Scheme.normalization X hfin)
  letI : AlgebraicGeometry.IsNormal (AlgebraicGeometry.Scheme.normalizationScheme X hfin) := by
    obtain ⟨ι, Z, hZ, _, ⟨e⟩⟩ :=
      AlgebraicGeometry.Scheme.exists_iso_sigma_isIntegral_isNormal_normalizationScheme X hfin
    let C := (sigmaOpenCover Z).pushforwardIso e.inv
    apply (AlgebraicGeometry.isNormal_iff_stalk_normal _).mpr
    intro x
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    subst x
    let φ := (asIso ((C.f i).stalkMap y)).commRingCatIsoToRingEquiv
    letI : IsDomain ((C.X i).presheaf.stalk y) := (hZ i).stalk_isDomain y
    letI : IsIntegrallyClosed ((C.X i).presheaf.stalk y) := (hZ i).stalk_normal y
    letI := Function.Injective.isDomain φ φ.injective
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv φ.symm⟩
  exact AlgebraicGeometry.isRegular_of_isNormal_of_topologicalKrullDim_le_one _
    ((AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom
      (AlgebraicGeometry.Scheme.normalization X hfin)).trans hdim)

private theorem exists_affineOpen_with_single_singularPoint
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] [IsReduced X]
    (hX : topologicalKrullDim X = 1) (x : X)
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hxU : x ∈ U),
      topologicalKrullDim U.toScheme = 1 ∧
      AlgebraicGeometry.singularLocus U.toScheme ⊆ {⟨x, hxU⟩} := by
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  have hNagata := AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field k
    (X ↘ AlgebraicGeometry.Spec (.of k))
  obtain ⟨V, hxV, hV⟩ := exists_open_meets_singularLocus_only_at
    (k := k) hNagata hX x hsing
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  let U : X.Opens := U
  refine ⟨U, hU, hxU, ?_, ?_⟩
  · apply le_antisymm
    · exact (topologicalKrullDim_subspace_le X U).trans hX.le
    · have hdim := ringKrullDim_stalk_eq_one_of_singular k hX x hsing
      let y : U.toScheme := ⟨x, hxU⟩
      have he := ringKrullDim_eq_of_ringEquiv
        (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
      have hy : ringKrullDim (U.toScheme.presheaf.stalk y) = 1 := he.symm.trans hdim
      exact hy ▸ AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim y
  · intro y hy
    apply Subtype.ext
    apply hV y.1 (hUV y.2)
    intro hreg
    apply hy
    letI : IsRegularLocalRing (X.presheaf.stalk (U.ι y)) := hreg
    exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv


/-! ### Clause (3): towers of glueings of two points -/

/-- **A tower of `n` glueings of two rational points below `X`.** `IsGlueingTower k 0 X` says
that `X` is nonsingular, and `IsGlueingTower k (n + 1) X` says that `X` is obtained by glueing
two rational points of a scheme which itself carries a tower of `n` glueings. Unfolded, it is
the sequence `X_n ⟶ X_{n-1} ⟶ … ⟶ X_0 = X` of clause (3) of [Stacks, Tag 0C1X]: each step is a
glueing of two points as in [Stacks, Tag 0C1J] and the top scheme `X_n` is nonsingular. -/
def IsGlueingTower (k : Type u) [Field k] [IsAlgClosed k] :
    ℕ → Over (AlgebraicGeometry.Spec (.of k)) → Prop
  | 0, X => AlgebraicGeometry.IsRegular X.left
  | n + 1, X => ∃ (W : Over (AlgebraicGeometry.Spec (.of k))) (f : W ⟶ X)
      (a b : AlgebraicGeometry.Spec (.of k) ⟶ W.left),
      AlgebraicGeometry.IsGlueingTwoPoints f.left a b ∧ IsGlueingTower k n W

/-- **Clause (3) of [Stacks, Tag 0C1X].** There is a sequence of morphisms
`U_n ⟶ U_{n-1} ⟶ … ⟶ U_0 = U ⊆ X` with `U` an open neighbourhood of `x`, with `U_n`
nonsingular, and with every step a glueing of two points. -/
def HasNonsingularGlueingResolution (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))] (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ),
    IsGlueingTower k n (Over.mk (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))))

/-- A tower of `n` glueings of two rational points joining `X` to a scheme isomorphic to `Z`.
This is `Stacks.Curves.IsGlueingTower` with the nonsingularity of the top scheme replaced by an
identification of it, so that two towers can be stacked. -/
private def IsGlueingTowerTo (k : Type u) [Field k] [IsAlgClosed k] :
    ℕ → Over (AlgebraicGeometry.Spec (.of k)) → Over (AlgebraicGeometry.Spec (.of k)) → Prop
  | 0, X, Z => Nonempty (X ≅ Z)
  | n + 1, X, Z => ∃ (W : Over (AlgebraicGeometry.Spec (.of k))) (f : W ⟶ X)
      (a b : AlgebraicGeometry.Spec (.of k) ⟶ W.left),
      AlgebraicGeometry.IsGlueingTwoPoints f.left a b ∧ IsGlueingTowerTo k n W Z

/-- `X` is obtained from a scheme isomorphic to `Z` by finitely many glueings of two rational
points. -/
private def HasGlueingTowerTo (k : Type u) [Field k] [IsAlgClosed k]
    (X Z : Over (AlgebraicGeometry.Spec (.of k))) : Prop :=
  ∃ n : ℕ, IsGlueingTowerTo k n X Z

/-- The empty tower. -/
private theorem hasGlueingTowerTo_of_iso {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Over (AlgebraicGeometry.Spec (.of k))} (e : X ≅ Z) : HasGlueingTowerTo k X Z :=
  ⟨0, ⟨e⟩⟩

/-- Prepending one glueing step to a tower. -/
private theorem HasGlueingTowerTo.cons {k : Type u} [Field k] [IsAlgClosed k]
    {W X Z : Over (AlgebraicGeometry.Spec (.of k))} (f : W ⟶ X)
    (a b : AlgebraicGeometry.Spec (.of k) ⟶ W.left)
    (hglue : AlgebraicGeometry.IsGlueingTwoPoints f.left a b)
    (h : HasGlueingTowerTo k W Z) : HasGlueingTowerTo k X Z := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, W, f, a, b, hglue, h⟩

/-- An isomorphism in `Over S` has an isomorphism as its underlying morphism. -/
private instance isIso_left_of_isIso_over {S : Scheme.{u}} {X Y : Over S} (g : X ⟶ Y) [IsIso g] :
    IsIso g.left :=
  inferInstanceAs (IsIso ((Over.forget S).map g))

/-- A tower is unchanged by an isomorphism at its bottom: the isomorphism is absorbed into the
first glueing step, by `Stacks.Curves.isGlueingTwoPoints_comp_iso`. -/
private theorem HasGlueingTowerTo.of_isoLeft {k : Type u} [Field k] [IsAlgClosed k]
    {X Y Z : Over (AlgebraicGeometry.Spec (.of k))} (e : X ≅ Y)
    (h : HasGlueingTowerTo k Y Z) : HasGlueingTowerTo k X Z := by
  obtain ⟨n, h⟩ := h
  match n, h with
  | 0, ⟨h⟩ => exact ⟨0, ⟨e.trans h⟩⟩
  | (n + 1), ⟨W, f, a, b, hglue, htower⟩ =>
    letI : LocallyOfFiniteType Y.hom := hglue.2.2.2.2.2.2.1
    letI : QuasiCompact Y.hom := hglue.2.2.2.2.2.2.2.1
    letI : LocallyOfFiniteType (X.left ↘ AlgebraicGeometry.Spec (.of k)) := by
      show LocallyOfFiniteType X.hom
      rw [← Over.w e.hom]
      infer_instance
    letI : QuasiCompact (X.left ↘ AlgebraicGeometry.Spec (.of k)) := by
      show QuasiCompact X.hom
      rw [← Over.w e.hom]
      infer_instance
    refine ⟨n + 1, W, f ≫ e.inv, a, b, ?_, htower⟩
    exact isGlueingTwoPoints_comp_iso f.left a b hglue (asIso e.inv.left) ⟨Over.w e.inv⟩

/-- Towers stack. -/
private theorem HasGlueingTowerTo.trans {k : Type u} [Field k] [IsAlgClosed k]
    {X Y Z : Over (AlgebraicGeometry.Spec (.of k))}
    (h₁ : HasGlueingTowerTo k X Y) (h₂ : HasGlueingTowerTo k Y Z) :
    HasGlueingTowerTo k X Z := by
  obtain ⟨n, h₁⟩ := h₁
  induction n generalizing X with
  | zero => exact HasGlueingTowerTo.of_isoLeft h₁.some h₂
  | succ n ih =>
    obtain ⟨W, f, a, b, hglue, htower⟩ := h₁
    exact HasGlueingTowerTo.cons f a b hglue (ih htower)

/-- A tower ending at a nonsingular scheme is a tower in the sense of
`Stacks.Curves.IsGlueingTower`. -/
private theorem exists_isGlueingTower_of_hasGlueingTowerTo {k : Type u} [Field k] [IsAlgClosed k]
    {X Z : Over (AlgebraicGeometry.Spec (.of k))} (h : HasGlueingTowerTo k X Z)
    (hZ : AlgebraicGeometry.IsRegular Z.left) : ∃ n : ℕ, IsGlueingTower k n X := by
  obtain ⟨n, h⟩ := h
  induction n generalizing X with
  | zero =>
    obtain ⟨e⟩ := h
    letI : IsLocallyNoetherian Z.left := by
      have h2 := ((AlgebraicGeometry.isRegular_tfae Z.left).out 1 2).mp hZ
      exact h2.1
    letI : IsLocallyNoetherian X.left :=
      LocallyOfFiniteType.isLocallyNoetherian e.hom.left
    exact ⟨0, AlgebraicGeometry.isRegular_of_iso (asIso e.hom.left) hZ⟩
  | succ n ih =>
    obtain ⟨W, f, a, b, hglue, htower⟩ := h
    obtain ⟨m, hm⟩ := ih htower
    exact ⟨m + 1, W, f, a, b, hglue, hm⟩

/-! ### Clause (3) implies clause (1) -/

/-- **Every closed point of a scheme carrying a tower of glueings has a completed local ring
which is a multicross ring or a field.** The top scheme of the tower is nonsingular, so this
holds there; and one glueing step adds exactly one point, whose completion is the pair pullback
of two completions below by
`Stacks.Curves.hasMulticrossOrFieldCompletion_of_isGlueingTwoPoints`, while over every other
point the step is an isomorphism on stalks. -/
private theorem hasMulticrossOrFieldCompletion_of_isGlueingTower
    {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ) :
    ∀ X : Over (AlgebraicGeometry.Spec (.of k)), IsGlueingTower k n X →
      LocallyOfFiniteType X.hom → topologicalKrullDim X.left ≤ 1 →
      ∀ x : X.left, IsClosed ({x} : Set X.left) →
        HasMulticrossOrFieldCompletion k X.left x := by
  induction n with
  | zero =>
    intro X hreg hft hdim x hx
    letI : LocallyOfFiniteType X.hom := hft
    letI : LocallyOfFiniteType (X.left ↘ AlgebraicGeometry.Spec (.of k)) := hft
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    letI : IsReduced X.left := isReduced_of_isRegular hreg
    exact hasMulticrossOrFieldCompletion_of_regular k X.left x hx
      (isRegularLocalRing_stalk_of_isRegular hreg x)
      ((AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim x).trans hdim)
  | succ n ih =>
    intro X htower hft hdim x hx
    obtain ⟨W, f, a, b, hglue, hW⟩ := htower
    letI : LocallyOfFiniteType X.hom := hft
    letI : LocallyOfFiniteType (X.left ↘ AlgebraicGeometry.Spec (.of k)) := hft
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    letI hftW : LocallyOfFiniteType W.hom := hglue.2.2.2.2.1
    letI : LocallyOfFiniteType (W.left ↘ AlgebraicGeometry.Spec (.of k)) := hftW
    letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
    letI : IsFinite f.left := hglue.2.2.2.2.2.2.2.2.choose_spec.1
    have hdimW : topologicalKrullDim W.left ≤ 1 :=
      (AlgebraicGeometry.topologicalKrullDim_le_of_isIntegralHom f.left).trans hdim
    have ihW := ih W hW hftW hdimW
    by_cases heq : x = (a ≫ f.left) (closedPoint k)
    · subst heq
      exact hasMulticrossOrFieldCompletion_of_isGlueingTwoPoints f.left a b hglue
        (ihW _ (pointEquivClosedPoint W.hom ⟨a, hglue.1.comp_over⟩).property)
        (ihW _ (pointEquivClosedPoint W.hom ⟨b, hglue.2.1.comp_over⟩).property)
    · obtain ⟨y, hy⟩ := (surjective_of_isGlueingTwoPoints f.left a b hglue).surj x
      have hne : f.left y ≠ (a ≫ f.left) (closedPoint k) := by rwa [hy]
      letI : IsIso (f.left.stalkMap y) :=
        isIso_stalkMap_of_isGlueingTwoPoints_of_ne f.left a b hglue y hne
      have hyclosed : IsClosed ({y} : Set W.left) := by
        obtain ⟨_, _, ⟨V, hV, hiso⟩, _⟩ := hglue.2.2.2.2.2.2.2.2
        letI : IsIso (f.left ∣_ V) := hiso
        have hxV : x ∈ V := by
          rw [← SetLike.mem_coe, hV]
          exact heq
        have hyV : y ∈ f.left ⁻¹ᵁ V := by change f.left y ∈ V; rwa [hy]
        have hfiber : f.left ⁻¹' ({x} : Set X.left) = {y} := by
          ext z
          constructor
          · intro hz
            have hz' : f.left z = x := hz
            have hzV : z ∈ f.left ⁻¹ᵁ V := by change f.left z ∈ V; rwa [hz']
            have hh : (f.left ∣_ V) ⟨z, hzV⟩ = (f.left ∣_ V) ⟨y, hyV⟩ := by
              apply Subtype.ext
              exact (morphismRestrict_base_coe f.left V ⟨z, hzV⟩).trans
                ((hz'.trans hy.symm).trans
                  (morphismRestrict_base_coe f.left V ⟨y, hyV⟩).symm)
            exact congrArg Subtype.val ((f.left ∣_ V).homeomorph.injective hh)
          · rintro rfl
            exact hy
        rw [← hfiber]
        exact hx.preimage f.left.continuous
      rw [← hy]
      exact hasMulticrossOrFieldCompletion_of_isIso_stalkMap f.left hglue.2.2.2.1 y
        (ihW y hyclosed)

/-- **Clause (3) implies clause (1) of [Stacks, Tag 0C1X].** -/
private theorem isMulticrossSingularity_of_hasNonsingularGlueingResolution
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X ≤ 1) (x : X)
    (hx : IsClosed ({x} : Set X)) (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (h : HasNonsingularGlueingResolution k X x) :
    Stacks.Curves.IsMulticrossSingularity k X x := by
  obtain ⟨U, hxU, n, htower⟩ := h
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  letI : U.toScheme.Over (AlgebraicGeometry.Spec (.of k)) :=
    ⟨U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))⟩
  letI : LocallyOfFiniteType (U.toScheme ↘ AlgebraicGeometry.Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))))
  letI : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U.toScheme ↘ AlgebraicGeometry.Spec (.of k))
  have hdimU : topologicalKrullDim U.toScheme ≤ 1 :=
    (topologicalKrullDim_subspace_le X U).trans hX
  have hc := hasMulticrossOrFieldCompletion_of_isGlueingTower n _ htower
    (inferInstanceAs (LocallyOfFiniteType (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k)))))
    hdimU
  let y : U.toScheme := ⟨x, hxU⟩
  have hyclosed : IsClosed ({y} : Set U.toScheme) := by
    have ht := hx.preimage U.ι.continuous
    convert ht using 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.Opens.ι_apply]
    exact Subtype.ext_iff
  have hcU : HasMulticrossOrFieldCompletion k U.toScheme y := hc _ hyclosed
  letI : IsIso (U.ι.stalkMap y) := inferInstance
  have hcX := hasMulticrossOrFieldCompletion_of_isIso_stalkMap U.ι ⟨rfl⟩ y hcU
  exact isMulticrossSingularity_of_hasMulticrossOrFieldCompletion k x hx hsing hcX

/-! ### Clause (1) implies clause (3) -/

/-- A chain of elementary modifications whose target is of finite type over `k` has a source of
finite type over `k`. -/
private theorem locallyOfFiniteType_of_isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (AlgebraicGeometry.Spec (.of k))} {f : X' ⟶ X}
    (h : Stacks.GlueSquishFactor.IsElementaryChain k f) :
    LocallyOfFiniteType X.hom → LocallyOfFiniteType X'.hom := by
  induction h with
  | @of_isIso Y' Y g hg =>
    intro hX
    haveI := hg
    letI : LocallyOfFiniteType Y.hom := hX
    rw [← Over.w g]
    infer_instance
  | of_step g hg =>
    intro _
    rcases hg with ⟨a, b, hh⟩ | ⟨θ, hh⟩
    · exact hh.2.2.2.2.1
    · exact hh.2.1
  | comp _ _ ihg ihf => exact fun hX => ihg (ihf hX)

/-- A chain of elementary modifications with a reduced source has a reduced target: every
elementary modification is injective on sections. -/
private theorem isReduced_of_isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (AlgebraicGeometry.Spec (.of k))} {f : X' ⟶ X}
    (h : Stacks.GlueSquishFactor.IsElementaryChain k f) :
    IsReduced X'.left → IsReduced X.left := by
  induction h with
  | of_isIso g hg =>
    intro hX'
    haveI := hg
    letI := hX'
    refine ⟨fun V => ?_⟩
    exact _root_.isReduced_of_injective (g.left.app V).hom
      (ConcreteCategory.bijective_of_isIso (g.left.app V)).1
  | of_step g hg =>
    intro hX'
    letI := hX'
    rcases hg with ⟨a, b, hh⟩ | ⟨θ, hh⟩
    · exact isReduced_of_isGlueingTwoPoints g.left a b hh
    · refine ⟨fun V => ?_⟩
      exact _root_.isReduced_of_injective (g.left.app V).hom
        (app_injective_of_isSquishingTangentVector g.left θ hh V)
  | comp _ _ ihg ihf => exact fun hX' => ihf (ihg hX')

/-- **No step of a chain of elementary modifications over a scheme with seminormal completed
local rings is a squishing of a tangent vector**, so such a chain is a tower of glueings of two
points; and the completed local rings at the source of the chain are seminormal too.

This is the step of the proof of [Stacks, Tag 0C1X] which rules out squishing a tangent vector.
The source argues numerically, that a squishing leaves the number of branches unchanged while
dropping the delta invariant by one, which contradicts [Stacks, Tag 0C1V] at a multicross
point; the argument here reads the same obstruction off the completion, since the completion at
a multicross point is seminormal while a squishing produces a non-seminormal completion. -/
private theorem hasGlueingTowerTo_of_isElementaryChain {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (AlgebraicGeometry.Spec (.of k))} {f : X' ⟶ X}
    (hchain : Stacks.GlueSquishFactor.IsElementaryChain k f)
    (hft : LocallyOfFiniteType X.hom) (hred : IsReduced X'.left)
    (hsemi : ∀ z : X.left, IsClosed ({z} : Set X.left) →
      IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X.left z)) :
    HasGlueingTowerTo k X X' ∧
      ∀ z : X'.left, IsClosed ({z} : Set X'.left) →
        IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X'.left z) := by
  induction hchain with
  | @of_isIso Y' Y g hg =>
    haveI := hg
    letI : LocallyOfFiniteType Y.hom := hft
    letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    letI : LocallyOfFiniteType Y'.hom := by rw [← Over.w g]; infer_instance
    letI : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
    refine ⟨hasGlueingTowerTo_of_iso (asIso g).symm, fun z hz => ?_⟩
    have hzc : IsClosed ({g.left z} : Set Y.left) := by
      simpa using g.left.isClosedMap _ hz
    exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
      (completedLocalRing_ringEquiv_of_isIso_stalkMap g.left z).symm (hsemi _ hzc)
  | @of_step Y' Y g hg =>
    letI : LocallyOfFiniteType Y.hom := hft
    letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    letI := hred
    rcases hg with ⟨a, b, hh⟩ | ⟨θ, hh⟩
    · letI : LocallyOfFiniteType Y'.hom := hh.2.2.2.2.1
      letI : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
      exact ⟨⟨1, Y', g, a, b, hh, ⟨Iso.refl Y'⟩⟩,
        isSeminormalRing_completedLocalRing_of_isGlueingTwoPoints g.left a b hh hsemi⟩
    · exact (not_isSquishingTangentVector_of_seminormal_completions g.left θ hsemi hh).elim
  | @comp Z Y' Y g gf hg hf ihg ihf =>
    have hftMid := locallyOfFiniteType_of_isElementaryChain hf hft
    have hredMid := isReduced_of_isElementaryChain hg hred
    obtain ⟨h₁, hsemiMid⟩ := ihf hft hredMid hsemi
    obtain ⟨h₂, hsemiTop⟩ := ihg hftMid hred hsemiMid
    exact ⟨h₁.trans h₂, hsemiTop⟩


/-- **The normalization morphism of a reduced one-dimensional algebraic scheme satisfies the
hypotheses of [Stacks, Tag 0C1L]**: it is finite, it is injective on sections, and it is an
isomorphism over the regular locus, whose complement is the singular locus. -/
private theorem isAlmostIso_normalization
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (.of k))] [IsReduced X] [IsLocallyNoetherian X]
    (hNagata : IsNagataScheme X) (hX : topologicalKrullDim X = 1)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hSing : (AlgebraicGeometry.singularLocus X).Finite) :
    Stacks.GlueSquishFactor.IsAlmostIso
      (Over.homMk (AlgebraicGeometry.Scheme.normalization X hfin) rfl :
        Over.mk (AlgebraicGeometry.Scheme.normalization X hfin ≫
            (X ↘ AlgebraicGeometry.Spec (.of k))) ⟶
          Over.mk (X ↘ AlgebraicGeometry.Spec (.of k))) := by
  set ν := AlgebraicGeometry.Scheme.normalization X hfin with hν
  letI : IsFinite ν := AlgebraicGeometry.Scheme.isFinite_normalization hNagata hfin
  haveI := AlgebraicGeometry.Scheme.quasiCompactFromGenericPointResidueFields X hfin
  haveI := AlgebraicGeometry.Scheme.quasiSeparatedFromGenericPointResidueFields X
  have hinjapp : ∀ U : X.Opens, Function.Injective (ν.app U) :=
    Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app
      (AlgebraicGeometry.Scheme.fromGenericPointResidueFields X)
  let R : X.Opens :=
    ⟨AlgebraicGeometry.regularLocus X,
      AlgebraicGeometry.isOpen_regularLocus_of_isNagataScheme X hNagata hX.le⟩
  have hRreg : AlgebraicGeometry.IsRegular R.toScheme := by
    apply ((AlgebraicGeometry.isRegular_tfae R.toScheme).out 1 2).mpr
    refine ⟨inferInstance, fun y => ?_⟩
    exact (AlgebraicGeometry.mem_regularLocus_opens_iff R y).mpr y.2
  have hRnormal : AlgebraicGeometry.IsNormal R.toScheme :=
    AlgebraicGeometry.isNormal_of_isRegular R.toScheme hRreg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, R, hSing,
    AlgebraicGeometry.Scheme.isIso_normalization_restrict_of_isNormal X hfin R hRnormal⟩, ?_⟩
  · show LocallyOfFiniteType (ν ≫ (X ↘ AlgebraicGeometry.Spec (.of k)))
    infer_instance
  · show QuasiCompact (ν ≫ (X ↘ AlgebraicGeometry.Spec (.of k)))
    infer_instance
  · show LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))
    infer_instance
  · show QuasiCompact (X ↘ AlgebraicGeometry.Spec (.of k))
    infer_instance
  · show IsFinite ν
    infer_instance
  refine Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_injective_app ν fun y => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨V, hV, hyV, hinjapp V⟩

/-- **Clause (1) implies clause (3) of [Stacks, Tag 0C1X], at the level of the whole scheme.**
A reduced one-dimensional algebraic scheme with finitely many singular points and seminormal
completed local rings carries a tower of glueings of two points: apply [Stacks, Tag 0C1L] to the
normalization morphism and rule out every squishing of a tangent vector. -/
private theorem exists_isGlueingTower_of_forall_isSeminormalRing
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (.of k))] [IsReduced X]
    (hX : topologicalKrullDim X = 1) (hSing : (AlgebraicGeometry.singularLocus X).Finite)
    (hsemi : ∀ z : X, IsClosed ({z} : Set X) →
      IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X z)) :
    ∃ n : ℕ, IsGlueingTower k n (Over.mk (X ↘ AlgebraicGeometry.Spec (.of k))) := by
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  have hNagata := AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field k
    (X ↘ AlgebraicGeometry.Spec (.of k))
  have hfin := finite_irreducibleComponents_of_isNagataScheme X hNagata
  letI : IsFinite (AlgebraicGeometry.Scheme.normalization X hfin) :=
    AlgebraicGeometry.Scheme.isFinite_normalization hNagata hfin
  have hregν : AlgebraicGeometry.IsRegular
      (AlgebraicGeometry.Scheme.normalizationScheme X hfin) :=
    normalizationScheme_isRegular hNagata hfin hX.le
  have hchain := Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain
    (Over.homMk (AlgebraicGeometry.Scheme.normalization X hfin) rfl :
      Over.mk (AlgebraicGeometry.Scheme.normalization X hfin ≫
          (X ↘ AlgebraicGeometry.Spec (.of k))) ⟶
        Over.mk (X ↘ AlgebraicGeometry.Spec (.of k)))
    (isAlmostIso_normalization k X hNagata hX hfin hSing)
  obtain ⟨htower, -⟩ := hasGlueingTowerTo_of_isElementaryChain hchain
    (inferInstanceAs (LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))))
    (isReduced_of_isRegular hregν) hsemi
  exact exists_isGlueingTower_of_hasGlueingTowerTo htower hregν


/-! ### The displayed equivalence fails at a nonsingular point -/

/-- **The equivalence of [Stacks, Tag 0C1X] as displayed is false at a nonsingular closed point,
and this is the counterexample.** Let `x` be a closed point of a reduced algebraic
one-dimensional `k`-scheme whose local ring is regular of dimension one — a nonsingular point of
the curve. Then the delta invariant of `X` at `x` is `0` and the number of branches is `1`, so
clause (2) holds with both its sides `0`, while clause (1) fails: Definition 0C1W asks the
completion to be the multicross ring on `n ≥ 2` branches, which has `n` minimal primes and not
one. Those two facts are
`Stacks.Curves.deltaInvariant_eq_and_not_isMulticrossSingularity_of_isRegularLocalRing`: the
local ring is a discrete valuation ring, hence integrally closed, so its delta invariant
vanishes, and its completion is a domain, so it has a single minimal prime.

Every displayed hypothesis of the lemma holds at such a point — `k` is algebraically closed, `X`
is a reduced algebraic one-dimensional `k`-scheme, `x` is a point of `X` — and the displayed
conclusion fails already between clauses (1) and (2), whatever clause (3) does there. So the
restriction to a point whose local ring is not regular carried by
`Stacks.Curves.isMulticrossSingularity_tfae` is an erratum repair and not a weakening: it is
exactly the hypothesis that rules this configuration out.

The hypotheses are satisfiable, and
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_specPolynomial`
exhibits them at a concrete scheme: the origin of the affine line. -/
theorem exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (.of k))] [IsReduced X]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    (topologicalKrullDim X = 1 ∧ IsClosed ({x} : Set X)) ∧
      (Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1 ∧
        ¬ Stacks.Curves.IsMulticrossSingularity k X x) ∧
      ¬ List.TFAE
        [Stacks.Curves.IsMulticrossSingularity k X x,
          Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1,
          HasNonsingularGlueingResolution k X x] := by
  obtain ⟨⟨heq, -⟩, hnot⟩ :=
    deltaInvariant_eq_and_not_isMulticrossSingularity_of_isRegularLocalRing k X x hx hreg hdim
  exact ⟨⟨hX, hx⟩, ⟨heq, hnot⟩, fun h => hnot ((h.out 2 1).mp heq)⟩

/-- **The counterexample of
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point` on
a concrete scheme.** Take `X` to be the affine line over an algebraically closed field `k` and
`x` to be its origin, the prime generated by the coordinate. The affine line is a reduced
algebraic one-dimensional `k`-scheme — `AlgebraicGeometry.topologicalKrullDim_specPolynomial`
for the dimension — and the origin is a closed point because the coordinate generates a maximal
ideal of `k[T]`. The local ring there is the localization of `k[T]` at that maximal ideal, a
discrete valuation ring because `k[T]` is a Dedekind domain, so it is regular of dimension one.

So the displayed hypotheses of [Stacks, Tag 0C1X] are satisfied by a configuration in which its
displayed conclusion fails: clause (2) holds at the origin of the affine line and clause (1)
does not.

The first conjunct records which `k`-scheme the affine line is here: its structure morphism is
`Spec` of the inclusion `k → k[T]`, the instance `AlgebraicGeometry.specOverSpec`, so no other
`k`-structure is secretly in play. -/
theorem exists_counterexample_to_displayed_statement_of_tag_0C1X_specPolynomial
    (k : Type u) [Field k] [IsAlgClosed k] :
    ((AlgebraicGeometry.Spec (.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (.of k)) =
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        topologicalKrullDim (AlgebraicGeometry.Spec (.of (Polynomial k))) = 1 ∧
        IsClosed ({AlgebraicGeometry.originPolynomial k} :
          Set (AlgebraicGeometry.Spec (.of (Polynomial k))))) ∧
      (Ring.deltaInvariant ((AlgebraicGeometry.Spec (.of (Polynomial k))).presheaf.stalk
            (AlgebraicGeometry.originPolynomial k)) =
          numberOfBranches (AlgebraicGeometry.Spec (.of (Polynomial k)))
            (AlgebraicGeometry.originPolynomial k) - 1 ∧
        ¬ Stacks.Curves.IsMulticrossSingularity k
          (AlgebraicGeometry.Spec (.of (Polynomial k)))
          (AlgebraicGeometry.originPolynomial k)) ∧
      ¬ List.TFAE
        [Stacks.Curves.IsMulticrossSingularity k
            (AlgebraicGeometry.Spec (.of (Polynomial k)))
            (AlgebraicGeometry.originPolynomial k),
          Ring.deltaInvariant ((AlgebraicGeometry.Spec (.of (Polynomial k))).presheaf.stalk
              (AlgebraicGeometry.originPolynomial k)) =
            numberOfBranches (AlgebraicGeometry.Spec (.of (Polynomial k)))
              (AlgebraicGeometry.originPolynomial k) - 1,
          HasNonsingularGlueingResolution k (AlgebraicGeometry.Spec (.of (Polynomial k)))
            (AlgebraicGeometry.originPolynomial k)] := by
  let A := (AlgebraicGeometry.Spec (.of (Polynomial k))).presheaf.stalk
    (AlgebraicGeometry.originPolynomial k)
  have hclosed : IsClosed ({AlgebraicGeometry.originPolynomial k} :
      Set (AlgebraicGeometry.Spec (.of (Polynomial k)))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X)
  let : Algebra (Polynomial k) A :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (Polynomial k)
      (AlgebraicGeometry.originPolynomial k)
  have : IsLocalization.AtPrime A (AlgebraicGeometry.originPolynomial k).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk (Polynomial k)
      (AlgebraicGeometry.originPolynomial k)
  have : IsDomain A :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (Ideal.primeCompl_le_nonZeroDivisors (AlgebraicGeometry.originPolynomial k).asIdeal)
  have hne : (AlgebraicGeometry.originPolynomial k).asIdeal ≠ ⊥ := by
    simpa [AlgebraicGeometry.originPolynomial, Ideal.span_singleton_eq_bot] using
      (Polynomial.X_ne_zero (R := k))
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) hne A
  obtain ⟨⟨hdimX, -⟩, hclauses, hnot⟩ :=
    exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point k
      (AlgebraicGeometry.Spec (.of (Polynomial k)))
      (AlgebraicGeometry.topologicalKrullDim_specPolynomial k)
      (AlgebraicGeometry.originPolynomial k) hclosed
      (IsRegularRing.isRegularLocalRing_of_isLocalization
        (AlgebraicGeometry.originPolynomial k).asIdeal A)
      (IsDiscreteValuationRing.ringKrullDim_eq_one A)
  exact ⟨⟨rfl, hdimX, hclosed⟩, hclauses, hnot⟩

/-! ### The equivalence of the three clauses -/

/-- **Stacks 0C1X.** Let `k` be an algebraically closed field, `X` a reduced algebraic
one-dimensional `k`-scheme and `x ∈ X` a closed point whose local ring is not regular. The
following are equivalent:

1. `x` defines a multicross singularity;
2. the delta invariant of `X` at `x` is the number of branches of `X` at `x` minus one;
3. there is a sequence of morphisms `U_n ⟶ U_{n-1} ⟶ … ⟶ U_0 = U ⊆ X` with `U` an open
   neighbourhood of `x`, with `U_n` nonsingular, and with every step a glueing of two points as
   in Example 0C1J.

The equivalence of (1) and (2) is
`Stacks.Curves.isMulticrossSingularity_iff_deltaInvariant_eq_of_not_isRegularLocalRing`, which
is Tag 0C1V read at a point of a scheme. For (3) implies (1) the completion at the point glued
in each step is the pair pullback of the two completions above it, hence a multicross ring or a
field, and over every other point the step is an isomorphism on stalks. For (1) implies (3) an
open neighbourhood on which `x` is the only singular point is chosen, Tag 0C1L factors its
normalization morphism into glueings of two points and squishings of tangent vectors, and no
step is a squishing because a multicross completion is seminormal while a squishing produces a
non-seminormal completion. -/
@[stacks 0C1X "all three clauses.  The hypothesis that the local ring at `x` is not regular is \
an erratum repair, not a weakening: the source's displayed equivalence is false at a \
nonsingular closed point, where the delta invariant is 0 and the number of branches is 1, so \
clauses (2) and (3) hold while (1) fails because Definition 0C1W requires n ≥ 2 -- Lemma 0C1V, \
which the source cites for the equivalence of (1) and (2), puts no lower bound on n.  That \
counterexample is proved, not asserted, in \
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_at_nonsingular_point`, \
and at a concrete scheme -- the origin of the affine line -- in \
`Stacks.Curves.exists_counterexample_to_displayed_statement_of_tag_0C1X_specPolynomial`.  The \
hypothesis excludes exactly the regular configurations, where the equivalence fails, and \
nothing else"]
theorem isMulticrossSingularity_tfae
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    [QuasiCompact (X ↘ AlgebraicGeometry.Spec (.of k))] [IsReduced X]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X))
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    List.TFAE
      [Stacks.Curves.IsMulticrossSingularity k X x,
        Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1,
        HasNonsingularGlueingResolution k X x] := by
  tfae_have 1 ↔ 2 :=
    isMulticrossSingularity_iff_deltaInvariant_eq_of_not_isRegularLocalRing k X hX x hx hsing
  tfae_have 3 → 1 :=
    isMulticrossSingularity_of_hasNonsingularGlueingResolution k X hX.le x hx hsing
  tfae_have 1 → 3 := by
    intro h
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
    obtain ⟨U, hU, hxU, hdimU, hsingU⟩ :=
      exists_affineOpen_with_single_singularPoint k X hX x hsing
    letI : IsAffine U.toScheme := hU
    letI : U.toScheme.Over (AlgebraicGeometry.Spec (.of k)) :=
      ⟨U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))⟩
    letI : LocallyOfFiniteType (U.toScheme ↘ AlgebraicGeometry.Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))))
    letI : QuasiCompact (U.toScheme ↘ AlgebraicGeometry.Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))))
    letI : IsLocallyNoetherian U.toScheme :=
      LocallyOfFiniteType.isLocallyNoetherian (U.toScheme ↘ AlgebraicGeometry.Spec (.of k))
    have hsemiU : ∀ z : U.toScheme, IsClosed ({z} : Set U.toScheme) →
        IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing U.toScheme z) := by
      intro z hz
      by_cases hr : IsRegularLocalRing (U.toScheme.presheaf.stalk z)
      · exact isSeminormalRing_completedLocalRing_of_hasMulticrossOrFieldCompletion
          (hasMulticrossOrFieldCompletion_of_regular k U.toScheme z hz hr
            ((AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim z).trans hdimU.le))
      · have hzx : z = ⟨x, hxU⟩ := hsingU hr
        obtain ⟨m, hm, hc⟩ := h.exists_hasMulticrossCompletion
        have hs : IsSeminormalRing (AlgebraicGeometry.Scheme.completedLocalRing X x) :=
          isSeminormalRing_completedLocalRing_of_hasMulticrossOrFieldCompletion
            (Or.inr ⟨m, by omega, hc⟩)
        letI : IsIso (U.ι.stalkMap z) := inferInstance
        have heq : U.ι z = x := by rw [hzx]; simp
        have hs' : IsSeminormalRing
            (AlgebraicGeometry.Scheme.completedLocalRing X (U.ι z)) := by
          rw [heq]; exact hs
        exact Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv
          (completedLocalRing_ringEquiv_of_isIso_stalkMap U.ι z).symm hs'
    have hfinite : (AlgebraicGeometry.singularLocus U.toScheme).Finite :=
      (Set.finite_singleton _).subset hsingU
    obtain ⟨n, htower⟩ :=
      exists_isGlueingTower_of_forall_isSeminormalRing k U.toScheme hdimU hfinite hsemiU
    exact ⟨U, hxU, n, htower⟩
  tfae_finish

end Stacks.Curves

end
