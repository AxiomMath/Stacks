module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.AnnihilatorPowerPlus
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.AnnihilatorsLocalCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.Ubiquity
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Finiteness of local cohomology with specialization-closed support

Let `A` be a Noetherian ring admitting a dualizing complex, let `T ⊆ Spec(A)` be stable
under specialization and let `M` be a finite `A`-module. Faltings' finiteness criterion says that
the local cohomology modules `H^i_T(M)` are finite for all `i ≤ s` exactly when
$$ s < \operatorname{depth}_{A_p}(M_p) + \dim((A/p)_q) $$
for every pair of primes `p ∉ T`, `q ∈ T` with `p ⊆ q`.

This file is the reduction of that criterion to two statements of the source, each taken here as
a predicate so that this file does not depend on its proof. Writing

* `FinitenessAnnihilatorCriterionPlus A` for Tag 0EI1, the equivalence of (1) and (2): finiteness
  of the local cohomology of a bounded-below complex with finite cohomology through a degree is
  equivalent to uniform annihilation by one ideal supported in `T`, and
* `AnnihilatorDepthCriterion A` for Tag 0EFC, Faltings' annihilator theorem: such an ideal exists
  exactly when the depth-plus-dimension bound holds,

the criterion follows, and that implication is proved here in full.

Tag 0EFC is then **itself proved**, from `AnnihilatorDepthCriterionPlus A`, the predicate for Tag
0EHZ: the same annihilator criterion for a bounded-below *complex* with finite cohomology rather
than for a module. The module criterion is Tag 0EHZ applied to `M[0]`, and
`annihilatorDepthCriterion_of_annihilatorDepthCriterionPlus` carries out that specialization in
full. So the two inputs taken as predicates *in this file* are Tag 0EI1 and Tag 0EHZ, and both are
discharged downstream. **Tag 0EI1 is proved in this library**, unconditionally for every Noetherian
ring: `Stacks.LocalCohomology.finitenessAnnihilatorCriterionPlus` of
`FinitenessCriterionPlusUnconditional.lean` discharges
`FinitenessAnnihilatorCriterionPlus.{u, v} A` from
`localCohomologyWithSupportInPlus_finite_iff_exists_annihilator`.

## Which model of local cohomology

Throughout, local cohomology is the **set-indexed** model: `Stacks.LocalCohomology.
localCohomologyWithSupportIn` and its bounded-below companion
`localCohomologyWithSupportInPlus`, the cohomology of the total right derived functor of sections
with support in a *subset* `T` of the spectrum. It is **not** the ideal-indexed coreflection model
of `StacksFrontier/RingTheory/LocalCohomology/ModelComparison/DerivedTorsion.lean`. The two models
agree for a *closed* support `V(I)` with `I` finitely generated over a Noetherian ring, which is Tag
0955 at `Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology`; but `T` here is
only specialization-closed, so the statements below do **not** transport to the coreflection model
as they stand. What *is* available, and is used, is the comparison between
the bounded-below and the unbounded right derived functors of the *same* set-indexed model on
`D^+`, which is formalized as
`Stacks.LocalCohomology.nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso`. All of the
model bookkeeping in this file is that `D^+`-versus-unbounded comparison, applied to a module
placed in degree zero.

The derived depth `DerivedCategory.Plus.depth` is an abbreviation for the infimum of the degrees
in which this same `localCohomologyWithSupportInPlus` is nonzero, so the depth bookkeeping below
unfolds to it directly.

## Main results

* `Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_iff_exists_annihilator` — Tag 0AW8,
  the equivalence of (1) and (2), from Tag 0EI1.
* `Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_iff_depth_add_dim` — Tag 0EFD,
  Faltings' finiteness criterion, from Tag 0EI1 and Tag 0EFC.
* `Stacks.LocalCohomology.localizedComplex` and
  `Stacks.LocalCohomology.AnnihilatorDepthCriterionPlus` — the construction and the statement of
  Tag 0EHZ, the annihilator criterion for a complex.
* `Stacks.LocalCohomology.annihilatorDepthCriterion_of_annihilatorDepthCriterionPlus` —
  **Tag 0EFC from Tag 0EHZ**.
* `Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_iff_depth_add_dim_of_criterionPlus`
  — Tag 0EFD from Tag 0EI1 and Tag 0EHZ alone.
* `Stacks.LocalCohomology.finitenessAnnihilatorCriterionPlus_of_subsingleton`,
  `Stacks.LocalCohomology.annihilatorDepthCriterion_of_subsingleton` and
  `Stacks.LocalCohomology.annihilatorDepthCriterionPlus_of_subsingleton` — the three predicates
  hold over the zero ring, so none is a contradictory assumption.
* `Stacks.LocalCohomology.annihilatorDepthCriterionPlus_univ` — both sides of the Tag 0EHZ
  criterion hold at `T' = Spec(A)` over an arbitrary, in particular nontrivial, ring.
* `Stacks.LocalCohomology.exists_specialization_into_stableUnderSpecialization` — the premises
  `p ∉ T`, `q ∈ T`, `p ⊆ q` of the depth-dimension clause are simultaneously
  satisfiable, so that clause is not quantified over an empty family.
* `Stacks.LocalCohomology.exists_isDualizingComplex_and_stableUnderSpecialization` — a field has
  a dualizing complex and a nonempty specialization-closed support, so the ambient hypotheses of
  the criterion are satisfiable at a nontrivial ring.
* `Stacks.LocalCohomology.not_depth_add_dim_gt_of_eq_natCast` and
  `Stacks.LocalCohomology.depth_add_dim_gt_of_lt` — at finite depth `d` and dimension `n` the
  depth-dimension clause holds exactly for `s < d + n`; in particular the coercions into `EInt`
  make it neither automatically true nor automatically false.

## Implementation notes

The dimension of `(A/p)_q` appears in two equivalent shapes. Tag 0EFC states it as the Krull
dimension of `A_q / p A_q`, valued in `WithBot ℕ∞` and compared against the degree
in the extended integers `EInt` through `Stacks.Algebraization.enatToEInt` and
`Stacks.Algebraization.krullDimToEInt`. Tag 0EFD states it as the height of the image of `q` in
`A/p`, with the comparison in `ℕ∞` against a natural-number degree. The two are
reconciled by `ringKrullDim_quotient_map_ker_eq_height` together with the case analysis in
`depth_add_height_iff_eint`; the cohomological degree stays an integer, as in the source.

The derived depth of Tag 0EHY is defined with the `Module`-namespace copy of sections with
support, and the criteria here with the `Stacks.LocalCohomology` copy. The two developments are
character-identical and definitionally equal, so the arguments that unfold
`DerivedCategory.Plus.depth` — `moduleDepth_eq_plusDepth_single` and `plusDepth_eq_of_iso` —
cross between the two spellings by `exact` and `change` rather than by rewriting.

No `@[stacks]` attribute is placed. Tag 0EFD's covering set is the criterion itself, and the
criterion is proved here only *conditionally* on those predicates, so an attribute would report the
tag as formalized from a statement that assumes it. The same holds for the 0AW8 statement here,
which is conditional on the Tag 0EI1 predicate; the other half of 0AW8, the equivalence of (2) and
(3), is proved unconditionally on
`Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator` in
`StacksFrontier/RingTheory/LocalCohomology/AnnihilatorPower.lean`, and carries the tag there. Tag 0EFC
is proved here, but only from the Tag 0EHZ predicate, which is unproved, so it carries no attribute
either.

## References

* [Faltings-annulators]
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
* [Stacks Project, Tag 0EHZ](https://stacks.math.columbia.edu/tag/0EHZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

/-- **Stacks 0EI1, equivalence of (1) and (2)**, as a predicate on the base ring.

For every specialization-closed `T` and every bounded-below complex `K` with finite cohomology,
the local cohomology `H^i_T(K)` is finite for all `i ≤ n` exactly when one ideal whose zero
locus lies in `T` annihilates all of them. It is one of the two inputs to Faltings' finiteness
criterion below, taken as a predicate here so that this file does not depend on its proof —
but it **is** proved in this library, unconditionally for every Noetherian ring, by
`Stacks.LocalCohomology.finitenessAnnihilatorCriterionPlus` of
`FinitenessCriterionPlusUnconditional.lean`. -/
def FinitenessAnnihilatorCriterionPlus (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (T : Set (PrimeSpectrum A)), StableUnderSpecialization T →
    ∀ (K : DerivedCategory.Plus (ModuleCat.{max u v} A)),
      (∀ i : ℤ, Module.Finite A
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) →
      ∀ n : ℤ,
      ((∀ i : ℤ, i ≤ n → Module.Finite A
          (localCohomologyWithSupportInPlus.{u, v} A T K i)) ↔
        (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
          ∀ i : ℤ, i ≤ n → J ≤ Module.annihilator A
            (localCohomologyWithSupportInPlus.{u, v} A T K i)))

/-- The comparison, on a module placed in degree zero, between its bounded-below and its
unbounded local cohomology with support in `T`. Both are the same set-indexed model; this is the
`D^+`-versus-unbounded identification of Tag 0EF4's cohomology calculation. -/
private noncomputable def localCohomologyWithSupportInPlusIso
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) :
    localCohomologyWithSupportInPlus.{u, v} A T
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i ≅
      localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i := by
  let K := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  let e := (nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso.{u, v} A T).some.app K
  let eM := (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u v} A) 0).app M
  change (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      (DerivedCategory.Plus.ι.obj ((derivedSectionsWithSupportInPlus.{u, v} A T).obj K)) ≅ _
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    (e ≪≫ (derivedSectionsWithSupportIn.{u, v} A T).mapIso eM)

/-- A finite module placed in degree zero has finite cohomology in every degree: the module
itself in degree zero, and zero elsewhere. -/
private theorem finite_homology_singleFunctor
    (A : Type u) [CommRing A] (M : ModuleCat.{max u v} A) [Module.Finite A M] (i : ℤ) :
    Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) := by
  by_cases hi : i = 0
  · subst i
    let e : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) 0).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) ≅ M :=
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u v} A) 0).app M) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) 0).app M
    exact (Module.Finite.equiv_iff e.toLinearEquiv).mpr inferInstance
  · have hz : Limits.IsZero ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{max u v} A) i).obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) := by
      have hzD : Limits.IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} A) i).obj ((DerivedCategory.singleFunctor
            (ModuleCat.{max u v} A) 0).obj M)) := by
        show Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))
        exact (HomologicalComplex.isZero_single_obj_homology
          (ComplexShape.up ℤ) 0 M i hi).of_iso ((DerivedCategory.homologyFunctorFactors
          (ModuleCat.{max u v} A) i).app _)
      exact hzD.of_iso ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} A) i).mapIso
          ((DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u v} A) 0).app M))
    have : Subsingleton ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{max u v} A) i).obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    have : Module.FinitePresentation A ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{max u v} A) i).obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) :=
      inferInstance
    exact inferInstance

/-- An ideal supported in `T'` annihilates the bounded-below local cohomology of `M[0]` through
degree `s` exactly when it annihilates the unbounded one. -/
private theorem exists_annihilator_plus_iff
    (A : Type u) [CommRing A] (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (s : ℤ) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
          (localCohomologyWithSupportInPlus.{u, v} A T
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
          (localCohomologyWithSupportIn.{u, v} A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) := by
  refine exists_congr fun J => and_congr_right fun _ => forall₂_congr fun i _ => ?_
  rw [(localCohomologyWithSupportInPlusIso.{u, v} A T M i).toLinearEquiv.annihilator_eq]

/-- **Stacks 0AW8, equivalence of (1) and (2).** For a finite module over a Noetherian ring,
finiteness of local cohomology with specialization-closed support through degree `n` is
equivalent to uniform annihilation by one ideal supported in `T`.

This is Tag 0EI1 for the complex `M[0]`, transported from the bounded-below to the unbounded
derived functor of sections with support. -/
theorem localCohomologyWithSupportIn_finite_iff_exists_annihilator
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEI1 : FinitenessAnnihilatorCriterionPlus.{u, v} A)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] (n : ℕ) :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
      (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A
          (localCohomologyWithSupportIn.{u, v} A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) := by
  have hcrit := hEI1 T hT ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
    (finite_homology_singleFunctor.{u, v} A M) (n : ℤ)
  have hfinite :
      (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportInPlus.{u, v} A T
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn.{u, v} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) :=
    forall₂_congr fun i _ =>
      Module.Finite.equiv_iff (localCohomologyWithSupportInPlusIso.{u, v} A T M i).toLinearEquiv
  exact hfinite.symm.trans (hcrit.trans (exists_annihilator_plus_iff.{u, v} A T T M n))

/-- **Stacks 0EFC, Faltings' annihilator theorem**, as a predicate on the base ring.

For a finite module `M`, nested specialization-closed subsets `T ⊆ T'` and a dualizing
complex, an ideal supported in `T'` annihilates `H^i_T(M)` for all `i ≤ s` exactly when
`depth_{A_p}(M_p) + \dim(A_q/pA_q) > s` for every `p ∉ T'` and `q ∈ T` with
`p ⊆ q`. It is taken here as a predicate so that this file does not depend on its proof; the tag
itself is proved in this library, with the three universes collapsed, by
`Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff`. It is the second input
to Faltings' finiteness criterion below. -/
def AnnihilatorDepthCriterion (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (M : Type (max u v)) [AddCommGroup M] [Module A M] [Module.Finite A M],
    ∀ (T T' : Set (PrimeSpectrum A)), T ⊆ T' →
      StableUnderSpecialization T → StableUnderSpecialization T' →
      ∀ s : ℤ, 0 ≤ s →
      ∀ (omega : DerivedCategory (ModuleCat.{w} A)), Dualizing.IsDualizingComplex omega →
      ((∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
          ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
            (localCohomologyWithSupportIn.{u, v} A T
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
                (ModuleCat.of A M)) i)) ↔
        (∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
          Stacks.Algebraization.enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M)) +
            Stacks.Algebraization.krullDimToEInt
              (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt)))

/-- A natural number is smaller than `⊤` in the extended integers. -/
public theorem eint_natCast_lt_top (n : ℕ) : ((n : ℤ) : EInt) < ⊤ := by
  show (WithBot.some (WithTop.some (n : ℤ))) < (WithBot.some (⊤ : WithTop ℤ))
  exact (WithBot.coe_lt_coe).2 (WithTop.coe_lt_top _)

private theorem depth_add_height_iff_eint (s : ℕ) (d h : ℕ∞) :
    (s : ℕ∞) < d + h ↔
      Stacks.Algebraization.enatToEInt d +
        Stacks.Algebraization.krullDimToEInt (h : WithBot ℕ∞) > ((s : ℤ) : EInt) := by
  cases d <;> cases h
  case coe.coe d h =>
    dsimp [Stacks.Algebraization.enatToEInt, Stacks.Algebraization.krullDimToEInt,
      WithBotTop.coe]
    show (s : ℕ∞) < d + h ↔ ((d + h : ℤ) : EInt) > ((s : ℤ) : EInt)
    simp only [WithBotTop.coe_lt_coe]
    norm_cast
  all_goals exact ⟨fun _ => eint_natCast_lt_top s, fun _ => by simp⟩

/-- The dimension `dim((A/p)_q)`, spelled as the Krull dimension of `A_q / p A_q`, is the
height of the image of `q` in `A/p`. -/
public theorem ringKrullDim_localization_quotient_eq_height
    {A : Type u} [CommRing A] (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) =
      ((q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height : WithBot ℕ∞) := by
  let f : A →+* A ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  let qbar : Ideal (A ⧸ p.asIdeal) := q.asIdeal.map f
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) (qbar.comap f) := by
    simpa only [qbar, f, Ideal.comap_map_mk hpq] using
      (inferInstance : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) q.asIdeal)
  have h := ringKrullDim_quotient_map_ker_eq_height f Ideal.Quotient.mk_surjective
    qbar (Localization.AtPrime q.asIdeal)
  rw [show RingHom.ker f = p.asIdeal from Ideal.mk_ker] at h
  simpa [qbar, f] using h

/-- **Stacks 0EFD, Proposition 51.11.1: Faltings' finiteness criterion**, conditional on Tag 0EI1
and Tag 0EFC.

For a finite module `M` over a Noetherian ring with a dualizing complex and a specialization-closed
`T`, the local cohomology modules `H^i_T(M)` are finite for all `i ≤ s` exactly when
`s < depth_{A_p}(M_p) + height(q/p)` for every `p ∉ T` and `q ∈ T` with
`p ⊆ q`. -/
theorem localCohomologyWithSupportIn_finite_iff_depth_add_dim
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEI1 : FinitenessAnnihilatorCriterionPlus.{u, v} A)
    (hEFC : AnnihilatorDepthCriterion.{u, v, w} A)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℕ) (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    (∀ i : ℤ, i ≤ (s : ℤ) →
      Module.Finite A (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
        (s : ℕ∞) <
          Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) +
          (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height) := by
  refine (localCohomologyWithSupportIn_finite_iff_exists_annihilator.{u, v}
    A hEI1 T hT M s).trans ((hEFC M T T Set.Subset.rfl hT hT (s : ℤ) (by omega)
      omega homega).trans ?_)
  constructor
  · intro h p q hp hq hpq
    exact (depth_add_height_iff_eint s _ _).mpr
      (by simpa [ringKrullDim_localization_quotient_eq_height p q hpq] using h p q hp hq hpq)
  · intro h p q hp hq hpq
    simpa [ringKrullDim_localization_quotient_eq_height p q hpq] using
      (depth_add_height_iff_eint s _ _).mp (h p q hp hq hpq)

private theorem subsingleton_moduleCat_of_subsingleton
    {A : Type u} [CommRing A] [Subsingleton A] (M : ModuleCat.{max u v} A) :
    Subsingleton (M : Type (max u v)) := by
  refine ⟨fun x y => ?_⟩
  have h1 : (1 : A) = 0 := Subsingleton.elim _ _
  have hz : ∀ z : (M : Type (max u v)), z = 0 := fun z => by
    rw [← one_smul A z, h1, zero_smul]
  rw [hz x, hz y]

/-- Tag 0EI1 holds over the zero ring, so `FinitenessAnnihilatorCriterionPlus` is not an empty
assumption. The spectrum is empty, every module is trivial and there is only one ideal, so both
sides of the equivalence hold. -/
theorem finitenessAnnihilatorCriterionPlus_of_subsingleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] [Subsingleton A] :
    FinitenessAnnihilatorCriterionPlus.{u, v} A := by
  intro T _ K _ n
  refine ⟨fun _ => ⟨⊥, fun x _ => (IsEmpty.false x).elim,
    fun i _ => le_of_eq (Subsingleton.elim _ _)⟩, fun _ i _ => ?_⟩
  have := subsingleton_moduleCat_of_subsingleton.{u, v}
    (localCohomologyWithSupportInPlus.{u, v} A T K i)
  infer_instance

/-- Tag 0EFC holds over the zero ring, so `AnnihilatorDepthCriterion` is not an empty
assumption. The depth-dimension clause is quantified over an empty spectrum and the zero ideal
annihilates everything, so both sides of the equivalence hold. -/
theorem annihilatorDepthCriterion_of_subsingleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] [Subsingleton A] :
    AnnihilatorDepthCriterion.{u, v, w} A := by
  intro M _ _ _ T T' _ _ _ s _ omega _
  exact ⟨fun _ p _ _ _ _ => (IsEmpty.false p).elim,
    fun _ => ⟨⊥, fun x _ => (IsEmpty.false x).elim,
      fun i _ => le_of_eq (Subsingleton.elim _ _)⟩⟩


/-- The premises of the depth-dimension clause are simultaneously satisfiable: over a local domain
that is not a field, the closed point is a specialization-closed subset which the generic point
lies outside of and specializes into. So the clause quantified over `p ∉ T`, `q ∈ T`,
`p ⊆ q` in the two criteria above is not a quantification over an empty family. -/
theorem exists_specialization_into_stableUnderSpecialization
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    (hA : maximalIdeal A ≠ ⊥) :
    ∃ (T : Set (PrimeSpectrum A)) (p q : PrimeSpectrum A),
      StableUnderSpecialization T ∧ p ∉ T ∧ q ∈ T ∧ p.asIdeal ≤ q.asIdeal := by
  have hmax : (maximalIdeal A).IsMaximal := maximalIdeal.isMaximal A
  refine ⟨{⟨maximalIdeal A, hmax.isPrime⟩}, ⟨⊥, inferInstance⟩,
    ⟨maximalIdeal A, hmax.isPrime⟩, ?_, ?_, rfl, bot_le⟩
  · intro x y hxy hx
    rw [Set.mem_singleton_iff] at hx ⊢
    subst hx
    exact (PrimeSpectrum.ext (hmax.eq_of_le y.2.1
      ((PrimeSpectrum.le_iff_specializes _ _).2 hxy))).symm
  · rw [Set.mem_singleton_iff]
    intro h
    exact hA (congrArg PrimeSpectrum.asIdeal h).symm

/-! ### Tag 0EHZ, the complex-level annihilator criterion -/

/-- The localization of a bounded-below derived object at a prime, again bounded below.

Extension of scalars along `A → A_p` is flat, hence exact, so it descends to the derived
category and preserves the bound. This is the construction of Tag 0EHZ. -/
noncomputable def localizedComplex
    {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) :
    DerivedCategory.Plus (ModuleCat.{max u v} (Localization.AtPrime p.asIdeal)) := by
  let F := ModuleCat.extendScalars.{u, u, max u v}
    (algebraMap A (Localization.AtPrime p.asIdeal))
  have : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  refine ⟨F.mapDerivedCategory.obj K.1, ?_⟩
  obtain ⟨n, hn⟩ := K.2
  exact ⟨n, (DerivedCategory.isGE_iff _ n).2 fun i hi =>
    (F.map_isZero ((DerivedCategory.isGE_iff K.1 n).1 hn i hi)).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K.1)⟩

/-- **Stacks 0EHZ**, as a predicate on the base ring.

For a bounded-below complex `K` with finite cohomology over a Noetherian ring with a dualizing
complex and nested specialization-closed subsets `T ⊆ T'`, one ideal supported in `T'`
annihilates `H^i_T(K)` for all `i ≤ s` exactly when the depth of the localization `K_p`
plus the dimension of `(A/p)_q` exceeds `s` for every `p ∉ T'` and `q ∈ T` with `p ⊆ q`.

This is the generalization of Tag 0EFC from a module to a complex. It is taken here as a
predicate so that this file does not depend on its proof; it is discharged, with the three
universes collapsed, by `Stacks.LocalCohomology.annihilatorDepthCriterionPlus`. It is the single
remaining input to `AnnihilatorDepthCriterion` below. -/
def AnnihilatorDepthCriterionPlus (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (omega : DerivedCategory (ModuleCat.{w} A)), Dualizing.IsDualizingComplex omega →
    ∀ (T T' : Set (PrimeSpectrum A)), T ⊆ T' →
      StableUnderSpecialization T → StableUnderSpecialization T' →
      ∀ (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)),
        (∀ i : ℤ, Module.Finite A
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) →
        ((∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
            ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
              (localCohomologyWithSupportInPlus.{u, v} A T K i)) ↔
          (∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
            letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
              Ideal.isPrime_map_quotientMk_of_isPrime hpq
            (DerivedCategory.Plus.depth.{u, v} (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (localizedComplex.{u, v} p K) : EInt) +
              Stacks.Algebraization.krullDimToEInt
                (ringKrullDim (Localization.AtPrime
                  (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt)))

/-- A localization of `R` at a prime `p`, divided by the extension of an ideal `J ≤ p`, is the
localization of `R ⧸ J` at the image of `p`. -/
private theorem isLocalizationAtPrimeQuotient
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Sp : Type*) [CommRing Sp] [Algebra R Sp] [IsLocalization.AtPrime Sp p]
    (J : Ideal R) (q : Ideal (R ⧸ J)) [q.IsPrime]
    (hcomap : q.comap (Ideal.Quotient.mk J) = p) :
    IsLocalization.AtPrime (Sp ⧸ J.map (algebraMap R Sp)) q := by
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ J) p.primeCompl = q.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      subst hcomap
      refine fun hmem => hz ?_
      have hzz : Ideal.Quotient.mk J z = Ideal.Quotient.mk J y := by
        simpa [Ideal.Quotient.algebraMap_eq] using hzy
      simpa [Ideal.mem_comap, hzz] using hmem
    · intro hx
      exact ⟨y, by subst hcomap; exact hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (M := p.primeCompl) (S := Sp) J
  rwa [hsub] at h

/-- The two shapes of the local dimension of `A ⧸ p` at `q`: the Krull dimension of the
localization of `A ⧸ p` at the image of `q`, and the Krull dimension of `A_q ⧸ p A_q`. -/
private theorem krullDim_localization_quotient_eq
    {A : Type*} [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) [(q.map (Ideal.Quotient.mk p)).IsPrime] :
    ringKrullDim (Localization.AtPrime (q.map (Ideal.Quotient.mk p))) =
      ringKrullDim ((Localization.AtPrime q) ⧸
        p.map (algebraMap A (Localization.AtPrime q))) := by
  let qbar := q.map (Ideal.Quotient.mk p)
  let S := Localization.AtPrime q
  let J := p.map (algebraMap A S)
  have hcomap : qbar.comap (Ideal.Quotient.mk p) = q := by
    rw [Ideal.comap_map_of_surjective (f := Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective q, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hpq]
  have : IsLocalization.AtPrime (S ⧸ J) qbar :=
    isLocalizationAtPrimeQuotient q S p qbar hcomap
  let e := IsLocalization.algEquiv qbar.primeCompl (Localization.AtPrime qbar) (S ⧸ J)
  simpa [qbar, S, J] using ringKrullDim_eq_of_ringEquiv e.toRingEquiv

section ExtendScalars

open scoped TensorProduct ChangeOfRings

/-- Extension of scalars to a localization agrees with the localized-module functor. -/
private noncomputable def extendScalarsLocalizedIso {R : Type u} [CommRing R]
    (T : Submonoid R) (M : ModuleCat.{max u v} R) :
    (ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization T))).obj M ≅
      (ModuleCat.localizedModuleFunctor.{max u v} T).obj M :=
  Dualizing.extendScalarsTensorIso (Localization T) M ≪≫
    ((IsLocalizedModule.isBaseChange T (Localization T)
      (M.localizedModuleMkLinearMap T)).equiv).toModuleIso

end ExtendScalars

/-- The localization of a module placed in degree zero is the extension of scalars of that
module, placed in degree zero. -/
private noncomputable def localizedComplexSingleIso
    (A : Type u) [CommRing A] (p : PrimeSpectrum A)
    (M : ModuleCat.{max u v} A) :
    localizedComplex.{u, v} p
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor
        (ModuleCat.{max u v} (Localization.AtPrime p.asIdeal)) 0).obj
          ((ModuleCat.extendScalars.{u, u, max u v}
            (algebraMap A (Localization.AtPrime p.asIdeal))).obj M) := by
  let B := Localization.AtPrime p.asIdeal
  let F := ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)
  let K := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  have : F.Additive := (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive
  have : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' (algebraMap A B)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).leftAdjoint_preservesColimits
  have : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  have e : DerivedCategory.Plus.ι.obj (localizedComplex.{u, v} p K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj (F.obj M) := by
    change F.mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj K) ≅ _
    exact (F.mapDerivedCategorySingleFunctor 0).app M
  exact DerivedCategory.Plus.ι.preimageIso e

/-- Local cohomology with support in `T` of a complex in degrees `≥ 0` again sits in degrees
`≥ 0`: it is the right derived functor of sections with support, and a right derived functor
moves cohomology to the right. -/
private theorem isGE_derivedSectionsWithSupportInPlus
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) [K.IsGE 0] :
    ((derivedSectionsWithSupportInPlus.{u, v} A T).obj K).IsGE 0 := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  show ((sectionsWithSupportInFunctor.{u, v} A T).rightDerivedFunctorPlus.obj K).IsGE 0
  exact Functor.isGE_rightDerivedFunctorPlus_obj _ K 0

/-- The derived depth is infinite when the local cohomology vanishes in every degree. -/
private theorem plusDepth_eq_top_of_isZero
    (A : Type u) [CommRing A] (I : Ideal A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (h : ∀ i : ℤ, Limits.IsZero (localCohomologyWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K i)) :
    DerivedCategory.Plus.depth.{u, v} A I K = ⊤ := by
  change sInf ((fun i : ℤ => (i : WithTop ℤ)) ''
    {i : ℤ | ¬ Limits.IsZero (localCohomologyWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K i)}) = ⊤
  rw [Set.eq_empty_of_forall_notMem (s := {i : ℤ | ¬ Limits.IsZero _}) fun i hi => hi (h i)]
  simp

/-- Nontriviality of bounded-below and of unbounded local cohomology of a module placed in
degree zero agree. -/
private theorem nontrivial_localCohomologyPlusSingle_iff
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ) :
    Nontrivial (localCohomologyWithSupportInPlus.{u, v} A T
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) ↔
      Nontrivial (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
  (localCohomologyWithSupportInPlusIso.{u, v} A T M i).toLinearEquiv.toEquiv.nontrivial_congr

/-- **Tag 0EHY against Tag 00LE**, for a finite module placed in degree zero and an ideal that
does not already expand the module: the derived depth of `M[0]` is the module depth of `M`.

Both are the first degree in which local cohomology with support in `V(I)` is nonzero: for the
module depth this is Tag 0AVZ, and the bounded-below and unbounded models agree on
`M[0]`. The infimum is taken over `ℕ` on one side and over `ℤ` on the other, and the two agree
because local cohomology of `M[0]` vanishes in negative degrees. -/
private theorem moduleDepth_eq_plusDepth_single
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (hIM : I • (⊤ : Submodule A M) ≠ ⊤) :
    Stacks.Algebraization.enatToEInt (Module.depth A I M) =
      (DerivedCategory.Plus.depth.{u, v} A I
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) : EInt) := by
  classical
  let lc (i : ℕ) := localCohomologyWithSupportIn.{u, v} A
    (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) (i : ℤ)
  let lcPlus (i : ℤ) := localCohomologyWithSupportInPlus.{u, v} A
    (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i
  let S : Set ℕ∞ := {n | ∃ i : ℕ, n = (i : ℕ∞) ∧ Nontrivial (lc i)}
  have hdepth := depth_eq_sInf_nontrivial_localCohomologyWithSupportIn.{u, v} A I M hIM
  have hGE : ∀ i : ℤ, i < 0 → Limits.IsZero (lcPlus i) := by
    intro i hi
    have hRF := isGE_derivedSectionsWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hi
  have hbridge (i : ℤ) : Nontrivial (lcPlus i) ↔
      Nontrivial (localCohomologyWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
    nontrivial_localCohomologyPlusSingle_iff.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) M i
  have hnat : ∀ i : ℤ, ¬ Limits.IsZero (lcPlus i) → 0 ≤ i :=
    fun i hi => not_lt.mp fun h => hi (hGE i h)
  have hlc : ∀ i : ℤ, ¬ Limits.IsZero (lcPlus i) → Nontrivial (lc i.toNat) := fun i hi =>
    (hbridge (i.toNat : ℤ)).mp (by
      rw [Int.toNat_of_nonneg (hnat i hi)]
      exact not_subsingleton_iff_nontrivial.mp fun hs =>
        hi (ModuleCat.isZero_iff_subsingleton.mpr hs))
  by_cases hS : S.Nonempty
  · obtain ⟨n, hn, hnz⟩ : sInf S ∈ S := csInf_mem hS
    have hdn : Module.depth A I M = (n : ℕ∞) := hdepth.trans hn
    have hplusN : Nontrivial (lcPlus (n : ℤ)) := (hbridge (n : ℤ)).mpr hnz
    have hmemInf : ((n : ℤ) : WithTop ℤ) ∈
        (fun i : ℤ => (i : WithTop ℤ)) '' {i : ℤ | ¬ Limits.IsZero (lcPlus i)} := by
      refine ⟨n, fun hz => ?_, rfl⟩
      exact (not_nontrivial_iff_subsingleton.mpr
        (ModuleCat.isZero_iff_subsingleton.mp hz)) hplusN
    have hDlb : BddBelow
        ((fun i : ℤ => (i : WithTop ℤ)) '' {i : ℤ | ¬ Limits.IsZero (lcPlus i)}) := by
      refine ⟨0, ?_⟩
      rintro z ⟨i, hi, rfl⟩
      exact WithTop.coe_le_coe.mpr (hnat i hi)
    have hupper : DerivedCategory.Plus.depth.{u, v} A I
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) ≤
          ((n : ℤ) : WithTop ℤ) := csInf_le hDlb hmemInf
    have hlower : ((n : ℤ) : WithTop ℤ) ≤ DerivedCategory.Plus.depth.{u, v} A I
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) := by
      refine le_csInf (Set.nonempty_of_mem hmemInf) ?_
      rintro z ⟨i, hi, rfl⟩
      have hle : sInf S ≤ ((i.toNat : ℕ∞)) := sInf_le ⟨i.toNat, rfl, hlc i hi⟩
      rw [hn] at hle
      rw [← Int.toNat_of_nonneg (hnat i hi)]
      exact WithTop.coe_le_coe.mpr (by exact_mod_cast hle)
    have hdep : DerivedCategory.Plus.depth.{u, v} A I
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M) =
          ((n : ℤ) : WithTop ℤ) := le_antisymm hupper hlower
    rw [hdn, hdep]
    rfl
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have htop : Module.depth A I M = ⊤ := by
      rw [show Module.depth A I M = sInf S by simpa [S] using hdepth, hempty]
      simp
    have hdep := plusDepth_eq_top_of_isZero.{u, v} A I
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
      fun i => not_not.mp fun hi => hS ⟨(i.toNat : ℕ∞), i.toNat, rfl, hlc i hi⟩
    rw [htop, hdep]
    rfl

/-- The same comparison over a Noetherian local ring, with no hypothesis on the ideal. If the
maximal ideal does expand `M`, then `M` is zero by Nakayama, and both depths are infinite. -/
private theorem moduleDepth_eq_plusDepth_single_unconditional
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) [Module.Finite R M] :
    Stacks.Algebraization.enatToEInt (Module.depth R (maximalIdeal R) M) =
      (DerivedCategory.Plus.depth.{u, v} R (maximalIdeal R)
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} R) 0).obj M) : EInt) := by
  classical
  by_cases hIM : (maximalIdeal R) • (⊤ : Submodule R M) ≠ ⊤
  · exact moduleDepth_eq_plusDepth_single.{u, v} R (maximalIdeal R) M hIM
  · have hIeq : (maximalIdeal R) • (⊤ : Submodule R M) = ⊤ := not_not.mp hIM
    have htopbot : (⊤ : Submodule R M) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
        Module.Finite.fg_top (by rw [hIeq]) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have hsub : Subsingleton (M : Type (max u v)) := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : (M : Type (max u v)), z = 0 := by
        intro z
        have hz : z ∈ (⊤ : Submodule R M) := Submodule.mem_top
        rw [htopbot] at hz
        simpa using hz
      rw [hx x, hx y]
    let K := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} R) 0).obj M
    have hK : Limits.IsZero K :=
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} R) 0).map_isZero
        (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hLC (i : ℤ) : Limits.IsZero (localCohomologyWithSupportInPlus.{u, v} R
        (PrimeSpectrum.zeroLocus ((maximalIdeal R) : Set R)) K i) := by
      let F := sectionsWithSupportInFunctor.{u, v} R
        (PrimeSpectrum.zeroLocus ((maximalIdeal R) : Set R))
      have : EnoughInjectives (ModuleCat.{max u v} R) := ModuleCat.enoughInjectives R
      exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} R) i).map_isZero
        (F.rightDerivedFunctorPlus.map_isZero hK)
    have hdep := plusDepth_eq_top_of_isZero.{u, v} R (maximalIdeal R) K hLC
    have hmod : Module.depth R (maximalIdeal R) M = ⊤ := by
      simp [Module.depth, hIeq]
    rw [hmod, hdep]
    rfl

/-- The derived depth only depends on the isomorphism class of the complex. -/
private theorem plusDepth_eq_of_iso
    (A : Type u) [CommRing A] (I : Ideal A)
    (K L : DerivedCategory.Plus (ModuleCat.{max u v} A)) (e : K ≅ L) :
    DerivedCategory.Plus.depth.{u, v} A I K = DerivedCategory.Plus.depth.{u, v} A I L := by
  have he (j : ℤ) : localCohomologyWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) K j ≅
    localCohomologyWithSupportInPlus.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A)) L j :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) j).mapIso
      ((derivedSectionsWithSupportInPlus.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).mapIso e)
  have hset : {i : ℤ | ¬ Limits.IsZero (localCohomologyWithSupportInPlus.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A)) K i)} =
      {i : ℤ | ¬ Limits.IsZero (localCohomologyWithSupportInPlus.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A)) L i)} := by
    ext j
    exact ⟨fun hj hz => hj (hz.of_iso (he j)), fun hj hz => hj (hz.of_iso (he j).symm)⟩
  exact congrArg sInf (congrArg (Set.image (fun i : ℤ => (i : WithTop ℤ))) hset)

/-- **The depth bridge of Tag 0EFC.** The module depth of the localization `M_p`, as it appears
in Tag 0EFC, is the derived depth of the localization of `M[0]` at `p`, as it appears in
Tag 0EHZ. -/
private theorem localizedDepthBridge
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    Stacks.Algebraization.enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) =
      (DerivedCategory.Plus.depth.{u, v} (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (localizedComplex.{u, v} p
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) : EInt) := by
  let B := Localization.AtPrime p.asIdeal
  let T := p.asIdeal.primeCompl
  let F := ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)
  let eM : (F.obj M : Type (max u v)) ≃ₗ[B] LocalizedModule T M :=
    (extendScalarsLocalizedIso.{u, v} T M).toLinearEquiv.trans
      (Shrink.linearEquiv.{max u v} B _)
  have hF : Module.Finite B (F.obj M) := Module.Finite.equiv eM.symm
  let Kloc := localizedComplex.{u, v} p
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
  let Kl : DerivedCategory.Plus (ModuleCat.{max u v} B) :=
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} B) 0).obj (F.obj M)
  calc
    Stacks.Algebraization.enatToEInt
          (Module.depth B (maximalIdeal B) (LocalizedModule T M)) =
        Stacks.Algebraization.enatToEInt (Module.depth B (maximalIdeal B) (F.obj M)) :=
      congrArg Stacks.Algebraization.enatToEInt
        (Module.depth_eq_depth_of_linearEquiv (maximalIdeal B) eM).symm
    _ = (DerivedCategory.Plus.depth.{u, v} B (maximalIdeal B) Kl : EInt) :=
      moduleDepth_eq_plusDepth_single_unconditional.{u, v} B (F.obj M)
    _ = (DerivedCategory.Plus.depth.{u, v} B (maximalIdeal B) Kloc : EInt) :=
      congrArg (fun z : WithTop ℤ => (z : EInt))
        (plusDepth_eq_of_iso.{u, v} B (maximalIdeal B) Kl Kloc
          (localizedComplexSingleIso.{u, v} A p M).symm)

/-- **Stacks 0EFC, Faltings' annihilator theorem, from Tag 0EHZ.**

The module-level criterion `AnnihilatorDepthCriterion` is the complex-level criterion
`AnnihilatorDepthCriterionPlus` applied to the module placed in degree zero. Three
identifications turn one into the other:

* the bounded-below and the unbounded local cohomology of `M[0]` agree, so the annihilator
  conditions agree (`localCohomologyWithSupportInPlusIso`);
* the derived depth of the localization of `M[0]` at `p` is the module depth of `M_p`
  (`localizedDepthBridge`, which rests on Tag 0AVZ);
* the Krull dimension of the localization of `A ⧸ p` at the image of `q` is the Krull
  dimension of `A_q ⧸ p A_q` (`krullDim_localization_quotient_eq`). -/
theorem annihilatorDepthCriterion_of_annihilatorDepthCriterionPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEHZ : AnnihilatorDepthCriterionPlus.{u, v, w} A) :
    AnnihilatorDepthCriterion.{u, v, w} A := by
  classical
  intro M _ _ _ T T' hTT' hT hT' s _hs omega homega
  have hcrit := hEHZ omega homega T T' hTT' hT hT' s
    ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A M))
    (finite_homology_singleFunctor.{u, v} A (ModuleCat.of A M))
  refine (exists_annihilator_plus_iff.{u, v} A T T' _ s).symm.trans (hcrit.trans ?_)
  constructor
  all_goals
    intro h p q hp hq hpq
    have : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    simpa only [localizedDepthBridge.{u, v} A p (ModuleCat.of A M),
      krullDim_localization_quotient_eq p.asIdeal q.asIdeal hpq] using h p q hp hq hpq

/-- **Stacks 0EFD, Faltings' finiteness criterion**, now conditional on Tag 0EI1 and Tag 0EHZ
only: the module-level Tag 0EFC has been discharged. -/
theorem localCohomologyWithSupportIn_finite_iff_depth_add_dim_of_criterionPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEI1 : FinitenessAnnihilatorCriterionPlus.{u, v} A)
    (hEHZ : AnnihilatorDepthCriterionPlus.{u, v, w} A)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℕ) (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    (∀ i : ℤ, i ≤ (s : ℤ) →
      Module.Finite A (localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
        (s : ℕ∞) <
          Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) +
          (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height) :=
  localCohomologyWithSupportIn_finite_iff_depth_add_dim.{u, v, w} A hEI1
    (annihilatorDepthCriterion_of_annihilatorDepthCriterionPlus.{u, v, w} A hEHZ)
    omega homega T hT s M

/-- Tag 0EHZ holds over the zero ring, so `AnnihilatorDepthCriterionPlus` is not a contradictory
assumption. The spectrum is empty, so the depth-dimension clause is vacuous and the zero ideal
annihilates everything. -/
theorem annihilatorDepthCriterionPlus_of_subsingleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] [Subsingleton A] :
    AnnihilatorDepthCriterionPlus.{u, v, w} A := by
  intro omega _ T T' _ _ _ s K _
  exact ⟨fun _ p _ _ _ _ => (IsEmpty.false p).elim,
    fun _ => ⟨⊥, fun x _ => (IsEmpty.false x).elim,
      fun i _ => le_of_eq (Subsingleton.elim _ _)⟩⟩

/-- Both sides of the criterion of Tag 0EHZ hold over an arbitrary — in particular a nontrivial —
Noetherian ring once `T' = Spec(A)`: no prime lies outside `T'`, so the depth-dimension clause is
vacuous, and the zero ideal has zero locus inside `T'` and lies below every annihilator. So the
assumption is inhabited at rings other than the zero ring as well. -/
theorem annihilatorDepthCriterionPlus_univ
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (s : ℤ)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ Set.univ ∧
        ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
          (localCohomologyWithSupportInPlus.{u, v} A T K i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ (Set.univ : Set (PrimeSpectrum A)) → q ∈ T →
        (hpq : p.asIdeal ≤ q.asIdeal) →
          letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
            Ideal.isPrime_map_quotientMk_of_isPrime hpq
          (DerivedCategory.Plus.depth.{u, v} (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (localizedComplex.{u, v} p K) : EInt) +
            Stacks.Algebraization.krullDimToEInt
              (ringKrullDim (Localization.AtPrime
                (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt)) :=
  ⟨fun _ _ _ hp => absurd (Set.mem_univ _) hp,
    fun _ => ⟨⊥, fun _ _ => Set.mem_univ _, fun _ _ => bot_le⟩⟩

/-- The ambient hypotheses of Faltings' criterion are jointly satisfiable at a **nontrivial**
ring, with a nonempty support: a field has a dualizing complex, the whole spectrum is stable
under specialization and nonempty, and the field is a finite module over itself. So the criterion
above is not conditional on an unexhibited structure in the sense that nothing in the library
builds a dualizing complex. -/
theorem exists_isDualizingComplex_and_stableUnderSpecialization (k : Type u) [Field k] :
    ∃ (omega : DerivedCategory (ModuleCat.{u} k)) (T : Set (PrimeSpectrum k)),
      Dualizing.IsDualizingComplex omega ∧ StableUnderSpecialization T ∧ T.Nonempty := by
  obtain ⟨omega, homega⟩ := Dualizing.exists_isDualizingComplex k
  exact ⟨omega, Set.univ, homega, fun _ _ _ _ => Set.mem_univ _,
    ⟨⟨⊥, inferInstance⟩, Set.mem_univ _⟩⟩

/-- The depth-dimension clause of Tags 0EFC and 0EHZ is a genuine constraint, not a tautology
produced by the coercions into the extended integers: if the depth is a natural number `d` and
the local dimension is a natural number `n`, the clause **fails** at the degree `s = d + n`.

Together with `depth_add_dim_gt_of_lt` below this pins the clause down: it holds exactly below
`d + n`, so neither side of the criteria above is automatically true. -/
theorem not_depth_add_dim_gt_of_eq_natCast (d n : ℕ) :
    ¬ (Stacks.Algebraization.enatToEInt (d : ℕ∞) +
        Stacks.Algebraization.krullDimToEInt ((n : ℕ∞) : WithBot ℕ∞) >
      (((d + n : ℕ) : ℤ) : EInt)) := by
  refine fun h => ?_
  have hlt := (depth_add_height_iff_eint (d + n) (d : ℕ∞) (n : ℕ∞)).mpr h
  rw [show ((d : ℕ∞) + (n : ℕ∞)) = (((d + n : ℕ) : ℕ∞)) by push_cast; rfl] at hlt
  exact lt_irrefl _ hlt

/-- The depth-dimension clause does hold below `d + n`, so it is not automatically false
either. -/
theorem depth_add_dim_gt_of_lt (d n s : ℕ) (hs : s < d + n) :
    Stacks.Algebraization.enatToEInt (d : ℕ∞) +
        Stacks.Algebraization.krullDimToEInt ((n : ℕ∞) : WithBot ℕ∞) > ((s : ℤ) : EInt) :=
  (depth_add_height_iff_eint s (d : ℕ∞) (n : ℕ∞)).mp (by exact_mod_cast hs)

end Stacks.LocalCohomology

end
