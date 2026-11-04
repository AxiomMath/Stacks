module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEIsoOfCohomologyIsomorphisms
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedBelowApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CanonicalTruncation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.OpcyclesFiniteFreeSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.OpcyclesFinitePresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RestrictionOfOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.LocalApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness from Tor amplitude and pseudo-coherence

Tag 08CP says that an object `E` of `D(O_X)` on a ringed space with Tor amplitude in `[a, b]`
which is in addition `(a-1)`-pseudo-coherent is perfect. This file proves it.

## Main results

* `Stacks.Cohomology.PerfectFromTorAmplitude.isFlat_opcycles_of_isZero_X`: the flatness of the
  degree-`a` opcycles of a complex concentrated in `[a-1, b]`, with the two concentration
  conditions given as the vanishing of terms rather than as instances.
* `Stacks.Cohomology.PerfectFromTorAmplitude.exists_isDirectSummandOfFiniteFree_opcycles`: near
  every point, the degree-`a` opcycles of the restricted approximation is a direct summand of a
  finite free module.
* `Stacks.Cohomology.PerfectFromTorAmplitude.isPerfect_of_hasTorAmplitude_of_isPseudoCoherentFrom`:
  **Tag 08CP.**

## Implementation notes

**The route.** `AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_boundedAbove`
turns the `(a-1)`-pseudo-coherence, together with the vanishing of the cohomology of `E` above
`b` that Tor amplitude supplies, into a representative `C` of `E` with local strictly perfect
approximations `α : P ⟶ C|_U` having no terms above degree `b`. Replacing `P` by its brutal
truncation `σ^{≥a-1}P` makes it concentrated in `[a-1, b]` without losing either strict
perfection (`StrictlyPerfect.isStrictlyPerfect_stupidTrunc`) or the approximation property above
`a - 1` (`StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE`). Tor amplitude restricts
to the open subspace (`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules`) and
`CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap` identifies `τ^{≥a}σ^{≥a-1}P` with
`E|_U` in the derived category, so the Tor-amplitude hypothesis reaches the canonical truncation
and `Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_opcycles_of_hasTorAmplitude_truncGE`
applies: the lowest term of that truncation, the opcycles `Coker(P^{a-1} ⟶ P^a)`, is flat. It is
of finite presentation
(`Stacks.Cohomology.OpcyclesFinitePresentation.isFinitePresentation_opcycles`), so Stacks 08BL, in
the shape `exists_isDirectSummandOfFiniteFree_restrict_of_isFlat` of the namespace
`Stacks.Cohomology.OpcyclesFiniteFreeSummand`, makes it a direct summand of a finite free module
after one more shrinking. Read through
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictOpcyclesIso` that is exactly the hypothesis
of `Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_approximation_of_opcycles`,
which carries the covering bookkeeping and concludes.

**One restatement, and why it is needed.** The category of `O_X`-modules has two spellings,
`StrictlyPerfect.OXMod X` and `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`, the
second being the one the derived tensor product -- hence Tor amplitude, hence
`isFlat_opcycles_of_hasTorAmplitude_truncGE` -- is stated at. They are equal by `rfl`, but an
instance proved at one does not fire at the other, so the `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE` *instance* arguments of that lemma cannot be discharged by
hypotheses established at the `OXMod` spelling, where the brutal truncation is built.
`isFlat_opcycles_of_isZero_X` below is that lemma with those two instance arguments turned into
ordinary hypotheses about the vanishing of terms; inside it the instances are rebuilt in the one
context that demands them. This is the same device as
`Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X`
on the ringed-site side.

**Universes.** The space, its structure sheaf and its modules all coincide, as they already must
for `StrictlyPerfect.OXMod` and for `Stacks.Cohomology.TorAmplitude.derTensor`. The derived
category's hom universe `d` is shared between `X` and its open subspaces rather than kept
independent, because `hasTorAmplitude_restrictModules` -- which compares Tor amplitude on `X`
with Tor amplitude on `X|_U` -- is stated that way; nothing below narrows the mathematics.

## References

* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.PerfectFromTorAmplitude

universe u d

variable {X : RingedSpace.{u, u}}

section FlatOpcyclesRestated

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **The degree-`a` opcycles of a bounded complex of flat `O_X`-modules concentrated in degrees
`≥ a - 1` are flat as soon as its canonical truncation at `a` has Tor amplitude in `[a, b]`**,
with the two concentration conditions given as the vanishing of terms rather than as instances of
`CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`.

This is
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_opcycles_of_hasTorAmplitude_truncGE` at
`n = a - 1`; see the implementation notes of this file for why the two instance arguments have to
be moved out of the instance context. -/
theorem isFlat_opcycles_of_isZero_X (P : CochainComplex (Modules X) ℤ) (a b : ℤ)
    (hGE : ∀ i : ℤ, i < a - 1 → IsZero (P.X i)) (hLE : ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (P.X i))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj (P.truncGE a)) a b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (HomologicalComplex.opcycles P a) := by
  have hge : CochainComplex.IsStrictlyGE P (a - 1) :=
    (CochainComplex.isStrictlyGE_iff P (a - 1)).2 hGE
  have hle : CochainComplex.IsStrictlyLE P b := (CochainComplex.isStrictlyLE_iff P b).2 hLE
  have e : a - 1 + 1 = a := by omega
  have h := Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_opcycles_of_hasTorAmplitude_truncGE
    P (a - 1) b hflat (by rwa [e])
  rwa [e] at h

end FlatOpcyclesRestated

section Main

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

-- Restriction to an open is exact (Stacks 08C9), at both spellings of the restriction functor:
-- the `PseudoCoherence` one, which the truncation criterion is stated at, and the
-- `AlgebraicGeometry.RingedSpace` one, which the bounded approximation is stated at. Neither is
-- an instance where it is proved, so both are seated here.
attribute [local instance]
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteColimits
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits
  AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
  AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits

omit [HasDerivedCategory (OXMod X)] in
open Stacks.Cohomology.OpcyclesFiniteFreeSummand
  AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- **Near every point the degree-`a` opcycles of the restricted approximation is a direct
summand of a finite free module.**

Let `Q` be a strictly perfect complex on `X|_U` concentrated in degrees `[a - 1, b]` whose
canonical truncation at `a` represents the restriction of `E` to `X|_U`. Its degree-`a` opcycles
is flat, by `isFlat_opcycles_of_isZero_X` fed with the restricted Tor amplitude, and of finite
presentation, because every term of a strictly perfect complex is; so Stacks 08BL makes it a
direct summand of a finite free module on some neighbourhood `V` of any given point, and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictOpcyclesIso` reads that as a statement
about the degree-`a` opcycles of the restricted complex. -/
theorem exists_isDirectSummandOfFiniteFree_opcycles (U : Opens X.carrier)
    (Q : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hQ : IsStrictlyPerfect Q) (a b : ℤ)
    (hGE : ∀ i : ℤ, i < a - 1 → IsZero (Q.X i)) (hLE : ∀ i : ℤ, b < i → IsZero (Q.X i))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude (X.restrict U.isOpenEmbedding)
      (DerivedCategory.Q.obj (Q.truncGE a)) a b)
    (y : (X.restrict U.isOpenEmbedding).carrier) :
    ∃ V : Opens (X.restrict U.isOpenEmbedding).carrier, y ∈ V ∧
      IsDirectSummandOfFiniteFree
        (HomologicalComplex.opcycles (restrictComplex Q V) a) := by
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (X.restrict U.isOpenEmbedding).sheaf) (Q.X i) := fun i =>
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree
      _ (hQ.directSummand i)
  have hop := isFlat_opcycles_of_isZero_X Q a b hGE hLE hflat hamp
  have hfp : (HomologicalComplex.opcycles Q a).IsFinitePresentation :=
    Stacks.Cohomology.OpcyclesFinitePresentation.isFinitePresentation_opcycles hQ a
  obtain ⟨V, hyV, hsum⟩ :=
    exists_isDirectSummandOfFiniteFree_restrict_of_isFlat
      (HomologicalComplex.opcycles Q a) hop y
  exact ⟨V, hyV, isDirectSummandOfFiniteFree_opcycles_restrictComplex Q V a hsum⟩

open AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- **Tag 08CP.** An object of `D(O_X)` on a ringed space with Tor amplitude in `[a, b]`, for
integers `a ≤ b`, which is `(a - 1)`-pseudo-coherent, is perfect.

The pseudo-coherence supplies a representative `C` and, near every point, a strictly perfect
approximation of `C|_U` in degrees above `a - 1` with no terms above `b`; its brutal truncation
`σ^{≥a-1}P` is concentrated in `[a-1, b]` and still approximates above `a - 1`, and the
Tor-amplitude hypothesis makes the degree-`a` opcycles of that truncation flat, hence locally a
direct summand of a finite free module. That is what the truncation criterion consumes. -/
@[stacks 08CP, sga "6 I 5.8" "(ii) ⟹ (i)"]
theorem isPerfect_of_hasTorAmplitude_of_isPseudoCoherentFrom
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) (hab : a ≤ b)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b)
    (hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom E (a - 1)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect E := by
  have hout : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) := fun i hi =>
    Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isZero_homology_of_hasTorAmplitude
      E a b hamp i (by simp only [Set.mem_Icc]; omega)
  have hlow : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) := fun i hi =>
    hout i (.inl hi)
  obtain ⟨C, ⟨eC⟩, hloc⟩ :=
    AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_boundedAbove E (a - 1) b
      (by omega) hpc fun i hi => hout i (.inr hi)
  -- The cohomology of the representative, and of its restrictions, vanishes below `a`.
  have hCzero : ∀ i : ℤ, i < a → IsZero (C.homology i) := fun i hi =>
    (hlow i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) i).app C).symm.trans
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso eC))
  refine Stacks.Cohomology.PerfectCanonicalTruncation.isPerfect_of_local_approximation_of_opcycles
    E a hlow C eC fun x => ?_
  obtain ⟨U, hxU, P, hP, hPzero, α, hαiso, hαepi⟩ := hloc x
  -- Cut `P` down to degrees `≥ a - 1`; it stays strictly perfect and still approximates above
  -- `a - 1`, because the inclusion of a brutal truncation is invertible on cohomology there.
  have hPgsp : IsStrictlyPerfect (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) :=
    isStrictlyPerfect_stupidTrunc _ hP _
  have hPgGE : ∀ i : ℤ, i < a - 1 →
      IsZero ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).X i) := fun i hi =>
    CochainComplex.isZero_of_isStrictlyGE
      (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) i hi
  have hPgLE : ∀ i : ℤ, b < i →
      IsZero ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).X i) := fun i hi =>
    IsZero.of_iso (hPzero i hi)
      (P.stupidTruncXIso (ComplexShape.embeddingUpIntGE (a - 1))
        (i := (i - (a - 1)).toNat) (by change a - 1 + ((i - (a - 1)).toNat : ℤ) = i; omega))
  have hαg : ∀ j : ℤ, a - 1 < j → IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex.ιStupidTrunc P
        (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) j) := by
    intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have h1 := StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE P (a - 1) j hj
    have h2 := hαiso j hj
    infer_instance
  refine ⟨U, hxU, P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)), hPgsp,
    ⟨HomologicalComplex.ιStupidTrunc P
      (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α, hαg⟩, fun y => ?_⟩
  -- `τ^{≥a}σ^{≥a-1}P` represents `E|_U`, so it carries the restricted Tor amplitude.
  have hCU : (DerivedCategory.Q.obj
      (AlgebraicGeometry.RingedSpace.restrictComplex C U)).IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact IsZero.of_iso
      ((AlgebraicGeometry.RingedSpace.restrictModules X U).map_isZero (hCzero i hi))
      (((DerivedCategory.homologyFunctorFactors (OXMod.{u, u}
          (X.restrict U.isOpenEmbedding)) i).app
        (AlgebraicGeometry.RingedSpace.restrictComplex C U)).trans
        ((C.sc i).mapHomologyIso (AlgebraicGeometry.RingedSpace.restrictModules X U)))
  obtain ⟨etr⟩ := CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap a
    (HomologicalComplex.ιStupidTrunc P
      (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) (fun i hi => hαg i (by omega))
  have eCU : DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.restrictComplex C U) ≅
      (restrictModules.{u, u} X U).mapDerivedCategory.obj E :=
    ((restrictModules.{u, u} X U).mapDerivedCategoryFactors.app C).symm ≪≫
      (restrictModules.{u, u} X U).mapDerivedCategory.mapIso eC
  have hampU := Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules U E a b hab hamp
  exact exists_isDirectSummandOfFiniteFree_opcycles U
    (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) hPgsp a b hPgGE hPgLE
    (Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso hampU
      (etr ≪≫ eCU)) y

end Main

end Stacks.Cohomology.PerfectFromTorAmplitude

end
