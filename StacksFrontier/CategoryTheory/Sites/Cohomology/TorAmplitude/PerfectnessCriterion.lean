module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.BrutalTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.OpcyclesFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.RestrictionOfOpcycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessFromTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-! # The perfectness criterion of Stacks 08G7

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct` (Stacks 06YU). Stacks 08G7 says that an object of
`D(O)` with Tor amplitude in `[a, b]` which is in addition `(a - 1)`-pseudo-coherent is perfect.
This file states that criterion as a proposition and proves it.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.TorAmplitudePerfectnessCriterion`: the statement
  of Stacks 08G7, as a proposition.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion`: **Stacks
  08G7.**
* `Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X`
  and
  `exists_coveringSieve_isDirectSummandOfFiniteFree_overMap_of_isFinitePresentation` in the same
  namespace: two results of the development restated with a hypothesis moved out of the
  instance arguments; see the implementation notes.

## Implementation notes

**The route.** Perfectness is checked by producing a strictly perfect model above each member of
a covering of each object — Stacks 08G6 (1), in the form
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect`. The
`(a-1)`-pseudo-coherence together with the vanishing of the cohomology of `E` above `b` —
which is the Tor-amplitude hypothesis read through
`Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude` — gives, on a covering,
strictly perfect approximations `α : P ⟶ E|_V` with no terms above degree `b` and invertible on
cohomology above `a - 1`
(`AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove`).
Replacing `P` by its brutal truncation `σ^{≥a-1}P` makes it concentrated in `[a-1, b]` without
losing either strict perfection (`Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc`) or the
approximation property above `a - 1`
(`StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE`). Tor amplitude restricts to the
slice (`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction`), so
`Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles` applies: the
canonical truncation `τ^{≥a}σ^{≥a-1}P` represents `E|_V` and its lowest term, the opcycles
`Coker(P^{a-1} ⟶ P^a)`, is flat. That term is of finite presentation
(`Stacks.SheafOfModules.isFinitePresentation_opcycles`, through Stacks 0H98), so Stacks 08FD —
read on the slice and through restriction along an arrow of the base by
`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_overMap` — makes it a
direct summand of a finite free module after one more refinement of the covering. On a member
`W ⟶ V` of that refinement the restricted truncation is therefore strictly perfect
(`SheafOfModules.isStrictlyPerfect_truncGE`, fed by
`Stacks.SheafOfModules.restrictOpcyclesAlongIso`) and still represents `E|_W`. The two layers of
coverings are composed by `CategoryTheory.Sieve.bind`, the refinement produced on the slice being
carried back to the base by `CategoryTheory.Sieve.overEquiv` and
`CategoryTheory.GrothendieckTopology.mem_over_iff`.

**Two restatements, and why they are needed.** The same sheaf of modules on a slice has two
spellings — `X.ringSheaf.over V` and `(X.over V).ringSheaf`, equivalently
`Stacks.commRingSheafToRingSheaf (X.O.over V)` — which are definitionally equal but are reached
by different instance paths. A term elaborated at one spelling and a class applied at the other
therefore do not unify at the transparency typeclass synthesis uses, even though they do at the
transparency an ordinary argument is checked with. Both results below are the existing result
with the offending *instance* argument — `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE` in one case, `SheafOfModules.IsFinitePresentation` in the other —
turned into an ordinary hypothesis, which is all it takes: inside the restatement the instance is
rebuilt in the one context where it is demanded.

**The derived tensor product on the slices.** The proof needs Tor amplitude on each slice, and
Tor amplitude on a slice is measured against a derived tensor product datum *on that slice*; no
datum on `C` measures anything on `C/V`. That datum does not occur in the statement, so it is
not a parameter: it is the derived tensor product of Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which exists on each slice under the
hypotheses the statement already carries. The datum `T` on `C` itself does occur — Tor amplitude
is measured against it — and stays, so the criterion is proved for every derived tensor product
and not only for the canonical one.

**Universes.** The sections of the structure sheaf and of the modules live in `Type`. That is
forced, not chosen: perfectness `AlgebraicGeometry.RingedSite.IsPerfect` and pseudo-coherence
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` are both built on `IsStrictlyPerfect`
(Stacks 08FL), which is monomorphic there, and the whole of the perfectness development is
stated at those universes for the same reason.

The two site universes are *expressible* freely, as the statement below shows, but they are not
free for a **proof**: every route to Stacks 08G7 passes through Stacks 08G1 in the direction
that produces a bounded flat representative
(`Stacks.SheafOfModules.DerivedTensorProduct.exists_flatRepresentative_of_hasTorAmplitude`) and
through the flatness of a direct summand of a finite free module
(`Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree`), and both are available only
when the sections of the structure sheaf live in `max u v`, that being where the unit law for
the tensor product of `O`-modules is. Together with the pin to `Type` above this forces
`max u v = 0`, that is `RingedSite.{0, 0, 0}`; and since the objects of a slice of a
`RingedSite.{u, v, w}` live in `max u v`, the local statements the proof passes through force
the same. Tor-dimension statements that do have the two site universes free are the ones
measured against a given derived tensor product datum and nothing else, such as
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`.

## References

* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v d

namespace Stacks.SheafOfModules.DerivedTensorProduct

section Statement

variable {X : RingedSite.{u, v, 0}}
  [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, 0} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, 0, 0, 0} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, 0, 0, 0} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, 0} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The statement of **Stacks 08G7** for the derived tensor product `T`: an object of `D(O)`
with Tor amplitude in `[a, b]`, for integers `a ≤ b`, which is `(a - 1)`-pseudo-coherent, is
perfect.

It is proved below, as `torAmplitudePerfectnessCriterion`; it is recorded as a proposition
because the proof needs the two site universes pinned, while the statement does not. -/
def TorAmplitudePerfectnessCriterion
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (T : DerivedTensorProduct.{u, v, 0, d} X) : Prop :=
  ∀ (E : RingedSite.DerivedModules.{u, v, 0, d} X) (a b : ℤ), a ≤ b →
    HasTorAmplitude T E a b → X.IsPseudoCoherentFrom E (a - 1) → X.IsPerfect E

end Statement

section Proof

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{0, 0, 0}}
  [HasSheafify Z.J AddCommGrpCat.{0}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{0}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Z.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ)]
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

variable
  [∀ U : Z.C, (Z.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})]
  [∀ U : Z.C, (Z.J.over U).HasSheafCompose (forget₂ RingCat.{0} AddCommGrpCat.{0})]
  [∀ (U : Z.C) (W : Over U), HasWeakSheafify ((Z.J.over U).over W) AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).HasSheafCompose (forget₂ RingCat.{0} AddCommGrpCat.{0})]

/-- **Stacks 08FD on a slice, read through `SheafOfModules.overMap`, with the
finite-presentation hypothesis given explicitly** rather than as an instance.

`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_overMap` asks for
`SheafOfModules.IsFinitePresentation` as an instance, and typeclass synthesis does not cross
between the two spellings of the structure sheaf of a slice; see the implementation notes of
this file. -/
theorem exists_coveringSieve_isDirectSummandOfFiniteFree_overMap_of_isFinitePresentation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ T : C, HasSheafify (J.over T) AddCommGrpCat.{max u v}]
    [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ T : C, (J.over T).HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [∀ T : C, (J.over T).HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
    (U : C)
    [∀ T : Over U, HasWeakSheafify ((J.over U).over T) AddCommGrpCat.{max u v}]
    [∀ T : Over U, ((J.over U).over T).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ T : Over U, ((J.over U).over T).HasSheafCompose
      (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
    (O : Sheaf J CommRingCat.{max u v})
    (F : _root_.SheafOfModules.{max u v} (commRingSheafToRingSheaf (O.over U)))
    (hfp : F.IsFinitePresentation) (hF : Stacks.SheafOfModules.IsFlat (O := O.over U) F)
    (W₀ : Over U) :
    ∃ S : Sieve W₀, S ∈ (J.over U) W₀ ∧ ∀ {W : Over U} (g : W ⟶ W₀), S g →
      IsDirectSummandOfFiniteFree ((commRingSheafToRingSheaf O).over W.left)
        ((_root_.SheafOfModules.overMap.{max u v}
          (commRingSheafToRingSheaf O) W.hom).obj F) :=
  have := hfp
  exists_coveringSieve_isDirectSummandOfFiniteFree_overMap U O F hF W₀

/-- **The local core of Stacks 08G7, with the two concentration hypotheses on `P` given as the
vanishing of its terms** rather than as instances of `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE`.

This is `Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles`;
typeclass synthesis does not cross between the two spellings of the structure sheaf of a slice,
so the two instance arguments are moved out of the instance context. See the implementation
notes of this file. -/
theorem exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X
    {Y : RingedSite.{0, 0, 0}} [HasSheafify Y.J AddCommGrpCat.{0}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} Y)]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.O).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} Y) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct.{0, 0, 0, d} Y)
    (E : RingedSite.DerivedModules.{0, 0, 0, d} Y) (n b : ℤ)
    (Ecpx : CochainComplex (RingedSite.Modules.{0, 0, 0} Y) ℤ)
    (eE : DerivedCategory.Q.obj Ecpx ≅ E)
    (P : CochainComplex (RingedSite.Modules.{0, 0, 0} Y) ℤ)
    (hGE : ∀ i : ℤ, i < n → IsZero (P.X i)) (hLE : ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0} (O := Y.O) (P.X i))
    (α : P ⟶ Ecpx)
    (hα : ∀ i : ℤ, n + 1 ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hamp : HasTorAmplitude T E (n + 1) b) :
    Nonempty (DerivedCategory.Q.obj (P.truncGE (n + 1)) ≅ E) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0} (O := Y.O) (P.opcycles (n + 1)) := by
  have hge : CochainComplex.IsStrictlyGE P n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hGE i hi
  have hle : CochainComplex.IsStrictlyLE P b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hLE i hi
  exact exists_iso_truncGE_and_isFlat_opcycles T E n b Ecpx eE P hflat α hα hamp

/-- Restriction along an arrow of the site preserves finite limits, by Stacks 04IX. -/
local instance critPreservesFiniteLimitsOverMap {U V : Z.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits, by Stacks 04IX. -/
local instance critPreservesFiniteColimitsOverMap {U V : Z.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (_root_.SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- **Stacks 08G7.** Let `(C, O)` be a ringed site and let `T` be a derived tensor product on
`D(O)`. An object of `D(O)` with Tor amplitude in `[a, b]` for `T`, with `a ≤ b`, which is
`(a - 1)`-pseudo-coherent, is perfect.

The proof reads Tor amplitude on each slice `(C/U, O|_U)`, which needs a derived tensor product
there; that is the derived tensor product of Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which exists on each slice under the
hypotheses already in force, so it is not a parameter of the statement. -/
@[stacks 08G7, sga "6 I 5.8" "(ii) ⟹ (i)"]
theorem torAmplitudePerfectnessCriterion
    (T : DerivedTensorProduct.{0, 0, 0, d} Z) :
    TorAmplitudePerfectnessCriterion T := by
  classical
  let T' : ∀ U : Z.C, DerivedTensorProduct.{0, 0, 0, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{0, 0, d} (Z.over U)
  intro E a b hab hamp hpc
  have hzero : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{0, 0, 0} Z) i).obj E) :=
    (DerivedCategory.isLE_iff E b).1 (isLE_of_hasTorAmplitude T E hamp)
  obtain ⟨Ecpx, ⟨eE⟩, hloc⟩ :=
    RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove Z E (a - 1) b
      (by omega) hpc hzero
  -- The comparison of the derived restriction of `E` with the restriction of `Ecpx`.
  have hrepr : ∀ V : Z.C, DerivedCategory.Q.obj (Z.restrictComplex Ecpx V) ≅
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        V).mapDerivedCategoryFactors.app Ecpx).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
        V).mapDerivedCategory.mapIso eE
  -- Tor amplitude of the derived restriction of `E`, in the shape the local core consumes.
  have hampS : ∀ V : Z.C, HasTorAmplitude (T' V)
      ((RingedSite.derivedRestriction.{0, 0, 0, d} Z V).obj E) (a - 1 + 1) b := fun V => by
    rw [show a - 1 + 1 = a from by omega]
    exact hasTorAmplitude_derivedRestriction T V (T' V) E a b hab hamp
  refine RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect Z E (fun U => ?_)
  obtain ⟨S₀, hS₀, hprop⟩ := hloc U
  have key : ∀ (V : Z.C) (f : V ⟶ U), S₀ f → ∃ Sv : Sieve V, Sv ∈ Z.J V ∧
      ∀ ⦃W : Z.C⦄ (k : W ⟶ V), Sv k →
        ∃ Q : CochainComplex
            (_root_.SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W) Q ∧
          Nonempty (DerivedCategory.Q.obj Q ≅
            (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
              W).mapDerivedCategory.obj E) := by
    intro V f hf
    obtain ⟨P, hP, hPzero, α, hαiso, hαepi⟩ := hprop f hf
    have hPLE : CochainComplex.IsStrictlyLE P b := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => hPzero i hi
    have hPgGE : CochainComplex.IsStrictlyGE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) := inferInstance
    have hPgLE : CochainComplex.IsStrictlyLE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b := inferInstance
    have hPg : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) :=
      isStrictlyPerfect_stupidTrunc ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V) _ hP
    have hαg : ∀ i : ℤ, a - 1 + 1 ≤ i → IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.ιStupidTrunc P
          (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) i) := by
      intro i hi
      rw [HomologicalComplex.homologyMap_comp]
      have h1 := StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE P (a - 1) i
        (by omega)
      have h2 := hαiso i (by omega)
      infer_instance
    have hflatg : ∀ i : ℤ,
        AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0} (O := (Z.over V).O)
          ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).X i) :=
      fun i => isFlat_X_of_isStrictlyPerfect (Y := Z.over V) hPg i
    have hop := (exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X (Y := Z.over V) (T' V)
      ((RingedSite.derivedRestriction.{0, 0, 0, d} Z V).obj E) (a - 1) b
      (Z.restrictComplex Ecpx V) (hrepr V)
      (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) i hi)
      (fun i hi => CochainComplex.isZero_of_isStrictlyLE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b i hi)
      hflatg _ hαg (hampS V)).2
    rw [show a - 1 + 1 = a from by omega] at hop
    have hfpop :
        ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).opcycles a).IsFinitePresentation :=
      isFinitePresentation_opcycles (Z.over V) hPg a
    obtain ⟨Sv', hSv', hsummand⟩ :=
      exists_coveringSieve_isDirectSummandOfFiniteFree_overMap_of_isFinitePresentation V Z.O
        ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).opcycles a) hfpop hop
        (Over.mk (𝟙 V))
    refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) Sv', (Z.J.mem_over_iff Sv').1 hSv', ?_⟩
    intro W k hk
    rw [Sieve.overEquiv_iff] at hk
    have hsum := hsummand _ hk
    simp only [Over.mk_left, Over.mk_hom, Category.comp_id] at hsum
    have hPr : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        (restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))) :=
      isStrictlyPerfect_restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k hPg
    have hPrGE : ∀ i : ℤ, i < a - 1 → IsZero
        ((restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).X i) :=
      fun i hi => (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
          k).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) i hi)
    have hPrLE : ∀ i : ℤ, b < i → IsZero
        ((restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).X i) :=
      fun i hi => (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
          k).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b i hi)
    have hopr : IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        ((restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).opcycles a) :=
      IsDirectSummandOfFiniteFree.of_iso _
        (restrictOpcyclesAlongIso (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) a) hsum
    have hQ : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        ((restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).truncGE a) :=
      _root_.SheafOfModules.isStrictlyPerfect_truncGE hPr a hopr
    have hflatr : ∀ i : ℤ,
        AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0} (O := (Z.over W).O)
          ((restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
            (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).X i) :=
      fun i => isFlat_X_of_isStrictlyPerfect (Y := Z.over W) hPr i
    have hαr : ∀ i : ℤ, a - 1 + 1 ≤ i → IsIso (HomologicalComplex.homologyMap
        (((SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
              k).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (HomologicalComplex.ιStupidTrunc P
              (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) ≫
          (restrictComplexAlongOverIso (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
            Ecpx).hom) i) := by
      intro i hi
      rw [HomologicalComplex.homologyMap_comp]
      refine IsIso.comp_isIso'
        (AlgebraicGeometry.RingedSpace.isIso_homologyMap_map _ _ i (hαg i hi)) ?_
      exact (HomologicalComplex.homologyMapIso
        (restrictComplexAlongOverIso (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k Ecpx)
          i).isIso_hom
    obtain ⟨iso⟩ := (exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X (Y := Z.over W) (T' W)
      ((RingedSite.derivedRestriction.{0, 0, 0, d} Z W).obj E) (a - 1) b
      (Z.restrictComplex Ecpx W) (hrepr W)
      (restrictComplexAlong (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))) hPrGE hPrLE
      hflatr _ hαr (hampS W)).1
    rw [show a - 1 + 1 = a from by omega] at iso
    exact ⟨_, hQ, ⟨iso⟩⟩
  choose Sv hSv hmodel using key
  have hbind : Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf) ∈ Z.J U := by
    refine Z.J.transitive hS₀ _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine Z.J.superset_covering (fun Y g hg => ?_)
      (Z.J.pullback_stable k (hSv _ s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  refine ⟨(Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf)).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hbind
  intro V g hg
  obtain ⟨W, k, s, hs, hk, _⟩ :=
    (show Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf) g from hg)
  exact hmodel _ s hs k hk

end Proof

end Stacks.SheafOfModules.DerivedTensorProduct

end
