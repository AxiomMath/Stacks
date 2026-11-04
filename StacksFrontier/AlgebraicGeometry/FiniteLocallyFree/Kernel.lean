module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Extension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The sub-object of a short exact sequence of `𝒪_X`-modules is finite locally free

Let `0 ⟶ ℰ' ⟶ ℰ ⟶ ℰ'' ⟶ 0` be a short exact sequence of `𝒪_X`-modules on a scheme `X` whose
middle term `ℰ` is finite locally free.  The sub-object `ℰ'` is then finite locally free in each
of two cases: when `ℰ''` is itself finite locally free, and when `ℰ''` is a perfect module of tor
dimension at most one.

These are the two displayed short exact sequences of the proof of [Stacks, Tag 0F8J],

  `0 ⟶ Im(d^i) ⟶ Ker(d^{i+1}) ⟶ H^{i+1}(E) ⟶ 0`,   `0 ⟶ Ker(d^i) ⟶ ℰ^i ⟶ Im(d^i) ⟶ 0`,

in the order the source's descending induction uses them.  What is *not* here is the induction
itself: the source's statement is about the images and kernels of the differentials of a bounded
complex, and assembling these two steps into that statement is a separate step, so no tag is
claimed below.

Both run the opposite way to the extension closure
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact`, which concludes about the middle
term from the two ends; neither is a consequence of it, and the second is false without the tor
hypothesis.

## Main results

* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact`: the finite locally free
  quotient case, the source's second sequence.
* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact_of_isPerfect`: the perfect
  quotient of tor dimension at most one case, the source's first sequence.
* `Stacks.FiniteLocallyFree.isFinitePresentation_of_isPerfect_singleFunctor`: a module perfect in
  degree zero is of finite presentation, which is the half of [Stacks, Tag 09V9] (2) that the
  second case needs.

## Implementation notes

**Both cases are `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude` with its
finite presentation hypothesis discharged**, and they discharge it differently.  That theorem —
the kernel of a surjection from a finite locally free module onto a module of tor dimension at
most one is finite locally free as soon as it is finitely presented — is already in the library;
nothing below reproves any part of it.  The sub-object is *not* obtained by exhibiting it as
locally free directly: a local splitting makes it a direct summand of a finite free module with
free complement, which is stably free and need not be free.

* When the quotient is finite locally free, the tor-amplitude hypothesis comes from a finite
  locally free module in degree zero having tor amplitude in `[0, 0]`, widened to `[-1, 0]`, and
  finite presentation of the sub-object comes from
  `AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree`, whose own proof splits
  the sequence locally and reads the kernel off as the cokernel of the splitting section.
* When the quotient is perfect of tor dimension at most one, the tor-amplitude hypothesis is
  assumed, as the source assumes it, and finite presentation of the sub-object comes from
  perfectness: the sub-object is perfect by [Stacks, Tag 08CR] applied to the first vertex of the
  sequence's distinguished triangle, a perfect object is pseudo-coherent, and a module which is
  `(-1)`-pseudo-coherent in degree zero is of finite presentation by [Stacks, Tag 09V9] (2).
  This is the only route to finite presentation here: there is no two-out-of-three property for
  finite presentation of sheaves of modules, and there cannot be one, since a finitely generated
  ideal of a non-coherent ring is the kernel of a map of finitely presented modules without being
  finitely presented.

**Which finite-local-freeness predicate.**  Every statement is about
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` at `X.ringCatSheaf`, the spelling the consumers of
this file use.  It is a reducible abbreviation of the canonical class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` that
`AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree` takes as an instance, so
no bridge is needed.

**Which pseudo-coherence predicate.**  There are likewise two `abbrev`s named
`IsPseudoCoherent` for objects of `D(𝒪_X)`, in the namespaces
`AlgebraicGeometry.RingedSpace` and `AlgebraicGeometry.RingedSpace.PseudoCoherence`, with the
same body.  `Stacks.FiniteLocallyFree.isPseudoCoherent_of_pseudoCoherence` names that
definitional identity, and
`Stacks.FiniteLocallyFree.isFinitePresentation_of_isPerfect_singleFunctor` goes through it rather
than relying on unification to cross the two spellings silently.

## References

* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 09V9](https://stacks.math.columbia.edu/tag/09V9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u d

namespace Stacks.FiniteLocallyFree

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **The sub-object of a short exact sequence of `𝒪_X`-modules whose middle term and quotient
are finite locally free is of finite presentation.**  It is the kernel of an epimorphism from a
finitely presented module onto a finite locally free one, which is
`AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree`, transported along the
identification of the sub-object with that kernel. -/
theorem isFinitePresentation_X₁_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂)
    (h₃ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃) :
    _root_.SheafOfModules.IsFinitePresentation.{u, u, u} S.X₁ := by
  have h₂' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₂ :=
    h₂
  have h₃' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₃ :=
    h₃
  let : _root_.SheafOfModules.IsFinitePresentation.{u, u, u} S.X₂ :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree S.X₂ h₂'
  have h₂qc : S.X₂.IsQuasicoherent := by
    obtain ⟨q, hq, -⟩ := h₂.exists_isFiniteLocallyFreeData
    have := hq
    exact q.quasiCoherentData.isQuasicoherent
  have := h₂qc
  have := h₃'
  have := hS.epi_g
  have hker : (kernel S.g).IsFinitePresentation :=
    AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree S.g
  exact (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (hS.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)).symm hker

/-- **The sub-object of a short exact sequence of `𝒪_X`-modules whose middle term and quotient
are finite locally free is finite locally free.**

This is the finite-locally-free case of the second displayed short exact sequence of the proof of
[Stacks, Tag 0F8J], `0 ⟶ Ker(d^i) ⟶ ℰ^i ⟶ Im(d^i) ⟶ 0`: once the image is known to be finite
locally free, the kernel is too, and no hypothesis on the cohomology is needed for this step.

It is `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude` with its two
remaining hypotheses discharged: the quotient, being finite locally free, has tor amplitude in
`[0, 0]` and hence in `[-1, 0]`, and the sub-object is finitely presented by
`Stacks.FiniteLocallyFree.isFinitePresentation_X₁_of_shortExact`. -/
theorem isFiniteLocallyFree_X₁_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂)
    (h₃ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁ :=
  AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude S hS h₂
    (Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (AlgebraicGeometry.hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree X S.X₃ h₃)
      (show (-1 : ℤ) ≤ 0 by omega) le_rfl)
    (isFinitePresentation_X₁_of_shortExact S hS h₂ h₃)

/-! ### The sub-object of a sequence whose quotient is perfect of tor dimension at most one -/

/-- **The two spellings of pseudo-coherence for an object of `D(𝒪_X)` agree.**

`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`
(`StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel`) and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent`
(`StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs`) are two `abbrev`s, in two
namespaces, with the same body: the object is represented by a complex which, near every point
and from every degree, admits a strictly perfect approximation.  They are stated over the same
`AlgebraicGeometry.StrictlyPerfect.OXMod` and the same
`AlgebraicGeometry.StrictlyPerfect.IsStrictlyPerfect`, so the identity is definitional and this
proof is the hypothesis itself.

It is recorded as a lemma rather than left to unification.  The next result needs to move a
hypothesis across the two spellings, and doing that implicitly inside an `exact` makes the
load-bearing step invisible; naming it means that if either `abbrev` is ever changed the
breakage is a single error here, with this docstring attached, rather than an unexplained
failure in a proof about finite presentation. -/
theorem isPseudoCoherent_of_pseudoCoherence {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} Y)]
    {E : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} Y)}
    (h : RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) E) :
    RingedSpace.IsPseudoCoherent E := h

/-- **A sheaf of modules on a scheme which is perfect in degree zero is of finite presentation.**
A perfect object of the derived category is pseudo-coherent, hence `(-1)`-pseudo-coherent, and a
module placed in degree zero is `(-1)`-pseudo-coherent exactly when it is of finite presentation,
which is [Stacks, Tag 09V9] (2).

The two pseudo-coherence predicates in play are identified by
`Stacks.FiniteLocallyFree.isPseudoCoherent_of_pseudoCoherence`; see its docstring. -/
theorem isFinitePresentation_of_isPerfect_singleFunctor (M : X.Modules)
    (hM : IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :
    _root_.SheafOfModules.IsFinitePresentation.{u, u, u} M := by
  have hpc := isPseudoCoherent_of_pseudoCoherence (Y := X.toRingedSpace)
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
      (X := X.toRingedSpace) _ hM)
  have hiff :=
    RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_neg_one_iff_isFinitePresentation
      (X := X.toRingedSpace) M
  exact hiff.1 (RingedSpace.IsPseudoCoherent.isPseudoCoherentFrom hpc (-1))

/-- **The sub-object of a short exact sequence of `𝒪_X`-modules is perfect in degree zero when
the other two terms are.**  This is [Stacks, Tag 08CR] for the first vertex of the distinguished
triangle `ℰ'[0] ⟶ ℰ[0] ⟶ ℰ''[0] ⟶ ℰ'[1]` of the sequence, the middle term being perfect because
it is finite locally free. -/
theorem isPerfect_singleFunctor_X₁_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂)
    (h₃ : IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj S.X₃)) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj S.X₁) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    hS.singleTriangle hS.singleTriangle_distinguished
    (AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree X S.X₂ h₂) h₃

/-- **The sub-object of a short exact sequence of `𝒪_X`-modules whose middle term is finite
locally free and whose quotient is a perfect module of tor dimension at most one is finite
locally free.**

This is the first displayed short exact sequence of the proof of [Stacks, Tag 0F8J],
`0 ⟶ Im(d^i) ⟶ Ker(d^{i+1}) ⟶ H^{i+1}(E) ⟶ 0`, with the source's hypothesis on the cohomology
exactly as the source states it: `H^{i+1}(E)` is a perfect `𝒪_X`-module of tor dimension at most
one.  Neither half of that hypothesis can be dropped — the conclusion is false without a tor
condition, and perfectness is what makes the sub-object finitely presented.

It is `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude` with its finite
presentation hypothesis discharged: the sub-object is perfect in degree zero by
`Stacks.FiniteLocallyFree.isPerfect_singleFunctor_X₁_of_shortExact`, hence of finite presentation
by `Stacks.FiniteLocallyFree.isFinitePresentation_of_isPerfect_singleFunctor`. -/
theorem isFiniteLocallyFree_X₁_of_shortExact_of_isPerfect (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₂ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂)
    (h₃perf : IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj S.X₃))
    (h₃tor : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj S.X₃) (-1) 0) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁ :=
  AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude S hS h₂ h₃tor
    (isFinitePresentation_of_isPerfect_singleFunctor S.X₁
      (isPerfect_singleFunctor_X₁_of_shortExact S hS h₂ h₃perf))

end Stacks.FiniteLocallyFree
