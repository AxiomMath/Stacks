module

public import StacksFrontier.Algebra.Homology.PseudoCoherent.CohomologyBoundedAbove
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coherent modules on a locally Noetherian scheme are pseudo-coherent

Let `X` be a locally Noetherian scheme and let `ℱ` be a coherent `𝒪_X`-module. Viewed in degree
zero as an object of the derived category of `𝒪_X`-modules, `ℱ` is `m`-pseudo-coherent for every
integer `m`.

The mechanism is the syzygy induction. For `m = 0` the statement is that coherence implies finite
type, which is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_of_isFiniteType`.
For the step, finite type gives, near every point, an epimorphism `𝒪_W^{⊕n} ⟶ ℱ|_W`; its kernel
is again coherent, because coherent modules are closed under kernels and a finite free module on
a locally Noetherian scheme is coherent, so the inductive hypothesis applies to it on the open
subscheme `W`. The short exact sequence `0 → 𝒦 → 𝒪_W^{⊕n} → ℱ|_W → 0` gives a distinguished
triangle of the corresponding objects in degree zero, and Stacks 08CD part (1) turns
`(m+1)`-pseudo-coherence of `𝒦` and `m`-pseudo-coherence of `𝒪_W^{⊕n}` into
`m`-pseudo-coherence of `ℱ|_W`. Pseudo-coherence is local, so this suffices.

## Main results

* `AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_finiteFree`: a finite free module
  placed in degree zero is `m`-pseudo-coherent for every `m`, being strictly perfect.
* `AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent`: a coherent module on
  a locally Noetherian scheme, placed in degree zero, is `m`-pseudo-coherent for every `m`.

## Implementation notes

The induction is over all locally Noetherian schemes at once, because its step replaces `X` by an
open subscheme `W` and `ℱ` by the kernel of a map of modules on `W`. The open subscheme
`W.toScheme` of a scheme `X` has `W.toScheme.toRingedSpace` equal to
`X.toRingedSpace.restrict W.isOpenEmbedding` by definition, so the two idioms for restriction to
an open — `AlgebraicGeometry.RingedSpace.restrictModules`, in which Stacks 08CB is phrased, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, in which the coherence theory is phrased —
have the same source and target; they are identified by
`Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict`.

There are two coherence classes, `SheafOfModules.IsCoherent` and
`Stacks.SheafOfModules.IsCoherent`, with the same fields; the closure of coherent modules under
kernels is stated for the second and the scheme-level criteria for the first, so the proof below
moves between them with `SheafOfModules.IsCoherent.stacksIsCoherent` and
`Stacks.SheafOfModules.IsCoherent.rootIsCoherent`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect TopologicalSpace

namespace AlgebraicGeometry

universe d u

/-- **A finite free module placed in degree zero is `m`-pseudo-coherent for every `m`.** The
complex with `𝒪_Y^{⊕n}` in degree zero is strictly perfect, and it is its own approximation. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_finiteFree {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] (n : ℕ) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj (finiteFree Y n)) m :=
  ((RingedSpace.isPseudoCoherent_Q_obj_of_isStrictlyPerfect
      (isStrictlyPerfect_single
        ((isDirectSummandOfFiniteFree_iff_retract (finiteFree Y n)).mpr
          ⟨n, ⟨Retract.refl _⟩⟩) 0)).isPseudoCoherentFrom m).ofIso
    ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} Y) 0).app (finiteFree Y n)).symm

attribute [local instance] HasDerivedCategory.standard

/-- The syzygy induction behind
`AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent`, with the number of
syzygy steps as the induction variable and the scheme quantified inside, since the step replaces
the scheme by an open subscheme. -/
private theorem isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent_aux :
    ∀ (k : ℕ) (X : Scheme.{u}) (_ : IsLocallyNoetherian X)
      (F : OXMod.{u, u} X.toRingedSpace), Stacks.SheafOfModules.IsCoherent F →
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F)
        (-(k : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro X hX F hF
    simp only [Nat.cast_zero, neg_zero]
    exact RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_of_isFiniteType
      (X := X.toRingedSpace) F hF.rootIsCoherent.isFiniteType
  | succ k ih =>
    intro X hX F hF
    have hFr := hF.rootIsCoherent
    refine RingedSpace.isPseudoCoherentFrom_of_local_restrict (X := X.toRingedSpace) _ _
      fun x => ?_
    obtain ⟨W, hxW, n, q, hq⟩ :=
      RingedSpace.exists_epi_finiteFree_of_isFiniteType (X := X.toRingedSpace) F
        hFr.isFiniteType x
    refine ⟨W, hxW, ?_⟩
    have hNW : IsLocallyNoetherian (Scheme.Opens.toScheme (X := X) W) :=
      isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι (X := X) W)
    have hGc : Stacks.SheafOfModules.IsCoherent
        ((RingedSpace.restrictModules X.toRingedSpace W).obj F) :=
      Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X W).app F).symm
        (Modules.isCoherent_restrict (M := F) (hM := hFr) W).stacksIsCoherent
    have hff : Stacks.SheafOfModules.IsCoherent
        (finiteFree (X.toRingedSpace.restrict W.isOpenEmbedding) n) :=
      Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_finiteFree
        (Scheme.Opens.toScheme (X := X) W) n
    have hSE : (ShortComplex.kernelSequence q).ShortExact :=
      { exact := ShortComplex.kernelSequence_exact q
        mono_f := inferInstance
        epi_g := hq }
    have hmain : RingedSpace.IsPseudoCoherentFrom
        (X := X.toRingedSpace.restrict W.isOpenEmbedding)
        ((DerivedCategory.singleFunctor
            (OXMod.{u, u} (X.toRingedSpace.restrict W.isOpenEmbedding)) 0).obj
          ((RingedSpace.restrictModules X.toRingedSpace W).obj F)) (-(k : ℤ) - 1) :=
      RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished (-(k : ℤ) - 1)
        hSE.singleTriangle hSE.singleTriangle_distinguished
        (by
          have harith : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
          rw [harith]
          exact ih (Scheme.Opens.toScheme (X := X) W) hNW (kernel q)
            (Stacks.SheafOfModules.isCoherent_kernel q))
        (isPseudoCoherentFrom_singleFunctor_zero_finiteFree
          (Y := X.toRingedSpace.restrict W.isOpenEmbedding) n (-(k : ℤ) - 1))
    refine (hmain.ofIso
      (RingedSpace.derivedRestrictSingleFunctorIso (X := X.toRingedSpace) W 0 F).symm).mono ?_
    push_cast
    omega

/-- **On a locally Noetherian scheme a coherent module, placed in degree zero, is
`m`-pseudo-coherent for every `m`.** Over a Noetherian ring a finite module has an infinite
resolution by finite free modules, and this is the sheaf-theoretic form of that statement: the
syzygies of a coherent module are coherent, so the resolution can be continued indefinitely. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : OXMod.{u, u} X.toRingedSpace)
    (hF : Stacks.SheafOfModules.IsCoherent F) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) m :=
  (isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent_aux (-m).toNat X inferInstance F
    hF).mono (by omega)

end AlgebraicGeometry

end
