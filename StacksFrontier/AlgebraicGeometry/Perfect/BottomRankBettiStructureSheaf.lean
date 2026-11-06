module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBettiGeneration
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.ModuleInDegreeZero
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The bottom derived-fibre Betti number of the structure sheaf

The structure sheaf `𝒪_X` of a scheme, placed in degree zero, is a pseudo-coherent object of
`D(𝒪_X)`, and its zeroth derived-fibre Betti function is constantly `1`.

This is the smallest instance of the hypotheses of
`AlgebraicGeometry.BottomRankStratum.isClosedImmersion_fittingRankStratum_of_derivedFiberBetti_le`,
and it is the one that shows them satisfiable: an arbitrary scheme `X`, the module `𝒪_X`, the
degree `0` and the rank `1` satisfy every hypothesis of that statement, pseudo-coherence and the
bound `β_0 ≤ 1` included, with nothing assumed of `X`. The bound is attained rather than
satisfied slackly — `β_0` is equal to `1`, not merely at most `1` — so the rank `1` stratum of
`𝒪_X` is the whole of `X` and the conclusion is the assertion that the identity is a closed
immersion.

## Main results

* `AlgebraicGeometry.BottomRankStratum.isPseudoCoherent_singleFunctor_unit`: the structure sheaf
  placed in degree zero is pseudo-coherent.
* `AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_singleFunctor_unit`: its zeroth
  derived-fibre Betti number is `1` at every point.
* `AlgebraicGeometry.BottomRankStratum.isClosedImmersion_fittingRankStratum_unit`: the rank `1`
  Fitting stratum of the structure sheaf is a closed subscheme.

## Implementation notes

Pseudo-coherence is read off the strictly perfect complex `𝒪_X` in degree zero: the structure
sheaf is a direct summand of a finite free module
(`AlgebraicGeometry.StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule`), a complex
concentrated in one degree on such a module is strictly perfect
(`AlgebraicGeometry.StrictlyPerfect.isStrictlyPerfect_single`), a strictly perfect complex is a
perfect complex, and a perfect complex is pseudo-coherent in every degree
(`AlgebraicGeometry.RingedSpace.IsPerfectComplex.isPseudoCoherentComplex`). The single complex
and the single object of the derived category are identified by
`DerivedCategory.singleFunctorIsoCompQ`.

The Betti number is read off `AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_single_eq`:
the pullback of `𝒪_X` to `Spec κ(x)` is `𝒪_{Spec κ(x)}`
(`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`), which is finite locally free of rank `1`,
and over a field a finite locally free sheaf of rank `1` has global sections of dimension `1`.
Nakayama's lemma is not used here — this is the direct computation, not
`isGeneratedByNear_iff_derivedFiberBetti_le`.

## References

* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable (X : Scheme.{u})

/-- **The structure sheaf placed in degree zero is pseudo-coherent.** The complex concentrated in
degree zero on `𝒪_X` is strictly perfect, hence a perfect complex, hence pseudo-coherent in every
degree, and it represents the object of the derived category that the single functor produces. -/
public theorem isPseudoCoherent_singleFunctor_unit :
    RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  ⟨(CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf),
    (RingedSpace.isPerfectComplex_of_isStrictlyPerfect
      (StrictlyPerfect.isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace)
        0)).isPseudoCoherentComplex,
    ⟨((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
      (SheafOfModules.unit X.ringCatSheaf)).symm⟩⟩

/-- **The zeroth derived-fibre Betti number of the structure sheaf is `1`.** The derived fibre of
`𝒪_X` at `x` is `𝒪_{Spec κ(x)}` in degree zero, which is finite locally free of rank `1`, and over
a field such a sheaf has global sections of dimension `1`. -/
public theorem derivedFiberBetti_singleFunctor_unit (x : X) :
    DerivedFibreBetti.derivedFiberBetti X
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_singleFunctor_unit X) 0 x = 1 := by
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField x)).symm
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit
        (Spec (X.residueField x)))
  rw [derivedFiberBetti_single_eq _ 0 (isPseudoCoherent_singleFunctor_unit X) x]
  exact finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank (Field.toIsField _) _ 1 h2

/-- **The rank `1` Fitting stratum of the structure sheaf is a closed subscheme.** The structure
sheaf satisfies every hypothesis of
`isClosedImmersion_fittingRankStratum_of_derivedFiberBetti_le` in degree zero at the rank `1`,
with nothing assumed of `X`. -/
public theorem isClosedImmersion_fittingRankStratum_unit :
    IsClosedImmersion (fittingRankStratum (SheafOfModules.unit X.ringCatSheaf) 1).hom :=
  isClosedImmersion_fittingRankStratum_of_derivedFiberBetti_le
    (SheafOfModules.unit X.ringCatSheaf) 0 (isPseudoCoherent_singleFunctor_unit X) 1
    fun x => (derivedFiberBetti_singleFunctor_unit X x).le

end AlgebraicGeometry.BottomRankStratum

end
