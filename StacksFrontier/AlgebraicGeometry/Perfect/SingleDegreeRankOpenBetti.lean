module

public import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenChart
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankBettiGeneration

/-!
# The derived-fibre Betti numbers on the single-degree rank locus

Let `X` be a scheme, `E` a pseudo-coherent object of the derived category of sheaves of modules
on `X`, `i` an integer and `r` a natural number, and let `U = singleDegreeRankOpen E i r` be the
largest open subscheme of `X` on which `E` is a finite locally free module of rank `r` placed in
degree `i`. This file proves that at every point of `U` the derived-fibre Betti numbers of `E` of
[stacks 0BDI] are concentrated in degree `i` with value `r`:

`β_j(x) = 0` for `j ≠ i`, and `β_i(x) = r`.

That is one of the two implications of the pointwise description of `U` through the Betti numbers
which the proof of [stacks 0BDK] uses, and the half which needs no perfectness.

## Main results

* `AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_single_eq_zero`: for a **flat** module
  `F` placed in degree `a`, the Betti function `β_j` vanishes for every `j ≠ a`.
* `AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_single_eq_rank`: for a module `F` which
  is finite locally free of rank `r`, placed in degree `a`, the Betti function `β_a` is
  constantly `r`.
* `AlgebraicGeometry.Scheme.Modules.derivedFiberBetti_eq_zero_of_mem_singleDegreeRankOpen` and
  `AlgebraicGeometry.Scheme.Modules.derivedFiberBetti_eq_rank_of_mem_singleDegreeRankOpen`: the
  two halves of the concentration statement at a point of `U`.

## Implementation notes

*The two single-module computations.* For the on-degree value,
`AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_single_eq` identifies `β_a(x)` with the
dimension of the fibre of `F`, and that dimension is evaluated when `F` is finite locally free of
a fixed rank by
`AlgebraicGeometry.BottomRankStratum.finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank` applied
to the pullback of `F`. The off-degree vanishing is where flatness enters:
`AlgebraicGeometry.derivedPullbackSingleFlatIso` identifies `Li_x^*(F[-a])` with the ordinary
pullback of `F` placed in degree `a`, and the cohomology of an object concentrated in one degree
vanishes in every other
(`AlgebraicGeometry.Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj`). Without flatness
the statement is false — the cohomology below degree `a` is the higher Tor against `F`.

*The passage to the open subscheme.* On `U` the object `E` is its own degree-`i` cohomology sheaf
`N` placed in degree `i`, and `N` is finite locally free of rank `r`, hence flat. Base change for
the Betti functions along the open immersion `U.ι`, which is part (1) of [stacks 0BDI]
(`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback`), carries the computation
at `N[-i]` on `U` down to `E` on `X`, and
`AlgebraicGeometry.FibreBetti.derivedFiberBetti_eq_of_iso` transports it across the isomorphism.
The chain is written as a composite of equalities rather than as a `rw` chain: rewriting through
the derived pullback of `E` is not type-correct at `implicit` transparency.

*The converse.* That a point whose Betti numbers are concentrated in degree `i` with value `r`
lies in `U` is the half that needs perfectness of `E`, and it is
`AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_of_derivedFiberBetti` in
`StacksFrontier/AlgebraicGeometry/Perfect/SingleDegreeRankOpenAffine.lean`: the local structure
theorem [stacks 0BCD] on an affine chart, in the form
`StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated`, transported to the
chart through the affine derived equivalence, with
`AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_iff_exists_isAffineOpen` for the
chart-to-`X` half.

These results carry no Stacks attribute: they are steps of the proof of [stacks 0BDK], not
clauses of its statement.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable {X : Scheme.{u}}

/-- **For a flat module placed in degree `a`, the Betti function vanishes off degree `a`.** The
derived pullback of a flat module placed in a degree is its ordinary pullback placed in that
degree, and an object concentrated in one degree has no cohomology elsewhere. -/
public theorem derivedFiberBetti_single_eq_zero (F : X.Modules) (a : ℤ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules a).obj F))
    (j : ℤ) (hj : j ≠ a) (x : X) :
    DerivedFibreBetti.derivedFiberBetti X
      ((DerivedCategory.singleFunctor X.Modules a).obj F) hE j x = 0 := by
  rw [DerivedFibreBetti.derivedFiberBetti_apply]
  have hzero : IsZero ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules j).obj
      ((derivedPullback (X.fromSpecResidueField x).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj F))) :=
    IsZero.of_iso (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj _ hj)
      ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules j).mapIso
        (derivedPullbackSingleFlatIso (X.fromSpecResidueField x).toLRSHom.toShHom F hF a))
  have := ModuleCat.subsingleton_of_isZero
    (Functor.map_isZero (moduleSpecΓFunctor (R := X.residueField x)) hzero)
  exact Module.finrank_zero_of_subsingleton

/-- **For a finite locally free module of rank `r` placed in degree `a`, the Betti function in
degree `a` is constantly `r`.** The Betti number is the dimension of the fibre, the fibre of a
finite locally free module of rank `r` is finite locally free of rank `r`, and over a field that
dimension is `r`. -/
public theorem derivedFiberBetti_single_eq_rank (F : X.Modules) (a : ℤ) (r : ℕ)
    (hFr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules a).obj F))
    (x : X) :
    DerivedFibreBetti.derivedFiberBetti X
      ((DerivedCategory.singleFunctor X.Modules a).obj F) hE a x = r := by
  rw [derivedFiberBetti_single_eq F a hE x]
  exact finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank (Field.toIsField _) _ r
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (X.fromSpecResidueField x) F r)

end AlgebraicGeometry.BottomRankStratum

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- At a point of `singleDegreeRankOpen E i r`, the Betti numbers of `E` are those, at a point of
the open subscheme, of its degree-`i` cohomology sheaf placed in degree `i`. -/
private theorem exists_derivedFiberBetti_eq_single_homology
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) (j : ℤ) {x : X} (hx : x ∈ singleDegreeRankOpen E i r) :
    ∃ (y : singleDegreeRankOpen E i r) (hE' : RingedSpace.IsPseudoCoherent.{u, u + 1}
      (X := (singleDegreeRankOpen E i r).toScheme.toRingedSpace)
      ((DerivedCategory.singleFunctor (singleDegreeRankOpen E i r).toScheme.Modules i).obj
        ((DerivedCategory.homologyFunctor
            (singleDegreeRankOpen E i r).toScheme.Modules i).obj
          ((restrictFunctor (singleDegreeRankOpen E i r).ι).mapDerivedCategory.obj E)))),
      DerivedFibreBetti.derivedFiberBetti X E hE j x =
        DerivedFibreBetti.derivedFiberBetti (singleDegreeRankOpen E i r).toScheme _ hE' j y := by
  obtain ⟨y, rfl⟩ : x ∈ Set.range (singleDegreeRankOpen E i r).ι.base := by
    rwa [Scheme.Opens.range_ι]
  have e := ((derivedRestrictIsoDerivedPullback (singleDegreeRankOpen E i r).ι).app E).symm ≪≫
    (nonempty_iso_singleFunctor_restrict_singleDegreeRankOpen E i r).some
  have hpc := DerivedFibreBetti.isPseudoCoherent_derivedPullback
    (singleDegreeRankOpen E i r).ι E hE
  exact ⟨y, hpc.of_iso e,
    (congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback
      (singleDegreeRankOpen E i r).ι E hE j) y).symm.trans
    (congrFun (FibreBetti.derivedFiberBetti_eq_of_iso (singleDegreeRankOpen E i r).toScheme
      hpc (hpc.of_iso e) e j) y)⟩

/-- **The Betti numbers vanish off degree `i` at a point of the open subscheme of
[stacks 0BDK].** -/
public theorem derivedFiberBetti_eq_zero_of_mem_singleDegreeRankOpen
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) (j : ℤ) (hj : j ≠ i) {x : X}
    (hx : x ∈ singleDegreeRankOpen E i r) :
    DerivedFibreBetti.derivedFiberBetti X E hE j x = 0 := by
  obtain ⟨y, hE', h⟩ := exists_derivedFiberBetti_eq_single_homology E hE i r j hx
  exact h.trans (BottomRankStratum.derivedFiberBetti_single_eq_zero _ i
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFreeOfRank _ r
      (isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen E i r)) hE' j hj y)

/-- **The Betti number in degree `i` is `r` at a point of the open subscheme of
[stacks 0BDK].** -/
public theorem derivedFiberBetti_eq_rank_of_mem_singleDegreeRankOpen
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) {x : X} (hx : x ∈ singleDegreeRankOpen E i r) :
    DerivedFibreBetti.derivedFiberBetti X E hE i x = r := by
  obtain ⟨y, hE', h⟩ := exists_derivedFiberBetti_eq_single_homology E hE i r i hx
  exact h.trans (BottomRankStratum.derivedFiberBetti_single_eq_rank _ i r
    (isFiniteLocallyFreeOfRank_homology_singleDegreeRankOpen E i r) hE' y)

end AlgebraicGeometry.Scheme.Modules

end
