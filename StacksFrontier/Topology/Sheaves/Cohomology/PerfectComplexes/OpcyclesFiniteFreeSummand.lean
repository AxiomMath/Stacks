module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.FlatFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.CohomologyFiniteness
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.IteratedRestriction

/-!
# A flat module of finite presentation is locally a finite free summand on the open subspace

Stacks 08BL says that a flat sheaf of `O_X`-modules of finite presentation on a ringed space is,
locally on `X`, a direct summand of a finite free module; the retraction it produces lives over
the *slice* sheaf of rings `O_X|_V` on `Over V`. The predicate that the strictly perfect
complexes of Tag 08C5 are built from, `StrictlyPerfect.IsDirectSummandOfFiniteFree`, instead
asks for a retraction against `O_Y^{⊕n}` for a ringed space `Y`, and the perfectness criterion
of Tag 08CP consumes it on the open subspace `X|_V`. This file connects the two.

## Main results

* `Stacks.Cohomology.OpcyclesFiniteFreeSummand.equivRestrictFreeIso`: the slice-to-subspace
  equivalence carries the free module on `ULift (Fin n)` to `O_{X|_V}^{⊕n}`.
* `Stacks.Cohomology.OpcyclesFiniteFreeSummand`
  `.exists_isDirectSummandOfFiniteFree_restrict_of_isFlat`: **Stacks 08BL in the shape Tag 08CP
  consumes it.**

## Implementation notes

The identification of the two targets is a composite of four isomorphisms, three of which are
already in the trees and the fourth of which is `Iso.refl`:
`Stacks.SheafOfModules.SliceFinite.freeOverIso` identifies the free module on a finite index type
over the slice sheaf of rings with the restriction to the slice of the free module on `X`;
`AlgebraicGeometry.RingedSpace.PseudoCoherence.overFunctorIsoRestrictModules` is the (definitional)
identification of restriction to the slice followed by the slice-to-subspace equivalence with
restriction to the open subspace; `AlgebraicGeometry.RingedSpace.finiteFreeIsoFree`
identifies `O_X^{⊕n}` with the free module on `ULift (Fin n)`; and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModulesFiniteFreeIso` says restriction
preserves finite free modules.

The finite-presentation hypothesis is a named instance binder and is handed to Stacks 08BL as an
explicit argument: the two definitionally equal spellings of the structure sheaf of rings of a
ringed space are not interchangeable for typeclass synthesis, and an explicit application is
checked at default transparency, where they are.

## References

* [Stacks Project, Tag 08BL](https://stacks.math.columbia.edu/tag/08BL)
* [Stacks Project, Tag 08CP](https://stacks.math.columbia.edu/tag/08CP)
* [Stacks Project, Tag 08C5](https://stacks.math.columbia.edu/tag/08C5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open StrictlyPerfect AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.Cohomology.OpcyclesFiniteFreeSummand

universe u

variable {X : RingedSpace.{u, u}}

/-- **The slice-to-subspace equivalence carries the free module on `ULift (Fin n)` to the finite
free module of rank `n` on the open subspace.** -/
def equivRestrictFreeIso (X : RingedSpace.{u, u}) (V : Opens X.carrier) (n : ℕ) :
    (sheafOfModulesEquivRestrict.{u} X V).functor.obj
        (SheafOfModules.free (R := (structureSheafOfRings X).over V) (ULift.{u} (Fin n))) ≅
      finiteFree (X.restrict V.isOpenEmbedding) n :=
  (sheafOfModulesEquivRestrict.{u} X V).functor.mapIso
      (Stacks.SheafOfModules.SliceFinite.freeOverIso (Rs := structureSheafOfRings X) V
        (ULift.{u} (Fin n))) ≪≫
    (restrictModules.{u} X V).mapIso
      (AlgebraicGeometry.RingedSpace.finiteFreeIsoFree X n).symm ≪≫
    restrictModulesFiniteFreeIso X V n

/-- **Stacks 08BL in the shape the truncation criterion of Tag 08CP consumes.** A flat sheaf of
`O_X`-modules of finite presentation is, on a neighbourhood `V` of any given point, a direct
summand of a finite free module on the open subspace `X|_V`. -/
theorem exists_isDirectSummandOfFiniteFree_restrict_of_isFlat
    (M : OXMod.{u, u} X) [hfp : M.IsFinitePresentation]
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M)
    (x : X.carrier) :
    ∃ V : Opens X.carrier, x ∈ V ∧
      IsDirectSummandOfFiniteFree ((restrictModules.{u} X V).obj M) := by
  obtain ⟨V, hxV, n, ⟨ρ⟩⟩ :=
    Stacks.SheafOfModules.isLocallyFiniteFreeSummand_of_isFlat_of_isFinitePresentation M
      (hfp₀ := hfp) hM x
  refine ⟨V, hxV, (isDirectSummandOfFiniteFree_iff_retract _).2 ⟨n, ⟨?_⟩⟩⟩
  exact (ρ.map (sheafOfModulesEquivRestrict.{u} X V).functor).trans
    (equivRestrictFreeIso X V n).retract

end Stacks.Cohomology.OpcyclesFiniteFreeSummand

end
