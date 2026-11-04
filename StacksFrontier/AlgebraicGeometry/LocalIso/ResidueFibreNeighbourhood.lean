module

public import StacksFrontier.AlgebraicGeometry.LocalIso.OpenIsoLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StalkIsoSpreadout
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# From invertibility on the residue fibres to invertibility on a neighbourhood

Let `X` be a scheme and let `α : F ⟶ G` be a morphism of `𝒪_X`-modules.  If the fibre of `α` over
the residue field at `x` is invertible and the stalks of `F` and `G` at `x` are finite free, then
`α` is invertible on the stalk at `x`: this is
`AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback`, Nakayama plus the determinant trick.

This file turns that **pointwise** statement into a statement about a whole subset.  If the fibre
of `α` is invertible at every point of a subset `Z ⊆ X`, then there is an **open neighbourhood of
`Z`** over which `α` restricts to an isomorphism.  Nothing is assumed about `Z`: it need not be
closed, constructible or irreducible, and in the intended application it is the underlying set of
a closed subscheme.

## Main results

* `Stacks.AlgebraicGeometry.IsoLocus.mem_stalkIsoLocus_of_isIso_residuePullback`: **the residue
  fibre criterion puts a point in the stalkwise isomorphism locus.**
* `Stacks.AlgebraicGeometry.IsoLocus.mem_stalkIsoLocus_of_isIso_residuePullback_of_flf`: the same
  with the four freeness and finiteness hypotheses on the stalks discharged from finite local
  freeness of `F` and `G`.
* `…IsoLocus.exists_isIso_restrictFunctor_map_of_forall_isIso_residuePullback`: **a morphism of
  finite locally free modules whose residue fibre is invertible at every point of a subset `Z`
  restricts to an isomorphism over an open neighbourhood of `Z`.**

## Implementation notes

The hypotheses of `AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback` are freeness and
finiteness of the two stalks *at the one point*, not local freeness of the two sheaves, so the
first result below is stated in that generality and the finite-locally-free form is derived from
it by `Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`.

Coherence of the target is what makes the locus open, and it is required only by the last result.
The first two need nothing beyond finite type of the target, which coherence supplies.

## References

* [Stacks Project, Tag 01Y3](https://stacks.math.columbia.edu/tag/01Y3)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.IsoLocus

variable {X : Scheme.{u}}

/-- **The residue fibre criterion for membership of the stalkwise isomorphism locus.**  A
morphism whose fibre over the residue field at `x` is invertible, and whose source and target
have finite free stalks at `x`, is invertible on the stalk at `x`. -/
theorem mem_stalkIsoLocus_of_isIso_residuePullback {F G : X.Modules} [G.IsFiniteType]
    (α : F ⟶ G) (x : X)
    (hFfree : Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hFfin : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hGfree : Module.Free (X.presheaf.stalk x) (G.presheaf.stalk x))
    (hGfin : Module.Finite (X.presheaf.stalk x) (G.presheaf.stalk x))
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    x ∈ stalkIsoLocus α :=
  AlgebraicGeometry.isIso_stalk_of_isIso_residuePullback α x hFfree hFfin hGfree hGfin hα

/-- **The residue fibre criterion for finite locally free modules.**  The four stalk hypotheses
of `Stacks.AlgebraicGeometry.IsoLocus.mem_stalkIsoLocus_of_isIso_residuePullback` hold
automatically for a finite locally free module. -/
theorem mem_stalkIsoLocus_of_isIso_residuePullback_of_flf {F G : X.Modules} [G.IsFiniteType]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G]
    (α : F ⟶ G) (x : X)
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    x ∈ stalkIsoLocus α :=
  mem_stalkIsoLocus_of_isIso_residuePullback α x
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree F x).1
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree F x).2
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G x).1
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G x).2 hα

/-- **A morphism of finite locally free modules whose residue fibre is invertible at every point
of a subset restricts to an isomorphism over an open neighbourhood of that subset.**

This is the local-to-global form of the residue fibre criterion: the pointwise criterion places
every point of `Z` in the stalkwise isomorphism locus, that locus is open because the target is
coherent, and a morphism restricts to an isomorphism over any open contained in it. -/
theorem exists_isIso_restrictFunctor_map_of_forall_isIso_residuePullback {F G : X.Modules}
    [F.IsFiniteType] [hG : _root_.SheafOfModules.IsCoherent G]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G]
    (α : F ⟶ G) (Z : Set X)
    (hZ : ∀ x ∈ Z, IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField x)).map α)) :
    ∃ U : X.Opens, Z ⊆ (U : Set X) ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  have : G.IsFiniteType := hG.isFiniteType
  exact exists_isIso_restrictFunctor_map_of_subset_stalkIsoLocus α Z
    fun x hx => mem_stalkIsoLocus_of_isIso_residuePullback_of_flf α x (hZ x hx)

end Stacks.AlgebraicGeometry.IsoLocus

end
