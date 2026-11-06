module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.TopologyTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SyntomicSourceLocalityTransfer

/-!
# Stacks 06ER: a property local on the source passes from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**), and let
`P_spaces = AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` be the induced property of
morphisms of algebraic spaces over `S` (**Stacks 03MJ**). For each of the five topologies `τ`
of **Stacks 03YH** — fpqc, fppf, syntomic, smooth, étale — if `P` is local on the source for
the counterpart of `τ` on schemes, then `P_spaces` is local on the source for `τ`.

The argument, for a single `τ`, is `AlgebraicGeometry.Space.Topology.isLocalAtSource_of_schemes`:
a `τ`-covering of `X` is base-changed along an étale chart of `X` over a chart of `Y`, each
member is covered by an étale scheme atlas, and the composed family is a `τ`-covering of
representables, hence a covering family of the representing schemes. It consumes only the two
stability clauses `AlgebraicGeometry.Space.Topology.HasCoveringStability`: `τ`-coverings
compose and are stable under base change. This module supplies those clauses for the fpqc and
the syntomic topology, so that all five are available, and so proves Stacks 06ER itself.

For the fpqc topology the composition clause is **Stacks 03MR** and the base-change clause is
Stacks 03MR part (3), whose first-projection orientation is obtained from the second-projection
one through the symmetry of the fibre product. For the syntomic topology both clauses are
**Stacks 041B**.

## Main results

* `AlgebraicGeometry.Space.Topology.hasCoveringStability_fpqc` and
  `AlgebraicGeometry.Space.Topology.hasCoveringStability_syntomic`: the two stability clauses
  for the fpqc and the syntomic topology.
* `AlgebraicGeometry.Space.Topology.hasCoveringStability`: the two stability clauses for every
  one of the five topologies.
* `AlgebraicGeometry.Space.Topology.isLocalAtSource_holdsOnEveryEtaleChart`: **Stacks 06ER**.

## References

* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041B](https://stacks.math.columbia.edu/tag/041B)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_PropertyLocalOnSource :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_PropertyLocalOnSource
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_PropertyLocalOnSource B S hS).has_limit _

/-- **Stacks 03MR.** The fpqc covering families of algebraic spaces over `S` compose and are
stable under base change.

The base-change clause is Stacks 03MR part (3), stated there for the second projections out of
the fibre products; the first projections are the second ones precomposed with the symmetry of
the fibre product, and the fpqc condition is invariant under such a precomposition. -/
theorem Topology.hasCoveringStability_fpqc :
    Topology.HasCoveringStability.{u, v} .fpqc B S hS := by
  constructor
  · intro I X Xi Z f g hf hg
    exact ⟨hf.1, fun p => (hg p.1).2.1 p.2,
      isFpqcCovering_comp B S hS (J := fun _ : I => PUnit.{v + 1})
        (Xij := fun ij => Z ij.1) hf.1 hf.2.1 (fun i j => (hg i).2.1 j) f
        (fun i _ => g i) hf.2.2 fun i => (hg i).2.2⟩
  · intro I X X' Xi f g hf
    refine ⟨X'.property, fun i => isAlgebraicSpace_pullback B S hS g.hom (f i).hom
      X'.property (Xi i).property hf.1, ?_⟩
    simpa using isFpqcCovering_isoComp B S hS
      (fun i => (pullbackSymmetry g.hom (f i).hom).hom)
      (fun i => pullback.snd (f i).hom g.hom) (isFpqcCovering_pullback B S hS f g hf.2.2)

/-- **Stacks 041B.** The syntomic covering families of algebraic spaces over `S` compose and are
stable under base change. -/
theorem Topology.hasCoveringStability_syntomic :
    Topology.HasCoveringStability.{u, v} .syntomic B S hS := by
  constructor
  · intro I X Xi Z f g hf hg
    exact ⟨hf.1, fun p => (hg p.1).2.1 p.2,
      isSyntomicCovering_comp B S hS (fun _ : I => PUnit.{v + 1}) Xi f
        (fun i _ => Z i) (fun i _ => g i) hf.2.2 fun i => (hg i).2.2⟩
  · intro I X X' Xi f g hf
    exact ⟨X'.property, fun i => isAlgebraicSpace_pullback B S hS g.hom (f i).hom
      X'.property (Xi i).property hf.1,
      isSyntomicCovering_pullback B S hS g.hom X'.property (fun i => (Xi i).obj)
        (fun i => (f i).hom) hf.2.2⟩

/-- For every one of the five topologies of Stacks 03YH, the covering families of algebraic
spaces over `S` compose and are stable under base change: this is Stacks 03MR for the fpqc
topology, Stacks 03Y9 for the fppf topology, Stacks 041B for the syntomic topology,
Stacks 041D for the smooth topology and Stacks 041F for the étale topology. -/
theorem Topology.hasCoveringStability (τ : Topology) :
    Topology.HasCoveringStability.{u, v} τ B S hS := by
  cases τ with
  | fpqc => exact Topology.hasCoveringStability_fpqc B S hS
  | fppf => exact Topology.hasCoveringStability_fppf B S hS
  | syntomic => exact Topology.hasCoveringStability_syntomic B S hS
  | smooth => exact Topology.hasCoveringStability_smooth B S hS
  | etale => exact Topology.hasCoveringStability_etale B S hS

/-- **Stacks 06ER.** Let `P` be a property of morphisms of schemes over `S` which is étale local
on the source and target, and let `τ` be one of the five topologies of Stacks 03YH. If `P` is
local on the source for the counterpart of `τ` on schemes, then the associated property of
morphisms of algebraic spaces over `S` of Stacks 03MJ is local on the source for `τ`. -/
@[stacks 06ER]
theorem Topology.isLocalAtSource_holdsOnEveryEtaleChart (τ : Topology)
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    (hlocal : P.IsLocalAtSource τ.schemePrecoverage) :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} τ B S hS) := by
  let : P.IsLocalAtSource τ.schemePrecoverage := hlocal
  exact Topology.isLocalAtSource_of_schemes B S hS τ
    (Topology.hasCoveringStability.{u, v} B S hS τ) P hP

end AlgebraicGeometry.Space

end
