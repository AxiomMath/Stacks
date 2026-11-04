module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationCancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.StructureSheafFlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyExactness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly

/-!
# The vanishing of `H¹(𝒪)` descends along a modification

Let `q : Z ⟶ Y` be a modification of a normal integral scheme `Y`.  Then the map
`H¹(Y, 𝒪_Y) ⟶ H¹(Z, 𝒪_Z)` is injective, so `H¹(Z, 𝒪_Z) = 0` forces `H¹(Y, 𝒪_Y) = 0`.

This is the injectivity in the first conclusion of [Stacks, Tag 0AXF], at a target that is an
arbitrary normal integral scheme rather than the spectrum of a two-dimensional normal local
domain.  The two ingredients are the first Leray edge map `H¹(Y, q_*F) ⟶ H¹(Z, F)`, which is
injective for every continuous map and every abelian sheaf
(`Stacks.Cohomology.LerayLowDegree.abelianEdgeMap_injective`, [Stacks, Tag 01F2]), and
`q_*𝒪_Z = 𝒪_Y` for a modification of a normal integral scheme
(`AlgebraicGeometry.IsModification.isIso_c_of_isNormal_target`, [Stacks, Tag 0AY8]).

## Main results

The elided prefix is `AlgebraicGeometry`.

* `firstStructureSheafCohomologyVanishes_iff_isZero_abelianCohomology`: the vanishing
  `H¹(X, 𝒪_X) = 0` in the spelling of `FirstStructureSheafCohomologyVanishes` is the vanishing of
  the first right derived functor of global sections of abelian sheaves at the abelian sheaf
  underlying `𝒪_X`, which is the spelling the Leray edge map is stated against.
* `structureSheafToAbelianPushforward`, `isIso_structureSheafToAbelianPushforward`: the
  comparison `𝒪_Y ⟶ q_*𝒪_Z` of abelian sheaves induced by `q.c`, and that it is an isomorphism
  as soon as `q.c` is.
* `firstStructureSheafCohomologyVanishes_of_isIso_c`: the transfer of the vanishing along a
  morphism with `q_*𝒪_Z = 𝒪_Y`.
* `firstStructureSheafCohomologyVanishes_of_isModification`: the transfer along a modification of
  a normal integral scheme, which is the injectivity in the first conclusion of
  [Stacks, Tag 0AXF].
* `firstStructureSheafCohomologyVanishes_of_comp_eq`: the same in the shape in which the
  resolution-of-surfaces arguments consume it, two modifications of a common base one of which
  factors through the other.

## Implementation notes

The underlying abelian sheaf of `𝒪_X` is
`(SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)`, whose value is
`X.presheaf` composed with the forgetful functor `CommRingCat ⥤ AddCommGrpCat`; this is
definitionally the sheaf appearing in `AlgebraicGeometry.FirstStructureSheafCohomologyVanishes`.
The value of the abelian direct image along `q` is `q.base _* Z.presheaf` composed with the same
forgetful functor, again definitionally, so whiskering `q.c` by that functor already lands in the
right type and no comparison of pushforwards has to be constructed; the sheaf morphism it defines
is an isomorphism because `sheafToPresheaf` reflects isomorphisms.

Passing between `FirstStructureSheafCohomologyVanishes` and the abelian right derived sections is
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`, the comparison of
[Stacks, Tag 03FD]: it identifies the forgetful image of the module-valued derived sections with
the derived sections of the underlying abelian sheaf, and `IsZero` crosses the forgetful functor
on carriers.

Only the universe-homogeneous case `.{u, u}` of the Leray machinery is used, because the
instance that the abelian direct image preserves injective objects —
`Stacks.Cohomology.LerayLowDegree.abelianPushforward_preservesInjectiveObjects` — is available
only there, and that is the universe in which schemes live here.

**What is not proved.**  The first conclusion of [Stacks, Tag 0AXF] is the exactness of
`0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0`.  Only its left-hand half, the
injectivity of the first map, is proved here; the surjectivity onto `H⁰(X, R¹g_*𝒪_{X'})` rests on
[Stacks, Tag 02V7] in fibre dimension one and is not available in this development.  The two
remaining conclusions of the tag are carried in the namespace
`AlgebraicGeometry.SemistableReduction.TwoModifications`, as
`topologicalKrullDim_supp_rightDerived_one_pushforward_le_zero` and
`nonempty_generatingSections_rightDerived_one_pushforward`.

## References

* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.LerayLowDegree

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The two spellings of the vanishing -/

/-- **`H¹(X, 𝒪_X) = 0` as the vanishing of abelian-sheaf cohomology.** On the left is the
spelling `AlgebraicGeometry.DefinesRationalSingularity` uses; on the right is the first right
derived functor of global sections of abelian sheaves, evaluated at the abelian sheaf underlying
`𝒪_X`, which is the spelling the Leray edge map of [Stacks, Tag 01F2] is stated against.

Both sides are the vanishing of the module-valued derived sections, read through the comparison
of [Stacks, Tag 03FD]; `IsZero` crosses the forgetful functor on carriers. -/
public theorem firstStructureSheafCohomologyVanishes_iff_isZero_abelianCohomology
    (X : Scheme.{u}) :
    FirstStructureSheafCohomologyVanishes X ↔
      IsZero ((abelianCohomology.{u, u} X.toTopCat ⊤ 1).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  rw [firstStructureSheafCohomologyVanishes_iff_isZero_rightDerivedEvaluation X]
  have e := (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    X.ringCatSheaf (⊤ : Opens X) 1).app (SheafOfModules.unit X.ringCatSheaf)
  refine ⟨fun h => (Functor.map_isZero
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat.{u})
    h).of_iso e.symm, fun h => ?_⟩
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (h.of_iso e)

/-! ### The direct image of the structure sheaf as an abelian sheaf -/

/-! ### The transfer of the vanishing -/

/-- **The vanishing of `H¹(𝒪)` descends along a morphism with `q_*𝒪_Z = 𝒪_Y`.** The first Leray
edge map `H¹(Y, q_*𝒪_Z) ⟶ H¹(Z, 𝒪_Z)` is injective, so a vanishing target forces a vanishing
source, and the source is `H¹(Y, 𝒪_Y)` because `q_*𝒪_Z = 𝒪_Y`. -/
public theorem firstStructureSheafCohomologyVanishes_of_isIso_c {Z Y : Scheme.{u}} (q : Z ⟶ Y)
    (hq : IsIso q.c) (h : FirstStructureSheafCohomologyVanishes Z) :
    FirstStructureSheafCohomologyVanishes Y := by
  have := isIso_structureSheafToAbelianPushforward q hq
  have hZ : Subsingleton ((abelianCohomology.{u, u} Z.toTopCat ⊤ 1).obj
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf))) :=
    AddCommGrpCat.subsingleton_of_isZero
      ((firstStructureSheafCohomologyVanishes_iff_isZero_abelianCohomology Z).1 h)
  have hsub : Subsingleton ((abelianCohomology.{u, u} Y.toTopCat ⊤ 1).obj
      ((abelianPushforward.{u, u} q.base).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf)))) :=
    ⟨fun _ _ => abelianEdgeMap_injective.{u, u} q.base
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (SheafOfModules.unit Z.ringCatSheaf))
      (hZ.elim _ _)⟩
  exact (firstStructureSheafCohomologyVanishes_iff_isZero_abelianCohomology Y).2
    ((AddCommGrpCat.isZero_iff_subsingleton.2 hsub).of_iso
      ((abelianCohomology.{u, u} Y.toTopCat ⊤ 1).mapIso
        (asIso (structureSheafToAbelianPushforward q))))

/-- **Stacks Project, Tag 0AXF, the injectivity in the first conclusion.** For a modification
`q : Z ⟶ Y` of a normal integral scheme `Y`, the vanishing of `H¹(Z, 𝒪_Z)` implies the vanishing
of `H¹(Y, 𝒪_Y)`.

The source states this for modifications of the spectrum of a two-dimensional normal local
domain; neither the dimension nor the locality nor the affineness of the base is used, so it is
proved here for an arbitrary normal integral target. Only the injectivity half of the source's
exact sequence is proved: see the module docstring. -/
@[stacks 0AXF "first conclusion, injectivity only: the map H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) of the \
source's short exact sequence is injective, so a vanishing H¹ upstairs forces one downstairs. \
Generalized: the base is an arbitrary normal integral scheme, not the spectrum of a \
two-dimensional normal local domain. NOT proved, and not asserted by this entry: the \
surjectivity onto H⁰(X, R¹g_*𝒪_{X'}), which rests on Tag 02V7 in fibre dimension one. The \
tag's second and third conclusions are carried separately in \
AlgebraicGeometry.SemistableReduction.TwoModifications"]
public theorem firstStructureSheafCohomologyVanishes_of_isModification {Z Y : Scheme.{u}}
    [IsIntegral Y] [IsNormal Y] {q : Z ⟶ Y} (hq : IsModification q)
    (h : FirstStructureSheafCohomologyVanishes Z) :
    FirstStructureSheafCohomologyVanishes Y :=
  firstStructureSheafCohomologyVanishes_of_isIso_c q hq.isIso_c_of_isNormal_target h

/-- **The transfer of the vanishing between two modifications of a common base.** If `g : Y ⟶ S`
and `p : Z ⟶ S` are modifications with `Y` normal and `p` factors as `q ≫ g`, then the vanishing
of `H¹(Z, 𝒪_Z)` implies the vanishing of `H¹(Y, 𝒪_Y)`. -/
public theorem firstStructureSheafCohomologyVanishes_of_comp_eq {S Y Z : Scheme.{u}}
    [IsIntegral S] (g : Y ⟶ S) (p : Z ⟶ S) (q : Z ⟶ Y) (hY : IsNormal Y)
    (hg : IsModification g) (hp : IsModification p) (hqg : q ≫ g = p)
    (h : FirstStructureSheafCohomologyVanishes Z) :
    FirstStructureSheafCohomologyVanishes Y := by
  have : IsIntegral Y := hg.source_isIntegral
  have := hY
  exact firstStructureSheafCohomologyVanishes_of_isModification
    (SeparableGoUp.isModification_of_comp hg (hqg ▸ hp)) h

end AlgebraicGeometry

end
