module

public import StacksFrontier.AlgebraicGeometry.LocalIso.ResidueFibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# A morphism invertible on a closed subscheme is invertible near it

Let `i : Z ⟶ X` be a closed immersion and let `α : F ⟶ G` be a morphism of finite locally free
`𝒪_X`-modules with `G` coherent.  If `i^*α` is an isomorphism, then **`α` restricts to an
isomorphism over an open neighbourhood of `Z`**.

The passage from `i^*α` to the residue fibres is the only new step.  For `z : Z` the residue
field of `X` at `i z` is the residue field of `Z` at `z`, because a closed immersion is surjective
on stalks (`Stacks.Thickenings.isIso_residueFieldMap_of_surjective_stalkMap` fed Mathlib's
`AlgebraicGeometry.Scheme.Hom.stalkMap_surjective`), and Mathlib's
`AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` is the commuting
square which lets the fibre of `α` over `κ(i z)` be read as the fibre of `i^*α` over `κ(z)`.
Pullback along an isomorphism of schemes is an equivalence of module categories
(`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isEquivalence_pullback`), hence reflects
isomorphisms, which is what turns that reading into the hypothesis the residue fibre criterion
needs.

## Main results

* `Stacks.AlgebraicGeometry.IsoLocus.isIso_residuePullback_of_isIso_pullback_of_isClosedImmersion`:
  **if `i^*α` is an isomorphism then so is the fibre of `α` over the residue field at every point
  of `Z`.**  No finiteness hypothesis of any kind is used.
* `…IsoLocus.subset_stalkIsoLocus_range_of_isIso_pullback`: the image of `Z` lies in the
  stalkwise isomorphism locus of `α`, for `α` a morphism of finite locally free modules.
* `…IsoLocus.exists_isIso_restrictFunctor_map_of_isIso_pullback_isClosedImmersion`: **`α`
  restricts to an isomorphism over an open neighbourhood of `Z`.**
* `…IsoLocus.exists_isIso_restrictFunctor_map_of_isIso_pullback_of_isLocallyNoetherian`: the same
  with coherence and finite type discharged — on a locally Noetherian scheme a finite locally
  free module is coherent ([Stacks, Tag 01XZ]), so the only hypotheses left are that `i` is a
  closed immersion, that `F` and `G` are finite locally free, and that `i^*α` is invertible.

## Implementation notes

`Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff` is used twice, in opposite
directions, to move between the pullback along a composite and the iterated pullback; it carries
the defining equation of the composite as an argument, so the commuting square above is supplied
to it directly and no rewrite is performed on a hypothesis mentioning a pullback functor.

`CategoryTheory.isIso_of_reflects_iso` is applied with all arguments explicit: left to instance
search its `IsIso` argument is demanded while the morphism is still a metavariable.

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

variable {X Z : Scheme.{u}}

/-- **The fibre of `α` over the residue field at a point of a closed subscheme on which `α`
becomes invertible is invertible.** -/
theorem isIso_residuePullback_of_isIso_pullback_of_isClosedImmersion (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] {F G : X.Modules} (α : F ⟶ G)
    (h : IsIso ((Scheme.Modules.pullback i).map α)) (z : Z) :
    IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField (i.base z))).map α) := by
  have h1 : IsIso ((Scheme.Modules.pullback (Z.fromSpecResidueField z)).map
      ((Scheme.Modules.pullback i).map α)) := by
    have := h
    infer_instance
  have h2 : IsIso ((Scheme.Modules.pullback (Z.fromSpecResidueField z ≫ i)).map α) :=
    (ModuleLimits.isIso_pullback_map_comp_iff _ _ _ rfl α).mp h1
  have h3 : IsIso ((Scheme.Modules.pullback (Spec.map (i.residueFieldMap z))).map
      ((Scheme.Modules.pullback (X.fromSpecResidueField (i.base z))).map α)) :=
    (ModuleLimits.isIso_pullback_map_comp_iff (Spec.map (i.residueFieldMap z))
      (X.fromSpecResidueField (i.base z)) (Z.fromSpecResidueField z ≫ i)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField i z) α).mpr h2
  have : IsIso (i.residueFieldMap z) :=
    Stacks.Thickenings.isIso_residueFieldMap_of_surjective_stalkMap i z
      (i.stalkMap_surjective z)
  have : (Scheme.Modules.pullback (Spec.map (i.residueFieldMap z))).IsEquivalence :=
    AffineBaseChangeIso.isEquivalence_pullback (Spec.map (i.residueFieldMap z))
  exact @isIso_of_reflects_iso _ _ _ _ _ _
    ((Scheme.Modules.pullback (X.fromSpecResidueField (i.base z))).map α)
    (Scheme.Modules.pullback (Spec.map (i.residueFieldMap z))) h3 inferInstance

/-- **The image of a closed subscheme on which `α` becomes invertible lies in the stalkwise
isomorphism locus of `α`.** -/
theorem subset_stalkIsoLocus_range_of_isIso_pullback (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] {F G : X.Modules} [G.IsFiniteType]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G]
    (α : F ⟶ G) (h : IsIso ((Scheme.Modules.pullback i).map α)) :
    Set.range i.base ⊆ stalkIsoLocus α := by
  rintro x ⟨z, rfl⟩
  exact mem_stalkIsoLocus_of_isIso_residuePullback_of_flf α (i.base z)
    (isIso_residuePullback_of_isIso_pullback_of_isClosedImmersion i α h z)

/-- **A morphism of finite locally free modules which becomes an isomorphism on a closed
subscheme is an isomorphism over an open neighbourhood of that subscheme.**

This is the statement the essential surjectivity half of [Stacks, Tag 0EXD] consumes: a
trivialisation of the restriction of a module to the exceptional fibre extends to a
trivialisation over a neighbourhood of it. -/
theorem exists_isIso_restrictFunctor_map_of_isIso_pullback_isClosedImmersion (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] {F G : X.Modules} [F.IsFiniteType]
    [hG : _root_.SheafOfModules.IsCoherent G]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G]
    (α : F ⟶ G) (h : IsIso ((Scheme.Modules.pullback i).map α)) :
    ∃ U : X.Opens, Set.range i.base ⊆ (U : Set X) ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  have : G.IsFiniteType := hG.isFiniteType
  exact exists_isIso_restrictFunctor_map_of_subset_stalkIsoLocus α _
    (subset_stalkIsoLocus_range_of_isIso_pullback i α h)

/-- **A morphism of finite locally free modules on a locally Noetherian scheme which becomes an
isomorphism on a closed subscheme is an isomorphism over an open neighbourhood of that
subscheme.**

This is the form in which the essential surjectivity half of [Stacks, Tag 0EXD] consumes the
statement, once the Noetherian reduction of [Stacks, Tag 0B8W] has been performed: on a locally
Noetherian scheme a finite locally free module is coherent by [Stacks, Tag 01XZ], so no
coherence or finite type hypothesis has to be carried. -/
theorem exists_isIso_restrictFunctor_map_of_isIso_pullback_of_isLocallyNoetherian (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsLocallyNoetherian X]
    {F G : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G]
    (α : F ⟶ G) (h : IsIso ((Scheme.Modules.pullback i).map α)) :
    ∃ U : X.Opens, Set.range i.base ⊆ (U : Set X) ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  have hF : _root_.SheafOfModules.IsCoherent F := inferInstance
  have : F.IsFiniteType := hF.isFiniteType
  exact exists_isIso_restrictFunctor_map_of_isIso_pullback_isClosedImmersion i α h

end Stacks.AlgebraicGeometry.IsoLocus

end
