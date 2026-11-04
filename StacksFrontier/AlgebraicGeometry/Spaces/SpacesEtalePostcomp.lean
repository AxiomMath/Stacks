module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# Postcomposition of spaces-étale sites along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  If `W ⟶ X` is étale then so is `W ⟶ X ⟶ Y`, by Stacks 03FT, so
postcomposition with `f` is a functor

`j_{spaces} : X_{spaces, étale} ⥤ Y_{spaces, étale}`, `(φ : W ⟶ X) ↦ (φ ≫ f : W ⟶ Y)`,

leaving the underlying algebraic space of every object and of every morphism unchanged.  This
file constructs that functor and shows it is continuous, so that restriction along it carries
spaces-étale sheaves on `Y` to spaces-étale sheaves on `X`.

This is the spaces-étale counterpart of `AlgebraicGeometry.Space.smallEtalePostcomp`, the
functor `j` of Stacks 03LP, which it becomes after restriction to the étale *scheme* charts:
`AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtalePostcomp` is the postcomposition functor.

## Main results

* `AlgebraicGeometry.Space.spacesEtalePostcomp_comp_toSpaces`: postcomposition leaves the
  underlying algebraic space unchanged, on objects and on morphisms at once, and holds by `rfl`.
* `AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`: postcomposition of
  spaces-étale sites restricts along the comparison functor of Stacks 03G1 to postcomposition of
  small étale sites, again by `rfl`.
* `AlgebraicGeometry.Space.isContinuous_spacesEtalePostcomp`: postcomposition is continuous for
  the spaces-étale topologies.

## Implementation notes

Both the covering condition and the fibre products of a spaces-étale site are detected on the
underlying algebraic spaces — `AlgebraicGeometry.Space.SpacesEtale.IsCovering` is joint
surjectivity on points of `AlgebraicGeometry.Space.SpacesEtale.toSpaces`, and
`AlgebraicGeometry.Space.SpacesEtale.instPreservesPullbacksToSpaces` together with the fact that
the inclusion into the slice creates fibre products — so both inputs to continuity follow from
`spacesEtalePostcomp_comp_toSpaces` without any computation, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePostcomp.lean`.  In particular no base-change
stability of the chosen covering families is needed, which is why
`Stacks.Sites.isContinuous_toGrothendieck_of_le_comap` is used rather than
`CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`.

Cocontinuity of `j_{spaces}` is *not* proved here.  Its small étale analogue,
`AlgebraicGeometry.Space.smallEtalePostcomp_isCocontinuous`, rests on the comparison of the two
slices `AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`, and the corresponding
comparison of the slice of `X_{spaces, étale}` at `W` with the slice of `Y_{spaces, étale}` at
`jW` has not been constructed.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Postcomposition of an object étale over `X` with an étale morphism `f : X ⟶ Y`, as a
functor between the spaces-étale sites.  The underlying algebraic space and the underlying
morphisms of algebraic spaces are unchanged. -/
noncomputable def spacesEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SpacesEtale B S hS X ⥤ SpacesEtale B S hS Y :=
  (IsEtaleOver B S hS Y).lift (SpacesEtale.inclusion B S hS X ⋙ Over.map f)
    (fun W ↦ isEtale_comp B S hS W.property hf)

/-- On objects, postcomposition replaces the structure morphism `W ⟶ X` by its composite
with `f`. -/
theorem spacesEtalePostcomp_obj_hom (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (W : SpacesEtale B S hS X) :
    ((spacesEtalePostcomp B S hS f hf).obj W).1.hom = W.1.hom ≫ f :=
  rfl

/-- Postcomposition leaves the underlying algebraic space over `S` unchanged, on objects and
on morphisms at once. -/
theorem spacesEtalePostcomp_comp_toSpaces (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    spacesEtalePostcomp B S hS f hf ⋙ SpacesEtale.toSpaces B S hS Y =
      SpacesEtale.toSpaces B S hS X :=
  rfl

/-- **The comparison square of Stacks 03G1 for postcomposition.** The restriction of
spaces-étale postcomposition to the étale scheme charts is small étale postcomposition: an
étale chart `U ⟶ X` of `X`, read as an algebraic space étale over `X` and then postcomposed
with `f`, is the chart `U ⟶ X ⟶ Y` of `Y` read as an algebraic space étale over `Y`.

Both sides leave the underlying object of the big fppf site of `S` unchanged, and the structure
morphism is in both cases the composite, so the equality holds by `rfl`. -/
theorem comparisonFunctor_comp_spacesEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    comparisonFunctor B S hS X ⋙ spacesEtalePostcomp B S hS f hf =
      smallEtalePostcomp B S hS f hf ⋙ comparisonFunctor B S hS Y :=
  rfl

/-- Postcomposition preserves fibre products of spaces-étale sites: fibre products are created
by the inclusion into the slice and computed on the underlying algebraic spaces, which
postcomposition leaves unchanged. -/
instance preservesPullbacks_spacesEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    PreservesLimitsOfShape WalkingCospan (spacesEtalePostcomp B S hS f hf) :=
  have : ReflectsLimitsOfShape WalkingCospan (SpacesEtale.toSpaces B S hS Y) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan
      (spacesEtalePostcomp B S hS f hf ⋙ SpacesEtale.toSpaces B S hS Y) := by
    change PreservesLimitsOfShape WalkingCospan (SpacesEtale.toSpaces B S hS X)
    infer_instance
  preservesLimitsOfShape_of_reflects_of_preserves _ (SpacesEtale.toSpaces B S hS Y)

/-- A jointly point-surjective family of algebraic spaces étale over `X` is carried by
postcomposition to a jointly point-surjective family of algebraic spaces étale over `Y`: the
covering condition only sees the underlying algebraic spaces and their points, which
postcomposition leaves unchanged. -/
theorem precoverage_le_comap_spacesEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    SpacesEtale.precoverage B S hS X ≤
      (SpacesEtale.topology B S hS Y).toPrecoverage.comap
        (spacesEtalePostcomp B S hS f hf) := by
  intro W R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    ← PreZeroHypercover.presieve₀_map]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨E.map (spacesEtalePostcomp B S hS f hf), rfl, hE⟩

/-- Postcomposition along an étale morphism of algebraic spaces is continuous for the
spaces-étale topologies, so restriction along it carries sheaves on the spaces-étale site of
`Y` to sheaves on that of `X`. -/
instance isContinuous_spacesEtalePostcomp (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (spacesEtalePostcomp B S hS f hf).IsContinuous
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) :=
  Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
    (precoverage_le_comap_spacesEtalePostcomp B S hS f hf)

end AlgebraicGeometry.Space

end
