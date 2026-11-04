module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatBaseChange

/-!
# Surjectivity of the conormal module map of a fibre product square

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, in which `Z'` is a closed subspace of `X'` and `Z` is its inverse image `g⁻¹(Z')`, a closed
subspace of `X` by Stacks 083Q.  Stacks 04CQ asserts that the canonical map
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of conormal modules of Stacks 04CP is surjective.  This file proves
that clause.

The three steps are the ones the affine-chart computation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChange.lean` left open.  The map of
defining ideal sheaves `g^*𝓘' ⟶ 𝓘` is surjective on the sections over every commutative diagram
of étale scheme charts over `g` whose two charts are affine
(`AlgebraicGeometry.Space.surjective_idealSheafMap_val_app`); those charts of `X` are cover-dense
in the small étale site of `X`
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), so the map is locally
surjective, hence an epimorphism of sheaves of modules
(`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`); and the conormal module map is the
inverse image of it along the inclusion of `Z`, precomposed with an isomorphism, so it is an
epimorphism because the inverse image is a left adjoint.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_idealSheafMap`: the map `g^*𝓘' ⟶ 𝓘` of
  [Stacks Project, Tag 04CP] attached to the fibre product square is locally surjective on the
  small étale site of `X`.
* `AlgebraicGeometry.Space.epi_idealSheafMap`: consequently it is an epimorphism of
  `𝒪_X`-modules.
* `AlgebraicGeometry.Space.conormalMap_eq`: the canonical map of conormal modules read as the
  composite of the comparison isomorphism with the inverse image of the map of defining ideal
  sheaves.  This is the defining equation of `AlgebraicGeometry.Space.conormalMap`, stated so
  that the two spellings of its target are crossed once and for all; see the implementation
  notes.
* `AlgebraicGeometry.Space.epi_conormalMap`: **the surjectivity clause of
  [Stacks Project, Tag 04CQ]**.  Its input, that an epimorphic map of defining ideal sheaves
  gives an epimorphic map of conormal modules over an arbitrary commutative square, is
  `AlgebraicGeometry.Space.epi_conormalMap_of_epi_idealSheafMap`.
* `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`: **the exactness at the right term
  of [Stacks Project, Tag 06BD]**, which is that clause at the fibre product square of a pair of
  closed subspaces `Z ⊆ Y ⊆ X`.

## Implementation notes

**Local surjectivity is read off the image sieve.**  `CategoryTheory.Presheaf.imageSieve` of a
section is a sieve, hence downward closed, so it suffices that it contain the morphisms out of
the charts carrying an affine chart diagram — on such a chart the map of sections is surjective,
so the restricted section is in its image.  That containment is exactly the hypothesis of
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`, and the chart diagram the
surjectivity statement consumes is assembled from the witness of
`AlgebraicGeometry.Space.HasAffineChartDiagram` on the nose.

**Why the defining equation of the conormal map pins its target.**
`AlgebraicGeometry.Space.conormalMap` is *defined* as
`conormalPullbackComparison ≫ (modulePullback i).map idealSheafMap`, so the equation below is a
single delta reduction — but its two sides are not syntactically equal, because the inverse
image of the defining ideal sheaf along the inclusion of `Z` is written
`AlgebraicGeometry.Space.conormalModule` in the declared type of `conormalMap` and written out
in the type of the second factor.  Those are the same object by
`AlgebraicGeometry.Space.conormalModule_eq`, and crossing between them inside a composition
is what the default heartbeat budget does not survive: comparing two `CategoryStruct.comp`
applications whose middle object has two spellings sends the definitional unifier through the
composition law of the category of sheaves of modules.  Crossing it *outside* the composition
costs nothing.  So the equation below ascribes the type of the second factor with
`AlgebraicGeometry.Space.conormalModule` as its target, which fixes the target of the
composition to the spelling `conormalMap` uses, and both sides are then equal at reducible
transparency.  Consumers rewrite with the equation rather than unfold the definition, and the
epimorphism hypotheses they feed to `CategoryTheory.epi_comp'` are stated with the same
ascription.

**The fibre product is taken as an inverse image**, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChange.lean`: "the square is a fibre
product" is expressed by *being* the configuration `g⁻¹(Z') ⊆ X` over `Z' ⊆ X'`, with the
commutative square supplied by `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare`, which
assumes nothing about `g`.

## What is not proved

* **The flat clause of Stacks 04CQ is not proved**, and nothing here bears on it.  It asserts
  that the map is an isomorphism when `g` is flat, which needs the injectivity of
  `g^*𝓘' ⟶ g^*𝒪_{X'} = 𝒪_X`, that is the exactness of the inverse image of modules along a flat
  morphism of algebraic spaces.  No statement in this development establishes it, and the
  scheme-level clause of Stacks 0473 to which the source reduces it is not formalized either
  (`StacksFrontier/AlgebraicGeometry/Conormal/SquareEpi.lean` carries only
  `@[stacks 0473 "surjectivity"]`).
* **The exactness in the middle of Stacks 06BD is not proved.**  The two other clauses of the
  conormal sequence `𝒞_{Y/X} ⊗ 𝒪_Z ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` are: exactness at the right term,
  which is `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces` below, and the vanishing of
  the composite, which is
  `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_closedSubspaces_eq_zero` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleClosedSubspacesComplex.lean`.  The first
  map of the sequence is the map of Stacks 04CP of the square of `Z ⊆ X` over `Y ⊆ X` with the
  identity of `X` as its morphism of ambient spaces, so it does exist; the statement that it does
  not, which this section used to make, was wrong.  What is missing is only the exactness at
  `𝒞_{Z/X}`, and it is not formalized at the scheme level either
  (`StacksFrontier/AlgebraicGeometry/Conormal/ConormalSequence.lean` carries only
  `@[stacks 062S "exactness at the right term: the canonical map 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} is epi"]`).

## References

* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-! ### The map of defining ideal sheaves of a fibre product square is an epimorphism -/

/-- **The canonical map of defining ideal sheaves of a fibre product square is locally
surjective.**  For a closed subspace `Z'` of `X'` and a morphism `g : X ⟶ X'`, the map
`g^*𝓘' ⟶ 𝓘` of [Stacks Project, Tag 04CP] attached to the fibre product square — the one with
`g⁻¹(Z') ⊆ X` upstairs and the projection as its vertical morphism — is locally surjective on
the small étale site of `X`.

Over a chart of `X` carrying an affine chart diagram over `g` the map is surjective on sections
by `AlgebraicGeometry.Space.surjective_idealSheafMap_val_app`, so the image sieve of any section
contains the morphisms out of such charts; it is therefore a covering sieve by
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`. -/
theorem isLocallySurjective_idealSheafMap (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).map
        (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z')
          (conormalEtaleRestrictionSquare B S hS g Z')).val) := by
  constructor
  intro U s
  refine mem_topology_of_hasAffineChartDiagram B S hS g U _ ?_
  intro W a hW
  obtain ⟨hWaff, V, q, hcomm, hVaff⟩ := hW
  -- The two affineness assertions are the instance arguments of the chartwise surjectivity.
  have := hWaff
  have := hVaff
  exact surjective_idealSheafMap_val_app B S hS g Z'
    { U := W, V := V, g := q, comm := hcomm.symm } _

/-- **The canonical map of defining ideal sheaves of a fibre product square is an
epimorphism.**  A locally surjective morphism of sheaves of modules is an epimorphism by
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`, which is the clause of
[Stacks Project, Tag 01AH] for sheaves of modules. -/
theorem epi_idealSheafMap (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1) :
    Epi (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_idealSheafMap B S hS g Z')

/-! ### From the ideal sheaves to the conormal modules -/

section Square

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The defining equation of `AlgebraicGeometry.Space.conormalMap`**: the canonical map of
conormal modules of a commutative square is the comparison isomorphism
`f^*𝒞_{Z'/X'} ⟶ i^*g^*𝓘'` of `AlgebraicGeometry.Space.conormalPullbackComparison` followed by
the inverse image along the inclusion of `Z` of the map `g^*𝓘' ⟶ 𝓘` of
`AlgebraicGeometry.Space.idealSheafMap`.

The target of the second factor is ascribed as `AlgebraicGeometry.Space.conormalModule`, which
it is by `AlgebraicGeometry.Space.conormalModule_eq`; the implementation notes of this file
record why the ascription must be made there and not around the composite. -/
theorem conormalMap_eq
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    conormalMap B S hS Z Z' g f hsq =
      conormalPullbackComparison B S hS Z Z' g f hsq ≫
        (show (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              ((modulePullback B S hS g).obj
                (definingIdealSheaf B S hS X' Z').toSheafOfModules) ⟶
            conormalModule B S hS X Z from
          (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            (idealSheafMap B S hS Z Z' g f hsq)) := by
  delta conormalMap
  with_reducible rfl

end Square

/-! ### The surjectivity clause of Stacks 04CQ -/

/-- **The surjectivity clause of [Stacks Project, Tag 04CQ], for closed immersions.**  Let `Z'`
be a closed subspace of an algebraic space `X'` and let `g : X ⟶ X'` be a morphism of algebraic
spaces.  For the fibre product square — the one whose upper closed subspace is the inverse image
`g⁻¹(Z') ⊆ X` of [Stacks Project, Tag 083Q] and whose vertical morphism is the projection
`g⁻¹(Z') ⟶ Z'` — the canonical map of conormal modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of [Stacks Project, Tag 04CP] is an epimorphism of
`𝒪_{g⁻¹(Z')}`-modules.

The source states the lemma for immersions and reduces it to closed immersions at the start of
the proof of [Stacks Project, Tag 04CP]; the closed case is the one this development carries,
for the reasons recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean`.  The flat clause of the tag is not
proved; see the "What is not proved" section of this file.

Surjectivity of a map of modules on the small étale site means that the map is an epimorphism,
which by [Stacks Project, Tag 01AH] is local surjectivity; the chartwise statement behind it is
`AlgebraicGeometry.Space.surjective_idealSheafMap_val_app`. -/
@[stacks 04CQ "surjectivity"]
theorem epi_conormalMap (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1) :
    Epi (conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) :=
  epi_conormalMap_of_epi_idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')
    (epi_idealSheafMap B S hS g Z')

/-- **Exactness at the right term of [Stacks Project, Tag 06BD].**  Let `Y` and `Z` be closed
subspaces of an algebraic space `X` with `Z ⊆ Y`.  The canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of
[Stacks Project, Tag 04CP], the right-hand map of the conormal sequence of the pair, is an
epimorphism.

This is the surjectivity clause of [Stacks Project, Tag 04CQ] at the fibre product square whose
morphism of ambient spaces is the inclusion `j : Y ⟶ X`: the inverse image `j⁻¹(Z)` is `Z` read
as a closed subspace of `Y`, and `𝒞_{Z/Y}` is its conormal module there.  The subspace of `Y` is
taken as that inverse image rather than as `Z` itself because this development has no
composition of closed subspaces, so no closed subspace of `Y` is attached to `Z` by any other
route.  The hypothesis `Z ⊆ Y` is what makes that inverse image the subspace the source calls
`Z`, and it is carried for that reason alone: the proof is the instance of Stacks 04CQ, which
holds for any pair, so the hypothesis is not used and its name is prefixed accordingly.

The exactness in the middle is not proved; see the "What is not proved" section of this file,
which also names the composite-is-zero clause. -/
@[stacks 06BD "exactness at the right term"]
theorem epi_conormalMap_closedSubspaces (Y Z : ClosedSubspaces B S hS X.1)
    (_hZY : Z.1 ≤ Y.1) :
    Epi (conormalMap B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
      (subspaceInclusion B S hS X Y)
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) :=
  epi_conormalMap B S hS (subspaceInclusion B S hS X Y) Z

end AlgebraicGeometry.Space

end
