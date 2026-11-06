module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverseSupplement
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullbackSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# Stacks 04CQ at an arbitrary fibre product square

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, in which `Z'` is a closed subspace of `X'` and `Z` is a closed subspace of `X`, with `i`
and `i'` the inclusions.  [Stacks Project, Tag 04CQ] asserts that the canonical map
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is surjective, and an isomorphism when
`g` is flat.  This file proves both clauses for such a square.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean` prove the two clauses
for the *canonical* fibre product square, the one whose upper subspace is the inverse image
`g⁻¹(Z')` of [Stacks Project, Tag 083Q] and whose vertical morphism is the projection
`g⁻¹(Z') ⟶ Z'`.  The square of the tag is any cartesian one, and a closed subspace `Z ⊆ X`
fitting into it need not be presented as that inverse image.  The content of this file is that
it nevertheless *is* that inverse image, on the nose and not merely up to isomorphism, so that
the two clauses proved for that inverse image apply to it verbatim.

The reduction has two steps, and both are forced.  A leg of a cartesian square of presheaves has
as range the inverse image of the range of the opposite leg
(`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`), and the range of the inclusion of
a subfunctor is that subfunctor; so `Z = g⁻¹(Z')` as subfunctors of `X`, hence as closed
subspaces, the closedness being a proposition.  The vertical morphism is then pinned down too:
it and the projection `g⁻¹(Z') ⟶ Z'` have the same composite with `i'`, by the square's own
commutativity and `CategoryTheory.Subfunctor.fromPreimage_ι`, and `i'` is a monomorphism.

## Main results

* `AlgebraicGeometry.Space.closedSubspaces_eq_preimageSubspace_of_isPullback`: the upper closed
  subspace of a cartesian square is the inverse image of the lower one.
* `AlgebraicGeometry.Space.vertical_eq_preimageProjection_of_isPullback`: its vertical morphism
  is the projection of that inverse image.
* `AlgebraicGeometry.Space.epi_conormalMap_of_isPullback`: **the surjectivity clause of
  [Stacks Project, Tag 04CQ]** at an arbitrary fibre product square of closed immersions.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_isPullback_of_isFlat`: **the flat clause of
  [Stacks Project, Tag 04CQ]** at an arbitrary fibre product square of closed immersions.

## Implementation notes

**Why the cartesian hypothesis is taken at the level of presheaves.**  The square is required to
be cartesian as a square of presheaves on the big fppf site, `IsPullback Z.1.ι f.hom g.hom Z'.1.ι`,
rather than in the category of algebraic spaces.  That is the right reading and not a weakening:
the fibre product of algebraic spaces is computed as the fibre product of presheaves — which is
exactly what `AlgebraicGeometry.Space.isAlgebraicSpace_pullback` is for, and what
`CategoryTheory.Subfunctor.isPullback_preimage` of Stacks 083Q delivers for the inverse image —
so a square of algebraic spaces is a fibre product square precisely when its underlying square
of presheaves is cartesian.  Taking the hypothesis there also avoids asking whether the
inclusion of the full subcategory of algebraic spaces preserves the pullback, which is a
question about the ambient category and not about this tag.

**Why the subspaces stay closed.**  Stacks 04CQ is stated for a square whose horizontal arrows
are immersions, and this file, like the two it builds on, carries the closed case.  An earlier
revision of this paragraph gave as the reason that no canonical map exists at a square of
non-closed immersions, so that there was "nothing for 04CQ to be a statement about".  **That is
no longer true**: `AlgebraicGeometry.Space.conormalMapOfImmersions` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean` is the canonical
map of [Stacks Project, Tag 04CP] for a commutative square of arbitrary immersions, carrying no
hypothesis beyond the commutativity of the square, and
`AlgebraicGeometry.Space.epi_conormalMapOfImmersions_of_epi` and
`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isIso` reduce the two clauses of
Stacks 04CQ at that generality to the degree-one map
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`.  What is still missing is not the map
but the input, and it is a statement about sheaves of ideals on `X`.

**What the immersion case still needs.**  By the naturality of
`AlgebraicGeometry.Space.squarePullbackCompIso` the degree-one square map is the inverse image
along `i` of the single map of sheaves of ideals
`AlgebraicGeometry.Space.kernelIdealSquareMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMap.lean`, so what both
clauses need at a fibre product square of immersions is that `g^*(Ker((i')^♯)) ⟶ Ker(i^♯)`
becomes surjective, respectively invertible, after inverse image along `i`.  The inverse image
cannot be dropped: that file exhibits a cartesian square of immersions at which the map itself is
not surjective while the tag's conclusion holds, because `Z` is empty there.  So the statement has
to be read on an open subspace `V ⊆ X` in which `Z` is closed and which `g` carries into an open
subspace of `X'` in which `Z'` is closed — for instance
`V = (X ∖ ∂Z) ∩ g⁻¹(X' ∖ ∂Z')`, which contains `Z` because `g(i(Z)) ⊆ Z'` — where the square of
`Z ⊆ V` over `Z' ⊆ X' ∖ ∂Z'` is cartesian with *closed* subspaces and the clauses of this file
apply verbatim.  Three things are needed to run that reduction and none of them is present:

* the conormal module of an immersion through an **arbitrary** ambient open subspace, rather than
  only through the canonical `X ∖ ∂Z` of `AlgebraicGeometry.Space.immersionAmbient`.  This is one
  instantiation away: `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso` is stated
  for any cartesian square with étale transverse arrow, and taking that arrow to be the inclusion
  of `V` gives it, exactly as
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` takes it to be the inclusion of
  `X ∖ ∂Z`;
* the open subspace `V` itself: the intersection of two open subspaces of an algebraic space and
  the inverse image of an open subspace along `g`, with `Z` closed in the result;
* the compatibility of `AlgebraicGeometry.Space.kernelIdealSquareMap` with restricting
  the ambient space along the inclusion of `V`.  The sheaves do restrict —
  `AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq` is an equality, not merely
  an isomorphism — but that the *map* restricts to the corresponding map of the restricted square
  is not proved.

The first of the two identifications that the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapDegreePropagation.lean` named as
missing for the passage to the immersion case is discharged above, by
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf_preimageSubspace_of_isPullback`;
the second, the degree-one agreement of
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` with
`AlgebraicGeometry.Space.idealSheafMap`, **is now also discharged**, by
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`, stated for
`AlgebraicGeometry.Space.kernelIdealSquareMap` — of which that ambient map is the second factor
— because the ambient map alone has no source in common with
`AlgebraicGeometry.Space.idealSheafMap`.

Both identifications are therefore in.  Reading the closed clauses of this file as clauses about
`AlgebraicGeometry.Space.conormalMapOfImmersions` is not done here, and is no longer blocked by a
missing identification: what it now needs is only the assembly, carrying those two equalities
through `AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap` and the
square comparison that relates `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` to
`AlgebraicGeometry.Space.kernelIdealSquareMap`.  No clause of this file is restated for it.

Note that the claim in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` that the open subspace `X ∖ ∂Z` and
the factorisation of an immersion through it (Stacks 04CE, 06EC) are absent from this
development is out of date: both are in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebra.lean`.  What is absent is the canonical
map, not the ambient open subspace.

## References

* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-! ### A cartesian square presents its upper subspace as an inverse image -/

/-- **The upper closed subspace of a fibre product square is the inverse image of the lower
one.**  If the square of inclusions and vertical morphisms is cartesian as a square of
presheaves, then `Z` is `g⁻¹(Z')` — not merely isomorphic to it, but equal as a subfunctor of
`X`, hence equal as a closed subspace.

A leg of a cartesian square of presheaves of types has as range the inverse image of the range
of the opposite leg (`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback`), and the range
of the inclusion of a subfunctor is that subfunctor. -/
theorem closedSubspaces_eq_preimageSubspace_of_isPullback
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι) :
    Z = preimageSubspace B S hS g Z' := by
  refine Subtype.ext ?_
  have h := Subfunctor.range_eq_preimage_of_isPullback hcart
  rwa [Subfunctor.range_ι, Subfunctor.range_ι] at h

/-- **The vertical morphism of a fibre product square is the projection of the inverse image.**
Once the upper subspace is known to be the inverse image `g⁻¹(Z')`, the vertical morphism of the
square is the projection `g⁻¹(Z') ⟶ Z'`: both have the same composite with the inclusion of
`Z'`, by the commutativity of the square and `CategoryTheory.Subfunctor.fromPreimage_ι`, and
that inclusion is a monomorphism. -/
theorem vertical_eq_preimageProjection_of_isPullback
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨(preimageSubspace B S hS g Z').1.toFunctor,
        (preimageSubspace B S hS g Z').2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X (preimageSubspace B S hS g Z') ≫ g =
      f ≫ subspaceInclusion B S hS X' Z') :
    f = preimageProjection B S hS g Z' := by
  refine ObjectProperty.hom_ext _ ((cancel_mono Z'.1.ι).mp ?_)
  have h := congrArg (fun k => k.hom) hsq
  exact h.symm.trans (Subfunctor.fromPreimage_ι Z'.1 g.hom).symm

/-- **The canonical inverse-image square is cartesian.**  This is
`CategoryTheory.Subfunctor.isPullback_preimage` of [Stacks Project, Tag 083Q], transposed, read
with the inverse image presented as a closed subspace.  It is what makes the cartesian
hypothesis of the two clauses below satisfiable, and it exhibits the clauses for the
canonical square as the instance of them at this square. -/
theorem isPullback_preimageSubspace (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1) :
    IsPullback (preimageSubspace B S hS g Z').1.ι
      (preimageProjection B S hS g Z').hom g.hom Z'.1.ι :=
  (Subfunctor.isPullback_preimage g.hom Z'.1).flip

/-- **The kernel ideal sheaf of the upper inclusion of a fibre product square is the defining
ideal sheaf of the inverse image.**  For a cartesian square of closed subspaces, the kernel ideal
sheaf `Ker(i^♯)` of the inclusion `i : Z ⟶ X` — the sheaf of ideals the conormal algebra of an
arbitrary morphism of `AlgebraicGeometry.Space.conormalAlgebra` is built from — is the defining
ideal sheaf of Stacks 03MB of the inverse image `g⁻¹(Z')`.

The two inputs are both already present: the kernel ideal sheaf of the inclusion of a closed
subspace is that subspace's defining ideal sheaf
(`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`, an equality by definition), and
the cartesian hypothesis makes `Z` the inverse image on the nose
(`AlgebraicGeometry.Space.closedSubspaces_eq_preimageSubspace_of_isPullback`).

This is recorded because the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapDegreePropagation.lean` names this
identification as one of two that a passage from the closed case to the immersion case would need
and asserts that the development carries no such passage outside the étale case.  For this first
identification that assertion is false, and the correction is this lemma; for the second one, the
degree-one agreement of `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` with
`AlgebraicGeometry.Space.idealSheafMap`, it is false as well, the correction being
`AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`. -/
theorem kernelIdealSheaf_eq_definingIdealSheaf_preimageSubspace_of_isPullback
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι) :
    kernelIdealSheaf B S hS (subspaceInclusion B S hS X Z) =
      definingIdealSheaf B S hS X (preimageSubspace B S hS g Z') := by
  obtain rfl := closedSubspaces_eq_preimageSubspace_of_isPullback B S hS Z Z' g f hcart
  rfl

/-! ### Stacks 04CQ at an arbitrary fibre product square -/

/-- **The surjectivity clause of [Stacks Project, Tag 04CQ].**  Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a fibre product square of algebraic spaces over `S` in which `Z ⊆ X` and `Z' ⊆ X'` are closed
subspaces and `i`, `i'` are their inclusions.  Then the canonical map of conormal modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is an epimorphism of `𝒪_Z`-modules.

This is `AlgebraicGeometry.Space.epi_conormalMap` released from the canonical inverse-image
square: by `AlgebraicGeometry.Space.closedSubspaces_eq_preimageSubspace_of_isPullback` the
cartesian hypothesis makes `Z` the inverse image `g⁻¹(Z')` and by
`AlgebraicGeometry.Space.vertical_eq_preimageProjection_of_isPullback` it makes `f` the
projection, after which the square's commutativity proof and the canonical one are proofs of the
same proposition.

The horizontal arrows are closed immersions, where the source takes immersions; the
implementation notes of this file record what the passage to the immersion case still needs. -/
@[stacks 04CQ "surjectivity, at an arbitrary fibre product square"]
theorem epi_conormalMap_of_isPullback
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι) :
    Epi (conormalMap B S hS Z Z' g f hsq) := by
  obtain rfl := closedSubspaces_eq_preimageSubspace_of_isPullback B S hS Z Z' g f hcart
  obtain rfl := vertical_eq_preimageProjection_of_isPullback B S hS Z' g f hsq
  exact epi_conormalMap B S hS g Z'

/-- **The flat clause of [Stacks Project, Tag 04CQ].**  For a fibre product square as in
`AgebraicGeometry.Space.epi_conormalMap_of_isPullback`, if `g` is flat — that is, if the
morphism of small étale ringed topoi it induces is flat in the sense of
[Stacks Project, Tag 04JB] — then the canonical map of conormal modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_conormalMap_of_isFlat` released from the canonical
inverse-image square, by the same two identifications. -/
@[stacks 04CQ "flat isomorphism, at an arbitrary fibre product square"]
theorem isIso_conormalMap_of_isPullback_of_isFlat
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hcart : IsPullback Z.1.ι f.hom g.hom Z'.1.ι)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (conormalMap B S hS Z Z' g f hsq) := by
  obtain rfl := closedSubspaces_eq_preimageSubspace_of_isPullback B S hS Z Z' g f hcart
  obtain rfl := vertical_eq_preimageProjection_of_isPullback B S hS Z' g f hsq
  exact isIso_conormalMap_of_isFlat B S hS g Z' hg

/-! ### The clauses for the canonical square are instances -/



end AlgebraicGeometry.Space

end
