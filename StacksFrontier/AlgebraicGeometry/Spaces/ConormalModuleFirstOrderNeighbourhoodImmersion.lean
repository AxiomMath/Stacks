module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderNeighbourhoodIdealPow
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# The conormal module of an immersion in its first order neighbourhood

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  It factors as a closed immersion `Z ⟶ X ∖ ∂Z` followed by the inclusion of the open
complement of the boundary of its image ([Stacks Project, Tag 04CE]), and the first order
infinitesimal neighbourhood `Z ⊆ Z'` of [Stacks Project, Tag 05ZV] is the closed subspace of
`X ∖ ∂Z` cut out by the square of the defining ideal of `Z` there.  [Stacks Project, Tag 05ZX]
asserts that the map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP], induced by the square
```
Z --→ Z'
|     |
Z --→ X
```
is an isomorphism.  This file constructs that map for the conormal modules
`AlgebraicGeometry.Space.conormalModuleOfImmersion` of [Stacks Project, Tag 04CN] — modules on
`Z` itself — and proves it invertible.

## Main definitions

* `AlgebraicGeometry.Space.immersionLiftClosedSubspace`: the factorisation `Z ⟶ Z'` of an
  immersion through a closed subspace `Z'` of `X ∖ ∂Z` containing its image; it is a closed
  immersion (`AlgebraicGeometry.Space.isClosedImmersion_immersionLiftClosedSubspace`), so it has
  a conormal module.
* `AlgebraicGeometry.Space.immersionLiftConormalMap`: the map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of
  [Stacks Project, Tag 04CP] for the square above.

## Main results

* `AlgebraicGeometry.Space.isIso_immersionLiftConormalMap`: **[Stacks Project, Tag 05ZX]**.

## Implementation notes

**The map is the one of the proof of [Stacks Project, Tag 04CP].**  That proof replaces both
immersions of the square by closed immersions into open subspaces compatible with the vertical
morphism.  For `i` the open subspace is `X ∖ ∂Z`, through which
`AlgebraicGeometry.Space.conormalModuleOfImmersion` is defined; for `Z ⟶ Z'` it is the
complement in `Z'` of the boundary of `Z`, which is the open subspace that the same definition
uses for that immersion, and it maps into `X ∖ ∂Z` through `Z'`
(`AlgebraicGeometry.Space.immersionLiftAmbientι`).  The resulting square of closed subspaces has
its map of defining ideal sheaves `AlgebraicGeometry.Space.idealSheafMap`, and the conormal map is
its inverse image along the closed factorisation of `Z ⟶ Z'`, read through the composition
comparison of [Stacks Project, Tag 03LU].

**The proof reduces to the closed case.**  The vertical morphism `Z' ∖ ∂Z ⟶ X ∖ ∂Z` is the open
inclusion `Z' ∖ ∂Z ⟶ Z'` followed by `Z' ⟶ X ∖ ∂Z`, and the image of `Z` in `Z' ∖ ∂Z` is the
inverse image of its image in `Z'`
(`AlgebraicGeometry.Space.immersionRangeSubspace_immersionLiftClosedSubspace_eq`).  The map of
defining ideal sheaves therefore splits, by the composition law
`AlgebraicGeometry.Space.idealSheafMap_comp`, into the one along the étale open inclusion, which
is invertible by [Stacks Project, Tag 04CO], and the inverse image of the one along `Z' ⟶ X ∖ ∂Z`,
whose inverse image to `Z` is invertible by the closed case
`AlgebraicGeometry.Space.isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood`.

**The neighbourhood is a hypothesis.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderNeighbourhood.lean`, `Z'` is a
closed subspace of `X ∖ ∂Z` whose defining ideal sheaf is the square of that of `Z`
(`AlgebraicGeometry.Space.IsFirstOrderNeighbourhood`); the statement holds for every such `Z'`.

## References

* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Immersion

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i)
    (Z' : ClosedSubspaces B S hS (immersionAmbient B S hS hX hZ i hi).1)
    (hle : (immersionRangeSubspace B S hS hX hZ i hi).1 ≤ Z'.1)

/-- The factorisation `Z₀ ⟶ Z'` of an immersion through a closed subspace `Z'` of the complement
of its boundary containing its image. -/
noncomputable def immersionLiftClosedSubspace : Z₀ ⟶ Z'.1.toFunctor :=
  Subfunctor.lift (boundaryComplementLift B S hS hX hZ i hi) hle

/-- The factorisation through `Z'` followed by the inclusion of `Z'` is the closed factorisation
of the immersion. -/
theorem immersionLiftClosedSubspace_comp_ι :
    immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle ≫ Z'.1.ι =
      boundaryComplementLift B S hS hX hZ i hi :=
  rfl

/-- The factorisation of an immersion through a closed subspace of the complement of its
boundary containing its image is a closed immersion. -/
theorem isClosedImmersion_immersionLiftClosedSubspace :
    IsClosedImmersion B S hS (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) :=
  isClosedImmersion_of_comp_mono B S hS _ Z'.1.ι
    (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi)

/-- The factorisation of an immersion through a closed subspace of the complement of its boundary
containing its image is an immersion. -/
theorem isImmersion_immersionLiftClosedSubspace :
    IsImmersion B S hS (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) :=
  isImmersion_of_isClosedImmersion B S hS
    (isClosedImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)

/-- The factorisation of an immersion through a closed subspace `Z'` of the complement of its
boundary containing its image, read as a morphism into the inverse image in `Z'` of that
image. -/
noncomputable def immersionLiftPreimage :
    (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)).1.toFunctor,
        (preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)).2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (Subfunctor.lift (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
    (by rintro U _ ⟨x, rfl⟩; exact ⟨x, rfl⟩))

/-- The inclusion into `Z'` of the complement, inside `Z'`, of the boundary of the immersion
`Z₀ ⟶ Z'`: the open subspace of `Z'` in which [Stacks Project, Tag 04CN] takes the conormal
module of that immersion. -/
noncomputable def immersionLiftAmbientι :
    immersionAmbient B S hS Z'.2.1 hZ (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (boundaryComplement B S hS Z'.1.toFunctor
    (Set.range (pointsMap B S hS Z₀ (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)))).ι

/-- The inclusion of the complement of the boundary of `Z ⟶ Z'` into `Z'` is étale, being an
open immersion. -/
theorem isEtale_immersionLiftAmbientι :
    IsEtale B S hS (immersionLiftAmbientι B S hS hX hZ i hi Z' hle).hom :=
  isEtale_of_isOpenImmersion B S hS (isOpenSubspace_boundaryComplement B S hS Z'.2.1
    (isLocallyClosed_range_pointsMap_of_isImmersion B S hS Z'.2.1
      (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
      (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle))).2

/-- The image of `Z₀` in the complement of its boundary in `Z'` is the inverse image of the
image of `Z₀` in `X ∖ ∂Z`. -/
theorem immersionRangeSubspace_immersionLiftClosedSubspace_eq :
    immersionRangeSubspace B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) =
      preimageSubspace B S hS (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
        (preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)) := by
  refine Subtype.ext (Subfunctor.ext (funext fun U => Set.ext fun x => ⟨?_, ?_⟩))
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext (Subtype.ext hz)⟩

/-- The morphism from the image of `Z₀` in the complement of its boundary in `Z'` to the inverse
image in `Z'` of the image of `Z₀` in `X ∖ ∂Z`. -/
noncomputable def immersionLiftRangeHom :
    (⟨(immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)).1.toFunctor,
        (immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)).2.1⟩ :
        AlgebraicSpaces B S hS) ⟶
      (⟨(preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)).1.toFunctor,
        (preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)).2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (Subfunctor.lift
    ((immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)).1.ι ≫
      (immersionLiftAmbientι B S hS hX hZ i hi Z' hle).hom)
    (by rintro U _ ⟨⟨_, ⟨z, rfl⟩⟩, rfl⟩; exact ⟨z, rfl⟩))

/-- The square of closed subspaces along the open inclusion `Z' ∖ ∂Z ⟶ Z'` commutes. -/
theorem immersionLiftRangeHom_square :
    subspaceInclusion B S hS _ (immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)) ≫
        immersionLiftAmbientι B S hS hX hZ i hi Z' hle =
      immersionLiftRangeHom B S hS hX hZ i hi Z' hle ≫
        subspaceInclusion B S hS _ (preimageSubspace B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)) :=
  rfl

/-- The square of closed subspaces along `Z' ∖ ∂Z ⟶ X ∖ ∂Z` commutes. -/
theorem immersionLiftRangeHom_square_comp :
    subspaceInclusion B S hS _ (immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)) ≫
        immersionLiftAmbientι B S hS hX hZ i hi Z' hle ≫
          subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z' =
      (immersionLiftRangeHom B S hS hX hZ i hi Z' hle ≫
        preimageProjection B S hS
          (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
          (immersionRangeSubspace B S hS hX hZ i hi)) ≫
        subspaceInclusion B S hS _ (immersionRangeSubspace B S hS hX hZ i hi) :=
  rfl

/-- The closed factorisation of `Z ⟶ Z'` followed by `Z' ∖ ∂Z ⟶ X ∖ ∂Z` is the closed
factorisation of `i`. -/
theorem immersionClosedFactorization_comp_immersionLiftAmbientι :
    immersionClosedFactorization B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) ≫
      immersionLiftAmbientι B S hS hX hZ i hi Z' hle ≫
        subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z' =
    immersionClosedFactorization B S hS hX hZ i hi :=
  rfl

/-- **The canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP]** for an immersion
`i : Z ⟶ X` and a closed subspace `Z'` of `X ∖ ∂Z` containing the image of `Z`, attached to the
square with `𝟙 Z` on the left and `Z' ⟶ X` on the right.  Both modules are the conormal modules
`AlgebraicGeometry.Space.conormalModuleOfImmersion` of [Stacks Project, Tag 04CN], of `i` and of
the immersion `Z ⟶ Z'`.

As in the proof of [Stacks Project, Tag 04CP], the two immersions are replaced by closed
immersions into open subspaces compatible with the vertical morphism: `X ∖ ∂Z` for `i`, and the
complement of the boundary of `Z` in `Z'` for `Z ⟶ Z'`, which maps into `X ∖ ∂Z`.  The map is
the inverse image along the closed factorisation of `Z ⟶ Z'` of the map of defining ideal sheaves
`AlgebraicGeometry.Space.idealSheafMap` of the resulting square of closed subspaces, read through
the composition comparison of [Stacks Project, Tag 03LU]. -/
noncomputable def immersionLiftConormalMap :
    conormalModuleOfImmersion B S hS hX hZ i hi ⟶
      conormalModuleOfImmersion B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle) :=
  eqToHom (conormalModuleOfImmersion_eq B S hS hX hZ i hi) ≫
    eqToHom (congrArg (fun m => (modulePullback B S hS m).obj
        (definingIdealSheaf B S hS _ (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules)
      (immersionClosedFactorization_comp_immersionLiftAmbientι B S hS hX hZ i hi Z' hle).symm) ≫
    (modulePullbackCompIso B S hS
      (immersionClosedFactorization B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle))
      (immersionLiftAmbientι B S hS hX hZ i hi Z' hle ≫
        subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')).inv.app
      (definingIdealSheaf B S hS _ (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules ≫
    (modulePullback B S hS (immersionClosedFactorization B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle))).map
      (idealSheafMap B S hS
        (immersionRangeSubspace B S hS Z'.2.1 hZ
          (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
          (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle))
        (immersionRangeSubspace B S hS hX hZ i hi)
        (immersionLiftAmbientι B S hS hX hZ i hi Z' hle ≫
          subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
        (immersionLiftRangeHom B S hS hX hZ i hi Z' hle ≫
          preimageProjection B S hS
            (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
            (immersionRangeSubspace B S hS hX hZ i hi))
        (immersionLiftRangeHom_square_comp B S hS hX hZ i hi Z' hle)) ≫
    eqToHom (conormalModuleOfImmersion_eq B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)).symm

/-- A functor carries a threefold composite of morphisms with invertible images to a morphism with
invertible image. -/
private theorem isIso_map_comp_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (k : Y ⟶ Z) (hf : IsIso (F.map f))
    (hg : IsIso (F.map g)) (hk : IsIso (F.map k)) : IsIso (F.map (f ≫ g ≫ k)) := by
  rw [F.map_comp, F.map_comp]
  infer_instance

/-- The map of defining ideal sheaves along an étale morphism, at a square whose upper closed
subspace is the inverse image of the lower one, is an isomorphism; stated for any closed
subspace equal to that inverse image and any morphism completing the square. -/
private theorem isIso_idealSheafMap_of_eq_preimageSubspace {Y Y' : AlgebraicSpaces B S hS}
    (g : Y ⟶ Y') (hg : IsEtale B S hS g.hom) (W : ClosedSubspaces B S hS Y'.1) :
    ∀ (T : ClosedSubspaces B S hS Y.1), T = preimageSubspace B S hS g W →
      ∀ (f : (⟨T.1.toFunctor, T.2.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS))
        (hsq : subspaceInclusion B S hS Y T ≫ g = f ≫ subspaceInclusion B S hS Y' W),
        IsIso (idealSheafMap B S hS T W g f hsq) := by
  rintro T rfl f hsq
  obtain rfl : f = preimageProjection B S hS g W := by
    refine ObjectProperty.hom_ext _ ?_
    refine (cancel_mono W.1.ι).1 ?_
    exact (congrArg (fun m => m.hom) hsq).symm
  rw [idealSheafMap_eq_modulePullbackIsoEtaleModulePullback_hom_comp B S hS g hg W]
  exact IsIso.comp_isIso' (inferInstanceAs (IsIso (((modulePullbackIsoEtaleModulePullback B S hS
    g hg).app (definingIdealSheaf B S hS Y' W).toSheafOfModules).hom)))
    (Iso.isIso_hom (etaleIdealSheafRestrictionIso B S hS g hg W))

/-- The invertibility of `AlgebraicGeometry.Space.immersionLiftConormalMap` at a first order
neighbourhood, for any proof of the containment the map is built from. -/
private theorem isIso_immersionLiftConormalMap_of_le
    (h : IsFirstOrderNeighbourhood B S hS (immersionAmbient B S hS hX hZ i hi)
      (immersionRangeSubspace B S hS hX hZ i hi) Z') :
    IsIso (immersionLiftConormalMap B S hS hX hZ i hi Z' hle) := by
  have h1 := isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood B S hS
    (immersionAmbient B S hS hX hZ i hi) (immersionRangeSubspace B S hS hX hZ i hi) Z' h
  have h2 := Functor.map_isIso (modulePullback B S hS
    (immersionLiftPreimage B S hS hX hZ i hi Z' hle))
    ((modulePullback B S hS (subspaceInclusion B S hS _
        (preimageSubspace B S hS (subspaceInclusion B S hS
          (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi)))).map
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS
          (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi))
        (immersionRangeSubspace B S hS hX hZ i hi)
        (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
        (preimageProjection B S hS (subspaceInclusion B S hS
          (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi))
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS
          (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi))))
  have h3 := (NatIso.isIso_map_iff (modulePullbackCompIso B S hS
    (immersionLiftPreimage B S hS hX hZ i hi Z' hle)
    (subspaceInclusion B S hS _ (preimageSubspace B S hS
      (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
      (immersionRangeSubspace B S hS hX hZ i hi)))) _).1 h2
  have h4 := (NatIso.isIso_map_iff (modulePullbackCompIso B S hS
    (immersionClosedFactorization B S hS Z'.2.1 hZ
        (immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle)
        (isImmersion_immersionLiftClosedSubspace B S hS hX hZ i hi Z' hle))
    (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)) _).2 h3
  have h5 := isIso_idealSheafMap_of_eq_preimageSubspace B S hS
    (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
    (isEtale_immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
    (preimageSubspace B S hS (subspaceInclusion B S hS
      (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi))
    _ (immersionRangeSubspace_immersionLiftClosedSubspace_eq B S hS hX hZ i hi Z' hle)
    (immersionLiftRangeHom B S hS hX hZ i hi Z' hle)
    (immersionLiftRangeHom_square B S hS hX hZ i hi Z' hle)
  rw [immersionLiftConormalMap, idealSheafMap_comp B S hS
    (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
    (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')
    _ _ _ _ _ (immersionLiftRangeHom_square B S hS hX hZ i hi Z' hle)
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS
      (immersionAmbient B S hS hX hZ i hi) Z') (immersionRangeSubspace B S hS hX hZ i hi))]
  have : IsIso ((modulePullbackCompIso B S hS
      (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
      (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')).inv.app
      (definingIdealSheaf B S hS _ (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules) :=
    inferInstanceAs (IsIso ((modulePullbackCompIso B S hS
      (immersionLiftAmbientι B S hS hX hZ i hi Z' hle)
      (subspaceInclusion B S hS (immersionAmbient B S hS hX hZ i hi) Z')).app
      (definingIdealSheaf B S hS _
        (immersionRangeSubspace B S hS hX hZ i hi)).toSheafOfModules).inv)
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_
    (IsIso.comp_isIso' (isIso_map_comp_comp _ _ _ _ ?_ h4 ?_) ?_)))
  · infer_instance
  · infer_instance
  · exact Iso.isIso_inv ((modulePullbackCompIso B S hS _ _).app _)
  · exact Functor.map_isIso _ _
  · exact Functor.map_isIso _ _
  · infer_instance

/-- **[Stacks Project, Tag 05ZX].**  Let `i : Z ⟶ X` be an immersion of algebraic spaces and let
`Z ⊆ Z'` be the first order infinitesimal neighbourhood of `Z` in `X`: the closed subspace of
the complement `X ∖ ∂Z` of the boundary of the image, through which `i` factors as a closed
immersion, cut out by the square of the defining ideal sheaf of `Z` there.  Then the map
`𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP] induced by the square with `𝟙 Z` on the left
and `Z' ⟶ X` on the right, `AlgebraicGeometry.Space.immersionLiftConormalMap`, is an isomorphism
of `𝒪_Z`-modules.

The two conormal modules are `AlgebraicGeometry.Space.conormalModuleOfImmersion` of
[Stacks Project, Tag 04CN], for `i` and for the immersion `Z ⟶ Z'`.  The containment of the
image of `Z` in `Z'`, which the map is built from, is derived from the neighbourhood hypothesis
by `AlgebraicGeometry.Space.le_of_isFirstOrderNeighbourhood`. -/
@[stacks 05ZX "the map of conormal modules of 04CP from an immersion to its first order \
infinitesimal neighbourhood is an isomorphism"]
theorem isIso_immersionLiftConormalMap
    (h : IsFirstOrderNeighbourhood B S hS (immersionAmbient B S hS hX hZ i hi)
      (immersionRangeSubspace B S hS hX hZ i hi) Z') :
    IsIso (immersionLiftConormalMap B S hS hX hZ i hi Z'
      (le_of_isFirstOrderNeighbourhood B S hS _ _ Z' h)) :=
  isIso_immersionLiftConormalMap_of_le B S hS hX hZ i hi Z' _ h

end Immersion

end AlgebraicGeometry.Space
