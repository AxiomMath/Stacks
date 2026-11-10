module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of a pair of immersions

For immersions `Z --i--→ Y --j--→ X` of schemes, [Stacks Project, Tag 062S] asserts a canonical
exact sequence `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`, both maps being the canonical maps of
[Stacks Project, Tag 01R4]. This file constructs the right-hand map and proves that it is
surjective, which is the exactness of the sequence at `𝒞_{Z/Y}`.

## Main definitions

* `Stacks.Immersion.conormalSequenceRightMap` is the canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}`: the map
  of [Stacks Project, Tag 01R4] for the square with horizontal maps `i` and `i ≫ j` and vertical
  maps `𝟙_Z` and `j`, read through the identification `(𝟙_Z)^* ≅ id` of
  `RingedSpaceModuleAdjunction.modulePullbackId`.

## Main results

* `Stacks.Immersion.conormalSequence_isPullback`: the square defining the right-hand map is
  cartesian, because `j` is a monomorphism.
* `Stacks.Immersion.epi_conormalSequenceRightMap`: the right-hand map is an epimorphism, which is
  the exactness of the conormal sequence at `𝒞_{Z/Y}` — the `⟶ 0` of the source.

## Implementation notes

The square
```
Z --i--→ Y
|        |
𝟙        j
↓        ↓
Z -i≫j-→ X
```
commutes and is cartesian: its left edge is an isomorphism and `j`, being an immersion, is a
monomorphism. So `Stacks.Immersion.epi_immersionConormalSheafMap` applies and gives surjectivity
of the canonical map out of `(𝟙_Z)^* 𝒞_{Z/X}`; composing with the inverse of the pullback-identity
isomorphism, which is an isomorphism and hence an epimorphism, gives the statement for the map out
of `𝒞_{Z/X}` itself.

This file constructs only the right-hand map; the left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` is
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap` of
`StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence`, which imports this file and where it
carries the corresponding clause of [Stacks Project, Tag 062S].

Exactness of the sequence at the middle term `𝒞_{Z/X}` and the vanishing of the composite are
not proved here; they are `Stacks.Immersion.conormalSequence_exact` and
`Stacks.Immersion.conormalSequence_comp_zero` of
`StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact`, which imports this file and
where they carry the remaining clauses of [Stacks Project, Tag 062S]. Exactness at the middle
term is an affine-local computation —
over an affine `V ⊆ X` with `J ⊆ I ⊆ Γ(X, V)` the defining ideals of `Y` and of `Z`, it is the
exactness of `J/(J² + IJ) ⟶ I/I² ⟶ I/(J + I²) ⟶ 0` — carried out there using the affine
identification of all three conormal sheaves together with the local-to-global criterion
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` of
[Stacks Project, Tag 01AG].

## References

* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion

universe u

namespace Stacks.Immersion

variable {Z Y X : Scheme.{u}}

/-- **The square defining the right-hand map of the conormal sequence is cartesian.** Its left
edge is the identity and its right edge `j` is a monomorphism, being an immersion. -/
theorem conormalSequence_isPullback (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion j] :
    IsPullback i (𝟙 Z) j (i ≫ j) := by
  have : Mono j := inferInstance
  exact IsPullback.of_vert_isIso_mono (CommSq.mk (by simp))

/-- **The right-hand map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence of
[Stacks Project, Tag 062S].** It is the canonical map of [Stacks Project, Tag 01R4] attached to
the square with horizontal maps `i` and `i ≫ j` and vertical maps `𝟙_Z` and `j`, read through the
identification of the pullback along the identity with the identity functor. -/
@[stacks 062S "the second arrow 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}"]
def conormalSequenceRightMap (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom :=
  ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
      (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom)).inv ≫
    immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j
      (toShHom_square (conormalSequence_isPullback i j).w)

/-- **[Stacks Project, Tag 062S]: the conormal sequence is exact at `𝒞_{Z/Y}`.** For immersions
`Z ⟶ Y ⟶ X` the canonical map `𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` is an epimorphism, which is the `⟶ 0` at the
right-hand end of the canonical sequence `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`.

The defining square is cartesian by `Stacks.Immersion.conormalSequence_isPullback`, so
`Stacks.Immersion.epi_immersionConormalSheafMap` applies; the pullback-identity isomorphism is an
epimorphism. -/
@[stacks 062S "exactness at the right term: the canonical map 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} is epi",
  ega "IV 16.2.7" "surjectivity at right"]
theorem epi_conormalSequenceRightMap (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    Epi (conormalSequenceRightMap i j) := by
  have h := epi_immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j (conormalSequence_isPullback i j)
  change Epi (((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
      (conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom)).inv ≫
    immersionConormalSheafMap i (i ≫ j) (𝟙 Z) j
      (toShHom_square (conormalSequence_isPullback i j).w))
  exact @epi_comp _ _ _ _ _ _ inferInstance _ h

end Stacks.Immersion

end
