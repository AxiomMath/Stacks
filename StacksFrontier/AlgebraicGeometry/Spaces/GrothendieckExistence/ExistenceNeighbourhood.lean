module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent

/-!
# The open neighbourhood of the closed fibre on which `K` is a finitely presented module

In Situation [Stacks, Tag 0CX4] let `K = R lim_{D_QCoh(𝒪_X)} Fₙ` be as in [Stacks, Tag 0CX5] and
let `X₀ ⊂ |X|` be the closed subset of points lying over the closed subset
`Spec(A₁) = Spec(A₂) = ⋯` of `Spec(A)`. [Stacks, Tag 0CX9] produces an open subspace `W ⊂ X`
containing `X₀` such that

1. `Hⁱ(K)|_W` is zero unless `i = 0`,
2. `F = H⁰(K)|_W` is of finite presentation, and
3. `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}`.

This file names the objects of that statement.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.pointsOverFirstStage`: the set `X₀`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stagePreimage`: the preimage
  `Wₙ = W ×_X Xₙ` of an open subspace `W` of `X` in `Xₙ`, an open subspace of `Xₙ`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageComparison`: for an object `K` of
  `D(𝒪_X)` with maps `K ⟶ iₙ,* Fₙ`, the induced map `iₙ^* H⁰(K) ⟶ Fₙ` of `𝒪_{Xₙ}`-modules.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.IsExistenceNeighbourhood`: the three
  conclusions of [Stacks, Tag 0CX9] for an open subspace `W` containing `X₀`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimitProjection`: the canonical
  map `K ⟶ Fₙ` of [Stacks, Tag 0CX9] for `K = DQ_X(L)`, `L = R lim_{D(𝒪_X)} Fₙ`.

## Implementation notes

The point `x ∈ |X|` *lies over* `Spec(A₁)` when its image under `|X| → |Spec A|` lies in the
image of `|Spec A₁| → |Spec A|`; the index `0` of the formalization stands for the level `1` of
the source, as in `AlgebraicGeometry.Space.FlatSheafExistenceSituation`.

The restriction `M|_W` of an `𝒪_X`-module to an open subspace is the inverse image along the open
immersion `W ⟶ X` (Stacks 03LU), as in `AlgebraicGeometry.Space.flatLocusRestrict`. Part (3)
says that the map `H⁰(K) ⊗_{𝒪_X} 𝒪_{Xₙ} = iₙ^* H⁰(K) ⟶ Fₙ` adjoint to the canonical map
`H⁰(K) ⟶ H⁰(iₙ,* Fₙ) = iₙ,* Fₙ` becomes an isomorphism on `Wₙ = W ×_X Xₙ`; by
[Stacks, Tag 04CJ] (the equivalence the source cites in Situation 0CX4) this is the
identification `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}` of the source.

The canonical map `K ⟶ Fₙ` is the map the derived limit comes with: for a distinguished triangle
`L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` presenting `L = R lim_{D(𝒪_X)} Fₙ` and a right adjoint `DQ_X` of the
inclusion `D_QCoh(𝒪_X) ⊂ D(𝒪_X)`, it is the counit `DQ_X(L) ⟶ L` followed by the projection to
the factor `Fₙ`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0CX5](https://stacks.math.columbia.edu/tag/0CX5)
* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The set `X₀ ⊂ |X|` of points lying over the closed subset `Spec(A₁)` of `Spec(A)`: the points
whose image in `|Spec A|` lies in the image of `|Spec A₁|`. -/
def pointsOverFirstStage : Set (points D.B D.S D.containsLimitBase D.X.left.1) :=
  {x | pointsMap D.B D.S D.containsLimitBase D.X.left.1 D.X.hom.hom x ∈
    Set.range (pointsMap D.B D.S D.containsLimitBase _
      (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt 0).hom)}

/-- The preimage `Wₙ = W ×_X Xₙ` of an open subspace `W` of `X` in `Xₙ`. -/
abbrev stagePreimage (W : Subfunctor D.X.left.1) (n : ℕ) : Subfunctor (D.stage n).1 :=
  W.preimage (D.closedImmersion n).hom

/-- `Wₙ = W ×_X Xₙ` is an open subspace of `Xₙ`. -/
theorem isOpenSubspace_stagePreimage {W : Subfunctor D.X.left.1}
    (hW : IsOpenSubspace D.B D.S D.containsLimitBase W) (n : ℕ) :
    IsOpenSubspace D.B D.S D.containsLimitBase (D.stagePreimage W n) :=
  isOpenSubspace_preimage D.B D.S D.containsLimitBase _ W D.X.left.2 (D.stage n).2 hW

/-- For an object `K` of `D(𝒪_X)` with maps `πₙ : K ⟶ iₙ,* Fₙ`, the map
`iₙ^* H⁰(K) ⟶ Fₙ` of `𝒪_{Xₙ}`-modules adjoint to `H⁰(πₙ) : H⁰(K) ⟶ H⁰(iₙ,* Fₙ) = iₙ,* Fₙ`. -/
def stageComparison (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)) (n : ℕ) :
    (modulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)).obj
      ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K) ⟶ D.F n :=
  ((modulePullbackAdjunction D.B D.S D.containsLimitBase (D.closedImmersion n)).homEquiv _ _).symm
    ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).map (π n) ≫
      ((@DerivedCategory.singleFunctorCompHomologyFunctorIso _ _
        (modulesAbelianSmallEtale D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
        (spaceHasDerivedCategory D.B D.S D.containsLimitBase D.X.left) 0).app
          (D.pushforwardModule n)).hom)

/-- **The conclusion of [Stacks, Tag 0CX9]** for an object `K` of `D(𝒪_X)` with maps
`πₙ : K ⟶ Fₙ` and an open subspace `W` of `X`: `W` contains `X₀`, and

1. `Hⁱ(K)|_W = 0` for `i ≠ 0`,
2. `H⁰(K)|_W` is of finite presentation,
3. for every `n`, the map `H⁰(K) ⊗_{𝒪_X} 𝒪_{Xₙ} ⟶ Fₙ` induced by `πₙ` is an isomorphism on
   `Wₙ = W ×_X Xₙ`. -/
structure IsExistenceNeighbourhood (K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)) (W : Subfunctor D.X.left.1)
    (hW : IsOpenSubspace D.B D.S D.containsLimitBase W) : Prop where
  /-- `W` contains `X₀`. -/
  subset_range : D.pointsOverFirstStage ⊆
    Set.range (pointsMap D.B D.S D.containsLimitBase W.toFunctor W.ι)
  /-- Part (1): `Hⁱ(K)|_W = 0` for `i ≠ 0`. -/
  isZero_homology (i : ℤ) (hi : i ≠ 0) :
    IsZero ((modulePullback D.B D.S D.containsLimitBase
      (openSubspaceHom D.B D.S D.containsLimitBase W hW)).obj
        ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left i).obj K))
  /-- Part (2): `H⁰(K)|_W` is of finite presentation. -/
  isFinitePresentation :
    ((modulePullback D.B D.S D.containsLimitBase
      (openSubspaceHom D.B D.S D.containsLimitBase W hW)).obj
        ((spaceDerivedHomology D.B D.S D.containsLimitBase D.X.left 0).obj K))
      |>.IsFinitePresentationOnSite
  /-- Part (3): `Fₙ = H⁰(K)|_W ⊗_{𝒪_X} 𝒪_{Xₙ}` on `Wₙ`, through the map induced by `πₙ`. -/
  isIso_stageComparison (n : ℕ) :
    IsIso ((modulePullback D.B D.S D.containsLimitBase
      (openSubspaceHom D.B D.S D.containsLimitBase (D.stagePreimage W n)
        (D.isOpenSubspace_stagePreimage hW n))).map (D.stageComparison K π n))

/-- The canonical map `K ⟶ Fₙ` of [Stacks, Tag 0CX9], for `K = DQ_X(L)`: the counit
`DQ_X(L) ⟶ L` followed by the projection `L ⟶ ∏ Fₙ ⟶ Fₙ` of a triangle presenting `L` as the
derived limit `R lim_{D(𝒪_X)} Fₙ`. -/
def derivedLimitProjection
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n : ℕ) :
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L) ⟶
      D.derivedSystem.obj (op n) :=
  adj.counit.app L ≫ p ≫ Pi.π _ n

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
