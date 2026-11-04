module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect
public import StacksFrontier.Homology.Tor.StandardModelExtensionScalars

/-!
# The base change map `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` in Situation 0CX4

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the coherator of a derived limit
`L = R lim Fₙ` of the system `(iₙ,* Fₙ)` ([Stacks, Tag 0CX5]), with projection
`φ : K ⟶ iₙ,* Fₙ` (`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimitProjection`).
For an object `E` of `D(𝒪_X)` the **canonical map** of [Stacks, Tag 0CX6] (1) is the morphism

`RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)`

of `D(Aₙ)` adjoint, under derived extension and restriction of scalars along `A ⟶ Aₙ`, to the
composite of `RΓ(X, E ⊗^𝐋 φ)` with the identification
`RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)`
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap`).

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.limitTensorSections`: `RΓ(X, E ⊗^𝐋 K)`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.limitTensorSectionsBaseChangeMap`: the
  canonical map.

## Implementation notes

The data `(DQ, adj, L, p)` are those of the `K` of [Stacks, Tag 0CX5]: a coherator `adj : ι ⊣ DQ`
and a derived limit `L` of the system `(iₙ,* Fₙ)`, as provided by
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded` (its first two
conjuncts), and `p : L ⟶ ∏ iₙ,* Fₙ` the first component of a witness of
`CategoryTheory.Pretriangulated.IsDerivedLimit D.derivedSystem L`, i.e. the map of a distinguished
triangle `L ⟶ ∏ iₙ,* Fₙ ⟶ ∏ iₙ,* Fₙ ⟶ L⟦1⟧` with the difference map in the middle. The map is
defined for every such `p`; nothing about this particular `L` is assumed.

The tensor order is `E ⊗ -`, the order of `AlgebraicGeometry.Space.smallEtaleDerivedTensor` and of
`stageTensorSectionsMap`. Every derived category of modules over a ring is written
`StacksDraft.ringDerivedCategory`, and derived extension of scalars
`StacksDraft.ringExtendScalars`, so the module installs no derived-category instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

variable (DQ) in
/-- `RΓ(X, E ⊗^𝐋 K)` in `D(A)`, for `K = DQ_X(L)`. -/
abbrev limitTensorSections :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  (representedAffineDerivedSections D.B D.S D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
    ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).obj
      (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).obj
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))))

/-- **The canonical map of [Stacks, Tag 0CX6] (1)**,
`RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)` for `K = DQ_X(L)` and a presentation
`p : L ⟶ ∏ iₙ,* Fₙ` of `L` as a derived limit: the transpose, under derived extension and
restriction of scalars along `A ⟶ Aₙ`, of `RΓ(X, E ⊗^𝐋 φ)` followed by `stageTensorSectionsMap`,
where `φ : K ⟶ iₙ,* Fₙ` is `derivedLimitProjection adj p n`. -/
def limitTensorSectionsBaseChangeMap
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n : ℕ) :
    (StacksDraft.ringExtendScalars (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).obj
        (D.limitTensorSections DQ L E) ⟶
      D.stageTensorSectionsTarget n E :=
  ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).homEquiv
      _ _).symm
    ((representedAffineDerivedSections D.B D.S D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).map
      ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).map
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).map
          (D.derivedLimitProjection adj p n))) ≫
      D.stageTensorSectionsMap n E)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
