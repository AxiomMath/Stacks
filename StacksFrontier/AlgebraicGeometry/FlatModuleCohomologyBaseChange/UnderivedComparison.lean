module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.CoefficientFunctors
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# The underived comparison of the two coefficient functors

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

and an `𝒪_{S'}`-module `G`, write

`Φ : M ↦ g^*M ⊗_{𝒪_{S'}} G` and `Ψ : F ↦ (g')^*F ⊗_{𝒪_{X'}} (f')^*G`

for the two coefficient functors of [Stacks, Tag 0GN5]. This file constructs the canonical
natural transformation

`Φ ∘ f_* ⟶ f'_* ∘ Ψ`,

the degree-zero case of the comparison that tag asserts to be invertible. It is the composite of
two transformations that exist for an arbitrary commutative square: the base-change morphism
`g^*f_* ⟶ f'_*(g')^*` of [Stacks, Tag 02KG], tensored with the identity of `G`, followed by the
projection-formula morphism `f'_*M ⊗ G ⟶ f'_*(M ⊗ (f')^*G)` of [Stacks, Tag 0FZE].

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.projectionNatTrans`: the projection formula of
  [Stacks, Tag 0FZE] as a natural transformation
  `f'_* ∘ (- ⊗ G) ⟶ (- ⊗ (f')^*G) ∘ f'_*`, the second tensor factor held fixed.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseChangeNatTrans`: the base-change morphism of
  [Stacks, Tag 02KG].
* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison`: **the comparison**
  `Φ ∘ f_* ⟶ f'_* ∘ Ψ`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_app`: **the normalisation.**
  The component at `F` is the base-change morphism tensored with the identity of `G`, followed
  by the projection formula; naming both factors is what pins the comparison down.

## Implementation notes

Everything is written over `SheafOfModules (structureSheafRing _)`, with the inverse and direct
images `RingedSpaceModuleAdjunction.modulePullback` and `modulePushforward`, which is the
spelling the tensor product of [Stacks, Tag 01CB] and the projection formula are stated over;
see the implementation notes of `CoefficientFunctors.lean` for why one spelling must be used
throughout. The base-change morphism of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is stated over
`AlgebraicGeometry.Scheme.Modules`, and `baseChangeNatTrans` below is that transformation read
at the other spelling; the two types are definitionally equal.

Naturality of the comparison needs no proof: the base-change factor is whiskered on the right by
a functor and the projection-formula factor is whiskered on the left by one, so the composite is
a natural transformation by construction. Only `projectionNatTrans` carries a naturality
obligation, and it is
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural` with the second
tensor factor at the identity of `G`, whose pullback is removed by functoriality.

Neither the square's being cartesian nor flatness of `G` is used; those enter only when the
comparison is asserted to be invertible.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### The projection formula as a natural transformation -/

/-- **The projection formula of [Stacks, Tag 0FZE] as a natural transformation**, with the
second tensor factor held fixed at `G`: the morphisms `f'_*M ⊗ G ⟶ f'_*(M ⊗ (f')^*G)` are
natural in `M`. -/
def projectionNatTrans (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    modulePushforward f'.toLRSHom.toShHom ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S'.toRingedSpace.sheaf).flip.obj G ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X'.toRingedSpace.sheaf).flip.obj ((modulePullback f'.toLRSHom.toShHom).obj G) ⋙
        modulePushforward f'.toLRSHom.toShHom where
  app M := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' M G
  naturality M M' ψ := by
    let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf
    let targetTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X'.toRingedSpace.sheaf
    let inverseImage := modulePullback f'.toLRSHom.toShHom
    let directImage := modulePushforward f'.toLRSHom.toShHom
    have sourceIdentity :=
      (congrArg ((sourceTensor.map (directImage.map ψ)).app G ≫ ·)
        ((sourceTensor.obj (directImage.obj M')).map_id G)).trans (Category.comp_id _)
    have targetIdentity :=
      (congrArg ((targetTensor.map ψ).app (inverseImage.obj G) ≫ (targetTensor.obj M').map ·)
          (inverseImage.map_id G)).trans
        ((congrArg ((targetTensor.map ψ).app (inverseImage.obj G) ≫ ·)
          ((targetTensor.obj M').map_id (inverseImage.obj G))).trans (Category.comp_id _))
    exact (congrArg (· ≫ Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' M' G)
        sourceIdentity).symm.trans
      ((Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural f' ψ (𝟙 G)).trans
        (congrArg (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' M G ≫
          directImage.map ·) targetIdentity))

/-- The component of `projectionNatTrans` at `M` is the projection-formula morphism
`f'_*M ⊗ G ⟶ f'_*(M ⊗ (f')^*G)` of [Stacks, Tag 0FZE]. -/
@[simp]
theorem projectionNatTrans_app (f' : X' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) :
    (projectionNatTrans f' G).app M =
      Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' M G :=
  rfl

/-! ### The base-change morphism, at the ringed-space spelling -/

/-- **The base-change morphism `g^*f_* ⟶ f'_*(g')^*` of [Stacks, Tag 02KG]**, read over
`SheafOfModules (structureSheafRing _)`. -/
def baseChangeNatTrans {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (w : g' ≫ f = f' ≫ g) :
    modulePushforward f.toLRSHom.toShHom ⋙ modulePullback g.toLRSHom.toShHom ⟶
      modulePullback g'.toLRSHom.toShHom ⋙ modulePushforward f'.toLRSHom.toShHom :=
  AffinePushforward.baseChangeNatTrans w

/-- The component of `baseChangeNatTrans` at `F` is the component of the base-change morphism of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the two types being
definitionally equal. -/
@[simp]
theorem baseChangeNatTrans_app {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (w : g' ≫ f = f' ≫ g)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (baseChangeNatTrans w).app F = (AffinePushforward.baseChangeNatTrans w).app F :=
  rfl

/-! ### The comparison -/

/-- **The underived comparison** `Φ ∘ f_* ⟶ f'_* ∘ Ψ` of the two coefficient functors, for a
commutative square of schemes and an `𝒪_{S'}`-module `G`: the base-change morphism
`g^*f_* ⟶ f'_*(g')^*` tensored with the identity of `G`, followed by the projection-formula
morphism. -/
def underivedComparison {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    modulePushforward f.toLRSHom.toShHom ⋙ baseCoefficients g G ⟶
      totalCoefficients g' f' G ⋙ modulePushforward f'.toLRSHom.toShHom :=
  Functor.whiskerRight (baseChangeNatTrans w)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf).flip.obj G) ≫
    Functor.whiskerLeft (modulePullback g'.toLRSHom.toShHom) (projectionNatTrans f' G)

/-- **The normalisation of the underived comparison**: its component at `F` is the base-change
morphism of [Stacks, Tag 02KG] tensored with `G`, followed by the projection-formula morphism of
[Stacks, Tag 0FZE] at `(g')^*F`. -/
theorem underivedComparison_app {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (underivedComparison w G).app F =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S'.toRingedSpace.sheaf).flip.obj G).map ((baseChangeNatTrans w).app F) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
          ((modulePullback g'.toLRSHom.toShHom).obj F) G :=
  rfl

/-- The normalisation of the underived comparison, with both factors written in the vocabulary
of the tensor product. The same statement as `underivedComparison_app`, in the shape `rw`
needs; it is stated here rather than re-declared in each file that rewrites with it. -/
theorem underivedComparison_app' {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (w : g' ≫ f = f' ≫ g)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (underivedComparison w G).app F =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S'.toRingedSpace)).presheaf, ((S'.toRingedSpace)).IsSheaf⟩)).map
        ((((baseChangeNatTrans w).app F), (𝟙 G)) : (_, _) ⟶ (_, _))) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
          ((modulePullback g'.toLRSHom.toShHom).obj F) G :=
  (underivedComparison_app w G F).trans (by
    let sourceTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      S'.toRingedSpace.sheaf
    let baseMap := (baseChangeNatTrans w).app F
    have identityLaw :=
      (congrArg ((sourceTensor.map baseMap).app G ≫ ·)
        ((sourceTensor.obj ((modulePushforward f'.toLRSHom.toShHom).obj
          ((modulePullback g'.toLRSHom.toShHom).obj F))).map_id G)).trans (Category.comp_id _)
    exact congrArg (· ≫ Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
      ((modulePullback g'.toLRSHom.toShHom).obj F) G) identityLaw.symm)

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
