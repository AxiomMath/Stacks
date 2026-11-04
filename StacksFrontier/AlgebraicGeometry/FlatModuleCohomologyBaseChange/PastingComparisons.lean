module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DegreewiseComparison
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting

/-!
# The two coefficient functors under a further inverse image

Let

```
X'' --h'--> X' --g'--> X
|f''        |f'        |f
v           v          v
S'' --h-->  S' --g-->  S
```

be two commutative squares of schemes stacked along the base, and let `G` be an
`𝒪_{S'}`-module.  The two coefficient functors of [Stacks, Tag 0GN5] for the left-hand square
and the module `h^*G`,

`Φ'' : M ↦ (h ≫ g)^*M ⊗_{𝒪_{S''}} h^*G` and `Ψ'' : F ↦ (h' ≫ g')^*F ⊗_{𝒪_{X''}} (f'')^*h^*G`,

are the composites of the coefficient functors of the right-hand square with the inverse images
along `h` and along `h'`.  This file constructs those two identifications, together with the two
underived inputs of the pasting law for the comparison of that tag: the base-change morphism of
a stacked rectangle, and the hexagon of [Stacks, Tag 0E48], both read at the
`SheafOfModules (structureSheafRing _)` spelling the comparison is written in.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.tensorPullbackComparison`: the comparison of
  [Stacks, Tag 01CD] `k^*(M ⊗ G) ≅ k^*M ⊗ k^*G`, at the spelling of the tensor product of
  [Stacks, Tag 01CB] that the coefficient functors use.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.tensorRightFactorPullbackIso`: that comparison as
  an isomorphism of the functors tensoring with a fixed right factor.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.squarePullbackIso`: the identification of the two
  composite inverse images around a commutative square.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseCoefficientsPullbackIso` and
  `totalCoefficientsPullbackIso`: **the two identifications** `Φ ⋙ h^* ≅ Φ''` and
  `Ψ ⋙ (h')^* ≅ Ψ''`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseChangeNatTrans_pasteBase_app`: the base-change
  morphism of [Stacks, Tag 02KG] for a rectangle obtained by stacking two squares along the
  base.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.projectionFormulaMap_baseChangeNatTrans`: **the
  hexagon of [Stacks, Tag 0E48]** — the projection-formula morphism of [Stacks, Tag 0FZE] is
  compatible with the base-change morphism of an arbitrary commutative square.

## Implementation notes

Everything is stated over `SheafOfModules (structureSheafRing _)` with the tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` and the inverse and direct images
`RingedSpaceModuleAdjunction.modulePullback` and `modulePushforward`, which is the spelling the
comparison of `UnderivedComparison.lean` is written in.  The two facts imported from elsewhere
are stated at other spellings — the base-change pasting law over
`AlgebraicGeometry.Scheme.Modules`, and the hexagon over the uncurried tensor bifunctor
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor _)` — and each is restated here
once.

The coefficient functors tensor with a *fixed* factor, so they are the curried bifunctor
`(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj G` and its action on morphisms is
`((sheafTensor _).flip.obj G).map φ`, while the ringed-space hexagon is stated for the uncurried
bifunctor and `(Functor.uncurry.obj (sheafTensor _)).map (φ ×ₘ ψ)`.  The two spellings of the
tensor product of two morphisms are equal, but the objects they live over —
`((sheafTensor s).obj M).obj G` and `(Functor.uncurry.obj (sheafTensor s)).obj (M, G)` — are only
definitionally so, and *unifying them at a composition* `≫` exhausts the elaborator's heartbeat
budget.  Every chain below is therefore composed in one spelling throughout, and the crossing is
confined to the equalities `tensorPullbackComparison_hom`,
`tensorSheafMap_eq_bifunctor_map_right`, `tensorSheafMap_eq_bifunctor_map_left` and
`projectionFormulaMap_toShHom`, where it is a single definitional check between two closed terms.
The hexagon is crossed one side at a time, in `projectionFormulaMap_baseChangeNatTrans_lhs` and
`..._rhs`, because the two sides together exceed the heartbeat budget for a single declaration.

`toShHom_comp` exists for a related reason: the identity `(h ≫ g)^* = h^* ∘ g^*` of underlying
ringed-space morphisms holds by `rfl` but not reducibly, so it has to be applied as a rewrite
rather than left to unification.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {S S' S'' X X' X'' : Scheme.{u}}

/-! ### The comparison of Tag 01CD at the spelling of the coefficient functors -/

/-- **The comparison of [Stacks, Tag 01CD]** `k^*(M ⊗ G) ≅ k^*M ⊗ k^*G`, at the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling of the tensor product of
[Stacks, Tag 01CB]. -/
def tensorPullbackComparison {Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (k : Z ⟶ Y)
    (M G : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullback k).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj M).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj
          ((modulePullback k).obj M)).obj ((modulePullback k).obj G) :=
  (Stacks.RingedSpace.comparisonBifunctorIso k).app (M, G)

/-- The forward map of `tensorPullbackComparison` is the component of the comparison natural
transformation of [Stacks, Tag 01CD] at the pair `(M, G)`. -/
theorem tensorPullbackComparison_hom {Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (k : Z ⟶ Y)
    (M G : SheafOfModules.{u} (structureSheafRing Y)) :
    (tensorPullbackComparison k M G).hom =
      (Stacks.RingedSpace.comparisonNatTrans k).app (M, G) :=
  rfl

/-- Tensoring a morphism with the identity of a fixed right factor, at the curried spelling the
coefficient functors use and at the uncurried one the ringed-space hexagon is stated at. -/
theorem tensorSheafMap_eq_bifunctor_map_right (Y : AlgebraicGeometry.RingedSpace.{u, u})
    {F F' : SheafOfModules.{u} (structureSheafRing Y)} (φ : F ⟶ F')
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).flip.obj G).map φ =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map (φ ×ₘ 𝟙 G) :=
  (Category.comp_id
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Y.sheaf).map φ).app G)).symm.trans
    (congrArg
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map φ).app G ≫ ·)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F').map_id G).symm)

/-- Tensoring the identity of a fixed left factor with a morphism, at the curried spelling the
coefficient functors use and at the uncurried one the ringed-space hexagon is stated at. -/
theorem tensorSheafMap_eq_bifunctor_map_left (Y : AlgebraicGeometry.RingedSpace.{u, u})
    (F : SheafOfModules.{u} (structureSheafRing Y))
    {G G' : SheafOfModules.{u} (structureSheafRing Y)} (χ : G ⟶ G') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).map χ =
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map (𝟙 F ×ₘ χ) :=
  (Category.id_comp
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).map
          χ)).symm.trans
    (congrArg
      (· ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).map χ)
      (congrArg
        (fun t : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F ⟶
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F => t.app G)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map_id F)).symm)

/-- The projection-formula morphism of a morphism of schemes is the one of its underlying
morphism of ringed spaces: the crossing between the two spellings of [Stacks, Tag 0FZE]. -/
theorem projectionFormulaMap_toShHom {T S : Scheme.{u}} (k : T ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
    (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap k G H =
      Stacks.AffineProjectionFormula.projectionFormulaMap k.toLRSHom.toShHom G H :=
  Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq k G H

/-- Naturality of the comparison of [Stacks, Tag 01CD] in both tensor factors. -/
theorem tensorPullbackComparison_naturality {Y Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (k : Z ⟶ Y) {M N G G' : SheafOfModules.{u} (structureSheafRing Y)} (ψ : M ⟶ N) (χ : G ⟶ G') :
    (modulePullback k).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).map ψ).app G ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj N).map χ) ≫
        (tensorPullbackComparison k N G').hom =
      (tensorPullbackComparison k M G).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).map
              ((modulePullback k).map ψ)).app ((modulePullback k).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj
            ((modulePullback k).obj N)).map ((modulePullback k).map χ)) :=
  (Stacks.RingedSpace.comparisonNatTrans k).naturality (ψ ×ₘ χ)

/-! ### Transporting the fixed tensor factor -/

/-- Tag 01CD as an isomorphism of the functors `M ↦ h^*(M ⊗ G)` and `M ↦ h^*M ⊗ h^*G`. -/
def tensorRightFactorPullbackIso (h : S'' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S'.toRingedSpace.sheaf).flip.obj G ⋙ modulePullback h.toLRSHom.toShHom ≅
      modulePullback h.toLRSHom.toShHom ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            S''.toRingedSpace.sheaf).flip.obj ((modulePullback h.toLRSHom.toShHom).obj G) :=
  NatIso.ofComponents (fun M => tensorPullbackComparison h.toLRSHom.toShHom M G)
    (fun {M N} ψ => by
      let baseTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S'.toRingedSpace.sheaf
      let totalTensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S''.toRingedSpace.sheaf
      let inverseImage := modulePullback h.toLRSHom.toShHom
      have sourceIdentity :=
        (congrArg (fun arrow => (baseTensor.map ψ).app G ≫ arrow)
          ((baseTensor.obj N).map_id G)).trans (Category.comp_id ((baseTensor.map ψ).app G))
      have targetIdentity :=
        (congrArg (fun arrow =>
            (totalTensor.map (inverseImage.map ψ)).app (inverseImage.obj G) ≫
              (totalTensor.obj (inverseImage.obj N)).map arrow) (inverseImage.map_id G)).trans
          ((congrArg (fun arrow =>
              (totalTensor.map (inverseImage.map ψ)).app (inverseImage.obj G) ≫ arrow)
            ((totalTensor.obj (inverseImage.obj N)).map_id (inverseImage.obj G))).trans
            (Category.comp_id ((totalTensor.map (inverseImage.map ψ)).app (inverseImage.obj G))))
      exact (congrArg (fun arrow => inverseImage.map arrow ≫
          (tensorPullbackComparison h.toLRSHom.toShHom N G).hom) sourceIdentity).symm.trans
        ((tensorPullbackComparison_naturality h.toLRSHom.toShHom ψ (𝟙 G)).trans
          (congrArg (fun arrow =>
            (tensorPullbackComparison h.toLRSHom.toShHom M G).hom ≫ arrow) targetIdentity)))

/-- The component of `tensorRightFactorPullbackIso` at `M` is the comparison of [Stacks,
Tag 01CD] for the pair `(M, G)`. -/
theorem tensorRightFactorPullbackIso_hom_app (h : S'' ⟶ S')
    (G M : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (tensorRightFactorPullbackIso h G).hom.app M =
      (tensorPullbackComparison h.toLRSHom.toShHom M G).hom :=
  rfl

/-! ### The two coefficient functors under a further inverse image -/

/-- **The coefficient functor on the base under a further inverse image**:
`h^*(g^*M ⊗ G) ≅ (h ≫ g)^*M ⊗ h^*G`. -/
def baseCoefficientsPullbackIso (g : S' ⟶ S) (h : S'' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    baseCoefficients g G ⋙ modulePullback h.toLRSHom.toShHom ≅
      baseCoefficients (h ≫ g) ((modulePullback h.toLRSHom.toShHom).obj G) :=
  Functor.isoWhiskerLeft (modulePullback g.toLRSHom.toShHom)
      (tensorRightFactorPullbackIso h G) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
        g.toLRSHom.toShHom)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S''.toRingedSpace.sheaf).flip.obj ((modulePullback h.toLRSHom.toShHom).obj G))

/-- The component of `baseCoefficientsPullbackIso` at `M`, as the composite of its two factors:
the comparison of [Stacks, Tag 01CD] at `(g^*M, G)`, followed by the comparison of the composite
inverse images tensored into the first factor. -/
theorem baseCoefficientsPullbackIso_hom_app (g : S' ⟶ S) (h : S'' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (M : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (baseCoefficientsPullbackIso g h G).hom.app M =
      (tensorPullbackComparison h.toLRSHom.toShHom
            ((modulePullback g.toLRSHom.toShHom).obj M) G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S''.toRingedSpace.sheaf).flip.obj
            ((modulePullback h.toLRSHom.toShHom).obj G)).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
            g.toLRSHom.toShHom).hom.app M) :=
  rfl

/-- The identification of the two composite inverse images around a commutative square. -/
def squarePullbackIso {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}
    (w : h' ≫ f' = f'' ≫ h) :
    modulePullback h.toLRSHom.toShHom ⋙ modulePullback f''.toLRSHom.toShHom ≅
      modulePullback f'.toLRSHom.toShHom ⋙ modulePullback h'.toLRSHom.toShHom :=
  Stacks.AffineProjectionFormula.squareCompositeIso
    (Stacks.RingedSpace.pullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
      f'.toLRSHom.toShHom h.toLRSHom.toShHom (Stacks.Modules.toShHom_comm w))
    (Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
      f'.toLRSHom.toShHom)

/-- **The coefficient functor upstairs under a further inverse image**:
`(h')^*((g')^*F ⊗ (f')^*G) ≅ (h' ≫ g')^*F ⊗ (f'')^*h^*G`. -/
def totalCoefficientsPullbackIso {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} (g' : X' ⟶ X) {h : S'' ⟶ S'}
    {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    totalCoefficients g' f' G ⋙ modulePullback h'.toLRSHom.toShHom ≅
      totalCoefficients (h' ≫ g') f'' ((modulePullback h.toLRSHom.toShHom).obj G) :=
  (Functor.isoWhiskerLeft (modulePullback g'.toLRSHom.toShHom)
        (tensorRightFactorPullbackIso h' ((modulePullback f'.toLRSHom.toShHom).obj G)) ≪≫
      Functor.isoWhiskerLeft
        (modulePullback g'.toLRSHom.toShHom ⋙ modulePullback h'.toLRSHom.toShHom)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X''.toRingedSpace.sheaf).flip.mapIso ((squarePullbackIso w).app G).symm)) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
        g'.toLRSHom.toShHom)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X''.toRingedSpace.sheaf).flip.obj ((modulePullback f''.toLRSHom.toShHom).obj
            ((modulePullback h.toLRSHom.toShHom).obj G)))

/-- The component of `totalCoefficientsPullbackIso` at `F`, as the composite of its three
factors: the comparison of [Stacks, Tag 01CD] at `((g')^*F, (f')^*G)`, the identification of the
two composite inverse images around the square, and the comparison of the composite inverse
images tensored into the first factor. -/
theorem totalCoefficientsPullbackIso_hom_app {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} (g' : X' ⟶ X)
    {h : S'' ⟶ S'} {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (totalCoefficientsPullbackIso g' w G).hom.app F =
      ((tensorPullbackComparison h'.toLRSHom.toShHom
              ((modulePullback g'.toLRSHom.toShHom).obj F)
              ((modulePullback f'.toLRSHom.toShHom).obj G)).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X''.toRingedSpace.sheaf).obj
              ((modulePullback h'.toLRSHom.toShHom).obj
                ((modulePullback g'.toLRSHom.toShHom).obj F))).map
            ((squarePullbackIso w).inv.app G)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X''.toRingedSpace.sheaf).flip.obj
            ((modulePullback f''.toLRSHom.toShHom).obj
              ((modulePullback h.toLRSHom.toShHom).obj G))).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
            g'.toLRSHom.toShHom).hom.app F) :=
  rfl

/-- The direct image of `totalCoefficientsPullbackIso_hom_app`, with the two factors of the
comparison separated. -/
theorem map_totalCoefficientsPullbackIso_hom_app {f' : X' ⟶ S'} {f'' : X'' ⟶ S''} (g' : X' ⟶ X)
    {h : S'' ⟶ S'} {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (modulePushforward f''.toLRSHom.toShHom).map
        ((totalCoefficientsPullbackIso g' w G).hom.app F) =
      (modulePushforward f''.toLRSHom.toShHom).map
          ((tensorPullbackComparison h'.toLRSHom.toShHom
                ((modulePullback g'.toLRSHom.toShHom).obj F)
                ((modulePullback f'.toLRSHom.toShHom).obj G)).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X''.toRingedSpace.sheaf).obj
                ((modulePullback h'.toLRSHom.toShHom).obj
                  ((modulePullback g'.toLRSHom.toShHom).obj F))).map
              ((squarePullbackIso w).inv.app G)) ≫
        (modulePushforward f''.toLRSHom.toShHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                X''.toRingedSpace.sheaf).flip.obj
              ((modulePullback f''.toLRSHom.toShHom).obj
                ((modulePullback h.toLRSHom.toShHom).obj G))).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
              g'.toLRSHom.toShHom).hom.app F)) :=
  (modulePushforward f''.toLRSHom.toShHom).map_comp _ _

/-! ### Reassociated forms, and the two underived inputs -/

/-- The underlying morphism of sheafed spaces of a composite of morphisms of schemes is the
composite of the underlying morphisms.  It holds by `rfl` but not reducibly, so the identity
`(a ≫ b)^* = a^* ∘ b^*` has to be applied as a rewrite rather than left to unification. -/
theorem toShHom_comp {T T' T'' : Scheme.{u}} (a : T'' ⟶ T') (b : T' ⟶ T) :
    (a ≫ b).toLRSHom.toShHom = a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom :=
  rfl

/-- **The base-change morphism of [Stacks, Tag 02KG] for a rectangle obtained by stacking two
squares along the base**: it is the base-change morphism of the right-hand square, pulled back
along `h`, followed by that of the left-hand square, the two comparisons of the composite
inverse images mediating. -/
theorem baseChangeNatTrans_pasteBase_app {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}
    (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (baseChangeNatTrans (FlatBaseChangeCohomology.pasteBase w₁ w₂)).app F =
      (Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
            g.toLRSHom.toShHom).inv.app ((modulePushforward f.toLRSHom.toShHom).obj F) ≫
        (modulePullback h.toLRSHom.toShHom).map ((baseChangeNatTrans w₁).app F) ≫
          (baseChangeNatTrans w₂).app ((modulePullback g'.toLRSHom.toShHom).obj F) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
              ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
                g'.toLRSHom.toShHom).hom.app F) :=
  FlatBaseChangeCohomology.baseChangeNatTrans_pasteBase_app w₁ w₂ F

/-- The left-hand side of the hexagon of [Stacks, Tag 0E48], crossed from the spelling of the
comparison to the one the ringed-space statement is written at. -/
private theorem projectionFormulaMap_baseChangeNatTrans_lhs {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
    {h : S'' ⟶ S'} {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (E : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    (K : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (tensorPullbackComparison h.toLRSHom.toShHom
            ((modulePushforward f'.toLRSHom.toShHom).obj E) K).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S''.toRingedSpace.sheaf).flip.obj
            ((modulePullback h.toLRSHom.toShHom).obj K)).map
            ((baseChangeNatTrans w).app E) ≫
          Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f''
            ((modulePullback h'.toLRSHom.toShHom).obj E)
            ((modulePullback h.toLRSHom.toShHom).obj K) =
      (Stacks.RingedSpace.comparisonNatTrans h.toLRSHom.toShHom).app
            ((modulePushforward f'.toLRSHom.toShHom).obj E, K) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            S''.toRingedSpace.sheaf)).map
            (Stacks.RingedSpace.squareBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                f'.toLRSHom.toShHom h.toLRSHom.toShHom (Stacks.Modules.toShHom_comm w) E ×ₘ
              𝟙 ((modulePullback h.toLRSHom.toShHom).obj K)) ≫
          Stacks.AffineProjectionFormula.projectionFormulaMap f''.toLRSHom.toShHom
            ((modulePullback h'.toLRSHom.toShHom).obj E)
            ((modulePullback h.toLRSHom.toShHom).obj K) := by
  rw [tensorSheafMap_eq_bifunctor_map_right S''.toRingedSpace ((baseChangeNatTrans w).app E)
      ((modulePullback h.toLRSHom.toShHom).obj K), baseChangeNatTrans_app,
    projectionFormulaMap_toShHom, tensorPullbackComparison_hom,
    ← Stacks.Modules.squareBaseChangeMap_eq_baseChangeNatTrans w E]
  rfl

/-- The right-hand side of the hexagon of [Stacks, Tag 0E48], crossed from the spelling of the
comparison to the one the ringed-space statement is written at. -/
private theorem projectionFormulaMap_baseChangeNatTrans_rhs {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
    {h : S'' ⟶ S'} {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (E : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    (K : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (modulePullback h.toLRSHom.toShHom).map
          (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' E K) ≫
        (baseChangeNatTrans w).app
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                X'.toRingedSpace.sheaf).obj E).obj
              ((modulePullback f'.toLRSHom.toShHom).obj K)) ≫
          (modulePushforward f''.toLRSHom.toShHom).map
            ((tensorPullbackComparison h'.toLRSHom.toShHom E
                ((modulePullback f'.toLRSHom.toShHom).obj K)).hom ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  X''.toRingedSpace.sheaf).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj E)).map
                ((squarePullbackIso w).inv.app K)) =
      (modulePullback h.toLRSHom.toShHom).map
            (Stacks.AffineProjectionFormula.projectionFormulaMap f'.toLRSHom.toShHom E K) ≫
        Stacks.RingedSpace.squareBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom
            f'.toLRSHom.toShHom h.toLRSHom.toShHom (Stacks.Modules.toShHom_comm w)
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X'.toRingedSpace.sheaf)).obj
              (E, (modulePullback f'.toLRSHom.toShHom).obj K)) ≫
          (modulePushforward f''.toLRSHom.toShHom).map
            ((Stacks.RingedSpace.comparisonNatTrans h'.toLRSHom.toShHom).app
                (E, (modulePullback f'.toLRSHom.toShHom).obj K) ≫
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                X''.toRingedSpace.sheaf)).map
                (𝟙 ((modulePullback h'.toLRSHom.toShHom).obj E) ×ₘ
                  (squarePullbackIso w).inv.app K)) := by
  rw [tensorSheafMap_eq_bifunctor_map_left X''.toRingedSpace
      ((modulePullback h'.toLRSHom.toShHom).obj E) ((squarePullbackIso w).inv.app K),
    baseChangeNatTrans_app w
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.toRingedSpace.sheaf).obj E).obj
        ((modulePullback f'.toLRSHom.toShHom).obj K)),
    projectionFormulaMap_toShHom, tensorPullbackComparison_hom,
    ← Stacks.Modules.squareBaseChangeMap_eq_baseChangeNatTrans w
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.toRingedSpace.sheaf).obj E).obj
        ((modulePullback f'.toLRSHom.toShHom).obj K))]
  rfl

/-- The inverse image of the underived comparison, with its two factors separated and a
morphism composed on the right. -/
theorem map_underivedComparison_app_assoc {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}
    (w : g' ≫ f = f' ≫ g) (h : S'' ⟶ S')
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {Z : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace)}
    (m : (modulePullback h.toLRSHom.toShHom).obj
        ((totalCoefficients g' f' G ⋙ modulePushforward f'.toLRSHom.toShHom).obj F) ⟶ Z) :
    (modulePullback h.toLRSHom.toShHom).map ((underivedComparison w G).app F) ≫ m =
      (modulePullback h.toLRSHom.toShHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S'.toRingedSpace.sheaf).flip.obj G).map ((baseChangeNatTrans w).app F)) ≫
        (modulePullback h.toLRSHom.toShHom).map
            (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
              ((modulePullback g'.toLRSHom.toShHom).obj F) G) ≫ m :=
  (congrArg (fun t => t ≫ m) ((modulePullback h.toLRSHom.toShHom).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- **The hexagon of [Stacks, Tag 0E48]** for a commutative square of schemes, written at the
spelling of the comparison. -/
theorem projectionFormulaMap_baseChangeNatTrans {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
    {h : S'' ⟶ S'} {h' : X'' ⟶ X'} (w : h' ≫ f' = f'' ≫ h)
    (E : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    (K : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace)) :
    (tensorPullbackComparison h.toLRSHom.toShHom
            ((modulePushforward f'.toLRSHom.toShHom).obj E) K).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S''.toRingedSpace.sheaf).flip.obj
            ((modulePullback h.toLRSHom.toShHom).obj K)).map
            ((baseChangeNatTrans w).app E) ≫
          Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f''
            ((modulePullback h'.toLRSHom.toShHom).obj E)
            ((modulePullback h.toLRSHom.toShHom).obj K) =
      (modulePullback h.toLRSHom.toShHom).map
            (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f' E K) ≫
          (baseChangeNatTrans w).app
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  X'.toRingedSpace.sheaf).obj E).obj
                ((modulePullback f'.toLRSHom.toShHom).obj K)) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
              ((tensorPullbackComparison h'.toLRSHom.toShHom E
                  ((modulePullback f'.toLRSHom.toShHom).obj K)).hom ≫
                ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    X''.toRingedSpace.sheaf).obj
                    ((modulePullback h'.toLRSHom.toShHom).obj E)).map
                  ((squarePullbackIso w).inv.app K)) :=
  (projectionFormulaMap_baseChangeNatTrans_lhs w E K).trans
    ((Stacks.RingedSpace.projectionFormulaMap_baseChange h'.toLRSHom.toShHom
        f''.toLRSHom.toShHom f'.toLRSHom.toShHom h.toLRSHom.toShHom
        (Stacks.Modules.toShHom_comm w) E K).trans
      (projectionFormulaMap_baseChangeNatTrans_rhs w E K).symm)

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
