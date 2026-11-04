module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.PastingComparisons

/-!
# The pasting law for the comparison of flat base change

Let

```
X'' --h'--> X' --g'--> X
|f''        |f'        |f
v           v          v
S'' --h-->  S' --g-->  S
```

be two commutative squares of schemes stacked along the base and let `G` be an `𝒪_{S'}`-module.
The outer rectangle is again a commutative square, and this file proves that the comparison of
[Stacks, Tag 0GN5] for the rectangle and the module `h^*G` is the composite of the comparison for
the right-hand square and the base-change morphism of the left-hand square, read through the two
identifications of `PastingComparisons.lean` of the coefficient functors under a further inverse
image:

* underived, as an identity of morphisms of `𝒪_{S''}`-modules;
* and on bounded below derived categories, where the composite of the two descents is
  `Stacks.Cohomology.BaseChange.derivedPaste`.

The derived statement is the one the reduction of [Stacks, Tag 0GN5] to affine bases needs: with
`h` the inclusion of an open `V` of `S'` and `h'` the inclusion of its inverse image in `X'`, it
says that the derived comparison restricted to `V` is the derived comparison of the restricted
square.

## The route

The underived identity is the hexagon of [Stacks, Tag 0E48] and the pasting law for the
base-change morphism of [Stacks, Tag 02KG], glued by naturality. Unwinding both sides through
`Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_app`, the comparison of the
rectangle is the base-change morphism of the rectangle tensored with `h^*G`, followed by the
projection-formula morphism of [Stacks, Tag 0FZE] for `f''`; the pasted composite is the
base-change morphism of the right-hand square tensored with `G`, pulled back along `h`, then the
projection formula for `f'` pulled back, then the base-change morphism of the left-hand square.
The hexagon moves the projection formula for `f'` past the base-change morphism of the left-hand
square, naturality of [Stacks, Tag 01CD] moves the comparison past the tensored base-change
morphism, naturality of the projection formula moves the identification of the composite inverse
images out of the direct image, and what remains is the pasting law for the base-change morphism.

The derived identity is then `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste`, whose sole
hypothesis is that underived identity. Nothing else is needed: that generic descent asks only
for exactness of the horizontal legs, and the derived-functor units of exact functors are
invertible.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_pasteBase`: **the underived
  pasting law**, in the shape `derived_eq_derivedPaste` consumes — the comparison of the
  rectangle, read through the inverse of the identification on the base.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_pasteBase_hom`: the same
  identity with that identification on the other side, where no inverse occurs.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison_eq_derivedPaste`: **the derived
  pasting law** — the descent of the rectangle's comparison is
  `Stacks.Cohomology.BaseChange.derivedPaste` of the two squares.

## Implementation notes

Neither statement needs the squares to be cartesian, and neither needs `G` quasi-coherent; the
underived one needs no hypothesis at all beyond the two commutativities. The derived one needs
exactness of the two coefficient functors on the base and of the two inverse images `h^*` and
`(h')^*`, which are the hypotheses of the generic descent; they are taken as instance arguments,
to be supplied by `Stacks.AlgebraicGeometry.ModuleBaseChange.preservesFiniteLimits_baseCoefficients`
and its companions, or found by instance search when `h` and `h'` are open immersions.

The proof is split into `pasteBase_lhs`, `pasteBase_mid` and `pasteBase_rhs` because the two
sides of the identity are stated in the vocabulary of the coefficient functors and proved in the
vocabulary of the tensor product: crossing between the two is `rfl` but not reducibly so, and
doing it in one declaration exceeds the elaborator's heartbeat budget. `pasteBase_lhs` and
`pasteBase_rhs` are the two crossings and `pasteBase_mid` is the mathematics.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance] HasDerivedCategory.standard

variable {S S' S'' X X' X'' : Scheme.{u}}

section Underived

variable {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

private theorem pasteBase_lhs (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (baseCoefficientsPullbackIso g h G).hom.app
          ((modulePushforward f.toLRSHom.toShHom).obj F) ≫
        (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂)
          ((modulePullback h.toLRSHom.toShHom).obj G)).app F =
      (tensorPullbackComparison h.toLRSHom.toShHom
            ((modulePullback g.toLRSHom.toShHom).obj
              ((modulePushforward f.toLRSHom.toShHom).obj F)) G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S''.toRingedSpace.sheaf).flip.obj
            ((modulePullback h.toLRSHom.toShHom).obj G)).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
              g.toLRSHom.toShHom).hom.app ((modulePushforward f.toLRSHom.toShHom).obj F)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S''.toRingedSpace.sheaf).flip.obj
              ((modulePullback h.toLRSHom.toShHom).obj G)).map
              ((baseChangeNatTrans (FlatBaseChangeCohomology.pasteBase w₁ w₂)).app F) ≫
            Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f''
              ((modulePullback (h' ≫ g').toLRSHom.toShHom).obj F)
              ((modulePullback h.toLRSHom.toShHom).obj G) := by
  rw [underivedComparison_app]
  exact Category.assoc _ _ _

private theorem pasteBase_rhs (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (modulePullback h.toLRSHom.toShHom).map ((underivedComparison w₁ G).app F) ≫
        (baseChangeNatTrans w₂).app ((totalCoefficients g' f' G).obj F) ≫
          (modulePushforward f''.toLRSHom.toShHom).map
            ((totalCoefficientsPullbackIso g' w₂ G).hom.app F) =
      (modulePullback h.toLRSHom.toShHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S'.toRingedSpace.sheaf).flip.obj G).map ((baseChangeNatTrans w₁).app F)) ≫
        (modulePullback h.toLRSHom.toShHom).map
            (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
              ((modulePullback g'.toLRSHom.toShHom).obj F) G) ≫
          (baseChangeNatTrans w₂).app
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    X'.toRingedSpace.sheaf).obj
                  ((modulePullback g'.toLRSHom.toShHom).obj F)).obj
                ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
                ((tensorPullbackComparison h'.toLRSHom.toShHom
                    ((modulePullback g'.toLRSHom.toShHom).obj F)
                    ((modulePullback f'.toLRSHom.toShHom).obj G)).hom ≫
                  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      X''.toRingedSpace.sheaf).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj
                        ((modulePullback g'.toLRSHom.toShHom).obj F))).map
                    ((squarePullbackIso w₂).inv.app G)) ≫
              (modulePushforward f''.toLRSHom.toShHom).map
                (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      X''.toRingedSpace.sheaf).flip.obj
                    ((modulePullback f''.toLRSHom.toShHom).obj
                      ((modulePullback h.toLRSHom.toShHom).obj G))).map
                  ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
                    g'.toLRSHom.toShHom).hom.app F)) := by
  rw [map_underivedComparison_app_assoc, map_totalCoefficientsPullbackIso_hom_app]
  rfl

private theorem pasteBase_mid (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (tensorPullbackComparison h.toLRSHom.toShHom
            ((modulePullback g.toLRSHom.toShHom).obj
              ((modulePushforward f.toLRSHom.toShHom).obj F)) G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              S''.toRingedSpace.sheaf).flip.obj
            ((modulePullback h.toLRSHom.toShHom).obj G)).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
              g.toLRSHom.toShHom).hom.app ((modulePushforward f.toLRSHom.toShHom).obj F)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S''.toRingedSpace.sheaf).flip.obj
              ((modulePullback h.toLRSHom.toShHom).obj G)).map
              ((baseChangeNatTrans (FlatBaseChangeCohomology.pasteBase w₁ w₂)).app F) ≫
            Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f''
              ((modulePullback (h' ≫ g').toLRSHom.toShHom).obj F)
              ((modulePullback h.toLRSHom.toShHom).obj G) =
      (modulePullback h.toLRSHom.toShHom).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                S'.toRingedSpace.sheaf).flip.obj G).map ((baseChangeNatTrans w₁).app F)) ≫
        (modulePullback h.toLRSHom.toShHom).map
            (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f'
              ((modulePullback g'.toLRSHom.toShHom).obj F) G) ≫
          (baseChangeNatTrans w₂).app
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                    X'.toRingedSpace.sheaf).obj
                  ((modulePullback g'.toLRSHom.toShHom).obj F)).obj
                ((modulePullback f'.toLRSHom.toShHom).obj G)) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
                ((tensorPullbackComparison h'.toLRSHom.toShHom
                    ((modulePullback g'.toLRSHom.toShHom).obj F)
                    ((modulePullback f'.toLRSHom.toShHom).obj G)).hom ≫
                  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      X''.toRingedSpace.sheaf).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj
                        ((modulePullback g'.toLRSHom.toShHom).obj F))).map
                    ((squarePullbackIso w₂).inv.app G)) ≫
              (modulePushforward f''.toLRSHom.toShHom).map
                (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                      X''.toRingedSpace.sheaf).flip.obj
                    ((modulePullback f''.toLRSHom.toShHom).obj
                      ((modulePullback h.toLRSHom.toShHom).obj G))).map
                  ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
                    g'.toLRSHom.toShHom).hom.app F)) := by
  have hp := (projectionNatTrans f'' ((modulePullback h.toLRSHom.toShHom).obj G)).naturality
    ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
      g'.toLRSHom.toShHom).hom.app F)
  dsimp only [Functor.comp_map, Functor.comp_obj, projectionNatTrans_app] at hp
  have hc := (tensorRightFactorPullbackIso h G).hom.naturality ((baseChangeNatTrans w₁).app F)
  dsimp only [Functor.comp_map, Functor.comp_obj, tensorRightFactorPullbackIso_hom_app] at hc
  have hx := projectionFormulaMap_baseChangeNatTrans w₂
    ((modulePullback g'.toLRSHom.toShHom).obj F) G
  dsimp only [Functor.comp_obj] at hx
  dsimp only [toShHom_comp]
  rw [baseChangeNatTrans_pasteBase_app w₁ w₂, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hx, reassoc_of% hc, Functor.map_comp_assoc,
    Functor.map_comp_assoc, hp]

/-- **The underived pasting law**, with the identification of the coefficient functors on the
base composed on the left: the comparison of [Stacks, Tag 0GN5] for the outer rectangle, read
through `baseCoefficientsPullbackIso`, is the inverse image along `h` of the comparison for the
right-hand square followed by the base-change morphism of the left-hand square and the
identification of the coefficient functors upstairs. -/
theorem underivedComparison_pasteBase_hom (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (baseCoefficientsPullbackIso g h G).hom.app
          ((modulePushforward f.toLRSHom.toShHom).obj F) ≫
        (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂)
          ((modulePullback h.toLRSHom.toShHom).obj G)).app F =
      (modulePullback h.toLRSHom.toShHom).map ((underivedComparison w₁ G).app F) ≫
        (baseChangeNatTrans w₂).app ((totalCoefficients g' f' G).obj F) ≫
          (modulePushforward f''.toLRSHom.toShHom).map
            ((totalCoefficientsPullbackIso g' w₂ G).hom.app F) :=
  (pasteBase_lhs w₁ w₂ G F).trans
    ((pasteBase_mid w₁ w₂ G F).trans (pasteBase_rhs w₁ w₂ G F).symm)


/-- **The underived pasting law**, in the shape the derived descent consumes: the comparison of
[Stacks, Tag 0GN5] for the outer rectangle is the inverse of the identification on the base,
followed by the inverse image of the comparison for the right-hand square, the base-change
morphism of the left-hand square, and the direct image of the identification upstairs. -/
theorem underivedComparison_pasteBase (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂)
        ((modulePullback h.toLRSHom.toShHom).obj G)).app F =
      (baseCoefficientsPullbackIso g h G).inv.app
          ((modulePushforward f.toLRSHom.toShHom).obj F) ≫
        (modulePullback h.toLRSHom.toShHom).map ((underivedComparison w₁ G).app F) ≫
          (baseChangeNatTrans w₂).app ((totalCoefficients g' f' G).obj F) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
              ((totalCoefficientsPullbackIso g' w₂ G).hom.app F) := by
  rw [← underivedComparison_pasteBase_hom w₁ w₂ G F, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

end Underived

section Derived

variable {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- **The pasting law for the derived comparison of [Stacks, Tag 0GN5].**  For two commutative
squares of schemes stacked along the base and an `𝒪_{S'}`-module `G`, the descent to bounded
below derived categories of the comparison of the outer rectangle at the module `h^*G` is the
composite of the descents of the two squares, read through the identifications of the two
coefficient functors under the further inverse images.

Neither square is required to be cartesian and `G` is arbitrary; what is used is exactness of
the two coefficient functors on the base and of the inverse images along `h` and `h'`. -/
theorem derivedComparison_eq_derivedPaste (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (G : SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
    [PreservesFiniteLimits (baseCoefficients g G)]
    [PreservesFiniteColimits (baseCoefficients g G)]
    [PreservesFiniteLimits (modulePullback h.toLRSHom.toShHom)]
    [PreservesFiniteColimits (modulePullback h.toLRSHom.toShHom)]
    [PreservesFiniteLimits
      (baseCoefficients (h ≫ g) ((modulePullback h.toLRSHom.toShHom).obj G))]
    [PreservesFiniteColimits
      (baseCoefficients (h ≫ g) ((modulePullback h.toLRSHom.toShHom).obj G))]
    [PreservesFiniteLimits (modulePullback h'.toLRSHom.toShHom)]
    [PreservesFiniteColimits (modulePullback h'.toLRSHom.toShHom)]
    (hG : AlgebraicGeometry.IsFlatOver (h ≫ g).toLRSHom.toShHom
      ((modulePullback h.toLRSHom.toShHom).obj G)) :
    derivedComparison ((modulePullback h.toLRSHom.toShHom).obj G)
        (FlatBaseChangeCohomology.pasteBase w₁ w₂) hG =
      Stacks.Cohomology.BaseChange.derivedPaste
        (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
        (modulePushforward f''.toLRSHom.toShHom) (baseCoefficients g G)
        (modulePullback h.toLRSHom.toShHom)
        (baseCoefficients (h ≫ g) ((modulePullback h.toLRSHom.toShHom).obj G))
        (totalCoefficients g' f' G) (modulePullback h'.toLRSHom.toShHom)
        (totalCoefficients (h' ≫ g') f'' ((modulePullback h.toLRSHom.toShHom).obj G))
        (baseCoefficientsPullbackIso g h G) (totalCoefficientsPullbackIso g' w₂ G)
        (underivedComparison w₁ G) (baseChangeNatTrans w₂) :=
  Stacks.Cohomology.BaseChange.derived_eq_derivedPaste
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (modulePushforward f''.toLRSHom.toShHom) (baseCoefficients g G)
    (modulePullback h.toLRSHom.toShHom)
    (baseCoefficients (h ≫ g) ((modulePullback h.toLRSHom.toShHom).obj G))
    (totalCoefficients g' f' G) (modulePullback h'.toLRSHom.toShHom)
    (totalCoefficients (h' ≫ g') f'' ((modulePullback h.toLRSHom.toShHom).obj G))
    (baseCoefficientsPullbackIso g h G) (totalCoefficientsPullbackIso g' w₂ G)
    (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂)
      ((modulePullback h.toLRSHom.toShHom).obj G))
    (underivedComparison w₁ G) (baseChangeNatTrans w₂)
    (underivedComparison_pasteBase w₁ w₂ G)

end Derived

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
