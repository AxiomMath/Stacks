module

public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.BaseChangeDerivedIso
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Pasting

/-!
# The pasting law for a rectangle whose right-hand square carries no coefficients

Let

```
X'' --h'--> X' --g'--> X
|f''        |f'        |f
v           v          v
S'' --h-->  S' --g-->  S
```

be two commutative squares of schemes stacked along the base and let `M` be an
`𝒪_{S''}`-module — a module on the *far* base, not on the middle one.  The comparison of
[Stacks, Tag 0GN5] for the outer rectangle at `M` then decomposes differently from the way
`Pasting.lean` decomposes it: the right-hand square contributes only its base-change morphism of
[Stacks, Tag 02KG], with no coefficients, and the whole twist by `M` sits in the comparison of the
left-hand square.

This is the decomposition that shrinks the base of the *source*: with `g = U.ι` the inclusion of
an open `U` of `S` and `g'` the inclusion of its inverse image in `X`, the right-hand square is a
restriction square, whose base-change morphism is invertible, so the rectangle's comparison and
the comparison of the square over `U` are invertible together.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseCoefficientsCompIso`: the identification
  `g^* ∘ Φ_h ≅ Φ_{h ≫ g}` of the coefficient functors on the base under a further inverse image
  *on the other side*.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.totalCoefficientsCompIso`: the same for the
  coefficient functor upstairs.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.underivedComparison_pasteBaseChange`: **the underived
  pasting law** — the comparison of the rectangle is the inverse image of the base-change morphism
  of the right-hand square, followed by the comparison of the left-hand square, read through the
  two identifications.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.derivedComparison_eq_derivedPasteBaseChange`: **the
  derived pasting law**, the descent of that identity to bounded below derived categories.

## Implementation notes

The underived identity needs two inputs and no hexagon: the pasting law for the base-change
morphism of [Stacks, Tag 02KG], available as `baseChangeNatTrans_pasteBase_app`, and naturality of
the projection-formula morphism of [Stacks, Tag 0FZE] in its first variable.  This is why it is
much shorter than `underivedComparison_pasteBase`: there the base-change morphism of the left-hand
square has to be moved past the projection formula of the right-hand one, which is the hexagon of
[Stacks, Tag 0E48]; here the only coefficients are those of the left-hand square, which is the
last factor, and nothing has to cross anything.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' S'' X X' X'' : Scheme.{u}}

/-! ### The two identifications -/

/-- **The coefficient functor on the base under a further inverse image on the other side**: for
`h : S'' ⟶ S'`, `g : S' ⟶ S` and an `𝒪_{S''}`-module `M`, the composite of the inverse image along
`g` with `Φ_h = h^*(-) ⊗ M` is `Φ_{h ≫ g}`.  This is the comparison of the composite inverse
images, tensored with the identity of `M`. -/
def baseCoefficientsCompIso (g : S' ⟶ S) (h : S'' ⟶ S')
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace)) :
    modulePullback g.toLRSHom.toShHom ⋙ baseCoefficients h M ≅ baseCoefficients (h ≫ g) M :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
        g.toLRSHom.toShHom)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        S''.toRingedSpace.sheaf).flip.obj M)

theorem baseCoefficientsCompIso_inv_app (g : S' ⟶ S) (h : S'' ⟶ S')
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace))
    (N : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (baseCoefficientsCompIso g h M).inv.app N =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S''.toRingedSpace.sheaf).flip.obj M).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
          g.toLRSHom.toShHom).inv.app N) :=
  Category.comp_id _

/-- **The coefficient functor upstairs under a further inverse image on the other side**: for
`h' : X'' ⟶ X'`, `g' : X' ⟶ X`, `f'' : X'' ⟶ S''` and an `𝒪_{S''}`-module `M`, the composite of
the inverse image along `g'` with `Ψ_{h'} = (h')^*(-) ⊗ (f'')^*M` is `Ψ_{h' ≫ g'}`. -/
def totalCoefficientsCompIso (g' : X' ⟶ X) (h' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace)) :
    modulePullback g'.toLRSHom.toShHom ⋙ totalCoefficients h' f'' M ≅
      totalCoefficients (h' ≫ g') f'' M :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
        g'.toLRSHom.toShHom)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X''.toRingedSpace.sheaf).flip.obj ((modulePullback f''.toLRSHom.toShHom).obj M))

theorem totalCoefficientsCompIso_hom_app (g' : X' ⟶ X) (h' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (totalCoefficientsCompIso g' h' f'' M).hom.app F =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X''.toRingedSpace.sheaf).flip.obj
          ((modulePullback f''.toLRSHom.toShHom).obj M)).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
          g'.toLRSHom.toShHom).hom.app F) :=
  Category.id_comp _

/-! ### The underived pasting law -/

section Underived

variable {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- **The underived pasting law for a rectangle whose right-hand square carries no
coefficients.**  The comparison of [Stacks, Tag 0GN5] for the outer rectangle at an
`𝒪_{S''}`-module `M` is the inverse image along `g` of the base-change morphism of the right-hand
square, followed by the comparison of the left-hand square at the inverse image of `F`, read
through the identifications `baseCoefficientsCompIso` and `totalCoefficientsCompIso`.

Neither square need be cartesian and `M` is arbitrary. -/
theorem underivedComparison_pasteBaseChange (w₁ : g' ≫ f = f' ≫ g) (w₂ : h' ≫ f' = f'' ≫ h)
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace))
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂) M).app F =
      (baseCoefficientsCompIso g h M).inv.app ((modulePushforward f.toLRSHom.toShHom).obj F) ≫
        (baseCoefficients h M).map
            (X := (modulePullback g.toLRSHom.toShHom).obj
              ((modulePushforward f.toLRSHom.toShHom).obj F))
            ((baseChangeNatTrans w₁).app F) ≫
          (underivedComparison w₂ M).app ((modulePullback g'.toLRSHom.toShHom).obj F) ≫
            (modulePushforward f''.toLRSHom.toShHom).map
              ((totalCoefficientsCompIso g' h' f'' M).hom.app F) := by
  have hnat := (projectionNatTrans f'' M).naturality
    ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
      g'.toLRSHom.toShHom).hom.app F)
  dsimp only [Functor.comp_map, projectionNatTrans_app] at hnat
  have hbase : (baseCoefficients h M).map
        (X := (modulePullback g.toLRSHom.toShHom).obj
          ((modulePushforward f.toLRSHom.toShHom).obj F))
        ((baseChangeNatTrans w₁).app F) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S''.toRingedSpace.sheaf).flip.obj M).map
        ((modulePullback h.toLRSHom.toShHom).map ((baseChangeNatTrans w₁).app F)) := rfl
  rw [underivedComparison_app, baseChangeNatTrans_pasteBase_app w₁ w₂ F,
    baseCoefficientsCompIso_inv_app, hbase, underivedComparison_app,
    totalCoefficientsCompIso_hom_app]
  dsimp only [Functor.comp_obj, toShHom_comp]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hnat]
  simp only [Category.assoc, Functor.comp_obj]
  exact congrArg (fun arrow =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S''.toRingedSpace.sheaf).flip.obj M).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp h.toLRSHom.toShHom
            g.toLRSHom.toShHom).inv.app ((modulePushforward f.toLRSHom.toShHom).obj F)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            S''.toRingedSpace.sheaf).flip.obj M).map
            ((modulePullback h.toLRSHom.toShHom).map ((baseChangeNatTrans w₁).app F)) ≫ arrow)
    (Category.assoc
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          S''.toRingedSpace.sheaf).flip.obj M).map
        ((baseChangeNatTrans w₂).app ((modulePullback g'.toLRSHom.toShHom).obj F)))
      (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap f''
        ((modulePullback h'.toLRSHom.toShHom).obj
          ((modulePullback g'.toLRSHom.toShHom).obj F)) M)
      ((modulePushforward f''.toLRSHom.toShHom).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              X''.toRingedSpace.sheaf).flip.obj
            ((modulePullback f''.toLRSHom.toShHom).obj M)).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp h'.toLRSHom.toShHom
            g'.toLRSHom.toShHom).hom.app F)))).symm

end Underived

/-! ### The derived pasting law -/

section Derived

variable {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
  {g : S' ⟶ S} {g' : X' ⟶ X} {h : S'' ⟶ S'} {h' : X'' ⟶ X'}

/-- **The pasting law for the derived comparison of [Stacks, Tag 0GN5] along a rectangle whose
right-hand square carries no coefficients.**  The descent to bounded below derived categories of
the comparison of the outer rectangle at an `𝒪_{S''}`-module `M` is
`Stacks.Cohomology.BaseChange.derivedPaste` of the base-change morphism of the right-hand square
and the comparison of the left-hand square.

What is used is exactness of the inverse image along `g` and of the two coefficient functors
`Φ_h` and `Φ_{h ≫ g}`, and exactness of `Ψ_{h'}`; they are instance arguments. -/
theorem derivedComparison_eq_derivedPasteBaseChange (w₁ : g' ≫ f = f' ≫ g)
    (w₂ : h' ≫ f' = f'' ≫ h)
    (M : SheafOfModules.{u} (structureSheafRing S''.toRingedSpace))
    [PreservesFiniteLimits (modulePullback g.toLRSHom.toShHom)]
    [PreservesFiniteColimits (modulePullback g.toLRSHom.toShHom)]
    [PreservesFiniteLimits (baseCoefficients h M)] [PreservesFiniteColimits (baseCoefficients h M)]
    [PreservesFiniteLimits (baseCoefficients (h ≫ g) M)]
    [PreservesFiniteColimits (baseCoefficients (h ≫ g) M)]
    [PreservesFiniteLimits (totalCoefficients h' f'' M)]
    [PreservesFiniteColimits (totalCoefficients h' f'' M)]
    (hM : AlgebraicGeometry.IsFlatOver (h ≫ g).toLRSHom.toShHom M) :
    derivedComparison M (FlatBaseChangeCohomology.pasteBase w₁ w₂) hM =
      Stacks.Cohomology.BaseChange.derivedPaste
        (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
        (modulePushforward f''.toLRSHom.toShHom) (modulePullback g.toLRSHom.toShHom)
        (baseCoefficients h M) (baseCoefficients (h ≫ g) M)
        (modulePullback g'.toLRSHom.toShHom) (totalCoefficients h' f'' M)
        (totalCoefficients (h' ≫ g') f'' M)
        (baseCoefficientsCompIso g h M) (totalCoefficientsCompIso g' h' f'' M)
        (baseChangeNatTrans w₁) (underivedComparison w₂ M) :=
  Stacks.Cohomology.BaseChange.derived_eq_derivedPaste
    (modulePushforward f.toLRSHom.toShHom) (modulePushforward f'.toLRSHom.toShHom)
    (modulePushforward f''.toLRSHom.toShHom) (modulePullback g.toLRSHom.toShHom)
    (baseCoefficients h M) (baseCoefficients (h ≫ g) M)
    (modulePullback g'.toLRSHom.toShHom) (totalCoefficients h' f'' M)
    (totalCoefficients (h' ≫ g') f'' M)
    (baseCoefficientsCompIso g h M) (totalCoefficientsCompIso g' h' f'' M)
    (underivedComparison (FlatBaseChangeCohomology.pasteBase w₁ w₂) M)
    (baseChangeNatTrans w₁) (underivedComparison w₂ M)
    (underivedComparison_pasteBaseChange w₁ w₂ M)

end Derived

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
