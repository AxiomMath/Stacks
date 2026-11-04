module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeAffineUnitCoherence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionSection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionUnitor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# Multiplication crosses the projection formula of [Stacks, Tag 0EX3] (c)

The projection formula the computation of conclusion (c) of [Stacks, Tag 0EX3] uses,
`…TopDegreeBaseChange.pushforwardPullbackTensorIsoRight`, is the comparison

`F' ⊗_{𝒪_{X'}} ((f')^* h_* 𝒪_{Y''}) ≅ h'_* (h')^* F'`

attached to a cartesian square with `h` affine and `F'` quasi-coherent. This file proves that it
carries multiplication by a global function `a` on `Y''`, acting in the structure-sheaf tensor
factor, to `h'_*`(multiplication by the pullback `f''^♯ a`) — which is what the right-hand end of
the comparison map of (c) needs.

The comparison has four factors, and three of them are crossed by naturality: the symmetry of
the tensor product, the structure-sheaf base change of the square, and the projection-formula
morphism itself, which is natural in both module arguments. The structure-sheaf base change is
the one with content of its own, and it is proved here first: it is the base-change morphism of
[Stacks, Tag 02KG] at the structure sheaf, which multiplication crosses by naturality, followed
by the direct image of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which it crosses by
`AlgebraicGeometry.IntegralTransformQcoh.pullbackUnitIso_sectionScalar`.

The fourth factor is the left unitor of the tensor product, crossed by
`…TopDegreeBaseChange.tensorSheafUnitLeftIso_sectionScalar`.

## Main results

* `…TopDegreeBaseChange.sectionScalar_comp_pullbackPushforwardUnitIso`: **the structure-sheaf
  base change of a cartesian square intertwines multiplication by a global function with
  multiplication by its pullback.**
* `…TopDegreeBaseChange.sectionScalar_comp_pushforwardPullbackTensorIsoRight`: **the projection
  formula intertwines multiplication in its structure-sheaf factor with multiplication
  upstairs.**

## Implementation notes

*The pullback of the function is named with its defining equation.* As in
`…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_baseScalar`, the pullback
`f''^♯ a` is taken as an argument together with the equation defining it, so that a consumer may
supply whichever spelling of it the surrounding computation has produced.

*Why the identity in the second argument of the projection formula is converted by hand.* The
naturality of the projection-formula morphism leaves `(h')^*(𝟙)` where the composite needs
`𝟙`, and the two are related by `CategoryTheory.Functor.map_id` — but the rewriting tactics
cannot see the occurrence, because the identity in the goal is taken at the category of module
sheaves of a scheme and the one in the naturality statement at the category of module sheaves of
the underlying ringed space. These are definitionally equal with different instance paths, so
the conversion is stated as `hkey` with its type written out and used as a rewrite.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.IntegralTransformQcoh
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard

variable {X' Y' X'' Y'' : Scheme.{u}} (f' : X' ⟶ Y') (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'')
  (h : Y'' ⟶ Y')

/-- **The structure-sheaf base change of a cartesian square intertwines multiplication by a
global function with multiplication by its pullback.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `h` affine, a global function `a` on `Y''` and its pullback `c = f''^♯ a` on `X''`, the
comparison `…TopDegreeBaseChange.pullbackPushforwardUnitIso` carries `(f')^*h_*`(multiplication
by `a`) to `h'_*`(multiplication by `c`).

The comparison is the base-change morphism of [Stacks, Tag 02KG] at the structure sheaf of
`Y''`, which multiplication crosses by naturality, followed by the direct image along `h'` of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, which it crosses by
`AlgebraicGeometry.IntegralTransformQcoh.pullbackUnitIso_sectionScalar`. -/
theorem sectionScalar_comp_pullbackPushforwardUnitIso (hsq : IsPullback h' f'' f' h)
    [IsAffineHom h] (a : Γ(Y'', ⊤)) (c : Γ(X'', ⊤)) (hc : f''.appTop.hom a = c) :
    (Scheme.Modules.pullback f').map
          ((Scheme.Modules.pushforward h).map
            (sectionScalar Y'' a (Scheme.unitModule Y''))) ≫
        (pullbackPushforwardUnitIso f' h' f'' h hsq).hom =
      (pullbackPushforwardUnitIso f' h' f'' h hsq).hom ≫
        (Scheme.Modules.pushforward h').map
          (sectionScalar X'' c (Scheme.unitModule X'')) := by
  subst hc
  exact comp_two_squares
    ((AffinePushforward.baseChangeNatTrans hsq.flip.w).naturality
      (sectionScalar Y'' a (Scheme.unitModule Y'')))
    (map_comp_square (Scheme.Modules.pushforward h')
      (pullbackUnitIso_sectionScalar f'' a))

/-- **The projection formula of [Stacks, Tag 0EX3] (c) intertwines multiplication in its
structure-sheaf factor with multiplication upstairs.** For a cartesian square with `h` affine, a
global function `a` on `Y''` with pullback `c` on `X''` and a quasi-coherent `F'`, the comparison
`…TopDegreeBaseChange.pushforwardPullbackTensorIsoRight` carries multiplication by `a` in the
factor `(f')^* h_* 𝒪_{Y''}` to `h'_*`(multiplication by `c`).

Three of the four factors of the comparison are crossed by naturality: the symmetry of the
tensor product by `…TopDegreeBaseChange.tensorSheafSchemeCommIso_naturality`, the structure-sheaf
base change by `sectionScalar_comp_pullbackPushforwardUnitIso` tensored into the first factor,
and the projection-formula morphism itself by
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_natural` in its first argument.
The fourth is the left unitor, crossed by
`…TopDegreeBaseChange.tensorSheafUnitLeftIso_sectionScalar`. -/
theorem sectionScalar_comp_pushforwardPullbackTensorIsoRight (hsq : IsPullback h' f'' f' h)
    [IsAffineHom h] [IsAffineHom h'] (F' : X'.Modules) (hF' : F'.IsQuasicoherent)
    (a : Γ(Y'', ⊤)) (c : Γ(X'', ⊤)) (hc : f''.appTop.hom a = c) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map
          ((𝟙 F' ×ₘ (Scheme.Modules.pullback f').map
                ((Scheme.Modules.pushforward h).map
                  (sectionScalar Y'' a (Scheme.unitModule Y''))) :
            ((F', (Scheme.Modules.pullback f').obj
              ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))) : _ × _) ⟶
              (F', (Scheme.Modules.pullback f').obj
                ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))))) ≫
        (pushforwardPullbackTensorIsoRight f' h' f'' h hsq F' hF').hom =
      (pushforwardPullbackTensorIsoRight f' h' f'' h hsq F' hF').hom ≫
        (Scheme.Modules.pushforward h').map
          (sectionScalar X'' c ((Scheme.Modules.pullback h').obj F')) := by
  rw [pushforwardPullbackTensorIsoRight_hom f' h' f'' h hsq F' hF']
  have s1 := tensorSheafSchemeCommIso_naturality X' F'
    ((Scheme.Modules.pullback f').map
      ((Scheme.Modules.pushforward h).map (sectionScalar Y'' a (Scheme.unitModule Y''))))
  have s3 := projectionFormulaMap_natural h'
    (sectionScalar X'' c (Scheme.unitModule X'')) (𝟙 F')
  have hkey : (RingedSpaceModuleAdjunction.modulePullback h'.toLRSHom.toShHom).map (𝟙 F') =
      𝟙 ((Scheme.Modules.pullback h').obj F') :=
    (RingedSpaceModuleAdjunction.modulePullback h'.toLRSHom.toShHom).map_id F'
  rw [hkey] at s3
  have s4 := map_comp_square (Scheme.Modules.pushforward h')
    (tensorSheafUnitLeftIso_sectionScalar X'' c ((Scheme.Modules.pullback h').obj F'))
  refine comp_two_squares s1 (comp_two_squares ?_ (comp_two_squares s3 s4))
  exact
      (Eq.trans
        (tensorSheaf_map_comp_left X' (B := F')
          ((Scheme.Modules.pullback f').map
            ((Scheme.Modules.pushforward h).map
              (sectionScalar Y'' a (Scheme.unitModule Y''))))
          (pullbackPushforwardUnitIso f' h' f'' h hsq).hom)
        (Eq.trans
          (congrArg
            (fun z : (Scheme.Modules.pullback f').obj
                  ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) ⟶
                (Scheme.Modules.pushforward h').obj (Scheme.unitModule X'') =>
              (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩)).map ((z ×ₘ 𝟙 F' :
                (((Scheme.Modules.pullback f').obj
                    ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')), F') : _ × _) ⟶
                  ((Scheme.Modules.pushforward h').obj (Scheme.unitModule X''), F'))))
            (sectionScalar_comp_pullbackPushforwardUnitIso f' h' f'' h hsq a c hc))
          (tensorSheaf_map_comp_left X' (B := F')
            (pullbackPushforwardUnitIso f' h' f'' h hsq).hom
            ((Scheme.Modules.pushforward h').map
              (sectionScalar X'' c (Scheme.unitModule X'')))).symm))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
