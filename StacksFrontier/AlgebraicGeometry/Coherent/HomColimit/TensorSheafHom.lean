module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowTensorSmul
public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom

/-!
# Morphisms out of a tensor product from morphisms into a sheaf Hom

Let `X` be a scheme and let `A`, `G`, `F` be `𝒪_X`-modules.  A morphism
`ψ : A ⟶ SheafHom_{𝒪_X}(G, F)` gives a morphism

`A ⊗_{𝒪_X} G ⟶ F`

sending a local pure tensor `a ⊗ g` to `ψ(a)(g)`. This file constructs that morphism and computes
it on local pure tensors.

The evaluation `SheafHom_{𝒪_X}(G, F) ⊗_{𝒪_X} G ⟶ F` of the tensor product of [Stacks, Tag 01CA] is
the sheafification of the evaluation pairing `Stacks.SheafOfModules.evalPresheaf` of presheaves of
modules, composed with the counit of the sheafification adjunction. Precomposing it with `ψ ⊗ 𝟙`
gives the morphism out of `A ⊗_{𝒪_X} G`.

## Main definitions

* `evalTensorPresheaf`: the evaluation pairing `SheafHom_{𝒪_X}(G, F) ⊗^{pre} G ⟶ F` of
  presheaves of modules, at the spelling of the presheaf tensor product of [Stacks, Tag 01CB].
* `evalTensorModules`: **the evaluation `SheafHom_{𝒪_X}(G, F) ⊗_{𝒪_X} G ⟶ F`** of
  `𝒪_X`-modules.
* `tensorHomToModule`: **the morphism `A ⊗_{𝒪_X} G ⟶ F` attached to a morphism
  `ψ : A ⟶ SheafHom_{𝒪_X}(G, F)`.**

## Main results

* `evalTensorModules_app_toTensorSheafSection`: the evaluation on a local pure tensor,
  `α ⊗ g ↦ α(g)`.
* `tensorHomToModule_app_toTensorSheafSection`: **the morphism `A ⊗_{𝒪_X} G ⟶ F` on a local pure
  tensor**, `a ⊗ g ↦ ψ(a)(g)`.

## Implementation notes

For `𝒪 = X.sheaf.obj` on the site of opens of a scheme, the source of
`Stacks.SheafOfModules.evalPresheaf` agrees definitionally with
`Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor`.

`evalTensorModules` is `(sheafifyFunctor X).map` of the presheaf pairing followed by
`Stacks.SheafOfModules.sheafifyValIso`; its action on sections is
`Stacks.SheafOfModules.TensorUnit.sheafifyMap_sheafifyValIso_sheafifyUnit`.

## References

* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealProduct
open Stacks.SheafOfModules

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.InternalHomModules

variable {X : Scheme.{u}}

/-- The evaluation pairing `SheafHom_{𝒪_X}(G, F) ⊗^{pre} G ⟶ F` of presheaves of modules, the
tensor product being the pointwise one of [Stacks, Tag 01CB].  On sections it sends `α ⊗ g` to
the value of `α` at `g`. -/
public noncomputable def evalTensorPresheaf (G F : X.Modules) :
    (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) ((sheafHomModules G F).val)
      (G.val)) ⟶ F.val :=
  evalPresheaf X.sheaf.obj (structureSheafRing X.toRingedSpace).property G F

/-- **The evaluation pairing `SheafHom_{𝒪_X}(G, F) ⊗_{𝒪_X} G ⟶ F`** of `𝒪_X`-modules on a
scheme: the sheafification of the presheaf pairing followed by the counit of the sheafification
adjunction. -/
public noncomputable def evalTensorModules (G F : X.Modules) :
    tensorModules (sheafHomModules G F) G ⟶ F :=
  (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).map
      (evalTensorPresheaf G F) ≫
    (Stacks.SheafOfModules.sheafifyValIso X.presheaf
      (structureSheafRing X.toRingedSpace).property F).hom

/-- **The evaluation pairing on a local pure tensor**: `α ⊗ g` goes to the value of `α` at `g`,
that is to the component of `α : G|_V ⟶ F|_V` at the terminal object of the slice site over `V`
applied to `g`. -/
public theorem evalTensorModules_app_toTensorSheafSection (G F : X.Modules) (V : X.Opens)
    (α : Γ(sheafHomModules G F, V)) (g : Γ(G, V)) :
    (evalTensorModules G F).app V (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
    X.toRingedSpace
        (sheafHomModules G F) G (op V) (α ⊗ₜ[X.presheaf.obj (op V)] g))
      = evalSection X.sheaf.obj G.val F.val (op V) α g :=
  Stacks.SheafOfModules.TensorUnit.sheafifyMap_sheafifyValIso_sheafifyUnit
    X.toRingedSpace F (evalTensorPresheaf G F) (op V) (α ⊗ₜ[X.presheaf.obj (op V)] g)

/-- **The morphism `A ⊗_{𝒪_X} G ⟶ F` attached to a morphism `ψ : A ⟶ SheafHom_{𝒪_X}(G, F)`**,
sending a local pure tensor `a ⊗ g` to `ψ(a)(g)`. -/
public noncomputable def tensorHomToModule {A G F : X.Modules}
    (ψ : A ⟶ sheafHomModules G F) : tensorModules A G ⟶ F :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
    (X := (A, G)) (Y := (sheafHomModules G F, G)) (ψ, 𝟙 G) ≫
    evalTensorModules G F

/-- **The morphism `A ⊗_{𝒪_X} G ⟶ F` on a local pure tensor**: `a ⊗ g` goes to `ψ(a)(g)`. -/
public theorem tensorHomToModule_app_toTensorSheafSection {A G F : X.Modules}
    (ψ : A ⟶ sheafHomModules G F) (V : X.Opens) (a : Γ(A, V)) (g : Γ(G, V)) :
    (tensorHomToModule ψ).app V (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
    X.toRingedSpace A G (op V)
        (a ⊗ₜ[X.presheaf.obj (op V)] g))
      = evalSection X.sheaf.obj G.val F.val (op V) (ψ.app V a) g :=
  (congrArg (ConcreteCategory.hom ((evalTensorModules G F).app V))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      X.toRingedSpace A G (sheafHomModules G F) G ψ (𝟙 G) V a g)).trans
    (evalTensorModules_app_toTensorSheafSection G F V (ψ.app V a) g)

end Stacks.AlgebraicGeometry.InternalHomModules

end

end
