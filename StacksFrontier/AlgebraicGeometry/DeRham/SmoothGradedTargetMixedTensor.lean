module

public import StacksFrontier.AlgebraicGeometry.DeRham.MixedTensorRingSheafBinders
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTarget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SheafificationAndRestrictionOfScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSymmNaturality

/-!
# The two coefficient rings of the graded piece of Section 0FMK

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. The comparison onto the graded pieces of the filtration of `Ω^n_{X/S}`
by the forms pulled back from `Y` has, after [Stacks, Tag 01CI], the source

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y}`

(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`), a tensor product
over `𝒪_X`. Section 50.12 writes the graded piece with a tensor product over `f^{-1}𝒪_Y`
instead,

`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{m+1}_{X/Y}`,

and that is the ring over which `Stacks.DeRhamSmooth.gradedTargetComplex` is formed. **This file
identifies the two readings.**

The identity is the underived half of [Stacks, Tag 08DE], `F ⊗_{𝒪_X} f^*G ≅ F ⊗_{f^{-1}𝒪_Y}
f^{-1}G`, in the form that records the `f^{-1}𝒪_Y`-module structure rather than the `𝒪_X`-linear
one: `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageLinearIso`, which is
unconditional.

`(Tensor.sheafTensor 𝒪).flip.obj G` is `F ↦ F ⊗_𝒪 G`, a tensor product on the right; the generic
identity is stated with it, while `Stacks.DeRhamSmooth.pulledBackTargetFormsTensor` and the source
of `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` tensor on the
left, so each side is turned around by the symmetry of the tensor product.

## Main results

* `Stacks.DeRhamSmooth.pulledBackTargetForms_eq_pullbackTopos` and
  `Stacks.DeRhamSmooth.pullbackTopos_relativeDifferentialForms`: the inverse image and the
  pullback of `Ω^k_{Y/S}` taken along the topos factorization of `f` are the ones of the de Rham
  tree, by `rfl`.
* `Stacks.DeRhamSmooth.targetFormsMixedTensorNatIso` and
  `Stacks.DeRhamSmooth.targetFormsMixedTensorIso`: **[Stacks, Tag 08DE] at the binders of
  Section 0FMK** —
  `F|_{f^{-1}𝒪_Y} ⊗_{f^{-1}𝒪_Y} f^{-1}Ω^k_{Y/S} ≅ (F ⊗_{𝒪_X} f^*Ω^k_{Y/S})|_{f^{-1}𝒪_Y}`,
  as an isomorphism of functors of the sheaf `F` of `𝒪_X`-modules and at one such `F`, with
  `Stacks.DeRhamSmooth.targetFormsMixedTensorIso_naturality` the resulting square.
* `Stacks.DeRhamSmooth.deRhamTermMixedTensorIso`: the same at `F = Ω^m_{X/Y}`, so that the left
  side is read on a term of the relative de Rham complex of `f`.
* `Stacks.DeRhamSmooth.tensorFunctorSymmIso` and
  `Stacks.DeRhamSmooth.tensorFunctorSymmIso'`: the symmetry of the tensor product on a ringed
  space, in the two orientations crossing between the three spellings of it that the two sides
  use, with `Stacks.DeRhamSmooth.tensorFunctor_obj_obj_eq_sheafTensorRight` and
  `Stacks.DeRhamSmooth.tensorSheafBifunctor_obj_eq_sheafTensorRight` the `rfl` identities that
  make the crossings legitimate. `Stacks.DeRhamSmooth.tensorFunctorSymmIso_naturality` and
  `Stacks.DeRhamSmooth.tensorFunctorSymmIso'_naturality` say each is **natural in the factor that
  crosses between the functor position and the object position**;
  `Stacks.DeRhamSmooth.pulledBackTargetFormsTensorSymmIso_naturality` and
  `Stacks.DeRhamSmooth.pullbackFormsTensorSymmIso_naturality` are their instances at the two
  sides.
* `Stacks.DeRhamSmooth.gradedSourceMixedTensorIso`: **the identity in the spelling each side
  uses** —
  `f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|_{f^{-1}𝒪_Y} ≅ (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|_{f^{-1}𝒪_Y}`, the
  left side the endofunctor `Stacks.DeRhamSmooth.gradedTargetComplex` is built from and the
  object inside the restriction on the right the source of
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`.
* `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso`: **the same identity read over
  `(f ∘ g)^{-1}𝒪_S`**, the coefficient ring `Stacks.DeRhamSmooth.gradedTargetComplex` and
  `Stacks.DeRhamSmooth.gradedPiece` are formed over, rather than over `f^{-1}𝒪_Y`. Its left side
  is the shape of a term of `Stacks.DeRhamSmooth.gradedTargetComplex`.
* `Stacks.DeRhamSmooth.gradedSourceMixedTensorIso_naturality` and
  `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso_naturality`: **both readings of the
  identity are natural in `F`**.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.MixedDerivedTensor
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace
open StacksPullbackFactorization

universe u

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The inverse image of `Ω^k_{Y/S}` along the geometric half of the topos factorization of
`f` is `Stacks.DeRhamSmooth.pulledBackTargetForms`.** Both are the module pullback along the
projection `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)`. -/
theorem pulledBackTargetForms_eq_pullbackTopos (k : ℕ) :
    (auxHomG (ringedToposSiteHom f.toLRSHom.toShHom)).pullbackTopos.obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      pulledBackTargetForms f g k :=
  rfl

/-- **The pullback of `Ω^k_{Y/S}` along the topos presentation of `f` is the pullback of sheaves
of modules along `f`.** This is
`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.pullbackTopos_eq` read on `Ω^k_{Y/S}`, and
it identifies the `𝒪_X`-linear side of [Stacks, Tag 08DE] with the first factor of the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`. -/
theorem pullbackTopos_relativeDifferentialForms (k : ℕ) :
    (ringedToposSiteHom f.toLRSHom.toShHom).pullbackTopos.obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      (Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) :=
  rfl

/-- **The underived identity of [Stacks, Tag 08DE] at the binders of Section 0FMK, as an
isomorphism of functors of `F`.** It is
`Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageLinearIso`, stated with the
inverse image and the pullback of `Ω^k_{Y/S}` and the coefficient ring sheaves of the de Rham
tree. -/
def targetFormsMixedTensorNatIso (k : ℕ) :
    pushforward (toInverseImageBase f) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor
            ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor
          X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) ⋙
        pushforward (toInverseImageBase f) :=
  underivedTensorInverseImageLinearIso (ringedToposSiteHom f.toLRSHom.toShHom)
    (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))

/-- **The underived identity of [Stacks, Tag 08DE] at the binders of Section 0FMK**: for a sheaf
`F` of `𝒪_X`-modules,

`F|_{f^{-1}𝒪_Y} ⊗_{f^{-1}𝒪_Y} f^{-1}Ω^k_{Y/S} ≅ (F ⊗_{𝒪_X} f^*Ω^k_{Y/S})|_{f^{-1}𝒪_Y}`,

naturally in `F`. The left-hand side is the tensor product over `f^{-1}𝒪_Y` that Section 50.12
writes the graded piece with, taken in the category of sheaves of `f^{-1}𝒪_Y`-modules that
`Stacks.DeRhamSmooth.gradedTargetComplex` lives in; the right-hand side is the `𝒪_X`-linear
tensor product of the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`, read over
`f^{-1}𝒪_Y`. Nothing is assumed of `f`. -/
def targetFormsMixedTensorIso (k : ℕ) (F : Modules X.toRingedSpace) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k)).obj
        ((pushforward (toInverseImageBase f)).obj F) ≅
      (pushforward (toInverseImageBase f)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).obj F) :=
  (targetFormsMixedTensorNatIso f g k).app F

/-- **[Stacks, Tag 08DE] at a term of the relative de Rham complex of `f`**:

`Ω^m_{X/Y} ⊗_{f^{-1}𝒪_Y} f^{-1}Ω^k_{Y/S} ≅ (Ω^m_{X/Y} ⊗_{𝒪_X} f^*Ω^k_{Y/S})|_{f^{-1}𝒪_Y}`.

This is `Stacks.DeRhamSmooth.targetFormsMixedTensorIso` at `F = Ω^m_{X/Y}`, the left-hand side
read on the degree-`m` term of `Stacks.DeRhamDirectImage.deRhamCochainComplex` at `f` — which is
`Ω^m_{X/Y}` restricted to `f^{-1}𝒪_Y` by
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`, pushforward along
`Stacks.DeRhamDirectImage.toInverseImageBase` being that restriction of scalars
(`Stacks.DeRhamDirectImage.pushforward_toInverseImageBase`). -/
def deRhamTermMixedTensorIso (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k)).obj
        ((AlgebraicGeometry.Scheme.Hom.deRhamComplex f).X m) ≅
      (pushforward (toInverseImageBase f)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f (m : ℤ))) :=
  targetFormsMixedTensorIso f g k _

/-! ### The two orientations of the tensor product

`Tensor.sheafTensor`'s flip tensors on the right and `Tensor.sheafTensor` on the left. The
generic identity above is stated with the former, while both the graded piece and the
comparison's source are written with the latter. -/

/-- **Tensoring on the left by `A` is tensoring on the right by `B`**, on a ringed space: both
are the sheafification of the objectwise tensor product of `A` with `B`. -/
theorem tensorFunctor_obj_obj_eq_sheafTensorRight (Z : RingedSpace.{u, u}) (A B : Modules Z) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj A).obj B =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).flip.obj B).obj A :=
  rfl

/-- **The tensor bifunctor at a pair is tensoring on the right by the second entry**, on a
ringed space. -/
theorem tensorSheafBifunctor_obj_eq_sheafTensorRight (Z : RingedSpace.{u, u}) (A B : Modules Z) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (A, B) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).flip.obj B).obj A :=
  rfl

/-- **The symmetry `A ⊗_{𝒪_Z} B ≅ B ⊗_{𝒪_Z} A` on a ringed space**, with the left-hand side read
through `Tensor.sheafTensor` and the right-hand side through
`Tensor.sheafTensor`'s flip. It is `Stacks.FlatChangeOfRings.sheafTensorSymmIso`. -/
def tensorFunctorSymmIso (Z : RingedSpace.{u, u}) (A B : Modules Z) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj A).obj B ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).flip.obj A).obj B :=
  Stacks.FlatChangeOfRings.sheafTensorSymmIso.{u} Z.sheaf B A

/-- **The symmetry of the tensor product on a ringed space is natural in the factor it moves out
of the functor position.** It is
`Stacks.FlatChangeOfRings.sheafTensorMapRight_comp_sheafTensorSymmIso_hom` at `Z.sheaf`. -/
theorem tensorFunctorSymmIso_naturality (Z : RingedSpace.{u, u}) (A : Modules Z)
    {B B' : Modules Z} (β : B ⟶ B') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj A).map β ≫
        (tensorFunctorSymmIso Z A B').hom =
      (tensorFunctorSymmIso Z A B).hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
          Z.sheaf).flip.obj A).map β :=
  Stacks.FlatChangeOfRings.sheafTensorMapRight_comp_sheafTensorSymmIso_hom Z.sheaf A β

/-- **The symmetry `B ⊗_{𝒪_Z} A ≅ A ⊗_{𝒪_Z} B` on a ringed space, in the other direction**:
from the spelling through `Tensor.sheafTensor`'s flip to the uncurried `Tensor.sheafTensor`
spelling that `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` is
written with. It is `Stacks.FlatChangeOfRings.sheafTensorSymmIso`. -/
def tensorFunctorSymmIso' (Z : RingedSpace.{u, u}) (A B : Modules Z) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).flip.obj A).obj B ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)).obj (A, B) :=
  Stacks.FlatChangeOfRings.sheafTensorSymmIso.{u} Z.sheaf A B

/-- **Naturality of `Stacks.DeRhamSmooth.tensorFunctorSymmIso'`**, the other orientation of
`Stacks.DeRhamSmooth.tensorFunctorSymmIso_naturality`. It is
`Stacks.FlatChangeOfRings.sheafTensorRight_map_comp_sheafTensorSymmIso_hom` at `Z.sheaf`. -/
theorem tensorFunctorSymmIso'_naturality (Z : RingedSpace.{u, u}) (A : Modules Z)
    {B B' : Modules Z} (β : B ⟶ B') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        Z.sheaf).flip.obj A).map β ≫ (tensorFunctorSymmIso' Z A B').hom =
      (tensorFunctorSymmIso' Z A B).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj A).map β :=
  Stacks.FlatChangeOfRings.sheafTensorRight_map_comp_sheafTensorSymmIso_hom Z.sheaf A β

/-- **The graded piece's tensor product, read as a tensor product on the right**:
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} N ≅ N ⊗_{f^{-1}𝒪_Y} f^{-1}Ω^k_{Y/S}`. The left-hand side is
`Stacks.DeRhamSmooth.pulledBackTargetFormsTensor`, the endofunctor
`Stacks.DeRhamSmooth.gradedTargetTensor` applies degreewise. -/
def pulledBackTargetFormsTensorSymmIso (k : ℕ) (N : Modules (inverseImageBase f)) :
    (pulledBackTargetFormsTensor f g k).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k)).obj N :=
  tensorFunctorSymmIso _ _ _

/-- **`Stacks.DeRhamSmooth.pulledBackTargetFormsTensorSymmIso` is natural in `N`.** This is
`Stacks.DeRhamSmooth.tensorFunctorSymmIso_naturality` at the ringed space
`Stacks.DeRhamDirectImage.inverseImageBase f`. -/
theorem pulledBackTargetFormsTensorSymmIso_naturality (k : ℕ)
    {N N' : Modules (inverseImageBase f)} (ν : N ⟶ N') :
    (pulledBackTargetFormsTensor f g k).map ν ≫
        (pulledBackTargetFormsTensorSymmIso f g k N').hom =
      (pulledBackTargetFormsTensorSymmIso f g k N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k)).map ν :=
  tensorFunctorSymmIso_naturality (inverseImageBase f) (pulledBackTargetForms f g k) ν

/-- **The comparison's source, read as a tensor product on the right**:
`F ⊗_{𝒪_X} f^*Ω^k_{Y/S} ≅ f^*Ω^k_{Y/S} ⊗_{𝒪_X} F`. The right-hand side is the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`, spelled with
the uncurried `Tensor.sheafTensor` as that comparison spells it. -/
def pullbackFormsTensorSymmIso (k : ℕ) (F : Modules X.toRingedSpace) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).obj F ≅
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)), F) :=
  tensorFunctorSymmIso' _ _ _

/-- **`Stacks.DeRhamSmooth.pullbackFormsTensorSymmIso` is natural in `F`.** This is
`Stacks.DeRhamSmooth.tensorFunctorSymmIso'_naturality` at the ringed space underlying `X`, with
`A` the pullback `f^*Ω^k_{Y/S}`; the morphism on the right is the one the second variable of
the uncurried `Tensor.sheafTensor` contributes, which is how the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` varies with `F`. -/
theorem pullbackFormsTensorSymmIso_naturality (k : ℕ)
    {F F' : Modules X.toRingedSpace} (φ : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ ≫
        (pullbackFormsTensorSymmIso f g k F').hom =
      (pullbackFormsTensorSymmIso f g k F).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
            X.toRingedSpace.sheaf).obj
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ :=
  tensorFunctorSymmIso'_naturality X.toRingedSpace _ φ

/-- **[Stacks, Tag 08DE] at the binders of Section 0FMK, in the spelling each side uses**: for a
sheaf `F` of `𝒪_X`-modules,

`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|_{f^{-1}𝒪_Y} ≅ (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|_{f^{-1}𝒪_Y}`.

The left-hand side is `Stacks.DeRhamSmooth.pulledBackTargetFormsTensor`, the endofunctor
`Stacks.DeRhamSmooth.gradedTargetComplex` is built from; the object inside the restriction of
scalars on the right is the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`, the comparison onto
the graded piece read at the pullback of the forms of the target. So this is the identification
of the two readings of that source, with nothing assumed of `f`.

It is `Stacks.DeRhamSmooth.targetFormsMixedTensorIso` with the orientation of the tensor product
crossed on each side. -/
def gradedSourceMixedTensorIso (k : ℕ) (F : Modules X.toRingedSpace) :
    (pulledBackTargetFormsTensor f g k).obj ((pushforward (toInverseImageBase f)).obj F) ≅
      (pushforward (toInverseImageBase f)).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)), F)) :=
  pulledBackTargetFormsTensorSymmIso f g k _ ≪≫ targetFormsMixedTensorIso f g k F ≪≫
    (pushforward (toInverseImageBase f)).mapIso (pullbackFormsTensorSymmIso f g k F)

/-- **`Stacks.DeRhamSmooth.targetFormsMixedTensorIso` is natural in `F`**: it is a component of
`Stacks.DeRhamSmooth.targetFormsMixedTensorNatIso`. -/
theorem targetFormsMixedTensorIso_naturality (k : ℕ) {F F' : Modules X.toRingedSpace}
    (φ : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((inverseImageBase f).sheaf)).flip.obj (pulledBackTargetForms f g k)).map
          ((pushforward (toInverseImageBase f)).map φ) ≫
        (targetFormsMixedTensorIso f g k F').hom =
      (targetFormsMixedTensorIso f g k F).hom ≫
        (pushforward (toInverseImageBase f)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              X.toRingedSpace.sheaf).flip.obj ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ) :=
  (targetFormsMixedTensorNatIso f g k).hom.naturality φ

/-- **[Stacks, Tag 08DE] at the binders of Section 0FMK is natural in `F`**: the identity

`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|_{f^{-1}𝒪_Y} ≅ (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|_{f^{-1}𝒪_Y}`

of `Stacks.DeRhamSmooth.gradedSourceMixedTensorIso` commutes with the morphism any `φ : F ⟶ F'`
induces on the two sides. Nothing is assumed of `f`. -/
theorem gradedSourceMixedTensorIso_naturality (k : ℕ) {F F' : Modules X.toRingedSpace}
    (φ : F ⟶ F') :
    (pulledBackTargetFormsTensor f g k).map ((pushforward (toInverseImageBase f)).map φ) ≫
        (gradedSourceMixedTensorIso f g k F').hom =
      (gradedSourceMixedTensorIso f g k F).hom ≫
        (pushforward (toInverseImageBase f)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              X.toRingedSpace.sheaf).obj
            ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ) :=
  Stacks.MixedBaseChange.paste_squares
    (pulledBackTargetFormsTensorSymmIso_naturality f g k
      ((pushforward (toInverseImageBase f)).map φ))
    (Stacks.MixedBaseChange.paste_squares (targetFormsMixedTensorIso_naturality f g k φ)
      (Stacks.map_comp_eq_map_comp (pushforward (toInverseImageBase f))
        (pullbackFormsTensorSymmIso_naturality f g k φ)))

/-- **[Stacks, Tag 08DE] at the binders of Section 0FMK, read over `(f ∘ g)^{-1}𝒪_S`**: for a
sheaf `F` of `𝒪_X`-modules,

`(f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|_{f^{-1}𝒪_Y})|_{(f∘g)^{-1}𝒪_S} ≅
  (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|_{(f∘g)^{-1}𝒪_S}`.

`Stacks.DeRhamSmooth.gradedSourceMixedTensorIso` identifies the two readings of the source over
`f^{-1}𝒪_Y`; this reads both sides one restriction of scalars further out, over
`(f ∘ g)^{-1}𝒪_S`. The left side is the shape of a term of
`Stacks.DeRhamSmooth.gradedTargetComplex` (`Stacks.DeRhamSmooth.gradedTargetComplex_X`), and the
right side reads the source of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` — a sheaf of
`𝒪_X`-modules — over `(f ∘ g)^{-1}𝒪_S` in one step.

The two restrictions of scalars compose to the one along `𝒪_X ⟶ (f ∘ g)^{-1}𝒪_S` by
`Stacks.DeRhamDirectImage.coefficientRestrictionToInverseImageBaseIso`, the triangle on the three
restrictions; nothing is assumed of `f`. -/
def gradedSourceMixedTensorCoefficientIso (k : ℕ) (F : Modules X.toRingedSpace) :
    (coefficientRestriction f g).obj
        ((pulledBackTargetFormsTensor f g k).obj ((pushforward (toInverseImageBase f)).obj F)) ≅
      (pushforward (toInverseImageBase (f ≫ g))).obj
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)), F)) :=
  (coefficientRestriction f g).mapIso (gradedSourceMixedTensorIso f g k F) ≪≫
    (coefficientRestrictionToInverseImageBaseIso f g).app _

/-- **The identity read over `(f ∘ g)^{-1}𝒪_S` is natural in `F`**: the isomorphism
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` commutes with the morphism any
`φ : F ⟶ F'` induces on the two sides. Nothing is assumed of `f`. -/
theorem gradedSourceMixedTensorCoefficientIso_naturality (k : ℕ)
    {F F' : Modules X.toRingedSpace} (φ : F ⟶ F') :
    (coefficientRestriction f g).map
          ((pulledBackTargetFormsTensor f g k).map
            ((pushforward (toInverseImageBase f)).map φ)) ≫
        (gradedSourceMixedTensorCoefficientIso f g k F').hom =
      (gradedSourceMixedTensorCoefficientIso f g k F).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              X.toRingedSpace.sheaf).obj
            ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ) :=
  Stacks.MixedBaseChange.paste_squares
    (Stacks.map_comp_eq_map_comp (coefficientRestriction f g)
      (gradedSourceMixedTensorIso_naturality f g k φ))
    ((coefficientRestrictionToInverseImageBaseIso f g).hom.naturality
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          X.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map φ))

end Stacks.DeRhamSmooth

end
