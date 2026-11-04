module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.LocalityRingedSpace

/-!
# The projection formula along a finite locally free module, for a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of **ringed spaces**, `ℱ` an `𝒪_X`-module and `ℰ` a **finite locally
free** `𝒪_Y`-module in the sense of [Stacks, Tag 01C6]. This file proves the two clauses of
[Stacks, Tag 01E8]:

* `R^q f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^q f_*ℱ) ⊗_{𝒪_Y} ℰ` for every `q`, naturally in `ℱ`;
* the same in the bounded below derived category, `D(- ⊗ f^*ℰ) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗ ℰ)`.

The rank of `ℰ` is arbitrary, and there is no hypothesis on `f`, on `ℱ` or on the degree.

## Main definitions

* `Stacks.ProjectionFormula.tensorRightSheaf`: tensoring on the right by a module on a ringed
  space, as an endofunctor of its category of modules.
* `Stacks.ProjectionFormula.pushforwardTensorRightRingedSpaceNatIso`: the degree-zero formula as a
  natural isomorphism of functors.

## Main results

* `Stacks.ProjectionFormula.derivedPushforwardTensorRightRingedSpacePlusIso`: the `D⁺` clause of
  [Stacks, Tag 01E8], for an arbitrary morphism of ringed spaces.
* `Stacks.ProjectionFormula.higherDirectImageProjectionFormulaRingedSpaceIso`: the higher direct
  image clause of [Stacks, Tag 01E8], for an arbitrary morphism of ringed spaces.

## Implementation notes

`Stacks.RingedSpace.structureRingSheaf` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` are the same sheaf of rings by
`rfl`, but instance synthesis does not cross between them: the dual and its adjunctions live at
the second, the projection-formula map and the direct image at the first. Instance arguments are
therefore supplied positionally, and `isFiniteLocallyFree_structureSheafRing` re-spells the
hypothesis on `ℰ` at the second spelling.

[Stacks, Tag 01E8] asserts `ℰ ⊗_{𝒪_Y} R^q f_*ℱ ≅ R^q f_*(f^*ℰ ⊗_{𝒪_X} ℱ)`, while the isomorphisms
here go `R^q f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^q f_*ℱ) ⊗_{𝒪_Y} ℰ`; the two differ by the symmetry of the
tensor product on each side and by the direction of an isomorphism. In positive degree the
isomorphism is not identified with a canonical map; in degree zero it is the canonical map.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01E7](https://stacks.math.columbia.edu/tag/01E7)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.RingedSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard

-- Instance search otherwise reaches for
-- `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective`, which applies at an
-- arbitrary object, before the instance deducing the same conclusion from `EnoughInjectives`.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **`Rf_*` exists on `D⁺` for a morphism of ringed spaces**, stated at the
`Stacks.RingedSpace.structureRingSheaf` spelling of the structure sheaf of rings. The instance at
the `structureSheafRing` spelling is the same up to `rfl`, but instance search does not cross
between the two spellings. -/
instance hasRightDerivedFunctorPlus_pushforwardFunctor
    {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) :
    ((pushforwardFunctor f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureRingSheaf X))) :=
  inferInstanceAs (((modulePushforward f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (SheafOfModules.{u} (structureSheafRing X))))

/-- **Tensoring an `𝒪_W`-module on the right by `H`**, as an endofunctor of the category of
`𝒪_W`-modules on a ringed space `W`: `Stacks.ProjectionFormula.tensorRightOf` for the
tensor-product bifunctor of `W`, at the `Stacks.RingedSpace.structureRingSheaf` spelling of the
structure sheaf of rings. -/
@[sga "4 IV 12.12" "special case"]
def tensorRightSheaf (W : AlgebraicGeometry.RingedSpace.{u, u})
    (H : SheafOfModules.{u} (structureRingSheaf W)) :
    SheafOfModules.{u} (structureRingSheaf W) ⥤ SheafOfModules.{u} (structureRingSheaf W) :=
  tensorRightOf
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.presheaf, W.IsSheaf⟩)) H

/-- Tensoring on the right by `H` sends `A` to the tensor product `A ⊗_{𝒪_W} H`. -/
theorem tensorRightSheaf_obj (W : AlgebraicGeometry.RingedSpace.{u, u})
    (H A : SheafOfModules.{u} (structureRingSheaf W)) :
    (tensorRightSheaf W H).obj A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj A).obj H := rfl

/-! ### Tensoring on the right by a finite locally free module is additive and exact -/

section Exact

variable (W : AlgebraicGeometry.RingedSpace.{u, u})
  (E : SheafOfModules.{u} (structureRingSheaf W))
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The finite local freeness of `ℰ`, re-spelled at the
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` spelling of the structure sheaf
of rings, which is where the monoidal structure and the dual live. -/
theorem isFiniteLocallyFree_structureSheafRing :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (E : SheafOfModules.{u} (structureSheafRing W)) := hE

/-- **Tensoring on the right by a finite locally free module preserves finite limits**, by the
left dual of [Stacks, Tag 0FNV]. -/
instance preservesFiniteLimits_tensorRightSheaf :
    PreservesFiniteLimits (tensorRightSheaf W E) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (tensorRightOfIsoTensorRight W E).symm
    (@preservesFiniteLimits_tensorRight W E (isFiniteLocallyFree_structureSheafRing W E))

/-- **Tensoring on the right by a finite locally free module preserves finite colimits**, by the
same left dual. -/
instance preservesFiniteColimits_tensorRightSheaf :
    PreservesFiniteColimits (tensorRightSheaf W E) :=
  @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (tensorRightOfIsoTensorRight W E).symm
    (@preservesFiniteColimits_tensorRight W E (isFiniteLocallyFree_structureSheafRing W E))

/-- **Tensoring on the right by a finite locally free module preserves zero morphisms**: it
preserves finite colimits, hence the initial object, which in an abelian category is the zero
object. -/
instance preservesZeroMorphisms_tensorRightSheaf :
    (tensorRightSheaf W E).PreservesZeroMorphisms :=
  have := preservesFiniteColimits_tensorRightSheaf W E
  Functor.preservesZeroMorphisms_of_map_zero_object <|
    (tensorRightSheaf W E).mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso (tensorRightSheaf W E) ≪≫ HasZeroObject.zeroIsoInitial.symm

/-- **Tensoring on the right by a finite locally free module is additive**, preserving binary
products and the zero object. -/
instance additive_tensorRightSheaf : (tensorRightSheaf W E).Additive :=
  have := preservesFiniteLimits_tensorRightSheaf W E
  Functor.additive_of_preserves_binary_products _

/-- **[Stacks, Tag 01E7]**: an injective module tensored on the right by a finite locally free
module is injective.  This is
`Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree` with the two tensor
factors exchanged along the braiding of the tensor product. -/
theorem injective_tensorRightSheaf_obj
    (I : SheafOfModules.{u} (structureRingSheaf W)) (hI : Injective I) :
    Injective ((tensorRightSheaf W E).obj I) := by
  have hI' : Injective (I : SheafOfModules.{u} (structureSheafRing W)) := hI
  have h : Injective
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf).obj E).obj I) :=
    @Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree
      W I E hI' (isFiniteLocallyFree_structureSheafRing W E)
  exact Injective.of_iso (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap W E I) h

end Exact

/-! ### The degree-zero formula, as a natural isomorphism -/

section Zero

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  (E : SheafOfModules.{u} (structureRingSheaf Y))
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **[Stacks, Tag 01C6] is stable under inverse image**: for an arbitrary morphism of ringed
spaces `f`, the inverse image `f^*ℰ` of a finite locally free module `ℰ` is finite locally
free. -/
instance isFiniteLocallyFree_modulePullback :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((pullbackFunctor f).obj E) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback f.hom.base
    (structureSheafHom f) E hE

/-- **The projection formula morphism as a natural transformation in the module upstairs**,
`f_*(-) ⊗_{𝒪_Y} ℰ ⟶ f_*((-) ⊗_{𝒪_X} f^*ℰ)`, for an arbitrary morphism of ringed spaces and with
no hypothesis on `ℰ`. -/
def pushforwardTensorRightRingedSpaceNatTrans
    (E : SheafOfModules.{u} (structureRingSheaf Y)) :
    pushforwardFunctor f ⋙ tensorRightSheaf Y E ⟶
      tensorRightSheaf X ((pullbackFunctor f).obj E) ⋙ pushforwardFunctor f where
  app A := projectionFormulaMap' f A E
  naturality A B g := by
    have h := projectionFormulaMap'_natural f g (𝟙 E)
    rw [(pullbackFunctor f).map_id E] at h
    exact h

/-- **The projection formula for a finite locally free module, in degree zero and naturally in
the module on the source**, for an arbitrary morphism of ringed spaces:
`(- ⊗_{𝒪_X} f^*ℰ) ⋙ f_* ≅ f_* ⋙ (- ⊗_{𝒪_Y} ℰ)`. -/
@[ega "0 12.2.3" "p = 0"]
def pushforwardTensorRightRingedSpaceNatIso :
    tensorRightSheaf X ((pullbackFunctor f).obj E) ⋙ pushforwardFunctor f ≅
      pushforwardFunctor f ⋙ tensorRightSheaf Y E :=
  haveI : ∀ A, IsIso ((pushforwardTensorRightRingedSpaceNatTrans f E).app A) := fun A =>
    AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree_class_ringedSpace
      f A E
  haveI := NatIso.isIso_of_isIso_app (pushforwardTensorRightRingedSpaceNatTrans f E)
  (asIso (pushforwardTensorRightRingedSpaceNatTrans f E)).symm

/-- **An injective module tensored by `f^*ℰ` is right acyclic for `f_*`.** -/
theorem rightAcyclic_pushforward_tensorRightSheaf
    (I : SheafOfModules.{u} (structureRingSheaf X)) (hI : Injective I) :
    (pushforwardFunctor f).rightAcyclic
      ((tensorRightSheaf X ((pullbackFunctor f).obj E)).obj I) :=
  have := injective_tensorRightSheaf_obj X ((pullbackFunctor f).obj E) I hI
  Functor.rightAcyclic_of_injective (pushforwardFunctor f) _

end Zero

/-! ### The projection formula in every degree, and in `D⁺` -/

section Higher

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  (E : SheafOfModules.{u} (structureRingSheaf Y))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The `D⁺` clause of [Stacks, Tag 01E8]**: for a morphism of **ringed spaces** `f : X ⟶ Y` and
a **finite locally free** `𝒪_Y`-module `ℰ`,

`D(- ⊗_{𝒪_X} f^*ℰ) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗_{𝒪_Y} ℰ)`

as functors `D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`: the projection formula in the bounded below derived category,
for an arbitrary morphism of ringed spaces, every object of `D⁺(𝒪_X)` and `ℰ` of arbitrary
rank. -/
@[stacks 01E8 "the D⁺ clause: for a morphism of ringed spaces f : X ⟶ Y and a finite locally \
free 𝒪_Y-module ℰ, the isomorphism ℰ ⊗_{𝒪_Y} Rf_*ℱ ≅ Rf_*(f^*ℰ ⊗_{𝒪_X} ℱ) in D^+(Y), \
functorial in ℱ", ega "0 12.2.3" "more general", sga "6 III 5.8" "special case"]
def derivedPushforwardTensorRightRingedSpacePlusIso :
    (tensorRightSheaf X ((pullbackFunctor f).obj E)).mapDerivedCategoryPlus ⋙
        (pushforwardFunctor f).rightDerivedFunctorPlus ≅
      (pushforwardFunctor f).rightDerivedFunctorPlus ⋙
        (tensorRightSheaf Y E).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (tensorRightSheaf X ((pullbackFunctor f).obj E))
    (tensorRightSheaf Y E)
    (pushforwardFunctor f) (pushforwardFunctor f)
    (pushforwardTensorRightRingedSpaceNatIso f E)
    (rightAcyclic_pushforward_tensorRightSheaf f E)

/-- **The projection formula for the higher direct images along a finite locally free module, as a
natural isomorphism of functors**, for an arbitrary morphism of ringed spaces:
`(- ⊗_{𝒪_X} f^*ℰ) ⋙ R^n f_* ≅ R^n f_* ⋙ (- ⊗_{𝒪_Y} ℰ)`, for every integer `n`. -/
@[ega "0 12.2.3" "partial", sga "6 III 5.8" "special case"]
def higherDirectImageTensorRightRingedSpaceIso
    (n : ℤ) :
    tensorRightSheaf X ((pullbackFunctor f).obj E) ⋙
        (pushforwardFunctor f).rightDerivedPlus n ≅
      (pushforwardFunctor f).rightDerivedPlus n ⋙ tensorRightSheaf Y E :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (tensorRightSheaf X ((pullbackFunctor f).obj E)) 0).symm
      ((pushforwardFunctor f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureRingSheaf Y)) n) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureRingSheaf X)) 0)
      (Functor.isoWhiskerRight
        (derivedPushforwardTensorRightRingedSpacePlusIso f E)
        (DerivedCategory.Plus.homologyFunctor
          (SheafOfModules.{u} (structureRingSheaf Y)) n)) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} (structureRingSheaf X)) 0 ⋙
        (pushforwardFunctor f).rightDerivedFunctorPlus)
      (Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (tensorRightSheaf Y E))
          (DerivedCategory.Plus.homologyFunctor
            (SheafOfModules.{u} (structureRingSheaf Y)) n) ≪≫
        Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (tensorRightSheaf Y E) n)

/-- **The higher direct image clause of [Stacks, Tag 01E8]**: for a morphism of **ringed spaces**
`f : X ⟶ Y`, an arbitrary `𝒪_X`-module `ℱ` and a **finite locally free** `𝒪_Y`-module `ℰ`,

`R^n f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^n f_*ℱ) ⊗_{𝒪_Y} ℰ`

for every integer `n`; the tag's `q ≥ 0` is the case `n = (q : ℤ)`. -/
@[stacks 01E8 "the higher direct image clause: for a morphism of ringed spaces f : X ⟶ Y, an \
𝒪_X-module ℱ and a finite locally free 𝒪_Y-module ℰ, the isomorphisms \
R^n f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ R^n f_*ℱ ⊗_{𝒪_Y} ℰ for every integer n; the tag's q ≥ 0 is the case \
n = (q : ℤ)", ega "0 12.2.3" "partial"]
def higherDirectImageProjectionFormulaRingedSpaceIso
    (F : SheafOfModules.{u} (structureRingSheaf X)) (n : ℤ) :
    ((pushforwardFunctor f).rightDerivedPlus n).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj
          ((pullbackFunctor f).obj E)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
        (((pushforwardFunctor f).rightDerivedPlus n).obj F)).obj E :=
  (higherDirectImageTensorRightRingedSpaceIso f E n).app F

end Higher

end Stacks.ProjectionFormula

end
