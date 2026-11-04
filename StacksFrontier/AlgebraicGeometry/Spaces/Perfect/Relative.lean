module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Perfect complexes relative to a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally
of finite presentation.  An object `E` of `D(𝒪_X)` is *perfect relative to `Y`* when it is
pseudo-coherent on the small étale ringed site of `X` and, read as an object of `D(f⁻¹𝒪_Y)`
through restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`, locally has finite Tor dimension.

Restriction of scalars does not change the underlying sheaf of abelian groups, so it is exact
and induces a functor of unbounded derived categories.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageRingedSite`: the small étale site of the source,
  endowed with the inverse image `f⁻¹𝒪_Y` of the structure sheaf of the target, as a ringed
  site.
* `AlgebraicGeometry.Space.inverseImageStructureMap`: the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of
  sheaves of rings on the small étale site of `X`.
* `AlgebraicGeometry.Space.scalarRestriction`: restriction of scalars along it,
  `Mod(𝒪_X) ⥤ Mod(f⁻¹𝒪_Y)`.
* `AlgebraicGeometry.Space.derivedScalarRestriction`: the induced functor
  `D(𝒪_X) ⥤ D(f⁻¹𝒪_Y)`.
* `AlgebraicGeometry.Space.derivedScalarRestrictionFactors`: the comparison isomorphism
  saying that it is computed termwise.
* `AlgebraicGeometry.Space.IsPerfectRelativeTo`: relative perfectness.

## Main results

* `AlgebraicGeometry.Space.derivedScalarRestriction_commShift` and
  `AlgebraicGeometry.Space.derivedScalarRestriction_isTriangulated`: derived restriction of
  scalars commutes with the shift and is triangulated.

## References

* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u d e

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The small étale site of the source of `f : X ⟶ Y`, endowed with the inverse image
`f⁻¹𝒪_Y` of the structure sheaf of the target, as a ringed site.

Only the structure sheaf differs from `AlgebraicGeometry.Space.smallEtaleRingedSite`: the
underlying category and topology are its projections. -/
abbrev inverseImageRingedSite (f : X ⟶ Y) : RingedSite.{u + 1, u, u} where
  C := (smallEtaleRingedSite B S hS X.1 X.2).C
  J := (smallEtaleRingedSite B S hS X.1 X.2).J
  O := (inverseImageCommRingFunctor (smallEtaleRingedToposHom B S hS f).toToposHom).obj
    (smallEtaleRingedTopos B S hS Y).O

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings on the small étale site of `X`: the
inverse-image form of the structure map of
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`, from the structure sheaf of
`AlgebraicGeometry.Space.inverseImageRingedSite` to that of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
@[implicit_reducible]
def inverseImageStructureMap (f : X ⟶ Y) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage

/-- **Restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X`**, `Mod(𝒪_X) ⥤ Mod(f⁻¹𝒪_Y)`: an
`𝒪_X`-module read as a module over the inverse image of the structure sheaf of the target. -/
abbrev scalarRestriction (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f) :=
  SheafOfModules.restrictScalars.{u} (inverseImageStructureMap B S hS f)

variable (f : X ⟶ Y)
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

/-- **Restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` on derived categories**,
`D(𝒪_X) ⥤ D(f⁻¹𝒪_Y)`. -/
@[implicit_reducible]
def derivedScalarRestriction :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      RingedSite.DerivedModules.{u + 1, u, u, e} (inverseImageRingedSite B S hS f) :=
  (scalarRestriction B S hS f).mapDerivedCategory

/-- Derived restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` is computed by termwise restriction
of scalars on any complex of `𝒪_X`-modules. -/
@[implicit_reducible]
def derivedScalarRestrictionFactors :
    DerivedCategory.Q ⋙ derivedScalarRestriction B S hS f ≅
      (scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (scalarRestriction B S hS f).mapDerivedCategoryFactors

/-- Derived restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` commutes with the shift. -/
instance derivedScalarRestriction_commShift :
    (derivedScalarRestriction B S hS f).CommShift ℤ := by
  dsimp only [derivedScalarRestriction]
  infer_instance

/-- Derived restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` is triangulated. -/
instance derivedScalarRestriction_isTriangulated :
    (derivedScalarRestriction B S hS f).IsTriangulated := by
  dsimp only [derivedScalarRestriction]
  infer_instance

variable
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).J.over U) AddCommGrpCat.{u}]
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C) M,
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive]
    [∀ (U : (inverseImageRingedSite B S hS f).C)
        (K L : CochainComplex
          (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- For a morphism `f : X ⟶ Y` of algebraic spaces which is flat and locally of finite
presentation, an object `E` of `D(𝒪_X)` is *perfect relative to `Y`* when `E` is
pseudo-coherent and, read as an object of `D(f⁻¹𝒪_Y)` through restriction of scalars along
`f⁻¹𝒪_Y ⟶ 𝒪_X`, locally has finite Tor dimension.

Finite Tor dimension on the slice of the small étale site over `V` is measured against the
derived tensor product `T V` on that slice. The hypotheses `_hflat` and `_hlfp` that `f` is flat
and locally of finite presentation do not enter the condition. -/
@[stacks 0DKN, sga "6 III 4.1" "spaces, flat l.f.p."]
abbrev IsPerfectRelativeTo
    (_hflat : IsFlat B S hS f.hom)
    (_hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E ∧
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension T
      ((derivedScalarRestriction B S hS f).obj E)

end AlgebraicGeometry.Space

end
