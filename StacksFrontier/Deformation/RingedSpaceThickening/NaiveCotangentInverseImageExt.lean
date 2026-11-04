module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsKInjective
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.RingedSpace.FlatOfIsoStalkMap
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentActingGroup
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedPullbackAdditive
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback
public import StacksFrontier.Topology.Sheaves.Modules.DifferentialsOfSiteBridge

/-!
# The groups of Stacks 08U8 computed over `g⁻¹𝒪_{X₁}`

Let `g : (X₂, 𝒪_{X₂}) ⟶ (X₁, 𝒪_{X₁})` and `f₁ : (X₁, 𝒪_{X₁}) ⟶ (S₁, 𝒪_{S₁})` be morphisms of
ringed spaces and let `𝒢₂` be an `𝒪_{X₂}`-module.  The proof of **Stacks 08U8** replaces the
groups `Ext^k_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)` of the statement by
`Ext^k_{g⁻¹𝒪_{X₁}}(𝖭𝖫_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂)`, computed on the single space `X₂`, using
that `g⁻¹𝖭𝖫_{X₁/S₁}` is the naive cotangent complex of `g⁻¹f₁⁻¹𝒪_{S₁} ⟶ g⁻¹𝒪_{X₁}`
(**Stacks 08TM**).  This file constructs both identifications, with nothing assumed beyond
`g`, `f₁` and `𝒢₂`:

* in degree `1` (clause (1)),
  `Hom_{D(g⁻¹𝒪_{X₁})}(𝖭𝖫_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂[1]) = Ext¹_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`;
* the acting group of clause (2),
  `Hom_{g⁻¹𝒪_{X₁}}(Ω_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.restrictToInverseImageRing`: `𝒢₂` viewed as a
  `g⁻¹𝒪_{X₁}`-module, by restriction of scalars along `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`.
* `AlgebraicGeometry.RingedSpaceThickening.inverseImageSpaceLift`: the morphism of ringed spaces
  `ψ : (X₂, 𝒪_{X₂}) ⟶ (X₂, g⁻¹𝒪_{X₁})` with identity underlying map, through which `g` factors
  as `ψ ≫ π` (`inverseImageSpaceLift_comp_projection`), `π` the inverse-image projection.
* `AlgebraicGeometry.RingedSpaceThickening.inverseImageNaiveCotangentExtOneAddEquiv`: the
  identification of clause (1).
* `AlgebraicGeometry.RingedSpaceThickening.inverseImageDifferentialsHomAddEquiv`: the
  identification of clause (2).

## Implementation notes

The degree `1` identification is a composite of canonical isomorphisms:

`Lg^*𝖭𝖫_{X₁/S₁} ≅ Lψ^*Lπ^*𝖭𝖫_{X₁/S₁}` (**Stacks 0D5S**, with `g = ψ ≫ π`),
`Lπ^*𝖭𝖫_{X₁/S₁} ≅ π^*𝖭𝖫_{X₁/S₁}` (`π` is flat: its stalk maps are isomorphisms),
`Hom(Lψ^*K, 𝒢₂[1]) = Hom(K, Rψ_*(𝒢₂[1]))` (the derived adjunction of **Stacks 079W**),
`Rψ_* ≅ D(ψ_*)` (`ψ_*` is restriction of scalars along `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`, hence exact),
so that `Rψ_*(𝒢₂[1]) ≅ (ψ_*𝒢₂)[0][1]`, and finally
`π^*𝖭𝖫_{X₁/S₁} ≅ 𝖭𝖫_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}` (**Stacks 08TM**).
Here `π^*` is the inverse image of modules, since the structure sheaf of `(X₂, g⁻¹𝒪_{X₁})` is
`g⁻¹𝒪_{X₁}`; both this and `ψ_* = ` restriction of scalars hold by `rfl`
(`modulePushforward_inverseImageSpaceLift`), as do the identifications of the category of
modules over `(X₂, g⁻¹𝒪_{X₁})` with the category of `g⁻¹𝒪_{X₁}`-modules in the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf` in which the naive cotangent complex is stated.

The degree `0` identification of clause (2) is the canonical identification
`g⁻¹Ω_{X₁/S₁} = Ω_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}` of **Stacks 08RR**, followed by the adjunction between
the inverse image of modules and the pushforward of modules along `g⁻¹`, and the description of
`g_*` as restriction of scalars followed by that pushforward
(`RingedSpaceModuleAdjunction.modulePushforward_eq`).

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR), the inverse image of
  the module of differentials
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S), composition of derived
  pullbacks
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W), the derived adjunction
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules (inverseImageMiddleRing inverseImageBaseRing inverseImageFirstRingMap
  ringedSpaceStructureMap inverseImageBaseRingOnMiddle naiveCotangentComplex)
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom moduleOfDifferentialsOfSite
  pullbackDifferentialsIso inverseImageAdjunction)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X₁ X₂ S₁ : RingedSpace.{u, u}} (g : X₂ ⟶ X₁) (f₁ : X₁ ⟶ S₁)
  (G : SheafOfModules.{u} (structureSheafRing X₂))

/-- `𝒢₂` viewed as a `g⁻¹𝒪_{X₁}`-module: restriction of scalars along the structure map
`g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}` (the adjoint transpose of `g^♯`). -/
abbrev restrictToInverseImageRing :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageMiddleRing g)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X₂.carrier) (forget₂ CommRingCat RingCat)).map
      (ringedSpaceStructureMap g))).obj G

/-- **The acting group of clause (2) of Stacks 08U8, computed over `g⁻¹𝒪_{X₁}`.**

`Hom_{g⁻¹𝒪_{X₁}}(Ω_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂) = Hom_{𝒪_{X₁}}(Ω_{X₁/S₁}, g_*𝒢₂)`.

The module of differentials commutes with inverse image (**Stacks 08RR**,
`AlgebraicGeometry.SheafOfModules.pullbackDifferentialsIso`), the inverse image of modules along
`g` is left adjoint to the pushforward of modules along the unit `𝒪_{X₁} ⟶ g_*g⁻¹𝒪_{X₁}`, and
`g_*` is restriction of scalars to `g⁻¹𝒪_{X₁}` followed by that pushforward
(`RingedSpaceModuleAdjunction.modulePushforward_eq`). -/
def inverseImageDifferentialsHomAddEquiv :
    (moduleOfDifferentialsOfSite.{u, u, u, u} (inverseImageBaseRing g f₁)
        (inverseImageMiddleRing g) (inverseImageFirstRingMap g f₁) ⟶
        restrictToInverseImageRing g G) ≃+
      ((show SheafOfModules.{u} (structureSheafRing X₁) from relativeDifferentials f₁) ⟶
        (modulePushforward g).obj G) :=
  ((pullbackDifferentialsIso g.hom.base (ringedSpaceStructureMap f₁)).precompHomAddEquiv
      (restrictToInverseImageRing g G)).trans
    (((inverseImageAdjunction g.hom.base X₁.sheaf).homAddEquiv _ _).trans
      (Linear.homCongr ℤ (Iso.refl _)
        (eqToIso (Functor.congr_obj (modulePushforward_eq g) G).symm)).toAddEquiv)

/-! ### Factoring `g` through `(X₂, g⁻¹𝒪_{X₁})` -/

/-- The ringed space `(X₂, g⁻¹𝒪_{X₁})`: the space of `X₂` with the inverse image of the
structure sheaf of `X₁`. -/
abbrev inverseImageSpace : RingedSpace.{u, u} :=
  AlgebraicGeometry.RingedSpace.inverseImage X₁ g.hom.base

/-- The inverse-image projection `π : (X₂, g⁻¹𝒪_{X₁}) ⟶ (X₁, 𝒪_{X₁})`, lying over `g`. -/
abbrev inverseImageSpaceProjection : inverseImageSpace g ⟶ X₁ :=
  AlgebraicGeometry.RingedSpace.inverseImageProjection X₁ g.hom.base

/-- The morphism of ringed spaces `ψ : (X₂, 𝒪_{X₂}) ⟶ (X₂, g⁻¹𝒪_{X₁})` with identity
underlying map, whose structure map `g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}` is the adjoint transpose of `g^♯`. -/
def inverseImageSpaceLift : X₂ ⟶ inverseImageSpace g :=
  Stacks.Cohomology.SupportedComplexes.inverseImageRingedSpaceLift X₁ g.hom.base
    (𝟙 X₂.carrier) ⟨g.hom.c⟩

/-- **`g` factors as `ψ ≫ π`** through `(X₂, g⁻¹𝒪_{X₁})`. -/
theorem inverseImageSpaceLift_comp_projection :
    inverseImageSpaceLift g ≫ inverseImageSpaceProjection g = g := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.hext _ _ rfl ?_
  exact heq_of_eq (Stacks.Cohomology.SupportedComplexes.inverseImageRingedSpaceLift_comp_c X₁
    g.hom.base (Y := X₂) (𝟙 X₂.carrier) ⟨g.hom.c⟩)

/-- The pushforward of modules along `ψ` is restriction of scalars along the structure map
`g⁻¹𝒪_{X₁} ⟶ 𝒪_{X₂}`; this holds by `rfl`. -/
theorem modulePushforward_inverseImageSpaceLift : modulePushforward (inverseImageSpaceLift g) =
    SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X₂.carrier) (forget₂ CommRingCat RingCat)).map
        (ringedSpaceStructureMap g)) := rfl

/-- The pushforward of modules along `ψ` is left exact: it is restriction of scalars. -/
instance preservesFiniteLimits_modulePushforward_inverseImageSpaceLift :
    PreservesFiniteLimits (modulePushforward (inverseImageSpaceLift g)) :=
  Stacks.SheafOfModules.CoextendScalars.preservesFiniteLimits_restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X₂.carrier) (forget₂ CommRingCat RingCat)).map
      (ringedSpaceStructureMap g))

/-- The pushforward of modules along `ψ` is right exact: it is restriction of scalars. -/
instance preservesFiniteColimits_modulePushforward_inverseImageSpaceLift :
    PreservesFiniteColimits (modulePushforward (inverseImageSpaceLift g)) :=
  Stacks.SheafOfModules.CoextendScalars.preservesFiniteColimits_restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X₂.carrier) (forget₂ CommRingCat RingCat)).map
      (ringedSpaceStructureMap g))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The derived adjunction `Lψ^* ⊣ D(ψ_*)`: the adjunction `Lψ^* ⊣ Rψ_*` of **Stacks 079W**,
with `Rψ_*` replaced by the functor `D(ψ_*)` induced by the exact functor `ψ_*`. -/
def inverseImageSpaceLiftAdjunction :
    derivedPullback (inverseImageSpaceLift g) ⊣
      (modulePushforward (inverseImageSpaceLift g)).mapDerivedCategory :=
  (derivedAdjunction (inverseImageSpaceLift g)).ofNatIsoRight
    (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      (modulePushforward (inverseImageSpaceLift g))).symm

/-- The complex `π^*𝖭𝖫_{X₁/S₁}` of `g⁻¹𝒪_{X₁}`-modules: the degreewise pullback along the
inverse-image projection, that is, the inverse image `g⁻¹𝖭𝖫_{X₁/S₁}`. -/
abbrev projectionPulledNaiveCotangent :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageSpace g))) ℤ :=
  ((modulePullback (inverseImageSpaceProjection g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
      AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁)

/-- **Stacks 08TM along `g`**: `g⁻¹𝖭𝖫_{X₁/S₁} ≅ 𝖭𝖫_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}`, read as an
isomorphism of complexes of modules over `(X₂, g⁻¹𝒪_{X₁})`. -/
def projectionPulledNaiveCotangentIso :
    projectionPulledNaiveCotangent g f₁ ≅
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageSpace g))) ℤ from
        naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X₂.carrier)
          (inverseImageBaseRing g f₁) (inverseImageMiddleRing g) (inverseImageFirstRingMap g f₁)) :=
  Stacks.SheafOfModules.naiveCotangentComplexInverseImageIso g.hom.base
    (inverseImageBaseRingOnMiddle f₁) X₁.sheaf (ringedSpaceStructureMap f₁)

/-- `Lψ^*(π^*𝖭𝖫_{X₁/S₁}) ≅ Lg^*𝖭𝖫_{X₁/S₁}`: `Lπ^*` is computed degreewise since `π` is flat,
and `Lψ^* ⋙ Lπ^*` is `L(ψ ≫ π)^* = Lg^*` (**Stacks 0D5S**). -/
def derivedPullbackNaiveCotangentFactorIso :
    (derivedPullback (inverseImageSpaceLift g)).obj
        (DerivedCategory.Q.obj (projectionPulledNaiveCotangent g f₁)) ≅
      derivedPullbackNaiveCotangent g f₁ :=
  (derivedPullback (inverseImageSpaceLift g)).mapIso
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat
        (inverseImageSpaceProjection g)
        (AlgebraicGeometry.RingedSpace.isFlat_inverseImageProjection X₁ g.hom.base)
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing X₁)) ℤ from
          AlgebraicGeometry.RingedSpace.naiveCotangentComplex f₁)).symm ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (inverseImageSpaceLift g) (inverseImageSpaceProjection g)).app
        (relativeNaiveCotangentObj f₁) ≪≫
    eqToIso (by rw [inverseImageSpaceLift_comp_projection])

/-- `D(ψ_*)(𝒢₂[0][1]) ≅ (ψ_*𝒢₂)[0][1]`: the functor induced by an exact functor commutes
with shifts and with the inclusion of degree `0` objects. -/
def pushforwardShiftedSingleIso :
    (modulePushforward (inverseImageSpaceLift g)).mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X₂)) 0).obj
          G)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (inverseImageSpace g))) 0).obj
        ((modulePushforward (inverseImageSpaceLift g)).obj G))⟦(1 : ℤ)⟧ :=
  ((modulePushforward (inverseImageSpaceLift g)).mapDerivedCategory.commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso
      (((modulePushforward (inverseImageSpaceLift g)).mapDerivedCategorySingleFunctor 0).app G)

/-- **The obstruction group of clause (1) of Stacks 08U8, computed over `g⁻¹𝒪_{X₁}`.**

`Hom_{D(g⁻¹𝒪_{X₁})}(𝖭𝖫_{g⁻¹𝒪_{X₁}/g⁻¹f₁⁻¹𝒪_{S₁}}, 𝒢₂[1]) = Ext¹_{𝒪_{X₂}}(Lg^*𝖭𝖫_{X₁/S₁}, 𝒢₂)`,

the identification the proof of the source makes when it reduces to a single space.  It is the
composite of **Stacks 08TM** along `g` (`projectionPulledNaiveCotangentIso`), the identification
`Rψ_*(𝒢₂[1]) = (ψ_*𝒢₂)[0][1]` (`pushforwardShiftedSingleIso`), the derived adjunction
`Lψ^* ⊣ Rψ_*` (`inverseImageSpaceLiftAdjunction`) and `Lψ^*π^* = Lg^*`
(`derivedPullbackNaiveCotangentFactorIso`).  Nothing is assumed beyond `g`, `f₁` and `𝒢₂`. -/
def inverseImageNaiveCotangentExtOneAddEquiv :
    (DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X₂.carrier)
          (inverseImageBaseRing g f₁) (inverseImageMiddleRing g) (inverseImageFirstRingMap g f₁)) ⟶
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageMiddleRing g))) 0).obj
        (restrictToInverseImageRing g G))⟦(1 : ℤ)⟧) ≃+
      extOnePulledNaiveCotangent g f₁ G :=
  letI := Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackAdditive
    (inverseImageSpaceLift g)
  (Linear.homCongr ℤ (DerivedCategory.Q.mapIso (projectionPulledNaiveCotangentIso g f₁)).symm
      (pushforwardShiftedSingleIso g G).symm).toAddEquiv.trans
    (((inverseImageSpaceLiftAdjunction g).homAddEquiv _ _).symm.trans
      (Linear.homCongr ℤ (derivedPullbackNaiveCotangentFactorIso g f₁) (Iso.refl _)).toAddEquiv)

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
