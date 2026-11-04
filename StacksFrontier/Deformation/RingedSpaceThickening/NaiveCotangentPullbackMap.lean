module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentation
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPushforwardComplexMap

/-!
# The canonical map `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces. The
canonical presentation `f⁻¹𝒪_S[𝒪_X] ⟶ 𝒪_X` maps along `g` to the canonical presentation
`(g ∘ f)⁻¹𝒪_S[𝒪_Y] ⟶ 𝒪_Y`: on coefficients by the canonical `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S`, on
variables by `[s] ↦ [g^♯ s]`. The induced chain map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}` is transposed
along `g^* ⊣ g_*` to the canonical map `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`, the map of Stacks 0GQ1's proof
before the derived pullback is applied.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseRingPushMap`: `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S`.
* `AlgebraicGeometry.RingedSpaceThickening.structureComorphism`: `g^♯ : 𝒪_X ⟶ g_*𝒪_Y`.
* `AlgebraicGeometry.RingedSpaceThickening.naiveCotangentPushMap`: `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}`.
* `AlgebraicGeometry.RingedSpaceThickening.pullbackNaiveCotangentMap`:
  `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- `g^♯ : 𝒪_X ⟶ g_*𝒪_Y`, as a morphism of sheaves of commutative rings. -/
abbrev structureComorphism : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj
    Y.sheaf :=
  ObjectProperty.homMk g.hom.c

/-- The canonical `f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S`: the transpose along `f⁻¹ ⊣ f_*` of the unit
`𝒪_S ⟶ (g ∘ f)_*(g ∘ f)⁻¹𝒪_S`. -/
def baseRingPushMap : inverseImageBaseRing f ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing (g ≫ f)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).unit.app
      S.sheaf)

/-- The transpose of `baseRingPushMap` along `f⁻¹ ⊣ f_*` is the unit
`𝒪_S ⟶ (g ∘ f)_*(g ∘ f)⁻¹𝒪_S`. -/
theorem homEquiv_baseRingPushMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _
        (baseRingPushMap g f) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).unit.app
        S.sheaf :=
  Equiv.apply_symm_apply _ _

/-- The structure maps are compatible with `g`: `f⁻¹𝒪_S ⟶ 𝒪_X ⟶ g_*𝒪_Y` is
`f⁻¹𝒪_S ⟶ g_*(g ∘ f)⁻¹𝒪_S ⟶ g_*𝒪_Y`. -/
theorem structureRingMap_comp_structureComorphism :
    structureRingMap f ≫ structureComorphism g =
      baseRingPushMap g f ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
        (structureRingMap (g ≫ f)) := by
  have h2 : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).unit.app
        S.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (g ≫ f).hom.base).map
          (structureRingMap (g ≫ f)) =
      ObjectProperty.homMk (g ≫ f).hom.c :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).homEquiv_unit
      _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have key : (ObjectProperty.homMk f.hom.c : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map (structureComorphism g) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (g ≫ f).hom.base).unit.app
        S.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          ((TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map (structureRingMap (g ≫ f))) :=
    Eq.trans (by ext U x; rfl) h2.symm
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right_symm _ _).symm.trans ?_
  refine (congrArg (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv _ _).symm) key).trans ?_
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    f.hom.base).homEquiv_naturality_right_symm _ _

/-- The canonical presentation of `𝒪_X` maps along `g` to that of `𝒪_Y`. -/
theorem underlyingPresheafMap_comp :
    Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u}) ≫
        Functor.whiskerLeft (Opens.map g.hom.base).op
          (𝟙 (Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology Y.carrier)
            Y.sheaf)) =
      𝟙 (Stacks.Sites.FreeAlgebra.underlyingPresheaf (Opens.grothendieckTopology X.carrier)
          X.sheaf) ≫ Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u}) :=
  rfl

/-- **The chain map `𝖭𝖫_{X/S} ⟶ g_*𝖭𝖫_{Y/S}`** of the canonical presentations along `g`. -/
def naiveCotangentPushMap :
    PresentedSquareZeroExtension.relativeComplex f ⟶
      ((SheafOfModules.pushforward.{u} (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base
        (structureComorphism g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (PresentedSquareZeroExtension.relativeComplex (g ≫ f)) :=
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing f) X.sheaf (structureRingMap f) (X.sheaf.obj ⋙ forget CommRingCat)
        (𝟙 _)).hom :=
    Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
        (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
        (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)).hom :=
    Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap g.hom.base
    (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g)

/-- **The canonical map `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`**: the transpose of `naiveCotangentPushMap`
along `g^* ⊣ g_*`, applied degreewise. -/
def pullbackNaiveCotangentMap :
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ from
          PresentedSquareZeroExtension.relativeComplex f) ⟶
      (show CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ from
          PresentedSquareZeroExtension.relativeComplex (g ≫ f)) :=
  ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv _ _).symm (naiveCotangentPushMap g f)

end AlgebraicGeometry.RingedSpaceThickening

end
