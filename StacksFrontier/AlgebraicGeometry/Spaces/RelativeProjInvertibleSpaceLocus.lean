module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# The source and the target of `θ` of Stacks 0D2Z on the algebraic space `U(ψ)`

Let `f : X ⟶ Y` be a morphism from an algebraic space `X` towards the algebraic space `Y` of
Situation 0849, with `ℒ` and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` given by their restrictions to the scheme
points of `X` (`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`).
The open subspace `U(ψ) ⊆ X` is an algebraic space, and `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)` and the
inclusion `U(ψ) ⊆ X` are morphisms of algebraic spaces.  This file records them as such, and the
source `r^*𝒪(d)` of the degree-`d` part of `θ` as a quasi-coherent `𝒪_{U(ψ)}`-module
(Stacks 03GA); for a pair `(ℒ, ψ)` on the small étale site of `X`, also the target
`ℒ^{⊗ d}|_{U(ψ)}`.

## Main definitions

* `…InvertibleTwistingRestriction.locusSpace`: `U(ψ)`, as an algebraic space.
* `…InvertibleTwistingRestriction.locusInclusion`: `U(ψ) ⟶ X`.
* `…InvertibleTwistingRestriction.invertibleSpaceMorphism`: `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`.
* `…InvertibleTwistingRestriction.thetaSource`: `r^*𝒪_{Proj_Y(𝒜)}(d)`, quasi-coherent.
* `…InvertibleTwistingRestriction.thetaTarget`: `ℒ^{⊗ d}|_{U(ψ)}`, quasi-coherent, for a pair
  `(ℒ, ψ)` on `X`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f) (hX : IsAlgebraicSpace s.site s.base s.containsBase X)

/-- **`U(ψ)`, as an algebraic space** (an open subspace of the algebraic space `X`). -/
abbrev locusSpace : AlgebraicSpaces s.site s.base s.containsBase :=
  ⟨R.locus.toFunctor, (R.isOpenSubspace_locus hX).1⟩

/-- **The inclusion `U(ψ) ⟶ X`**, as a morphism of algebraic spaces. -/
abbrev locusInclusion : R.locusSpace hX ⟶ ⟨X, hX⟩ :=
  ObjectProperty.homMk R.locus.ι

/-- **`r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`**, as a morphism of algebraic spaces. -/
abbrev invertibleSpaceMorphism :
    R.locusSpace hX ⟶ ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :=
  ObjectProperty.homMk R.invertibleMorphism

/-- `r_{ℒ,ψ}` is a morphism of algebraic spaces over `Y`. -/
theorem invertibleSpaceMorphism_comp_π :
    R.invertibleSpaceMorphism hX ≫ (ObjectProperty.homMk s.relativeProjπ :
        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
          AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space) =
      R.locusInclusion hX ≫ (ObjectProperty.homMk f : (⟨X, hX⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space) :=
  ObjectProperty.hom_ext _ R.invertibleMorphism_comp_π

/-- **The section `W ⟶ W ×_Y Proj_Y(𝒜)` of a scheme point `w : W ⟶ X` of `U(ψ)`**: the section of
the base change attached to the value `R.point w hw` of `r_{ℒ,ψ}` at `w`. -/
def chartSection {W : BigFppfOver s.site s.base s.containsBase} (w : yoneda.obj W ⟶ X)
    (hw : R.locusOpen W w = ⊤) : W ⟶ s.relativeProjPoints.fibre W (w ≫ f) :=
  (s.relativeProjPoints.pointEquivOver W (w ≫ f) (𝟙 W) (R.point w hw)).1

/-- The section lies over the identity of `W`. -/
theorem chartSection_fibreHom {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤) :
    R.chartSection w hw ≫ s.relativeProjPoints.fibreHom W (w ≫ f) = 𝟙 W :=
  (s.relativeProjPoints.pointEquivOver W (w ≫ f) (𝟙 W) (R.point w hw)).2

/-- **The section followed by `W ×_Y Proj_Y(𝒜) ⟶ Proj_Y(𝒜)` is the value of `r_{ℒ,ψ}` at `w`.** -/
theorem map_chartSection_fibreToSpace {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤) :
    yoneda.map (R.chartSection w hw) ≫ s.relativeProjPoints.fibreToSpace W (w ≫ f) =
      (R.point w hw).1 :=
  s.relativeProjPoints.map_pointEquivOver W (w ≫ f) (𝟙 W) (R.point w hw)

/-- **The section, read on schemes, is `r_w : W ⟶ Proj_W((f ∘ w)^*𝒜)`** through the
identification `W ×_Y Proj_Y(𝒜) = Proj_W((f ∘ w)^*𝒜)` of Stacks 084B. -/
theorem toScheme_map_chartSection {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map (R.chartSection w hw) ≫
        (s.relativeProjPoints.fibreIso W (w ≫ f)).hom =
      R.chartMorphism w hw :=
  (s.relativeProjPoints.pointEquivProjOver_apply W (w ≫ f) (𝟙 W) (R.point w hw)).symm.trans
    (R.pointEquivProjOver_point w hw)

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The source `r^*𝒪_{Proj_Y(𝒜)}(d)` of the degree-`d` part of `θ`**, a quasi-coherent
`𝒪_{U(ψ)}`-module (Stacks 03GA), for the twist `𝒪(d)` of Stacks 084D built on the presentation
`Px` of `Y`. -/
def thetaSource (d : ℤ) :
    QuasicoherentSheaves.{u, u} s.site s.base s.containsBase (R.locusSpace hX).obj
      (R.locusSpace hX).property :=
  ⟨(modulePullback s.site s.base s.containsBase (R.invertibleSpaceMorphism hX)).obj
      (s.twistModule Px d).obj,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite _ _ _ _ _
      (s.isQuasicoherentOnSite_twistModule Px d)⟩

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))

/-- `U(ψ)`, as an algebraic space, for a pair `(ℒ, ψ)` on `X`: `locusSpace` of the restriction
datum `ofUnitalHom` of the pair. -/
abbrev locusSpaceOfUnitalHom : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase :=
  (ofUnitalHom s f L ψ).locusSpace X.property

/-- The inclusion `U(ψ) ⟶ X`, for a pair `(ℒ, ψ)` on `X`: `locusInclusion` of the restriction
datum `ofUnitalHom` of the pair. -/
abbrev locusInclusionOfUnitalHom : locusSpaceOfUnitalHom s f L ψ ⟶ X :=
  (ofUnitalHom s f L ψ).locusInclusion X.property

/-- **The target `ℒ^{⊗ d}|_{U(ψ)}` of the degree-`d` part of `θ`**, a quasi-coherent
`𝒪_{U(ψ)}`-module (Stacks 03GA), for a pair `(ℒ, ψ)` on the small étale site of `X`. -/
def thetaTarget (d : ℤ) :
    QuasicoherentSheaves.{u, u} s.shrink.site s.shrink.base s.shrink.containsBase
      (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property :=
  ⟨(modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
      (locusInclusionOfUnitalHom s f L ψ)).obj
      (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.shrink.site s.shrink.base s.shrink.containsBase X)
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property
            L) d),
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite _ _ _ _ _
      (isQuasicoherentOnSite_laurentAlgebra_piece_of_isInvertible L d)⟩


/-- `r^*𝒪_{Proj_Y(𝒜)}(d)`, for a pair `(ℒ, ψ)` on `X`: `thetaSource` of the restriction datum
`ofUnitalHom` of the pair. -/
abbrev thetaSourceOfUnitalHom
    (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property) (d : ℤ) :
    QuasicoherentSheaves.{u, u} s.shrink.site s.shrink.base s.shrink.containsBase
      (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property :=
  (ofUnitalHom s f L ψ).thetaSource X.property Px d

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
