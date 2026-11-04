module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGraded

/-!
# The chart maps `χ_w` of `θ` of Stacks 0D2Z on the algebraic space `U(ψ)`

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849 and a scheme point `w : W ⟶ X` of `U(ψ)`, the map `θ` of [Stacks, Tag 01O9]
on `W` (`…InvertibleTwistingRestriction.chartTheta`) is read here as a map of quasi-coherent
modules on `W` between the pullback, along the section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of `w`, of the
twist `𝒪(d)` of Stacks 01NR on `W ×_Y Proj_Y(𝒜) = Proj_W((f ∘ w)^*𝒜)`, and `(w^*ℒ)^{⊗ d}`.

On the represented algebraic space of `W`, this gives the chart map
`χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` from which `θ` on `U(ψ)` is descended
(`AlgebraicGeometry.Space.pointFamilyDescendedHom`).

## Main definitions

* `…InvertibleTwistingRestriction.chartSchemeTheta`: `c_w^*𝒪(d) ⟶ (w^*ℒ)^{⊗ d}`.
* `…InvertibleTwistingRestriction.chartSourceIso`: `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a`.
* `…InvertibleTwistingRestriction.chartTargetIso`: `((w^*ℒ)^{⊗ d})^a ≅ w^*(ℒ^{⊗ d}|_{U(ψ)})`.
* `…InvertibleTwistingRestriction.chartMap`: **the chart map `χ_w`**.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

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
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤)

/-- The section `c_w`, read on schemes and followed by the identification of
`W ×_Y Proj_Y(𝒜)` with `Proj_W((f ∘ w)^*𝒜)` used by the twists, is `r_w`. -/
theorem toScheme_map_chartSection_toRelativeProj :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map
        ((ofUnitalHom s f L ψ).chartSection x hx) ≫ s.toRelativeProj W (x ≫ f.hom) =
      (ofUnitalHom s f L ψ).chartMorphism x hx :=
  (ofUnitalHom s f L ψ).toScheme_map_chartSection x hx

/-- **`θ` at a scheme point `w` of `U(ψ)`, as a map of quasi-coherent modules on `W`**: the map
`c_w^*𝒪(d) ≅ r_w^*𝒪(d) ⟶ (w^*ℒ)^{⊗ d}` of `…InvertibleTwistingRestriction.chartTheta`, for the
section `c_w : W ⟶ W ×_Y Proj_Y(𝒜)` of `w` and the twist `𝒪(d)` of Stacks 01NR on
`W ×_Y Proj_Y(𝒜)`. -/
def chartSchemeTheta (d : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase ((ofUnitalHom s f L ψ).chartSection x hx)
        (s.twistPieceQcoh W (x ≫ f.hom) d) ⟶
      pointLaurentPieceQcoh L W x d :=
  ObjectProperty.homMk
    ((Scheme.Modules.pullbackComp _ _).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (toScheme_map_chartSection_toRelativeProj s f L ψ x hx)).hom.app
        _ ≫ (ofUnitalHom s f L ψ).chartTheta x hx d)

section Chart

variable {s f L ψ} {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}

/-- The scheme point of `X` underlying a scheme point `w : W ⟶ U(ψ)`. -/
abbrev locusPoint (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    yoneda.obj W ⟶ X.1 :=
  yonedaEquiv.symm (yonedaEquiv w).1

/-- The inclusion `U(ψ) ⊆ X` at a scheme point `w` of `U(ψ)`, as morphisms of algebraic spaces. -/
theorem pointHom_locusPoint (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    pointHom (X := X) (locusPoint w) =
      pointHom (X := locusSpaceOfUnitalHom s f L ψ) w ≫ locusInclusionOfUnitalHom s f L ψ :=
  ObjectProperty.hom_ext _
    (yonedaEquiv.injective ((Equiv.apply_symm_apply yonedaEquiv _).trans rfl))

/-- **The target of `χ_w`**: `((w^*ℒ)^{⊗ d})^a ≅ w^*(ℒ^{⊗ d}) ≅ w^*(ℒ^{⊗ d}|_{U(ψ)})`, the
inverse of `AlgebraicGeometry.Space.pointTargetIso` followed by the comparison of Stacks 03LU for
`w` and the inclusion `U(ψ) ⊆ X`. -/
def chartTargetIso (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℤ) :
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase W).functor.obj (pointLaurentPieceQcoh L W (locusPoint w) d)).obj ≅
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).obj (thetaTarget s f L ψ d).obj :=
  (pointTargetIso L W (locusPoint w) d).symm ≪≫
    eqToIso (congrArg (fun k => (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
      k).obj (SheafOfModules.GradedAlgebra.piece
        (R := structureRingSheaf s.shrink.site s.shrink.base s.shrink.containsBase X)
        (Stacks.SheafOfModules.TensorPower.laurentAlgebra
          (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property
            L) d)) (pointHom_locusPoint w)) ≪≫
    ((modulePullbackCompIso s.shrink.site s.shrink.base s.shrink.containsBase
      (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w) (locusInclusionOfUnitalHom s f L ψ)).app
        _).symm

/-- The comparisons of Stacks 03LU for two factorisations `a ≫ b = a' ≫ b'` of one morphism:
`a^*(b^*M) ≅ (a ≫ b)^*M = (a' ≫ b')^*M ≅ a'^*(b'^*M)`. -/
def modulePullbackCompTransportIso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {A Y Z P : AlgebraicSpaces B S hS} (a : A ⟶ Y) (b : Y ⟶ P) (a' : A ⟶ Z) (b' : Z ⟶ P)
    (h : a ≫ b = a' ≫ b') (M : Modules.{u, u} B S hS P.1 P.2) :
    (modulePullback B S hS a).obj ((modulePullback B S hS b).obj M) ≅
      (modulePullback B S hS a').obj ((modulePullback B S hS b').obj M) :=
  (modulePullbackCompIso B S hS a b).app M ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) h) ≪≫
    ((modulePullbackCompIso B S hS a' b').app M).symm

/-- `r_{ℒ,ψ}` at a scheme point `w` of `U(ψ)` is its value `point`. -/
theorem comp_invertibleMorphism (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)
    (hw : (ofUnitalHom s f L ψ).locusOpen W (locusPoint w) = ⊤) :
    w ≫ (ofUnitalHom s f L ψ).invertibleMorphism =
      ((ofUnitalHom s f L ψ).point (locusPoint w) hw).1 :=
  yonedaEquiv.injective rfl

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The source of `χ_w`**: `w^*(r^*𝒪(d)) ≅ (r ∘ w)^*𝒪(d) = c_w^*((W ×_Y P ⟶ P)^*𝒪(d)) ≅
(c_w^*𝒪(d))^a`, through the comparisons of Stacks 03LU, the base change identification of
Stacks 084D at `W` (`…RelativeProjSituation.fibreToSpaceTwistModuleIso`) and Stacks 03DX (2). -/
def chartSourceIso (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)
    (hw : (ofUnitalHom s f L ψ).locusOpen W (locusPoint w) = ⊤) (d : ℤ) :
    (modulePullback s.site s.base s.containsBase
        (pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)).obj
        ((ofUnitalHom s f L ψ).thetaSource X.property Px d).obj ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) hw)
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) d))).obj :=
  modulePullbackCompTransportIso
      (pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w)
      ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
      (representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) hw))
      (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
      (ObjectProperty.hom_ext _ ((comp_invertibleMorphism w hw).trans
        ((ofUnitalHom s f L ψ).map_chartSection_fibreToSpace _ _).symm))
      (s.twistModule Px d).obj ≪≫
    (modulePullback s.site s.base s.containsBase (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) hw))).mapIso
      (s.fibreToSpaceTwistModuleIso Px W (locusPoint w ≫ f.hom) d) ≪≫
    modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) hw)
      (s.twistPieceQcoh W (locusPoint w ≫ f.hom) d)

/-- A scheme point of `U(ψ)` lies in `U(ψ)`. -/
theorem locusOpen_locusPoint (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    (ofUnitalHom s f L ψ).locusOpen W (locusPoint w) = ⊤ :=
  (ofUnitalHom s f L ψ).locusOpen_eq_top_of_mem (yonedaEquiv w).2

/-- **The chart map `χ_w` of `θ` at a scheme point `w : W ⟶ U(ψ)`**, in degree `d`: the map
`w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` of `𝒪`-modules on the represented algebraic space of `W`
which is, through `…chartSourceIso` and `…chartTargetIso`, the module attached (Stacks 03DX (2))
to `θ` of [Stacks, Tag 01O9] on `W` (`…chartSchemeTheta`). -/
def chartMap (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℤ) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).obj
        (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).obj (thetaTarget s f L ψ d).obj :=
  (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
        s.shrink.containsBase W).functor.map
      (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
    (chartTargetIso w d).hom

end Chart

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
