module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LeftAdjoint
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite
public import StacksFrontier.Cotangent.SheavesOfRings.ULiftStandardResolution
public import StacksFrontier.Cotangent.Spaces.CotangentComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison `ε` for an algebraic space represented by a scheme

Let `T` be an object of the big fppf site over a scheme `S`, let `X = yoneda.obj T` be the
algebraic space it represents and `X₀` the underlying scheme.  Derived Categories of Spaces,
Section 071P, compares the small étale topos of `X` with the Zariski topos of `X₀` through the
morphism of ringed topoi `ε = id_{small, étale, Zar}` of Stacks 08H7.  This file constructs
`ε` for the small étale site of the *algebraic space* `X`, with both structure sheaves presented
in the universe `u + 1` of the étale site, which is where the cotangent complex
`AlgebraicGeometry.Space.cotangentComplex` of Stacks 08VD lives.

## Main definitions

* `AlgebraicGeometry.Space.representedOpensToSmallEtale`: the inclusion of the Zariski opens of
  `X₀` among the étale charts of `X`, the site functor of `ε`.
* `AlgebraicGeometry.Space.representedImageOpenAdjunction`: its left adjoint, sending an étale
  chart to its image open.
* `AlgebraicGeometry.Space.representedToZariskiMorphismOfTopoi`: the morphism of topoi
  `Sh(X_étale) ⟶ Sh(X₀,Zar)` of sheaves of sets in `Type (u + 1)` induced by the site functor.
* `AlgebraicGeometry.Space.smallEtaleRingedToposULift` and
  `AlgebraicGeometry.Space.representedZariskiRingedTopos`: the two ringed topoi
  `(X_étale, 𝒪_X)` and `(X₀,Zar, 𝒪_{X₀})` with structure rings in `CommRingCat.{u + 1}`.
* `AlgebraicGeometry.Space.representedToZariskiRingedToposHom`: `ε` as a morphism of ringed
  topoi.

## Main results

* `AlgebraicGeometry.Space.representedToZariskiMorphismOfTopoi_pushforward`: `ε_*` is
  restriction along the site functor.
* `AlgebraicGeometry.Space.representedToZariskiRingedToposHom_fSharp_app`: over an open
  `W ⊆ X₀` the structure map `ε♯` is the canonical identification `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`.
* `AlgebraicGeometry.Space.representedToZariskiRingedToposHom_unit_fSharpInverseImage`: the
  inverse-image form `ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of `ε♯` is its transpose under `ε⁻¹ ⊣ ε_*`.

## Implementation notes

The site functor is the inclusion `AlgebraicGeometry.SmallEtale.opensToSmallEtale` of the opens
of `X₀` into the small étale site of the *scheme* `X₀`, followed by the inverse of the
equivalence `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` between that site and the
small étale site of the algebraic space `X`.  The two sites live in different universes (the
opens of `X₀` form a `Type u`, the étale charts of `X` a `Type (u + 1)`), so the left exactness
of the inverse image is not the small-site statement of Stacks 00X5; it comes instead from the
left adjoint of the site functor, the image of an étale chart in `X₀` (openness of étale
morphisms, Stacks 03WT): by Stacks 08NH the inverse image is then the sheafification of
restriction along that left adjoint, which is left exact.

Both structure sheaves are presented in `CommRingCat.{u + 1}` by the canonical `ULift` of their
section rings, sectionwise through `AlgebraicGeometry.SheafOfModules.commRingCatULift`.  On the
étale side this is `AlgebraicGeometry.Space.smallEtaleStructureSheafULift`; on the Zariski side
`AlgebraicGeometry.SheafOfModules.sheafULift` would only reach the universe of the opens, so the
lift is `sheafCompose` with the universe lift itself.  The structure map `ε♯` is the lift of the
structure map `AlgebraicGeometry.SmallEtale.commRingStructureMap` of Stacks 070R for the scheme
`X₀`: the structure sheaf of the small étale site of `X` restricted along the equivalence is the
structure sheaf of the small étale site of `X₀` on the nose, both sending a chart to the global
functions of the same scheme.

## References

* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08NH](https://stacks.math.columbia.edu/tag/08NH)
* [Stacks Project, Tag 08VF](https://stacks.math.columbia.edu/tag/08VF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-! ### The site functor and its left adjoint -/

/-- **The site functor of `ε`**: the inclusion of the Zariski opens of the scheme `X₀`
underlying `T` among the étale charts of the algebraic space `yoneda.obj T`.  It is the
inclusion of the opens of `X₀` into the small étale site of the scheme `X₀`, followed by the
inverse of the equivalence of that site with the small étale site of `yoneda.obj T`. -/
noncomputable def representedOpensToSmallEtale :
    ((BigFppfOver.toScheme B S hS).obj T).Opens ⥤ SmallEtale B S hS (yoneda.obj T) :=
  _root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
    (representedSmallEtaleEquivalence B S hS T).inverse

/-- The image open of an étale chart of `yoneda.obj T` in the scheme `X₀`: the chart is carried
to the small étale site of `X₀`, where its image is open. -/
noncomputable def representedImageOpenFunctor :
    SmallEtale B S hS (yoneda.obj T) ⥤ ((BigFppfOver.toScheme B S hS).obj T).Opens :=
  (representedSmallEtaleEquivalence B S hS T).functor ⋙
    _root_.AlgebraicGeometry.SmallEtale.imageOpenFunctor (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- **The image open is left adjoint to the site functor of `ε`**: the composite of the
equivalence of sites with the adjunction `AlgebraicGeometry.SmallEtale.imageOpenAdjunction` of
the scheme `X₀` (openness of étale morphisms, Stacks 03WT). -/
noncomputable def representedImageOpenAdjunction :
    representedImageOpenFunctor B S hS T ⊣ representedOpensToSmallEtale B S hS T :=
  (representedSmallEtaleEquivalence B S hS T).toAdjunction.comp
    (_root_.AlgebraicGeometry.SmallEtale.imageOpenAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)

/-- The site functor of `ε` is continuous: it is the composite of two continuous functors. -/
instance isContinuous_representedOpensToSmallEtale :
    (representedOpensToSmallEtale B S hS T).IsContinuous
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) :=
  Functor.isContinuous_comp _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) _

/-! ### The morphism of topoi -/

open CategoryTheory.Adjunction in
/-- The direct image of sheaves of sets along the site functor of `ε` has a left adjoint, by
Stacks 08NH: the sheafification of restriction along the image-open functor. -/
instance isRightAdjoint_representedOpensToSmallEtale_sheafPushforward :
    ((representedOpensToSmallEtale B S hS T).sheafPushforwardContinuous (Type (u + 1))
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T))).IsRightAdjoint := by
  obtain ⟨⟨adj⟩, -⟩ :=
    nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous
      (Type (u + 1)) (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedImageOpenAdjunction B S hS T)
  exact adj.isRightAdjoint

open CategoryTheory.Adjunction in
/-- **The inverse image `ε⁻¹` of sheaves of sets is left exact.**  By Stacks 08NH it is the
sheafification of restriction along the left adjoint image-open functor, and both restriction
and sheafification are left exact. -/
instance preservesFiniteLimits_representedOpensToSmallEtale_sheafPullback :
    PreservesFiniteLimits ((representedOpensToSmallEtale B S hS T).sheafPullback (Type (u + 1))
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T))) := by
  obtain ⟨⟨adj⟩, _, -⟩ :=
    nonempty_adjunction_preservesFiniteLimits_isRightAdjoint_and_iso_sheafPushforwardCocontinuous
      (Type (u + 1)) (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedImageOpenAdjunction B S hS T)
  exact preservesFiniteLimits_of_natIso (adj.leftAdjointUniq
    ((representedOpensToSmallEtale B S hS T).sheafAdjunctionContinuous (Type (u + 1)) _ _))

/-- **The morphism of topoi underlying `ε`**, for the algebraic space `yoneda.obj T`
represented by the scheme `X₀`: the pair `ε⁻¹ ⊣ ε_*` on sheaves of sets in `Type (u + 1)`
induced by the site functor `AlgebraicGeometry.Space.representedOpensToSmallEtale`, whose
direct image is restriction along it and whose inverse image is left exact. -/
noncomputable def representedToZariskiMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS (yoneda.obj T)) (Type (u + 1)))
      (Sheaf (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
        (Type (u + 1))) where
  pushforward := (representedOpensToSmallEtale B S hS T).sheafPushforwardContinuous
    (Type (u + 1)) _ _
  inverseImage := (representedOpensToSmallEtale B S hS T).sheafPullback (Type (u + 1)) _ _
  adj := (representedOpensToSmallEtale B S hS T).sheafAdjunctionContinuous (Type (u + 1)) _ _
  preservesFiniteLimits := inferInstance

/-- `ε_*` is restriction along the site functor of `ε`. -/
@[simp]
theorem representedToZariskiMorphismOfTopoi_pushforward :
    (representedToZariskiMorphismOfTopoi B S hS T).pushforward =
      (representedOpensToSmallEtale B S hS T).sheafPushforwardContinuous (Type (u + 1))
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
        (SmallEtale.topology B S hS (yoneda.obj T)) :=
  rfl

/-- `ε⁻¹` is the pullback of sheaves of sets along the site functor of `ε`. -/
@[simp]
theorem representedToZariskiMorphismOfTopoi_inverseImage :
    (representedToZariskiMorphismOfTopoi B S hS T).inverseImage =
      (representedOpensToSmallEtale B S hS T).sheafPullback (Type (u + 1))
        (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
        (SmallEtale.topology B S hS (yoneda.obj T)) :=
  rfl

/-! ### The two ringed topoi -/

/-- The small étale ringed topos `(X_étale, 𝒪_X)` of an algebraic space, with its structure
rings presented in the universe `u + 1` of the site: the coefficient ring sheaf of the
cotangent complex `AlgebraicGeometry.Space.cotangentComplex`. -/
noncomputable abbrev smallEtaleRingedToposULift (X : AlgebraicSpaces B S hS) :
    RingedTopos.{u, u + 1, u + 1} :=
  ⟨SmallEtale B S hS X.1, SmallEtale.topology B S hS X.1, smallEtaleStructureSheafULift B S hS X⟩

/-- The Zariski ringed topos `(X₀,Zar, 𝒪_{X₀})` of the scheme underlying `T`, with the section
rings of `𝒪_{X₀}` lifted to `CommRingCat.{u + 1}` through
`AlgebraicGeometry.SheafOfModules.commRingCatULift`. -/
noncomputable abbrev representedZariskiRingedTopos : RingedTopos.{u, u, u + 1} :=
  ⟨((BigFppfOver.toScheme B S hS).obj T).Opens,
    Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T),
    (sheafCompose (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      SheafOfModules.commRingCatULift.{u, u + 1}).obj
      ((BigFppfOver.toScheme B S hS).obj T).sheaf⟩

/-! ### The morphism of ringed topoi -/

/-- The structure map of `ε` in restriction form: over an open `W ⊆ X₀` it is the lift of the
canonical identification `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`.  It is the lift of the structure map
`AlgebraicGeometry.SmallEtale.commRingStructureMap` of Stacks 070R for the scheme `X₀`, the
structure sheaf of `yoneda.obj T` restricted along the equivalence of sites being that of `X₀`
on the nose. -/
noncomputable def representedZariskiSharp :
    (representedZariskiRingedTopos B S hS T).O ⟶
      ((representedOpensToSmallEtale B S hS T).sheafPushforwardContinuous CommRingCat.{u + 1}
          (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
          (SmallEtale.topology B S hS (yoneda.obj T))).obj
        (smallEtaleStructureSheafULift B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  ObjectProperty.homMk (Functor.whiskerRight
    (_root_.AlgebraicGeometry.SmallEtale.commRingStructureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).hom
    SheafOfModules.commRingCatULift.{u, u + 1})

/-- Over an open `W ⊆ X₀`, the structure map of `ε` in restriction form is the lift of the
identification `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`. -/
@[simp]
theorem representedZariskiSharp_hom_app (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (representedZariskiSharp B S hS T).hom.app (op W) =
      SheafOfModules.commRingCatULift.{u, u + 1}.map (Scheme.Opens.topIso W).inv :=
  rfl

/-- **`ε : (X_étale, 𝒪_X) ⟶ (X₀,Zar, 𝒪_{X₀})` as a morphism of ringed topoi**, for the
algebraic space `yoneda.obj T` represented by the scheme `X₀` (Derived Categories of Spaces,
Section 071P; Stacks 08H7).  The underlying morphism of topoi is
`AlgebraicGeometry.Space.representedToZariskiMorphismOfTopoi` and the structure map is
`AlgebraicGeometry.Space.representedZariskiSharp`, read through the identification of the direct
image of sheaves of commutative rings with restriction along the site functor, which is the
identity on sections. -/
@[sga "4 VII 4.2.2"]
noncomputable def representedToZariskiRingedToposHom :
    RingedToposHom
      (smallEtaleRingedToposULift B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      (representedZariskiRingedTopos B S hS T) where
  toToposHom := representedToZariskiMorphismOfTopoi B S hS T
  fSharp := representedZariskiSharp B S hS T ≫
    (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
      (smallEtaleStructureSheafULift B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).inv

/-- `ε` has the morphism of topoi induced by its site functor. -/
@[simp]
theorem representedToZariskiRingedToposHom_toToposHom :
    (representedToZariskiRingedToposHom B S hS T).toToposHom =
      representedToZariskiMorphismOfTopoi B S hS T :=
  rfl

/-- The structure map `ε♯`, read through the identification of the direct image of sheaves of
commutative rings with restriction along the site functor, is
`AlgebraicGeometry.Space.representedZariskiSharp`. -/
theorem representedToZariskiRingedToposHom_fSharp_comp :
    (representedToZariskiRingedToposHom B S hS T).fSharp ≫
        (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
          (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
          (smallEtaleStructureSheafULift B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).hom =
      representedZariskiSharp B S hS T := by
  simp [representedToZariskiRingedToposHom]

/-- **`ε♯` on an open.**  Over an open `W ⊆ X₀` the structure map of `ε`, read through the
identification of the direct image with restriction (the identity on sections), is the lift of
the canonical identification `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`. -/
theorem representedToZariskiRingedToposHom_fSharp_app
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    ((representedToZariskiRingedToposHom B S hS T).fSharp ≫
        (restrictionCommRingIso (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
          (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
          (smallEtaleStructureSheafULift B S hS
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).hom).hom.app (op W) =
      SheafOfModules.commRingCatULift.{u, u + 1}.map
        (((BigFppfOver.toScheme B S hS).obj T).restrictFunctorΓ.inv.app (op W)) := by
  rw [representedToZariskiRingedToposHom_fSharp_comp, representedZariskiSharp_hom_app]
  rfl

/-- **`ε♯` on sections.**  Over an open `W ⊆ X₀` the structure map of `ε` sends a section of
the lifted `𝒪_{X₀}` to the lift of its image under `𝒪_{X₀}(W) = Γ(W, 𝒪_W)`. -/
theorem representedToZariskiRingedToposHom_fSharp_app_apply
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : (representedZariskiRingedTopos B S hS T).O.obj.obj (op W)) :
    (representedToZariskiRingedToposHom B S hS T).fSharp.hom.app (op W) x =
      (SheafOfModules.commRingCatULift.{u, u + 1}.map (Scheme.Opens.topIso W).inv) x :=
  rfl

/-- **The inverse-image form of `ε♯`.**  The structure map
`ε⁻¹𝒪_{X₀} ⟶ 𝒪_X` of `ε` corresponds to `ε♯` under the adjunction `ε⁻¹ ⊣ ε_*` of sheaves of
commutative rings: precomposed with the unit and pushed forward, it is `ε♯`. -/
theorem representedToZariskiRingedToposHom_unit_fSharpInverseImage :
    (commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T)).unit.app
          (representedZariskiRingedTopos B S hS T).O ≫
        (pushforwardCommRingFunctor (representedToZariskiMorphismOfTopoi B S hS T)).map
          (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage =
      (representedToZariskiRingedToposHom B S hS T).fSharp :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The inverse-image form of `ε♯` is the transpose of
`AlgebraicGeometry.Space.representedZariskiSharp` under `ε⁻¹ ⊣ ε_*`, the direct image being
read as restriction along the site functor. -/
theorem representedToZariskiRingedToposHom_fSharpInverseImage :
    (representedToZariskiRingedToposHom B S hS T).fSharpInverseImage =
      ((commRingImageAdjunction (representedToZariskiMorphismOfTopoi B S hS T)).homEquiv _ _).symm
        (representedZariskiSharp B S hS T ≫
          (restrictionCommRingIso
            (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj T))
            (SmallEtale.topology B S hS (yoneda.obj T)) (representedOpensToSmallEtale B S hS T)
            (smallEtaleStructureSheafULift B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)).inv) :=
  rfl

end AlgebraicGeometry.Space

end
