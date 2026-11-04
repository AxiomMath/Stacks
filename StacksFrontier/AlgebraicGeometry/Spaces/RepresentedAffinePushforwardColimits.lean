module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforwardColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent

/-!
# The direct image along an affine morphism of represented algebraic spaces commutes with colimits
of quasi-coherent modules

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is affine.  The direct image of Stacks 03LU along the morphism of representable algebraic
spaces `g` represents preserves the colimit of a diagram of quasi-coherent `𝒪`-modules.

This is `AlgebraicGeometry.SmallEtale.preservesColimit_pushforward_of_isAffineHom` carried across
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, exactly as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap` carries the
quasi-coherence statement across the same square.  The square is an isomorphism of *functors*, and
the two comparison functors of the small étale sites are equivalences, so no new geometry is
involved: both equivalences preserve all colimits and the quasi-coherence of the diagram transports
by `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff`.  This is the
colimit input of Stacks 01SB, carried across the square.

## Main results

* `AlgebraicGeometry.Space.preservesColimit_modulePushforward_representedSpaceMap`: **the direct
  image of Stacks 03LU along a morphism of representable algebraic spaces with affine underlying
  morphism of schemes preserves colimits of quasi-coherent modules.**

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₂ u₂ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

/-- The direct image along a morphism of representable algebraic spaces, conjugated back to the
small étale sites of the two schemes by the comparison equivalences: it is the small étale direct
image of the underlying morphism of schemes.

This is `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` with the equivalence on
the source cancelled by its counit, the form in which colimit preservation transports. -/
def representedModulePushforwardConjIso :
    (representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor) ≅
      modulePushforward B S hS (representedSpaceMap B S hS g) :=
  Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS T').inverse
      (representedModulePushforwardSquareIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) ≪≫
    Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalence B S hS T').counitIso
      (modulePushforward B S hS (representedSpaceMap B S hS g)) ≪≫
    Functor.leftUnitor _

/-- **The direct image of Stacks 03LU along a morphism of representable algebraic spaces whose
underlying morphism of schemes is affine preserves colimits of quasi-coherent modules.**

The diagram is carried to the small étale site of the scheme underlying `T'` by the comparison
equivalence, where it is still a diagram of quasi-coherent modules and where
`AlgebraicGeometry.SmallEtale.preservesColimit_pushforward_of_isAffineHom` applies; the two
equivalences preserve all colimits, being left adjoints. -/
theorem preservesColimit_modulePushforward_representedSpaceMap
    [_root_.AlgebraicGeometry.IsAffineHom (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left)]
    {D : K ⥤ Modules.{u, u} B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T')}
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    PreservesColimit D (modulePushforward B S hS (representedSpaceMap B S hS g)) := by
  have hD' : ∀ k, ((D ⋙ (representedSmallEtaleModuleEquivalence B S hS T').inverse).obj
      k).IsQuasicoherentOnSite := fun k ↦
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app (D.obj k)).symm (hD k))
  have _h1 : PreservesColimit (D ⋙ (representedSmallEtaleModuleEquivalence B S hS T').inverse)
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g)) :=
    _root_.AlgebraicGeometry.SmallEtale.preservesColimit_pushforward_of_isAffineHom
      (associatedBigEtaleSite B) g.left hD'
  have _e1 : PreservesColimit D (representedSmallEtaleModuleEquivalence B S hS T').inverse :=
    (Adjunction.leftAdjoint_preservesColimits
      (representedSmallEtaleModuleEquivalence B S hS
        T').symm.toAdjunction).preservesColimitsOfShape.preservesColimit
  have _e2 : PreservesColimitsOfSize.{v₂, u₂}
      (representedSmallEtaleModuleEquivalence B S hS T).functor :=
    Adjunction.leftAdjoint_preservesColimits
      (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction
  have _h2 : PreservesColimit (D ⋙ (representedSmallEtaleModuleEquivalence B S hS T').inverse)
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
    comp_preservesColimit _ _
  have _h3 : PreservesColimit D
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse ⋙
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T).functor)) :=
    comp_preservesColimit _ _
  exact (preservesColimit_iff_of_natIso D (representedModulePushforwardConjIso B S hS g)).1 _h3

end AlgebraicGeometry.Space

end
