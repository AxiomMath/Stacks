module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree
public import
StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso
public import StacksFrontier.CategoryTheory.Sites.Continuous.FreeAbelianLowerShriekTransition

/-!
# The two composition isomorphisms of derived pullback on small étale topoi of spaces

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces there are two spellings of the
identification `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D:
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, which compares the pullbacks of
modules along the composite of the morphisms of ringed topoi and along the morphism of the
composite as left adjoints of the transported direct image, and
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso`, which uses the
2-isomorphism of Stacks 03G8 between those morphisms of ringed topoi.  They agree.

## Main results

* `AlgebraicGeometry.Space.pushforwardModulesIso_compTwoIso` and
  `AlgebraicGeometry.Space.pullbackModulesIso_compTwoIso`: the direct image and the pullback of
  modules along the 2-isomorphism of Stacks 03G8 are the transports.  That the two spellings
  agree is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq`
  (`DerivedPullbackCompositionAgree.lean`).
* `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical_iso_eq_triangle_symm`: the
  identifications of the canonical pseudofunctoriality datum
  `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` are the inverses of the
  comparison triangles of the pullback datum
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, through
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The direct image of modules along the 2-isomorphism of Stacks 03G8 is the transport
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`. -/
theorem pushforwardModulesIso_compTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pushforwardModulesIso =
      pushforwardModulesCompTransport B S hS f g := by
  refine Iso.ext (NatTrans.ext (funext fun F => ?_))
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  rfl

/-- The pullback of modules along the 2-isomorphism of Stacks 03G8 is the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`: both are the uniqueness of left adjoints
of the transported direct image. -/
theorem pullbackModulesIso_compTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso =
      pullbackModulesCompTransport B S hS f g := by
  refine (Adjunction.leftAdjointUniq_ofNatIsoRight_left _ _
    (smallEtaleRingedToposHom_compTwoIso B S hS f g).pushforwardModulesIso.symm).trans ?_
  rw [pushforwardModulesIso_compTwoIso]
  rfl

variable {B S hS} in
/-- **The identifications of the canonical pseudofunctoriality datum are the inverses of the
comparison triangles of the pullback datum**: the composition comparison of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` is the inverse of the composition
isomorphism of Stacks 0D6D (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`). -/
theorem DerivedPullbackComposition.canonical_iso_eq_triangle_symm
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    (DerivedPullbackComposition.canonical B S hS).iso f g k h =
      ((smallEtaleDerivedPullbackData B S hS).triangle h).symm := by
  subst h
  rw [PullbackData.triangle_rfl, smallEtaleDerivedPullbackData_compIso_eq B S hS f g,
    smallEtaleDerivedModulePullbackCompIso_eq]
  ext M
  simp [DerivedPullbackComposition.canonical, smallEtaleDerivedPullbackFactorIso]
  rfl

end AlgebraicGeometry.Space

end
