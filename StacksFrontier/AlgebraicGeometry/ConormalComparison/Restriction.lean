module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison

/-!
# The ideal sheaf under restriction to an open of the target

For a morphism of schemes `f : X ⟶ S` and an open `V ≤ S`, the restriction to `V` of the ideal
sheaf of `f` is the ideal sheaf of the morphism `f ∣_ V : f ⁻¹ᵁ V ⟶ V`. Here the source is cut
down to `f ⁻¹ᵁ V`; `Stacks.IdealSheafRestrict.pullbackIdealSheafIso` treats the other
restriction, along an open immersion of the target with the source left whole.

## Main results

* `Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app`: the section formula for
  `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`. On sections over an open
  `W` of `V` the comparison is the restriction map of `M` along the equality
  `(f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ W) = f ⁻¹ᵁ (V.ι ''ᵁ W)`.
* `Stacks.Conormal.Restriction.restrictStructureMapRestrictSquare`: the structure-sheaf map of
  `f ∣_ V` is the restriction to `V` of the structure-sheaf map of `f`.
* `Stacks.Conormal.Restriction.restrictIdealSheafIso`: the restriction to `V` of the ideal sheaf
  of `f` is the ideal sheaf of `f ∣_ V`.
* `Stacks.Conormal.Restriction.restrictIdealSheafIso_hom_comp_ι`: its characterization through
  the monomorphism `CategoryTheory.Limits.kernel.ι`, which determines it.
* `Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app`: the adjoint
  characterization of `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`, which
  determines it since adjoint transposition is a bijection.

## Implementation notes

The square is checked on sections. Both sides are, after the three `rfl` steps
`Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app`,
`Stacks.Conormal.Restriction.restrictFunctor_map_structureMap_app` and
`AlgebraicGeometry.Scheme.Modules.pushforward_map_app`, the composite of `f.app (V.ι ''ᵁ W)`
with the restriction along `image_morphismRestrict_preimage`, which is exactly
`AlgebraicGeometry.morphismRestrict_app`. The two `restrictUnitModuleIso` factors are the
identity on sections because `AlgebraicGeometry.Scheme.Opens.ι_appIso` is `Iso.refl`.

The ideal sheaf is then transported by the same two steps as
`Stacks.IdealSheafRestrict.restrictKernelStructureMapIso`: restriction along an open immersion
preserves finite limits (`Stacks.IdealSheafRestrict.preservesFiniteLimits_restrictFunctor`), so
`CategoryTheory.Limits.PreservesKernel.iso` moves it inside the kernel, and
`CategoryTheory.Limits.kernel.mapIso` transports along the square.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafRestrict

universe u

namespace Stacks.Conormal.Restriction

/-! ### Section formulas -/

/-- **The section formula for `restrictPushforwardIso`.** Over an open `W` of `V`, the
comparison between the restriction to `V` of a direct image and the direct image along
`f ∣_ V` of the restriction is the restriction map of `M` along the equality
`(f ⁻¹ᵁ V).ι ''ᵁ ((f ∣_ V) ⁻¹ᵁ W) = f ⁻¹ᵁ (V.ι ''ᵁ W)`.

Three of the four factors of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` are identities on sections
(`SheafOfModules.pushforwardComp` twice and
`SheafOfModules.pushforwardCongr` once) and the fourth is
`SheafOfModules.pushforwardNatTrans` at an `eqToIso`, so the identity holds by
`rfl`. -/
theorem restrictPushforwardIso_hom_app {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (M : X.Modules) (W : V.toScheme.Opens)
    (x : Γ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor V.ι).obj M, W)) :
    ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app M).hom.app W
        x =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f V W)).op x :=
  rfl

/-- The identification of the restriction of the structure sheaf is the identity on sections,
for the inclusion of an open subscheme: `AlgebraicGeometry.Scheme.Opens.ι_appIso` is
`Iso.refl`. -/
theorem restrictUnitModuleIso_ι_hom_app {S : Scheme.{u}} (V : S.Opens) (W : V.toScheme.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor V.ι).obj (unitModule S), W)) :
    (restrictUnitModuleIso V.ι).hom.app W x = x :=
  (restrictUnitModuleIso_hom_app V.ι W x).trans (by simp only [Scheme.Opens.ι_appIso]; rfl)

/-- The restriction to `V` of the structure-sheaf map of `f` acts on sections over `W` as the
structure-sheaf map of `f` over `V.ι ''ᵁ W`. -/
theorem restrictFunctor_map_structureMap_app {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (W : V.toScheme.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor V.ι).obj (unitModule S), W)) :
    ((Scheme.Modules.restrictFunctor V.ι).map (structureMap f)).app W x =
      f.app (V.ι ''ᵁ W) x :=
  rfl

/-! ### The square -/

/-- **The structure-sheaf map of `f ∣_ V` is the restriction to `V` of the structure-sheaf map
of `f`.** This is `AlgebraicGeometry.morphismRestrict_app` read through the two identifications
of restricted structure sheaves and the comparison of the restricted direct image. -/
theorem restrictStructureMapRestrictSquare {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).map (structureMap f) ≫
        ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app
          (unitModule X)).hom ≫
        (Scheme.Modules.pushforward (f ∣_ V)).map
          (restrictUnitModuleIso (f ⁻¹ᵁ V).ι).hom =
      (restrictUnitModuleIso V.ι).hom ≫ structureMap (f ∣_ V) := by
  ext W x
  refine (restrictUnitModuleIso_ι_hom_app (f ⁻¹ᵁ V) ((f ∣_ V) ⁻¹ᵁ W) _).trans ?_
  refine Eq.trans ?_ (congrArg ((structureMap (f ∣_ V)).app W)
    (restrictUnitModuleIso_ι_hom_app V W x)).symm
  have h := morphismRestrict_app f V W
  exact congr($h.symm x)

/-! ### The ideal sheaf -/

/-- **Restriction to an open of the target commutes with the ideal sheaf, with the source cut
down to the preimage.** For a morphism of schemes `f : X ⟶ S` and an open `V ≤ S`, the
restriction to `V` of the ideal sheaf of `f` is the ideal sheaf of `f ∣_ V`.

Restriction along the open immersion `V.ι` preserves finite limits, so it may be moved inside
the kernel, and `CategoryTheory.Limits.kernel.mapIso` transports along
`restrictStructureMapRestrictSquare`. -/
noncomputable def restrictIdealSheafIso {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).obj (kernel (structureMap f)) ≅
      kernel (structureMap (f ∣_ V)) :=
  (PreservesKernel.iso (Scheme.Modules.restrictFunctor V.ι) (structureMap f)).trans
    (kernel.mapIso ((Scheme.Modules.restrictFunctor V.ι).map (structureMap f))
      (structureMap (f ∣_ V)) (restrictUnitModuleIso V.ι)
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso f V).app
          (unitModule X) ≪≫
        (Scheme.Modules.pushforward (f ∣_ V)).mapIso (restrictUnitModuleIso (f ⁻¹ᵁ V).ι))
      (restrictStructureMapRestrictSquare f V))

/-- **`restrictIdealSheafIso` commutes with the inclusions of the two ideal sheaves into the
two structure sheaves.** Those inclusions are monomorphisms, so this determines the
isomorphism. -/
theorem restrictIdealSheafIso_hom_comp_ι {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    (restrictIdealSheafIso f V).hom ≫ kernel.ι (structureMap (f ∣_ V)) =
      (Scheme.Modules.restrictFunctor V.ι).map (kernel.ι (structureMap f)) ≫
        (restrictUnitModuleIso V.ι).hom := by
  rw [restrictIdealSheafIso, Iso.trans_hom, Category.assoc, kernel.mapIso_hom, kernel.lift_ι,
    ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- `restrictIdealSheafIso` with the ideal sheaf written as `Stacks.ClosedImmersion.idealSheaf`.
The two statements are the same up to unfolding, by
`Stacks.IdealSheafRestrict.kernel_structureMap`. -/
noncomputable def restrictIdealSheafIso' {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom) ≅
      Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom :=
  restrictIdealSheafIso f V

/-! ### The adjoint characterization of `pullbackRestrictIso` -/

/-- **The adjoint characterization of
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso`.** That isomorphism is built
by `CategoryTheory.Adjunction.leftAdjointUniq`, and a `leftAdjointUniq` is pinned down by the
transpose of its components: the unit of the first adjunction, followed by the right adjoint
applied to the comparison, is the unit of the second.

Adjoint transposition is a bijection, so this determines `pullbackRestrictIso`. -/
theorem unit_comp_map_pullbackRestrictIso_hom_app {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (M : S.Modules) :
    (Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictAdjunction f V).unit.app M ≫
        (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
          ((Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso f V).hom.app M) =
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPullbackAdjunction f V).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V))).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

end Stacks.Conormal.Restriction

end
