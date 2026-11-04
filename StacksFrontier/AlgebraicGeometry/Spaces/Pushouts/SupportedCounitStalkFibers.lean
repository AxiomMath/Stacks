module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkRings

/-!
# The module fibres in the stalkwise proof of Stacks 0AEU

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `Z ⊆ X` a closed subspace such that
`f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat at the points of `f^{-1}Z`, and `ȳ` a geometric
point of `Y` with image `x̄`. The proof of Stacks 0AEU computes the stalk at `ȳ` of the counit
`Lf^*Rf_*Q ⟶ Q` on a K-injective complex supported on `|f^{-1}Z|`; degreewise, through Stacks 05V5
(`AlgebraicGeometry.Space.modulePullbackFiberIso`), this is the extension of scalars along
`ρ : 𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` (`AlgebraicGeometry.Space.smallEtaleStalkPullbackRingMap`) of the
comparison `θ : (f_*M)_x̄ ⟶ M_ȳ` followed by the action map. This file supplies the module-fibre
and ring-level facts that computation uses.

## Main results

* `AlgebraicGeometry.Space.isZero_sheafModuleFiberOfCommRing_obj_of_not_mem`: the fibre of a
  module at a geometric point outside its support vanishes.
* `AlgebraicGeometry.Space.flat_smallEtaleStalkPullbackRingMap_of_isFlatAt`,
  `AlgebraicGeometry.Space.bijective_quotientMap_smallEtaleStalkPullbackRingMap` and
  `AlgebraicGeometry.Space.map_comap_closedSubspaceStalkIdeal_le`: at a point of `f^{-1}Z` the
  ring map `ρ` is flat and bijective modulo the stalk `I_x̄` of the ideal of `Z`, and `I_x̄`
  generates an ideal inside the stalk of the ideal of `f^{-1}Z`; these are the hypotheses of
  Stacks 05E9 (`IPowerTorsion.extendRestrictScalarsAdj_counit_app_bijective`) at `ȳ`, read on the
  stalk rings of the points of the small étale sites.
* `AlgebraicGeometry.Space.extendScalars_map_directImageFiberMap_comp_counit`: the transpose of
  `θ` is the extension of scalars of `θ` followed by the action map.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre at a point off the support -/

/-- **The fibre of a module at a geometric point outside its support vanishes.** -/
theorem isZero_sheafModuleFiberOfCommRing_obj_of_not_mem (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (h : x.image ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :
    IsZero ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).obj M) := by
  have hs : Subsingleton (geometricModuleStalk B S hS X x M) := by
    rw [← not_nontrivial_iff_subsingleton]
    exact fun hnt ↦ h ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X M _).2
      ⟨x, rfl, hnt⟩)
  let e₁ := (Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O M).symm
  let e₂ := geometricModuleStalkAddEquiv B S hS X x M
  have : Subsingleton (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O M) :=
    ⟨fun a b ↦ e₁.injective (e₂.injective (Subsingleton.elim _ _))⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ### The stalk map at a point of `f^{-1}Z` -/

variable {B S hS}

/-- The stalk ring equivalences intertwine `ρ` with `etaleLocalRingMap`. -/
private theorem pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1) (a) :
    pointStalkRingEquiv B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y a) =
      etaleLocalRingMap Y.2 f.hom y (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y) a) :=
  RingHom.congr_fun (pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS f y) a

/-- **The stalk ring map of the pullback of modules is flat at a point where `f` is flat.** -/
theorem flat_smallEtaleStalkPullbackRingMap_of_isFlatAt {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1) (hf : IsFlatAt B S hS f.hom y.image) :
    (smallEtaleStalkPullbackRingMap B S hS f y).Flat :=
  IPowerTorsion.flat_of_ringEquiv (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y))
    (pointStalkRingEquiv B S hS Y y) _ (etaleLocalRingMap Y.2 f.hom y)
    (fun a ↦ (pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply f y a).symm)
    ((isFlatAt_iff_etaleLocalRingMap_flat Y.2 X.2 f.hom y).mp hf)

/-- **The stalk ring map of the pullback of modules is bijective modulo the ideal of `Z` at a
point of `f^{-1}Z`**, the ideal being the stalk `I_x̄` of the ideal of `Z` read on the stalk ring
of the point of the site. -/
theorem bijective_quotientMap_smallEtaleStalkPullbackRingMap {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (hfZ : IsIso (Z.fromPreimage f.hom))
    (hflat : ∀ p : points B S hS (Z.preimage f.hom).toFunctor,
      IsFlatAt B S hS f.hom
        (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι p))
    (y : GeometricPoint B S hS Y.1)
    (hy : y.image ∈
      Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) :
    Function.Bijective
      (Ideal.quotientMap
        (((closedSubspaceStalkIdeal B S hS X ⟨Z, hZ⟩ (geometricPointMap f.hom y)).comap
            (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y)).toRingHom).map
          (smallEtaleStalkPullbackRingMap B S hS f y))
        (smallEtaleStalkPullbackRingMap B S hS f y) Ideal.le_comap_map) :=
  IPowerTorsion.bijective_quotientMap_of_ringEquiv
    (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y)) (pointStalkRingEquiv B S hS Y y)
    _ (etaleLocalRingMap Y.2 f.hom y)
    (fun a ↦ (pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply f y a).symm) _
    (bijective_quotientMap_closedSubspaceStalkIdeal X.2 Y.2 f.hom Z hZ hfZ hflat y hy)

/-- **The stalk of the ideal of `Z` generates an ideal inside the stalk of the ideal of
`f^{-1}Z`**, read on the stalk rings of the points of the small étale sites. -/
theorem map_comap_closedSubspaceStalkIdeal_le {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (y : GeometricPoint B S hS Y.1) :
    ((closedSubspaceStalkIdeal B S hS X Z (geometricPointMap f.hom y)).comap
        (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y)).toRingHom).map
        (smallEtaleStalkPullbackRingMap B S hS f y) ≤
      (closedSubspaceStalkIdeal B S hS Y (preimageSubspace B S hS f Z) y).comap
        (pointStalkRingEquiv B S hS Y y).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  refine Ideal.mem_comap.2 ?_
  change pointStalkRingEquiv B S hS Y y (smallEtaleStalkPullbackRingMap B S hS f y a) ∈
    closedSubspaceStalkIdeal B S hS Y (preimageSubspace B S hS f Z) y
  rw [pointStalkRingEquiv_smallEtaleStalkPullbackRingMap_apply]
  exact map_closedSubspaceStalkIdeal_le B S hS f Z y
    (Ideal.mem_map_of_mem (etaleLocalRingMap Y.2 f.hom y) (Ideal.mem_comap.1 ha))

/-! ### The transpose of `θ` -/

variable (B S hS) in
/-- **The transpose of `θ` along extension of scalars is the extension of scalars of `θ` followed
by the action map** `𝒪_{Y,ȳ} ⊗ M_ȳ ⟶ M_ȳ`, the counit of extension and restriction of scalars
along `ρ`. -/
theorem extendScalars_map_directImageFiberMap_comp_counit {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
        ((directImageFiberMap B S hS f y).app M) ≫
      (ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).counit.app _ =
      directImageFiberMapTranspose B S hS f y M :=
  (Adjunction.homEquiv_counit _ _ _ _).symm.trans (directImageFiberMap_homEquiv_symm B S hS f y M)

end AlgebraicGeometry.Space

end
