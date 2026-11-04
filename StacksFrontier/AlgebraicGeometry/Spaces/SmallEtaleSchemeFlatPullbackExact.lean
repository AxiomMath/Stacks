module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left exactness of the small étale inverse image of modules along a flat morphism of schemes

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `E`, and let
`ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small étale ringed sites of
Stacks 070R (2), whose structure map is `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing`.
The inverse image `ε_a^*` of sheaves of modules is right exact, being a left adjoint. This file
proves that it is **left exact when `a` is flat**: it preserves finite limits.

The argument does not redo the stalk computation. It is already done for algebraic spaces:
`AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom` proves the inverse
image of modules of Stacks 03LU along a flat morphism of algebraic spaces left exact, by checking
it on the stalks at the geometric points, where it is extension of scalars along the flat map of
strictly henselian local rings. Two transports bring it to schemes.

* **From spaces to schemes, inside one fppf site.** For a morphism `g` of the big fppf category
  over `S`, `AlgebraicGeometry.Space.representedModulePullbackIso` identifies the inverse image
  along the represented morphism of algebraic spaces with `ε_{g}^*`, across the equivalences of
  the small étale sites of `yoneda.obj U` and of the scheme underlying `U`. The represented
  morphism is flat when the morphism of schemes is, flatness being étale local on source and
  target (Stacks 04R3), by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`.
  This is
  `AlgebraicGeometry.Space.preservesFiniteLimits_pullback_representedSchemeStructureMapRing`.
* **From the étale site of an fppf site to an arbitrary big étale site.** The previous step is
  about the big étale site `AlgebraicGeometry.associatedBigEtaleSite` attached to a big fppf
  site. Given an arbitrary big étale site `E`, the big fppf site
  `AlgebraicGeometry.BigFppfSite.ofCutoff` at the cutoff of `E` has, by definition, the same
  underlying category of schemes, so the small étale categories, the base change functors and the
  structure sheaves of the two étale sites agree on the nose. Only the topologies are written
  differently, through two different covering bounds; both are the topology of jointly surjective
  étale families, by `AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective` and
  `AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`, so they are equal, and
  `CategoryTheory.SheafOfModules.preservesFiniteLimits_pullback_of_eq_topology` carries left
  exactness of the pullback across an equality of topologies.

## Main results

* `CategoryTheory.SheafOfModules.preservesFiniteLimits_pullback_of_eq_topology`: left exactness
  of the pullback of sheaves of modules depends only on the underlying data, not on how the two
  topologies are written.
* `AlgebraicGeometry.Space.preservesFiniteLimits_pullback_representedSchemeStructureMapRing`: the
  small étale inverse image along a flat morphism of the big fppf category over `S` is left exact.
* `AlgebraicGeometry.SmallEtale.topology_associatedBigEtaleSite_ofCutoff`: the small étale
  topologies of a big étale site and of the étale site of the big fppf site at its cutoff agree.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_smallEtaleStructureMapRing`:
  **the inverse image `ε_a^*` of sheaves of modules along a flat morphism of schemes of an
  arbitrary big étale site is left exact.**
* `CategoryTheory.NatTrans.isIso_app_limit`: a natural transformation between functors which
  preserve limits of shape `J` is an isomorphism at the limit of a diagram as soon as it is one at
  each vertex; the dual of `CategoryTheory.NatTrans.isIso_app_colimit`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v v₁ v₂ u₁ u₂ w

namespace CategoryTheory.NatTrans

/-- A natural transformation `η : Φ ⟶ Ψ` between functors which preserve limits of shape `J`
is an isomorphism at the limit of a diagram `K : J ⥤ C` as soon as it is an isomorphism at each
`K i`.

Both `Φ` and `Ψ` turn the limit cone of `K` into a limit cone, and `η` whiskered with `K` is an
isomorphism, so postcomposing the image under `Φ` with it gives a second limit cone on `K ⋙ Ψ`.
The component of `η` at the limit is the comparison of the two, by naturality. This is the dual
of `CategoryTheory.NatTrans.isIso_app_colimit`. -/
theorem isIso_app_limit {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) (K : J ⥤ C) [HasLimit K]
    [PreservesLimitsOfShape J Φ] [PreservesLimitsOfShape J Ψ]
    (hη : ∀ i, IsIso (η.app (K.obj i))) :
    IsIso (η.app (limit K)) := by
  have hΨ : IsLimit (Ψ.mapCone (limit.cone K)) :=
    isLimitOfPreserves Ψ (limit.isLimit K)
  have hwi : ∀ i : J, IsIso ((Functor.whiskerLeft K η).app i) := hη
  have hw : IsIso (Functor.whiskerLeft K η) := NatIso.isIso_of_isIso_app _
  let α : K ⋙ Φ ≅ K ⋙ Ψ := asIso (Functor.whiskerLeft K η)
  have hΦ' : IsLimit ((Cone.postcompose α.hom).obj (Φ.mapCone (limit.cone K))) :=
    (IsLimit.postcomposeHomEquiv α _).symm (isLimitOfPreserves Φ (limit.isLimit K))
  have heq : η.app (limit K) = (IsLimit.conePointUniqueUpToIso hΦ' hΨ).hom := by
    refine hΨ.hom_ext fun i => ?_
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    exact (η.naturality (limit.π K i)).symm
  rw [heq]
  infer_instance

end CategoryTheory.NatTrans

namespace CategoryTheory.SheafOfModules

/-- **Left exactness of a pullback of sheaves of modules does not see how the topologies are
written.** Let `F` and `F'` be equal functors, continuous for topologies `J, K` and `J', K'`
with `J = J'` and `K = K'`, and let `φ` and `φ'` be morphisms of sheaves of rings along them with
the same underlying presheaves and the same underlying morphism. If pullback of sheaves of
modules along `φ` preserves finite limits, so does pullback along `φ'`.

After substituting the equalities the two situations coincide, sheaves being determined by their
underlying presheaves and their morphisms by the underlying morphisms of presheaves, and the
adjointness and continuity instances being propositions. -/
theorem preservesFiniteLimits_pullback_of_eq_topology
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J J' : GrothendieckTopology C} {K K' : GrothendieckTopology D} (hJ : J = J') (hK : K = K')
    {F F' : C ⥤ D} (hF : F = F') [hFc : F.IsContinuous J K] [hFc' : F'.IsContinuous J' K']
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} {S' : Sheaf J' RingCat.{w}}
    {R' : Sheaf K' RingCat.{w}} (hS : S.obj = S'.obj) (hR : R.obj = R'.obj)
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (φ' : S' ⟶ (F'.sheafPushforwardContinuous RingCat.{w} J' K').obj R')
    (hφ : HEq φ.hom φ'.hom)
    [hφr : (SheafOfModules.pushforward.{v} φ).IsRightAdjoint]
    [hφr' : (SheafOfModules.pushforward.{v} φ').IsRightAdjoint]
    (h : PreservesFiniteLimits (SheafOfModules.pullback.{v} φ)) :
    PreservesFiniteLimits (SheafOfModules.pullback.{v} φ') := by
  subst hJ hK hF
  obtain ⟨S, hS₁⟩ := S
  obtain ⟨S', hS'₁⟩ := S'
  obtain ⟨R, hR₁⟩ := R
  obtain ⟨R', hR'₁⟩ := R'
  dsimp only at hS hR
  subst hS hR
  obtain rfl : φ = φ' := Sheaf.hom_ext (eq_of_heq hφ)
  exact h

end CategoryTheory.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small étale inverse image along a flat morphism of the big fppf category over `S` is
left exact.** For `g : T' ⟶ T` whose underlying morphism of schemes is flat, pullback of
sheaves of modules along the structure map of the morphism of small étale ringed sites of
Stacks 070R (2) preserves finite limits.

Across the identifications of the small étale sites of `yoneda.obj T` and `yoneda.obj T'` with
those of the underlying schemes, this pullback is the inverse image of Stacks 03LU along the
represented morphism of algebraic spaces,
`AlgebraicGeometry.Space.representedModulePullbackIso`; that morphism is flat, flatness of
morphisms of algebraic spaces being read on étale charts and flatness of morphisms of schemes
being étale local on source and target, and the inverse image along a flat morphism of algebraic
spaces is left exact, `AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat_hom`.
Equivalences of categories preserve limits. -/
@[sga "4 IV 13.7" "special case"]
theorem preservesFiniteLimits_pullback_representedSchemeStructureMapRing
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : Flat ((BigFppfOver.toScheme B S hS).map g)) :
    PreservesFiniteLimits
      (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)) := by
  have h₁ : PreservesFiniteLimits (modulePullback B S hS (representedSpaceMap B S hS g)) :=
    preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (representedSpaceMap B S hS g)
      ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget g).2 hg)
  have h₂ : PreservesFiniteLimits
      ((representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ⋙
          (representedSmallEtaleModuleEquivalence B S hS T').inverse) := by
    have hinv' : PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS T').inverse :=
      inferInstance
    have hfun' : PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS T).functor :=
      inferInstance
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hfun'
      (@comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ hinv')
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerLeft (representedSmallEtaleModuleEquivalence B S hS T).functor
        (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalence B S hS T).unitIso.symm _ ≪≫
      Functor.leftUnitor _) h₂

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.SmallEtale

/-- The big fppf site at the cutoff of a big étale site `E`, with no initially prescribed schemes
or coverings. Its underlying category of schemes is the underlying category of `E` on the nose. -/
noncomputable abbrev fppfSiteAtCutoff (E : BigEtaleSite.{u}) : BigFppfSite.{u} :=
  BigFppfSite.ofCutoff E.cutoff E.aleph0_lt_cutoff E.cutoff_isStrongPrelimit
    E.aleph0_lt_cutoff_cof ∅ (by simp)

/-- **The small étale topology does not depend on the covering bound.** For a scheme `Z` of a big
étale site `E`, the small étale topology of `Z` in `E` and in the étale site of the big fppf site
at the cutoff of `E` agree: both are the topology whose covering sieves are those jointly
surjective on underlying points, by
`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective` and
`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`. -/
theorem topology_associatedBigEtaleSite_ofCutoff (E : BigEtaleSite.{u}) (Z : E.Scheme) :
    SmallEtale.topology (associatedBigEtaleSite (fppfSiteAtCutoff E)) Z.obj Z.property =
      SmallEtale.topology E Z.obj Z.property := by
  refine GrothendieckTopology.ext (funext fun W => Set.ext fun R => ⟨fun hR => ?_, fun hR => ?_⟩)
  · exact mem_topology_of_jointlySurjective fun x => exists_mem_arrows_mem_range
      (associatedBigEtaleSite (fppfSiteAtCutoff E)) Z.obj Z.property hR x
  · exact mem_topology_of_jointlySurjective fun x => exists_mem_arrows_mem_range
      E Z.obj Z.property hR x

/-- **The small étale inverse image of modules along a flat morphism of schemes is left exact.**
For a morphism `a : X ⟶ Y` of schemes of an arbitrary big étale site `E` whose underlying
morphism of schemes is flat, pullback of sheaves of modules along the structure map of the
morphism of small étale ringed sites `ε_a` of Stacks 070R (2) preserves finite limits.

The big fppf site at the cutoff of `E` has the same category of schemes as `E`; in its étale site
the statement is
`AlgebraicGeometry.Space.preservesFiniteLimits_pullback_representedSchemeStructureMapRing` at the
morphism `a` read as a morphism over `Y`. The two étale sites differ only in how their small étale
topologies are written, and those agree by
`AlgebraicGeometry.SmallEtale.topology_associatedBigEtaleSite_ofCutoff`. -/
theorem preservesFiniteLimits_pullback_smallEtaleStructureMapRing (E : BigEtaleSite.{u})
    {X Y : E.Scheme} (a : X ⟶ Y) (ha : Flat (E.inclusion.map a)) :
    PreservesFiniteLimits (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing E a)) := by
  let B : BigFppfSite.{u} := fppfSiteAtCutoff E
  let T : BigFppfOver B Y.obj Y.property := Over.mk (𝟙 (B.obj Y.property))
  let T' : BigFppfOver B Y.obj Y.property :=
    Over.mk (show (⟨X.obj, X.property⟩ : B.Schemes) ⟶ B.obj Y.property from a)
  let g : T' ⟶ T := Over.homMk (show T'.left ⟶ T.left from a) (Category.comp_id _)
  have hJ : Space.representedSchemeSmallEtaleTopology B Y.obj Y.property T =
      SmallEtale.topology E Y.obj Y.property :=
    topology_associatedBigEtaleSite_ofCutoff E Y
  have hK : Space.representedSchemeSmallEtaleTopology B Y.obj Y.property T' =
      SmallEtale.topology E X.obj X.property :=
    topology_associatedBigEtaleSite_ofCutoff E X
  exact SheafOfModules.preservesFiniteLimits_pullback_of_eq_topology.{u} hJ hK
    (F := Space.representedSchemeBaseChange B Y.obj Y.property g)
    (F' := smallEtaleBaseChange E a)
    (hFc := Space.isContinuous_representedSchemeBaseChange B Y.obj Y.property g)
    (hFc' := smallEtaleBaseChange_isContinuous E a)
    (hφr := Space.isRightAdjoint_pushforward_representedSchemeStructureMapRing B Y.obj
      Y.property g)
    (hφr' := pushforward_smallEtaleStructureMapRing_isRightAdjoint E a) rfl rfl rfl
    (Space.representedSchemeStructureMapRing B Y.obj Y.property g)
    (smallEtaleStructureMapRing E a) HEq.rfl
    (Space.preservesFiniteLimits_pullback_representedSchemeStructureMapRing B Y.obj Y.property g
      ha)

end AlgebraicGeometry.SmallEtale

end
