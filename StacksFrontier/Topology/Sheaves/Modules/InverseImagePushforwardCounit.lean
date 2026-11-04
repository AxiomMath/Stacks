module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
public import StacksFrontier.Topology.Sheaves.Modules.InverseImageStalk
public import StacksFrontier.Topology.Sheaves.Modules.PullbackUnderlyingSheaf
public import StacksFrontier.Topology.Sheaves.RingedSpace.OfSheaf

/-!
# `i⁻¹ i_* = id` for sheaves of modules

Stacks 00AE says that for an inducing map `i : Z ⟶ X` of topological spaces — in particular for
the inclusion of a closed subset — the counit `i⁻¹ i_* ⟶ 𝟭` of the inverse-image/direct-image
adjunction on sheaves is an isomorphism. For sheaves of sets, abelian sheaves and sheaves of
algebraic structures this is `ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso`.
This file proves the corresponding statement for sheaves of modules.

The module pullback `i^*` is the topological inverse image `i⁻¹` followed by extension of
scalars along `i⁻¹𝒪_X ⟶ 𝒪_Z`, and the two agree when that structure map is invertible on stalks
(`Stacks.RingedSpace.isIso_pullbackUnderlyingSheafMap`). Over the inverse-image ringed space
`(Z, i⁻¹𝒪_X)`, the germ maps of `AlgebraicGeometry.RingedSpace.inverseImageProjection` are
isomorphisms for every continuous map `i`
(`AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection`), so there the only
hypothesis is that `i` is inducing.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.inverseImagePushforwardIso`: `i⁻¹ (i_* N) ≅ N` for a
  sheaf of `i⁻¹O`-modules `N` and an inducing `i`.
* `AlgebraicGeometry.SheafOfModules.inverseImageIsoOfPushforwardIso`: a sheaf of `O`-modules
  identified with a direct image `i_* N` has `N` as its inverse image.

## Main results

* `Stacks.RingedSpace.pullbackUnderlyingSheafMap_comp_counit`: the comparison
  `f⁻¹(M^{ab}) ⟶ (f^*M)^{ab}` at `f_* N`, composed with the underlying abelian morphism of the
  module counit, is the counit of the abelian-sheaf adjunction.
* `Stacks.RingedSpace.isIso_modulePullbackPushforward_counit`: for a morphism of ringed spaces
  whose underlying map is inducing and all of whose germ maps are invertible, the counit
  `f^* f_* ⟶ 𝟭` of the module adjunction is an isomorphism.
* `AlgebraicGeometry.RingedSpace.isIso_inverseImageModuleAdjunction_counit`: the counit of
  `AlgebraicGeometry.RingedSpace.inverseImageModuleAdjunction` is an isomorphism for an inducing
  map.
* `AlgebraicGeometry.SheafOfModules.structureSheafHom_inverseImageProjection`,
  `AlgebraicGeometry.SheafOfModules.modulePullback_inverseImageProjection`,
  `AlgebraicGeometry.SheafOfModules.modulePushforward_inverseImageProjection` and
  `AlgebraicGeometry.SheafOfModules.modulePullbackPushforwardAdjunction_inverseImageProjection`:
  the module functors and the adjunction of `inverseImageProjection` are
  `AlgebraicGeometry.SheafOfModules.inverseImageModule`, the direct image and
  `AlgebraicGeometry.SheafOfModules.inverseImageAdjunction`, by definition.
* `AlgebraicGeometry.SheafOfModules.isIso_inverseImageAdjunction_counit`: the counit of
  `AlgebraicGeometry.SheafOfModules.inverseImageAdjunction` is an isomorphism for an inducing
  map.

## Implementation notes

The general statement assumes the germ maps invertible rather than the morphism of ringed spaces
a closed immersion: the structure morphism of `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` is the adjunction unit,
which is not locally surjective, while its germ maps are isomorphisms. Invertibility of a
morphism of sheaves of modules is read off the underlying sheaf of abelian groups, since
`CategoryTheory.SheafOfModules.toSheaf` is faithful and so reflects isomorphisms.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction

variable {X' Y' : AlgebraicGeometry.RingedSpace.{u, u}} (g : X' ⟶ Y')
  (N : _root_.SheafOfModules.{u} (structureSheafRing X'))

/-- The comparison `Stacks.RingedSpace.pullbackUnderlyingSheafMap` at `g_* N`, composed with the
underlying abelian morphism of the counit of the module adjunction, is the counit of the
adjunction on sheaves of abelian groups. -/
theorem pullbackUnderlyingSheafMap_comp_counit :
    pullbackUnderlyingSheafMap g ((modulePushforward g).obj N) ≫
        (_root_.SheafOfModules.toSheaf (structureSheafRing X')).map
          ((modulePullbackPushforwardAdjunction g).counit.app N) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.hom.base).counit.app
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).obj N) := by
  have hinner : moduleUnitUnderlying g ((modulePushforward g).obj N) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.hom.base).map
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).map
          ((modulePullbackPushforwardAdjunction g).counit.app N)) = 𝟙 _ := by
    refine Eq.trans ?_ (congrArg
      (_root_.SheafOfModules.toSheaf (structureSheafRing Y')).map
      ((modulePullbackPushforwardAdjunction g).right_triangle_components N))
    exact ((_root_.SheafOfModules.toSheaf (structureSheafRing Y')).map_comp
      ((modulePullbackPushforwardAdjunction g).unit.app ((modulePushforward g).obj N))
      ((modulePushforward g).map
        ((modulePullbackPushforwardAdjunction g).counit.app N))).symm
  refine Eq.trans (Adjunction.homEquiv_naturality_right_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.hom.base)
    (moduleUnitUnderlying g ((modulePushforward g).obj N))
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).map
      ((modulePullbackPushforwardAdjunction g).counit.app N))).symm ?_
  refine Eq.trans (congrArg
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.hom.base).homEquiv
      ((_root_.SheafOfModules.toSheaf (structureSheafRing Y')).obj
        ((modulePushforward g).obj N))
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).obj N)).symm hinner) ?_
  refine Eq.trans (Adjunction.homEquiv_counit
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.hom.base) _ _ _) ?_
  refine Eq.trans (congrArg (fun t ↦ t ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction
      AddCommGrpCat.{u} g.hom.base).counit.app
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).obj N))
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} g.hom.base).map_id _)) ?_
  exact Category.id_comp _

/-- For a morphism of ringed spaces `g` whose underlying map is inducing and whose germ maps are
invertible, the counit `g^* g_* ⟶ 𝟭` of the module adjunction is an isomorphism. -/
theorem isIso_modulePullbackPushforward_counit
    (hind : IsInducing (ConcreteCategory.hom g.hom.base))
    (hs : ∀ x : X', IsIso (g.hom.stalkMap x)) :
    IsIso ((modulePullbackPushforwardAdjunction g).counit.app N) := by
  have : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      g.hom.base).counit) :=
    ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso AddCommGrpCat.{u} hind
  have h₂ : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      g.hom.base).counit.app
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).obj N)) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((_root_.SheafOfModules.toSheaf (structureSheafRing X')).map
      ((modulePullbackPushforwardAdjunction g).counit.app N)) :=
    Stacks.Topology.isIso_of_comp_eq_right _ _ _ (isIso_pullbackUnderlyingSheafMap g _ hs) h₂
      (pullbackUnderlyingSheafMap_comp_counit g N)
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf (structureSheafRing X'))

end Stacks.RingedSpace

namespace AlgebraicGeometry.RingedSpace

open RingedSpaceModuleAdjunction

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier)

/-- For an inducing `i`, the counit `i⁻¹ i_* ⟶ 𝟭` is an isomorphism on sheaves of
`i⁻¹𝒪_X`-modules. -/
theorem isIso_inverseImageModuleAdjunction_counit
    (hi : IsInducing (ConcreteCategory.hom i))
    (N : _root_.SheafOfModules.{u} (structureSheafRing (inverseImage X i))) :
    IsIso ((inverseImageModuleAdjunction X i).counit.app N) :=
  Stacks.RingedSpace.isIso_modulePullbackPushforward_counit (inverseImageProjection X i) N hi
    (isIso_stalkMap_inverseImageProjection X i)

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.SheafOfModules

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X)

/-- The structure morphism of `AlgebraicGeometry.RingedSpace.inverseImageProjection`, at the type
the module pullback takes as input, is
`AlgebraicGeometry.SheafOfModules.inverseImageRingHom`. -/
theorem structureSheafHom_inverseImageProjection :
    RingedSpaceModuleAdjunction.structureSheafHom
        (AlgebraicGeometry.RingedSpace.inverseImageProjection (ringedSpaceOfSheaf O) f) =
      inverseImageRingHom f O :=
  rfl

/-- The module pullback along `inverseImageProjection` is the inverse image of sheaves of modules
`AlgebraicGeometry.SheafOfModules.inverseImageModule`. -/
theorem modulePullback_inverseImageProjection :
    AlgebraicGeometry.RingedSpace.inverseImageModulePullback (ringedSpaceOfSheaf O) f =
      _root_.SheafOfModules.pullback.{u} (inverseImageRingHom f O) :=
  rfl

/-- The module pushforward along `inverseImageProjection` is the direct image appearing in
`AlgebraicGeometry.SheafOfModules.inverseImageAdjunction`. -/
theorem modulePushforward_inverseImageProjection :
    AlgebraicGeometry.RingedSpace.inverseImageModulePushforward (ringedSpaceOfSheaf O) f =
      _root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O) :=
  rfl

/-- The module adjunction of `inverseImageProjection` is
`AlgebraicGeometry.SheafOfModules.inverseImageAdjunction`. -/
theorem modulePullbackPushforwardAdjunction_inverseImageProjection :
    AlgebraicGeometry.RingedSpace.inverseImageModuleAdjunction (ringedSpaceOfSheaf O) f =
      inverseImageAdjunction f O :=
  rfl

/-- For an inducing map `i : Y ⟶ X` the counit
`i⁻¹ i_* ⟶ 𝟭` of the inverse-image/direct-image adjunction on sheaves of `i⁻¹O`-modules is an
isomorphism. -/
theorem isIso_inverseImageAdjunction_counit
    (hf : IsInducing (ConcreteCategory.hom f))
    (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O))) :
    IsIso ((inverseImageAdjunction f O).counit.app N) :=
  AlgebraicGeometry.RingedSpace.isIso_inverseImageModuleAdjunction_counit
    (ringedSpaceOfSheaf O) f hf N

/-- `i⁻¹ (i_* N) ≅ N` for sheaves of modules over `i⁻¹O`, along an inducing map `i`. -/
noncomputable def inverseImagePushforwardIso
    (hf : IsInducing (ConcreteCategory.hom f))
    (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O))) :
    inverseImageModule f O
        ((_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj N) ≅ N :=
  @asIso _ _ _ _ ((inverseImageAdjunction f O).counit.app N)
    (isIso_inverseImageAdjunction_counit f O hf N)

/-- For an inducing `i`, a sheaf of `O`-modules `M` isomorphic to a direct image `i_* N` has
inverse image `i⁻¹ M ≅ N`. -/
noncomputable def inverseImageIsoOfPushforwardIso
    (hf : IsInducing (ConcreteCategory.hom f))
    {M : _root_.SheafOfModules.{u} (underlyingRingSheaf O)}
    {N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O))}
    (e : M ≅ (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj N) :
    inverseImageModule f O M ≅ N :=
  (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f O)).mapIso e ≪≫
    inverseImagePushforwardIso f O hf N

end AlgebraicGeometry.SheafOfModules

end
