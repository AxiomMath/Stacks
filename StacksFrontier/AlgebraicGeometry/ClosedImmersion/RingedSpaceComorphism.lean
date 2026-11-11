module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# A closed immersion of schemes is a closed quotient of ringed spaces

A closed immersion of schemes `i : Z ⟶ X` is in particular a morphism of ringed spaces whose
underlying continuous map is a closed embedding and whose comorphism of structure sheaves
`𝒪_X ⟶ i_* 𝒪_Z` is surjective as a morphism of sheaves. These are the two conditions that make
the underlying morphism of ringed spaces a *closed quotient morphism*.

## Main results

* `isClosedEmbedding_base_toShHom`: the map of underlying spaces of the morphism of presheafed
  spaces induced by a closed immersion of schemes is a closed embedding.
* `isLocallySurjective_c_toShHom`: the structure-sheaf comorphism of a closed immersion of
  schemes is locally surjective.
* `epi_unitToPushforwardObjUnit_structureSheafHom`: the comorphism of structure sheaves of a
  closed immersion of schemes is an epimorphism of sheaves of modules.

## References

* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

universe u

namespace Stacks.ClosedImmersion

/-- The map of underlying topological spaces of a closed immersion of schemes remains a closed
embedding after forgetting the scheme structure down to presheafed spaces. -/
theorem isClosedEmbedding_base_toShHom {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    Topology.IsClosedEmbedding
      (((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map
        i.toLRSHom.toShHom).base) :=
  AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i

/-- The structure-sheaf comorphism `𝒪_X ⟶ i_* 𝒪_Z` of a closed immersion of schemes is locally
surjective. -/
theorem isLocallySurjective_c_toShHom {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    TopCat.Presheaf.IsLocallySurjective
      (((SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)).map
        i.toLRSHom.toShHom).c) := by
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hx : x ∈ Set.range (ConcreteCategory.hom i.base)
  · obtain ⟨z, rfl⟩ := hx
    have key : Function.Surjective
        (⇑(ConcreteCategory.hom
            (Z.presheaf.stalkPushforward CommRingCat i.toLRSHom.toShHom.hom.base z)) ∘
          ⇑(ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor CommRingCat (i.base z)).map
              i.toLRSHom.toShHom.hom.c))) :=
      i.stalkMap_surjective z
    have hiso : IsIso (Z.presheaf.stalkPushforward CommRingCat
        i.toLRSHom.toShHom.hom.base z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing _
        (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).isInducing _ _
    exact key.of_comp_left (ConcreteCategory.bijective_of_isIso _).1
  · have hterm := ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
      i.toLRSHom.toShHom.hom.base Z.toSheafedSpace.IsSheaf
      (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i) x hx
    have hss := CommRingCat.subsingleton_of_isTerminal hterm
    exact fun _ => ⟨0, hss.elim _ _⟩

/-- The comorphism of structure sheaves of a closed immersion of schemes `i : Z ⟶ X`, as the
morphism `SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i)` of sheaves of
`𝒪_X`-modules, is an epimorphism. -/
theorem epi_unitToPushforwardObjUnit_structureSheafHom {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    Epi (_root_.SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)) := by
  set R := structureSheafRing X.toRingedSpace
  set h := _root_.SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom)
  have hloc := isLocallySurjective_c_toShHom i
  have hlocAb : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X.carrier)
      ((_root_.SheafOfModules.toSheaf R).map h).hom := by
    constructor
    intro U s x hx
    obtain ⟨V, f, ⟨a, ha⟩, hxV⟩ := hloc.imageSieve_mem s x hx
    refine ⟨V, f, ⟨a, ?_⟩, hxV⟩
    change h.val.app (Opposite.op V) a = _ at ha
    convert ha using 1
    rfl
  have : Sheaf.IsLocallySurjective ((_root_.SheafOfModules.toSheaf R).map h) := hlocAb
  exact (_root_.SheafOfModules.toSheaf R).epi_of_epi_map
    (show Epi ((_root_.SheafOfModules.toSheaf R).map h) by infer_instance)

end Stacks.ClosedImmersion

end
