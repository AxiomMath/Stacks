module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusPowerTrivialization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModulesStalkSequenceColimit
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The colimit clause of [Stacks, Tag 0EBN] is a statement about the points off the locus

`Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerSystemPushforwardCocone F s` is the
cocone of [Stacks, Tag 0EBN] on the system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`, with vertex `j_*𝒪_U` for
`U = AlgebraicGeometry.sectionIsomorphismOpen X F s`.  This file shows that it is colimiting as
soon as its stalk at every point of `X \ U` is colimiting.

A cocone on an `ℕ`-indexed diagram of `𝒪_X`-modules is colimiting as soon as its stalk at every
point is colimiting.  At a point of `U` the stalk of the cocone is colimiting unconditionally: the
leg at `n` is the unit `ℱ^{[n]} ⟶ j_*(ℱ^{[n]}|_U)` followed by the direct image of the
trivialization `ℱ^{[n]}|_U ≅ 𝒪_U`, and both factors are invertible on the stalk at a point of
`U`.

## Main results

* `Stacks.ModuleSkyscraper.isIso_modulesStalkFunctor_map_iff`: being invertible on the stalk over
  `𝒪_{X, x}` is being invertible on the stalk of abelian groups.
* `Stacks.ModuleSkyscraper.isIso_of_forall_isIso_modulesStalkFunctor_map`: a morphism of
  `𝒪_X`-modules invertible on every stalk over the local rings is invertible.
* `Stacks.ModuleSkyscraper.isColimitOfForallIsColimitModulesStalk`: **a cocone on an
  `ℕ`-indexed diagram of `𝒪_X`-modules whose stalk at every point is colimiting is colimiting.**
* `Stacks.ModuleSkyscraper.isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app`: the unit
  `ℳ ⟶ j_*(ℳ|_U)` of `Scheme.Modules.restrictAdjunction` is invertible on the stalk at a point
  of `U`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isColimitStalkPushforwardCocone_of_mem`: at a point
  of `U` the stalk of the cocone of [Stacks, Tag 0EBN] is colimiting.
* `Stacks.AlgebraicGeometry.ReflexivePowers.isColimitPushforwardCocone_of_notMem`: **the colimit
  clause of [Stacks, Tag 0EBN] follows from the stalk clause at the points of `X \ U`.**

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ModuleSkyscraper

variable {X : Scheme.{u}}

/-! ### Isomorphy is stalkwise, over the local rings -/

/-- **Invertibility on the stalk over `𝒪_{X, x}` is invertibility on the stalk of abelian
groups.** -/
theorem isIso_modulesStalkFunctor_map_iff {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    IsIso ((modulesStalkFunctor X x).map φ) ↔
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Scheme.Modules.toPresheaf X).map φ)) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

/-- **A morphism of `𝒪_X`-modules invertible on every stalk over the local rings is
invertible.** -/
theorem isIso_of_forall_isIso_modulesStalkFunctor_map {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, IsIso ((modulesStalkFunctor X x).map φ)) : IsIso φ :=
  ExtensionByZeroModules.isIso_of_stalk_isIso X.ringCatSheaf φ fun x =>
    (isIso_modulesStalkFunctor_map_iff φ x).mp (h x)

/-! ### Recognising a colimit of an `ℕ`-indexed diagram of modules stalkwise -/

/-- **A cocone on an `ℕ`-indexed diagram of `𝒪_X`-modules whose stalk at every point is
colimiting is colimiting.** -/
def isColimitOfForallIsColimitModulesStalk {D : CategoryTheory.Functor ℕ X.Modules}
    (c : Cocone D) (h : ∀ x : X, IsColimit ((modulesStalkFunctor X x).mapCocone c)) :
    IsColimit c := by
  have hd := colimit.isColimit D
  haveI : IsIso (hd.desc c) := by
    refine isIso_of_forall_isIso_modulesStalkFunctor_map _ fun x => ?_
    have key : (modulesStalkFunctor X x).map (hd.desc c) =
        ((isColimitModulesStalkMapCocone X x hd).coconePointUniqueUpToIso (h x)).hom := by
      refine (isColimitModulesStalkMapCocone X x hd).hom_ext fun n => ?_
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      change (modulesStalkFunctor X x).map ((colimit.cocone D).ι.app n) ≫
        (modulesStalkFunctor X x).map (hd.desc c) =
          (modulesStalkFunctor X x).map (c.ι.app n)
      rw [← Functor.map_comp, hd.fac]
    rw [key]
    infer_instance
  exact IsColimit.ofPointIso hd

/-! ### The unit of the restriction adjunction at a point of the open -/

/-- **The unit `ℳ ⟶ j_*(ℳ|_U)` of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is
invertible on the stalk at a point of `U`.** -/
theorem isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app (U : X.Opens) (M : X.Modules)
    (y : U.toScheme) :
    IsIso ((modulesStalkFunctor X (U.ι.base y)).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
  rw [isIso_modulesStalkFunctor_map_iff]
  have hL : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)) := by
    have htri : (Scheme.Modules.restrictFunctor U.ι).map
          ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) ≫
        (Scheme.Modules.restrictAdjunction U.ι).counit.app
          ((Scheme.Modules.restrictFunctor U.ι).obj M) = 𝟙 _ :=
      (Scheme.Modules.restrictAdjunction U.ι).left_triangle_components M
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) ≫
          (Scheme.Modules.restrictAdjunction U.ι).counit.app
            ((Scheme.Modules.restrictFunctor U.ι).obj M)) := by
      rw [htri]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj M))
  refine (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y)
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app M)).mp ?_
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    ((Scheme.Modules.toPresheaf U.toScheme).map ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.restrictAdjunction U.ι).unit.app M))))
  infer_instance

end Stacks.ModuleSkyscraper

namespace Stacks.AlgebraicGeometry.ReflexivePowers

open Stacks.ModuleSkyscraper (modulesStalkFunctor
  isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app
  isColimitOfForallIsColimitModulesStalk)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)
  [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme]

/-- **The leg of the cocone of [Stacks, Tag 0EBN] at `n`, written through the unit**: the unit
`ℱ^{[n]} ⟶ j_*(ℱ^{[n]}|_U)` of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` followed by
the direct image of the trivialization `ℱ^{[n]}|_U ≅ 𝒪_U`. -/
theorem reflexivePowerSystemPushforwardCocone_ι_app_eq_unit_comp (n : ℕ) :
    (reflexivePowerSystemPushforwardCocone F s).ι.app n =
      (Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).unit.app
          (reflexivePower F n) ≫
        (Scheme.Modules.pushforward (sectionIsomorphismOpen X F s).ι).map
          (restrictReflexivePowerUnitIso F s n).hom := by
  rw [reflexivePowerSystemPushforwardCocone_ι_app]
  exact (Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).homEquiv_unit _ _ _

/-- **Every leg of the cocone of [Stacks, Tag 0EBN] is invertible on the stalk at a point of
`U`.** -/
theorem isIso_modulesStalkFunctor_map_cocone_ι_app_of_mem (x : X)
    (hx : x ∈ sectionIsomorphismOpen X F s) (n : ℕ) :
    IsIso ((modulesStalkFunctor X x).map
      ((reflexivePowerSystemPushforwardCocone F s).ι.app n)) := by
  have hxb : (sectionIsomorphismOpen X F s).ι.base ⟨x, hx⟩ = x := rfl
  have h1 : IsIso ((modulesStalkFunctor X x).map
      ((Scheme.Modules.restrictAdjunction (sectionIsomorphismOpen X F s).ι).unit.app
        (reflexivePower F n))) :=
    hxb ▸ isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app
      (sectionIsomorphismOpen X F s) (reflexivePower F n) ⟨x, hx⟩
  rw [(congrArg (modulesStalkFunctor X x).map
    (reflexivePowerSystemPushforwardCocone_ι_app_eq_unit_comp F s n)).trans
    ((modulesStalkFunctor X x).map_comp _ _)]
  exact IsIso.comp_isIso' h1 ((modulesStalkFunctor X x).mapIso
    ((Scheme.Modules.pushforward (sectionIsomorphismOpen X F s).ι).mapIso
      (restrictReflexivePowerUnitIso F s n))).isIso_hom

/-- **At a point of `U` the stalk of the cocone of [Stacks, Tag 0EBN] is colimiting.** -/
def isColimitStalkPushforwardCocone_of_mem (x : X) (hx : x ∈ sectionIsomorphismOpen X F s) :
    IsColimit ((modulesStalkFunctor X x).mapCocone
      (reflexivePowerSystemPushforwardCocone F s)) :=
  Stacks.CategoryTheory.isColimitOfIsIso_ι _ fun n =>
    isIso_modulesStalkFunctor_map_cocone_ι_app_of_mem F s x hx n

/-- **The colimit clause of [Stacks, Tag 0EBN] is a statement about the points off `U`.**

If at every point `x ∉ U` the stalk `(j_*𝒪_U)_x` is the colimit of the stalks `ℱ^{[n]}_x` along
multiplication by `s`, then `j_*𝒪_U` is the colimit of `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`. -/
def isColimitPushforwardCocone_of_notMem
    (hout : ∀ x : X, x ∉ sectionIsomorphismOpen X F s →
      IsColimit ((modulesStalkFunctor X x).mapCocone
        (reflexivePowerSystemPushforwardCocone F s))) :
    IsColimit (reflexivePowerSystemPushforwardCocone F s) :=
  isColimitOfForallIsColimitModulesStalk _ fun x => by
    by_cases hx : x ∈ sectionIsomorphismOpen X F s
    · exact isColimitStalkPushforwardCocone_of_mem F s x hx
    · exact hout x hx

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
