module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian

/-!
# A conormal module presented by a generator of the ideal

Let `Z ⊆ Y` be a closed subspace of an algebraic space over a scheme `S`, with defining ideal
sheaf `𝓘 ⊆ 𝒪_Y` and inclusion `i : Z ⟶ Y`.  Suppose given a map of `𝒪_Y`-modules
`m : 𝒪_Y ⟶ 𝓘` which is a cokernel of the inclusion `𝓘 ⟶ 𝒪_Y` — for instance multiplication by a
global section `t` generating `𝓘` with annihilator `𝓘`, as for `ε` on a scheme flat over the dual
numbers.  Then the conormal module `𝒞_{Z/Y} = i^*𝓘` is free of rank one:

`𝒞_{Z/Y} = i^*𝓘 ≅ i^*𝒪_Y ≅ 𝒪_Z`,

because `i^*` is right exact and kills the inclusion `𝓘 ⟶ 𝒪_Y` (the inclusion of `Z` factors
through `Z`, Stacks 03MB), so `i^*m` is the cokernel of a zero map.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_definingIdealSheaf_ι_eq_zero`: `i^*(𝓘 ⟶ 𝒪_Y) = 0`.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_of_isColimit`: `i^*m` is an isomorphism.
* `AlgebraicGeometry.Space.conormalModuleIsoUnitOfIsColimit`: `𝒞_{Z/Y} ≅ 𝒪_Z`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS Y.1)

/-- **The inverse image along the inclusion of a closed subspace kills the inclusion of its
defining ideal**: the inclusion factors through the subspace (Stacks 03MB). -/
theorem modulePullback_map_definingIdealSheaf_ι_eq_zero :
    (modulePullback B S hS (subspaceInclusion B S hS Y Z)).map
      (definingIdealSheaf B S hS Y Z).ι = 0 := by
  have h := (exists_comp_eq_iff_modulePullback_map_comp_eq_zero B S hS Y Z
    (subspaceInclusion B S hS Y Z)).1 ⟨𝟙 _, Category.id_comp _⟩
  let e := modulePullbackUnitIso B S hS (subspaceInclusion B S hS Y Z)
  refine (Category.comp_id _).symm.trans ?_
  refine (congrArg (_ ≫ ·) e.hom_inv_id.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ e.inv) h).trans ?_
  exact Limits.zero_comp (f := e.inv)

variable {Y Z} (m : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶
  (definingIdealSheaf B S hS Y Z).toSheafOfModules)
  (hm : (definingIdealSheaf B S hS Y Z).ι ≫ m = 0)

/-- **The inverse image of a cokernel of the ideal inclusion is an isomorphism**: it is the
cokernel of `i^*(𝓘 ⟶ 𝒪_Y)`, which is zero. -/
theorem isIso_modulePullback_map_of_isColimit (hc : IsColimit (CokernelCofork.ofπ m hm)) :
    IsIso ((modulePullback B S hS (subspaceInclusion B S hS Y Z)).map m) := by
  have := modulePullback_additive (subspaceInclusion B S hS Y Z)
  have :=
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS Y Z)).leftAdjoint_preservesColimits
  have hc' := isColimitCoforkMapOfIsColimit'
    (modulePullback B S hS (subspaceInclusion B S hS Y Z)) hm hc
  exact CokernelCofork.IsColimit.isIso_π _ hc'
    (modulePullback_map_definingIdealSheaf_ι_eq_zero B S hS Y Z)

/-- **A conormal module whose ideal is presented by a cokernel of its inclusion is free of rank
one**: `𝒞_{Z/Y} = i^*𝓘 ≅ i^*𝒪_Y ≅ 𝒪_Z`. -/
def conormalModuleIsoUnitOfIsColimit (hc : IsColimit (CokernelCofork.ofπ m hm)) :
    conormalModule B S hS Y Z ≅
      SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
        AlgebraicSpaces B S hS)) :=
  haveI := isIso_modulePullback_map_of_isColimit B S hS m hm hc
  (asIso ((modulePullback B S hS (subspaceInclusion B S hS Y Z)).map m)).symm ≪≫
    modulePullbackUnitIso B S hS (subspaceInclusion B S hS Y Z)

end AlgebraicGeometry.Space

end
