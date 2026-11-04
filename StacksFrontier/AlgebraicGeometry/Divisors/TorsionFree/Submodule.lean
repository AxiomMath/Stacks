module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic

/-!
# A submodule of a torsion-free module is torsion free

Torsion freeness of an `𝒪_X`-module, `Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree`,
is a condition on local sections, so it passes to any module mapping into a torsion-free one by
maps injective on sections — in particular to a submodule.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionSection_app`: a morphism of
  `𝒪_X`-modules carries torsion local sections to torsion local sections.
* `Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_of_injective_app`: a module with a
  map into a torsion-free module which is injective on sections is torsion free.
* `Stacks.AlgebraicGeometry.ReflexiveModules.isTorsionFree_toSheafOfModules`: **a submodule of a
  torsion-free module is torsion free.**

## Implementation notes

No integrality or quasi-coherence hypothesis appears: the predicates of
`StacksFrontier/AlgebraicGeometry/Reflexive/Basic.lean` are defined for an arbitrary `𝒪_X`-module
on an arbitrary scheme, and the proof only moves a sectionwise annihilation equation across a
morphism.

The torsion condition is transported at the level of *sections* rather than of stalks. A germ
`r • germ s = 0` is first replaced by an honest equation `a • s|_W = 0` on a neighbourhood with
`Stacks.AlgebraicGeometry.ReflexiveModules.exists_annihilator_of_isTorsionSection`, that equation
is pushed through the morphism by `AlgebraicGeometry.Scheme.Modules.Hom.app_smul` and naturality,
and only then is a germ taken again. This avoids the induced map on stalks of a morphism of
presheaves of modules, which carries no linearity lemma in Mathlib.

`AlgebraicGeometry.Scheme.Modules` is a `def` over `SheafOfModules`, so the sheaf of modules
attached to a `SheafOfModules.Submodule` and its inclusion both need the type ascription
`(N.toSheafOfModules : X.Modules)` to be read in the category `X.Modules`; see
`Stacks.AlgebraicGeometry.AffineExtend.submoduleι` for the same device.

## References

* [Stacks Project, Tag 0AVR](https://stacks.math.columbia.edu/tag/0AVR)
* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- **A morphism of `𝒪_X`-modules carries torsion sections to torsion sections.** A local
annihilator of `s` with nonzero germ annihilates the image of `s` as well, because the morphism
is linear on sections and compatible with restriction. -/
public theorem isTorsionSection_app {F G : X.Modules} (j : F ⟶ G) {U : X.Opens} {s : Γ(F, U)}
    (hs : IsTorsionSection F s) : IsTorsionSection G (Scheme.Modules.Hom.app j U s) := by
  intro x hx
  obtain ⟨W, hWU, hxW, a, hga, has⟩ := exists_annihilator_of_isTorsionSection hx (hs x hx)
  refine ⟨X.presheaf.germ W x hxW a, hga, ?_⟩
  have hnat : G.presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app j U s) =
      Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s) :=
    (PresheafOfModules.naturality_apply j.val (homOfLE hWU).op s).symm
  have hgerm : G.presheaf.germ U x hx (Scheme.Modules.Hom.app j U s) =
      G.presheaf.germ W x hxW
        (Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s)) := by
    rw [← hnat, G.presheaf.germ_res_apply]
  have hzero : a • Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s) = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, has, map_zero]
  have hsmul : G.presheaf.germ W x hxW
        (a • Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s)) =
      X.presheaf.germ W x hxW a • G.presheaf.germ W x hxW
        (Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s)) :=
    G.val.germ_smul x W hxW _ _
  rw [hgerm, ← hsmul, hzero, map_zero]

/-- **A module mapping into a torsion-free module by a map injective on sections is torsion
free.** -/
public theorem isTorsionFree_of_injective_app {F G : X.Modules} (j : F ⟶ G)
    (hj : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app j U))
    (hG : IsTorsionFree G) : IsTorsionFree F := by
  intro U s hs
  refine hj U ?_
  rw [map_zero]
  exact hG U _ (isTorsionSection_app j hs)

/-- **A submodule of a torsion-free module is torsion free.** The inclusion of a submodule is
injective on sections, being the inclusion of a submodule of sections over every open. -/
public theorem isTorsionFree_toSheafOfModules {F : X.Modules} (hF : IsTorsionFree F)
    (N : F.Submodule) : IsTorsionFree (N.toSheafOfModules : X.Modules) :=
  isTorsionFree_of_injective_app (N.ι : (N.toSheafOfModules : X.Modules) ⟶ F)
    (fun _ _ _ h => Subtype.val_injective h) hF

end Stacks.AlgebraicGeometry.ReflexiveModules

end
