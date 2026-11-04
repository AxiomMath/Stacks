module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleResolution
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTransitionComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The resolution of the pullback of an arbitrary module along a ringed augmentation

Let `A` be a ringed augmentation of a simplicial-site situation `S` towards a ringed site
`(D, K, O_D)` as in Stacks 0D9D, with total morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` and component morphisms `a_n = a ∘ g_n`. Stacks 0D7C
asserts that for every sheaf of `O_D`-modules `G` there is an exact complex

`… ⟶ g_{2!}(a_2^*G) ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0`

of sheaves of `O`-modules on the total site, `g_{n!}` being the lower shriek of Stacks 0D72. This
file proves it, in the form
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.ModuleResolution`. The complex is the
simplex-coefficient resolution `n ↦ B_n(a^*G)` of `a^*G`.

## Main definitions

Names below are in the namespace
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation`.

* `componentPullbackModuleIsoRestriction`: `a_n^*G` is the literal restriction of `a^*G` to the
  degree-`n` component.
* `moduleBarResolutionTermIso`: the degree-`n` term of the simplex-coefficient resolution of
  `a^*G` is `g_{n!}(a_n^*G)`.
* `moduleResolution`: the resolution of Stacks 0D7C for an arbitrary coefficient module.

These are the constructions of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationModuleResolution.lean`
(`componentPullbackModuleIsoLiteralRestriction`, `moduleBarSheafIsoResolutionTerm`,
`simplexModuleResolution`), where they also prove
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.nonempty_moduleResolution_of_iso_unit`.

## Main results

* `isCartesianModule_totalPullbackModule`: `a^*G` is cartesian in the literal presentation of
  restriction to the components (Stacks 0D7H (3)).
* `nonempty_moduleResolution`: the complex above exists and is exact.

## References

* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Section 85.11 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- The pullback `a^*G` of a sheaf of `O_D`-modules along the ringed augmentation is a cartesian
sheaf of `O`-modules; this is `totalPullbackModule_isCartesianModule`. -/
alias isCartesianModule_totalPullbackModule := totalPullbackModule_isCartesianModule

/-- The pullback `a_n^*G` along the morphism of ringed topoi of degree `n` is isomorphic to the
literal restriction of `a^*G` to the degree-`n` component; this is
`componentPullbackModuleIsoLiteralRestriction`. -/
def componentPullbackModuleIsoRestriction (n : SimplexCategory)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    A.componentPullbackModule n G ≅
      (S.componentModuleRestriction (S.totalRingSheaf A.O) n).obj (A.totalPullbackModule G) :=
  A.componentPullbackModuleIsoLiteralRestriction n G

/-- The degree-`n` term of the simplex-coefficient resolution of `a^*G` is isomorphic to
`g_{n!}(a_n^*G)`; this is `moduleBarSheafIsoResolutionTerm`. -/
def moduleBarResolutionTermIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) (n : ℕ) :
    moduleBarSheaf (A.totalPullbackModule G) ⦋n⦌ ≅ A.resolutionTerm G n :=
  A.moduleBarSheafIsoResolutionTerm G n

/-- The resolution of Stacks 0D7C for a sheaf of `O_D`-modules `G`: the simplex-coefficient
resolution `simplexModuleResolution` of `a^*G`, whose degree-`n` term is identified with
`g_{n!}(a_n^*G)`, whose differentials are the alternating sums of its face maps, and which is
augmented onto `a^*G`. -/
def moduleResolution (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    A.ModuleResolution G :=
  A.simplexModuleResolution G

/-- With the notation of Stacks 0D9D, for a sheaf of `O_D`-modules `G` there is an exact complex

`… ⟶ g_{2!}(a_2^*G) ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0`

of sheaves of `O`-modules on the total site, with `g_{n!}` the lower shriek of Stacks 0D72: a
chain complex whose degree-`n` term is `g_{n!}(a_n^*G)`, whose differentials are the alternating
sums of the face maps of a simplicial structure on its terms, augmented onto `a^*G`, exact in
every positive degree and at the augmentation, the augmentation being an epimorphism. -/
@[stacks 0D7C]
alias nonempty_moduleResolution := nonempty_moduleResolution_of_iso_unit

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

end
