module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The simplicial modules of the Atiyah triangle, instantiated

`StacksFrontier/Cotangent/SheavesOfRings/AtiyahClass.lean` forms the Atiyah triangle of a sheaf of
modules over an abstract abelian category `M` of simplicial `P_•`-modules and an abstract functor
`Lπ_!`. This file records the library's own instances of those inputs at the standard resolution:
the abelian structure and derived category of the category of simplicial `P_•`-modules of
Tag 09D1 and of the modules over `π^{-1}ℬ`, and the augmentation `ε : P_• ⟶ ℬ` read on sheaves of
rings, which is the shape Tag 09D3 consumes.

The triangle of Tag 09DH at the library's own `Lπ_!` is
`CategoryTheory.Sheaf.resolutionAtiyahTriangle_distinguished`
(`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangle.lean`), and the Atiyah class of Tag 09DI
is `CategoryTheory.Sheaf.sheafAtiyahClass`
(`StacksFrontier/Cotangent/SheavesOfRings/AtiyahClassDefinite.lean`).

## Main definitions

* `CategoryTheory.Sheaf.resolutionModulesAbelian` and
  `CategoryTheory.Sheaf.resolutionModulesHasDerivedCategory`: the abelian structure of the
  category of simplicial `P_•`-modules of Tag 09D1 and its derived category `D(P_•)`.
* `CategoryTheory.Sheaf.constantTargetRing`, `CategoryTheory.Sheaf.constantTargetModulesAbelian`
  and `CategoryTheory.Sheaf.constantTargetModulesHasDerivedCategory`: the same for the modules
  over `π^{-1}B`, the intermediate category the functor of Tag 09D3 passes through.
* `CategoryTheory.Sheaf.resolutionAugmentationSimplicial`: the augmentation `ε : P_• ⟶ B` of the
  standard resolution, read on sheaves of rings.

## Main results

* `CategoryTheory.Sheaf.resolutionAugmentationSimplicial_app`: in simplicial degree `n` that
  augmentation is the augmentation of `P_n`.

## Implementation notes

The abelian structure used here must be the one instance search finds:
`Preadditive.fullSubcategory` is a global instance, so a `ShortComplex` of simplicial modules
formed with an *assumed* `Abelian` instance carries a `HasZeroMorphisms` that is not defeq to the
one `ShortComplex.ShortExact.singleTriangle` resolves. Writing a triangle at the category of
simplicial modules therefore has to use `Stacks.SimplicialModules.abelian` itself.

## References

* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), simplicial modules.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor `Lπ_!`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ### The library's own simplicial modules at the standard resolution -/

section Instantiated

open Stacks.SimplicialModules (SimplicialModule constantRing Augmentation augmentedLowerShriek)

section Structures

attribute [local instance] Stacks.SimplicialModules.abelian

/-- The category of simplicial `P_•`-modules of Tag 09D1 is abelian: it is the category of
sheaves of modules over the sheaf of rings on `Δ × C` associated to `P_•`. -/
@[instance_reducible, sga "4 IV 11.1.2" "special case"]
noncomputable def resolutionModulesAbelian : Abelian (resolutionModules J f) :=
  Stacks.SimplicialModules.abelian.{w, v, u, max u v w} J (resolutionRing J f)

/-- `D(P_•)`, the derived category of simplicial `P_•`-modules. -/
@[instance_reducible]
noncomputable def resolutionModulesHasDerivedCategory :
    HasDerivedCategory.{max u v w + 1} (resolutionModules J f) :=
  Stacks.SimplicialModules.hasDerivedCategory.{w, v, u, max u v w} J (resolutionRing J f)

/-- The sheaf of rings underlying a sheaf of commutative rings `O`, read as a constant simplicial
sheaf of rings. Its simplicial modules are the modules over `π^{-1}O` on `Δ × C`. -/
noncomputable abbrev constantTargetRing (O : Sheaf J CommRingCat.{max u v w}) :
    SimplicialObject (Sheaf J RingCat.{max u v w}) :=
  constantRing J (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} O)

/-- The category of modules over `π^{-1}ℬ` is abelian. -/
@[instance_reducible]
noncomputable def constantTargetModulesAbelian :
    Abelian (SimplicialModule.{max u v w, v, u, max u v w} J (constantTargetRing J B)) :=
  Stacks.SimplicialModules.abelian.{w, v, u, max u v w} J (constantTargetRing J B)

/-- `D(π^{-1}ℬ)`, the derived category of modules over `π^{-1}ℬ`. -/
@[instance_reducible]
noncomputable def constantTargetModulesHasDerivedCategory :
    HasDerivedCategory.{max u v w + 1}
      (SimplicialModule.{max u v w, v, u, max u v w} J (constantTargetRing J B)) :=
  Stacks.SimplicialModules.hasDerivedCategory.{w, v, u, max u v w} J (constantTargetRing J B)

end Structures

/-- The augmentation `ε : P_• ⟶ ℬ` of the standard resolution, read as an augmentation of the
simplicial sheaf of rings `P_•` by the sheaf of rings underlying `ℬ` in the sense of Tag 09D3. -/
noncomputable def resolutionAugmentationSimplicial :
    Augmentation J (resolutionRing J f)
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B) :=
  Functor.whiskerRight (standardResolution J f).hom
      (Under.forget A ⋙ sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})) ≫
    (Functor.constComp _ _ _).hom

/-- In simplicial degree `n` the augmentation of the standard resolution is the augmentation
`P_n ⟶ ℬ` of that term, read on sheaves of rings. -/
@[simp]
theorem resolutionAugmentationSimplicial_app (n : SimplexCategoryᵒᵖ) :
    (resolutionAugmentationSimplicial J f).app n = resolutionAugmentationRing J f n :=
  Category.comp_id _

end Instantiated

end CategoryTheory.Sheaf

end
