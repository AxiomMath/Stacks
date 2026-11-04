module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity

/-!
# Acyclicity of an injective sheaf of modules, at the morphism universe of the site

`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/InjectiveModuleSheafAcyclicity.lean`
proves that the underlying abelian sheaf of an injective sheaf of `R`-modules on a site `(𝒞, K)`
has vanishing higher cohomology over every object of the site, with coefficients
`AddCommGrpCat.{max u₁ v₁ t}`: the coefficient universe there dominates the universe `u₁` of the
*objects* of the site as well as the universe `v₁` of its morphisms.

This file proves the same two statements with coefficients `AddCommGrpCat.{max v₁ t}`, free of
`u₁`. A site whose objects live one universe above its morphisms — a small étale site of a
scheme, whose modules are at the morphism universe — is covered at its own module universe, which
a coefficient universe dominating `u₁` would miss. The statements of the base file are these at
`t := max u₁ t`.

## Main results

* `ext_eq_zero_of_injective_toSheafAtMorphismUniverse`: positive-degree `Ext` out of the free
  abelian sheaf on a representable into the underlying abelian sheaf of an injective sheaf of
  modules vanishes.
* `isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse`: `H^(q+1)(V, I_ab) = 0`.

## Implementation notes

**Route.** The acyclicity is `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`,
whose coefficient and `Ext` universes are independent of the site. The passage from `Ext` to
right-derived sections is
`FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`, the
corepresentation of sections read in degree-zero `Ext`, whose coefficient universe is tied to the
morphisms of the site only.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.FreeYonedaUnivLE

namespace Stacks.Cohomology.InjectiveModuleSheafAcyclicity

universe t v₁ u₁

section Sections

variable {C : Type u₁} [Category.{v₁} C] (K : GrothendieckTopology C)
  [HasSheafify K AddCommGrpCat.{max v₁ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max v₁ t}]
  [HasExt.{max v₁ t} (Sheaf K AddCommGrpCat.{max v₁ t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max v₁ t})]
  (R : Sheaf K RingCat.{max v₁ t}) (I : SheafOfModules.{max v₁ t} R) [Injective I]

/-- **The acyclicity of [Stacks, Tag 03FD] against the free abelian sheaf on a representable.**
The underlying abelian sheaf of an injective sheaf of `R`-modules has vanishing positive-degree
`Ext` out of the free abelian sheaf on the representable at an object `V` of the site, that sheaf
being the sheafification of a sectionwise free abelian presheaf.

The coefficient universe is `max v₁ t`, free of the universe `u₁` of the objects of the site:
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree` has its coefficient and `Ext`
universes independent of the site. -/
theorem ext_eq_zero_of_injective_toSheafAtMorphismUniverse (V : C) (n : ℕ)
    (e : Ext.{max v₁ t} ((freeYoneda.{t} K).obj V)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 :=
  Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree K R I _
    (ModuleSheafCohomology.isTorsionFree_sheafify K
      (uliftYoneda.{t}.obj V ⋙ AddCommGrpCat.free) (fun point => by
        show Module.IsTorsionFree ℤ
          (FreeAbelianGroup (ULift.{t} (point.unop ⟶ V)))
        exact Module.Flat.isTorsionFree)) n e

/-- **`H^(q+1)(V, I_ab) = 0`.** The higher cohomology over an object `V` of the site of the
underlying abelian sheaf of an injective sheaf of `R`-modules vanishes. Sections over `V` are
corepresented by the free abelian sheaf on the representable at `V`, so their right derived
functors are the `Ext`-groups out of it, which
`ext_eq_zero_of_injective_toSheafAtMorphismUniverse` kills.

The passage from `Ext` to right derived sections is
`FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives`, whose
coefficient universe does not have to dominate the objects of the site; so neither does the one
here, and a site whose objects live one universe above its morphisms — a small étale site of a
scheme, say — is covered at its own module universe. -/
theorem isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse (V : C) (q : ℕ) :
    IsZero ((((sheafSections K AddCommGrpCat.{max v₁ t}).obj (op V)).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) := by
  refine IsZero.of_iso ?_
    (((nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{t} K V
      (q + 1)).some).app ((SheafOfModules.toSheaf R).obj I)).symm
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  rw [ext_eq_zero_of_injective_toSheafAtMorphismUniverse.{t} K R I V q a,
    ext_eq_zero_of_injective_toSheafAtMorphismUniverse.{t} K R I V q b]

end Sections

end Stacks.Cohomology.InjectiveModuleSheafAcyclicity

end
