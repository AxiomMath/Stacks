module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentDerivedSections

/-!
# Cohomology of a sheaf of modules over an object of a simplicial component

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of rings on its total
site and let `U` be an object of the degree-`n` component. Stacks 0DH2 asserts that for a sheaf
of `O`-modules `F` one has `H^p(U, F) = H^p(U, g_n^*F)`, where on the left-hand side `U` is
viewed as an object of the total category.

Here `g_n : Sh(C_n) ⟶ Sh(C_total)` is the morphism of topoi of Stacks 09WG, the component
structure sheaf is `O_n = g_n⁻¹O`, and `g_n^*` is therefore restriction of sheaves of modules
along the component inclusion with the identity structure map, which is
`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction` of Stacks 0D72. As in the
source, the cohomology of a sheaf of modules is the cohomology of its underlying abelian sheaf.

The source deduces the statement from Cohomology on Sites, Lemma 0DD8 (2), whose input is that
the component inclusion is continuous and cocontinuous (Stacks 09WG) and that `g_n⁻¹O = O_n`.
This file performs that deduction at the level at which the source's own proof of Stacks 0DD8
works for a single module: `g_n^*` is restriction, so on underlying abelian sheaves it is
`g_n⁻¹` on the nose, and the comparison of cohomology of abelian sheaves is
`CategoryTheory.SimplicialSiteSituation.componentCohomologyIso`.

Stacks 0DD8 (2) itself is
`Stacks.Cohomology.DerivedLowerShriek.derivedModuleSectionsRestrictionIso`, and it is *not* used
here. That declaration is the unbounded derived-category statement; it carries as a hypothesis a
half of Stacks 0794
(`Stacks.Cohomology.DerivedLowerShriek.DerivedLowerShriekComputesGenerator`), and it is proved
by the source's unbounded argument through the derived adjunction of Stacks 07AC. For a single
module only the bounded-below half of the source's proof of Stacks 0DD8 is needed, and in the
simplicial situation that half has an unconditional input: restriction to a component preserves
injective abelian sheaves (Stacks 09WH), because lower shriek is exact (Stacks 09WG (7)). So
the comparison below needs no hypothesis beyond the data of Situation 09WE.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction_comp_toSheaf`: the
  underlying abelian sheaf of `g_n^*F` is `g_n⁻¹` of the underlying abelian sheaf of `F`, by
  `rfl`.
* `CategoryTheory.SimplicialSiteSituation.componentModuleCohomologyIso`: **Stacks 0DH2**,
  `H^p(U, g_n^*F) ≅ H^p(u(U), F)`, naturally in the sheaf of modules `F`.
* `CategoryTheory.SimplicialSiteSituation.componentModuleCohomologyObjIso`: **Stacks 0DH2**,
  the displayed equation of the tag at a single sheaf of modules.
* `CategoryTheory.SimplicialSiteSituation.componentModuleDerivedSectionsIso`: the same
  comparison at the level of `RΓ`, which is the shape of Stacks 0DD8 (2) in this situation.

## Implementation notes

`H^p(U, -)` is `Stacks.Cohomology.CompositeRightDerived.cohomology`, the `p`-th right derived
functor of sections over `U`, the definition the source makes and the one used for
Stacks 071E and Stacks 03YU. Sections of a sheaf of modules are its sections as an abelian sheaf,
so no comparison of sections functors intervenes and the equality
`componentModuleRestriction_comp_toSheaf` is definitional.

Nothing here is chosen: the comparison is built by whiskering
`CategoryTheory.SimplicialSiteSituation.componentCohomologyIso` with the forgetful functor to
abelian sheaves along that definitional equality, so it is pinned by the abelian comparison.

Coefficients sit at the site's own universe. That is forced by the two inputs: the left adjoint
of `componentModuleRestriction` exists only there (see
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`), and so
does the preservation of injectives on abelian sheaves of Stacks 09WH that
`componentCohomologyIso` consumes.

## References

* [Stacks Project, Tag 0DH2](https://stacks.math.columbia.edu/tag/0DH2)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CompositeRightDerived

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
  (n : SimplexCategory)

/-- **The underlying abelian sheaf of `g_n^*F` is `g_n⁻¹` of the underlying abelian sheaf of
`F`.** Restriction of sheaves of modules to a simplicial component has the identity structure
map, so on underlying sheaves of abelian groups it is restriction of abelian sheaves along the
component inclusion on the nose. -/
theorem componentModuleRestriction_comp_toSheaf :
    componentModuleRestriction S O n ⋙ SheafOfModules.toSheaf.{u} (componentRingSheaf S O n) =
      SheafOfModules.toSheaf.{u} O ⋙ (componentFunctor S n).sheafPushforwardContinuous
        AddCommGrpCat.{u} (S.componentTopology n) S.totalTopology :=
  rfl

/-- In the situation of Stacks 09WE let `O` be a sheaf of rings on the total site, let `U` be
an object of the degree-`n` component and let `p : ℕ`. For a sheaf of `O`-modules `F` one has
`H^p(U, g_n^*F) ≅ H^p(U, F)`, where on the right-hand side `U` is viewed as an object of the
total category; the isomorphism is natural in `F`. -/
@[stacks 0DH2]
noncomputable def componentModuleCohomologyIso (U : S.component n) (p : ℕ) :
    componentModuleRestriction S O n ⋙ SheafOfModules.toSheaf.{u} (componentRingSheaf S O n) ⋙
        cohomology (S.componentTopology n) U p ≅
      SheafOfModules.toSheaf.{u} O ⋙
        cohomology S.totalTopology ((componentFunctor S n).obj U) p :=
  (Functor.associator (componentModuleRestriction S O n)
      (SheafOfModules.toSheaf.{u} (componentRingSheaf S O n))
      (cohomology (S.componentTopology n) U p)).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (componentModuleRestriction_comp_toSheaf S O n))
      (cohomology (S.componentTopology n) U p) ≪≫
    Functor.associator (SheafOfModules.toSheaf.{u} O)
      ((componentFunctor S n).sheafPushforwardContinuous AddCommGrpCat.{u}
        (S.componentTopology n) S.totalTopology)
      (cohomology (S.componentTopology n) U p) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} O) (componentCohomologyIso S n U p)

/-- **`H^p(U, g_n^*F) ≅ H^p(U, F)` at a single sheaf of modules.** For `F` a sheaf of
`O`-modules on the total site of a simplicial-site situation and `U` an object of the degree-`n`
component, `H^p(U, g_n^*F) ≅ H^p(U, F)` with `U` viewed on the right-hand side as an object of
the total category. -/
@[stacks 0DH2]
noncomputable def componentModuleCohomologyObjIso (F : SheafOfModules.{u} O)
    (U : S.component n) (p : ℕ) :
    (cohomology (S.componentTopology n) U p).obj
        ((SheafOfModules.toSheaf.{u} (componentRingSheaf S O n)).obj
          ((componentModuleRestriction S O n).obj F)) ≅
      (cohomology S.totalTopology ((componentFunctor S n).obj U) p).obj
        ((SheafOfModules.toSheaf.{u} O).obj F) :=
  (componentModuleCohomologyIso S O n U p).app F

/-- **`RΓ(U, g_n^*F) ≅ RΓ(u(U), F)`**, naturally in the sheaf of modules `F`: the comparison of
`componentModuleCohomologyIso` at the level of the bounded-below derived category, modelled by
the homotopy category of bounded-below cochain complexes of abelian groups. This is the shape
of Stacks 0DD8 (2) in the situation of Stacks 09WE. -/
noncomputable def componentModuleDerivedSectionsIso (U : S.component n) :
    componentModuleRestriction S O n ⋙ SheafOfModules.toSheaf.{u} (componentRingSheaf S O n) ⋙
        RGamma (S.componentTopology n) U ≅
      SheafOfModules.toSheaf.{u} O ⋙ RGamma S.totalTopology ((componentFunctor S n).obj U) :=
  (Functor.associator (componentModuleRestriction S O n)
      (SheafOfModules.toSheaf.{u} (componentRingSheaf S O n))
      (RGamma (S.componentTopology n) U)).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (componentModuleRestriction_comp_toSheaf S O n))
      (RGamma (S.componentTopology n) U) ≪≫
    Functor.associator (SheafOfModules.toSheaf.{u} O)
      ((componentFunctor S n).sheafPushforwardContinuous AddCommGrpCat.{u}
        (S.componentTopology n) S.totalTopology)
      (RGamma (S.componentTopology n) U) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u} O) (componentDerivedSectionsIso S n U)

end CategoryTheory.SimplicialSiteSituation

end
