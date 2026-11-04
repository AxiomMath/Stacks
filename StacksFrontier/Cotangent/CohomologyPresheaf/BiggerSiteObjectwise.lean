module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison

/-!
# Ext-based cohomology over an object does not change on a bigger site

Let `u : C ⥤ D` be a continuous and cocontinuous functor between small sites whose restriction
functor on abelian sheaves admits an exact left adjoint and a right adjoint. Restriction along
`u` does not change cohomology over an object, where cohomology is Mathlib's `Ext`-based
`Sheaf.H'` rather than the right-derived sections functor of the chapter development.

## Main results

* `Stacks.Cohomology.BiggerSite.extFunctorObjIso`: the natural isomorphism
  `u^{-1} ⋙ Ext^p(ℤ_U, -) ≅ Ext^p(ℤ_{u(U)}, -)` of functors on abelian sheaves over the bigger
  site.
* `Stacks.Cohomology.BiggerSite.cohomologyObjIso`: its evaluation at a sheaf,
  `Sheaf.H' F p (u.obj U) ≅ Sheaf.H' (u^{-1} F) p U`, with restriction written as sheaf pullback
  along the cocontinuous `u`.

## Implementation notes

The chapter development proves the comparison for the right-derived functors of sections over an
object (`Stacks.Cohomology.CompositeRightDerived.statement2_cohomology`). This file transports it
  to the `Ext`-based
cohomology of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` along
`Stacks.Cohomology.SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections`, which
identifies the two on either site. Nothing about the comparison itself is reproved.

`Stacks.Cohomology.CompositeRightDerived.statement2_cohomology` asserts existence rather than
  exhibiting a canonical
natural isomorphism — its `omit` block drops the full faithfulness and fibre-product hypotheses
that the canonical `Stacks.Cohomology.CompositeRightDerived.cohomologyObjectIso` carries — so the
  isomorphism here is a
choice, as is each of the two transports.

The `Ext` universe is the morphism universe of the two sites. That restriction comes from the
corepresentation underlying the transport; see the implementation notes of
`StacksFrontier/Cotangent/CohomologyPresheaf/SiteSectionsComparison.lean`.

The hypothesis `[(u.sheafPullback Ab.{u} J K).PreservesMonomorphisms]` is exactness of lower
shriek on abelian sheaves. It is what makes restriction preserve injective sheaves, and so it is
the one hypothesis of this statement that is not formal: for a functor with fibre products and
equalizers that it preserves it is `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`
(Stacks 04BH), and for a representably flat functor it is Mathlib's
`CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits`.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.BiggerSite

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K]
  [(u.sheafPushforwardContinuous Ab.{u} J K).IsRightAdjoint]
  [∀ P : Cᵒᵖ ⥤ Ab.{u}, u.op.HasPointwiseRightKanExtension P]
  [(u.sheafPullback Ab.{u} J K).PreservesMonomorphisms]
  [HasSheafify J Ab.{u}] [HasSheafify K Ab.{u}]

/-- **Stacks 03YU, statement 2, in `Ext`-based form.** Restriction along `u` does not change the
`Ext`-groups out of the free abelian sheaf on an object, naturally in the abelian sheaf on the
bigger site. This is the `Ext`-based counterpart of
`Stacks.Cohomology.CompositeRightDerived.statement2_cohomology`, which is the same assertion for
  the right-derived
functors of sections over an object. -/
def extFunctorObjIso (U : C) (p : ℕ) :
    u.sheafPushforwardContinuous Ab.{u} J K ⋙
        Abelian.extFunctorObj (ModuleComparison.freeSectionsSheaf J U) p ≅
      Abelian.extFunctorObj (ModuleComparison.freeSectionsSheaf K (u.obj U)) p :=
  Functor.isoWhiskerLeft (u.sheafPushforwardContinuous Ab.{u} J K)
      (SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections J U p).some ≪≫
    (Stacks.Cohomology.CompositeRightDerived.statement2_cohomology J K u U p).some ≪≫
    (SiteSections.nonempty_extFunctorObj_iso_rightDerived_sheafSections K (u.obj U) p).some.symm

/-- **Stacks 03YU, statement 2, objectwise.** Cohomology of an abelian sheaf over `u U` on the
bigger site agrees with the cohomology over `U` of its restriction, with cohomology taken to be
Mathlib's `Sheaf.H'`. Restriction is written as sheaf pullback along the cocontinuous `u`, which
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` identifies with
`u.sheafPushforwardContinuous`. -/
def cohomologyObjIso (F : Sheaf K Ab.{u}) (p : ℕ) (U : C) :
    Sheaf.H'.{u, u, u} F p (u.obj U) ≅
      Sheaf.H'.{u, u, u} ((u.sheafPullbackCocontinuous Ab.{u} J K).obj F) p U :=
  ((extFunctorObjIso J K u U p).app F).symm ≪≫
    (Sheaf.cohomologyPresheafFunctor J p ⋙ (evaluation Cᵒᵖ Ab.{u}).obj (op U)).mapIso
      ((u.sheafPullbackCocontinuousIsoSheafPushforwardContinuous Ab.{u} J K).app F).symm

end Stacks.Cohomology.BiggerSite

end
