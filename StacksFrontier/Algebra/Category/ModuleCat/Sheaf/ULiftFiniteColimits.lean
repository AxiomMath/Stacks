module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits

/-!
# Raising the universe of the sections of a sheaf of modules is right exact

`Stacks.SheafOfModules.moduleULift` raises the universe of the sections of a sheaf of modules,
leaving the site and the coefficient ring sheaf unchanged. It is additive
(`Stacks.SheafOfModules.instAdditiveSheafOfModulesModuleULift`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit`) and left exact
(`Stacks.SheafOfModules.preservesFiniteLimits_moduleULift`, in
`StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison`). It is also right exact.

## Main results

* `Stacks.SheafOfModules.toSheaf_preservesFiniteColimits` and
  `Stacks.SheafOfModules.toSheaf_reflectsFiniteColimits`: the forgetful functor from sheaves of
  `R`-modules to sheaves of abelian groups preserves and reflects finite colimits.
* `Stacks.SheafOfModules.preservesFiniteColimits_moduleULift`: raising the universe of the
  sections of a sheaf of modules preserves finite colimits.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe t v u u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A functor preserves finite colimits as soon as its composite with a reflector does. -/
theorem preservesFiniteColimits_of_reflector
    {A : Type*} [Category A] {D : Type*} [Category D] {E : Type*} [Category E]
    {L : A ⥤ D} {Rr : D ⥤ A} (adj : L ⊣ Rr) [IsIso adj.counit] (F : D ⥤ E)
    [HasFiniteColimits A] [PreservesFiniteColimits (L ⋙ F)] :
    PreservesFiniteColimits F := by
  have : L.IsLeftAdjoint := ⟨Rr, ⟨adj⟩⟩
  refine ⟨fun shape => ⟨fun {diagram} => ?_⟩⟩
  let comparison : (diagram ⋙ Rr) ⋙ L ≅ diagram :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft diagram (asIso adj.counit) ≪≫ diagram.rightUnitor
  have : PreservesColimit ((diagram ⋙ Rr) ⋙ L) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (diagram ⋙ Rr)))
      (isColimitOfPreserves (L ⋙ F) (colimit.isColimit (diagram ⋙ Rr)))
  exact preservesColimit_of_iso_diagram _ comparison

section

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The forgetful functor from sheaves of `R`-modules to sheaves of abelian groups preserves
finite colimits. -/
theorem toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (_root_.SheafOfModules.toSheaf.{v} R) := by
  have := preservesFiniteColimits_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm
  exact preservesFiniteColimits_of_reflector
    (PresheafOfModules.sheafificationAdjunction.{v} (R := R) (𝟙 R.obj)) _

/-- The forgetful functor from sheaves of `R`-modules to sheaves of abelian groups reflects
finite colimits. -/
theorem toSheaf_reflectsFiniteColimits :
    ReflectsFiniteColimits (_root_.SheafOfModules.toSheaf.{v} R) := by
  have := toSheaf_preservesFiniteColimits.{v} R
  exact { reflects := fun _ => ⟨fun {_} => reflectsColimit_of_reflectsIsomorphisms _ _⟩ }

end

section

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]

/-- Raising the universe of the sections of a sheaf of modules preserves finite colimits. -/
theorem preservesFiniteColimits_moduleULift :
    PreservesFiniteColimits (moduleULift.{t, v} R) := by
  have := toSheaf_preservesFiniteColimits.{v} R
  have : PreservesColimitsOfSize.{v, v} (sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}) :=
    Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} (sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}) :=
    preservesSmallestColimits_of_preservesColimits _
  have : PreservesFiniteColimits
      (moduleULift.{t, v} R ⋙ _root_.SheafOfModules.toSheaf.{max v t} R) :=
    inferInstanceAs (PreservesFiniteColimits
      (_root_.SheafOfModules.toSheaf.{v} R ⋙ sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}))
  have := toSheaf_reflectsFiniteColimits.{max v t} R
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (_root_.SheafOfModules.toSheaf.{max v t} R)

end

end Stacks.SheafOfModules

end
