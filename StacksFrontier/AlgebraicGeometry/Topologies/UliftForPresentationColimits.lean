module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits

/-!
# The universe lift of sheaves of modules preserves colimits

`SheafOfModules.uliftForPresentation` raises the universe of the sections of a sheaf of modules
objectwise, keeping its coefficient ring sheaf.  It is the device by which
`SheafOfModules.HasGlobalPresentation` and the other local module conditions of Stacks 03DL are
stated in one fixed universe `max u v r m` without assuming a sheafification functor.  It is a
functor `SheafOfModules.uliftForPresentationFunctor`, whose coefficient ring sheaf is an implicit
argument; this file proves that that functor preserves colimits.

That is what lets a cokernel presentation formed at the module's own universe — for instance
Mathlib's `SheafOfModules.Presentation`, whose free modules `SheafOfModules.free` lie in
`SheafOfModules.{r} R` — be transported to the universe in which
`SheafOfModules.HasGlobalPresentation` states its coproducts and cokernel.

## Main definitions

* `SheafOfModules.uliftForPresentationFunctorCompToSheafIso` identifies the underlying abelian
  sheaf of the lift with the composition of the underlying abelian sheaf with the universe lift
  of abelian groups.

## Main results

* `SheafOfModules.preservesColimitsOfShape_uliftForPresentationFunctor`: the universe lift of
  sheaves of modules preserves colimits.

## Implementation notes

A colimit of sheaves of modules is not computed objectwise, so the universe lift — which *is*
objectwise — has no reason a priori to preserve one, and it has no adjoint on either side, a
universe not being shrinkable.  The proof factors the lift through abelian sheaves: the
underlying abelian sheaf of the lift of `M` is the composition of the underlying abelian sheaf
of `M` with `AddCommGrpCat.uliftFunctor`, an identification which holds objectwise on the nose;
`CategoryTheory.preservesColimitsOfShape_sheafCompose` carries colimits along that composition,
and `SheafOfModules.toSheaf` both preserves and reflects them.

The hypotheses are the sheafification data at the two universes and the colimits of the given
shape in abelian groups, in abelian presheaves and in sheaves of modules at the raised universe;
on a site whose objects and morphisms lie below the universe of sections, and on an essentially
small site at every universe, they are all available.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' t m r v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The underlying abelian sheaf of the universe lift of a sheaf of modules is the composition
of its underlying abelian sheaf with the universe lift of abelian groups. -/
public noncomputable def uliftForPresentationFunctorCompToSheafIso (R : Sheaf J RingCat.{r}) :
    (uliftForPresentationFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{max t m} R) ⋙
        toSheaf.{max t m} R ≅
      toSheaf.{m} R ⋙ sheafCompose J AddCommGrpCat.uliftFunctor.{t, m} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

section Colimits

variable (R : Sheaf J RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{max t m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]

/-- **The universe lift of sheaves of modules preserves colimits.**  Colimits of sheaves of
modules are detected and created by the underlying abelian sheaves, where the lift is
composition with `AddCommGrpCat.uliftFunctor`. -/
public theorem preservesColimitsOfShape_uliftForPresentationFunctor (K : Type w)
    [Category.{w'} K] [HasColimitsOfShape K (Cᵒᵖ ⥤ AddCommGrpCat.{m})]
    [HasColimitsOfShape K AddCommGrpCat.{m}] [HasColimitsOfShape K AddCommGrpCat.{max t m}]
    [HasColimitsOfShape K (SheafOfModules.{max t m} R)]
    [PreservesColimitsOfShape K (toSheaf.{m} R)]
    [PreservesColimitsOfShape K (toSheaf.{max t m} R)] :
    PreservesColimitsOfShape K
      (uliftForPresentationFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{max t m} R) := by
  have h₁ : PreservesColimitsOfShape K (sheafCompose J AddCommGrpCat.uliftFunctor.{t, m}) :=
    preservesColimitsOfShape_sheafCompose J AddCommGrpCat.uliftFunctor.{t, m} K
  have h₂ : PreservesColimitsOfShape K
      ((uliftForPresentationFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{max t m} R) ⋙
        toSheaf.{max t m} R) :=
    preservesColimitsOfShape_of_natIso
      (uliftForPresentationFunctorCompToSheafIso R :
        (uliftForPresentationFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{max t m} R) ⋙
          toSheaf.{max t m} R ≅ _).symm
  have : ReflectsColimitsOfShape K (toSheaf.{max t m} R) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (toSheaf.{max t m} R)

end Colimits

end SheafOfModules

end
