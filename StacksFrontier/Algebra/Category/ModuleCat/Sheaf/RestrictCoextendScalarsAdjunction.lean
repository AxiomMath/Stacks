module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension

@[expose] public section

/-!
# Restriction of scalars and coextension of scalars for sheaves of modules

Let `C` be a site and let `φ : O ⟶ O'` be a morphism of sheaves of rings on `C`. Restriction of
scalars along `φ` is left adjoint to coextension of scalars `F ↦ SheafHom_O(O', F)`; this is the
sheaf case of Stacks Tag 0932. Both the functor and the adjunction are constructed in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension`, as
`Stacks.SheafOfModules.CoextendScalars.coextendScalars` and
`Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction`; this file
records the adjunction under the Stacks tag.

## Main results

* `sheafRestrictCoextendAdjunction`: restriction of scalars along `φ` is left adjoint to
  coextension of scalars, for sheaves of modules. The presheaf case is
  `Stacks.PresheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction`.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

open CategoryTheory Opposite

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O O' : Sheaf J RingCat.{u}}

/-- Coextension of scalars along `φ : O ⟶ O'` for sheaves of modules: the functor
`F ↦ SheafHom_O(O', F)`, which is `coextendScalars φ`. -/
noncomputable def sheafCoextendScalars (φ : O ⟶ O') :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} O' :=
  coextendScalars φ

/-- **Stacks Tag 0932 / Lemma 18.27.8, sheaf case.** For a morphism `φ : O ⟶ O'` of sheaves of
rings on a site, restriction of scalars along `φ` is left adjoint to coextension of scalars
`F ↦ SheafHom_O(O', F)`, i.e. `Hom_O(G_O, F) = Hom_{O'}(G, SheafHom_O(O', F))` naturally in the
sheaf of `O'`-modules `G` and the sheaf of `O`-modules `F`. This is
`restrictScalars_coextendScalars_adjunction`. -/
@[stacks 0932 "the sheaf case: Hom_O(G, F) = Hom_O'(G, SheafHom_O(O', F)) for C a site and \
O ⟶ O' a map of sheaves of rings"]
noncomputable def sheafRestrictCoextendAdjunction (φ : O ⟶ O') :
    SheafOfModules.restrictScalars.{u} φ ⊣ sheafCoextendScalars φ :=
  restrictScalars_coextendScalars_adjunction φ

end Stacks.SheafOfModules.CoextendScalars
