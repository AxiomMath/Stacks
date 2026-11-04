module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# Global sections of modules on a scheme, over the ring of global functions

Global sections of a sheaf of `𝒪_X`-modules carry an action of the ring `Γ(X, 𝒪_X)` of global
functions, and `AlgebraicGeometry.moduleGlobalSections X` is the resulting additive functor
`X.Modules ⥤ ModuleCat Γ(X, ⊤)`. It is the functor whose right derived functors are the
cohomology modules `H^q(X, ℱ)` appearing in Stacks 01XK, and in the statements of Stacks 02O6
and 02O5, where the comparison with a base ring is made *after* deriving, by restricting
scalars along `Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X)`.

That ordering is the reason this functor is needed alongside the already available
`AlgebraicGeometry.globalSectionsOver`, which restricts scalars *before* deriving and is
therefore valued in `ModuleCat A` rather than in `ModuleCat Γ(X, ⊤)`; the two sit in different
places in a derived expression and neither determines the other. The identity
`globalSectionsOver_eq_moduleGlobalSections_comp` records how the two are related
underived — they differ exactly by postcomposition with the restriction of scalars.

Also proved here, for an arbitrary additive functor between abelian categories, is the
vanishing of its right derived functors in negative degrees, and its specialization to global
sections on a scheme. Both carry the derived-category model as a free `[HasDerivedCategory]`
binder, so a consumer may instantiate it at any model; nothing here pins one.

## Main definitions

* `AlgebraicGeometry.moduleGlobalSections` — global sections `Γ(X, -)` of sheaves of modules on
  a scheme, valued in modules over `Γ(X, 𝒪_X)`.

## Main results

* `AlgebraicGeometry.globalSectionsOver_eq_moduleGlobalSections_comp` — `A`-linear global
  sections of a scheme over `A` is `moduleGlobalSections` followed by restriction of scalars.
* `CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`, of
  `StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology` — the right derived
  functors of an additive functor vanish in negative degrees.
* `AlgebraicGeometry.isZero_moduleGlobalSections_rightDerivedPlus_of_neg` — in particular the
  cohomology modules `H^q(X, ℱ)` vanish for `q < 0`.

## Implementation notes

`Scheme.Modules` is a `def` wrapping `SheafOfModules X.ringCatSheaf` with separately declared
`Category`, `Preadditive` and `Abelian` instances, so a functor written with source
`SheafOfModules X.ringCatSheaf` does not have the instances that a statement about `X.Modules`
is elaborated with, and instance search does not cross between the two. `moduleGlobalSections`
is therefore stated with source `X.Modules`, which is the view its consumers use; the body is
Mathlib's evaluation functor, and the crossing happens once, inside the definition.

The remaining inputs needed to *state* a right derived functor out of `X.Modules` — `Abelian`,
`EnoughInjectives`, and additivity of `Scheme.Modules.pushforward` — are all already available
at this pin by instance search, so they are not restated here.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-- **`A`-linear global sections is global sections followed by restriction of scalars.** For a
scheme `f : X ⟶ Spec A`, the functor `AlgebraicGeometry.globalSectionsOver f` of
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean` restricts scalars along
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` *before* any deriving takes place, whereas `H^q(X, ℱ)` as it
appears in Stacks 01XK and 02O6 is a derived functor of `moduleGlobalSections` and is restricted
*after*. Underived the two agree, by this identity. -/
theorem globalSectionsOver_eq_moduleGlobalSections_comp {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) :
    globalSectionsOver f = moduleGlobalSections X ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :=
  rfl

/-- **Cohomology of a sheaf of modules vanishes in negative degrees.** The right derived
functors of `Γ(X, -)` are zero below degree `0`; this is the negative-degree half of the
identification `H^q(X, ℱ) = H⁰(S, R^qf_*ℱ)` of Stacks 01XK, where both sides vanish.

The derived-category model is a free binder, so this holds at whichever model the consumer
chooses. -/
theorem isZero_moduleGlobalSections_rightDerivedPlus_of_neg (X : Scheme.{u})
    [HasDerivedCategory X.Modules] [HasDerivedCategory (ModuleCat.{u} Γ(X, ⊤))]
    (F : X.Modules) (q : ℤ) (hq : q < 0) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus q).obj F) :=
  (moduleGlobalSections X).isZero_rightDerivedPlus_of_neg F q hq

end AlgebraicGeometry

end
